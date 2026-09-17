//! Transactional writes — the unit every change lands through.
//!
//! Changing a set of linked files is rarely a single-file operation. A rename
//! that keeps backlinks intact has to rewrite every file that pointed at the
//! moved one; a move between directories has to re-relativize the links inside
//! the file it moved. What is logically one edit is physically several, and
//! issued one at a time an I/O failure partway through the burst leaves the
//! tree torn: updated in the files already written, stale in the ones never
//! reached.
//!
//! A [`ChangeSet`] closes that window. A caller stages its writes into one
//! instead of issuing them, and [`ChangeSet::apply`] executes the whole set as
//! a unit: each op records how to undo itself *at the moment it runs*, and the
//! first failure unwinds every op already applied, in reverse. Either the whole
//! set lands or the tree is as it was.
//!
//! ## What this does and does not buy
//!
//! This is **error** atomicity and **crash** atomicity across the whole set. A
//! failed write, a full disk, a permission error, or a rejected edit cannot
//! leave the tree half-updated, because unwinding puts back every op already
//! applied. And no single file can be caught half-written even by a power cut:
//! every [`FileOp::Write`] lands through [`Storage::write_atomic`], which
//! stages the new bytes in a temporary sibling, flushes them, and renames it
//! over the target, so an observer sees the whole old file or the whole new
//! one, never a splice. A `kill -9` or power cut *between* ops leaves the
//! journal behind; [`crate::journal::recover`] replays it forward to the
//! fully-applied state. The distinction is worth keeping sharp: caught errors
//! abort back to the pre-change state, while crashes recover to the committed
//! state.
//!
//! Both answers are **durable**, not merely consistent. `Ok` means the whole
//! set — the renames and removals as much as the writes — survives a power
//! cut from that moment on: every write settles its own flush through
//! [`Storage::write_atomic`] as it lands, and everything else the set dirtied
//! (directory entries, execute bits, freshly-minted directory chains) is
//! flushed before the journal is given up. `Err` from a clean rollback means
//! the abort is equally a fact: the restored state is flushed and the
//! journal's deletion made durable, so no later recovery can quietly roll the
//! aborted set forward. The one answer that promises less is
//! [`Error::Torn`], which says so.
//!
//! Two smaller honesties, both deliberate:
//!
//! - **Directories are not unwound.** Applying a set creates any parent
//!   directory its writes need; a rollback leaves an empty one behind. An empty
//!   directory is litter, not a torn tree.
//! - **Undo is held in memory.** Overwriting or removing a file reads its old
//!   bytes first so the rollback can put them back, which means a removed
//!   payload is briefly held whole. The buffer lives only for the length of the
//!   apply, but it does mean a set is bounded by what fits in memory —
//!   [`FileOp::CopyFrom`] is the escape hatch for a large payload already on
//!   disk.
//!
//! ## Staging is also a plan
//!
//! Because a set is a value that describes writes without performing them, it
//! is equally an answer to "what *would* this do?" — the shape a `--dry-run`
//! needs. [`ChangeSet::ops`] is that view, and it is the same sequence `apply`
//! will execute rather than a reconstruction of it.
//!
//! ## A set can expect
//!
//! A set is computed from a reading of the tree, and the tree may have moved
//! between that reading and the apply. [`ChangeSet::expect`] stages the
//! reading itself — the bytes a path held when the caller looked, or
//! [its absence](ChangeSet::expect_absent) — and `apply` checks every
//! expectation against the tree as it finds it, after the stale-journal
//! refusal and before the commit point. One that does not hold refuses the
//! whole set with [`Error::Drifted`] *before* anything is written, journaled,
//! or unwound: the caller re-reads, restages, and retries, which is
//! optimistic concurrency in exactly the compare-and-swap sense.
//!
//! Expectations speak of the tree **before** the set runs, so a set may
//! expect a path absent and then write it. And they are never journaled: the
//! journal is written only once they have held, so recovery completes an
//! interrupted set unconditionally rather than re-litigating a question the
//! commit point already answered — a recovered tree would fail its own set's
//! expectations by construction, having half-applied them.
//!
//! ## Single writer
//!
//! A set assumes it is the only thing mutating the tree while it applies. There
//! is no locking here: two processes applying sets against the same root will
//! race on the journal, and the [`Error::StaleJournal`] check that guards
//! against a *previous* interrupted change is a check-then-act, not a mutex. A
//! caller that needs several writers has to serialize them itself.
//! [Expectations](ChangeSet::expect) narrow this window rather than close
//! it — the check is itself a check-then-act, and what it detects is a writer
//! that raced the gap between the caller's *read* and this apply, which is
//! the far wider gap in practice.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::error::{Error, Result};
use crate::fs::Storage;
use crate::journal::Journal;
use crate::path::guard_in_root;

/// One staged filesystem operation. Paths are **root-relative** — the root
/// is joined on at [`apply`](ChangeSet::apply) time, so a set is portable
/// between trees and prints readably in a dry run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FileOp {
    /// Write `bytes` to `path`, creating it (and any missing parent directory)
    /// or replacing it wholesale.
    Write {
        /// The file to write.
        path: PathBuf,
        /// Its full new contents.
        bytes: Vec<u8>,
    },
    /// Move `from` to `to`, creating any missing parent directory of `to`.
    Rename {
        /// The current path.
        from: PathBuf,
        /// The new path.
        to: PathBuf,
    },
    /// Remove the file at `path`. It must exist.
    Remove {
        /// The file to remove.
        path: PathBuf,
    },
    /// Copy the bytes already on disk at `source` to `path`, verbatim.
    ///
    /// [`Write`](FileOp::Write) with the payload left where it lies. The journal
    /// records the *source path* instead of the bytes, so a set that writes a
    /// large payload costs O(path) of journal rather than a second copy of every
    /// byte — which is what makes putting a whole captured tree back
    /// tractable, where `Write` would duplicate every byte of it into the
    /// journal at the commit point.
    ///
    /// **The source must be immutable for the lifetime of the change**, because
    /// that is the entire correctness argument. A `Write` journals the exact bytes
    /// it intends, so replay after a crash is deterministic by construction; a
    /// `CopyFrom` journals a reference, and replay is deterministic only if the
    /// referent cannot have changed underneath it. A content-addressed blob
    /// satisfies this by definition — its path *is* the digest of its
    /// contents, so bytes found there are the bytes intended, or the file is gone
    /// and replay fails loudly. Do not point this at a mutable file, at a
    /// path some other op in the same set writes, or at anything outside the
    /// root.
    ///
    /// This bounds *journal* growth, not peak memory: rollback still buffers the
    /// bytes it overwrites, exactly as `Write` does.
    CopyFrom {
        /// The file to write.
        path: PathBuf,
        /// The root-relative file to copy from — immutable, and ideally
        /// content-addressed.
        source: PathBuf,
    },
    /// Make the file at `path` runnable, or not — one bit, not a mode.
    ///
    /// Lands through [`Storage::set_executable`], whose default is the honest
    /// no-op for a backend with no such bit: over such a backend the op
    /// "applies" as nothing, which is the same nothing the bit's absence
    /// already means there. Undo is captured through
    /// [`ReadStorage::executable`](crate::fs::ReadStorage::executable), so a
    /// bit that was already in the requested state rolls back to itself rather
    /// than to its opposite.
    ///
    /// A path holding a symbolic link is **refused**
    /// ([`InvalidInput`](std::io::ErrorKind::InvalidInput)), whoever made the
    /// link: mode writes follow links, so the bit would land on the link's
    /// referent — wherever it points, the lexical root guard notwithstanding.
    SetExecutable {
        /// The file whose execute bit is set or cleared.
        path: PathBuf,
        /// Whether the file should be runnable afterwards.
        executable: bool,
    },
    /// Place a symbolic link at `path` pointing at `target`, replacing
    /// whatever is there.
    ///
    /// The target is **recorded, never resolved**: it may point outside the
    /// root, at nothing, or at another link, and staging it writes nothing
    /// through it — the same terms as [`Storage::set_link`]. What is *not*
    /// permitted is another op in the same set addressing a path that
    /// traverses this link: the root guard is lexical, and a set that writes
    /// through its own fresh link is writing wherever the link points.
    ///
    /// Over a backend that models no links the op is refused
    /// ([`Unsupported`](std::io::ErrorKind::Unsupported)) and the set unwinds:
    /// unlike an execute bit, a link has no honest substitute.
    SetLink {
        /// Where the link itself lives.
        path: PathBuf,
        /// What it points at — recorded as given.
        target: PathBuf,
    },
}

impl FileOp {
    /// The path this op ultimately affects — the destination for a write or a
    /// rename, the victim for a remove. What a dry run lists.
    pub fn path(&self) -> &Path {
        match self {
            FileOp::Write { path, .. }
            | FileOp::CopyFrom { path, .. }
            | FileOp::SetExecutable { path, .. }
            | FileOp::SetLink { path, .. } => path,
            FileOp::Rename { to, .. } => to,
            FileOp::Remove { path } => path,
        }
    }
}

/// What one [expectation](ChangeSet::expect) says the tree holds at a path,
/// checked against the tree as it stands when [`apply`](ChangeSet::apply)
/// begins — before the set writes anything.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expected {
    /// The path holds exactly these bytes, read as the backend reads — which
    /// is *through* a symbolic link, if one stands there.
    Bytes(Vec<u8>),
    /// Nothing is at the path: no file, no directory, and no link — a
    /// dangling link is an entry, and counts as occupied.
    Absent,
}

/// A set of writes staged as one unit, applied all-or-nothing by
/// [`apply`](ChangeSet::apply).
///
/// Built by the mutation ops as they compute their edits, and applied once at
/// the end. Ops execute in the order they were staged: a set is a *sequence*,
/// not a bag, because `rename`-then-write and remove-then-rewrite-the-parent
/// depend on it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ChangeSet {
    ops: Vec<FileOp>,
    expected: Vec<(PathBuf, Expected)>,
}

impl ChangeSet {
    /// An empty set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Stage a write of `contents` to `path` (root-relative).
    pub fn write(&mut self, path: impl Into<PathBuf>, contents: impl Into<Vec<u8>>) -> &mut Self {
        self.ops.push(FileOp::Write {
            path: path.into(),
            bytes: contents.into(),
        });
        self
    }

    /// Stage a move from `from` to `to` (both root-relative).
    pub fn rename(&mut self, from: impl Into<PathBuf>, to: impl Into<PathBuf>) -> &mut Self {
        self.ops.push(FileOp::Rename {
            from: from.into(),
            to: to.into(),
        });
        self
    }

    /// Stage the removal of `path` (root-relative).
    pub fn remove(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.ops.push(FileOp::Remove { path: path.into() });
        self
    }

    /// Stage a copy of the file at `source` to `path` (both root-relative),
    /// instead of carrying its bytes through the set.
    ///
    /// See [`FileOp::CopyFrom`] for the immutability the source has to satisfy —
    /// it is what keeps crash recovery deterministic.
    pub fn copy_from(&mut self, path: impl Into<PathBuf>, source: impl Into<PathBuf>) -> &mut Self {
        self.ops.push(FileOp::CopyFrom {
            path: path.into(),
            source: source.into(),
        });
        self
    }

    /// Stage making the file at `path` (root-relative) runnable, or not.
    pub fn set_executable(&mut self, path: impl Into<PathBuf>, executable: bool) -> &mut Self {
        self.ops.push(FileOp::SetExecutable {
            path: path.into(),
            executable,
        });
        self
    }

    /// Stage a symbolic link at `path` (root-relative) pointing at `target`,
    /// replacing whatever is there.
    ///
    /// See [`FileOp::SetLink`] for what the target is and is not: recorded,
    /// never resolved, and not a door for other ops in the set to write
    /// through.
    pub fn set_link(&mut self, path: impl Into<PathBuf>, target: impl Into<PathBuf>) -> &mut Self {
        self.ops.push(FileOp::SetLink {
            path: path.into(),
            target: target.into(),
        });
        self
    }

    /// Expect `path` (root-relative) to hold exactly `contents` when the set
    /// applies — the bytes the caller read when it computed this set.
    ///
    /// Checked before the commit point; a mismatch (including the file being
    /// gone) refuses the whole set with [`Error::Drifted`] and nothing is
    /// written. See the [module docs](self#a-set-can-expect) for when
    /// expectations are checked and what they do and do not guard against.
    pub fn expect(&mut self, path: impl Into<PathBuf>, contents: impl Into<Vec<u8>>) -> &mut Self {
        self.expected
            .push((path.into(), Expected::Bytes(contents.into())));
        self
    }

    /// Expect nothing to be at `path` (root-relative) when the set applies —
    /// the guard for a create that must not overwrite what a racing writer
    /// put there first.
    ///
    /// An expectation speaks of the tree *before* the set runs, so expecting
    /// a path absent and then writing that same path is the ordinary use, not
    /// a contradiction.
    pub fn expect_absent(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.expected.push((path.into(), Expected::Absent));
        self
    }

    /// The staged ops, in execution order. The dry-run view.
    pub fn ops(&self) -> &[FileOp] {
        &self.ops
    }

    /// The staged expectations, in the order staged — the dry-run view's
    /// other half: what the set demands of the tree, next to what it
    /// [does](Self::ops) to it.
    pub fn expected(&self) -> &[(PathBuf, Expected)] {
        &self.expected
    }

    /// The bytes this set will leave at `path`, if it writes it — the *last*
    /// write staged, since a later one supersedes an earlier.
    ///
    /// This is what makes a set safe to read back mid-build. A document can be
    /// touched twice by one op (`reparent` repoints a child that is somehow its
    /// own old parent, and must then edit the text it just staged rather than the
    /// stale copy on disk), and before staging existed the second edit read the
    /// first one's *write* off the filesystem. Nothing hits the filesystem now
    /// until commit, so the set has to answer instead.
    ///
    /// `None` if the set does not write `path` — including when it renames or
    /// removes it, and including a [`FileOp::CopyFrom`], whose bytes are on disk
    /// at the source rather than held in the set. This is deliberately a lookup,
    /// not a filesystem overlay: it resolves the one hazard staging introduces and
    /// nothing more. A caller that must read back a path it staged a copy to has
    /// to read the source itself.
    pub fn staged(&self, path: &Path) -> Option<&[u8]> {
        self.ops.iter().rev().find_map(|op| match op {
            FileOp::Write { path: p, bytes } if p == path => Some(bytes.as_slice()),
            _ => None,
        })
    }

    /// Where this set moves `path` to, if it moves it — following a chain of
    /// renames to the final destination. `None` if the set leaves it where it is.
    ///
    /// The companion to [`staged`](Self::staged) for anything holding a path this
    /// set might move out from under it. The registry is exactly that: it knows
    /// which document it persists into, and a set that renames that document has
    /// to be followed, or its write lands at a path the set just emptied.
    pub fn renamed_to(&self, path: &Path) -> Option<PathBuf> {
        let mut current = path.to_path_buf();
        let mut moved = false;
        for op in &self.ops {
            if let FileOp::Rename { from, to } = op
                && *from == current
            {
                current = to.clone();
                moved = true;
            }
        }
        moved.then_some(current)
    }

    /// Whether nothing is staged — no ops and no
    /// [expectations](Self::expect) — so [`apply`](ChangeSet::apply) would be
    /// a no-op.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty() && self.expected.is_empty()
    }

    /// The number of staged ops.
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Append `other`'s ops after this set's, consuming it. Its expectations
    /// come along too — they still speak of the pre-apply tree, exactly as
    /// they did in the set that staged them.
    pub fn extend(&mut self, other: ChangeSet) -> &mut Self {
        self.ops.extend(other.ops);
        self.expected.extend(other.expected);
        self
    }

    /// Execute every staged op against `fs`, rooted at `root`, as one unit —
    /// crash-atomically, behind the [default](Journal::DEFAULT_NAME)
    /// write-ahead journal.
    ///
    /// Shorthand for [`Journal::default().apply(..)`](Journal::apply); reach
    /// for a named [`Journal`] when the default file name would collide with
    /// something the tree already means. Whichever is used here, the same one
    /// has to be used to [`recover`](Journal::recover) an interruption of it.
    pub async fn apply<FS: Storage>(&self, fs: &FS, root: &Path) -> Result<()> {
        Journal::default().apply(self, fs, root).await
    }
}

impl Journal {
    /// Execute every op `changes` staged against `fs`, rooted at `root`, as one
    /// unit — crash-atomically, behind this write-ahead journal.
    ///
    /// The set's intent is journaled and flushed *before* any document is
    /// touched (see [`crate::journal`]); that flush is the commit point. From
    /// there the ops run in order, each recording how to undo itself:
    ///
    /// - **On success**, everything the set dirtied is flushed durable —
    ///   pushes capped by one drain — and only then is the journal removed:
    ///   `Ok` means the change survives a power cut, not merely that it
    ///   happened.
    /// - **On an error** (a full disk, a permission fault), every op already
    ///   applied is unwound in reverse, the restored state is flushed, and the
    ///   journal is durably cleared — the mutation aborts as if it never
    ///   began, and a power cut cannot contradict the abort by resurrecting
    ///   the journal for recovery to roll forward.
    /// - **On a crash** (a `kill -9`, a power cut) there is no error to catch and
    ///   no chance to unwind, so the journal simply survives; the next
    ///   [`crate::journal::recover`] rolls the set forward to its fully-applied
    ///   state. An interrupted change set is therefore always resolved to a
    ///   consistent tree — fully before it on a caught error, fully after it
    ///   on a crash.
    ///
    /// A set of **one** op skips the journal entirely: a single op is already
    /// indivisible on a backend claiming `atomic_replace`, so there is no
    /// multi-file window for a journal to close, and a crash leaves the op either
    /// wholly done or wholly not — the same two states a recovered set lands on.
    /// It is the ordinary shape of a save, and it costs one file operation rather
    /// than four. What it does not skip is durability: a lone rename or remove
    /// still flushes the entries it edited before `Ok`, on the same promise a
    /// journaled set keeps.
    ///
    /// The rare exception is a rollback that *itself* fails ([`Error::Torn`]):
    /// the pre-change state could not be restored, so — rather than leave an
    /// unknown one — the journal is kept, and recovery will later roll the set
    /// forward to the consistent applied state. Either way the tree lands on
    /// a state this crate can name.
    ///
    /// Takes `fs`/`root` rather than a higher-level object so a bootstrap
    /// that must write two files before the tree exists can still land them
    /// together.
    ///
    /// Whatever recovers an interruption of this call must name the same
    /// journal — see [`Journal`] for why the two operations live together.
    pub async fn apply<FS: Storage>(
        &self,
        changes: &ChangeSet,
        fs: &FS,
        root: &Path,
    ) -> Result<()> {
        if changes.is_empty() {
            return Ok(());
        }
        // Clamp every staged path to the root *before* anything is
        // written or journaled. A set is built from root-relative,
        // already-normalized paths when a caller builds them that way — but
        // `apply` also lands sets assembled from data it did not author,
        // and a link target that resolves to `../../../etc/passwd` must be refused
        // rather than let an apply write outside the tree it was pointed at.
        // Expectation paths are clamped on the same terms: they are read, and
        // a set must no more be able to probe `../../../etc/passwd` than to
        // write it.
        guard_ops(&changes.ops)?;
        for (path, _) in &changes.expected {
            guard_in_root(path)?;
        }
        // Refuse to clobber a journal left by a *previous* interrupted change. Its
        // presence means an earlier mutation crashed mid-apply and has not been
        // recovered; overwriting it with this set's intent would strand the old
        // change half-applied with no record of how to finish it. Recovery
        // ([`Journal::recover`]) must complete it first. A journal this same apply is about to write does not exist yet,
        // so this only ever fires on a genuinely stale one.
        let journal = self.path_in(root);
        if fs.try_exists(&journal).await? {
            return Err(Error::StaleJournal(journal));
        }
        // Expectations are checked here and nowhere else: after the
        // stale-journal refusal, because a tree with an unrecovered change in
        // it is mid-flight and not yet in any state worth comparing against;
        // and before the fast path and the commit point alike, so a set of
        // one is guarded exactly as a set of many. A failure is a refusal,
        // not an abort — nothing has been written, so there is nothing to
        // unwind and no flush to owe.
        check_expected(fs, root, &changes.expected).await?;
        if changes.ops.is_empty() {
            return Ok(());
        }
        // A set of one needs no journal. The journal exists to make *several*
        // file operations land as one unit; a lone op is already indivisible on a
        // backend claiming `atomic_replace` — a `write_atomic` is all-or-nothing
        // by construction, and a lone `rename` or `unlink` is atomic by the
        // filesystem's own guarantee. Journaling it would write, flush, and then
        // delete a second file in order to restate a promise the op already
        // carries, roughly tripling what the commonest mutation there is — saving
        // one document — costs in writes and flushes alike.
        //
        // What this gives up is *liveness*, not safety. With a journal, a crash
        // mid-apply is rolled forward to the applied state by the next
        // [`crate::journal::recover`]; without one, a crash simply means the op
        // did not happen. For a set of one those are the only two states there
        // are — no caller can observe a half-applied set of one — so all that
        // changes is which side of the atomic instant a crash lands on, never
        // whether it lands on one at all.
        //
        // The stale-journal refusal above still applies: this path writes no
        // journal, but it must not slip a write past an *earlier* interrupted
        // change that recovery has yet to roll forward, or recovery would later
        // overwrite what was just written.
        //
        // A lone `SetLink` is excluded: the port's contract for `set_link` is
        // "replaces whatever is there", not "in one indivisible step", so on a
        // backend that replaces by remove-then-remake a crash inside the call
        // can leave the path holding neither the old file nor the link. That
        // is a half-applied set of one — the very thing the fast path's
        // argument says cannot exist — so the op takes the journal, whose
        // recovery re-runs `set_link` to the applied state.
        if changes.ops.len() == 1
            && fs.capabilities().atomic_replace
            && !matches!(changes.ops[0], FileOp::SetLink { .. })
        {
            // No undo to record, either. Nothing preceded this op that could need
            // unwinding, and every failure mode leaves the target untouched — so
            // the reflexive read of the very file about to be overwritten, whose
            // only purpose is to hold the old bytes for a rollback that cannot
            // happen here, goes with it.
            //
            // The flush debt is still owed: a lone rename or remove edits
            // directory entries nothing else will flush, and `Ok` from this
            // crate means the op outlives a power cut — for a set of one
            // exactly as for a set of many. The one honest caveat, the same
            // one `write_atomic` has always had: if the certifying flush
            // itself fails, the op has landed but `Ok` is withheld, and with
            // no journal and no undo there is nothing to roll back — the
            // error is the flush's, and the caller knows the op is at most
            // applied-but-uncertified.
            let mut touched = BTreeSet::new();
            exec(fs, root, &changes.ops[0], None, &mut touched).await?;
            return Ok(
                crate::fs::flush_all(fs, touched, root, crate::fs::Durability::Durable).await?,
            );
        }
        // The commit point: durably record the whole intent before touching a
        // single document. `write_atomic` flushes it, so a crash finds the
        // journal whole or not at all — never half-written. A journal kept
        // outside the root may be pointed at a directory nothing has made yet
        // (a cache directory on a fresh machine), so its home is made here —
        // and every directory the making mints is flushed durable before the
        // intent is trusted to live there, because a commit point inside a
        // chain of unflushed names is one a power cut can take back whole:
        // the journal file durable, the directory naming it gone, and a
        // half-applied set with no record to roll forward. `write_atomic`
        // flushes the home itself; the chain above it is owed here. The root
        // needs no such courtesy, since a tree being applied to exists.
        if let Some(home) = self.home() {
            for made in crate::fs::create_dir_all_traced(fs, home).await? {
                fs.sync(&made, crate::fs::Durability::Durable).await?;
            }
        }
        fs.write_atomic(&journal, &crate::journal::encode(&changes.ops)?)
            .await?;

        let mut undo: Vec<Undo> = Vec::new();
        let mut touched = BTreeSet::new();
        let mut cause: Option<Error> = None;
        for op in &changes.ops {
            if let Err(e) = exec(fs, root, op, Some(&mut undo), &mut touched).await {
                cause = Some(e);
                break;
            }
        }
        // Applied cleanly — now make that mean something across a power cut.
        // `exec` barriered every name-unstable debt as it ran; what remains
        // is the stable ones (edited directories, fresh chains), flushed as
        // pushes capped by one drain of the root, so the whole set survives
        // before the journal that certifies it is given up. A certification
        // that *fails* is treated exactly as a failed op — the set rolls
        // back — because "applied, but perhaps not durable" is neither of
        // the two endpoints `Ok` and `Err` name.
        if cause.is_none()
            && let Err(e) =
                crate::fs::flush_all(fs, touched, root, crate::fs::Durability::Durable).await
        {
            cause = Some(e.into());
        }
        if let Some(cause) = cause {
            return Err(match unwind_durable(fs, undo, root, &journal).await {
                // Reverted cleanly and durably: the abort is now a fact a
                // power cut cannot contradict, so the cause alone is the
                // answer.
                Ok(()) => cause,
                // Could not revert, or could not certify the reversion: the
                // journal is kept where possible, so recovery rolls the set
                // forward to the consistent applied state.
                Err(rollback) => Error::Torn {
                    cause: cause.to_string(),
                    rollback: rollback.to_string(),
                },
            });
        }
        // The deletion itself is deliberately *not* flushed: if a crash
        // resurrects the journal, the ops it names are already durable and
        // replay is idempotent, so the next recovery no-ops through it and
        // clears it — the designed-for state, at the price of at most one
        // StaleJournal prompt.
        match fs.remove_file(&journal).await {
            Ok(()) => Ok(()),
            // The set is applied and certified durable; only the journal's
            // retirement failed. Rolling a *certified* change back over a
            // delete error would be strictly worse, and a plain `Err` would
            // claim an abort that did not happen — so this is `Torn`, whose
            // contract fits exactly: the tree is at a nameable state, and
            // the surviving journal makes the next recovery an idempotent
            // no-op replay that clears it.
            Err(e) => Err(Error::Torn {
                cause: format!(
                    "the set applied and was certified durable, but its journal \
                     could not be retired: {e}"
                ),
                rollback: "the surviving journal will be replayed idempotently and \
                           cleared by the next recovery"
                    .to_string(),
            }),
        }
    }
}

/// Reverse every recorded op, certify the reversion durable, then durably
/// retire `journal` — the abort-side counterpart of the flush `apply` runs on
/// success, with the unwind folded in.
///
/// Folded in because the barriers must interleave: a step that writes bytes
/// barriers them *immediately*, while the name it wrote still resolves — a
/// later step may move it (the reversed order of a rename-then-edit set does
/// exactly that), and a barrier deferred to the end would be addressed to
/// nothing and quietly no-op. Directory debts are stable names and batch.
/// Best-effort like the unwind it absorbs: a step that fails does not abandon
/// the rest — the more that is put back the better — and the first failure is
/// what gets reported, with the journal left standing so recovery can roll
/// the set forward to the nameable applied state.
///
/// The certification order is the argument. Barriers; then, for a
/// [homed](crate::Journal::kept_in) journal, one drain of the root — the home
/// may live on another device, whose drain proves nothing about the tree's —
/// making the restored state a fact; then the journal's deletion; then one
/// drain of the journal's own directory, making the retirement a fact too.
/// When the journal lives in the root the two caps collapse into one, placed
/// after the deletion so it certifies both. Only after all of it is `Err` a
/// promise: durably before the set, with no journal for a later recovery to
/// contradict the abort with. A failure *after* the deletion leaves the abort
/// certified but its retirement not — still [`Error::Torn`]'s territory, and
/// still nameable: if the deletion survives, recovery finds nothing; if a
/// power cut takes it back, recovery rolls the set forward.
async fn unwind_durable<FS: Storage>(
    fs: &FS,
    undo: Vec<Undo>,
    root: &Path,
    journal: &Path,
) -> Result<()> {
    let mut first_error: Option<std::io::Error> = None;
    let mut dirs: BTreeSet<PathBuf> = BTreeSet::new();
    for step in undo.into_iter().rev() {
        let result = match step {
            Undo::Restore { path, bytes } => {
                // The parent joins the debt even when a Restore born of an
                // overwrite left it unchanged: the same variant reverses a
                // `Remove`, whose reversal *re-creates* the entry, and an
                // extra barrier on an unchanged directory costs less than
                // telling the two origins apart.
                if let Some(dir) = crate::fs::parent_dir(&path) {
                    dirs.insert(dir.to_path_buf());
                }
                match fs.write(&path, &bytes).await {
                    Ok(()) => fs.sync(&path, crate::fs::Durability::Ordered).await,
                    e => e,
                }
            }
            // Already absent is already undone — see `Undo::Delete`. Reporting it
            // would raise `Error::Torn` over the single most ordinary rollback
            // there is: a write to a new file that failed before creating it.
            Undo::Delete { path } => {
                if let Some(dir) = crate::fs::parent_dir(&path) {
                    dirs.insert(dir.to_path_buf());
                }
                match fs.remove_file(&path).await {
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
                    other => other,
                }
            }
            Undo::Rename { from, to } => {
                for side in [&from, &to] {
                    if let Some(dir) = crate::fs::parent_dir(side) {
                        dirs.insert(dir.to_path_buf());
                    }
                }
                fs.rename(&from, &to).await
            }
            Undo::SetExecutable { path, executable } => {
                match fs.set_executable(&path, executable).await {
                    // The inode, barriered while the name still resolves.
                    Ok(()) => fs.sync(&path, crate::fs::Durability::Ordered).await,
                    e => e,
                }
            }
            Undo::Relink { path, target } => {
                if let Some(dir) = crate::fs::parent_dir(&path) {
                    dirs.insert(dir.to_path_buf());
                }
                fs.set_link(&path, &target).await
            }
            // The link first, tolerantly (the `set_link` being reversed may
            // have failed before creating it), and only then the bytes — a
            // plain write while the link stands would land them in its target,
            // which is also why a remove that fails for a real reason must
            // stop the write rather than precede it.
            Undo::RestoreOverLink { path, bytes } => {
                if let Some(dir) = crate::fs::parent_dir(&path) {
                    dirs.insert(dir.to_path_buf());
                }
                let removed = match fs.remove_file(&path).await {
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
                    other => other,
                };
                match removed {
                    Ok(()) => match fs.write(&path, &bytes).await {
                        Ok(()) => fs.sync(&path, crate::fs::Durability::Ordered).await,
                        e => e,
                    },
                    Err(e) => Err(e),
                }
            }
        };
        if let Err(e) = result
            && first_error.is_none()
        {
            first_error = Some(e);
        }
    }
    if let Some(e) = first_error {
        return Err(e.into());
    }
    for dir in dirs {
        fs.sync(&dir, crate::fs::Durability::Ordered).await?;
    }
    let jparent = crate::fs::parent_dir(journal);
    if jparent != Some(root) {
        fs.sync(root, crate::fs::Durability::Durable).await?;
    }
    fs.remove_file(journal).await?;
    match jparent {
        Some(dir) => Ok(fs.sync(dir, crate::fs::Durability::Durable).await?),
        None => Ok(()),
    }
}

/// How to reverse one applied op, recorded against the state that op found.
///
/// Recorded *per op at execution time*, not for the whole set up front, because
/// ops in a set are not independent: `rename` moves `a.md` to `sub/a.md` and
/// then rewrites `sub/a.md`'s re-relativized links, so the write's undo has to
/// restore the bytes the rename put there — a snapshot taken before the set ran
/// would say "`sub/a.md` did not exist; delete it", and the rename's undo would
/// then have nothing to move back. Paths here are already root-joined.
enum Undo {
    /// Put these bytes back (the file existed and was overwritten or removed).
    Restore { path: PathBuf, bytes: Vec<u8> },
    /// Delete the file (it did not exist before the write created it).
    ///
    /// Recorded *before* the write it reverses, because a write that fails
    /// partway still leaves a file behind — so this has to tolerate finding
    /// nothing there, which is the case where the write failed before creating
    /// anything at all. Undoing nothing is success, not a torn tree.
    Delete { path: PathBuf },
    /// Move `from` back to `to`.
    Rename { from: PathBuf, to: PathBuf },
    /// Put the execute bit back the way it was.
    SetExecutable { path: PathBuf, executable: bool },
    /// Point the link back at its old target (the path held a link before a
    /// [`FileOp::SetLink`] repointed it).
    Relink { path: PathBuf, target: PathBuf },
    /// Put a regular file's bytes back where a link now stands.
    ///
    /// Not a [`Restore`](Undo::Restore): a plain `write` to a path holding a
    /// link writes *through* it, landing the old bytes in whatever the link
    /// points at instead of back at the path. The link has to be removed
    /// first — and tolerantly, since the `set_link` being reversed may have
    /// failed before creating it.
    RestoreOverLink { path: PathBuf, bytes: Vec<u8> },
}

/// Apply one op, optionally recording how to reverse it, and always recording
/// what it dirtied.
///
/// `undo` is `None` only for a set of one, which has no rollback to feed: see
/// the fast path in [`ChangeSet::apply`]. Recording is not merely unused there,
/// it is worth skipping — for a write it costs a full read of the file about to
/// be replaced.
///
/// `touched` collects everything this op changed that *nothing has flushed
/// yet* — the flush debt `apply` settles once, at the end, before the journal
/// is dropped. A write's rename-published entry (its bytes are barriered by
/// [`Storage::replace`] itself); a rename's or remove's edited entries; an
/// execute-bit flip's inode; a fresh directory chain. Deferring the lot to
/// one drain-capped flush is what makes ten writes into a directory cost
/// one drain, not ten.
async fn exec<FS: Storage>(
    fs: &FS,
    root: &Path,
    op: &FileOp,
    mut undo: Option<&mut Vec<Undo>>,
    touched: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    match op {
        FileOp::Write { path, bytes } => {
            let full = root.join(path);
            // Record the undo *before* writing: a write that fails partway
            // (a full disk) leaves a truncated file, and restoring the old
            // bytes over it is exactly the repair.
            if let Some(undo) = undo {
                capture_replaced(fs, &full, undo).await?;
            }
            ensure_parent(fs, &full, touched).await?;
            // Land the document through the atomic-replace protocol, so even a
            // crash mid-write cannot expose a half-written file. `replace`,
            // not `write_atomic`: the atomicity is per-file, but durability is
            // the *set's* — the parent entry (and, on a backend that cannot
            // replace atomically, the plainly-written bytes) joins the flush
            // debt the apply settles once, so ten writes into one directory
            // cost one drain rather than ten.
            fs.replace(&full, bytes).await?;
            settle_write_debt(fs, &full, touched).await?;
        }
        FileOp::Rename { from, to } => {
            let (from_full, to_full) = (root.join(from), root.join(to));
            if let Some(undo) = undo.as_deref_mut() {
                // The destination may be occupied, and the rename replaces
                // the occupant — the port contract's load-bearing half. What
                // it replaces is therefore part of "the tree as it was", and
                // the rollback owes it back: captured here, *before* the
                // Rename undo below, so the reversed unwind first moves the
                // mover home and then restores the displaced occupant into
                // the vacated name. An empty destination records a tolerant
                // delete, which the rename-back has already satisfied.
                capture_replaced(fs, &to_full, undo).await?;
            }
            ensure_parent(fs, &to_full, touched).await?;
            fs.rename(&from_full, &to_full).await?;
            // Two directory entries changed — the name removed from one
            // parent, added to the other — and nothing has flushed either.
            // The rename's *atomicity* across a crash is the metadata
            // journal's own gift on every filesystem this crate targets; what
            // the flush buys is that it is not taken back wholesale.
            for side in [&from_full, &to_full] {
                if let Some(dir) = crate::fs::parent_dir(side) {
                    touched.insert(dir.to_path_buf());
                }
            }
            if let Some(undo) = undo {
                undo.push(Undo::Rename {
                    from: to_full,
                    to: from_full,
                });
            }
        }
        FileOp::Remove { path } => {
            let full = root.join(path);
            // The entry leaves its parent, and nothing else flushes that.
            if let Some(dir) = crate::fs::parent_dir(&full) {
                touched.insert(dir.to_path_buf());
            }
            match undo {
                // What was removed is the undo, so it has to be read out
                // before it goes — the *link* where the path holds one
                // (`remove_file` removes the link, never its target, so a
                // rollback that rewrote it as a file holding the target's
                // bytes would remove a link and give back a copy), the bytes
                // everywhere else. A dangling link is removable on the same
                // terms; reading through it to capture bytes would refuse an
                // op the filesystem itself permits.
                Some(undo) => match fs.read_link(&full).await {
                    Ok(Some(target)) => {
                        fs.remove_file(&full).await?;
                        undo.push(Undo::Relink { path: full, target });
                    }
                    _ => {
                        let old = fs.read(&full).await?;
                        fs.remove_file(&full).await?;
                        undo.push(Undo::Restore {
                            path: full,
                            bytes: old,
                        });
                    }
                },
                None => fs.remove_file(&full).await?,
            }
        }
        // A `Write` whose bytes were left at the source. The read happens here, at
        // execution time, rather than when the op was staged — that is the whole
        // saving, and it is why the source has to be immutable.
        FileOp::CopyFrom { path, source } => {
            let (full, source_full) = (root.join(path), root.join(source));
            let bytes = fs.read(&source_full).await?;
            if let Some(undo) = undo {
                capture_replaced(fs, &full, undo).await?;
            }
            ensure_parent(fs, &full, touched).await?;
            fs.replace(&full, &bytes).await?;
            settle_write_debt(fs, &full, touched).await?;
        }
        FileOp::SetExecutable { path, executable } => {
            let full = root.join(path);
            guard_not_link(fs, &full).await?;
            if let Some(undo) = undo {
                // Captured through the read half, so the rollback restores
                // what *was* — not the blind opposite of what was asked,
                // which is wrong whenever the bit was already in the
                // requested state. A backend that declines the question
                // (`None`) has no bit to restore and the op below will no-op
                // on it too, so nothing is recorded.
                if let Some(was) = fs.executable(&full).await? {
                    undo.push(Undo::SetExecutable {
                        path: full.clone(),
                        executable: was,
                    });
                }
            }
            fs.set_executable(&full, *executable).await?;
            // A mode is inode metadata, and the inode is barriered *now*,
            // while the name still resolves to it — a later op in this very
            // set may rename or remove the name, and a flush deferred to the
            // final pass would then be addressed to nothing and quietly
            // no-op. The parent joins the batched debt instead: a stable
            // name, and what keeps the final drain owed at all.
            fs.sync(&full, crate::fs::Durability::Ordered).await?;
            if let Some(dir) = crate::fs::parent_dir(&full) {
                touched.insert(dir.to_path_buf());
            }
        }
        FileOp::SetLink { path, target } => {
            let full = root.join(path);
            if let Some(undo) = undo {
                match fs.read_link(&full).await {
                    // The path held a link: point it back afterwards.
                    Ok(Some(old_target)) => undo.push(Undo::Relink {
                        path: full.clone(),
                        target: old_target,
                    }),
                    // The backend models no links at all; `set_link` below
                    // will refuse, so there is nothing to record — the op
                    // never applies.
                    Ok(None) => {}
                    // Nothing there: the undo is removal, and `Delete`
                    // removes a link as readily as a file.
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                        undo.push(Undo::Delete { path: full.clone() });
                    }
                    // Not a link — a regular file about to give way to one.
                    // Its bytes are the undo, restored *after* the link is
                    // removed (see [`Undo::RestoreOverLink`]); any error
                    // reading them aborts the op before it touches anything.
                    Err(_) => {
                        let old = fs.read(&full).await?;
                        undo.push(Undo::RestoreOverLink {
                            path: full.clone(),
                            bytes: old,
                        });
                    }
                }
            }
            ensure_parent(fs, &full, touched).await?;
            fs.set_link(&full, target).await?;
            // The link is an entry (and its inode rides on the entry's
            // flush): the parent is the debt.
            if let Some(dir) = crate::fs::parent_dir(&full) {
                touched.insert(dir.to_path_buf());
            }
        }
    }
    Ok(())
}

/// Settle what one [`Storage::replace`] leaves behind: the parent entry the
/// rename published joins the batched debt, and on a backend that cannot
/// replace atomically the plainly-written bytes are barriered *here* — while
/// the name still resolves to them, since a later op in the same set may
/// rename or remove it, and a flush deferred to the final pass would then be
/// addressed to nothing. The final drain makes the barrier durable.
pub(crate) async fn settle_write_debt<FS: Storage>(
    fs: &FS,
    full: &Path,
    touched: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    if !fs.capabilities().atomic_replace {
        fs.sync(full, crate::fs::Durability::Ordered).await?;
    }
    if let Some(dir) = crate::fs::parent_dir(full) {
        touched.insert(dir.to_path_buf());
    }
    Ok(())
}

/// Refuse a [`FileOp::SetExecutable`] whose path holds a symbolic link.
///
/// Mode reads and writes follow links — `metadata` and `set_permissions`
/// both do — so setting the bit "at" a link sets it on the link's *referent*,
/// wherever that is. The root guard cannot see this: it is lexical, the link
/// is not, and a set that stages `set_link("l", "/outside/victim")` then
/// `set_executable("l", true)` would chmod a file the tree does not own. The
/// same applies to a link the set never made. So the op is refused on any
/// link, loudly, before the undo capture reads a bit that is not the path's
/// own. Shared by the apply and the journal replay, which faces the same
/// combination from bytes it did not author.
pub(crate) async fn guard_not_link<FS: Storage>(fs: &FS, full: &Path) -> Result<()> {
    if let Ok(Some(_)) = fs.read_link(full).await {
        return Err(Error::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "refusing to set the execute bit through the symbolic link at {}",
                full.display()
            ),
        )));
    }
    Ok(())
}

/// Record how to put back whatever a replacing write (`Write`, `CopyFrom`) is
/// about to displace at `full`.
///
/// The link question comes first, because a plain `read` follows one: capture
/// by bytes alone and a path holding a link rolls back to a *regular file*
/// holding a copy of its target — the link gone, shared content duplicated,
/// and "the tree is as it was" quietly false. So: a link is put back as a link
/// ([`Undo::Relink`] — `write_atomic` will have replaced the entry itself,
/// and `set_link` restores it the same way); nothing is put back by deletion;
/// and only a path holding an actual file is captured as bytes.
async fn capture_replaced<FS: Storage>(fs: &FS, full: &Path, undo: &mut Vec<Undo>) -> Result<()> {
    match fs.read_link(full).await {
        Ok(Some(target)) => undo.push(Undo::Relink {
            path: full.to_path_buf(),
            target,
        }),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            undo.push(Undo::Delete {
                path: full.to_path_buf(),
            });
        }
        // `Ok(None)` — a backend with no links, where nothing can be one —
        // and any other error — the path holds something that is not a link —
        // both fall through to capturing bytes.
        _ => match fs.read(full).await {
            Ok(old) => undo.push(Undo::Restore {
                path: full.to_path_buf(),
                bytes: old,
            }),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                undo.push(Undo::Delete {
                    path: full.to_path_buf(),
                });
            }
            Err(e) => return Err(e.into()),
        },
    }
    Ok(())
}

/// Clamp every path a sequence of ops names to the root it will run against.
///
/// Shared by [`ChangeSet::apply`], which guards sets assembled from data it
/// did not author, and by [`Journal::recover`](crate::Journal::recover), whose
/// input is *always* that: a journal is bytes found on disk, and — homed in a
/// synced folder, or planted — possibly bytes some other machine wrote. The
/// checksum authenticates nothing (anyone can recompute FNV-1a), so replay
/// must refuse an escaping path exactly as the apply that would have written
/// the journal honestly would have.
///
/// The one path deliberately *not* clamped is a [`FileOp::SetLink`] target:
/// nothing is written through it — it is recorded, not resolved — and a link
/// is allowed to point wherever links point, outside the root included.
pub(crate) fn guard_ops(ops: &[FileOp]) -> Result<()> {
    for op in ops {
        match op {
            FileOp::Write { path, .. }
            | FileOp::Remove { path }
            | FileOp::SetExecutable { path, .. }
            | FileOp::SetLink { path, .. } => {
                guard_in_root(path)?;
            }
            FileOp::Rename { from, to } => {
                guard_in_root(from)?;
                guard_in_root(to)?;
            }
            // The source is clamped too: it is read, and a set assembled by a
            // caller must not be able to pull `../../../etc/passwd` into the
            // tree any more than it may write out of one.
            FileOp::CopyFrom { path, source } => {
                guard_in_root(path)?;
                guard_in_root(source)?;
            }
        }
    }
    Ok(())
}

/// Check every staged expectation against the tree as it stands, before the
/// set touches anything.
///
/// Bytes are read as the backend reads — through a standing link — while
/// absence is judged on the *entry*: a dangling link names no bytes but still
/// occupies the path, and a create that expected absence must not land on top
/// of it. `read_link` settles the link question (its error is the normal
/// answer for "no link here", so only a real fault propagates), `try_exists`
/// settles the rest.
async fn check_expected<FS: Storage>(
    fs: &FS,
    root: &Path,
    expected: &[(PathBuf, Expected)],
) -> Result<()> {
    for (rel, want) in expected {
        let full = root.join(rel);
        match want {
            Expected::Bytes(bytes) => match fs.read(&full).await {
                Ok(found) if found == *bytes => {}
                Ok(_) => return Err(Error::Drifted(rel.clone())),
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    return Err(Error::Drifted(rel.clone()));
                }
                Err(e) => return Err(e.into()),
            },
            Expected::Absent => {
                let link = match fs.read_link(&full).await {
                    Ok(link) => link,
                    Err(e)
                        if matches!(
                            e.kind(),
                            std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidInput
                        ) =>
                    {
                        None
                    }
                    Err(e) => return Err(e.into()),
                };
                if link.is_some() || fs.try_exists(&full).await? {
                    return Err(Error::Drifted(rel.clone()));
                }
            }
        }
    }
    Ok(())
}

/// Create `full`'s parent directory if it is missing. Unconditional (rather than
/// staged as its own op) because a directory is not part of the document graph:
/// it is an artifact of *where* a write lands, so it belongs to the write.
///
/// Every directory the making mints joins `touched`: each is an entry of its
/// own, persisting separately from the file that prompted it, and a
/// durably-flushed file inside a chain of unflushed names is a file a power
/// cut can orphan.
async fn ensure_parent<FS: Storage>(
    fs: &FS,
    full: &Path,
    touched: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    if let Some(dir) = crate::fs::parent_dir(full) {
        for made in crate::fs::create_dir_all_traced(fs, dir).await? {
            touched.insert(made);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exec::block_on;
    use crate::fs::{ReadStorage, StdFs};
    use crate::fs_faults::{FailAtWrite, FsEvent, RecordingFs};
    use crate::journal::Journal;

    fn tmp(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("fstx-change-{name}"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn read(root: &Path, rel: &str) -> Option<String> {
        std::fs::read_to_string(root.join(rel)).ok()
    }

    #[test]
    fn applies_every_op_in_order() {
        let root = tmp("apply");
        std::fs::write(root.join("parent.md"), "old parent").unwrap();
        let mut cs = ChangeSet::new();
        cs.write("child.md", "child");
        cs.write("parent.md", "new parent");
        block_on(cs.apply(&StdFs, &root)).unwrap();
        assert_eq!(read(&root, "child.md").as_deref(), Some("child"));
        assert_eq!(read(&root, "parent.md").as_deref(), Some("new parent"));
    }

    #[test]
    fn creates_missing_parent_directories() {
        let root = tmp("mkdir");
        let mut cs = ChangeSet::new();
        cs.write("deep/nested/child.md", "hi");
        block_on(cs.apply(&StdFs, &root)).unwrap();
        assert_eq!(read(&root, "deep/nested/child.md").as_deref(), Some("hi"));
    }

    #[test]
    fn a_copy_lands_the_source_bytes_and_leaves_the_source_alone() {
        let root = tmp("copy");
        std::fs::create_dir_all(root.join("history/blobs/9f")).unwrap();
        std::fs::write(root.join("history/blobs/9f/86d081"), "captured").unwrap();
        std::fs::write(root.join("notes.md"), "damaged").unwrap();

        let mut cs = ChangeSet::new();
        cs.copy_from("notes.md", "history/blobs/9f/86d081");
        // A path that does not exist yet gets its parent made, as a write does.
        cs.copy_from("deep/fresh.md", "history/blobs/9f/86d081");
        block_on(cs.apply(&StdFs, &root)).unwrap();

        assert_eq!(read(&root, "notes.md").as_deref(), Some("captured"));
        assert_eq!(read(&root, "deep/fresh.md").as_deref(), Some("captured"));
        // The blob is shared by every event naming it: read, never consumed.
        assert_eq!(
            read(&root, "history/blobs/9f/86d081").as_deref(),
            Some("captured")
        );
    }

    #[test]
    fn a_failed_copy_rolls_back_exactly_as_a_failed_write_does() {
        // A copy is a write whose payload was fetched late, so it must record the
        // same undo: restore what it overwrote, delete what it created.
        let root = tmp("rollback-copy");
        std::fs::create_dir_all(root.join("history/blobs/9f")).unwrap();
        std::fs::write(root.join("history/blobs/9f/86d081"), "captured").unwrap();
        std::fs::write(root.join("notes.md"), "damaged").unwrap();

        let mut cs = ChangeSet::new();
        cs.copy_from("notes.md", "history/blobs/9f/86d081");
        cs.copy_from("fresh.md", "history/blobs/9f/86d081");
        cs.write("doomed.md", "never lands");
        let err = block_on(cs.apply(&FailAtWrite::nth(2), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");

        assert_eq!(read(&root, "notes.md").as_deref(), Some("damaged"));
        assert_eq!(read(&root, "fresh.md"), None);
    }

    #[test]
    fn a_copy_from_a_missing_source_fails_before_the_target_is_touched() {
        // The half-synced event: the manifest names a blob the transport has not
        // delivered. Better to fail the set than to write a hole into the tree.
        let root = tmp("copy-missing-source");
        std::fs::write(root.join("notes.md"), "damaged").unwrap();
        let mut cs = ChangeSet::new();
        cs.copy_from("notes.md", "history/blobs/9f/86d081");
        assert!(block_on(cs.apply(&StdFs, &root)).is_err());
        assert_eq!(read(&root, "notes.md").as_deref(), Some("damaged"));
    }

    #[test]
    fn a_copy_cannot_read_from_outside_the_root() {
        // The source is read, so it is clamped like every written path: a set a
        // caller assembled must not be able to pull the host's files into the tree.
        let root = tmp("copy-escape");
        let mut cs = ChangeSet::new();
        cs.copy_from("stolen.md", "../../../etc/passwd");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(matches!(err, Error::Escape(_)), "{err:?}");
        assert_eq!(read(&root, "stolen.md"), None);
    }

    #[test]
    fn a_failed_write_restores_the_files_already_written() {
        let root = tmp("rollback-write");
        std::fs::write(root.join("parent.md"), "old parent").unwrap();
        std::fs::write(root.join("child.md"), "old child").unwrap();

        // Three writes staged; the third fails.
        let mut cs = ChangeSet::new();
        cs.write("child.md", "new child");
        cs.write("parent.md", "new parent");
        cs.write("third.md", "third");
        let err = block_on(cs.apply(&FailAtWrite::nth(2), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");

        // Everything is as it was found — no half-linked tree.
        assert_eq!(read(&root, "child.md").as_deref(), Some("old child"));
        assert_eq!(read(&root, "parent.md").as_deref(), Some("old parent"));
    }

    #[test]
    fn a_failed_write_deletes_files_the_set_had_created() {
        let root = tmp("rollback-create");
        let mut cs = ChangeSet::new();
        cs.write("fresh.md", "fresh");
        cs.write("doomed.md", "doomed");
        let err = block_on(cs.apply(&FailAtWrite::nth(1), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");
        // The file the set created before failing is gone, not orphaned.
        assert_eq!(read(&root, "fresh.md"), None);
    }

    #[cfg(unix)]
    fn is_executable(root: &Path, rel: &str) -> bool {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::metadata(root.join(rel))
            .unwrap()
            .permissions()
            .mode()
            & 0o111
            != 0
    }

    #[cfg(unix)]
    #[test]
    fn sets_and_clears_the_execute_bit() {
        let root = tmp("exec-bit");
        std::fs::write(root.join("run.sh"), "#!/bin/sh").unwrap();
        std::fs::write(root.join("plain.md"), "notes").unwrap();

        let mut cs = ChangeSet::new();
        cs.set_executable("run.sh", true);
        cs.set_executable("plain.md", false);
        block_on(cs.apply(&StdFs, &root)).unwrap();

        assert!(is_executable(&root, "run.sh"));
        assert!(!is_executable(&root, "plain.md"));
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_restores_the_execute_bit_it_flipped() {
        let root = tmp("rollback-exec");
        std::fs::write(root.join("run.sh"), "#!/bin/sh").unwrap();
        assert!(!is_executable(&root, "run.sh"));

        let mut cs = ChangeSet::new();
        cs.set_executable("run.sh", true);
        cs.write("doomed.md", "never lands");
        let err = block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");

        assert!(
            !is_executable(&root, "run.sh"),
            "the bit must roll back to what was, not stay flipped"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_bit_already_in_the_requested_state_rolls_back_to_itself() {
        // The undo is captured through the read half, not derived as "the
        // opposite of what was asked" — which is wrong exactly here.
        use std::os::unix::fs::PermissionsExt as _;
        let root = tmp("rollback-exec-noop");
        std::fs::write(root.join("run.sh"), "#!/bin/sh").unwrap();
        let mut perms = std::fs::metadata(root.join("run.sh"))
            .unwrap()
            .permissions();
        perms.set_mode(perms.mode() | 0o100);
        std::fs::set_permissions(root.join("run.sh"), perms).unwrap();

        let mut cs = ChangeSet::new();
        cs.set_executable("run.sh", true); // already true
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        assert!(
            is_executable(&root, "run.sh"),
            "rolling back a no-op flip must not clear a bit the set never set"
        );
    }

    #[cfg(unix)]
    #[test]
    fn lands_a_link_and_reads_nothing_through_it() {
        let root = tmp("link");
        let mut cs = ChangeSet::new();
        // A dangling target, and one pointing outside the root: both are
        // honest links — recorded, never resolved.
        cs.set_link("here.md", "nowhere/yet.md");
        cs.set_link("out.md", "../elsewhere.md");
        block_on(cs.apply(&StdFs, &root)).unwrap();

        assert_eq!(
            std::fs::read_link(root.join("here.md")).unwrap(),
            PathBuf::from("nowhere/yet.md")
        );
        assert_eq!(
            std::fs::read_link(root.join("out.md")).unwrap(),
            PathBuf::from("../elsewhere.md")
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_restores_the_file_a_link_replaced() {
        // The sharp edge `Undo::RestoreOverLink` exists for: a plain write
        // while the link stands would land the old bytes in the link's
        // *target*. The rollback must leave a regular file holding them, and
        // the target untouched.
        let root = tmp("rollback-link-over-file");
        std::fs::write(root.join("victim.md"), "the original").unwrap();
        std::fs::write(root.join("target.md"), "someone else's file").unwrap();

        let mut cs = ChangeSet::new();
        cs.set_link("victim.md", "target.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        let md = std::fs::symlink_metadata(root.join("victim.md")).unwrap();
        assert!(md.file_type().is_file(), "the link must be gone");
        assert_eq!(read(&root, "victim.md").as_deref(), Some("the original"));
        assert_eq!(
            read(&root, "target.md").as_deref(),
            Some("someone else's file"),
            "nothing may be written through the link during rollback"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_repoints_a_link_it_had_repointed() {
        let root = tmp("rollback-relink");
        std::os::unix::fs::symlink("old-target.md", root.join("link.md")).unwrap();

        let mut cs = ChangeSet::new();
        cs.set_link("link.md", "new-target.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        assert_eq!(
            std::fs::read_link(root.join("link.md")).unwrap(),
            PathBuf::from("old-target.md")
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_removes_a_link_it_had_created() {
        let root = tmp("rollback-link-fresh");
        let mut cs = ChangeSet::new();
        cs.set_link("fresh.md", "anywhere.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        assert!(
            std::fs::symlink_metadata(root.join("fresh.md")).is_err(),
            "the created link must be gone"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_lone_link_takes_the_journal_rather_than_the_fast_path() {
        // `set_link`'s contract is "replaces", not "replaces indivisibly", so
        // a set of one link still needs the journal a crash can roll forward —
        // the fast path's no-half-applied-state argument does not cover it.
        let root = tmp("lone-link");
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.set_link("link.md", "target.md");
        block_on(cs.apply(&fs, &root)).unwrap();

        let journaled = fs
            .events()
            .iter()
            .any(|e| matches!(e, FsEvent::Write(p) if Journal::default().owns_path(p)));
        assert!(journaled, "events: {:?}", fs.events());
    }

    #[test]
    fn an_execute_flip_over_a_backend_with_no_bit_applies_as_nothing() {
        // The op means "make this runnable", and on a backend where nothing
        // is runnable there is nothing to do — the honest no-op, not an error.
        let fs = crate::fs::InMemoryFs::new();
        block_on(fs.write(Path::new("root/doc.md"), b"hi")).unwrap();
        let mut cs = ChangeSet::new();
        cs.set_executable("doc.md", true);
        cs.write("other.md", "lands");
        block_on(cs.apply(&fs, Path::new("root"))).unwrap();
        assert_eq!(
            block_on(fs.read_to_string(Path::new("root/other.md"))).unwrap(),
            "lands"
        );
    }

    #[test]
    fn a_link_over_a_backend_without_links_unwinds_the_set() {
        // Unlike an execute bit, a link has no honest substitute: the backend
        // refuses, and the refusal aborts the whole set.
        struct NoLinks(crate::fs::InMemoryFs);
        impl crate::fs::ReadStorage for NoLinks {
            async fn read(&self, path: &Path) -> std::io::Result<Vec<u8>> {
                self.0.read(path).await
            }
            async fn read_to_string(&self, path: &Path) -> std::io::Result<String> {
                self.0.read_to_string(path).await
            }
            async fn read_dir(&self, path: &Path) -> std::io::Result<Vec<crate::fs::DirEntry>> {
                self.0.read_dir(path).await
            }
            async fn metadata(&self, path: &Path) -> std::io::Result<crate::fs::Metadata> {
                self.0.metadata(path).await
            }
            // `executable` and `read_link` stay at the defaults: the declines.
        }
        impl Storage for NoLinks {
            async fn write(&self, path: &Path, contents: &[u8]) -> std::io::Result<()> {
                self.0.write(path, contents).await
            }
            async fn create_dir_all(&self, path: &Path) -> std::io::Result<()> {
                self.0.create_dir_all(path).await
            }
            async fn remove_file(&self, path: &Path) -> std::io::Result<()> {
                self.0.remove_file(path).await
            }
            async fn remove_dir_all(&self, path: &Path) -> std::io::Result<()> {
                self.0.remove_dir_all(path).await
            }
            async fn rename(&self, from: &Path, to: &Path) -> std::io::Result<()> {
                self.0.rename(from, to).await
            }
            fn capabilities(&self) -> crate::fs::Capabilities {
                self.0.capabilities()
            }
            // `write_atomic` deliberately stays at the default too: its
            // temp-then-rename runs fine over the wrapped backend now that
            // `InMemoryFs::rename` replaces an occupied file, which this
            // test then exercises for free.
            // `set_link` stays at the default: the refusal.
        }

        let fs = NoLinks(crate::fs::InMemoryFs::new());
        block_on(fs.0.write(Path::new("root/before.md"), b"old")).unwrap();
        let mut cs = ChangeSet::new();
        cs.write("before.md", "new");
        cs.set_link("link.md", "target.md");
        let err = block_on(cs.apply(&fs, Path::new("root"))).unwrap_err();
        assert!(err.to_string().contains("symbolic links"), "{err}");
        assert_eq!(
            block_on(fs.0.read_to_string(Path::new("root/before.md"))).unwrap(),
            "old",
            "the write that preceded the refused link must unwind"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_restores_a_link_a_write_replaced_as_a_link() {
        // Capture-by-bytes would follow the link and roll back to a regular
        // file holding a copy of the target — link gone, content duplicated,
        // "the tree is as it was" quietly false. The link must come back as
        // a link, pointing where it pointed.
        let root = tmp("rollback-write-over-link");
        std::fs::write(root.join("target.md"), "the target").unwrap();
        std::os::unix::fs::symlink("target.md", root.join("link.md")).unwrap();

        let mut cs = ChangeSet::new();
        cs.write("link.md", "replaces the link");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(1), &root)).unwrap_err();

        let md = std::fs::symlink_metadata(root.join("link.md")).unwrap();
        assert!(
            md.file_type().is_symlink(),
            "the link must come back as a link"
        );
        assert_eq!(
            std::fs::read_link(root.join("link.md")).unwrap(),
            PathBuf::from("target.md")
        );
        assert_eq!(
            read(&root, "target.md").as_deref(),
            Some("the target"),
            "the rollback must not have written through the link"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_failed_set_restores_a_link_it_removed_as_a_link() {
        // Also the dangling case: `remove_file` removes a link the read-based
        // capture could never have read through, so removal must not require
        // the target to exist.
        let root = tmp("rollback-remove-link");
        std::os::unix::fs::symlink("nowhere.md", root.join("dangling.md")).unwrap();

        let mut cs = ChangeSet::new();
        cs.remove("dangling.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        assert_eq!(
            std::fs::read_link(root.join("dangling.md")).unwrap(),
            PathBuf::from("nowhere.md"),
            "the removed link must come back as the link it was"
        );
    }

    #[cfg(unix)]
    #[test]
    fn the_execute_bit_is_refused_through_a_link_and_the_set_unwinds() {
        // The escape this closes: `set_link` at a path inside the root, then
        // `set_executable` at that same path — mode writes follow links, so
        // without the refusal the bit lands on the referent, wherever it
        // points. The root guard is lexical and cannot see it; the op must.
        use std::os::unix::fs::PermissionsExt as _;
        let root = tmp("exec-through-link");
        let outside = tmp("exec-through-link-outside");
        std::fs::write(outside.join("victim.sh"), "#!/bin/sh").unwrap();
        let victim = outside.join("victim.sh");
        let mode_before = std::fs::metadata(&victim).unwrap().permissions().mode();

        let mut cs = ChangeSet::new();
        cs.set_link("l", victim.to_str().unwrap());
        cs.set_executable("l", true);
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();

        assert!(err.to_string().contains("symbolic link"), "{err}");
        assert_eq!(
            std::fs::metadata(&victim).unwrap().permissions().mode(),
            mode_before,
            "the referent's mode must be untouched"
        );
        assert!(
            std::fs::symlink_metadata(root.join("l")).is_err(),
            "the refused set must unwind the link it made"
        );
    }

    // ---- the durability of an answer ----

    #[test]
    fn a_set_of_renames_and_removes_is_flushed_before_the_journal_is_dropped() {
        // `Ok` means the change survives a power cut. Renames and removes
        // edit directory entries no per-op call flushes, so the apply must
        // settle that debt — pushes capped by one durable sync — before it
        // gives up the journal that certifies the set.
        let root = tmp("flush-before-drop");
        std::fs::write(root.join("a.md"), "a").unwrap();
        std::fs::write(root.join("c.md"), "c").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.rename("a.md", "sub/b.md");
        cs.remove("c.md");
        block_on(cs.apply(&fs, &root)).unwrap();

        let journal = Journal::default().path_in(&root);
        let jtmp = crate::fs::temp_sibling(&journal);
        assert_eq!(
            fs.events(),
            vec![
                // The commit point: the journal, via write_atomic.
                FsEvent::Write(jtmp.clone()),
                FsEvent::Sync(jtmp.clone(), crate::fs::Durability::Ordered),
                FsEvent::Rename(jtmp, journal.clone()),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
                // The ops.
                FsEvent::Rename(root.join("a.md"), root.join("sub/b.md")),
                FsEvent::Remove(root.join("c.md")),
                // The debt: both touched directories, pushes capped by one
                // drain of the root — the anchor, which always exists, where
                // whichever debt happened to sort last might not — and only
                // then the journal.
                FsEvent::Sync(root.join("sub"), crate::fs::Durability::Pushed),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
                FsEvent::Remove(journal),
            ]
        );
    }

    #[test]
    fn a_lone_rename_flushes_the_entries_it_edited() {
        // The fast path skips the journal, never the promise.
        let root = tmp("lone-rename-flush");
        std::fs::write(root.join("a.md"), "a").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.rename("a.md", "b.md");
        block_on(cs.apply(&fs, &root)).unwrap();

        assert_eq!(
            fs.events(),
            vec![
                FsEvent::Rename(root.join("a.md"), root.join("b.md")),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
            ]
        );
    }

    #[test]
    fn a_lone_write_pays_the_staging_flush_and_one_drain() {
        // The commonest mutation there is must not get slower: a lone write
        // is `replace`'s three steps plus the one durable flush of its
        // parent — the same four events `write_atomic` always cost it.
        let root = tmp("lone-write-flush");
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("a.md", "a");
        block_on(cs.apply(&fs, &root)).unwrap();

        let tmp_name = crate::fs::temp_sibling(&root.join("a.md"));
        assert_eq!(
            fs.events(),
            vec![
                FsEvent::Write(tmp_name.clone()),
                FsEvent::Sync(tmp_name.clone(), crate::fs::Durability::Ordered),
                FsEvent::Rename(tmp_name, root.join("a.md")),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
            ]
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_lone_exec_flip_flushes_the_inode_it_edited() {
        // A mode is inode metadata: the inode is barriered while its name
        // still resolves, and the anchored drain makes the barrier durable.
        let root = tmp("lone-exec-flush");
        std::fs::write(root.join("run.sh"), "#!/bin/sh").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.set_executable("run.sh", true);
        block_on(cs.apply(&fs, &root)).unwrap();

        assert_eq!(
            fs.events(),
            vec![
                FsEvent::SetExecutable(root.join("run.sh"), true),
                FsEvent::Sync(root.join("run.sh"), crate::fs::Durability::Ordered),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
            ]
        );
    }

    /// A recording double whose `n`th non-journal write fails — the lever for
    /// exercising the rollback paths while still reading the event stream.
    struct FailingRecorder {
        inner: RecordingFs,
        writes: std::cell::Cell<usize>,
        fail_at: usize,
    }
    impl crate::fs::ReadStorage for FailingRecorder {
        async fn read(&self, path: &Path) -> std::io::Result<Vec<u8>> {
            self.inner.read(path).await
        }
        async fn read_to_string(&self, path: &Path) -> std::io::Result<String> {
            self.inner.read_to_string(path).await
        }
        async fn read_dir(&self, path: &Path) -> std::io::Result<Vec<crate::fs::DirEntry>> {
            self.inner.read_dir(path).await
        }
        async fn metadata(&self, path: &Path) -> std::io::Result<crate::fs::Metadata> {
            self.inner.metadata(path).await
        }
        async fn read_link(&self, path: &Path) -> std::io::Result<Option<PathBuf>> {
            self.inner.read_link(path).await
        }
    }
    impl Storage for FailingRecorder {
        async fn write(&self, path: &Path, contents: &[u8]) -> std::io::Result<()> {
            if !Journal::default().owns_path(path) {
                let n = self.writes.get();
                self.writes.set(n + 1);
                if n == self.fail_at {
                    return Err(std::io::Error::other("disk full (test)"));
                }
            }
            self.inner.write(path, contents).await
        }
        async fn create_dir_all(&self, path: &Path) -> std::io::Result<()> {
            self.inner.create_dir_all(path).await
        }
        async fn remove_file(&self, path: &Path) -> std::io::Result<()> {
            self.inner.remove_file(path).await
        }
        async fn remove_dir_all(&self, path: &Path) -> std::io::Result<()> {
            self.inner.remove_dir_all(path).await
        }
        async fn rename(&self, from: &Path, to: &Path) -> std::io::Result<()> {
            self.inner.rename(from, to).await
        }
        fn capabilities(&self) -> crate::fs::Capabilities {
            self.inner.capabilities()
        }
        async fn sync(&self, path: &Path, need: crate::fs::Durability) -> std::io::Result<()> {
            self.inner.sync(path, need).await
        }
    }

    #[test]
    fn an_abort_flushes_the_restored_state_and_durably_retires_the_journal() {
        // `Err` from a clean rollback is a promise too: the restored state is
        // flushed, the journal's deletion made durable — so a power cut right
        // after the abort cannot resurrect the journal for the next recovery
        // to roll the aborted set forward.
        let root = tmp("abort-durable");
        std::fs::write(root.join("existing.md"), "before").unwrap();
        let fs = FailingRecorder {
            inner: RecordingFs::local(),
            writes: std::cell::Cell::new(0),
            fail_at: 1,
        };
        let mut cs = ChangeSet::new();
        cs.write("existing.md", "after");
        cs.write("doomed.md", "never lands");
        let err = block_on(cs.apply(&fs, &root)).unwrap_err();
        assert!(matches!(err, Error::Io(_)), "{err:?}");
        assert_eq!(read(&root, "existing.md").as_deref(), Some("before"));

        // The tail of the event stream is the abort's certification: restored
        // bytes barriered the moment they land (while their name still
        // resolves), the edited directories barriered after, the journal
        // removed, and its directory drained.
        let journal = Journal::default().path_in(&root);
        let events = fs.inner.events();
        let tail = &events[events.len() - 4..];
        assert_eq!(
            tail,
            &[
                FsEvent::Sync(root.join("existing.md"), crate::fs::Durability::Ordered),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Ordered),
                FsEvent::Remove(journal),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
            ],
            "events: {events:?}"
        );
    }

    #[test]
    fn many_writes_into_one_directory_cost_one_drain() {
        // The engineered-away redundancy: per-file durable parent flushes
        // would make an N-write set drain the device N+1 times. Through
        // `replace` and the batched final pass, exactly two drains remain —
        // the journal's commit point, and the cap that certifies the set.
        let root = tmp("write-economy");
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("a.md", "a");
        cs.write("b.md", "b");
        cs.write("c.md", "c");
        cs.write("d.md", "d");
        block_on(cs.apply(&fs, &root)).unwrap();

        let drains = fs
            .events()
            .iter()
            .filter(|e| matches!(e, FsEvent::Sync(_, crate::fs::Durability::Durable)))
            .count();
        assert_eq!(drains, 2, "events: {:?}", fs.events());
    }

    #[cfg(unix)]
    #[test]
    fn a_flipped_bit_survives_its_name_being_renamed_away() {
        // The trap the anchored flush exists for: the flip's debt is a name,
        // and a later op in the same set moves it. The inode must be
        // barriered while the name still resolves, and the one drain must
        // land on a path that still exists — the root — never on whichever
        // stale name happened to sort last, which `sync` would answer with a
        // silent no-op.
        let root = tmp("flip-then-rename");
        std::fs::write(root.join("z.sh"), "#!/bin/sh").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.set_executable("z.sh", true);
        cs.rename("z.sh", "a.sh");
        block_on(cs.apply(&fs, &root)).unwrap();

        assert!(is_executable(&root, "a.sh"));
        let journal = Journal::default().path_in(&root);
        let jtmp = crate::fs::temp_sibling(&journal);
        assert_eq!(
            fs.events(),
            vec![
                FsEvent::Write(jtmp.clone()),
                FsEvent::Sync(jtmp.clone(), crate::fs::Durability::Ordered),
                FsEvent::Rename(jtmp, journal.clone()),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
                FsEvent::SetExecutable(root.join("z.sh"), true),
                // The inode, while `z.sh` still names it.
                FsEvent::Sync(root.join("z.sh"), crate::fs::Durability::Ordered),
                FsEvent::Rename(root.join("z.sh"), root.join("a.sh")),
                // The cap on the root — which exists — not on the stale name.
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
                FsEvent::Remove(journal),
            ]
        );
    }

    /// A recording double whose `sync` fails once, on the `n`th `Durable`
    /// drain of `anchor` — the smallest lever that reaches the certification
    /// paths without touching anything else.
    struct FailNthDrain {
        inner: RecordingFs,
        anchor: PathBuf,
        drains: std::cell::Cell<usize>,
        fail_at: usize,
    }
    impl crate::fs::ReadStorage for FailNthDrain {
        async fn read(&self, path: &Path) -> std::io::Result<Vec<u8>> {
            self.inner.read(path).await
        }
        async fn read_to_string(&self, path: &Path) -> std::io::Result<String> {
            self.inner.read_to_string(path).await
        }
        async fn read_dir(&self, path: &Path) -> std::io::Result<Vec<crate::fs::DirEntry>> {
            self.inner.read_dir(path).await
        }
        async fn metadata(&self, path: &Path) -> std::io::Result<crate::fs::Metadata> {
            self.inner.metadata(path).await
        }
        async fn read_link(&self, path: &Path) -> std::io::Result<Option<PathBuf>> {
            self.inner.read_link(path).await
        }
    }
    impl Storage for FailNthDrain {
        async fn write(&self, path: &Path, contents: &[u8]) -> std::io::Result<()> {
            self.inner.write(path, contents).await
        }
        async fn create_dir_all(&self, path: &Path) -> std::io::Result<()> {
            self.inner.create_dir_all(path).await
        }
        async fn remove_file(&self, path: &Path) -> std::io::Result<()> {
            self.inner.remove_file(path).await
        }
        async fn remove_dir_all(&self, path: &Path) -> std::io::Result<()> {
            self.inner.remove_dir_all(path).await
        }
        async fn rename(&self, from: &Path, to: &Path) -> std::io::Result<()> {
            self.inner.rename(from, to).await
        }
        fn capabilities(&self) -> crate::fs::Capabilities {
            self.inner.capabilities()
        }
        async fn sync(&self, path: &Path, need: crate::fs::Durability) -> std::io::Result<()> {
            if need == crate::fs::Durability::Durable && path == self.anchor.as_path() {
                let n = self.drains.get();
                self.drains.set(n + 1);
                if n == self.fail_at {
                    return Err(std::io::Error::other("cannot drain (test)"));
                }
            }
            self.inner.sync(path, need).await
        }
    }

    #[test]
    fn an_abort_flushes_the_entry_a_restored_removal_recreates() {
        // Rolling back a Remove re-creates a directory entry; an abort that
        // certified only the bytes would let a power cut keep the removal the
        // caller was told never happened.
        let root = tmp("abort-remove-entry");
        std::fs::create_dir_all(root.join("sub")).unwrap();
        std::fs::write(root.join("sub/gone.md"), "kept after all").unwrap();

        let fs = FailingRecorder {
            inner: RecordingFs::local(),
            writes: std::cell::Cell::new(0),
            fail_at: 0,
        };
        let mut cs = ChangeSet::new();
        cs.remove("sub/gone.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&fs, &root)).unwrap_err();

        assert_eq!(
            read(&root, "sub/gone.md").as_deref(),
            Some("kept after all")
        );
        let events = fs.inner.events();
        let entry_flushed = events
            .iter()
            .position(|e| matches!(e, FsEvent::Sync(p, _) if *p == root.join("sub")));
        let journal_retired = events
            .iter()
            .rposition(|e| matches!(e, FsEvent::Remove(p) if Journal::default().owns_path(p)));
        match (entry_flushed, journal_retired) {
            (Some(flush), Some(retire)) => assert!(
                flush < retire,
                "the recreated entry must be flushed before the journal goes; events: {events:?}"
            ),
            _ => panic!("expected a sub flush and a journal retirement; events: {events:?}"),
        }
    }

    #[test]
    fn a_failed_certification_rolls_the_set_back() {
        // "Applied, but perhaps not durable" is neither of the two endpoints
        // Ok and Err name — so a flush that fails is treated exactly as a
        // failed op, and the caller's Err still means durably-before.
        let root = tmp("failed-certification");
        std::fs::write(root.join("existing.md"), "before").unwrap();
        // Drain #0 is the journal commit's parent flush; #1 is the set's
        // certifying cap — the one that fails. The abort's own drain (#2)
        // succeeds, so the rollback certifies cleanly.
        let fs = FailNthDrain {
            inner: RecordingFs::local(),
            anchor: root.clone(),
            drains: std::cell::Cell::new(0),
            fail_at: 1,
        };
        let mut cs = ChangeSet::new();
        cs.write("existing.md", "after");
        cs.write("fresh.md", "fresh");
        let err = block_on(cs.apply(&fs, &root)).unwrap_err();

        assert!(matches!(err, Error::Io(_)), "a clean rollback: {err:?}");
        assert_eq!(read(&root, "existing.md").as_deref(), Some("before"));
        assert_eq!(read(&root, "fresh.md"), None);
        assert!(
            !Journal::default().path_in(&root).exists(),
            "the abort durably retired the journal"
        );
    }

    #[test]
    fn a_failed_rename_set_restores_the_file_the_rename_displaced() {
        // The destination's occupant is part of "the tree as it was": the
        // rename replaces it (the port contract's load-bearing half), so the
        // rollback owes it back — first the mover home, then the victim into
        // the vacated name.
        let root = tmp("rollback-rename-victim");
        std::fs::write(root.join("a.md"), "the mover").unwrap();
        std::fs::write(root.join("b.md"), "the victim").unwrap();

        let mut cs = ChangeSet::new();
        cs.rename("a.md", "b.md");
        cs.write("doomed.md", "never lands");
        block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();

        assert_eq!(read(&root, "a.md").as_deref(), Some("the mover"));
        assert_eq!(read(&root, "b.md").as_deref(), Some("the victim"));
    }

    #[test]
    fn a_deep_chain_written_through_a_set_is_flushed_link_by_link() {
        // The same debt OrderedBatch and the journal's home already pay:
        // directories the set freshly mints are entries a power cut can take
        // back out from under a durably-flushed file.
        let root = tmp("set-chain-flush");
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("deep/nested/a.md", "a");
        cs.write("b.md", "b");
        block_on(cs.apply(&fs, &root)).unwrap();

        for dir in [root.clone(), root.join("deep"), root.join("deep/nested")] {
            assert!(
                fs.events()
                    .iter()
                    .any(|e| matches!(e, FsEvent::Sync(p, _) if *p == dir)),
                "{} never flushed; events: {:?}",
                dir.display(),
                fs.events()
            );
        }
    }

    #[test]
    fn a_clean_rollback_reports_the_cause_not_a_tear() {
        // `Torn` means "this crate cannot say what is on disk" — it must be reserved
        // for a rollback that genuinely failed. The commonest rollback of all is a
        // write to a *new* file that failed before creating it, whose undo then
        // finds nothing to delete; calling that a tear would cry wolf on every
        // ordinary full disk. Asserted on the variant, because `Torn`'s message
        // embeds the cause and so still matches a "disk full" substring check.
        let root = tmp("clean-rollback");
        std::fs::write(root.join("existing.md"), "before").unwrap();
        let mut cs = ChangeSet::new();
        cs.write("existing.md", "after");
        cs.write("brand-new.md", "never lands");
        let err = block_on(cs.apply(&FailAtWrite::nth(1), &root)).unwrap_err();

        assert!(
            matches!(err, Error::Io(_)),
            "a clean rollback should surface the cause itself, got: {err:?}"
        );
        assert_eq!(read(&root, "existing.md").as_deref(), Some("before"));
        assert_eq!(read(&root, "brand-new.md"), None);
    }

    #[test]
    fn a_failed_write_after_a_rename_moves_the_file_back() {
        // The ordering `mutate::rename` actually uses: move the file, then
        // rewrite it with its re-relativized links. The write's undo must
        // restore the *renamed* bytes so the rename's undo has something to
        // move back — the reason undo is recorded per-op, not up front.
        let root = tmp("rollback-rename");
        std::fs::write(root.join("a.md"), "original").unwrap();
        let mut cs = ChangeSet::new();
        cs.rename("a.md", "sub/a.md");
        cs.write("sub/a.md", "rewritten");
        cs.write("parent.md", "never gets here");
        let err = block_on(cs.apply(&FailAtWrite::nth(1), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");

        assert_eq!(read(&root, "a.md").as_deref(), Some("original"));
        assert_eq!(read(&root, "sub/a.md"), None);
    }

    #[test]
    fn a_failed_write_restores_a_removed_file() {
        let root = tmp("rollback-remove");
        std::fs::write(root.join("gone.md"), "precious").unwrap();
        let mut cs = ChangeSet::new();
        cs.remove("gone.md");
        cs.write("parent.md", "boom");
        let err = block_on(cs.apply(&FailAtWrite::nth(0), &root)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");
        assert_eq!(read(&root, "gone.md").as_deref(), Some("precious"));
    }

    #[test]
    fn every_document_write_lands_atomically_and_leaves_no_temp_files() {
        // The payoff of routing `FileOp::Write` through `write_atomic`: applying a
        // set stages each document through a sibling and renames it into place, so
        // no reader ever catches one half-written, and a clean apply leaves not one
        // staging file behind.
        let root = tmp("apply-atomic");
        std::fs::write(root.join("parent.md"), "old parent").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("child.md", "child");
        cs.write("parent.md", "new parent");
        block_on(cs.apply(&fs, &root)).unwrap();

        assert_eq!(read(&root, "child.md").as_deref(), Some("child"));
        assert_eq!(read(&root, "parent.md").as_deref(), Some("new parent"));

        // Every write in the log is either a staging sibling or a rename target —
        // never a plain write straight to a document path.
        for event in fs.events() {
            if let FsEvent::Write(p) = event {
                let name = p.file_name().unwrap().to_string_lossy();
                assert!(
                    name.contains("fstx-tmp"),
                    "wrote a document non-atomically: {name}"
                );
            }
        }
        // And nothing staging survives.
        let leftovers: Vec<_> = std::fs::read_dir(&root)
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .filter(|n| n.contains("fstx-tmp"))
            .collect();
        assert!(
            leftovers.is_empty(),
            "staging files survived apply: {leftovers:?}"
        );
    }

    #[test]
    fn apply_journals_before_touching_documents_and_clears_it_after() {
        // The commit-point protocol: the journal is written and renamed into
        // place *before* the first document write, and removed *after* the last —
        // so a crash is always found with the journal either whole (roll forward)
        // or absent (nothing began).
        let root = tmp("journal-order");
        std::fs::write(root.join("parent.md"), "old parent").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("child.md", "child");
        cs.write("parent.md", "new parent");
        block_on(cs.apply(&fs, &root)).unwrap();

        let events = fs.events();
        let journal = Journal::default().path_in(&root);

        // The journal is renamed into place before any document write happens.
        let journal_committed = events
            .iter()
            .position(|e| matches!(e, FsEvent::Rename(_, to) if *to == journal))
            .expect("journal must be committed");
        let first_doc_write = events
            .iter()
            .position(|e| matches!(e, FsEvent::Write(p) if !Journal::default().owns_path(p)))
            .expect("a document must be written");
        assert!(
            journal_committed < first_doc_write,
            "the journal must be durable before any document is touched"
        );

        // And it is removed at the very end — nothing survives a clean apply.
        assert_eq!(events.last(), Some(&FsEvent::Remove(journal.clone())));
        assert!(!journal.exists());
    }

    #[test]
    fn a_set_of_one_lands_without_a_journal_at_all() {
        // The counterpart to the test above, and the reason it stages two ops: a
        // lone op is already indivisible, so the journal that makes *several* land
        // together has nothing left to guarantee and is skipped. The assertion is
        // the exact event list, because what is being claimed is an absence —
        // "contains no journal write" would still pass if the set quietly grew a
        // second file operation somewhere else.
        let root = tmp("journal-single");
        std::fs::write(root.join("doc.md"), "old").unwrap();
        let fs = RecordingFs::local();
        let mut cs = ChangeSet::new();
        cs.write("doc.md", "new");
        block_on(cs.apply(&fs, &root)).unwrap();

        let (target, temp) = (root.join("doc.md"), root.join(".doc.md.fstx-tmp"));
        assert_eq!(std::fs::read_to_string(&target).unwrap(), "new");
        assert_eq!(
            fs.events(),
            vec![
                FsEvent::Write(temp.clone()),
                FsEvent::Sync(temp.clone(), crate::fs::Durability::Ordered),
                FsEvent::Rename(temp, target),
                FsEvent::Sync(root.clone(), crate::fs::Durability::Durable),
            ],
            "a set of one must cost exactly one atomic write and nothing else"
        );
        assert!(!Journal::default().path_in(&root).exists());
    }

    #[test]
    fn a_set_of_one_still_refuses_to_run_over_a_stale_journal() {
        // Skipping the journal must not also skip the *check* for one. An earlier
        // change crashed mid-apply and recovery has yet to roll it forward; a save
        // that slipped past would be silently overwritten when it finally does.
        let root = tmp("journal-single-stale");
        std::fs::write(root.join("doc.md"), "old").unwrap();
        std::fs::write(
            Journal::default().path_in(&root),
            "a previous change's intent",
        )
        .unwrap();

        let mut cs = ChangeSet::new();
        cs.write("doc.md", "new");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();

        assert!(matches!(err, Error::StaleJournal(_)), "got {err:?}");
        assert_eq!(
            std::fs::read_to_string(root.join("doc.md")).unwrap(),
            "old",
            "the refused write must not have happened"
        );
    }

    #[test]
    fn a_set_of_one_does_not_read_the_file_it_is_about_to_replace() {
        // The undo bookkeeping is what made a save read its own target back, and a
        // set of one has no rollback to feed it to. Proven the only way an absent
        // read can be: a target that cannot be read at all still writes fine.
        let root = tmp("journal-single-unreadable");
        let target = root.join("doc.md");
        std::fs::write(&target, "old").unwrap();
        let mut perms = std::fs::metadata(&target).unwrap().permissions();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            perms.set_mode(0o200); // write-only: any read of it fails
        }
        std::fs::set_permissions(&target, perms).unwrap();

        let mut cs = ChangeSet::new();
        cs.write("doc.md", "new");
        block_on(cs.apply(&StdFs, &root)).expect("a write-only target is still replaceable");

        // Reading the result back needs the readability restored first: an
        // atomic write preserves the target's mode, so a write-only document is
        // still write-only afterwards. That is the point of the mode being
        // carried across, and it is why this cannot simply read the file.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                std::fs::metadata(&target).unwrap().permissions().mode() & 0o777,
                0o200,
                "replacing the contents must not have changed who may read it"
            );
            std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o600)).unwrap();
        }
        assert_eq!(std::fs::read_to_string(&target).unwrap(), "new");
    }

    #[test]
    fn a_caught_error_reverts_and_leaves_no_journal_behind() {
        // An error mid-apply unwinds to the pre-change state *and* clears the
        // journal — so a later recovery cannot roll the aborted set forward.
        let root = tmp("journal-abort");
        std::fs::write(root.join("existing.md"), "before").unwrap();
        let mut cs = ChangeSet::new();
        cs.write("existing.md", "after");
        cs.write("brand-new.md", "never lands");
        let err = block_on(cs.apply(&FailAtWrite::nth(1), &root)).unwrap_err();

        assert!(err.to_string().contains("disk full"), "{err}");
        assert_eq!(read(&root, "existing.md").as_deref(), Some("before"));
        assert_eq!(read(&root, "brand-new.md"), None);
        assert!(
            !Journal::default().path_in(&root).exists(),
            "a cleanly-reverted change must not leave a journal to roll forward"
        );
    }

    #[test]
    fn a_crash_mid_apply_is_recovered_forward_from_the_journal() {
        // The end-to-end crash story: apply writes the journal, a crash strikes
        // before the set finishes (modeled by leaving the journal and only the
        // first write on disk), and `recover` rolls the rest forward.
        let root = tmp("journal-crash");
        std::fs::write(root.join("parent.md"), "old parent").unwrap();
        let mut cs = ChangeSet::new();
        cs.write("child.md", "child");
        cs.write("parent.md", "new parent");

        // The journal the real apply would have committed at its commit point.
        std::fs::write(
            Journal::default().path_in(&root),
            crate::journal::encode(cs.ops()).unwrap(),
        )
        .unwrap();
        // A crash after the first document landed but before the second.
        std::fs::write(root.join("child.md"), "child").unwrap();

        let outcome = block_on(crate::journal::recover(&StdFs, &root)).unwrap();
        assert_eq!(outcome, crate::journal::Recovered::Applied(2));
        assert_eq!(read(&root, "child.md").as_deref(), Some("child"));
        assert_eq!(read(&root, "parent.md").as_deref(), Some("new parent"));
        assert!(!Journal::default().path_in(&root).exists());
    }

    #[test]
    fn apply_refuses_a_path_that_escapes_the_root() {
        // A staged op whose path climbs above the root (a hostile link target that
        // resolved to `../escape.md`) is refused before anything — journal or
        // document — is written.
        let root = tmp("escape-write");
        let mut cs = ChangeSet::new();
        cs.write("../escape.md", "should never land");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Escape(_)),
            "expected Escape, got {err:?}"
        );
        // Nothing was written, in or out of the root, and no journal remains.
        assert!(!root.parent().unwrap().join("escape.md").exists());
        assert!(!Journal::default().path_in(&root).exists());
    }

    #[test]
    fn apply_refuses_an_absolute_path() {
        // An absolute path would ignore the root under `root.join`; it escapes too.
        let root = tmp("escape-abs");
        let mut cs = ChangeSet::new();
        cs.write("/tmp/fstx-abs-escape-should-not-exist.md", "nope");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Escape(_)),
            "expected Escape, got {err:?}"
        );
    }

    #[test]
    fn apply_refuses_to_clobber_a_stale_journal() {
        // A journal from a *previous* interrupted change is on disk. Applying a new
        // set must refuse rather than overwrite it — the old change would otherwise
        // be stranded with no record to recover from.
        let root = tmp("stale-journal");
        std::fs::write(root.join("doc.md"), "before").unwrap();
        // Pretend a prior change crashed mid-apply, leaving a valid journal.
        let prior = vec![FileOp::Write {
            path: "other.md".into(),
            bytes: b"prior".to_vec(),
        }];
        std::fs::write(
            Journal::default().path_in(&root),
            crate::journal::encode(&prior).unwrap(),
        )
        .unwrap();

        let mut cs = ChangeSet::new();
        cs.write("doc.md", "after");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::StaleJournal(_)),
            "expected StaleJournal, got {err:?}"
        );
        // The new set did not land, and the old journal is untouched — recovery can
        // still complete the interrupted change.
        assert_eq!(read(&root, "doc.md").as_deref(), Some("before"));
        assert!(Journal::default().path_in(&root).exists());
    }

    #[test]
    fn apply_proceeds_once_the_stale_journal_is_recovered() {
        // After recovery clears the journal, the same set applies cleanly — the
        // refusal is about an *unrecovered* interruption, not a permanent lock.
        let root = tmp("stale-journal-cleared");
        std::fs::write(root.join("doc.md"), "before").unwrap();
        let prior = vec![FileOp::Write {
            path: "other.md".into(),
            bytes: b"prior".to_vec(),
        }];
        std::fs::write(
            Journal::default().path_in(&root),
            crate::journal::encode(&prior).unwrap(),
        )
        .unwrap();
        block_on(crate::journal::recover(&StdFs, &root)).unwrap();

        let mut cs = ChangeSet::new();
        cs.write("doc.md", "after");
        block_on(cs.apply(&StdFs, &root)).unwrap();
        assert_eq!(read(&root, "doc.md").as_deref(), Some("after"));
        assert_eq!(read(&root, "other.md").as_deref(), Some("prior"));
    }

    #[test]
    fn an_expectation_that_holds_lets_the_set_apply() {
        let root = tmp("expect-holds");
        std::fs::write(root.join("doc.md"), "as read").unwrap();
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        cs.write("doc.md", "rewritten");
        cs.write("index.md", "points at doc");
        block_on(cs.apply(&StdFs, &root)).unwrap();
        assert_eq!(read(&root, "doc.md").as_deref(), Some("rewritten"));
        assert_eq!(read(&root, "index.md").as_deref(), Some("points at doc"));
    }

    #[test]
    fn a_drifted_expectation_refuses_the_set_before_anything_is_written() {
        // The tree moved between the caller's read and the apply. The whole
        // set — including ops on paths that did NOT drift — is refused, and
        // the refusal precedes the commit point: no document touched, no
        // journal written.
        let root = tmp("expect-drift");
        std::fs::write(root.join("doc.md"), "someone else's edit").unwrap();
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        cs.write("doc.md", "rewritten");
        cs.write("index.md", "points at doc");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(&err, Error::Drifted(p) if p == Path::new("doc.md")),
            "expected Drifted(doc.md), got {err:?}"
        );
        assert_eq!(
            read(&root, "doc.md").as_deref(),
            Some("someone else's edit")
        );
        assert_eq!(read(&root, "index.md"), None);
        assert!(!Journal::default().path_in(&root).exists());
    }

    #[test]
    fn an_expectation_of_a_missing_file_is_drift_not_io() {
        // "I read these bytes, and now there is no file at all" is the same
        // story as "now there are different bytes": something else moved the
        // tree. The caller gets the retryable answer, not a bare NotFound.
        let root = tmp("expect-gone");
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        cs.write("doc.md", "rewritten");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(&err, Error::Drifted(p) if p == Path::new("doc.md")),
            "expected Drifted, got {err:?}"
        );
    }

    #[test]
    fn an_expected_absence_is_drift_when_the_path_is_occupied() {
        let root = tmp("expect-occupied");
        std::fs::write(root.join("new.md"), "raced you to it").unwrap();
        let mut cs = ChangeSet::new();
        cs.expect_absent("new.md");
        cs.write("new.md", "mine");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(&err, Error::Drifted(p) if p == Path::new("new.md")),
            "expected Drifted, got {err:?}"
        );
        assert_eq!(read(&root, "new.md").as_deref(), Some("raced you to it"));
    }

    #[test]
    #[cfg(unix)]
    fn a_dangling_link_counts_as_occupied_for_absence() {
        // `try_exists` follows links, so a dangling one answers "no" — but the
        // entry is there, and a create that expected absence must see it.
        let root = tmp("expect-dangling");
        std::os::unix::fs::symlink("points-at-nothing.md", root.join("new.md")).unwrap();
        let mut cs = ChangeSet::new();
        cs.expect_absent("new.md");
        cs.write("new.md", "mine");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(&err, Error::Drifted(p) if p == Path::new("new.md")),
            "expected Drifted, got {err:?}"
        );
    }

    #[test]
    fn expectations_speak_of_the_tree_before_the_set_runs() {
        // Expecting a path absent and then writing that same path is the
        // ordinary create guard, not a contradiction — and the second apply
        // of the very same set drifts, because the first one occupied it.
        let root = tmp("expect-preimage");
        let mut cs = ChangeSet::new();
        cs.expect_absent("new.md");
        cs.write("new.md", "mine");
        cs.write("index.md", "names it");
        block_on(cs.apply(&StdFs, &root)).unwrap();
        assert_eq!(read(&root, "new.md").as_deref(), Some("mine"));

        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(&err, Error::Drifted(p) if p == Path::new("new.md")),
            "expected Drifted on the second apply, got {err:?}"
        );
    }

    #[test]
    fn a_lone_op_is_guarded_exactly_as_a_set_of_many() {
        // The fast path skips the journal, never the expectations.
        let root = tmp("expect-fast-path");
        std::fs::write(root.join("doc.md"), "someone else's edit").unwrap();
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        cs.write("doc.md", "rewritten");
        assert_eq!(cs.len(), 1, "this test is about the fast path");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Drifted(_)),
            "expected Drifted, got {err:?}"
        );
        assert_eq!(
            read(&root, "doc.md").as_deref(),
            Some("someone else's edit")
        );
    }

    #[test]
    fn an_expectation_only_set_checks_without_writing() {
        // A set of zero ops and one expectation is an assertion about the
        // tree: Ok when it holds, Drifted when it does not, and no journal
        // either way.
        let root = tmp("expect-only");
        std::fs::write(root.join("doc.md"), "as read").unwrap();
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        assert!(!cs.is_empty(), "an expectation is staged state");
        block_on(cs.apply(&StdFs, &root)).unwrap();

        std::fs::write(root.join("doc.md"), "moved").unwrap();
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Drifted(_)),
            "expected Drifted, got {err:?}"
        );
        assert!(!Journal::default().path_in(&root).exists());
    }

    #[test]
    fn a_stale_journal_wins_over_a_drifted_expectation() {
        // An unrecovered change means the tree is mid-flight — not yet in any
        // state worth comparing against — so the stale refusal comes first.
        let root = tmp("expect-stale-first");
        std::fs::write(root.join("doc.md"), "drifted").unwrap();
        let prior = vec![FileOp::Write {
            path: "other.md".into(),
            bytes: b"prior".to_vec(),
        }];
        std::fs::write(
            Journal::default().path_in(&root),
            crate::journal::encode(&prior).unwrap(),
        )
        .unwrap();
        let mut cs = ChangeSet::new();
        cs.expect("doc.md", "as read");
        cs.write("doc.md", "rewritten");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::StaleJournal(_)),
            "expected StaleJournal, got {err:?}"
        );
    }

    #[test]
    fn recovery_never_rechecks_a_committed_sets_expectations() {
        // Expectations are not journaled: the commit point asserts they held.
        // A recovered tree would fail its own set's expectations by
        // construction — here, the crash landed the very write whose absence
        // the set expected — and recovery must complete it regardless.
        let root = tmp("expect-recovery");
        let mut cs = ChangeSet::new();
        cs.expect_absent("new.md");
        cs.write("new.md", "mine");
        cs.write("index.md", "names it");

        // The journal the real apply committed (its encoding carries no
        // expectations to recheck), and a crash after the first write.
        std::fs::write(
            Journal::default().path_in(&root),
            crate::journal::encode(cs.ops()).unwrap(),
        )
        .unwrap();
        std::fs::write(root.join("new.md"), "mine").unwrap();

        let outcome = block_on(crate::journal::recover(&StdFs, &root)).unwrap();
        assert_eq!(outcome, crate::journal::Recovered::Applied(2));
        assert_eq!(read(&root, "index.md").as_deref(), Some("names it"));
    }

    #[test]
    fn an_escaping_expectation_path_is_refused() {
        // An expectation reads; a set must no more probe outside the root
        // than write there.
        let root = tmp("expect-escape");
        let mut cs = ChangeSet::new();
        cs.expect("../secret.md", "sniffed");
        cs.write("doc.md", "cover");
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Escape(_)),
            "expected Escape, got {err:?}"
        );
        assert_eq!(read(&root, "doc.md"), None);
    }

    #[test]
    fn extend_carries_expectations_along() {
        let root = tmp("expect-extend");
        std::fs::write(root.join("doc.md"), "moved").unwrap();
        let mut guarded = ChangeSet::new();
        guarded.expect("doc.md", "as read");
        guarded.write("doc.md", "rewritten");
        let mut cs = ChangeSet::new();
        cs.write("index.md", "names it");
        cs.extend(guarded);
        assert_eq!(cs.expected().len(), 1);
        let err = block_on(cs.apply(&StdFs, &root)).unwrap_err();
        assert!(
            matches!(err, Error::Drifted(_)),
            "expected Drifted, got {err:?}"
        );
        assert_eq!(read(&root, "index.md"), None);
    }

    #[test]
    fn staged_ops_are_readable_without_applying() {
        // The dry-run view: a set describes writes without performing them.
        let root = tmp("dry-run");
        let mut cs = ChangeSet::new();
        cs.write("child.md", "child");
        cs.remove("old.md");
        assert_eq!(cs.len(), 2);
        assert_eq!(
            cs.ops().iter().map(FileOp::path).collect::<Vec<_>>(),
            [Path::new("child.md"), Path::new("old.md")]
        );
        assert_eq!(read(&root, "child.md"), None);
    }
}
