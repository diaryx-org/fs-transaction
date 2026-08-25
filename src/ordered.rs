//! Ordered writes — durability and ordering without atomicity, for trees where
//! every prefix is a legal state.
//!
//! A [`ChangeSet`](crate::ChangeSet) buys all-or-nothing: a journal, rollback,
//! and a recovery precondition, because for the trees it serves a half-applied
//! set is illegal and must be impossible to observe. Not every tree is like
//! that. An append-only store — content-addressed blobs, operation logs, a
//! write-once history — declares *every partially-written batch legal*: files
//! that arrived without the record that names them are exactly what any
//! interrupted transfer leaves, and the format already has a name for that
//! state. Buying atomicity there pays for a journal to rule out states that
//! were never illegal, and worse, it plants that journal (and a
//! recover-before-read obligation) in a tree that never asked for either.
//!
//! What such a tree *does* need is narrower, and this module is exactly it:
//!
//! - **Ordering.** Nothing durable may name anything that is not durable yet.
//!   The record naming a payload must never survive a crash the payload did
//!   not — a store where it could would hold a name pointing at nothing,
//!   which *is* an illegal state.
//! - **Durability**, when asked for: once [`apply`](OrderedBatch::apply)
//!   returns, the batch survives a power cut.
//!
//! ## The protocol
//!
//! An [`OrderedBatch`] is tiers of writes separated by
//! [`barrier`](OrderedBatch::barrier)s. Within a tier nothing is ordered —
//! payloads may land in any order, because nothing names them yet. At each
//! barrier, everything staged so far is ordered ([`Durability::Ordered`])
//! ahead of everything after it: each tier's files are flushed to the barrier
//! and each directory that gained an entry is flushed too, since a name in a
//! directory is its own write and persists separately from the bytes it
//! names. The final tier is flushed to whatever `finality` the caller asks —
//! [`Durable`](Durability::Durable) for "this write survives power loss",
//! [`Ordered`](Durability::Ordered) for "consistent, but the tail may be
//! lost with the crash that interrupted it".
//!
//! A crash therefore leaves **some prefix of the barriers**: every tier
//! before the interruption whole and durable, the interrupted tier possibly
//! partial, everything after it absent. For the store shaped as above, every
//! one of those states is a state it already tolerates.
//!
//! ## What a partial tier can hold
//!
//! The two op kinds degrade differently inside the interrupted tier, and the
//! difference is the port's, honestly inherited:
//!
//! - A [`write`](OrderedBatch::write) lands through the backend's own
//!   [`Storage::replace`] — its override included — so a crash shows the
//!   whole old file or the whole new one wherever the backend can promise
//!   that, and the documented degrade where it cannot. Its flush rides with
//!   the tier's, like everything else here: the bytes are barriered inside
//!   the call, and the entry that publishes them is the directory flush's to
//!   carry.
//! - A [`create_new`](OrderedBatch::create_new) is an exclusive create under
//!   its final name — decision-grade for concurrency (two writers racing to
//!   one name see one winner), but a crash mid-write can leave the newest
//!   tier's file **torn**. A consumer whose names promise their contents
//!   (a digest-named blob) must be able to recognize and discard a torn
//!   file nothing names yet; the barrier guarantees the "nothing names it
//!   yet" half.
//!
//! ## What this does not do
//!
//! No journal, no rollback, no recovery step, no stale-journal refusal. An
//! error mid-apply returns immediately and the tree holds a consistent
//! prefix — the same shape a crash leaves — for the caller to complete,
//! retry, or garbage-collect on its own terms. Single writer, like everything
//! in this crate: two appliers against one tree race, and exclusivity beyond
//! one `create_new` name is the caller's to arrange.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::error::Result;
use crate::fs::{Durability, Storage, parent_dir};
use crate::path::guard_in_root;

/// One staged op of an [`OrderedBatch`]. Paths are **root-relative**, joined
/// onto the root at [`apply`](OrderedBatch::apply) time, exactly as
/// [`FileOp`](crate::FileOp)'s are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BatchOp {
    /// Write `bytes` to `path`, creating it (and any missing parent directory)
    /// or replacing it wholesale — through [`Storage::replace`], the backend's
    /// own protocol, override included, so the atomicity promise is exactly
    /// the backend's
    /// ([`atomic_replace`](crate::fs::Capabilities::atomic_replace)). Its
    /// durability is the tier's, batched with everything else's.
    Write {
        /// The file to write.
        path: PathBuf,
        /// Its full new contents.
        bytes: Vec<u8>,
    },
    /// Create `path`, which must not already exist, holding `bytes` — through
    /// [`Storage::create_new`], so the exclusivity is the backend's own.
    ///
    /// An occupied path surfaces as
    /// [`AlreadyExists`](std::io::ErrorKind::AlreadyExists) and stops the
    /// apply where it stands; what the collision *means* — a race lost
    /// harmlessly to a writer producing the same bytes, or a real conflict —
    /// is the caller's to decide, because only the caller knows whether its
    /// names promise their contents.
    CreateNew {
        /// The file to create.
        path: PathBuf,
        /// Its contents.
        bytes: Vec<u8>,
    },
}

impl BatchOp {
    /// The file this op lands at. What a dry run lists.
    pub fn path(&self) -> &Path {
        match self {
            BatchOp::Write { path, .. } | BatchOp::CreateNew { path, .. } => path,
        }
    }
}

/// Tiers of writes separated by barriers, applied in order by
/// [`apply`](OrderedBatch::apply): within a tier nothing is ordered, across a
/// [`barrier`](OrderedBatch::barrier) everything is.
///
/// Built the way a store writes: payloads and records staged into the tier
/// they belong to, a barrier wherever a later write will *name* an earlier
/// one. The batch is a value describing writes without performing them, so —
/// like a [`ChangeSet`](crate::ChangeSet) — it is equally the answer to "what
/// would this do?": [`tiers`](OrderedBatch::tiers) is the dry-run view, and it
/// is the same sequence `apply` executes.
///
/// ```
/// use fs_transaction::{OrderedBatch, InMemoryFs, exec::block_on};
/// use fs_transaction::fs::Durability;
/// use std::path::Path;
///
/// let mut batch = OrderedBatch::new();
/// batch.create_new("blobs/9f86d081", "payload");
/// batch.create_new("ops/3a7bd3e2.op", "op-document");
/// batch.barrier(); // nothing below may be seen without everything above
/// batch.create_new("revisions/50d858e0.rev", "the record naming both");
/// block_on(batch.apply(&InMemoryFs::new(), Path::new("store"), Durability::Durable))?;
/// # Ok::<(), fs_transaction::Error>(())
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OrderedBatch {
    tiers: Vec<Vec<BatchOp>>,
}

impl OrderedBatch {
    /// An empty batch.
    pub fn new() -> Self {
        Self::default()
    }

    /// Stage a write of `contents` to `path` (root-relative) in the current
    /// tier, creating or atomically replacing the file.
    pub fn write(&mut self, path: impl Into<PathBuf>, contents: impl Into<Vec<u8>>) -> &mut Self {
        self.stage(BatchOp::Write {
            path: path.into(),
            bytes: contents.into(),
        })
    }

    /// Stage an exclusive create of `path` (root-relative) holding `contents`
    /// in the current tier. See [`BatchOp::CreateNew`] for what an occupied
    /// path does to the apply.
    pub fn create_new(
        &mut self,
        path: impl Into<PathBuf>,
        contents: impl Into<Vec<u8>>,
    ) -> &mut Self {
        self.stage(BatchOp::CreateNew {
            path: path.into(),
            bytes: contents.into(),
        })
    }

    /// Close the current tier: everything staged so far must land before
    /// anything staged after this call. Adjacent barriers, and barriers at the
    /// edges, cost nothing — an empty tier orders nothing and is skipped.
    pub fn barrier(&mut self) -> &mut Self {
        if !self.tiers.last().is_none_or(Vec::is_empty) {
            self.tiers.push(Vec::new());
        }
        self
    }

    /// The staged tiers, in execution order. The dry-run view; a trailing
    /// empty tier from a final [`barrier`](OrderedBatch::barrier) never
    /// appears, since barriers only exist *between* writes.
    pub fn tiers(&self) -> &[Vec<BatchOp>] {
        match self.tiers.split_last() {
            Some((last, rest)) if last.is_empty() => rest,
            _ => &self.tiers,
        }
    }

    /// Whether nothing is staged — [`apply`](OrderedBatch::apply) would be a
    /// no-op.
    pub fn is_empty(&self) -> bool {
        self.tiers.iter().all(Vec::is_empty)
    }

    /// The number of staged ops, across every tier.
    pub fn len(&self) -> usize {
        self.tiers.iter().map(Vec::len).sum()
    }

    fn stage(&mut self, op: BatchOp) -> &mut Self {
        match self.tiers.last_mut() {
            Some(tier) => tier.push(op),
            None => self.tiers.push(vec![op]),
        }
        self
    }

    /// Execute every staged op against `fs`, rooted at `root`, tier by tier:
    /// each tier's files and freshly-named directories are flushed
    /// [`Ordered`](Durability::Ordered) before the next tier begins, and the
    /// last tier is flushed to `finality`.
    ///
    /// `finality` is the strength of the batch's own landing:
    /// [`Durable`](Durability::Durable) makes "this call returned" mean "this
    /// batch survives a power cut", [`Ordered`](Durability::Ordered) makes it
    /// mean only "no crash shows a later tier without an earlier one" — the
    /// batch itself may vanish with the crash, wholly or from some barrier
    /// on, and for a caller that treats its tree as append-only that is often
    /// enough, at the cost of not one `Durable` request anywhere. (Whether a
    /// request is literally a drain is the backend's affair: without
    /// `barrier-fsync`, `StdFs` answers even `Ordered` with the full flush —
    /// stronger than asked, as ever.)
    ///
    /// On an error the apply stops where it stands and the tree holds a
    /// consistent prefix — see the module docs for exactly what that means
    /// inside the interrupted tier. Every staged path is clamped to the root
    /// before anything is written, on the same terms as
    /// [`ChangeSet::apply`](crate::ChangeSet::apply).
    pub async fn apply<FS: Storage>(
        &self,
        fs: &FS,
        root: &Path,
        finality: Durability,
    ) -> Result<()> {
        for op in self.tiers.iter().flatten() {
            guard_in_root(op.path())?;
        }
        let tiers: Vec<&Vec<BatchOp>> = self.tiers.iter().filter(|t| !t.is_empty()).collect();
        let Some((last, earlier)) = tiers.split_last() else {
            return Ok(());
        };

        for tier in earlier {
            apply_tier(fs, root, tier, Durability::Ordered).await?;
        }
        apply_tier(fs, root, last, finality).await
    }
}

/// Land one tier and flush it to `need`.
///
/// Files first, in staged order; then one flush per file that still owes one;
/// then one flush per directory an op landed in (gained a name or not — an
/// extra barrier on an unchanged directory costs less than proving it
/// unchanged). The directory flushes come last because they are what publish
/// the tier's *names* — a name must never be ordered ahead of the bytes it
/// stands for.
async fn apply_tier<FS: Storage>(
    fs: &FS,
    root: &Path,
    tier: &[BatchOp],
    need: Durability,
) -> Result<()> {
    let atomic_replace = fs.capabilities().atomic_replace;
    // `BTreeSet` for a deterministic flush order — nothing correctness-shaped
    // hangs on it, but a deterministic apply is one a fault-injection test can
    // pin down.
    let mut dirs: BTreeSet<PathBuf> = BTreeSet::new();
    let mut flush: Vec<PathBuf> = Vec::new();

    for op in tier {
        let full = root.join(op.path());
        if let Some(dir) = parent_dir(&full) {
            dirs.insert(dir.to_path_buf());
            // Directories the op's path freshly mints are entries of their
            // own, each persisting separately from the file that prompted
            // them — so every one of them (and the pre-existing ancestor
            // that received the topmost new name) joins the tier's flush
            // list, or a power cut takes the whole chain back out from
            // under a durably-flushed file.
            for made in crate::fs::create_dir_all_traced(fs, dir).await? {
                dirs.insert(made);
            }
        }
        match op {
            // Through the backend's own `replace` — override included, so a
            // native atomic replacement (a locked in-memory swap, a
            // transactional store) is honored rather than bypassed. The
            // bytes are barriered inside the call; the rename-published
            // entry rides on the tier's directory flush, and a backend that
            // cannot replace atomically leaves its plainly-written bytes as
            // an extra debt for the same flush.
            BatchOp::Write { bytes, .. } => {
                fs.replace(&full, bytes).await?;
                if !atomic_replace {
                    flush.push(full);
                }
            }
            BatchOp::CreateNew { bytes, .. } => {
                fs.create_new(&full, bytes).await?;
                flush.push(full);
            }
        }
    }
    // The tier's whole debt in one pass: files first, then the directories
    // that publish their names. An `Ordered` tier is barriers throughout; a
    // `Durable` one is barriers capped by a single drain — the corollary
    // [`Durability::Ordered`] documents, cashed in.
    let debts = flush.into_iter().chain(dirs);
    match need {
        Durability::Ordered => {
            for path in debts {
                fs.sync(&path, Durability::Ordered).await?;
            }
            Ok(())
        }
        Durability::Durable => Ok(crate::fs::flush_all_durable(fs, debts, root).await?),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Error;
    use crate::exec::block_on;
    use crate::fs::{InMemoryFs, ReadStorage, StdFs};
    use crate::fs_faults::{FailAtWrite, FsEvent, RecordingFs};

    fn tmp(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("fstx-ordered-{name}"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn read(root: &Path, rel: &str) -> Option<String> {
        std::fs::read_to_string(root.join(rel)).ok()
    }

    #[test]
    fn lands_every_tier_in_order() {
        let root = tmp("apply");
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/payload", "bytes");
        batch.barrier();
        batch.create_new("revisions/rev", "names the payload");
        batch.write("bookmark", "points at the revision");
        block_on(batch.apply(&StdFs, &root, Durability::Durable)).unwrap();

        assert_eq!(read(&root, "blobs/payload").as_deref(), Some("bytes"));
        assert_eq!(
            read(&root, "revisions/rev").as_deref(),
            Some("names the payload")
        );
        assert_eq!(
            read(&root, "bookmark").as_deref(),
            Some("points at the revision")
        );
    }

    #[test]
    fn flushes_each_tier_to_the_barrier_and_the_last_to_finality() {
        // The protocol, pinned event by event: tier files flush `Ordered`
        // with their directory after them, and only the last tier sees the
        // caller's finality.
        let root = tmp("events");
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "a");
        batch.barrier();
        batch.create_new("rev", "names a");
        block_on(batch.apply(&fs, &root, Durability::Durable)).unwrap();

        assert_eq!(
            fs.events(),
            vec![
                FsEvent::CreateNew(root.join("blobs/a")),
                FsEvent::Sync(root.join("blobs/a"), Durability::Ordered),
                // The root is flushed too: it gained the `blobs` entry, and
                // a directory entry persists separately from what it names.
                FsEvent::Sync(root.clone(), Durability::Ordered),
                FsEvent::Sync(root.join("blobs"), Durability::Ordered),
                FsEvent::CreateNew(root.join("rev")),
                // The `Durable` tier is barriers capped by one drain — the
                // corollary, cashed in: the directory flush at the end
                // carries everything barriered before it.
                FsEvent::Sync(root.join("rev"), Durability::Ordered),
                FsEvent::Sync(root.clone(), Durability::Durable),
            ]
        );
    }

    #[test]
    fn a_freshly_minted_directory_chain_is_flushed_link_by_link() {
        // Every directory the op's path creates is an entry of its own — a
        // durable file inside a chain of unflushed names is a file a power
        // cut can orphan. The flush list must hold the whole chain plus the
        // pre-existing ancestor that received the topmost new name.
        let root = tmp("chain");
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        batch.create_new("a/b/c/blob", "bytes");
        block_on(batch.apply(&fs, &root, Durability::Durable)).unwrap();

        for dir in [
            root.clone(),
            root.join("a"),
            root.join("a/b"),
            root.join("a/b/c"),
        ] {
            assert!(
                fs.events()
                    .iter()
                    .any(|e| matches!(e, FsEvent::Sync(p, _) if *p == dir)),
                "{} never flushed; events: {:?}",
                dir.display(),
                fs.events()
            );
        }
        // Barriers throughout, capped by exactly one drain that makes them
        // all durable — which must therefore come last.
        let drains: Vec<usize> = fs
            .events()
            .iter()
            .enumerate()
            .filter(|(_, e)| matches!(e, FsEvent::Sync(_, Durability::Durable)))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(drains.len(), 1, "events: {:?}", fs.events());
        assert_eq!(
            drains[0],
            fs.events().len() - 1,
            "events: {:?}",
            fs.events()
        );
    }

    #[test]
    fn an_ordered_finality_never_drains_the_device() {
        // The cheap contract: consistent, but the tail may go with the crash.
        // Not one `Durable` request anywhere — writes included, since a
        // `replace`'s durability is the tier's to grant, and an `Ordered`
        // tier grants none.
        let root = tmp("ordered-finality");
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "a");
        batch.barrier();
        batch.create_new("rev", "names a");
        batch.write("bookmark", "points at rev");
        block_on(batch.apply(&fs, &root, Durability::Ordered)).unwrap();

        assert!(
            fs.events()
                .iter()
                .all(|e| !matches!(e, FsEvent::Sync(_, Durability::Durable))),
            "events: {:?}",
            fs.events()
        );
    }

    #[test]
    fn a_replaced_write_lands_through_the_backends_replace() {
        // Delegated, not re-implemented: over a backend that leaves the
        // default in place this is the familiar temp-sibling staging, and
        // its durability is the tier's single flush — not a per-file drain.
        let root = tmp("write-durable");
        std::fs::write(root.join("bookmark"), "old").unwrap();
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        batch.write("bookmark", "new");
        block_on(batch.apply(&fs, &root, Durability::Durable)).unwrap();

        let tmp_name = crate::fs::temp_sibling(&root.join("bookmark"));
        assert_eq!(
            fs.events(),
            vec![
                FsEvent::Write(tmp_name.clone()),
                FsEvent::Sync(tmp_name.clone(), Durability::Ordered),
                FsEvent::Rename(tmp_name, root.join("bookmark")),
                FsEvent::Sync(root.clone(), Durability::Durable),
            ]
        );
        assert_eq!(read(&root, "bookmark").as_deref(), Some("new"));
    }

    #[test]
    fn a_replaced_write_respects_a_backends_native_atomic_replace() {
        // The delegation is the point: `InMemoryFs` overrides `write_atomic`
        // with its locked single write, and its `rename` refuses to clobber —
        // a batch that re-implemented the temp-then-rename dance would fail
        // with AlreadyExists on exactly this, the commonest replace there is.
        let fs = InMemoryFs::new();
        block_on(fs.write(Path::new("store/bookmark"), b"old")).unwrap();
        let mut batch = OrderedBatch::new();
        batch.write("bookmark", "new");
        block_on(batch.apply(&fs, Path::new("store"), Durability::Durable)).unwrap();
        assert_eq!(
            block_on(fs.read_to_string(Path::new("store/bookmark"))).unwrap(),
            "new"
        );
    }

    #[test]
    fn an_error_leaves_a_consistent_prefix() {
        // The whole contract on one failure: everything before the barrier
        // stands, nothing after the failed op exists, and there is no journal
        // anywhere asking to be recovered.
        let root = tmp("prefix");
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "a");
        batch.barrier();
        batch.create_new("rev", "never lands");
        batch.create_new("after", "never reached");
        let err =
            block_on(batch.apply(&FailAtWrite::nth(1), &root, Durability::Durable)).unwrap_err();
        assert!(err.to_string().contains("disk full"), "{err}");

        assert_eq!(read(&root, "blobs/a").as_deref(), Some("a"));
        assert_eq!(read(&root, "rev"), None);
        assert_eq!(read(&root, "after"), None);
        assert!(
            !crate::journal::Journal::default().path_in(&root).exists(),
            "an ordered batch must never plant a journal"
        );
    }

    #[test]
    fn an_occupied_create_surfaces_already_exists_and_stops() {
        let root = tmp("occupied");
        std::fs::create_dir_all(root.join("blobs")).unwrap();
        std::fs::write(root.join("blobs/a"), "already here").unwrap();
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "different bytes");
        batch.barrier();
        batch.create_new("rev", "never lands");
        let err = block_on(batch.apply(&StdFs, &root, Durability::Durable)).unwrap_err();
        match err {
            Error::Io(e) => assert_eq!(e.kind(), std::io::ErrorKind::AlreadyExists),
            other => panic!("expected Io(AlreadyExists), got {other:?}"),
        }
        assert_eq!(read(&root, "blobs/a").as_deref(), Some("already here"));
        assert_eq!(read(&root, "rev"), None);
    }

    #[test]
    fn a_path_escaping_the_root_is_refused_before_anything_lands() {
        let root = tmp("escape");
        let mut batch = OrderedBatch::new();
        batch.create_new("fine", "fine");
        batch.barrier();
        batch.write("../outside", "never");
        let err = block_on(batch.apply(&StdFs, &root, Durability::Durable)).unwrap_err();
        assert!(matches!(err, Error::Escape(_)), "{err:?}");
        assert_eq!(
            read(&root, "fine"),
            None,
            "the guard must run before the first tier, not between tiers"
        );
    }

    #[test]
    fn barriers_at_the_edges_and_doubled_up_cost_nothing() {
        let mut batch = OrderedBatch::new();
        batch.barrier();
        batch.create_new("a", "a");
        batch.barrier();
        batch.barrier();
        batch.create_new("b", "b");
        batch.barrier();
        assert_eq!(batch.tiers().len(), 2);
        assert_eq!(batch.len(), 2);

        let fs = InMemoryFs::new();
        block_on(batch.apply(&fs, Path::new("root"), Durability::Durable)).unwrap();
        assert_eq!(
            block_on(fs.read_to_string(Path::new("root/a"))).unwrap(),
            "a"
        );
        assert_eq!(
            block_on(fs.read_to_string(Path::new("root/b"))).unwrap(),
            "b"
        );
    }

    #[test]
    fn an_empty_batch_applies_as_nothing() {
        let fs = RecordingFs::local();
        let batch = OrderedBatch::new();
        assert!(batch.is_empty());
        block_on(batch.apply(&fs, Path::new("/nonexistent"), Durability::Durable)).unwrap();
        assert!(fs.events().is_empty());
    }

    #[test]
    fn works_over_a_backend_that_cannot_flush_at_all() {
        // `InMemoryFs` declines every sync; the batch still lands, it simply
        // carries no crash promise — the capabilities said so.
        let fs = InMemoryFs::new();
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "a");
        batch.barrier();
        batch.create_new("rev", "names a");
        block_on(batch.apply(&fs, Path::new("store"), Durability::Durable)).unwrap();
        assert_eq!(
            block_on(fs.read_to_string(Path::new("store/rev"))).unwrap(),
            "names a"
        );
    }
}
