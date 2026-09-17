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
//! ahead of everything after it: each tier's files are
//! [pushed](Durability::Pushed) to the device, each directory that gained an
//! entry is pushed too — since a name in a directory is its own write and
//! persists separately from the bytes it names — and then **one** barrier
//! orders the lot. A barrier speaks for everything the device has been
//! handed, so a tier of `N` files in `D` directories costs `N + D` pushes
//! and one barrier, not `N + D` barriers; on a platform where a push is
//! `fsync(2)` and a barrier is a queue command, that is most of the cost of
//! landing a large tier. The final tier is pushed and capped to whatever
//! `finality` the caller asks — [`Durable`](Durability::Durable) for "this
//! write survives power loss", [`Ordered`](Durability::Ordered) for
//! "consistent, but the tail may be lost with the crash that interrupted
//! it", [`Pushed`](Durability::Pushed) for "handed over, and the barrier is
//! mine to issue".
//!
//! A crash therefore leaves **some prefix of the barriers**: every tier
//! before the interruption whole and durable, the interrupted tier possibly
//! partial, everything after it absent. For the store shaped as above, every
//! one of those states is a state it already tolerates.
//!
//! ## What a partial tier can hold
//!
//! Nothing orders the files of one tier against each other — that is what
//! "within a tier nothing is ordered" means, and the pushes do not change
//! it. So the interrupted tier is not "the first `k` files whole and the
//! rest absent": **any** of its files may be present, absent, or partial,
//! independently. The two op kinds degrade differently inside it, and the
//! difference is the port's, honestly inherited:
//!
//! - A [`write`](OrderedBatch::write) lands through the backend's own
//!   [`Storage::replace`] — its override included — so a crash shows the
//!   whole old file or the whole new one wherever the backend can promise
//!   that, and the documented degrade where it cannot. That one barrier is
//!   `replace`'s own, not the tier's: a rename must never overtake the bytes
//!   it publishes, and no push can say so. The entry that publishes them is
//!   the tier's directory push to carry.
//! - A [`create_new`](OrderedBatch::create_new) is an exclusive create under
//!   its final name — decision-grade for concurrency (two writers racing to
//!   one name see one winner), but a crash can leave **any number** of the
//!   interrupted tier's files **torn**, not just the one in flight, since
//!   nothing orders them and the one barrier that would have was never
//!   reached. A consumer whose names promise their contents (a digest-named
//!   blob) must be able to recognize and discard every torn file nothing
//!   names yet; the barrier guarantees the "nothing names it yet" half.
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
    /// each tier's files and freshly-named directories are
    /// [pushed](Durability::Pushed) and then ordered
    /// ([`Ordered`](Durability::Ordered)) by one barrier at the root before
    /// the next tier begins, and the last tier is pushed and capped to
    /// `finality`.
    ///
    /// `finality` is the strength of the batch's own landing:
    /// [`Durable`](Durability::Durable) makes "this call returned" mean "this
    /// batch survives a power cut", [`Ordered`](Durability::Ordered) makes it
    /// mean only "no crash shows a later tier without an earlier one" — the
    /// batch itself may vanish with the crash, wholly or from some barrier
    /// on, and for a caller that treats its tree as append-only that is often
    /// enough, at the cost of not one `Durable` request anywhere.
    /// [`Pushed`](Durability::Pushed) makes it mean only "every earlier tier
    /// is ordered ahead of the last, and the last has been handed to the
    /// device": no barrier closes the batch, so what follows it is not
    /// ordered after it until the caller issues one — the shape for a
    /// caller landing a set one batch at a time that will
    /// [`sync`](Storage::sync) `Ordered` once at the end. (Whether a request
    /// is literally a push, a barrier, or a drain is the backend's affair:
    /// without `barrier-fsync`, `StdFs` answers `Ordered` with the full
    /// flush — stronger than asked, as ever.)
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
/// Files first, in staged order; then one push per file that still owes one;
/// then one push per directory an op landed in (gained a name or not — an
/// extra push on an unchanged directory costs less than proving it
/// unchanged); then one cap at the root, which is where the tier's ordering
/// actually comes from. Nothing within a tier is ordered, the pushes
/// included — the cap orders the whole tier against what follows, and a
/// name published in the tier is ordered ahead of nothing but the next tier.
/// The directory pushes still come after the files' because the order is
/// deterministic and the reading is the natural one, not because it buys
/// anything.
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
            // bytes are barriered inside the call — that one is `replace`'s
            // own, since a rename must never overtake the bytes it
            // publishes; the rename-published entry rides on the tier's
            // directory push, and a backend that cannot replace atomically
            // leaves its plainly-written bytes as an extra debt for the same
            // pass.
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
    // The tier's whole debt in one pass: every file that still owes a flush
    // and every directory that publishes a name, each handed over, then one
    // cap at the root that speaks for all of them — a barrier for an
    // `Ordered` tier, a drain for a `Durable` one. N + D pushes and one
    // barrier, where a barrier per debt would be N + D barriers: the pairing
    // [`Durability`] documents, cashed in. A `Pushed` finality caps nothing —
    // the tier is handed over, and the barrier is the caller's to issue.
    Ok(crate::fs::flush_all(fs, flush.into_iter().chain(dirs), root, need).await?)
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
        // The protocol, pinned event by event: tier files pushed, their
        // directories pushed after them, one barrier at the root to order
        // the lot — and only the last tier sees the caller's finality.
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
                FsEvent::Sync(root.join("blobs/a"), Durability::Pushed),
                // `blobs` gained the entry; the root gained `blobs`, and owes
                // a push too — but it is the anchor, so the barrier that
                // caps the tier is its push as well.
                FsEvent::Sync(root.join("blobs"), Durability::Pushed),
                FsEvent::Sync(root.clone(), Durability::Ordered),
                FsEvent::CreateNew(root.join("rev")),
                // The `Durable` tier is pushes capped by one drain — the
                // pairing, cashed in: the drain at the end carries
                // everything pushed before it.
                FsEvent::Sync(root.join("rev"), Durability::Pushed),
                FsEvent::Sync(root.clone(), Durability::Durable),
            ]
        );
    }

    #[test]
    fn a_tier_costs_a_push_per_debt_and_one_barrier() {
        // The saving, pinned by count: a tier of N creates across D
        // directories is N + D pushes and exactly one barrier, never N + D
        // barriers. The root is the anchor, so when it is among the D its
        // push and the barrier are one call.
        let root = tmp("push-count");
        std::fs::create_dir_all(root.join("blobs")).unwrap();
        std::fs::create_dir_all(root.join("ops")).unwrap();
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        for i in 0..5 {
            batch.create_new(format!("blobs/{i}"), "payload");
        }
        for i in 0..3 {
            batch.create_new(format!("ops/{i}"), "op");
        }
        batch.barrier();
        batch.create_new("rev", "names them all");
        block_on(batch.apply(&fs, &root, Durability::Ordered)).unwrap();

        let syncs = |need: Durability| -> Vec<PathBuf> {
            fs.events()
                .iter()
                .filter_map(|e| match e {
                    FsEvent::Sync(p, n) if *n == need => Some(p.clone()),
                    _ => None,
                })
                .collect()
        };
        // First tier: 8 files + 2 directories, none of them the root.
        // Second tier: 1 file; its directory is the root, folded into the
        // cap. 8 + 2 + 1 = 11 pushes.
        assert_eq!(syncs(Durability::Pushed).len(), 11, "{:?}", fs.events());
        // One barrier per tier, both at the root.
        assert_eq!(
            syncs(Durability::Ordered),
            vec![root.clone(), root.clone()],
            "{:?}",
            fs.events()
        );
        assert!(syncs(Durability::Durable).is_empty(), "{:?}", fs.events());
        // And the barrier closes its tier: every push of tier one precedes
        // it, and the first event of tier two follows it.
        let events = fs.events();
        let first_barrier = events
            .iter()
            .position(|e| matches!(e, FsEvent::Sync(_, Durability::Ordered)))
            .unwrap();
        let rev = events
            .iter()
            .position(|e| matches!(e, FsEvent::CreateNew(p) if *p == root.join("rev")))
            .unwrap();
        assert_eq!(first_barrier, 8 + 8 + 2, "{events:?}");
        assert_eq!(rev, first_barrier + 1, "{events:?}");
    }

    #[test]
    fn a_pushed_finality_hands_the_last_tier_over_and_barriers_nothing() {
        // The shape for a caller landing a set one batch at a time: every
        // earlier tier is still barriered, the last is pushed and left for
        // the caller's own barrier — not one `Ordered` or `Durable` request
        // after the last tier's creates.
        let root = tmp("pushed-finality");
        let fs = RecordingFs::local();
        let mut batch = OrderedBatch::new();
        batch.create_new("blobs/a", "a");
        batch.barrier();
        batch.create_new("blobs/b", "b");
        block_on(batch.apply(&fs, &root, Durability::Pushed)).unwrap();

        assert_eq!(
            fs.events(),
            vec![
                FsEvent::CreateNew(root.join("blobs/a")),
                FsEvent::Sync(root.join("blobs/a"), Durability::Pushed),
                FsEvent::Sync(root.join("blobs"), Durability::Pushed),
                FsEvent::Sync(root.clone(), Durability::Ordered),
                FsEvent::CreateNew(root.join("blobs/b")),
                FsEvent::Sync(root.join("blobs/b"), Durability::Pushed),
                FsEvent::Sync(root.join("blobs"), Durability::Pushed),
            ]
        );
        assert_eq!(read(&root, "blobs/b").as_deref(), Some("b"));
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
