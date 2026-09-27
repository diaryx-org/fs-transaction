//! The storage port as the proofs see it: one wrapper per call the executor
//! makes, each carrying the port contract as a spec over a ghost model of the
//! tree.
//!
//! This module is the trusted boundary. Everything the executor in
//! [`crate::change`] and [`crate::journal`] does to the tree goes through a
//! function here, and Verus checks the executor against these specs — not
//! against the [`Storage`] implementations, which it cannot see. A wrapper's
//! body is the one call it names, plus the error handling that call already
//! had; its spec is what [`Storage`]'s documentation promises that call does.
//! A backend that breaks its contract breaks the proofs with it.
//!
//! The model ([`Fs`]) maps each *file* — the tree's own identity for a path,
//! [`fid`] — to what it holds. What the proofs assume, and do not prove:
//!
//! - **The paths a set names are not nested.** Creating a parent directory
//!   changes the tree at the path's ancestors, and renaming a directory
//!   changes what is under it; the specs say so ([`ancestor`]), and the
//!   executor is verified on a set of paths none of which is another's
//!   ancestor. For a journaled set, the replayability rule checks this on the
//!   names; that the tree nests no two paths the names keep apart is assumed.
//! - **Scratch names are the crate's.** The journal, a replacement's staging
//!   sibling, and an aside are [`scratch`]; the proofs assume a set names none
//!   of them.
//! - **`read_link` answers truly.** Whether a path holds a link is what
//!   `read_link` says, where it says anything.

// The model names files by `PathBuf`, and spec code cannot follow the deref
// from `&PathBuf` to `&Path`, so the wrappers take the owned type's reference.
#![allow(clippy::ptr_arg)]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::error::{Error, Result};
use crate::fs::Storage;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub(crate) use crate::replayable::proof::{Content, Fs, Op, entry, is_dir, is_link, present};

#[cfg(verus_keep_ghost)]
verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPath(Path);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPathBuf(PathBuf);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExError(Error);

/// The file a path names.
pub(crate) uninterp spec fn fid(p: PathBuf) -> int;

/// The file a root-relative path names under `root`.
pub(crate) uninterp spec fn at(root: &Path, rel: PathBuf) -> int;

/// A link's target, as what the link holds.
pub(crate) uninterp spec fn tid(target: PathBuf) -> int;

/// Whether file `a` is a directory above file `b`.
pub(crate) uninterp spec fn ancestor(a: int, b: int) -> bool;

/// Whether a file is one of the crate's own: a journal, a staging sibling,
/// an aside.
pub(crate) uninterp spec fn scratch(x: int) -> bool;

/// A set of files the executor can be verified on: none above another, none
/// the crate's own.
pub(crate) open spec fn sound(keys: Set<int>) -> bool {
    &&& forall|a: int, b: int| keys.contains(a) && keys.contains(b) ==> !#[trigger] ancestor(a, b)
    &&& forall|a: int| keys.contains(a) ==> !#[trigger] scratch(a)
}

/// `a` and `b` agree on every file in `keys`.
pub(crate) open spec fn agree(keys: Set<int>, a: Fs, b: Fs) -> bool {
    forall|x: int| keys.contains(x) ==> #[trigger] entry(a, x) == entry(b, x)
}

/// Nothing changed but what is at `p`, and scratch.
pub(crate) open spec fn only_at(old: Fs, new: Fs, p: int) -> bool {
    forall|x: int| x != p && !scratch(x) ==> #[trigger] entry(new, x) == entry(old, x)
}

/// Nothing changed but what is above `p`.
pub(crate) open spec fn only_above(old: Fs, new: Fs, p: int) -> bool {
    forall|x: int| !ancestor(x, p) ==> #[trigger] entry(new, x) == entry(old, x)
}

pub(crate) open spec fn two_slot(op: crate::FileOp) -> bool {
    op is Rename || op is CopyFrom
}

/// An op as the proofs model it, with its paths resolved under `root`.
pub(crate) open spec fn model(root: &Path, op: crate::FileOp) -> Op {
    match op {
        crate::FileOp::Write { path, bytes } => Op {
            act: crate::replayable::Act::Write,
            path: at(root, path),
            other: 0,
            bytes: bytes@,
            target: 0,
        },
        crate::FileOp::CopyFrom { path, source } => Op {
            act: crate::replayable::Act::CopyFrom,
            path: at(root, path),
            other: at(root, source),
            bytes: Seq::empty(),
            target: 0,
        },
        crate::FileOp::Remove { path } => Op {
            act: crate::replayable::Act::Remove,
            path: at(root, path),
            other: 0,
            bytes: Seq::empty(),
            target: 0,
        },
        crate::FileOp::Rename { from, to } => Op {
            act: crate::replayable::Act::Rename,
            path: at(root, from),
            other: at(root, to),
            bytes: Seq::empty(),
            target: 0,
        },
        crate::FileOp::SetExecutable { path, .. } => Op {
            act: crate::replayable::Act::SetExecutable,
            path: at(root, path),
            other: 0,
            bytes: Seq::empty(),
            target: 0,
        },
        crate::FileOp::SetLink { path, target } => Op {
            act: crate::replayable::Act::SetLink,
            path: at(root, path),
            other: 0,
            bytes: Seq::empty(),
            target: tid(target),
        },
    }
}

/// The files an op names.
pub(crate) open spec fn names(root: &Path, op: crate::FileOp, keys: Set<int>) -> bool {
    let m = model(root, op);
    keys.contains(m.path) && ((m.act is Rename || m.act is CopyFrom) ==> keys.contains(m.other))
}

pub(crate) open spec fn models(root: &Path, ops: Seq<crate::FileOp>) -> Seq<Op> {
    Seq::new(ops.len(), |i: int| model(root, ops[i]))
}

/// Replay reads and writes only the files an op names, so two trees that
/// agree on those files replay alike there.
pub(crate) proof fn lemma_replay_congruent(keys: Set<int>, a: Fs, b: Fs, op: Op)
    requires
        agree(keys, a, b),
        keys.contains(op.path),
        (op.act is Rename || op.act is CopyFrom) ==> keys.contains(op.other),
    ensures
        crate::replayable::proof::replay_step(a, op) is Some
            <==> crate::replayable::proof::replay_step(b, op) is Some,
        crate::replayable::proof::replay_step(a, op) is Some ==> agree(
            keys,
            crate::replayable::proof::replay_step(a, op)->Some_0,
            crate::replayable::proof::replay_step(b, op)->Some_0,
        ),
{
    assert(entry(a, op.path) == entry(b, op.path));
    if op.act is Rename || op.act is CopyFrom {
        assert(entry(a, op.other) == entry(b, op.other));
    }
    if crate::replayable::proof::replay_step(a, op) is Some {
        let (ra, rb) = (
            crate::replayable::proof::replay_step(a, op)->Some_0,
            crate::replayable::proof::replay_step(b, op)->Some_0,
        );
        assert forall|x: int| keys.contains(x) implies #[trigger] entry(ra, x) == entry(rb, x) by {
            assert(entry(a, x) == entry(b, x));
        }
    }
}

} // verus!

/// `root.join(rel)`.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures fid(r) == at(root, *rel)))]
pub(crate) fn join(root: &Path, rel: &PathBuf) -> PathBuf {
    root.join(rel)
}

/// Record that `full`'s directory owes a flush.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) fn note_parent(touched: &mut BTreeSet<PathBuf>, full: &PathBuf) {
    if let Some(dir) = crate::fs::parent_dir(full) {
        touched.insert(dir.to_path_buf());
    }
}

/// Create whatever directories `full` needs, recording them as owed a flush.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        only_above(*old(tree), *final(tree), fid(*full)),
))]
pub(crate) async fn ensure_parent<FS: Storage>(
    fs: &FS,
    full: &PathBuf,
    touched: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    if let Some(dir) = crate::fs::parent_dir(full) {
        for made in crate::fs::create_dir_all_traced(fs, dir).await? {
            touched.insert(made);
        }
    }
    Ok(())
}

/// [`Storage::replace`]: the bytes land whole, or the target is untouched.
/// Nothing replaces a directory.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        only_at(*old(tree), *final(tree), fid(*full)),
        r is Ok ==> !is_dir(*old(tree), fid(*full))
            && entry(*final(tree), fid(*full)) == Some(Content::File(bytes@)),
        r is Err ==> entry(*final(tree), fid(*full)) == entry(*old(tree), fid(*full)),
))]
pub(crate) async fn replace<FS: Storage>(fs: &FS, full: &PathBuf, bytes: &Vec<u8>) -> Result<()> {
    Ok(fs.replace(full, bytes).await?)
}

/// What a replacement leaves owed: its parent's entry, and on a backend that
/// cannot replace atomically its bytes.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) async fn settle_write<FS: Storage>(
    fs: &FS,
    full: &PathBuf,
    touched: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    crate::change::settle_write_debt(fs, full, touched).await
}

/// Read a copy's source, as recovery does: a failure is recovery's to report.
/// A read fails on nothing and on a directory, and reads through a link.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&Fs>
    ensures
        r is Ok ==> tree.contains_key(fid(*source)) && !is_dir(*tree, fid(*source))
            && (tree[fid(*source)] is File ==> r->Ok_0@ == tree[fid(*source)]->File_0),
))]
pub(crate) async fn read_source<FS: Storage>(
    fs: &FS,
    full: &PathBuf,
    source: &PathBuf,
) -> Result<Vec<u8>> {
    fs.read(source).await.map_err(|e| {
        Error::Recovery(format!(
            "cannot copy {} from {} — {e}",
            full.display(),
            source.display()
        ))
    })
}

/// Remove what is at `full`, where something is: nothing there is success.
/// A directory is not removed.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        only_at(*old(tree), *final(tree), fid(*full)),
        r is Ok ==> !is_dir(*old(tree), fid(*full)) && !final(tree).contains_key(fid(*full)),
        r is Err ==> entry(*final(tree), fid(*full)) == entry(*old(tree), fid(*full)),
))]
pub(crate) async fn remove_if_there<FS: Storage>(fs: &FS, full: &PathBuf) -> Result<()> {
    match fs.remove_file(full).await {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(e.into()),
        _ => Ok(()),
    }
}

/// Whether a link stands at `full`.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&Fs>
    ensures
        r == is_link(*tree, fid(*full)),
))]
pub(crate) async fn holds_link<FS: Storage>(fs: &FS, full: &PathBuf) -> bool {
    matches!(fs.read_link(full).await, Ok(Some(_)))
}

/// [`ReadStorage::try_exists`](crate::fs::ReadStorage::try_exists): through a
/// link, the referent's answer, which the model does not hold.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&Fs>
    ensures
        r is Ok && !is_link(*tree, fid(*full)) ==> r->Ok_0 == present(*tree, fid(*full)),
))]
pub(crate) async fn exists<FS: Storage>(fs: &FS, full: &PathBuf) -> Result<bool> {
    Ok(fs.try_exists(full).await?)
}

/// [`Storage::set_executable`], then a barrier on the inode while its name
/// still resolves. What a file holds does not change.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        *final(tree) == *old(tree),
))]
pub(crate) async fn set_executable<FS: Storage>(
    fs: &FS,
    full: &PathBuf,
    executable: bool,
) -> Result<()> {
    fs.set_executable(full, executable).await?;
    Ok(fs.sync(full, crate::fs::Durability::Ordered).await?)
}

/// [`Storage::set_link`]: the link replaces whatever is there, and a failure
/// may leave the path empty. Nothing replaces a directory.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        only_at(*old(tree), *final(tree), fid(*full)),
        r is Ok ==> !is_dir(*old(tree), fid(*full))
            && entry(*final(tree), fid(*full)) == Some(Content::Link(tid(*target))),
))]
pub(crate) async fn set_link<FS: Storage>(fs: &FS, full: &PathBuf, target: &PathBuf) -> Result<()> {
    Ok(fs.set_link(full, target).await?)
}

/// [`Storage::rename`]: the entry moves, replacing any file or link at the
/// destination; a directory's contents move with it. Nothing is renamed onto
/// a directory.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    with Tracked(tree): Tracked<&mut Fs>
    ensures
        forall|x: int| x != fid(*from) && x != fid(*to) && !scratch(x)
            && !ancestor(fid(*from), x) && !ancestor(fid(*to), x)
            ==> #[trigger] entry(*final(tree), x) == entry(*old(tree), x),
        r is Ok ==> old(tree).contains_key(fid(*from)) && !is_dir(*old(tree), fid(*to))
            && (fid(*from) != fid(*to) ==> !final(tree).contains_key(fid(*from)))
            && entry(*final(tree), fid(*to)) == entry(*old(tree), fid(*from)),
        r is Err ==> entry(*final(tree), fid(*from)) == entry(*old(tree), fid(*from))
            && entry(*final(tree), fid(*to)) == entry(*old(tree), fid(*to)),
))]
pub(crate) async fn rename<FS: Storage>(fs: &FS, from: &PathBuf, to: &PathBuf) -> Result<()> {
    Ok(fs.rename(from, to).await?)
}

/// The error for an execute-bit flip that would land through a link.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) fn flip_through_link(full: &PathBuf) -> Error {
    Error::Io(std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        format!(
            "refusing to set the execute bit through the symbolic link at {}",
            full.display()
        ),
    ))
}

/// The error for a rename recovery finds neither side of.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) fn rename_lost(from: &PathBuf, to: &PathBuf) -> Error {
    Error::Recovery(format!(
        "neither {} nor {} exists — cannot complete the rename",
        from.display(),
        to.display()
    ))
}
