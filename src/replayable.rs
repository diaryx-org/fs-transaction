//! Which sets a crash can be recovered from — the rule
//! [`Journal::apply`](crate::Journal::apply) holds a journaled set to before
//! its commit point.
//!
//! Recovery replays a journal from its first op, over whatever the crash left:
//! the tree before the set, after it, or anywhere between. Replaying an op
//! that already ran is harmless when the op overwrites blindly — a write, a
//! remove, a link — because whatever it lands, the later ops that ran after it
//! land again on top. It is not harmless when the op *reads* the tree:
//!
//! - a **rename** moves whatever is at its source, and is skipped only when the
//!   source is gone and the destination is there;
//! - an **execute-bit flip** flips whatever file is there, and is skipped when
//!   nothing is;
//! - a **copy** reads its source.
//!
//! Replayed over a tree that later ops have already changed, those reads see
//! the later state. A swap through a temporary name is undone; a rename whose
//! old path is written again moves the new file over the renamed one; a
//! remove of a rename's destination deletes the only copy of what was renamed
//! there. So a set is refused when a later op could change what an earlier
//! reading op reads, and accepted otherwise. The rules are in [`pair`]:
//!
//! - no path the set names lies inside another;
//! - a rename's source is, before it, at most flipped — never written, since
//!   replay would write it afresh where the apply wrote into the file that was
//!   there, and move a file without that file's mode — and never used after
//!   it; its destination is untouched before it, and after it only written or
//!   flipped, so it stays a file;
//! - a file whose execute bit is flipped is, afterwards, only written,
//!   flipped, removed, or renamed away — never replaced by a link, which
//!   replay would refuse to flip through;
//! - a copy's source is only ever read, by copies.
//!
//! Paths are compared the way the tree may see them: normalized, and without
//! regard to case, since a case-insensitive filesystem makes `A.md` and `a.md`
//! one file. Treating two paths as one when they are two can only refuse a
//! set that was safe, never accept one that was not. What is not caught is two
//! spellings that differ in Unicode normalization, which some filesystems also
//! treat as one file.

use std::collections::BTreeMap;
use std::path::Path;

use crate::change::FileOp;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub(crate) mod proof;

/// Why a set was refused, and at which op.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    Nested,
    RenameInPlace,
    RenameSourceChangedBefore,
    RenameSourceUsedAfter,
    RenameOntoUsed,
    RenamedFileChangedAfter,
    ExecutableFileChangedAfter,
    CopySourceChanged,
    CopyOntoItsSource,
}

impl Refusal {
    pub(crate) fn reason(self) -> &'static str {
        match self {
            Refusal::Nested => "it names a path inside another path the set names",
            Refusal::RenameInPlace => "it renames a file onto itself",
            Refusal::RenameSourceChangedBefore => {
                "it renames a path an earlier op did more to than flip its execute bit"
            }
            Refusal::RenameSourceUsedAfter => "it renames away from a path a later op uses again",
            Refusal::RenameOntoUsed => "it renames onto a path an earlier op already used",
            Refusal::RenamedFileChangedAfter => {
                "it renames a file that a later op removes, moves, or replaces with a link"
            }
            Refusal::ExecutableFileChangedAfter => {
                "it flips the execute bit of a file that a later op replaces with a link \
                 or renames something onto"
            }
            Refusal::CopySourceChanged => "it copies from a path another op changes",
            Refusal::CopyOntoItsSource => "it copies a file onto itself",
        }
    }
}

/// Check `ops` against the rule, returning the first op that breaks it.
pub(crate) fn check(ops: &[FileOp]) -> Result<(), (usize, Refusal)> {
    let mut names = BTreeMap::new();
    let shapes: Vec<Shape> = ops.iter().map(|op| shape(op, &mut names)).collect();
    first_refusal(&shapes)
}

/// A path as the rule compares it: its normalized components, each lowered
/// and interned, so two spellings of one path become one sequence.
fn key(path: &Path, names: &mut BTreeMap<String, usize>) -> Vec<usize> {
    crate::path::normalize(path)
        .components()
        .map(|c| {
            let name = c.as_os_str().to_string_lossy().to_lowercase();
            let next = names.len();
            *names.entry(name).or_insert(next)
        })
        .collect()
}

fn shape(op: &FileOp, names: &mut BTreeMap<String, usize>) -> Shape {
    let (act, path, other) = match op {
        FileOp::Write { path, .. } => (Act::Write, path, None),
        FileOp::CopyFrom { path, source } => (Act::CopyFrom, path, Some(source)),
        FileOp::Remove { path } => (Act::Remove, path, None),
        FileOp::Rename { from, to } => (Act::Rename, from, Some(to)),
        FileOp::SetExecutable { path, .. } => (Act::SetExecutable, path, None),
        FileOp::SetLink { path, .. } => (Act::SetLink, path, None),
    };
    Shape {
        act,
        path: key(path, names),
        other: other.map(|p| key(p, names)).unwrap_or_default(),
    }
}

/// Which kind of op.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) enum Act {
    Write,
    CopyFrom,
    Remove,
    Rename,
    SetExecutable,
    SetLink,
}

/// An op with only what the rule reads: which kind it is, and the paths it
/// names — `path` always (a rename's source, a copy's destination), `other`
/// for the two kinds that name a second (a rename's destination, a copy's
/// source).
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Shape {
    pub(crate) act: Act,
    pub(crate) path: Vec<usize>,
    pub(crate) other: Vec<usize>,
}

/// The first op that breaks the rule, or none.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r is Ok <==> proof::admissible(proof::views(ops@)),
))]
fn first_refusal(ops: &[Shape]) -> Result<(), (usize, Refusal)> {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= ops@.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < ops@.len() ==>
                (#[trigger] proof::pair_refusal(proof::views(ops@), x, y)) is None,
        decreases ops@.len() - i,
    ))]
    while i < ops.len() {
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                i < ops@.len(),
                k <= ops@.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < ops@.len() ==>
                    (#[trigger] proof::pair_refusal(proof::views(ops@), x, y)) is None,
                forall|y: int| 0 <= y < k ==>
                    (#[trigger] proof::pair_refusal(proof::views(ops@), i as int, y)) is None,
            decreases ops@.len() - k,
        ))]
        while k < ops.len() {
            if let Some(refusal) = pair(ops, i, k) {
                return Err((i, refusal));
            }
            k += 1;
        }
        i += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == (a@ == b@)))]
fn same(a: &[usize], b: &[usize]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut j: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            j <= a@.len(),
            a@.len() == b@.len(),
            forall|x: int| 0 <= x < j ==> a@[x] == b@[x],
        decreases a@.len() - j,
    ))]
    while j < a.len() {
        if a[j] != b[j] {
            return false;
        }
        j += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(a@ =~= b@); }
    true
}

/// Whether `a` is a proper ancestor of `b`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::under(a@, b@)))]
fn strictly_under(a: &[usize], b: &[usize]) -> bool {
    if a.len() >= b.len() {
        return false;
    }
    let mut j: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            j <= a@.len(),
            a@.len() < b@.len(),
            forall|x: int| 0 <= x < j ==> a@[x] == b@[x],
        decreases a@.len() - j,
    ))]
    while j < a.len() {
        if a[j] != b[j] {
            #[cfg(verus_keep_ghost)]
            proof! { assert(b@.take(a@.len() as int)[j as int] != a@[j as int]); }
            return false;
        }
        j += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(b@.take(a@.len() as int) =~= a@); }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::nested(a@, b@)))]
fn nested(a: &[usize], b: &[usize]) -> bool {
    strictly_under(a, b) || strictly_under(b, a)
}

/// Whether this kind of op names a second path.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::two(act)))]
fn two(act: Act) -> bool {
    matches!(act, Act::CopyFrom | Act::Rename)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::mentions(proof::view(op), x@)))]
fn mentions(op: &Shape, x: &[usize]) -> bool {
    same(&op.path, x) || (two(op.act) && same(&op.other, x))
}

/// `op` names `x` only to write it whole.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::writes_only(proof::view(op), x@)))]
fn writes_only(op: &Shape, x: &[usize]) -> bool {
    match op.act {
        Act::Write => same(&op.path, x),
        Act::CopyFrom => same(&op.path, x) && !same(&op.other, x),
        _ => false,
    }
}

/// `op` names `x` only to flip its execute bit.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::flips(proof::view(op), x@)))]
fn flips(op: &Shape, x: &[usize]) -> bool {
    match op.act {
        Act::SetExecutable => same(&op.path, x),
        _ => false,
    }
}

/// `op` names `x` only in ways that leave a file there.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::keeps_file(proof::view(op), x@)))]
fn keeps_file(op: &Shape, x: &[usize]) -> bool {
    writes_only(op, x)
        || match op.act {
            Act::SetExecutable => same(&op.path, x),
            _ => false,
        }
}

/// `op` names `x` only to take the file away from it: removing it, or
/// renaming it somewhere else.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::leaves(proof::view(op), x@)))]
fn leaves(op: &Shape, x: &[usize]) -> bool {
    match op.act {
        Act::Remove => same(&op.path, x),
        Act::Rename => same(&op.path, x) && !same(&op.other, x),
        _ => false,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures r == proof::nested_ops(proof::view(a), proof::view(b)),
))]
fn nested_ops(a: &Shape, b: &Shape) -> bool {
    nested(&a.path, &b.path)
        || (two(a.act) && nested(&a.other, &b.path))
        || (two(b.act) && nested(&a.path, &b.other))
        || (two(a.act) && two(b.act) && nested(&a.other, &b.other))
}

/// What op `i` requires of op `k` (which may be itself).
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        i < ops@.len(),
        k < ops@.len(),
    ensures
        r == proof::pair_refusal(proof::views(ops@), i as int, k as int),
))]
fn pair(ops: &[Shape], i: usize, k: usize) -> Option<Refusal> {
    let a = &ops[i];
    let b = &ops[k];
    if nested_ops(a, b) {
        return Some(Refusal::Nested);
    }
    match a.act {
        Act::Rename => {
            let (f, t) = (&a.path, &a.other);
            if k == i && same(f, t) {
                Some(Refusal::RenameInPlace)
            } else if k < i && mentions(b, f) && !flips(b, f) {
                Some(Refusal::RenameSourceChangedBefore)
            } else if k > i && mentions(b, f) {
                Some(Refusal::RenameSourceUsedAfter)
            } else if k < i && mentions(b, t) {
                Some(Refusal::RenameOntoUsed)
            } else if k > i && mentions(b, t) && !keeps_file(b, t) {
                Some(Refusal::RenamedFileChangedAfter)
            } else {
                None
            }
        }
        Act::SetExecutable => {
            let p = &a.path;
            if k > i && mentions(b, p) && !keeps_file(b, p) && !leaves(b, p) {
                Some(Refusal::ExecutableFileChangedAfter)
            } else {
                None
            }
        }
        Act::CopyFrom => {
            let (p, s) = (&a.path, &a.other);
            if k == i && same(p, s) {
                Some(Refusal::CopyOntoItsSource)
            } else if k != i && mentions(b, s) && !only_copies_from(b, s) {
                Some(Refusal::CopySourceChanged)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `op` names `s` only to copy from it, somewhere else.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::only_copies_from(proof::view(op), s@)))]
fn only_copies_from(op: &Shape, s: &[usize]) -> bool {
    match op.act {
        Act::CopyFrom => same(&op.other, s) && !same(&op.path, s),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refuses(build: impl Fn(&mut crate::ChangeSet)) -> Option<Refusal> {
        let mut set = crate::ChangeSet::new();
        build(&mut set);
        check(set.ops()).err().map(|(_, r)| r)
    }

    #[test]
    fn what_prov_stages_is_accepted() {
        // rename: the node and its body move, each is rewritten, and the files
        // linking in are rewritten.
        assert_eq!(
            refuses(|c| {
                c.rename("a.md", "b.md");
                c.write("b.md", "x");
                c.rename("a.body.md", "b.body.md");
                c.write("b.body.md", "x");
                c.write("index.md", "x");
                c.write("registry.md", "x");
            }),
            None
        );
        // delete: the file goes, and the log and the parent are written.
        assert_eq!(
            refuses(|c| {
                c.remove("a.md");
                c.write("deletions.md", "x");
                c.write("index.md", "x");
            }),
            None
        );
        // Removing a path and writing it again is two blind ops.
        assert_eq!(
            refuses(|c| {
                c.remove("deletions.md");
                c.write("deletions.md", "x");
            }),
            None
        );
        // Move a file into place, then write it and make it runnable.
        assert_eq!(
            refuses(|c| {
                c.rename("staged", "bin/tool");
                c.write("bin/tool", "x");
                c.set_executable("bin/tool", true);
            }),
            None
        );
        // Or make it runnable first: replay finds nothing left to flip.
        assert_eq!(
            refuses(|c| {
                c.set_executable("staged", true);
                c.rename("staged", "bin/tool");
            }),
            None
        );
    }

    #[test]
    fn what_replay_cannot_recover_is_refused() {
        assert_eq!(
            refuses(|c| {
                c.rename("a", "tmp");
                c.rename("b", "a");
                c.rename("tmp", "b");
            }),
            Some(Refusal::RenameSourceUsedAfter)
        );
        assert_eq!(
            refuses(|c| {
                c.rename("old", "new");
                c.write("old", "stub");
            }),
            Some(Refusal::RenameSourceUsedAfter)
        );
        assert_eq!(
            refuses(|c| {
                c.remove("b");
                c.rename("a", "b");
            }),
            Some(Refusal::RenameOntoUsed)
        );
        assert_eq!(
            refuses(|c| {
                c.rename("a", "b");
                c.rename("b", "c");
            }),
            Some(Refusal::RenamedFileChangedAfter)
        );
        assert_eq!(
            refuses(|c| {
                c.set_executable("run", true);
                c.set_link("run", "elsewhere");
            }),
            Some(Refusal::ExecutableFileChangedAfter)
        );
        // Replay would write `staged` afresh and move a file without the
        // mode the apply's write kept.
        assert_eq!(
            refuses(|c| {
                c.write("staged", "x");
                c.rename("staged", "bin/tool");
            }),
            Some(Refusal::RenameSourceChangedBefore)
        );
        assert_eq!(
            refuses(|c| {
                c.copy_from("a", "blob");
                c.remove("blob");
            }),
            Some(Refusal::CopySourceChanged)
        );
        assert_eq!(
            refuses(|c| {
                c.rename("dir", "moved");
                c.write("dir/a", "x");
            }),
            Some(Refusal::Nested)
        );
    }

    #[test]
    fn two_spellings_of_one_path_are_one_path() {
        assert_eq!(
            refuses(|c| {
                c.rename("notes/old.md", "new.md");
                c.write("notes/./OLD.md", "stub");
            }),
            Some(Refusal::RenameSourceUsedAfter)
        );
    }
}
