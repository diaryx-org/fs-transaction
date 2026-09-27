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
//! - a rename's source is written or flipped, if at all, only by ops before
//!   it, and never used after it; its destination is untouched before it, and
//!   after it only written or flipped, so it stays a file;
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

/// Why a set was refused, and at which op.
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
                "it renames a path an earlier op did more to than write or flip"
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
    match op {
        FileOp::Write { path, .. } => Shape::Write(key(path, names)),
        FileOp::CopyFrom { path, source } => Shape::CopyFrom(key(path, names), key(source, names)),
        FileOp::Remove { path } => Shape::Remove(key(path, names)),
        FileOp::Rename { from, to } => Shape::Rename(key(from, names), key(to, names)),
        FileOp::SetExecutable { path, .. } => Shape::SetExecutable(key(path, names)),
        FileOp::SetLink { path, .. } => Shape::SetLink(key(path, names)),
    }
}

/// An op with only what the rule reads: which kind it is, and the paths it
/// names.
pub(crate) enum Shape {
    Write(Vec<usize>),
    CopyFrom(Vec<usize>, Vec<usize>),
    Remove(Vec<usize>),
    Rename(Vec<usize>, Vec<usize>),
    SetExecutable(Vec<usize>),
    SetLink(Vec<usize>),
}

fn first_refusal(ops: &[Shape]) -> Result<(), (usize, Refusal)> {
    let mut i = 0;
    while i < ops.len() {
        let mut k = 0;
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

fn same(a: &[usize], b: &[usize]) -> bool {
    a == b
}

/// Whether `a` is a proper ancestor of `b`.
fn strictly_under(a: &[usize], b: &[usize]) -> bool {
    a.len() < b.len() && same(a, &b[..a.len()])
}

fn first(op: &Shape) -> &[usize] {
    match op {
        Shape::Write(p)
        | Shape::CopyFrom(p, _)
        | Shape::Remove(p)
        | Shape::Rename(p, _)
        | Shape::SetExecutable(p)
        | Shape::SetLink(p) => p,
    }
}

fn second(op: &Shape) -> Option<&[usize]> {
    match op {
        Shape::CopyFrom(_, s) | Shape::Rename(_, s) => Some(s),
        _ => None,
    }
}

fn mentions(op: &Shape, x: &[usize]) -> bool {
    same(first(op), x) || matches!(second(op), Some(s) if same(s, x))
}

/// `op` names `x` only to write it whole.
fn writes_only(op: &Shape, x: &[usize]) -> bool {
    match op {
        Shape::Write(p) => same(p, x),
        Shape::CopyFrom(p, s) => same(p, x) && !same(s, x),
        _ => false,
    }
}

/// `op` names `x` only in ways that leave a file there.
fn keeps_file(op: &Shape, x: &[usize]) -> bool {
    writes_only(op, x) || matches!(op, Shape::SetExecutable(p) if same(p, x))
}

/// `op` names `x` only to take the file away from it: removing it, or
/// renaming it somewhere else.
fn leaves(op: &Shape, x: &[usize]) -> bool {
    match op {
        Shape::Remove(p) => same(p, x),
        Shape::Rename(f, t) => same(f, x) && !same(t, x),
        _ => false,
    }
}

fn nested(a: &[usize], b: &[usize]) -> bool {
    strictly_under(a, b) || strictly_under(b, a)
}

fn nested_ops(a: &Shape, b: &Shape) -> bool {
    let (a1, b1) = (first(a), first(b));
    nested(a1, b1)
        || matches!(second(a), Some(a2) if nested(a2, b1))
        || matches!(second(b), Some(b2) if nested(a1, b2))
        || matches!((second(a), second(b)), (Some(a2), Some(b2)) if nested(a2, b2))
}

/// What op `i` requires of op `k` (which may be itself).
fn pair(ops: &[Shape], i: usize, k: usize) -> Option<Refusal> {
    let (a, b) = (&ops[i], &ops[k]);
    if nested_ops(a, b) {
        return Some(Refusal::Nested);
    }
    match a {
        Shape::Rename(f, t) => {
            if k == i && same(f, t) {
                Some(Refusal::RenameInPlace)
            } else if k < i && mentions(b, f) && !keeps_file(b, f) {
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
        Shape::SetExecutable(p) => {
            if k > i && mentions(b, p) && !keeps_file(b, p) && !leaves(b, p) {
                Some(Refusal::ExecutableFileChangedAfter)
            } else {
                None
            }
        }
        Shape::CopyFrom(p, s) => {
            if k == i && same(p, s) {
                Some(Refusal::CopyOntoItsSource)
            } else if k != i
                && mentions(b, s)
                && !matches!(b, Shape::CopyFrom(p2, s2) if same(s2, s) && !same(p2, s))
            {
                Some(Refusal::CopySourceChanged)
            } else {
                None
            }
        }
        _ => None,
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
        // Write somewhere, then move it into place, then make it runnable.
        assert_eq!(
            refuses(|c| {
                c.write("staged", "x");
                c.rename("staged", "bin/tool");
                c.set_executable("bin/tool", true);
            }),
            None
        );
        // Or make it runnable first: replay finds nothing left to flip.
        assert_eq!(
            refuses(|c| {
                c.write("staged", "x");
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
