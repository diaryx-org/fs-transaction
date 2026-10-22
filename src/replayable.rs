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
    first_refusal(&shapes, &order(&shapes))
}

/// Every path `ops` name, as an entry — `2 * i` for op `i`'s `path`, `2 * i +
/// 1` for its `other` — sorted by key. Only a hint: [`first_refusal`] checks
/// it before it relies on it.
fn order(ops: &[Shape]) -> Vec<usize> {
    let mut order = Vec::with_capacity(2 * ops.len());
    for (i, op) in ops.iter().enumerate() {
        order.push(2 * i);
        if two(op.act) {
            order.push(2 * i + 1);
        }
    }
    order.sort_by(|&a, &b| entry_key(ops, a).cmp(entry_key(ops, b)));
    order
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

/// The first op that breaks the rule, or none: for the lowest `i` with a pair
/// `(i, k)` refused, the refusal at the lowest such `k`.
///
/// A pair can only be refused where a path one op names is a path the other
/// names, or lies inside it, so of every pair of ops this compares only those:
/// each entry in `order` with the ones after it that its key is a prefix of,
/// which in key order follow it without a gap. That costs a sort of the paths
/// and the pairs that meet, rather than every pair. Should `order` not be
/// what [`order`] makes, it compares every pair.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r is Ok <==> proof::admissible(proof::views(ops@)),
))]
fn first_refusal(ops: &[Shape], order: &[usize]) -> Result<(), (usize, Refusal)> {
    // `_pos`, and `_q` below, are read only by the proof.
    let _pos = match place(ops, order) {
        Some(pos) => pos,
        None => return first_refusal_pairwise(ops),
    };
    let mut best: Option<(usize, usize, Refusal)> = None;
    // Each op against itself.
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= ops@.len(),
            proof::found(proof::views(ops@), best),
            forall|x: int| 0 <= x < i ==>
                #[trigger] proof::covered(proof::views(ops@), best, x, x),
        decreases ops@.len() - i,
    ))]
    while i < ops.len() {
        best = least(best, ops, i, i);
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(proof::selfs);
        reveal(proof::swept);
    }
    // Each entry against the ones after it inside its key.
    let mut p: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            p <= order@.len(),
            proof::placed(proof::views(ops@), order@, _pos@),
            proof::found(proof::views(ops@), best),
            proof::selfs(proof::views(ops@), best),
            proof::swept(proof::views(ops@), order@, best, p as int),
        decreases order@.len() - p,
    ))]
    while p < order.len() {
        let (next, _q) = scan(ops, order, p, best);
        #[cfg(verus_keep_ghost)]
        proof! {
            proof::lemma_swept_one_more(proof::views(ops@), order@, _pos@, best, next, p as int, _q as int);
        }
        best = next;
        p += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { proof::lemma_swept(proof::views(ops@), order@, _pos@, best); }
    match best {
        None => Ok(()),
        Some((i, _, refusal)) => Err((i, refusal)),
    }
}

/// [`least`] over the entry at `p` in `order` and each one after it that its
/// key is a prefix of, up to the first `q` that it is not.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        p < order@.len(),
        forall|x: int| 0 <= x < order@.len() ==> proof::valid(proof::views(ops@), #[trigger] order@[x] as int),
        proof::found(proof::views(ops@), best),
    ensures
        p < r.1 <= order@.len(),
        proof::found(proof::views(ops@), r.0),
        proof::grows(proof::views(ops@), best, r.0),
        forall|t: int| p < t < r.1 ==>
            #[trigger] proof::scanned(proof::views(ops@), order@, r.0, p as int, t),
        r.1 < order@.len() ==> !proof::prefix(
            proof::key(proof::views(ops@), order@[p as int] as int),
            proof::key(proof::views(ops@), order@[r.1 as int] as int),
        ),
))]
fn scan(
    ops: &[Shape],
    order: &[usize],
    p: usize,
    best: Option<(usize, usize, Refusal)>,
) -> (Option<(usize, usize, Refusal)>, usize) {
    let a = order[p];
    let mut least_yet = best;
    let mut q = p + 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            p < q <= order@.len(),
            a == order@[p as int],
            forall|x: int| 0 <= x < order@.len() ==> proof::valid(proof::views(ops@), #[trigger] order@[x] as int),
            proof::found(proof::views(ops@), least_yet),
            proof::grows(proof::views(ops@), best, least_yet),
            forall|t: int| p < t < q ==>
                #[trigger] proof::scanned(proof::views(ops@), order@, least_yet, p as int, t),
        decreases order@.len() - q,
    ))]
    loop {
        if q >= order.len() || !prefix(entry_key(ops, a), entry_key(ops, order[q])) {
            return (least_yet, q);
        }
        let b = order[q];
        let mut next = least(least_yet, ops, a / 2, b / 2);
        next = least(next, ops, b / 2, a / 2);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|t: int| p < t < q + 1 implies
                #[trigger] proof::scanned(proof::views(ops@), order@, next, p as int, t) by {
                if t < q {
                    assert(proof::scanned(proof::views(ops@), order@, least_yet, p as int, t));
                    assert(proof::covered(proof::views(ops@), next, order@[p as int] as int / 2, order@[t] as int / 2));
                    assert(proof::covered(proof::views(ops@), next, order@[t] as int / 2, order@[p as int] as int / 2));
                }
            }
        }
        least_yet = next;
        q += 1;
    }
}

/// `best`, or the refusal of the pair `(i, k)` if there is one and it comes
/// before `best`'s.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        i < ops@.len(),
        k < ops@.len(),
        proof::found(proof::views(ops@), best),
    ensures
        proof::found(proof::views(ops@), r),
        proof::covered(proof::views(ops@), r, i as int, k as int),
        forall|x: int, y: int| #[trigger] proof::covered(proof::views(ops@), r, x, y) <==
            proof::covered(proof::views(ops@), best, x, y),
))]
fn least(
    best: Option<(usize, usize, Refusal)>,
    ops: &[Shape],
    i: usize,
    k: usize,
) -> Option<(usize, usize, Refusal)> {
    match pair(ops, i, k) {
        None => best,
        Some(refusal) => match best {
            Some((bi, bk, _)) if bi < i || (bi == i && bk <= k) => best,
            _ => Some((i, k, refusal)),
        },
    }
}

/// Check that `order` lists every entry of `ops`, each in key order after the
/// last, and find each one in it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r matches Some(pos) ==> proof::placed(proof::views(ops@), order@, pos@),
))]
fn place(ops: &[Shape], order: &[usize]) -> Option<Vec<usize>> {
    if ops.len() > usize::MAX / 2 {
        return None;
    }
    let entries = 2 * ops.len();
    let mut pos: Vec<usize> = Vec::new();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries == 2 * ops@.len(),
            pos@.len() <= entries,
            forall|c: int| 0 <= c < pos@.len() ==> #[trigger] pos@[c] == usize::MAX,
        decreases entries - pos@.len(),
    ))]
    while pos.len() < entries {
        pos.push(usize::MAX);
    }
    let mut p: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries == 2 * ops@.len(),
            pos@.len() == entries,
            p <= order@.len(),
            forall|x: int| 0 <= x < p ==> proof::valid(proof::views(ops@), #[trigger] order@[x] as int),
            forall|x: int| 0 <= x && x + 1 < p ==> proof::lex_le(
                proof::key(proof::views(ops@), #[trigger] order@[x] as int),
                proof::key(proof::views(ops@), order@[x + 1] as int),
            ),
            forall|c: int| 0 <= c < entries && #[trigger] pos@[c] != usize::MAX ==>
                pos@[c] < p && order@[pos@[c] as int] == c,
        decreases order@.len() - p,
    ))]
    while p < order.len() {
        let c = order[p];
        if !valid_entry(ops, c) {
            return None;
        }
        if p > 0 && !lex_le(entry_key(ops, order[p - 1]), entry_key(ops, c)) {
            return None;
        }
        pos[c] = p;
        p += 1;
    }
    let mut c: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries == 2 * ops@.len(),
            pos@.len() == entries,
            c <= entries,
            forall|x: int| 0 <= x < order@.len() ==> proof::valid(proof::views(ops@), #[trigger] order@[x] as int),
            forall|x: int| 0 <= x && x + 1 < order@.len() ==> proof::lex_le(
                proof::key(proof::views(ops@), #[trigger] order@[x] as int),
                proof::key(proof::views(ops@), order@[x + 1] as int),
            ),
            forall|x: int| 0 <= x < entries && #[trigger] pos@[x] != usize::MAX ==>
                pos@[x] < order@.len() && order@[pos@[x] as int] == x,
            forall|x: int| 0 <= x < c && #[trigger] proof::valid(proof::views(ops@), x) ==>
                pos@[x] != usize::MAX,
        decreases entries - c,
    ))]
    while c < entries {
        if valid_entry(ops, c) && pos[c] == usize::MAX {
            return None;
        }
        c += 1;
    }
    Some(pos)
}

/// Whether `c` is an entry of `ops`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::valid(proof::views(ops@), c as int)))]
// `% 2`, because Verus has no specification for `is_multiple_of`.
#[allow(clippy::manual_is_multiple_of)]
fn valid_entry(ops: &[Shape], c: usize) -> bool {
    c / 2 < ops.len() && (c % 2 == 0 || two(ops[c / 2].act))
}

/// The key of entry `c`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        c / 2 < ops@.len(),
    ensures
        r@ == proof::key(proof::views(ops@), c as int),
))]
// `% 2`, because Verus has no specification for `is_multiple_of`.
#[allow(clippy::manual_is_multiple_of)]
fn entry_key(ops: &[Shape], c: usize) -> &Vec<usize> {
    if c % 2 == 0 {
        &ops[c / 2].path
    } else {
        &ops[c / 2].other
    }
}

/// Whether `a` comes no later than `b`, in the order of `Vec<usize>`'s `Ord`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::lex_le(a@, b@)))]
fn lex_le(a: &[usize], b: &[usize]) -> bool {
    let mut j: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            j <= a@.len(),
            j <= b@.len(),
            proof::lex_le(a@, b@) == proof::lex_le_from(a@, b@, j as int),
        decreases a@.len() - j,
    ))]
    while j < a.len() {
        if j >= b.len() {
            return false;
        }
        if a[j] != b[j] {
            return a[j] < b[j];
        }
        j += 1;
    }
    true
}

/// Whether `a` is `b`, or `b` lies inside it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == proof::prefix(a@, b@)))]
fn prefix(a: &[usize], b: &[usize]) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(a@.take(a@.len() as int) =~= a@);
        assert(b@.take(b@.len() as int) =~= b@);
    }
    same(a, b) || strictly_under(a, b)
}

/// [`first_refusal`] by comparing every op with every other.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r is Ok <==> proof::admissible(proof::views(ops@)),
))]
fn first_refusal_pairwise(ops: &[Shape]) -> Result<(), (usize, Refusal)> {
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
    fn the_refusal_reported_is_the_first() {
        // Op 0 is refused by op 1 and, for another reason, by op 2, which sorts
        // beside it; op 1 is refused by nothing earlier. The lowest op wins,
        // then the lowest op it is refused by.
        let mut set = crate::ChangeSet::new();
        set.rename("a", "b").remove("b").write("a", "x");
        assert_eq!(check(set.ops()), Err((0, Refusal::RenamedFileChangedAfter)));
        let mut set = crate::ChangeSet::new();
        set.rename("a", "tmp")
            .write("dir/x", "x")
            .rename("b", "a")
            .rename("tmp", "b")
            .rename("dir", "d");
        assert_eq!(check(set.ops()), Err((0, Refusal::RenameSourceUsedAfter)));
    }

    /// Shapes for `set`, as [`check`] makes them.
    fn shapes(set: &crate::ChangeSet) -> Vec<Shape> {
        let mut names = BTreeMap::new();
        set.ops().iter().map(|op| shape(op, &mut names)).collect()
    }

    #[test]
    fn sweeping_finds_what_comparing_every_pair_finds() {
        // Sets of up to eight ops over a few paths, some inside others and
        // some two spellings of one, so most sets have pairs that meet.
        const PATHS: &[&str] = &["a", "A", "a/b", "a/b/c", "b", "./b/../a", "c", "c/d"];
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |n: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % n as u64) as usize
        };
        let mut refused = 0;
        for _ in 0..20_000 {
            let mut set = crate::ChangeSet::new();
            for _ in 0..1 + next(8) {
                let (p, q) = (PATHS[next(PATHS.len())], PATHS[next(PATHS.len())]);
                match next(6) {
                    0 => set.write(p, "x"),
                    1 => set.copy_from(p, q),
                    2 => set.remove(p),
                    3 => set.rename(p, q),
                    4 => set.set_executable(p, true),
                    _ => set.set_link(p, q),
                };
            }
            let shapes = shapes(&set);
            let pairwise = first_refusal_pairwise(&shapes);
            refused += usize::from(pairwise.is_err());
            assert_eq!(
                first_refusal(&shapes, &order(&shapes)),
                pairwise,
                "{:?}",
                set.ops()
            );
        }
        // Both answers are exercised.
        assert!(
            (1_000..19_000).contains(&refused),
            "{refused} of 20,000 refused"
        );
    }

    #[test]
    fn an_order_that_is_not_one_compares_every_pair() {
        let mut set = crate::ChangeSet::new();
        set.rename("a", "tmp").rename("b", "a").rename("tmp", "b");
        let shapes = shapes(&set);
        let expected = Err((0, Refusal::RenameSourceUsedAfter));
        let sorted = order(&shapes);
        let mut reversed = sorted.clone();
        reversed.reverse();
        // Unsorted, missing an entry, or naming one there is not.
        for bad in [
            reversed,
            sorted[1..].to_vec(),
            [sorted.clone(), vec![99]].concat(),
        ] {
            assert_eq!(first_refusal(&shapes, &bad), expected);
        }
    }

    #[test]
    fn ops_on_unrelated_paths_are_not_compared() {
        // 20,000 ops, no two naming one path or one inside another: 400
        // million pairs for a check that compares every op with every other,
        // which a debug build takes many seconds over.
        let mut set = crate::ChangeSet::new();
        for n in 0..20_000 {
            set.write(format!("dir{}/file{n}.md", n % 100), "x");
        }
        let start = std::time::Instant::now();
        assert_eq!(check(set.ops()), Ok(()));
        let took = start.elapsed();
        assert!(
            took < std::time::Duration::from_secs(1),
            "checking 20,000 unrelated ops took {took:?}"
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
