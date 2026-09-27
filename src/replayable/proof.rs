//! The proof that the rule in [`super`] is what it says, and that it is
//! enough: a set that passes it recovers from any crash by replaying from its
//! first op. Compiled only by Verus (`verus_keep_ghost`).

use vstd::prelude::*;
use super::{Act, Refusal, Shape};

verus! {

// ---- the rule, as the checker computes it ----

/// An op as the rule sees it: its kind and the key of each path it names.
pub(crate) struct SOp {
    pub(crate) act: Act,
    pub(crate) path: Seq<usize>,
    pub(crate) other: Seq<usize>,
}

pub(crate) open spec fn view(s: &Shape) -> SOp {
    SOp { act: s.act, path: s.path@, other: s.other@ }
}

pub(crate) open spec fn views(ops: Seq<Shape>) -> Seq<SOp> {
    Seq::new(ops.len(), |i: int| view(&ops[i]))
}

pub(crate) open spec fn two(act: Act) -> bool {
    act is CopyFrom || act is Rename
}

pub(crate) open spec fn under(a: Seq<usize>, b: Seq<usize>) -> bool {
    a.len() < b.len() && b.take(a.len() as int) == a
}

pub(crate) open spec fn nested(a: Seq<usize>, b: Seq<usize>) -> bool {
    under(a, b) || under(b, a)
}

pub(crate) open spec fn nested_ops(a: SOp, b: SOp) -> bool {
    nested(a.path, b.path) || (two(a.act) && nested(a.other, b.path)) || (two(b.act) && nested(
        a.path,
        b.other,
    )) || (two(a.act) && two(b.act) && nested(a.other, b.other))
}

pub(crate) open spec fn mentions(op: SOp, x: Seq<usize>) -> bool {
    op.path == x || (two(op.act) && op.other == x)
}

pub(crate) open spec fn writes_only(op: SOp, x: Seq<usize>) -> bool {
    match op.act {
        Act::Write => op.path == x,
        Act::CopyFrom => op.path == x && op.other != x,
        _ => false,
    }
}

pub(crate) open spec fn flips(op: SOp, x: Seq<usize>) -> bool {
    op.act is SetExecutable && op.path == x
}

pub(crate) open spec fn keeps_file(op: SOp, x: Seq<usize>) -> bool {
    writes_only(op, x) || (op.act is SetExecutable && op.path == x)
}

pub(crate) open spec fn leaves(op: SOp, x: Seq<usize>) -> bool {
    match op.act {
        Act::Remove => op.path == x,
        Act::Rename => op.path == x && op.other != x,
        _ => false,
    }
}

pub(crate) open spec fn only_copies_from(op: SOp, s: Seq<usize>) -> bool {
    op.act is CopyFrom && op.other == s && op.path != s
}

/// What op `i` requires of op `k`, and which requirement fails first.
pub(crate) open spec fn pair_refusal(ops: Seq<SOp>, i: int, k: int) -> Option<Refusal> {
    let (a, b) = (ops[i], ops[k]);
    if nested_ops(a, b) {
        Some(Refusal::Nested)
    } else {
        match a.act {
            Act::Rename => {
                let (f, t) = (a.path, a.other);
                if k == i && f == t {
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
            },
            Act::SetExecutable => {
                let p = a.path;
                if k > i && mentions(b, p) && !keeps_file(b, p) && !leaves(b, p) {
                    Some(Refusal::ExecutableFileChangedAfter)
                } else {
                    None
                }
            },
            Act::CopyFrom => {
                let (p, s) = (a.path, a.other);
                if k == i && p == s {
                    Some(Refusal::CopyOntoItsSource)
                } else if k != i && mentions(b, s) && !only_copies_from(b, s) {
                    Some(Refusal::CopySourceChanged)
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// The rule: no op refuses any other.
pub(crate) open spec fn admissible(ops: Seq<SOp>) -> bool {
    forall|i: int, k: int|
        0 <= i < ops.len() && 0 <= k < ops.len() ==> (#[trigger] pair_refusal(ops, i, k)) is None
}


// ---- what the tree holds, and what an apply and a replay do to it ----
//
// A tree is modeled by its contents: each path's file bytes or link target,
// or nothing. Paths are the rule's keys, so two keys are two files — the
// identity the rule assumes. Execute bits and permissions are not modeled:
// an execute-bit flip is a read here (it needs a file, and replay skips it
// where there is none), which is all the rule depends on.

pub(crate) enum Content {
    File(Seq<u8>),
    Link(Seq<u8>),
}

pub(crate) type Fs = Map<Seq<usize>, Content>;

/// An op with its payload: the bytes a write lands, the target a link names.
pub(crate) struct Op {
    pub(crate) act: Act,
    pub(crate) path: Seq<usize>,
    pub(crate) other: Seq<usize>,
    pub(crate) bytes: Seq<u8>,
    pub(crate) target: Seq<u8>,
}

pub(crate) open spec fn sop(op: Op) -> SOp {
    SOp { act: op.act, path: op.path, other: op.other }
}

pub(crate) open spec fn sops(ops: Seq<Op>) -> Seq<SOp> {
    Seq::new(ops.len(), |i: int| sop(ops[i]))
}

pub(crate) open spec fn entry(s: Fs, p: Seq<usize>) -> Option<Content> {
    if s.contains_key(p) {
        Some(s[p])
    } else {
        None
    }
}

pub(crate) open spec fn is_file(s: Fs, p: Seq<usize>) -> bool {
    s.contains_key(p) && s[p] is File
}

/// What `exec` does to the tree when the op succeeds. A removed or displaced
/// entry moved aside has left the tree; a rename's source is a file, since a
/// journaled set that renames a link is refused.
pub(crate) open spec fn step(s: Fs, op: Op) -> Option<Fs> {
    match op.act {
        Act::Write => Some(s.insert(op.path, Content::File(op.bytes))),
        Act::CopyFrom => if is_file(s, op.other) {
            Some(s.insert(op.path, s[op.other]))
        } else {
            None
        },
        Act::Remove => if s.contains_key(op.path) {
            Some(s.remove(op.path))
        } else {
            None
        },
        Act::Rename => if is_file(s, op.path) && op.path != op.other {
            Some(s.remove(op.path).insert(op.other, s[op.path]))
        } else {
            None
        },
        Act::SetExecutable => if is_file(s, op.path) {
            Some(s)
        } else {
            None
        },
        Act::SetLink => Some(s.insert(op.path, Content::Link(op.target))),
    }
}

/// What `journal::replay` does to the tree. `try_exists` follows links, so
/// only a file counts as present.
pub(crate) open spec fn replay_step(s: Fs, op: Op) -> Option<Fs> {
    match op.act {
        Act::Write => Some(s.insert(op.path, Content::File(op.bytes))),
        Act::CopyFrom => if is_file(s, op.other) {
            Some(s.insert(op.path, s[op.other]))
        } else {
            None
        },
        Act::Remove => Some(s.remove(op.path)),
        Act::Rename => if is_file(s, op.path) {
            Some(s.remove(op.path).insert(op.other, s[op.path]))
        } else if is_file(s, op.other) {
            Some(s)
        } else {
            None
        },
        Act::SetExecutable => if s.contains_key(op.path) && s[op.path] is Link {
            None
        } else {
            Some(s)
        },
        Act::SetLink => Some(s.insert(op.path, Content::Link(op.target))),
    }
}

/// The tree after the first `k` ops of an apply.
pub(crate) open spec fn apply_upto(s0: Fs, ops: Seq<Op>, k: nat) -> Option<Fs>
    decreases k,
{
    if k == 0 {
        Some(s0)
    } else {
        match apply_upto(s0, ops, (k - 1) as nat) {
            Some(s) => step(s, ops[k - 1]),
            None => None,
        }
    }
}

/// The tree after replaying the first `k` ops over `u`.
pub(crate) open spec fn replay_upto(u: Fs, ops: Seq<Op>, k: nat) -> Option<Fs>
    decreases k,
{
    if k == 0 {
        Some(u)
    } else {
        match replay_upto(u, ops, (k - 1) as nat) {
            Some(s) => replay_step(s, ops[k - 1]),
            None => None,
        }
    }
}

// ---- what a crash can leave ----

/// The one path an op can leave in neither its before nor its after state:
/// a write's target, mid-rollback (a plain write puts the old bytes back); a
/// rename's destination, between moving its occupant aside and moving the
/// mover in, or back; a link's path, on a backend that replaces by remove and
/// remake. Every other step — a rename, a move aside, a removal, a flip — is
/// one call that happens or does not.
pub(crate) open spec fn torn_path(op: Op) -> Option<Seq<usize>> {
    match op.act {
        Act::Write | Act::CopyFrom | Act::SetLink => Some(op.path),
        Act::Rename => Some(op.other),
        _ => None,
    }
}

/// What a write's target can hold, torn: what it held, or some file.
pub(crate) open spec fn torn_ok(op: Op, now: Option<Content>, before: Option<Content>) -> bool {
    match op.act {
        Act::Write | Act::CopyFrom => now == before || (now is Some && now->Some_0 is File),
        _ => true,
    }
}

/// `u` is a state a crash can leave during op `j`: the tree after the first
/// `j` ops — or, while op `j` was running or being rolled back, that tree
/// with its torn path holding anything the op could leave there.
pub(crate) open spec fn crash_state(s0: Fs, ops: Seq<Op>, j: nat, u: Fs) -> bool {
    let sj = apply_upto(s0, ops, j)->Some_0;
    if j < ops.len() && torn_path(ops[j as int]) is Some {
        let d = torn_path(ops[j as int])->Some_0;
        &&& forall|p: Seq<usize>| p != d ==> #[trigger] entry(u, p) == entry(sj, p)
        &&& torn_ok(ops[j as int], entry(u, d), entry(sj, d))
    } else {
        u == sj
    }
}

// ---- proofs ----

pub(crate) open spec fn writes(op: Op, p: Seq<usize>) -> bool {
    op.path == p || (op.act is Rename && op.other == p)
}

pub(crate) open spec fn total(op: Op, p: Seq<usize>) -> bool {
    op.path == p && (op.act is Write || op.act is CopyFrom || op.act is Remove || op.act is SetLink)
}

/// What a total op leaves at its path. A copy's source never changes, so what
/// it copies is what the source held to begin with.
pub(crate) open spec fn tc(s0: Fs, op: Op) -> Option<Content> {
    match op.act {
        Act::Write => Some(Content::File(op.bytes)),
        Act::CopyFrom => entry(s0, op.other),
        Act::SetLink => Some(Content::Link(op.target)),
        _ => None,
    }
}

/// The last of the first `k` ops that is total at `p`.
pub(crate) open spec fn last_total(ops: Seq<Op>, k: nat, p: Seq<usize>) -> Option<int>
    decreases k,
{
    if k == 0 {
        None
    } else if total(ops[k - 1], p) {
        Some(k - 1)
    } else {
        last_total(ops, (k - 1) as nat, p)
    }
}

proof fn lemma_last_total_bounds(ops: Seq<Op>, k: nat, p: Seq<usize>)
    ensures
        last_total(ops, k, p) is Some ==> {
            let q = last_total(ops, k, p)->Some_0;
            0 <= q < k && total(ops[q], p) && forall|m: int| q < m < k ==> !total(#[trigger] ops[m], p)
        },
        last_total(ops, k, p) is None ==> forall|m: int| 0 <= m < k ==> !total(#[trigger] ops[m], p),
    decreases k,
{
    if k > 0 {
        lemma_last_total_bounds(ops, (k - 1) as nat, p);
    }
}

/// What replay holds at `p` after `k` ops, by the invariant: what the last
/// total op there left, or what the crash left.
pub(crate) open spec fn lastr(u: Fs, s0: Fs, ops: Seq<Op>, k: nat, p: Seq<usize>) -> Option<Content> {
    match last_total(ops, k, p) {
        Some(q) => tc(s0, ops[q]),
        None => entry(u, p),
    }
}

proof fn lemma_admits(ops: Seq<Op>, i: int, k: int)
    requires
        admissible(sops(ops)),
        0 <= i < ops.len(),
        0 <= k < ops.len(),
    ensures
        pair_refusal(sops(ops), i, k) is None,
        sops(ops)[i] == sop(ops[i]),
        sops(ops)[k] == sop(ops[k]),
{
}

proof fn lemma_maps_equal(a: Fs, b: Fs)
    requires
        forall|p: Seq<usize>| #[trigger] entry(a, p) == entry(b, p),
    ensures
        a == b,
{
    assert forall|p: Seq<usize>| a.contains_key(p) <==> b.contains_key(p) by {
        assert(entry(a, p) == entry(b, p));
    }
    assert forall|p: Seq<usize>| a.contains_key(p) implies #[trigger] a[p] == b[p] by {
        assert(entry(a, p) == entry(b, p));
    }
    assert(a =~= b);
}

proof fn lemma_step_frame(s: Fs, op: Op, p: Seq<usize>)
    requires
        step(s, op) is Some,
        !writes(op, p),
    ensures
        entry(step(s, op)->Some_0, p) == entry(s, p),
{
}

proof fn lemma_apply_prefix(s0: Fs, ops: Seq<Op>, k: nat, n: nat)
    requires
        k <= n,
        apply_upto(s0, ops, n) is Some,
    ensures
        apply_upto(s0, ops, k) is Some,
    decreases n - k,
{
    if k < n {
        lemma_apply_prefix(s0, ops, k, (n - 1) as nat);
    }
}

/// A path no op in `[k, j)` writes holds after `j` ops what it held after `k`.
proof fn lemma_unwritten(s0: Fs, ops: Seq<Op>, k: nat, j: nat, p: Seq<usize>)
    requires
        k <= j,
        apply_upto(s0, ops, j) is Some,
        forall|m: int| k <= m < j ==> !writes(#[trigger] ops[m], p),
    ensures
        apply_upto(s0, ops, k) is Some,
        entry(apply_upto(s0, ops, j)->Some_0, p) == entry(apply_upto(s0, ops, k)->Some_0, p),
    decreases j - k,
{
    lemma_apply_prefix(s0, ops, k, j);
    if k < j {
        lemma_apply_prefix(s0, ops, (j - 1) as nat, j);
        lemma_unwritten(s0, ops, k, (j - 1) as nat, p);
        lemma_step_frame(apply_upto(s0, ops, (j - 1) as nat)->Some_0, ops[j - 1], p);
    }
}

/// Nothing writes a copy's source: every other op names it only to copy
/// from it.
proof fn lemma_copy_source(s0: Fs, ops: Seq<Op>, i: int, j: nat)
    requires
        admissible(sops(ops)),
        0 <= i < ops.len(),
        ops[i].act is CopyFrom,
        j <= ops.len(),
        apply_upto(s0, ops, j) is Some,
    ensures
        forall|m: int| 0 <= m < ops.len() ==> !writes(#[trigger] ops[m], ops[i].other),
        entry(apply_upto(s0, ops, j)->Some_0, ops[i].other) == entry(s0, ops[i].other),
{
    let src = ops[i].other;
    assert forall|m: int| 0 <= m < ops.len() implies !writes(#[trigger] ops[m], src) by {
        lemma_admits(ops, i, m);
        lemma_admits(ops, m, m);
    }
    lemma_unwritten(s0, ops, 0, j, src);
}

/// What the apply leaves at `p` after `k` ops, when some op before `k` was
/// total there: what the last one left. Between it and `k`, the rule lets
/// nothing else change `p`.
proof fn lemma_apply_last_total(s0: Fs, ops: Seq<Op>, k: nat, p: Seq<usize>)
    requires
        admissible(sops(ops)),
        k <= ops.len(),
        apply_upto(s0, ops, k) is Some,
        last_total(ops, k, p) is Some,
    ensures
        entry(apply_upto(s0, ops, k)->Some_0, p) == tc(s0, ops[last_total(ops, k, p)->Some_0]),
    decreases k,
{
    lemma_last_total_bounds(ops, k, p);
    let q = last_total(ops, k, p)->Some_0;
    lemma_apply_prefix(s0, ops, (k - 1) as nat, k);
    let prev = apply_upto(s0, ops, (k - 1) as nat)->Some_0;
    let op = ops[k - 1];
    if q == k - 1 {
        if op.act is CopyFrom {
            lemma_copy_source(s0, ops, k - 1, (k - 1) as nat);
        }
    } else {
        assert(last_total(ops, (k - 1) as nat, p) == Some(q));
        lemma_apply_last_total(s0, ops, (k - 1) as nat, p);
        if writes(op, p) {
            // Not total, so a flip — which changes nothing here — or a rename,
            // which the rule forbids around an op total at `p` before it.
            if op.act is Rename {
                lemma_admits(ops, k - 1, q);
                assert(false);
            }
        } else {
            lemma_step_frame(prev, op, p);
        }
    }
}

/// A rename's destination holds a file from the rename on: after it, the
/// rule lets only writes and flips touch it.
proof fn lemma_file_after_rename(s0: Fs, ops: Seq<Op>, m: int, k: nat)
    requires
        admissible(sops(ops)),
        0 <= m < k <= ops.len(),
        ops[m].act is Rename,
        apply_upto(s0, ops, k) is Some,
    ensures
        is_file(apply_upto(s0, ops, k)->Some_0, ops[m].other),
    decreases k,
{
    let t = ops[m].other;
    lemma_apply_prefix(s0, ops, (k - 1) as nat, k);
    let prev = apply_upto(s0, ops, (k - 1) as nat)->Some_0;
    let op = ops[k - 1];
    if k - 1 == m {
    } else {
        lemma_file_after_rename(s0, ops, m, (k - 1) as nat);
        if writes(op, t) {
            lemma_admits(ops, m, k - 1);
        } else {
            lemma_step_frame(prev, op, t);
        }
    }
}

/// A rename's source is gone from the rename on: after it, the rule lets
/// nothing name it.
proof fn lemma_gone_after_rename(s0: Fs, ops: Seq<Op>, m: int, k: nat)
    requires
        admissible(sops(ops)),
        0 <= m < k <= ops.len(),
        ops[m].act is Rename,
        apply_upto(s0, ops, k) is Some,
    ensures
        !apply_upto(s0, ops, k)->Some_0.contains_key(ops[m].path),
{
    let f = ops[m].path;
    lemma_admits(ops, m, m);
    assert forall|x: int| m + 1 <= x < k implies !writes(#[trigger] ops[x], f) by {
        lemma_admits(ops, m, x);
    }
    lemma_unwritten(s0, ops, (m + 1) as nat, k, f);
    lemma_apply_prefix(s0, ops, m as nat, k);
}

/// A flipped file never becomes a link: after a flip, the rule lets only
/// writes, flips, removals and renames away touch it.
proof fn lemma_no_link_after_flip(s0: Fs, ops: Seq<Op>, i: int, k: nat)
    requires
        admissible(sops(ops)),
        0 <= i < k <= ops.len(),
        ops[i].act is SetExecutable,
        apply_upto(s0, ops, k) is Some,
    ensures
        !(entry(apply_upto(s0, ops, k)->Some_0, ops[i].path) matches Some(Content::Link(_))),
    decreases k,
{
    let p = ops[i].path;
    lemma_apply_prefix(s0, ops, (k - 1) as nat, k);
    let prev = apply_upto(s0, ops, (k - 1) as nat)->Some_0;
    let op = ops[k - 1];
    if k - 1 > i {
        lemma_no_link_after_flip(s0, ops, i, (k - 1) as nat);
        if writes(op, p) {
            lemma_admits(ops, i, k - 1);
        } else {
            lemma_step_frame(prev, op, p);
        }
    }
}

/// **The invariant.** Replaying the first `k` ops over a crash state during
/// op `j` (`k <= j`) leaves, at every path, what the last total op before `k`
/// left there — or, where there was none, what the crash left.
proof fn lemma_replay_prefix(s0: Fs, ops: Seq<Op>, j: nat, u: Fs, k: nat)
    requires
        admissible(sops(ops)),
        j <= ops.len(),
        apply_upto(s0, ops, ops.len() as nat) is Some,
        crash_state(s0, ops, j, u),
        k <= j,
    ensures
        replay_upto(u, ops, k) is Some,
        forall|p: Seq<usize>| #[trigger] entry(replay_upto(u, ops, k)->Some_0, p) == lastr(u, s0, ops, k, p),
    decreases k,
{
    let n = ops.len() as nat;
    lemma_apply_prefix(s0, ops, j, n);
    let sj = apply_upto(s0, ops, j)->Some_0;
    if k > 0 {
        let km = (k - 1) as nat;
        lemma_replay_prefix(s0, ops, j, u, km);
        lemma_apply_prefix(s0, ops, km, n);
        lemma_apply_prefix(s0, ops, k, n);
        let r = replay_upto(u, ops, km)->Some_0;
        let sk = apply_upto(s0, ops, km)->Some_0;
        let op = ops[km as int];
        assert(step(sk, op) is Some);
        // Where the crash left something other than the tree after `j` ops.
        let torn = j < n && torn_path(ops[j as int]) is Some;
        let d = torn_path(ops[j as int])->Some_0;
        match op.act {
            Act::CopyFrom => {
                let src = op.other;
                lemma_copy_source(s0, ops, km as int, km);
                lemma_copy_source(s0, ops, km as int, j);
                lemma_last_total_bounds(ops, km, src);
                assert(last_total(ops, km, src) is None) by {
                    if last_total(ops, km, src) is Some {
                        let q = last_total(ops, km, src)->Some_0;
                        assert(writes(ops[q], src));
                    }
                }
                if torn {
                    assert(src != d) by {
                        assert(writes(ops[j as int], d));
                    }
                }
                assert(entry(r, src) == lastr(u, s0, ops, km, src));
                assert(entry(u, src) == entry(sj, src));
                assert(entry(r, src) == entry(s0, src));
                assert(entry(sk, src) == entry(s0, src));
                assert(is_file(r, src));
                lemma_replay_prefix_step(u, s0, ops, km, r);
            },
            Act::SetExecutable => {
                let p = op.path;
                lemma_last_total_bounds(ops, km, p);
                assert(entry(r, p) == lastr(u, s0, ops, km, p));
                if last_total(ops, km, p) is Some {
                    lemma_apply_last_total(s0, ops, km, p);
                    assert(entry(r, p) == entry(sk, p));
                } else {
                    lemma_no_link_after_flip(s0, ops, km as int, j);
                    if torn && p == d {
                        lemma_admits(ops, km as int, j as int);
                        assert(ops[j as int].act is Write || ops[j as int].act is CopyFrom);
                        assert(torn_ok(ops[j as int], entry(u, d), entry(sj, d)));
                    } else {
                        assert(entry(u, p) == entry(sj, p));
                    }
                }
                assert(!(r.contains_key(p) && r[p] is Link));
                lemma_replay_prefix_step(u, s0, ops, km, r);
            },
            Act::Rename => {
                let (f, t) = (op.path, op.other);
                lemma_admits(ops, km as int, km as int);
                // The source: nothing total before (only flips), gone at `j`.
                lemma_last_total_bounds(ops, km, f);
                assert(last_total(ops, km, f) is None) by {
                    if last_total(ops, km, f) is Some {
                        let q = last_total(ops, km, f)->Some_0;
                        lemma_admits(ops, km as int, q);
                    }
                }
                lemma_gone_after_rename(s0, ops, km as int, j);
                if torn {
                    assert(f != d) by {
                        lemma_admits(ops, km as int, j as int);
                    }
                }
                assert(entry(r, f) == lastr(u, s0, ops, km, f));
                assert(entry(u, f) == entry(sj, f));
                assert(!is_file(r, f));
                // The destination: nothing before, a file at `j`.
                lemma_last_total_bounds(ops, km, t);
                assert(last_total(ops, km, t) is None) by {
                    if last_total(ops, km, t) is Some {
                        let q = last_total(ops, km, t)->Some_0;
                        lemma_admits(ops, km as int, q);
                    }
                }
                lemma_file_after_rename(s0, ops, km as int, j);
                assert(entry(r, t) == lastr(u, s0, ops, km, t));
                if torn && t == d {
                    // What tore it is a later write there: the file it held,
                    // or another.
                    lemma_admits(ops, km as int, j as int);
                    assert(ops[j as int].act is Write || ops[j as int].act is CopyFrom);
                    assert(torn_ok(ops[j as int], entry(u, d), entry(sj, d)));
                } else {
                    assert(entry(u, t) == entry(sj, t));
                }
                assert(is_file(r, t));
                lemma_replay_prefix_step(u, s0, ops, km, r);
            },
            _ => {
                lemma_replay_prefix_step(u, s0, ops, km, r);
            },
        }
    }
}

/// One turn of the invariant: an op whose reads came out as the invariant
/// says leaves the invariant holding one op on.
proof fn lemma_replay_prefix_step(u: Fs, s0: Fs, ops: Seq<Op>, km: nat, r: Fs)
    requires
        km < ops.len(),
        replay_upto(u, ops, km) == Some(r),
        forall|p: Seq<usize>| #[trigger] entry(r, p) == lastr(u, s0, ops, km, p),
        ops[km as int].act is CopyFrom ==> is_file(r, ops[km as int].other) && entry(r, ops[km as int].other) == entry(s0, ops[km as int].other),
        ops[km as int].act is SetExecutable ==> !(r.contains_key(ops[km as int].path) && r[ops[km as int].path] is Link),
        ops[km as int].act is Rename ==> !is_file(r, ops[km as int].path) && is_file(r, ops[km as int].other),
    ensures
        replay_upto(u, ops, km + 1) is Some,
        forall|p: Seq<usize>| #[trigger] entry(replay_upto(u, ops, km + 1)->Some_0, p) == lastr(u, s0, ops, km + 1, p),
{
    let op = ops[km as int];
    let k = km + 1;
    assert(replay_upto(u, ops, k) == replay_step(r, op));
    let r2 = replay_step(r, op)->Some_0;
    assert forall|p: Seq<usize>| #[trigger] entry(r2, p) == lastr(u, s0, ops, k, p) by {
        assert(entry(r, p) == lastr(u, s0, ops, km, p));
        assert(last_total(ops, k, p) == if total(op, p) { Some(km as int) } else { last_total(ops, km, p) });
    }
}

/// Over the tree an op actually ran against, replaying it does what running
/// it did.
proof fn lemma_replay_is_step(s: Fs, op: Op)
    requires
        step(s, op) is Some,
    ensures
        replay_step(s, op) == step(s, op),
{
}

/// From the tree after `k` ops, replaying the rest reaches the applied tree.
proof fn lemma_replay_suffix(s0: Fs, ops: Seq<Op>, u: Fs, k: nat, m: nat)
    requires
        k <= m <= ops.len(),
        apply_upto(s0, ops, ops.len() as nat) is Some,
        replay_upto(u, ops, k) == apply_upto(s0, ops, k),
    ensures
        replay_upto(u, ops, m) == apply_upto(s0, ops, m),
    decreases m - k,
{
    if k < m {
        lemma_replay_suffix(s0, ops, u, k, (m - 1) as nat);
        lemma_apply_prefix(s0, ops, m, ops.len() as nat);
        lemma_apply_prefix(s0, ops, (m - 1) as nat, ops.len() as nat);
        lemma_replay_is_step(apply_upto(s0, ops, (m - 1) as nat)->Some_0, ops[m - 1]);
    }
}

/// **A set the rule accepts recovers from any crash.** Whatever state a crash
/// leaves during any op of a set the apply would have completed — before the
/// op, after it, halfway through it, or halfway through rolling it back —
/// replaying the whole journal from its first op reaches exactly the tree the
/// apply would have.
pub(crate) proof fn theorem_replay_recovers(s0: Fs, ops: Seq<Op>, j: nat, u: Fs)
    requires
        admissible(sops(ops)),
        apply_upto(s0, ops, ops.len() as nat) is Some,
        j <= ops.len(),
        crash_state(s0, ops, j, u),
    ensures
        replay_upto(u, ops, ops.len() as nat) == apply_upto(s0, ops, ops.len() as nat),
{
    let n = ops.len() as nat;
    lemma_replay_prefix(s0, ops, j, u, j);
    lemma_apply_prefix(s0, ops, j, n);
    let sj = apply_upto(s0, ops, j)->Some_0;
    let rj = replay_upto(u, ops, j)->Some_0;
    let torn = j < n && torn_path(ops[j as int]) is Some;
    let d = torn_path(ops[j as int])->Some_0;
    // Away from the torn path, the replay has caught up with the apply.
    assert forall|p: Seq<usize>| !(torn && p == d) implies #[trigger] entry(rj, p) == entry(sj, p) by {
        assert(entry(rj, p) == lastr(u, s0, ops, j, p));
        if last_total(ops, j, p) is Some {
            lemma_apply_last_total(s0, ops, j, p);
        }
    }
    if !torn {
        lemma_maps_equal(rj, sj);
        lemma_replay_suffix(s0, ops, u, j, n);
    } else {
        // Op `j` itself overwrites the torn path, reading nothing there.
        let op = ops[j as int];
        lemma_apply_prefix(s0, ops, j + 1, n);
        let sj1 = apply_upto(s0, ops, j + 1)->Some_0;
        if op.act is CopyFrom {
            lemma_admits(ops, j as int, j as int);
            assert(entry(rj, op.other) == entry(sj, op.other));
        }
        if op.act is Rename {
            lemma_admits(ops, j as int, j as int);
            assert(entry(rj, op.path) == entry(sj, op.path));
        }
        let rj1 = replay_upto(u, ops, j + 1)->Some_0;
        assert forall|p: Seq<usize>| #[trigger] entry(rj1, p) == entry(sj1, p) by {
            assert(p != d ==> entry(rj, p) == entry(sj, p));
        }
        lemma_maps_equal(rj1, sj1);
        lemma_replay_suffix(s0, ops, u, j + 1, n);
    }
}

} // verus!
