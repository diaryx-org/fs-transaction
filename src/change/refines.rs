//! The proof that an op which lands does what the recovery theorem's `step`
//! says, and so that a crash between two ops of a real apply leaves a tree
//! recovery rolls forward. Compiled only by Verus (`verus_keep_ghost`).
//!
//! [`exec`](super::exec) is verified to [`lands`]: when it returns `Ok`, every
//! file of the set but the op's own aside holds what [`step`] says the op
//! leaves there. The aside is the one file the model does not have — an entry
//! moved aside has, as far as the model is concerned, left the tree — and no
//! op but its own names it. The exception is the two reads the model cannot
//! see through: a rename or a copy whose source is a link, which the apply
//! reads through to a referent outside the tree. [`seen`] excludes them, and
//! a set the model completes never makes either.
//!
//! [`run_or_roll_back`](super::run_or_roll_back) carries that from op to op:
//! between any two ops the tree agrees with [`apply_upto`] on every file the
//! set names, and a landed set with the applied tree. [`theorem_between_ops`]
//! is what that buys: from such a tree, replay reaches the applied tree.

use vstd::prelude::*;

use super::rollback::{aside_key, aside_ok, asides, asides_apart, frame, touches};
use crate::port::{Tree, content, ent, model, models, names};
use crate::replayable::proof::{
    Fs, Op, apply_upto, crash_state, entry, flat_admissible, fops, is_link, lemma_apply_prefix,
    replay_step, replay_upto, step, theorem_replay_recovers, torn_ok,
};

verus! {

/// The reads of `m` the model sees: a rename's source and a copy's source
/// are not links, and a rename does not name one file twice.
pub(crate) open spec fn seen(m: Op, s: Fs) -> bool {
    &&& m.act is Rename ==> !is_link(s, m.path) && m.path != m.other
    &&& m.act is CopyFrom ==> !is_link(s, m.other)
}

/// Whether `x` is where op `index` moves an entry aside.
pub(crate) open spec fn is_aside(root: &std::path::Path, op: crate::FileOp, index: int, x: int) -> bool {
    asides(root, op) && x == aside_key(root, op, index)
}

/// Op `index` took `old` to `new` as the model's `step` says, on every file
/// of `keys` but its aside.
pub(crate) open spec fn lands(
    root: &std::path::Path,
    op: crate::FileOp,
    index: int,
    keys: Set<int>,
    old: Tree,
    new: Tree,
) -> bool {
    let m = model(root, op);
    let s = content(old);
    &&& step(s, m) is Some
    &&& forall|x: int| keys.contains(x) && !is_aside(root, op, index, x)
        ==> #[trigger] entry(content(new), x) == entry(step(s, m)->Some_0, x)
}

/// No op of the set moves anything aside to `x`.
pub(crate) open spec fn unasided(root: &std::path::Path, ops: Seq<crate::FileOp>, x: int) -> bool {
    forall|i: int| 0 <= i < ops.len() ==> !#[trigger] is_aside(root, ops[i], i, x)
}

/// `t` agrees with the model `s` on every file of the set but the asides.
pub(crate) open spec fn matches(
    root: &std::path::Path,
    ops: Seq<crate::FileOp>,
    keys: Set<int>,
    t: Tree,
    s: Fs,
) -> bool {
    forall|x: int| keys.contains(x) && unasided(root, ops, x) ==> #[trigger] entry(content(t), x) == entry(s, x)
}

/// An op that changed nothing of the set but what it names and its aside,
/// and left at what it names what the model's `step` does, lands.
pub(crate) proof fn lemma_lands(
    root: &std::path::Path,
    op: crate::FileOp,
    index: int,
    keys: Set<int>,
    old: Tree,
    new: Tree,
)
    requires
        step(content(old), model(root, op)) is Some,
        frame(keys, old, new, touches(root, op, index)),
        entry(content(new), model(root, op).path) == entry(step(content(old), model(root, op))->Some_0, model(root, op).path),
        (model(root, op).act is Rename || model(root, op).act is CopyFrom) ==> entry(content(new), model(root, op).other)
            == entry(step(content(old), model(root, op))->Some_0, model(root, op).other),
    ensures
        lands(root, op, index, keys, old, new),
{
    broadcast use crate::port::lemma_content;
    let m = model(root, op);
    let s = content(old);
    assert forall|x: int| keys.contains(x) && !is_aside(root, op, index, x)
        implies #[trigger] entry(content(new), x) == entry(step(s, m)->Some_0, x) by {
        if x != m.path && !((m.act is Rename || m.act is CopyFrom) && x == m.other) {
            assert(!touches(root, op, index).contains(x));
            assert(ent(new, x) == ent(old, x));
        }
    }
}

/// The model's tree after the first `k` ops of a set, from `t`.
pub(crate) open spec fn applied(root: &std::path::Path, ops: Seq<crate::FileOp>, t: Tree, k: nat) -> Fs {
    apply_upto(content(t), models(root, ops), k)->Some_0
}

/// The model completes the set from `t`.
pub(crate) open spec fn completes(root: &std::path::Path, ops: Seq<crate::FileOp>, t: Tree) -> bool {
    apply_upto(content(t), models(root, ops), ops.len() as nat) is Some
}

/// One op on: an op that lands from a tree matching the model after `i` ops
/// leaves one matching it after `i + 1`.
pub(crate) proof fn lemma_next(
    root: &std::path::Path,
    ops: Seq<crate::FileOp>,
    i: int,
    keys: Set<int>,
    start: Tree,
    before: Tree,
    after: Tree,
)
    requires
        0 <= i < ops.len(),
        completes(root, ops, start),
        forall|x: int| 0 <= x < ops.len() ==> names(root, #[trigger] ops[x], keys),
        aside_ok(root, ops[i], i, keys, before),
        asides_apart(root, ops),
        matches(root, ops, keys, before, applied(root, ops, start, i as nat)),
        seen(model(root, ops[i]), content(before)) ==> lands(root, ops[i], i, keys, before, after),
    ensures
        matches(root, ops, keys, after, applied(root, ops, start, (i + 1) as nat)),
{
    let n = ops.len() as nat;
    let ms = models(root, ops);
    let s0 = content(start);
    lemma_apply_prefix(s0, ms, (i + 1) as nat, n);
    lemma_apply_prefix(s0, ms, i as nat, n);
    let si = apply_upto(s0, ms, i as nat)->Some_0;
    let m = model(root, ops[i]);
    assert(ms[i] == m);
    assert(step(si, m) is Some);
    assert(apply_upto(s0, ms, (i + 1) as nat)->Some_0 == step(si, m)->Some_0);
    // What op `i` names is no op's aside, so the tree holds there what the
    // model does.
    assert(names(root, ops[i], keys));
    assert forall|x: int| (x == m.path || ((m.act is Rename || m.act is CopyFrom) && x == m.other))
        implies unasided(root, ops, x) by {
        assert forall|j: int| 0 <= j < ops.len() implies !#[trigger] is_aside(root, ops[j], j, x) by {
            if j != i && asides(root, ops[j]) {
                assert(!touches(root, ops[i], i).contains(aside_key(root, ops[j], j)));
            }
        }
    }
    let b = content(before);
    assert(entry(b, m.path) == entry(si, m.path));
    if m.act is Rename || m.act is CopyFrom {
        assert(entry(b, m.other) == entry(si, m.other));
    }
    lemma_step_seen(si, m);
    lemma_step_congruent(b, si, m, m.path);
    assert(seen(m, b));
    assert forall|x: int| keys.contains(x) && unasided(root, ops, x)
        implies #[trigger] entry(content(after), x) == entry(step(si, m)->Some_0, x) by {
        assert(!is_aside(root, ops[i], i, x));
        assert(entry(b, x) == entry(si, x));
        lemma_step_congruent(b, si, m, x);
    }
}

/// An op the model completes reads only what it sees.
pub(crate) proof fn lemma_step_seen(s: Fs, m: Op)
    requires
        step(s, m) is Some,
    ensures
        seen(m, s),
{
}

/// `step` reads and writes only the files an op names: two trees that agree
/// there step alike, and agree after at every file they agreed on before.
pub(crate) proof fn lemma_step_congruent(a: Fs, b: Fs, m: Op, x: int)
    requires
        entry(a, m.path) == entry(b, m.path),
        (m.act is Rename || m.act is CopyFrom) ==> entry(a, m.other) == entry(b, m.other),
    ensures
        step(a, m) is Some <==> step(b, m) is Some,
        step(a, m) is Some && entry(a, x) == entry(b, x) ==> entry(step(a, m)->Some_0, x) == entry(
            step(b, m)->Some_0,
            x,
        ),
{
}

/// `replay_step` likewise.
pub(crate) proof fn lemma_replay_step_congruent(named: Set<int>, a: Fs, b: Fs, m: Op)
    requires
        named.contains(m.path),
        (m.act is Rename || m.act is CopyFrom) ==> named.contains(m.other),
        forall|x: int| named.contains(x) ==> #[trigger] entry(a, x) == entry(b, x),
    ensures
        replay_step(a, m) is Some <==> replay_step(b, m) is Some,
        replay_step(a, m) is Some ==> forall|x: int| named.contains(x)
            ==> #[trigger] entry(replay_step(a, m)->Some_0, x) == entry(replay_step(b, m)->Some_0, x),
{
    assert(entry(a, m.path) == entry(b, m.path));
    if m.act is Rename || m.act is CopyFrom {
        assert(entry(a, m.other) == entry(b, m.other));
    }
    if replay_step(a, m) is Some {
        assert forall|x: int| named.contains(x) implies #[trigger] entry(replay_step(a, m)->Some_0, x)
            == entry(replay_step(b, m)->Some_0, x) by {
            assert(entry(a, x) == entry(b, x));
        }
    }
}

/// Replaying over two trees that agree on every file a set names agrees on
/// them after.
pub(crate) proof fn lemma_replay_congruent(named: Set<int>, a: Fs, b: Fs, ops: Seq<Op>, k: nat)
    requires
        k <= ops.len(),
        forall|i: int| 0 <= i < ops.len() ==> named.contains(#[trigger] ops[i].path),
        forall|i: int| 0 <= i < ops.len() && (ops[i].act is Rename || ops[i].act is CopyFrom)
            ==> named.contains(#[trigger] ops[i].other),
        forall|x: int| named.contains(x) ==> #[trigger] entry(a, x) == entry(b, x),
    ensures
        replay_upto(a, ops, k) is Some <==> replay_upto(b, ops, k) is Some,
        replay_upto(a, ops, k) is Some ==> forall|x: int| named.contains(x)
            ==> #[trigger] entry(replay_upto(a, ops, k)->Some_0, x) == entry(replay_upto(b, ops, k)->Some_0, x),
    decreases k,
{
    if k > 0 {
        let km = (k - 1) as nat;
        lemma_replay_congruent(named, a, b, ops, km);
        if replay_upto(a, ops, km) is Some {
            let m = ops[km as int];
            assert(named.contains(m.path));
            lemma_replay_step_congruent(named, replay_upto(a, ops, km)->Some_0, replay_upto(b, ops, km)->Some_0, m);
        }
    }
}

/// **A crash between two ops recovers.** Of a set the rule accepts and the
/// apply would complete, a tree that agrees with the tree after its first `i`
/// ops on every file the set names — which is what a crash between op `i - 1`
/// and op `i` leaves — replays to exactly the applied tree on every one of
/// them.
pub(crate) proof fn theorem_between_ops(s0: Fs, ops: Seq<Op>, i: nat, u: Fs, named: Set<int>)
    requires
        flat_admissible(fops(ops)),
        apply_upto(s0, ops, ops.len() as nat) is Some,
        i <= ops.len(),
        forall|k: int| 0 <= k < ops.len() ==> named.contains(#[trigger] ops[k].path),
        forall|k: int| 0 <= k < ops.len() && (ops[k].act is Rename || ops[k].act is CopyFrom)
            ==> named.contains(#[trigger] ops[k].other),
        forall|x: int| named.contains(x) ==> #[trigger] entry(u, x) == entry(apply_upto(s0, ops, i)->Some_0, x),
    ensures
        replay_upto(u, ops, ops.len() as nat) is Some,
        forall|x: int| named.contains(x) ==> #[trigger] entry(replay_upto(u, ops, ops.len() as nat)->Some_0, x)
            == entry(apply_upto(s0, ops, ops.len() as nat)->Some_0, x),
{
    let n = ops.len() as nat;
    lemma_apply_prefix(s0, ops, i, n);
    let si = apply_upto(s0, ops, i)->Some_0;
    assert(crash_state(s0, ops, i, si)) by {
        if i < n {
            let d = crate::replayable::proof::torn_path(ops[i as int]);
            if d is Some {
                assert(torn_ok(ops[i as int], entry(si, d->Some_0), entry(si, d->Some_0)));
            }
        }
    }
    theorem_replay_recovers(s0, ops, i, si);
    lemma_replay_congruent(named, u, si, ops, n);
}

} // verus!
