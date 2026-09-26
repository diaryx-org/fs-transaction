//! `src/journal.rs`: rolling a journaled set forward after a crash.
//!
//! `recover` replays *every* op in the journal, from the first, over whatever
//! state the crash left behind. The claim in the source is that replay is
//! idempotent — "a write already landed is simply rewritten, a rename already
//! done is recognized and skipped" — so it does not matter how far the set got.
//! `apply` relies on that twice: once for a crash mid-set, and once for a
//! crash after `Ok`, because the journal's deletion is deliberately not
//! flushed and a power cut may bring it back.
//!
//! **What is proved** (`theorem_replay_from_crash_point`): replaying the ops
//! *from the one the crash interrupted* gets to the applied state — whether
//! that op had not started, had finished, or (for `set_link`) was caught
//! halfway. The ambiguity of the one op in flight is handled correctly.
//!
//! **What is not true**: that it does not matter where replay starts.
//! Replaying from the first op over a state later ops have already changed
//! re-runs the earlier ops against a tree they were not written for. Five
//! checked counterexamples, all from sets `apply` accepts. Each starts from a
//! resurrected journal after a clean apply, the state the source calls the
//! designed-for case:
//!
//! - `counterexample_swap`: a swap through a temporary is silently undone.
//! - `counterexample_recreate`: renaming a file and then writing a new one at
//!   its old path loses the renamed file's contents. The destination ends up
//!   with the new file's bytes.
//! - `counterexample_remove_then_rename`: the moved file is deleted, and
//!   recovery then fails, leaving the journal to refuse every later apply.
//! - `counterexample_chain`: `a → b → c` fails recovery.
//! - `counterexample_chmod_then_rename`: flipping a bit and then moving the
//!   file fails recovery.
//!
//! Modeled as in `change.rs`, with one addition: `try_exists` follows links,
//! so a link counts as missing here, which is what a dangling link is.

use vstd::prelude::*;
use crate::change::*;

verus! {

/// `try_exists`.
pub open spec fn present(s: Fs, p: int) -> bool {
    s.dom().contains(p) && s[p] is File
}

/// `replay`, one op.
pub open spec fn replay_step(s: Fs, op: Op) -> Option<Fs> {
    match op {
        Op::Write { path, bytes } => Some(replace(s, path, bytes)),
        Op::CopyFrom { path, source } => if present(s, source) {
            Some(replace(s, path, s[source]->File_bytes))
        } else {
            None
        },
        Op::Remove { path } => Some(s.remove(path)),
        Op::SetExecutable { path, executable } => if present(s, path) {
            Some(
                s.insert(
                    path,
                    Entry::File { bytes: s[path]->File_bytes, executable, perm: s[path]->File_perm },
                ),
            )
        } else {
            None
        },
        Op::SetLink { path, target } => Some(s.insert(path, Entry::Link { target })),
        // Move it if the source is there, accept it as done if only the
        // destination is, and refuse if neither is.
        Op::Rename { from, to } => if present(s, from) {
            rename(s, from, to)
        } else if present(s, to) {
            Some(s)
        } else {
            None
        },
    }
}

/// `Journal::recover`: every op, in order, from the first.
pub open spec fn replay(s: Fs, ops: Seq<Op>) -> Option<Fs>
    decreases ops.len(),
{
    if ops.len() == 0 {
        Some(s)
    } else {
        match replay(s, ops.drop_last()) {
            None => None,
            Some(r) => replay_step(r, ops.last()),
        }
    }
}

/// Every rename in the set moves a regular file, as `try_exists` sees one.
pub open spec fn renames_move_files(s0: Fs, ops: Seq<Op>) -> bool {
    forall|i: int|
        0 <= i < ops.len() && (#[trigger] ops[i]) is Rename ==> present(
            apply_seq(s0, ops.take(i))->Some_0.0,
            ops[i]->Rename_from,
        )
}

// ---- the positive half ----

/// Over the state an op actually ran against, replaying it does what running
/// it did.
proof fn lemma_replay_step_is_effect(s: Fs, op: Op)
    requires
        exec_ok(s, op) is Some,
        op is Rename ==> present(s, op->Rename_from),
    ensures
        replay_step(s, op) == Some(exec_ok(s, op)->Some_0.0),
{
}

proof fn lemma_apply_seq_prefix(s0: Fs, ops: Seq<Op>, i: int)
    requires
        0 <= i <= ops.len(),
        apply_seq(s0, ops) is Some,
    ensures
        apply_seq(s0, ops.take(i)) is Some,
    decreases ops.len() - i,
{
    if i < ops.len() {
        lemma_apply_seq_prefix(s0, ops, i + 1);
        assert(ops.take(i + 1).drop_last() =~= ops.take(i));
    } else {
        assert(ops.take(i) =~= ops);
    }
}

/// Replaying ops `j..k` over the state after op `j` gives the state after op `k`.
proof fn lemma_replay_segment(s0: Fs, ops: Seq<Op>, j: int, k: int)
    requires
        0 <= j <= k <= ops.len(),
        apply_seq(s0, ops) is Some,
        renames_move_files(s0, ops),
    ensures
        replay(apply_seq(s0, ops.take(j))->Some_0.0, ops.subrange(j, k)) == Some(
            apply_seq(s0, ops.take(k))->Some_0.0,
        ),
    decreases k - j,
{
    lemma_apply_seq_prefix(s0, ops, j);
    if k == j {
        assert(ops.subrange(j, k) =~= seq![]);
    } else {
        lemma_replay_segment(s0, ops, j, k - 1);
        lemma_apply_seq_prefix(s0, ops, k);
        lemma_apply_seq_prefix(s0, ops, k - 1);
        assert(ops.subrange(j, k).drop_last() =~= ops.subrange(j, k - 1));
        assert(ops.subrange(j, k).last() == ops[k - 1]);
        assert(ops.take(k).drop_last() =~= ops.take(k - 1));
        assert(ops.take(k).last() == ops[k - 1]);
        let m = apply_seq(s0, ops.take(k - 1))->Some_0.0;
        if ops[k - 1] is Rename {
            assert(present(m, ops[k - 1]->Rename_from));
        }
        lemma_replay_step_is_effect(m, ops[k - 1]);
    }
}

/// **Replay from the crash point is correct.** A crash at op `j` leaves the
/// state after op `j - 1`, the state after op `j`, or, when op `j` is a
/// `set_link`, the first with the path emptied. From any of these, replaying
/// op `j` onward reaches the state the whole set applies to. A journal that
/// knew `j` would recover correctly with the per-op logic it already has.
pub proof fn theorem_replay_from_crash_point(s0: Fs, ops: Seq<Op>, j: int)
    requires
        0 <= j < ops.len(),
        apply_seq(s0, ops) is Some,
        renames_move_files(s0, ops),
    ensures
        ({
            let before = apply_seq(s0, ops.take(j))->Some_0.0;
            let after = apply_seq(s0, ops.take(j + 1))->Some_0.0;
            let applied = apply_seq(s0, ops)->Some_0.0;
            &&& replay(before, ops.subrange(j, ops.len() as int)) == Some(applied)
            &&& replay(after, ops.subrange(j, ops.len() as int)) == Some(applied)
            &&& (ops[j] is SetLink ==> replay(
                before.remove(ops[j]->SetLink_path),
                ops.subrange(j, ops.len() as int),
            ) == Some(applied))
        }),
{
    let n = ops.len() as int;
    assert(ops.take(n) =~= ops);
    lemma_replay_segment(s0, ops, j, n);
    lemma_replay_segment(s0, ops, j + 1, n);
    lemma_apply_seq_prefix(s0, ops, j);
    lemma_apply_seq_prefix(s0, ops, j + 1);
    let before = apply_seq(s0, ops.take(j))->Some_0.0;
    let after = apply_seq(s0, ops.take(j + 1))->Some_0.0;
    assert(ops.take(j + 1).drop_last() =~= ops.take(j));
    assert(ops.take(j + 1).last() == ops[j]);
    // Op `j`, over the state it produced: every op the model has is
    // idempotent against its own result.
    let tail = ops.subrange(j, n);
    let rest = ops.subrange(j + 1, n);
    lemma_replay_prepend(after, ops[j], rest);
    lemma_replay_prepend(before, ops[j], rest);
    assert(tail =~= seq![ops[j]] + rest);
    if ops[j] is Rename {
        assert(present(before, ops[j]->Rename_from));
    }
    lemma_replay_step_is_effect(before, ops[j]);
    lemma_replay_step_idempotent(before, ops[j]);
    if ops[j] is SetLink {
        let p = ops[j]->SetLink_path;
        lemma_replay_prepend(before.remove(p), ops[j], rest);
        assert(before.remove(p).insert(p, Entry::Link { target: ops[j]->SetLink_target })
            =~= before.insert(p, Entry::Link { target: ops[j]->SetLink_target }));
    }
}

/// Replaying an op over the state it produced changes nothing.
proof fn lemma_replay_step_idempotent(s: Fs, op: Op)
    requires
        exec_ok(s, op) is Some,
        op is Rename ==> present(s, op->Rename_from),
    ensures
        replay_step(exec_ok(s, op)->Some_0.0, op) == Some(exec_ok(s, op)->Some_0.0),
{
    let t = exec_ok(s, op)->Some_0.0;
    match op {
        Op::Write { path, bytes } => {
            assert(replace(t, path, bytes) =~= t);
        },
        Op::CopyFrom { path, source } => {
            // The bytes at the source are the ones copied, whether or not the
            // source is the target itself.
            assert(t[source]->File_bytes == s[source]->File_bytes);
            assert(replace(t, path, s[source]->File_bytes) =~= t);
        },
        Op::Remove { path } => {
            assert(t.remove(path) =~= t);
        },
        Op::SetExecutable { path, executable } => {
            assert(t.insert(path, t[path]) =~= t);
        },
        Op::SetLink { path, target } => {
            assert(t.insert(path, Entry::Link { target }) =~= t);
        },
        Op::Rename { from, to } => {
            if from != to {
                // The source is gone and the destination holds a file.
                assert(!present(t, from));
                assert(present(t, to));
            } else {
                assert(t =~= s);
                assert(s.remove(from).insert(to, s[from]) =~= s);
            }
        },
    }
}

/// Replaying `[op] + rest` is one step, then the rest.
proof fn lemma_replay_prepend(s: Fs, op: Op, rest: Seq<Op>)
    ensures
        replay(s, seq![op] + rest) == match replay_step(s, op) {
            None => None,
            Some(t) => replay(t, rest),
        },
    decreases rest.len(),
{
    if rest.len() == 0 {
        assert(seq![op] + rest =~= seq![op]);
        assert(seq![op].drop_last() =~= seq![]);
        reveal_with_fuel(replay, 2);
    } else {
        lemma_replay_prepend(s, op, rest.drop_last());
        assert((seq![op] + rest).drop_last() =~= seq![op] + rest.drop_last());
        assert((seq![op] + rest).last() == rest.last());
        match replay_step(s, op) {
            None => {},
            Some(t) => {},
        }
    }
}

// ---- the negative half ----

pub open spec fn file(b: u8) -> Entry {
    fresh(seq![b])
}

/// `a → tmp, b → a, tmp → b` swaps `a` and `b`. Replayed over the swapped tree,
/// it swaps them back and reports success.
pub proof fn counterexample_swap() {
    let (a, b, tmp) = (1int, 2int, 3int);
    let s0: Fs = Map::empty().insert(a, file(65)).insert(b, file(66));
    let ops = seq![
        Op::Rename { from: a, to: tmp },
        Op::Rename { from: b, to: a },
        Op::Rename { from: tmp, to: b },
    ];
    reveal_with_fuel(apply_seq, 4);
    reveal_with_fuel(replay, 4);
    assert(ops.drop_last() =~= seq![Op::Rename { from: a, to: tmp }, Op::Rename { from: b, to: a }]);
    assert(ops.drop_last().drop_last() =~= seq![Op::Rename { from: a, to: tmp }]);
    assert(ops.drop_last().drop_last().drop_last() =~= seq![]);
    let s1 = s0.remove(a).insert(tmp, file(65));
    let s2 = s1.remove(b).insert(a, file(66));
    let s3 = s2.remove(tmp).insert(b, file(65));
    assert(apply_seq(s0, ops)->Some_0.0 == s3);
    // The tree is swapped.
    assert(s3[a] == file(66) && s3[b] == file(65));
    // Replay over it moves `a` (now B) to tmp, `b` (now A) to `a`, and tmp to `b`.
    let r1 = s3.remove(a).insert(tmp, file(66));
    let r2 = r1.remove(b).insert(a, file(65));
    let r3 = r2.remove(tmp).insert(b, file(66));
    assert(replay(s3, ops) == Some(r3));
    assert(r3[a] == file(65) && r3[b] == file(66));
    assert(!same(r3, s3)) by {
        assert(seq![65u8][0] != seq![66u8][0]);
        assert(shape(r3[a]) != shape(s3[a]));
    }
}

/// `old → new`, then a new file at `old`. Replayed over the result, the rename
/// moves the new file over the renamed one, whose bytes are then gone from
/// the tree.
pub proof fn counterexample_recreate() {
    let (old, new) = (1int, 2int);
    let s0: Fs = Map::empty().insert(old, file(79));
    let ops = seq![Op::Rename { from: old, to: new }, Op::Write { path: old, bytes: seq![83u8] }];
    reveal_with_fuel(apply_seq, 3);
    reveal_with_fuel(replay, 3);
    assert(ops.drop_last() =~= seq![Op::Rename { from: old, to: new }]);
    assert(ops.drop_last().drop_last() =~= seq![]);
    let s1 = s0.remove(old).insert(new, file(79));
    let s2 = s1.insert(old, file(83));
    assert(apply_seq(s0, ops)->Some_0.0 == s2);
    let r1 = s2.remove(old).insert(new, file(83));
    let r2 = r1.insert(old, file(83));
    assert(replay(s2, ops) == Some(r2));
    // Nothing in the recovered tree holds the original bytes.
    assert(forall|p: int| r2.dom().contains(p) ==> #[trigger] r2[p] == file(83));
    assert(s2[new] == file(79));
}

/// Remove `b`, then rename `a` over it. Replayed over the result, the remove
/// deletes the only copy of `a`'s bytes, and the rename then finds neither
/// name and fails, leaving the journal in place.
pub proof fn counterexample_remove_then_rename() {
    let (a, b) = (1int, 2int);
    let s0: Fs = Map::empty().insert(a, file(65)).insert(b, file(66));
    let ops = seq![Op::Remove { path: b }, Op::Rename { from: a, to: b }];
    reveal_with_fuel(apply_seq, 3);
    reveal_with_fuel(replay, 3);
    assert(ops.drop_last() =~= seq![Op::Remove { path: b }]);
    assert(ops.drop_last().drop_last() =~= seq![]);
    let s2 = s0.remove(b).remove(a).insert(b, file(65));
    assert(apply_seq(s0, ops)->Some_0.0 =~= s2);
    assert(replay(s2, ops) is None);
}

/// `a → b → c`. Replayed over the result, the first rename finds neither name.
pub proof fn counterexample_chain() {
    let (a, b, c) = (1int, 2int, 3int);
    let s0: Fs = Map::empty().insert(a, file(65));
    let ops = seq![Op::Rename { from: a, to: b }, Op::Rename { from: b, to: c }];
    reveal_with_fuel(apply_seq, 3);
    reveal_with_fuel(replay, 3);
    assert(ops.drop_last() =~= seq![Op::Rename { from: a, to: b }]);
    assert(ops.drop_last().drop_last() =~= seq![]);
    let s2 = s0.remove(a).insert(b, file(65)).remove(b).insert(c, file(65));
    assert(apply_seq(s0, ops)->Some_0.0 == s2);
    assert(replay(s2, ops) is None);
}

/// Make a file executable, then move it. Replayed over the result, the flip
/// finds nothing at the old name.
pub proof fn counterexample_chmod_then_rename() {
    let (run, bin) = (1int, 2int);
    let s0: Fs = Map::empty().insert(run, file(120));
    let ops = seq![
        Op::SetExecutable { path: run, executable: true },
        Op::Rename { from: run, to: bin },
    ];
    reveal_with_fuel(apply_seq, 3);
    reveal_with_fuel(replay, 3);
    assert(ops.drop_last() =~= seq![Op::SetExecutable { path: run, executable: true }]);
    assert(ops.drop_last().drop_last() =~= seq![]);
    let x = Entry::File { bytes: seq![120u8], executable: true, perm: default_perm() };
    let s2 = s0.insert(run, x).remove(run).insert(bin, x);
    assert(apply_seq(s0, ops)->Some_0.0 == s2);
    assert(replay(s2, ops) is None);
}

} // verus!
