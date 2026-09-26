//! `src/change.rs`: what happens when `Journal::apply` hits an error.
//!
//! The tree is a map from path to entry. Paths are opaque tokens here, and
//! `path.rs` covers lexical containment. Every op runs as `exec` runs it: it
//! records its undo entries at the moment it executes, performs its effect,
//! and may fail at any of the points where `exec` can return `Err`. The first
//! failure — or a failed certifying flush after every op landed — unwinds
//! everything recorded, in reverse, as `unwind_durable` does.
//!
//! **What is proved** (`theorem_error_atomicity`): whichever op fails, and
//! wherever inside it, if the unwind's own calls do not fail, the unwind
//! succeeds and gives back the tree the set started from — every path present
//! or absent as before, every file holding its old bytes, every link its old
//! target.
//!
//! **What is not true** (`counterexample_permissions`): the tree is not given
//! back *with its permissions*. A file the set removed, displaced with a
//! rename, or replaced with a link comes back through a plain `write` onto an
//! absent path, and so gets the backend's default mode: its execute bit and
//! any narrowing such as `0600` are lost. The theorem is stated over contents
//! because the full statement is false.
//!
//! Not modeled: directories (`ensure_parent`'s chains are not unwound, and
//! the source says so), the staging siblings `replace` removes on failure,
//! durability (the flushes are only failure points here), and reading
//! *through* a link, which is conservatively an error.

use vstd::prelude::*;

verus! {

pub enum Entry {
    File { bytes: Seq<u8>, executable: bool, perm: nat },
    Link { target: int },
}

pub type Fs = Map<int, Entry>;

/// The mode a freshly created file is given (0o644 under a usual umask).
pub open spec fn default_perm() -> nat {
    420
}

pub open spec fn fresh(bytes: Seq<u8>) -> Entry {
    Entry::File { bytes, executable: false, perm: default_perm() }
}

/// What the theorem compares: an entry without its mode.
pub enum Shape {
    File(Seq<u8>),
    Link(int),
}

pub open spec fn shape(e: Entry) -> Shape {
    match e {
        Entry::File { bytes, .. } => Shape::File(bytes),
        Entry::Link { target } => Shape::Link(target),
    }
}

/// Same paths, and each holds the same bytes or the same link.
pub open spec fn same(a: Fs, b: Fs) -> bool {
    &&& a.dom() == b.dom()
    &&& forall|p: int| a.dom().contains(p) ==> shape(#[trigger] a[p]) == shape(b[p])
}

pub enum Op {
    Write { path: int, bytes: Seq<u8> },
    Rename { from: int, to: int },
    Remove { path: int },
    CopyFrom { path: int, source: int },
    SetExecutable { path: int, executable: bool },
    SetLink { path: int, target: int },
}

/// `change::Undo`, variant for variant.
pub enum Undo {
    Restore { path: int, bytes: Seq<u8> },
    Delete { path: int },
    Rename { from: int, to: int },
    SetExecutable { path: int, executable: bool },
    Relink { path: int, target: int },
    RestoreOverLink { path: int, bytes: Seq<u8> },
}

// ---- the storage port ----

/// `Storage::write`: the bytes land in the existing file (its mode kept), or
/// a new one is made with the default mode. Through a link it would write the
/// link's referent, which is outside this model — so `None`, and the proofs
/// show the unwind never asks for it.
pub open spec fn write(s: Fs, p: int, bytes: Seq<u8>) -> Option<Fs> {
    if !s.dom().contains(p) {
        Some(s.insert(p, fresh(bytes)))
    } else {
        match s[p] {
            Entry::File { executable, perm, .. } => Some(s.insert(p, Entry::File { bytes, executable, perm })),
            Entry::Link { .. } => None,
        }
    }
}

/// `Storage::replace`: a staged sibling, `copy_permissions` from the target
/// onto it, and a rename over the target. The mode a replaced link leaves is
/// its referent's; it is the default here, and nothing below depends on it.
pub open spec fn replace(s: Fs, p: int, bytes: Seq<u8>) -> Fs {
    if s.dom().contains(p) && s[p] is File {
        s.insert(p, Entry::File { bytes, executable: s[p]->File_executable, perm: s[p]->File_perm })
    } else {
        s.insert(p, fresh(bytes))
    }
}

pub open spec fn rename(s: Fs, from: int, to: int) -> Option<Fs> {
    if s.dom().contains(from) {
        Some(s.remove(from).insert(to, s[from]))
    } else {
        None
    }
}

// ---- exec ----

/// `capture_replaced`.
pub open spec fn capture(s: Fs, p: int) -> Undo {
    if !s.dom().contains(p) {
        Undo::Delete { path: p }
    } else {
        match s[p] {
            Entry::Link { target } => Undo::Relink { path: p, target },
            Entry::File { bytes, .. } => Undo::Restore { path: p, bytes },
        }
    }
}

/// The undo entries an op records *before* its effect, or `None` where the
/// op cannot get that far (a read that fails, a guard that refuses).
pub open spec fn pre_undo(s: Fs, op: Op) -> Option<Seq<Undo>> {
    match op {
        Op::Write { path, .. } => Some(seq![capture(s, path)]),
        Op::CopyFrom { path, source } => if s.dom().contains(source) && s[source] is File {
            Some(seq![capture(s, path)])
        } else {
            None
        },
        Op::Rename { to, .. } => Some(seq![capture(s, to)]),
        // The read happens first, so a missing file fails before anything.
        Op::Remove { path } => if s.dom().contains(path) {
            Some(seq![])
        } else {
            None
        },
        // `guard_not_link`, then `executable`, which errors on a missing file.
        Op::SetExecutable { path, .. } => if s.dom().contains(path) && s[path] is File {
            Some(seq![Undo::SetExecutable { path, executable: s[path]->File_executable }])
        } else {
            None
        },
        Op::SetLink { path, .. } => Some(
            seq![
                if !s.dom().contains(path) {
                    Undo::Delete { path }
                } else {
                    match s[path] {
                        Entry::Link { target } => Undo::Relink { path, target },
                        Entry::File { bytes, .. } => Undo::RestoreOverLink { path, bytes },
                    }
                },
            ],
        ),
    }
}

/// The op's effect, or `None` where its mutating call fails (atomically:
/// nothing changes).
pub open spec fn effect(s: Fs, op: Op) -> Option<Fs> {
    match op {
        Op::Write { path, bytes } => Some(replace(s, path, bytes)),
        Op::CopyFrom { path, source } => Some(replace(s, path, s[source]->File_bytes)),
        Op::Rename { from, to } => rename(s, from, to),
        Op::Remove { path } => Some(s.remove(path)),
        Op::SetExecutable { path, executable } => Some(
            s.insert(
                path,
                Entry::File { bytes: s[path]->File_bytes, executable, perm: s[path]->File_perm },
            ),
        ),
        Op::SetLink { path, target } => Some(s.insert(path, Entry::Link { target })),
    }
}

/// The undo entries recorded *after* the effect.
pub open spec fn post_undo(s: Fs, op: Op) -> Seq<Undo> {
    match op {
        Op::Rename { from, to } => seq![Undo::Rename { from: to, to: from }],
        Op::Remove { path } => seq![capture(s, path)],
        _ => seq![],
    }
}

/// An op that completes: its new state and everything it recorded.
pub open spec fn exec_ok(s: Fs, op: Op) -> Option<(Fs, Seq<Undo>)> {
    match (pre_undo(s, op), effect(s, op)) {
        (Some(pre), Some(t)) => Some((t, pre + post_undo(s, op))),
        _ => None,
    }
}

/// Where inside an op the error lands.
pub enum Fault {
    /// Before anything was recorded or changed.
    Early,
    /// After the pre-effect undo was recorded, with the effect failing
    /// atomically.
    Captured,
    /// `set_link` only: its contract is "replaces whatever is there", not
    /// "in one step", so a failure can leave the path holding nothing.
    Torn,
    /// After the effect landed — a barrier after it failed.
    Late,
}

/// The state and undo log an op leaves when it fails at `f`, or `None` where
/// `f` cannot happen to this op in this state.
pub open spec fn exec_fail(s: Fs, op: Op, f: Fault) -> Option<(Fs, Seq<Undo>)> {
    match f {
        Fault::Early => Some((s, seq![])),
        Fault::Captured => match pre_undo(s, op) {
            Some(pre) => Some((s, pre)),
            None => None,
        },
        Fault::Torn => match (op, pre_undo(s, op)) {
            (Op::SetLink { path, .. }, Some(pre)) => Some((s.remove(path), pre)),
            _ => None,
        },
        Fault::Late => exec_ok(s, op),
    }
}

/// Ops run in order until one does not complete.
pub open spec fn apply_seq(s: Fs, ops: Seq<Op>) -> Option<(Fs, Seq<Undo>)>
    decreases ops.len(),
{
    if ops.len() == 0 {
        Some((s, seq![]))
    } else {
        match apply_seq(s, ops.drop_last()) {
            None => None,
            Some((m, u)) => match exec_ok(m, ops.last()) {
                None => None,
                Some((t, v)) => Some((t, u + v)),
            },
        }
    }
}

// ---- unwind_durable ----

pub open spec fn undo_step(s: Fs, u: Undo) -> Option<Fs> {
    match u {
        Undo::Restore { path, bytes } => write(s, path, bytes),
        // Tolerant of finding nothing.
        Undo::Delete { path } => Some(s.remove(path)),
        Undo::Rename { from, to } => rename(s, from, to),
        Undo::SetExecutable { path, executable } => if s.dom().contains(path) && s[path] is File {
            Some(
                s.insert(
                    path,
                    Entry::File { bytes: s[path]->File_bytes, executable, perm: s[path]->File_perm },
                ),
            )
        } else {
            None
        },
        Undo::Relink { path, target } => Some(s.insert(path, Entry::Link { target })),
        // Remove (tolerantly), then write onto the empty path.
        Undo::RestoreOverLink { path, bytes } => Some(s.insert(path, fresh(bytes))),
    }
}

/// Undo entries run last-recorded first.
pub open spec fn unwind(s: Fs, us: Seq<Undo>) -> Option<Fs>
    decreases us.len(),
{
    if us.len() == 0 {
        Some(s)
    } else {
        match undo_step(s, us.last()) {
            None => None,
            Some(t) => unwind(t, us.drop_last()),
        }
    }
}

// ---- proofs ----

proof fn lemma_same_refl(a: Fs)
    ensures
        same(a, a),
{
}

proof fn lemma_same_trans(a: Fs, b: Fs, c: Fs)
    requires
        same(a, b),
        same(b, c),
    ensures
        same(a, c),
{
    assert forall|p: int| a.dom().contains(p) implies shape(#[trigger] a[p]) == shape(c[p]) by {
        assert(b.dom().contains(p));
        assert(shape(b[p]) == shape(c[p]));
    }
}

/// An undo step cannot tell two states apart that differ only in modes.
proof fn lemma_undo_step_congruent(a: Fs, b: Fs, u: Undo)
    requires
        same(a, b),
    ensures
        undo_step(a, u) is Some <==> undo_step(b, u) is Some,
        undo_step(a, u) is Some ==> same(undo_step(a, u)->Some_0, undo_step(b, u)->Some_0),
{
    match u {
        Undo::Restore { path, .. } => {
            if a.dom().contains(path) {
                assert(shape(a[path]) == shape(b[path]));
            }
        },
        Undo::Rename { from, to } => {
            if a.dom().contains(from) {
                assert(shape(a[from]) == shape(b[from]));
            }
            let (x, y) = (a.remove(from).insert(to, a[from]), b.remove(from).insert(to, b[from]));
            assert(x.dom() =~= y.dom());
        },
        Undo::SetExecutable { path, .. } => {
            if a.dom().contains(path) {
                assert(shape(a[path]) == shape(b[path]));
            }
        },
        Undo::Delete { path } => {
            assert(a.remove(path).dom() =~= b.remove(path).dom());
        },
        _ => {},
    }
}

proof fn lemma_unwind_congruent(a: Fs, b: Fs, us: Seq<Undo>)
    requires
        same(a, b),
    ensures
        unwind(a, us) is Some <==> unwind(b, us) is Some,
        unwind(a, us) is Some ==> same(unwind(a, us)->Some_0, unwind(b, us)->Some_0),
    decreases us.len(),
{
    if us.len() > 0 {
        lemma_undo_step_congruent(a, b, us.last());
        if undo_step(a, us.last()) is Some {
            lemma_unwind_congruent(
                undo_step(a, us.last())->Some_0,
                undo_step(b, us.last())->Some_0,
                us.drop_last(),
            );
        }
    }
}

/// Unwinding `u + v` is unwinding `v`, then `u`.
proof fn lemma_unwind_append(s: Fs, u: Seq<Undo>, v: Seq<Undo>)
    ensures
        unwind(s, u + v) == match unwind(s, v) {
            None => None,
            Some(t) => unwind(t, u),
        },
    decreases v.len(),
{
    if v.len() == 0 {
        assert(u + v =~= u);
    } else {
        assert((u + v).last() == v.last());
        assert((u + v).drop_last() =~= u + v.drop_last());
        match undo_step(s, v.last()) {
            None => {},
            Some(t) => lemma_unwind_append(t, u, v.drop_last()),
        }
    }
}

/// One undo step on its own.
proof fn lemma_unwind_one(s: Fs, u: Undo)
    ensures
        unwind(s, seq![u]) == undo_step(s, u),
{
    reveal_with_fuel(unwind, 2);
    assert(seq![u].drop_last() =~= seq![]);
    assert(seq![u].last() == u);
}

/// Two undo steps, the second recorded first.
proof fn lemma_unwind_two(s: Fs, u: Undo, v: Undo)
    ensures
        unwind(s, seq![u, v]) == match undo_step(s, v) {
            None => None,
            Some(t) => undo_step(t, u),
        },
{
    assert(seq![u, v].drop_last() =~= seq![u]);
    assert(seq![u, v].last() == v);
    match undo_step(s, v) {
        None => {},
        Some(t) => lemma_unwind_one(t, u),
    }
}

/// Undoing the capture of `p` puts `p` back as it was in `s`, from any state
/// that agrees with `s` everywhere else. Where the undo is a `Restore` —
/// `p` held a file — the state must hold nothing at `p`, or a file: a plain
/// `write` onto a link would land the bytes in its referent.
proof fn lemma_capture_restores(s: Fs, t: Fs, p: int)
    requires
        forall|q: int| q != p ==> (s.dom().contains(q) <==> t.dom().contains(q)),
        forall|q: int| q != p && s.dom().contains(q) ==> #[trigger] s[q] == t[q],
        capture(s, p) is Restore ==> (t.dom().contains(p) ==> t[p] is File),
    ensures
        undo_step(t, capture(s, p)) is Some,
        same(undo_step(t, capture(s, p))->Some_0, s),
{
    let r = undo_step(t, capture(s, p))->Some_0;
    assert(r.dom() =~= s.dom());
    assert forall|q: int| r.dom().contains(q) implies shape(#[trigger] r[q]) == shape(s[q]) by {
        if q != p {
            assert(s[q] == t[q]);
        }
    }
}

/// **Per op.** Whatever an op recorded before it failed (or completed) puts
/// the state back to what the op found.
proof fn lemma_op_unwinds(s: Fs, op: Op, f: Fault)
    requires
        exec_fail(s, op, f) is Some,
    ensures
        ({
            let (t, us) = exec_fail(s, op, f)->Some_0;
            unwind(t, us) is Some && same(unwind(t, us)->Some_0, s)
        }),
{
    let (t, us) = exec_fail(s, op, f)->Some_0;
    lemma_same_refl(s);
    match f {
        Fault::Early => {},
        Fault::Captured => {
            // Nothing changed; each recorded entry puts back what is there.
            match op {
                Op::Remove { .. } => {},
                Op::SetExecutable { path, .. } => {
                    lemma_unwind_one(s, us[0]);
                    let r = undo_step(s, us[0])->Some_0;
                    assert(r.dom() =~= s.dom());
                },
                Op::SetLink { path, .. } => {
                    lemma_unwind_one(s, us[0]);
                    let r = undo_step(s, us[0])->Some_0;
                    assert(r.dom() =~= s.dom());
                },
                Op::Write { path, .. } => {
                    lemma_unwind_one(s, us[0]);
                    lemma_capture_restores(s, s, path);
                },
                Op::CopyFrom { path, .. } => {
                    lemma_unwind_one(s, us[0]);
                    lemma_capture_restores(s, s, path);
                },
                Op::Rename { to, .. } => {
                    lemma_unwind_one(s, us[0]);
                    lemma_capture_restores(s, s, to);
                },
            }
        },
        Fault::Torn => {
            let path = op->SetLink_path;
            lemma_unwind_one(t, us[0]);
            let r = undo_step(t, us[0])->Some_0;
            assert(r.dom() =~= s.dom());
        },
        Fault::Late => {
            let pre = pre_undo(s, op)->Some_0;
            match op {
                Op::Write { path, bytes } => {
                    assert(us =~= seq![capture(s, path)]);
                    lemma_unwind_one(t, us[0]);
                    lemma_capture_restores(s, t, path);
                },
                Op::CopyFrom { path, source } => {
                    assert(us =~= seq![capture(s, path)]);
                    lemma_unwind_one(t, us[0]);
                    lemma_capture_restores(s, t, path);
                },
                Op::Remove { path } => {
                    assert(us =~= seq![capture(s, path)]);
                    lemma_unwind_one(t, us[0]);
                    let r = undo_step(t, us[0])->Some_0;
                    assert(r.dom() =~= s.dom());
                },
                Op::SetExecutable { path, .. } => {
                    assert(us =~= pre);
                    lemma_unwind_one(t, us[0]);
                    let r = undo_step(t, us[0])->Some_0;
                    assert(r.dom() =~= s.dom());
                },
                Op::SetLink { path, .. } => {
                    assert(us =~= pre);
                    lemma_unwind_one(t, us[0]);
                    let r = undo_step(t, us[0])->Some_0;
                    assert(r.dom() =~= s.dom());
                },
                Op::Rename { from, to } => {
                    // The mover goes home first; then the occupant it
                    // displaced is put back in the name it vacated.
                    assert(us =~= seq![capture(s, to), Undo::Rename { from: to, to: from }]);
                    lemma_unwind_two(t, capture(s, to), Undo::Rename { from: to, to: from });
                    let m = undo_step(t, Undo::Rename { from: to, to: from })->Some_0;
                    if from == to {
                        assert(t =~= s);
                        assert(m =~= s);
                        lemma_capture_restores(s, m, to);
                    } else {
                        assert(m =~= s.remove(to));
                        lemma_capture_restores(s, m, to);
                    }
                },
            }
        },
    }
}

/// Unwinding everything a run of completed ops recorded, from any state that
/// agrees with where the run ended, gets back to where it began.
proof fn lemma_run_unwinds(s0: Fs, ops: Seq<Op>, t: Fs)
    requires
        apply_seq(s0, ops) is Some,
        same(t, apply_seq(s0, ops)->Some_0.0),
    ensures
        unwind(t, apply_seq(s0, ops)->Some_0.1) is Some,
        same(unwind(t, apply_seq(s0, ops)->Some_0.1)->Some_0, s0),
    decreases ops.len(),
{
    if ops.len() == 0 {
        lemma_same_trans(t, s0, s0);
    } else {
        let (m, u) = apply_seq(s0, ops.drop_last())->Some_0;
        let (e, v) = exec_ok(m, ops.last())->Some_0;
        // `exec_ok` is the `Late` fault's outcome.
        assert(exec_fail(m, ops.last(), Fault::Late) == exec_ok(m, ops.last()));
        lemma_op_unwinds(m, ops.last(), Fault::Late);
        lemma_unwind_append(t, u, v);
        lemma_unwind_congruent(t, e, v);
        let back = unwind(t, v)->Some_0;
        lemma_same_trans(back, unwind(e, v)->Some_0, m);
        lemma_run_unwinds(s0, ops.drop_last(), back);
    }
}

/// **Error atomicity.** Run the first `k` ops of a set; then either op `k`
/// fails at `f`, or (`k` is the whole set) the certifying flush fails. If the
/// unwind's own calls do not fail, it succeeds, and every path holds what it
/// held before the set began.
pub proof fn theorem_error_atomicity(s0: Fs, ops: Seq<Op>, k: int, f: Fault)
    requires
        0 <= k <= ops.len(),
        apply_seq(s0, ops.take(k)) is Some,
        k < ops.len() ==> exec_fail(apply_seq(s0, ops.take(k))->Some_0.0, ops[k], f) is Some,
    ensures
        ({
            let (m, u) = apply_seq(s0, ops.take(k))->Some_0;
            let (t, v) = if k < ops.len() {
                exec_fail(m, ops[k], f)->Some_0
            } else {
                (m, seq![])
            };
            unwind(t, u + v) is Some && same(unwind(t, u + v)->Some_0, s0)
        }),
{
    let (m, u) = apply_seq(s0, ops.take(k))->Some_0;
    let (t, v) = if k < ops.len() {
        exec_fail(m, ops[k], f)->Some_0
    } else {
        (m, seq![])
    };
    lemma_unwind_append(t, u, v);
    if k < ops.len() {
        lemma_op_unwinds(m, ops[k], f);
    } else {
        lemma_same_refl(m);
    }
    let back = unwind(t, v)->Some_0;
    lemma_run_unwinds(s0, ops.take(k), back);
}

/// **Not with its permissions.** An executable file, removed by a set whose
/// next op fails: the rollback succeeds, the bytes are back, and the file is
/// no longer executable. The same holds for any narrowed mode, and for a file
/// displaced by a rename or replaced by a link.
pub proof fn counterexample_permissions() {
    let tool = 1int;
    let missing = 2int;
    let script = Entry::File { bytes: seq![35u8, 33u8], executable: true, perm: 493 };  // 0o755
    let s0: Fs = Map::empty().insert(tool, script);
    let ops = seq![Op::Remove { path: tool }, Op::Remove { path: missing }];

    // `remove tool` completes.
    reveal_with_fuel(apply_seq, 2);
    assert(ops.take(1) =~= seq![Op::Remove { path: tool }]);
    assert(ops.take(1).drop_last() =~= seq![]);
    let m = s0.remove(tool);
    let u = seq![Undo::Restore { path: tool, bytes: seq![35u8, 33u8] }];
    assert(seq![] + u =~= u);
    assert(apply_seq(s0, ops.take(1)) == Some((m, u)));
    // `remove missing` fails reading the file it would take out.
    assert(pre_undo(m, ops[1]) is None);
    assert(exec_fail(m, ops[1], Fault::Early) == Some((m, Seq::<Undo>::empty())));
    assert(u + seq![] =~= u);
    lemma_unwind_one(m, u[0]);
    let r = unwind(m, u)->Some_0;
    assert(r[tool] == fresh(seq![35u8, 33u8]));
    assert(same(r, s0)) by {
        assert(r.dom() =~= s0.dom());
    }
    assert(r != s0) by {
        assert(r[tool] != s0[tool]);
    }
}

} // verus!
