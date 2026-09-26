//! `src/path.rs`: `normalize` and `escapes_root`.
//!
//! A path is modeled as the sequence of components `Path::components` yields.
//! A `Normal` component's name is an opaque token, because the algorithm only
//! ever asks which variant a component is. The functions below are the
//! production loop transcribed onto that sequence. What they are proved
//! against is not the loop itself: it is a *meaning* for a path, `lex`, which
//! walks names from a starting directory and fails if it climbs above the
//! root.
//!
//! The trusted step is `std`'s. Production builds a `PathBuf` from the
//! components and `escapes_root` parses it back with `components()`. For a
//! well-formed sequence with no `CurDir`, that round trip gives back the same
//! sequence, and that is assumed here rather than proved.

use vstd::prelude::*;

verus! {

/// One `std::path::Component`, with `Normal`'s name reduced to a token.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Comp {
    Prefix,
    Root,
    Cur,
    Parent,
    Normal(u64),
}

pub open spec fn is_head(c: Comp) -> bool {
    c is Prefix || c is Root
}

/// The shape `Path::components` guarantees: a `Prefix` only first, and a
/// `Root` only first or directly after the `Prefix`.
pub open spec fn well_formed(p: Seq<Comp>) -> bool {
    &&& forall|i: int| 0 <= i < p.len() && (#[trigger] p[i]) is Prefix ==> i == 0
    &&& forall|i: int|
        0 <= i < p.len() && (#[trigger] p[i]) is Root ==> (i == 0 || (i == 1 && p[0] is Prefix))
}

/// A relative path: no `Prefix` and no `Root` anywhere in it.
pub open spec fn relative(p: Seq<Comp>) -> bool {
    forall|i: int| 0 <= i < p.len() ==> !is_head(#[trigger] p[i])
}

// ---- the algorithm, as a spec ----

/// One turn of `normalize`'s loop.
pub open spec fn step(out: Seq<Comp>, c: Comp) -> Seq<Comp> {
    match c {
        Comp::Cur => out,
        Comp::Parent => if out.len() > 0 && out.last() is Normal {
            out.drop_last()
        } else {
            out.push(Comp::Parent)
        },
        _ => out.push(c),
    }
}

pub open spec fn normalize(p: Seq<Comp>) -> Seq<Comp>
    decreases p.len(),
{
    if p.len() == 0 {
        seq![]
    } else {
        step(normalize(p.drop_last()), p.last())
    }
}

pub open spec fn escapes(p: Seq<Comp>) -> bool {
    let n = normalize(p);
    n.len() > 0 && (n[0] is Parent || n[0] is Root || n[0] is Prefix)
}

// ---- what a path means ----

/// Walk `p` from the directory `cwd`, a stack of names under the root.
/// `None` means the walk climbed above the root at some point, or met a
/// component that is not relative.
pub open spec fn lex(cwd: Seq<u64>, p: Seq<Comp>) -> Option<Seq<u64>>
    decreases p.len(),
{
    if p.len() == 0 {
        Some(cwd)
    } else {
        match lex(cwd, p.drop_last()) {
            None => None,
            Some(d) => match p.last() {
                Comp::Cur => Some(d),
                Comp::Parent => if d.len() > 0 { Some(d.drop_last()) } else { None },
                Comp::Normal(n) => Some(d.push(n)),
                _ => None,
            },
        }
    }
}

/// The names a sequence of `Normal` components spells.
pub open spec fn names(p: Seq<Comp>) -> Seq<u64>
    decreases p.len(),
{
    if p.len() == 0 {
        seq![]
    } else {
        names(p.drop_last()).push(p.last()->Normal_0)
    }
}

/// Normal form: no `.`; any head first; then only `..`s; then only names.
pub open spec fn normal_form(p: Seq<Comp>) -> bool {
    &&& well_formed(p)
    &&& forall|i: int| 0 <= i < p.len() ==> !((#[trigger] p[i]) is Cur)
    &&& forall|i: int, j: int| #![trigger p[i], p[j]] 0 <= i < j < p.len() && p[i] is Normal ==> p[j] is Normal
    &&& forall|i: int, j: int| #![trigger p[i], p[j]] 0 <= i < j < p.len() && p[j] is Prefix ==> false
    &&& forall|i: int, j: int| #![trigger p[i], p[j]]
        0 <= i < j < p.len() && p[j] is Root ==> (j == 1 && p[0] is Prefix)
}

// ---- proofs ----

/// The prefix of a well-formed path is well-formed.
proof fn lemma_well_formed_prefix(p: Seq<Comp>)
    requires
        p.len() > 0,
        well_formed(p),
    ensures
        well_formed(p.drop_last()),
{
}

/// Normalizing a path adds no head it did not have: a relative path stays
/// relative.
pub proof fn lemma_normalize_relative(p: Seq<Comp>)
    requires
        relative(p),
    ensures
        relative(normalize(p)),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_normalize_relative(p.drop_last());
        let q = normalize(p.drop_last());
        assert(p.last() == p[p.len() - 1]);
        let r = normalize(p);
        assert forall|i: int| 0 <= i < r.len() implies !is_head(#[trigger] r[i]) by {
            if i < q.len() {
                assert(r[i] == q[i]);
            }
        }
    }
}

/// **Normal form.** Whatever a well-formed path was, `normalize` returns one
/// with no `.`, its head (if any) first, then its surviving `..`s, then names.
pub proof fn lemma_normal_form(p: Seq<Comp>)
    requires
        well_formed(p),
    ensures
        normal_form(normalize(p)),
    decreases p.len(),
{
    if p.len() > 0 {
        let p0 = p.drop_last();
        lemma_well_formed_prefix(p);
        lemma_normal_form(p0);
        let q = normalize(p0);
        let c = p.last();
        assert(c == p[p.len() - 1]);
        let r = normalize(p);
        assert(r == step(q, c));
        if is_head(c) {
            // A head sits at index 0, or at 1 behind a Prefix, so what came
            // before it normalizes to nothing, or to that one Prefix.
            if p.len() == 1 {
                assert(p0 =~= seq![]);
                assert(q =~= seq![]);
            } else {
                assert(p.len() == 2 && p[0] is Prefix && c is Root);
                assert(p0 =~= seq![Comp::Prefix]);
                assert(p0.drop_last() =~= seq![]);
                assert(normalize(p0.drop_last()) =~= seq![]);
                assert(q =~= seq![Comp::Prefix]);
            }
        }
        if c is Parent && !(q.len() > 0 && q.last() is Normal) {
            // No Normal at all in q: its Normals would form a suffix, and the
            // last element is not one.
            assert forall|i: int| 0 <= i < q.len() implies !(q[i] is Normal) by {
                if q[i] is Normal && i < q.len() - 1 {
                    assert(q[q.len() - 1] is Normal);
                }
            }
        }
        if c is Normal || c is Parent {
            // Nothing is appended but a Normal or a Parent, so the head rules
            // carry over from q.
            assert forall|i: int| 0 <= i < r.len() && r[i] is Prefix implies i == 0 by {
                if i < q.len() {
                    assert(r[i] == q[i]);
                }
            }
        }
    }
}

/// The prefix of a path in normal form is in normal form.
proof fn lemma_normal_form_prefix(q: Seq<Comp>)
    requires
        q.len() > 0,
        normal_form(q),
    ensures
        normal_form(q.drop_last()),
{
}

/// **Idempotence.** A path in normal form is its own normalization, so
/// normalizing twice is normalizing once.
pub proof fn lemma_idempotent_on_normal_form(q: Seq<Comp>)
    requires
        normal_form(q),
    ensures
        normalize(q) == q,
    decreases q.len(),
{
    if q.len() > 0 {
        lemma_normal_form_prefix(q);
        lemma_idempotent_on_normal_form(q.drop_last());
        let c = q.last();
        assert(c == q[q.len() - 1]);
        let q0 = q.drop_last();
        if c is Parent && q0.len() > 0 {
            assert(q0.last() == q[q0.len() - 1]);
        }
        assert(step(q0, c) =~= q);
    }
}

pub proof fn lemma_idempotent(p: Seq<Comp>)
    requires
        well_formed(p),
    ensures
        normalize(normalize(p)) == normalize(p),
{
    lemma_normal_form(p);
    lemma_idempotent_on_normal_form(normalize(p));
}

/// `lex` over `q.push(c)` is one more turn over `lex` of `q`.
proof fn lemma_lex_push(cwd: Seq<u64>, q: Seq<Comp>, c: Comp)
    ensures
        lex(cwd, q.push(c)) == match lex(cwd, q) {
            None => None,
            Some(d) => match c {
                Comp::Cur => Some(d),
                Comp::Parent => if d.len() > 0 { Some(d.drop_last()) } else { None },
                Comp::Normal(n) => Some(d.push(n)),
                _ => None,
            },
        },
{
    assert(q.push(c).drop_last() =~= q);
}

/// **Meaning is preserved.** From any starting directory, a relative path and
/// its normalization reach the same place, or both climb out of the root.
pub proof fn lemma_meaning_preserved(cwd: Seq<u64>, p: Seq<Comp>)
    requires
        relative(p),
    ensures
        lex(cwd, normalize(p)) == lex(cwd, p),
    decreases p.len(),
{
    if p.len() > 0 {
        let p0 = p.drop_last();
        lemma_meaning_preserved(cwd, p0);
        let q = normalize(p0);
        let c = p.last();
        assert(c == p[p.len() - 1]);
        match c {
            Comp::Cur => {},
            Comp::Parent => {
                if q.len() > 0 && q.last() is Normal {
                    // Folding `name/..` cancels a push and its pop.
                    let q0 = q.drop_last();
                    assert(q0.push(q.last()) =~= q);
                    lemma_lex_push(cwd, q0, q.last());
                    match lex(cwd, q0) {
                        None => {},
                        Some(d) => {
                            assert(d.push(q.last()->Normal_0).drop_last() =~= d);
                        },
                    }
                } else {
                    lemma_lex_push(cwd, q, c);
                }
            },
            _ => {
                lemma_lex_push(cwd, q, c);
            },
        }
    }
}

/// `lex` from the root, over a normal form with no heads: it fails exactly
/// when there is a `..` left, and otherwise spells the names.
proof fn lemma_lex_normal_form(q: Seq<Comp>)
    requires
        normal_form(q),
        relative(q),
    ensures
        lex(seq![], q) == if q.len() > 0 && q[0] is Parent {
            None::<Seq<u64>>
        } else {
            Some(names(q))
        },
    decreases q.len(),
{
    if q.len() > 0 {
        let q0 = q.drop_last();
        lemma_normal_form_prefix(q);
        lemma_lex_normal_form(q0);
        let c = q.last();
        assert(c == q[q.len() - 1]);
        if q0.len() > 0 {
            assert(q0[0] == q[0]);
        }
        if c is Parent {
            // A trailing `..` means every earlier component is one too, so
            // from the root the walk starts by climbing out.
            if q0.len() > 0 {
                assert(q[0] is Parent) by {
                    if q[0] is Normal {
                        assert(q[q.len() - 1] is Normal);
                    }
                }
            } else {
                assert(q0 =~= seq![]);
            }
        } else {
            assert(c is Normal);
            if q.len() > 1 && q[0] is Parent {
            } else if q0.len() > 0 {
                assert(!(q0[0] is Parent));
            }
        }
    }
}

/// A walk that has climbed out stays out.
pub proof fn lemma_lex_none_absorbs(cwd: Seq<u64>, p: Seq<Comp>, k: int)
    requires
        0 <= k <= p.len(),
        lex(cwd, p.take(k)) is None,
    ensures
        lex(cwd, p) is None,
    decreases p.len() - k,
{
    if k < p.len() {
        assert(p.take(k + 1).drop_last() =~= p.take(k));
        lemma_lex_none_absorbs(cwd, p, k + 1);
    } else {
        assert(p.take(k) =~= p);
    }
}

/// A path whose first component is a head, or a `..`, keeps it first.
proof fn lemma_first_survives(p: Seq<Comp>)
    requires
        p.len() > 0,
        !(p[0] is Normal),
        !(p[0] is Cur),
    ensures
        normalize(p).len() > 0,
        normalize(p)[0] == p[0],
    decreases p.len(),
{
    if p.len() == 1 {
        assert(p.drop_last() =~= seq![]);
        assert(p.last() == p[0]);
    } else {
        let p0 = p.drop_last();
        assert(p0[0] == p[0]);
        lemma_first_survives(p0);
        let q = normalize(p0);
        if p.last() is Parent && q.last() is Normal {
            // q[0] is not Normal, so the Normal being folded is not q[0].
            assert(q.len() > 1);
            assert(q.drop_last()[0] == q[0]);
        }
    }
}

/// **`escapes_root` is exactly right.** A well-formed path escapes if and only
/// if it is not relative, or its walk from the root climbs above the root at
/// some point — at its end, or anywhere before.
pub proof fn theorem_escapes_root(p: Seq<Comp>)
    requires
        well_formed(p),
    ensures
        escapes(p) <==> (!relative(p) || lex(seq![], p) is None),
        !escapes(p) ==> forall|k: int| 0 <= k <= p.len() ==> lex(seq![], #[trigger] p.take(k)) is Some,
        !escapes(p) ==> lex(seq![], p) == Some(names(normalize(p))),
{
    lemma_normal_form(p);
    if !relative(p) {
        // Well-formedness puts the head first, and nothing folds it away.
        let i = choose|i: int| 0 <= i < p.len() && is_head(#[trigger] p[i]);
        assert(is_head(p[0]));
        lemma_first_survives(p);
    } else {
        lemma_normalize_relative(p);
        lemma_meaning_preserved(seq![], p);
        lemma_lex_normal_form(normalize(p));
        if !escapes(p) {
            assert forall|k: int| 0 <= k <= p.len() implies lex(seq![], #[trigger] p.take(k)) is Some by {
                if lex(seq![], p.take(k)) is None {
                    lemma_lex_none_absorbs(seq![], p, k);
                }
            }
        }
    }
}

// ---- the unit tests in `src/path.rs`, as facts about the spec ----

/// `a/../../b` normalizes to `../b`, and so escapes; `notes/../a.md` does not.
proof fn examples() {
    let (a, b) = (Comp::Normal(1), Comp::Normal(2));
    let p = seq![a, Comp::Parent, Comp::Parent, b];
    assert(normalize(p) =~= seq![Comp::Parent, b]) by {
        reveal_with_fuel(normalize, 5);
        assert(p.drop_last() =~= seq![a, Comp::Parent, Comp::Parent]);
        assert(p.drop_last().drop_last() =~= seq![a, Comp::Parent]);
        assert(p.drop_last().drop_last().drop_last() =~= seq![a]);
        assert(p.drop_last().drop_last().drop_last().drop_last() =~= seq![]);
        assert(seq![a].drop_last() =~= seq![]);
    }
    assert(escapes(p));
    let q = seq![a, Comp::Parent, b];
    assert(normalize(q) =~= seq![b]) by {
        reveal_with_fuel(normalize, 4);
        assert(q.drop_last() =~= seq![a, Comp::Parent]);
        assert(q.drop_last().drop_last() =~= seq![a]);
        assert(q.drop_last().drop_last().drop_last() =~= seq![]);
    }
    assert(!escapes(q));
}

// ---- the production code, transcribed ----

/// `normalize`, as `src/path.rs` writes it.
pub fn exec_normalize(path: &Vec<Comp>) -> (out: Vec<Comp>)
    ensures
        out@ == normalize(path@),
{
    let mut out: Vec<Comp> = Vec::new();
    let mut i: usize = 0;
    while i < path.len()
        invariant
            i <= path.len(),
            out@ == normalize(path@.take(i as int)),
        decreases path.len() - i,
    {
        let component = path[i];
        assert(path@.take(i as int + 1).drop_last() =~= path@.take(i as int));
        assert(path@.take(i as int + 1).last() == component);
        match component {
            Comp::Cur => {},
            Comp::Parent => {
                if out.len() > 0 && matches!(out[out.len() - 1], Comp::Normal(_)) {
                    out.pop();
                } else {
                    out.push(component);
                }
            },
            other => {
                out.push(other);
            },
        }
        i += 1;
    }
    assert(path@.take(path.len() as int) =~= path@);
    out
}

/// `escapes_root`, as `src/path.rs` writes it — reading the first component of
/// the normalized path (the `PathBuf` round trip is the trusted step).
pub fn exec_escapes_root(path: &Vec<Comp>) -> (b: bool)
    ensures
        b == escapes(path@),
{
    let n = exec_normalize(path);
    n.len() > 0 && matches!(n[0], Comp::Parent | Comp::Root | Comp::Prefix)
}

} // verus!
