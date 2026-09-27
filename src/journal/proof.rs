//! The journal's format as the proofs see it: the bytes [`encode`](super::encode)
//! writes for a set, and what [`decode`](super::decode) is proved to read back
//! from them. Compiled only by Verus (`verus_keep_ghost`).
//!
//! A journal is the magic, the op count, each op, and a checksum of all of
//! it, every number eight bytes little-endian and every path or payload
//! prefixed by its length. [`journal`] says so, and is `None` for a set with a
//! path that is not UTF-8, which `encode` refuses.

use std::path::PathBuf;

use vstd::prelude::*;

use crate::change::FileOp;
use crate::port::utf8;

verus! {

/// `x`, eight bytes little-endian.
pub(crate) open spec fn le(x: u64) -> Seq<u8> {
    seq![
        x as u8,
        (x >> 8u64) as u8,
        (x >> 16u64) as u8,
        (x >> 24u64) as u8,
        (x >> 32u64) as u8,
        (x >> 40u64) as u8,
        (x >> 48u64) as u8,
        (x >> 56u64) as u8,
    ]
}

/// The number eight little-endian bytes spell.
pub(crate) open spec fn unle(b: Seq<u8>) -> u64 {
    (b[0] as u64) | ((b[1] as u64) << 8u64) | ((b[2] as u64) << 16u64) | ((b[3] as u64) << 24u64)
        | ((b[4] as u64) << 32u64) | ((b[5] as u64) << 40u64) | ((b[6] as u64) << 48u64) | ((b[7]
        as u64) << 56u64)
}

pub(crate) proof fn lemma_le(x: u64)
    ensures
        le(x).len() == 8,
        unle(le(x)) == x,
{
    let b = le(x);
    assert(b[0] == x as u8 && b[1] == (x >> 8u64) as u8 && b[2] == (x >> 16u64) as u8 && b[3] == (x
        >> 24u64) as u8 && b[4] == (x >> 32u64) as u8 && b[5] == (x >> 40u64) as u8 && b[6] == (x
        >> 48u64) as u8 && b[7] == (x >> 56u64) as u8);
    assert(x == ((x as u8) as u64) | ((((x >> 8u64) as u8) as u64) << 8u64) | ((((x >> 16u64) as u8)
        as u64) << 16u64) | ((((x >> 24u64) as u8) as u64) << 24u64) | ((((x >> 32u64) as u8)
        as u64) << 32u64) | ((((x >> 40u64) as u8) as u64) << 40u64) | ((((x >> 48u64) as u8)
        as u64) << 48u64) | ((((x >> 56u64) as u8) as u64) << 56u64)) by (bit_vector);
}

pub(crate) open spec fn fnv_basis() -> u64 {
    0xcbf2_9ce4_8422_2325
}

pub(crate) open spec fn fnv_prime() -> u64 {
    0x0000_0100_0000_01b3
}

/// FNV-1a, 64-bit.
pub(crate) open spec fn fnv(s: Seq<u8>) -> u64
    decreases s.len(),
{
    if s.len() == 0 {
        fnv_basis()
    } else {
        (((fnv(s.drop_last()) ^ (s.last() as u64)) as int * fnv_prime() as int) % 0x1_0000_0000_0000_0000int) as u64
    }
}

/// A length-prefixed field.
pub(crate) open spec fn field(b: Seq<u8>) -> Seq<u8> {
    le(b.len() as u64) + b
}

/// An op with one path, and what follows it.
pub(crate) open spec fn one(tag: u8, p: PathBuf, rest: Seq<u8>) -> Option<Seq<u8>> {
    match utf8(p) {
        Some(t) => Some(seq![tag] + field(t) + rest),
        None => None,
    }
}

/// An op with two paths.
pub(crate) open spec fn two(tag: u8, p: PathBuf, q: PathBuf) -> Option<Seq<u8>> {
    match (utf8(p), utf8(q)) {
        (Some(t), Some(u)) => Some(seq![tag] + field(t) + field(u)),
        _ => None,
    }
}

/// One op's record.
pub(crate) open spec fn enc_op(op: FileOp) -> Option<Seq<u8>> {
    match op {
        FileOp::Write { path, bytes } => one(0, path, field(bytes@)),
        FileOp::Rename { from, to } => two(1, from, to),
        FileOp::Remove { path } => one(2, path, Seq::empty()),
        FileOp::CopyFrom { path, source } => two(3, path, source),
        FileOp::SetExecutable { path, executable } => one(4, path, seq![if executable { 1u8 } else { 0u8 }]),
        FileOp::SetLink { path, target } => two(5, path, target),
    }
}

/// Every op's record, in order.
pub(crate) open spec fn enc_ops(ops: Seq<FileOp>) -> Option<Seq<u8>>
    decreases ops.len(),
{
    if ops.len() == 0 {
        Some(Seq::empty())
    } else {
        match (enc_ops(ops.drop_last()), enc_op(ops.last())) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        }
    }
}

/// What the checksum covers: the magic, the count, the ops.
pub(crate) open spec fn body(magic: Seq<u8>, ops: Seq<FileOp>) -> Option<Seq<u8>> {
    match enc_ops(ops) {
        Some(e) => Some(magic + le(ops.len() as u64) + e),
        None => None,
    }
}

/// The journal `encode` writes for `ops`.
pub(crate) open spec fn journal(magic: Seq<u8>, ops: Seq<FileOp>) -> Option<Seq<u8>> {
    match body(magic, ops) {
        Some(b) => Some(b + le(fnv(b))),
        None => None,
    }
}

/// Two ops that are the same op: the same paths, the same bytes.
pub(crate) open spec fn same_op(a: FileOp, b: FileOp) -> bool {
    match (a, b) {
        (FileOp::Write { path: p, bytes: x }, FileOp::Write { path: q, bytes: y }) => p == q && x@ == y@,
        (FileOp::Rename { from: p, to: x }, FileOp::Rename { from: q, to: y }) => p == q && x == y,
        (FileOp::Remove { path: p }, FileOp::Remove { path: q }) => p == q,
        (FileOp::CopyFrom { path: p, source: x }, FileOp::CopyFrom { path: q, source: y }) => p == q && x == y,
        (FileOp::SetExecutable { path: p, executable: x }, FileOp::SetExecutable { path: q, executable: y }) => p
            == q && x == y,
        (FileOp::SetLink { path: p, target: x }, FileOp::SetLink { path: q, target: y }) => p == q && x == y,
        _ => false,
    }
}

pub(crate) open spec fn same_ops(a: Seq<FileOp>, b: Seq<FileOp>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] same_op(a[i], b[i])
}

/// The field that starts at `at`, if the bytes hold it whole.
pub(crate) open spec fn field_at(b: Seq<u8>, at: int) -> Option<Seq<u8>> {
    if 0 <= at && at + 8 <= b.len() && at + 8 + unle(b.subrange(at, at + 8)) as int <= b.len() {
        Some(b.subrange(at + 8, at + 8 + unle(b.subrange(at, at + 8)) as int))
    } else {
        None
    }
}

pub(crate) open spec fn tag(op: FileOp) -> u8 {
    match op {
        FileOp::Write { .. } => 0,
        FileOp::Rename { .. } => 1,
        FileOp::Remove { .. } => 2,
        FileOp::CopyFrom { .. } => 3,
        FileOp::SetExecutable { .. } => 4,
        FileOp::SetLink { .. } => 5,
    }
}

/// The path an op's record names first.
pub(crate) open spec fn first(op: FileOp) -> PathBuf {
    match op {
        FileOp::Write { path, .. } | FileOp::Remove { path } | FileOp::CopyFrom { path, .. }
        | FileOp::SetExecutable { path, .. } | FileOp::SetLink { path, .. } => path,
        FileOp::Rename { from, .. } => from,
    }
}

/// The path an op's record names second, for the ops that name two.
pub(crate) open spec fn second(op: FileOp) -> PathBuf {
    match op {
        FileOp::Rename { to, .. } => to,
        FileOp::CopyFrom { source, .. } => source,
        FileOp::SetLink { target, .. } => target,
        _ => arbitrary(),
    }
}

/// A write's payload.
pub(crate) open spec fn payload(op: FileOp) -> Seq<u8> {
    match op {
        FileOp::Write { bytes, .. } => bytes@,
        _ => arbitrary(),
    }
}

/// An execute-bit flip's byte.
pub(crate) open spec fn flag(op: FileOp) -> u8 {
    match op {
        FileOp::SetExecutable { executable, .. } => if executable { 1u8 } else { 0u8 },
        _ => arbitrary(),
    }
}

pub(crate) open spec fn names_two(op: FileOp) -> bool {
    op is Rename || op is CopyFrom || op is SetLink
}

/// A field laid down at `at` is read back from there.
pub(crate) proof fn lemma_field_at(b: Seq<u8>, at: int, x: Seq<u8>)
    requires
        0 <= at,
        at + 8 + x.len() <= b.len(),
        b.len() < 0x1_0000_0000_0000_0000int,
        b.subrange(at, at + 8 + x.len()) == field(x),
    ensures
        field_at(b, at) == Some(x),
{
    lemma_le(x.len() as u64);
    assert(b.subrange(at, at + 8) =~= field(x).subrange(0, 8));
    assert(field(x).subrange(0, 8) =~= le(x.len() as u64));
    assert(b.subrange(at + 8, at + 8 + x.len()) =~= field(x).subrange(8, 8 + x.len() as int));
    assert(field(x).subrange(8, 8 + x.len() as int) =~= x);
}

/// Bytes `b` hold `s` at `at`: they hold each piece of it where it falls.
pub(crate) proof fn lemma_piece(b: Seq<u8>, at: int, s: Seq<u8>, i: int, j: int)
    requires
        0 <= at,
        0 <= i <= j <= s.len(),
        at + s.len() <= b.len(),
        b.subrange(at, at + s.len()) == s,
    ensures
        b.subrange(at + i, at + j) == s.subrange(i, j),
{
    assert forall|x: int| 0 <= x < j - i implies b.subrange(at + i, at + j)[x] == s.subrange(i, j)[x] by {
        assert(b.subrange(at, at + s.len())[i + x] == s[i + x]);
    }
    assert(b.subrange(at + i, at + j) =~= s.subrange(i, j));
}

/// What a record laid down at `at` holds where `decode` reads it: its tag,
/// then its first path, then its second, its payload, or its flag.
pub(crate) proof fn lemma_record(b: Seq<u8>, at: int, op: FileOp)
    requires
        b.len() < 0x1_0000_0000_0000_0000int,
        holds_at(b, at, op),
    ensures
        at < b.len() && b[at] == tag(op),
        utf8(first(op)) is Some && field_at(b, at + 1) == utf8(first(op)),
        ({
            let a2 = at + 9 + utf8(first(op))->Some_0.len();
            let end = at + enc_op(op)->Some_0.len();
            &&& names_two(op) ==> utf8(second(op)) is Some && field_at(b, a2) == utf8(second(op))
                && end == a2 + 8 + utf8(second(op))->Some_0.len()
            &&& op is Write ==> field_at(b, a2) == Some(payload(op)) && end == a2 + 8 + payload(op).len()
            &&& op is SetExecutable ==> a2 < b.len() && b[a2] == flag(op) && end == a2 + 1
            &&& op is Remove ==> end == a2
        }),
{
    let s = enc_op(op)->Some_0;
    let t = utf8(first(op))->Some_0;
    let rest = s.subrange(9 + t.len() as int, s.len() as int);
    assert(s =~= seq![tag(op)] + field(t) + rest);
    lemma_record_head(b, at, tag(op), t, rest);
    lemma_piece(b, at, s, 9 + t.len() as int, s.len() as int);
    let a2 = at + 9 + t.len() as int;
    if names_two(op) {
        let u = utf8(second(op))->Some_0;
        assert(rest =~= field(u));
        lemma_field_at(b, a2, u);
    }
    if op is Write {
        assert(rest =~= field(payload(op)));
        lemma_field_at(b, a2, payload(op));
    }
    if op is SetExecutable {
        assert(rest =~= seq![flag(op)]);
        assert(b[a2] == b.subrange(a2, at + s.len())[0]);
    }
    if op is Remove {
        assert(rest =~= Seq::<u8>::empty());
    }
}

/// A record's tag and first field.
proof fn lemma_record_head(b: Seq<u8>, at: int, tag: u8, t: Seq<u8>, rest: Seq<u8>)
    requires
        0 <= at,
        b.len() < 0x1_0000_0000_0000_0000int,
        at + 9 + t.len() + rest.len() <= b.len(),
        b.subrange(at, at + 9 + t.len() + rest.len()) == seq![tag] + field(t) + rest,
    ensures
        b[at] == tag,
        field_at(b, at + 1) == Some(t),
{
    let s = seq![tag] + field(t) + rest;
    lemma_piece(b, at, s, 0, 1);
    assert(b[at] == b.subrange(at, at + 1)[0]);
    lemma_piece(b, at, s, 1, 9 + t.len() as int);
    assert(s.subrange(1, 9 + t.len() as int) =~= field(t));
    lemma_field_at(b, at + 1, t);
}

/// Bytes `b` hold `op`'s record at `at`.
pub(crate) open spec fn holds_at(b: Seq<u8>, at: int, op: FileOp) -> bool {
    &&& 0 <= at
    &&& enc_op(op) is Some
    &&& at + enc_op(op)->Some_0.len() <= b.len()
    &&& b.subrange(at, at + enc_op(op)->Some_0.len()) == enc_op(op)->Some_0
}

/// A journal's body holds op `k`'s record just after the records of the ops
/// before it.
pub(crate) proof fn lemma_in_body(magic: Seq<u8>, ops: Seq<FileOp>, k: int)
    requires
        magic.len() == 8,
        body(magic, ops) is Some,
        0 <= k < ops.len(),
    ensures
        enc_ops(ops.take(k)) is Some,
        holds_at(body(magic, ops)->Some_0, 16 + enc_ops(ops.take(k))->Some_0.len() as int, ops[k]),
        enc_ops(ops.take(k + 1)) == Some(enc_ops(ops.take(k))->Some_0 + enc_op(ops[k])->Some_0),
{
    lemma_enc_prefix(ops, k);
    lemma_enc_prefix(ops, k + 1);
    let e = enc_ops(ops)->Some_0;
    let b = body(magic, ops)->Some_0;
    let p = enc_ops(ops.take(k))->Some_0;
    let q = enc_ops(ops.take(k + 1))->Some_0;
    let rec = enc_op(ops[k])->Some_0;
    let at = 16 + p.len() as int;
    assert(b.subrange(at, at + rec.len()) =~= rec) by {
        assert forall|j: int| 0 <= j < rec.len() implies b.subrange(at, at + rec.len())[j] == rec[j] by {
            assert(b[at + j] == e[p.len() + j]);
            assert(e.take(q.len() as int)[p.len() + j] == q[p.len() + j]);
        }
    }
}

/// A reader `at` the end of the first `k` records has read `got`, the same
/// ops as the first `k`.
pub(crate) open spec fn read_so_far(written: Seq<FileOp>, at: int, k: int, got: Seq<FileOp>) -> bool {
    &&& 0 <= k <= written.len()
    &&& enc_ops(written.take(k)) is Some
    &&& at == 16 + enc_ops(written.take(k))->Some_0.len()
    &&& same_ops(got, written.take(k))
}

pub(crate) proof fn lemma_read_none(written: Seq<FileOp>)
    ensures
        read_so_far(written, 16, 0, Seq::empty()),
{
    assert(written.take(0) =~= Seq::<FileOp>::empty());
}

/// Where the reader stands, the next record is.
pub(crate) proof fn lemma_next_record(magic: Seq<u8>, written: Seq<FileOp>, at: int, k: int, got: Seq<FileOp>)
    requires
        magic.len() == 8,
        body(magic, written) is Some,
        read_so_far(written, at, k, got),
        k < written.len(),
    ensures
        holds_at(body(magic, written)->Some_0, at, written[k]),
{
    lemma_in_body(magic, written, k);
}

/// One more record read is one more op.
pub(crate) proof fn lemma_read_one(written: Seq<FileOp>, k: int, got: Seq<FileOp>, op: FileOp)
    requires
        0 <= k < written.len(),
        enc_ops(written) is Some,
        same_ops(got, written.take(k)),
        same_op(op, written[k]),
    ensures
        enc_ops(written.take(k + 1)) is Some,
        enc_ops(written.take(k + 1))->Some_0.len() == enc_ops(written.take(k))->Some_0.len() + enc_op(written[k])->Some_0.len(),
        same_ops(got.push(op), written.take(k + 1)),
{
    lemma_enc_prefix(written, k);
    let t = written.take(k + 1);
    assert(t =~= written.take(k).push(written[k]));
    assert forall|j: int| 0 <= j < got.push(op).len() implies #[trigger] same_op(got.push(op)[j], t[j]) by {
        if j < k {
            assert(same_op(got[j], written.take(k)[j]));
        }
    }
}

/// A reader that has read every record has read the set, and is at the end
/// of the body.
pub(crate) proof fn lemma_read_all(magic: Seq<u8>, written: Seq<FileOp>, at: int, got: Seq<FileOp>)
    requires
        magic.len() == 8,
        body(magic, written) is Some,
        read_so_far(written, at, written.len() as int, got),
    ensures
        same_ops(got, written),
        at == body(magic, written)->Some_0.len(),
{
    assert(written.take(written.len() as int) =~= written);
}

/// The records of a set's first `k` ops are where its records begin, and the
/// next op's record follows them.
pub(crate) proof fn lemma_enc_prefix(ops: Seq<FileOp>, k: int)
    requires
        0 <= k <= ops.len(),
        enc_ops(ops) is Some,
    ensures
        enc_ops(ops.take(k)) is Some,
        enc_ops(ops.take(k))->Some_0.len() <= enc_ops(ops)->Some_0.len(),
        enc_ops(ops)->Some_0.take(enc_ops(ops.take(k))->Some_0.len() as int) == enc_ops(ops.take(k))->Some_0,
        k < ops.len() ==> enc_op(ops[k]) is Some && enc_ops(ops.take(k + 1)) == Some(
            enc_ops(ops.take(k))->Some_0 + enc_op(ops[k])->Some_0,
        ),
    decreases ops.len(),
{
    if k == ops.len() {
        assert(ops.take(k) =~= ops);
        assert(enc_ops(ops)->Some_0.take(enc_ops(ops)->Some_0.len() as int) =~= enc_ops(ops)->Some_0);
    } else {
        let d = ops.drop_last();
        lemma_enc_prefix(d, k);
        assert(d.take(k) =~= ops.take(k));
        let a = enc_ops(d)->Some_0;
        let e = enc_ops(ops)->Some_0;
        let p = enc_ops(ops.take(k))->Some_0;
        assert(e == a + enc_op(ops.last())->Some_0);
        assert(e.take(p.len() as int) =~= a.take(p.len() as int));
        if k + 1 == ops.len() {
            assert(ops.take(k + 1) =~= ops);
            assert(d =~= ops.take(k));
        } else {
            lemma_enc_prefix(d, k);
            assert(d.take(k + 1) =~= ops.take(k + 1));
            assert(d[k] == ops[k]);
        }
    }
}

/// A set has no more ops than its records have bytes: each record is at
/// least its tag.
pub(crate) proof fn lemma_enc_len(ops: Seq<FileOp>)
    requires
        enc_ops(ops) is Some,
    ensures
        ops.len() <= enc_ops(ops)->Some_0.len(),
    decreases ops.len(),
{
    if ops.len() > 0 {
        lemma_enc_len(ops.drop_last());
    }
}

} // verus!
