//! Machine-checked proofs about fs-transaction's algorithms, in Verus.
//!
//! These model `src/change.rs` and `src/journal.rs` as they were *before*
//! the rollback moved files aside and the apply refused unreplayable sets —
//! the counterexamples below are the bugs those changes fix. They are
//! being replaced by proofs in the source itself.
//!
//! They are models of the code, not the
//! code itself, and nothing mechanical ties them to it. They exist until that
//! code is restructured so its decisions can be verified where they are
//! written, as `src/path.rs` already is. Each module names the source it
//! transcribes and what it leaves unmodeled.
//!
//! ```text
//! verus verify/lib.rs --crate-type=lib --no-cheating
//! ```
//!
//! `--no-cheating` refuses `assume`, `admit`, and trusted bodies, so what
//! verifies is proved from the definitions alone.
//!
//! - [`change`]: a failed apply that unwinds cleanly gives back every path's
//!   bytes and link target, but not its permissions (counterexample).
//! - [`journal`]: replay from the op a crash interrupted is correct. Replay
//!   from the first op, which is what `recover` does, is not (five
//!   counterexamples).

#![allow(unused_imports)]

pub mod change;
pub mod journal;
