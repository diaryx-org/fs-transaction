//! Machine-checked proofs about fs-transaction's algorithms, in Verus.
//!
//! These files are not part of the crate. They model the algorithms in `src/`
//! and prove things about the models, so the library keeps its promise of no
//! dependencies. Each module names the source it transcribes and what it
//! leaves unmodeled. The code is kept close to the source so drift shows up in
//! review, but nothing mechanical ties the two together.
//!
//! ```text
//! verus verify/lib.rs --crate-type=lib --no-cheating
//! ```
//!
//! `--no-cheating` refuses `assume`, `admit`, and trusted bodies, so what
//! verifies is proved from the definitions alone.
//!
//! - [`path`]: `normalize` puts a path in normal form, is idempotent, and
//!   keeps its meaning. `escapes_root` is true exactly when the path is not
//!   relative, or its walk from the root climbs out at any point.
//! - [`change`]: a failed apply that unwinds cleanly gives back every path's
//!   bytes and link target, but not its permissions (counterexample).
//! - [`journal`]: replay from the op a crash interrupted is correct. Replay
//!   from the first op, which is what `recover` does, is not (five
//!   counterexamples).

#![allow(unused_imports)]

pub mod change;
pub mod journal;
pub mod path;
