//! Memory-consistency argument backed by the [Zinc+](https://github.com/NethermindEth/zinc-plus)
//! proof system (feature `zinc`).
//!
//! This module is an *optional, alternative* proof-system backend for the
//! same statement as the composed Halo2 circuit in [`crate::constraints`]:
//!
//! 1. the *original* (time-ordered) trace starts at `time_log = 0` and its
//!    `time_log`s strictly increase,
//! 2. the trace sorted by `(address, time_log)` is memory-consistent (every
//!    read returns the last value written to that address), and
//! 3. the sorted trace is a permutation of the original trace.
//!
//! Zinc+ has no permutation/lookup argument, so sub-statement 3 is enforced
//! **deterministically** with a Beneš switching network inside the AIR (see
//! [`uair`] and [`benes`]) instead of a randomized shuffle argument. The
//! module follows the multi-backend layout of [`crate::nova`] and
//! [`crate::supernova`] and is selectable next to Halo2 through
//! [`crate::backend`].
//!
//! # Quick start
//!
//! ```ignore
//! use zkmemory::zincplus::{prove_memory_consistency, verify_memory_consistency};
//!
//! let trace = machine.trace(); // Vec<TraceRecord<B256, B256, 32, 32>>, time-ordered
//! let proof = prove_memory_consistency(&trace)?;
//! verify_memory_consistency(&proof)?;
//! let bytes = proof.to_bytes()?; // transferable, succinct proof
//! ```
//!
//! The input trace must be in execution order with `time_log`s starting at
//! `0` and strictly increasing — the same contract the Halo2
//! `OriginalMemoryCircuit` enforces.
//!
//! # Security status — read before use
//!
//! * Zinc+ is a transparent, plausibly post-quantum **SNARK without
//!   zero-knowledge**: proofs are succinct but do **not** hide the witness.
//! * Upstream Zinc+ is unaudited research software; this integration pins
//!   one reviewed git revision.
//!
//! The full discussion lives in
//! [`src/zincplus/README.md`](https://github.com/orochi-network/orochimaru/blob/main/zkmemory/src/zincplus/README.md).

/// Prover-side Beneš-network routing for the permutation argument.
pub(crate) mod benes;
/// Prover / verifier entry points, proof and error types.
pub(crate) mod prover;
/// Concrete Zinc+ protocol type parameters (field, codes, widths).
pub(crate) mod types;
/// The memory-consistency UAIR and its witness builder.
pub(crate) mod uair;

#[cfg(test)]
mod testcases;

pub use prover::{
    prove_memory_consistency, verify_memory_consistency, ZincMemoryError, ZincMemoryProof,
};
pub use uair::MemoryConsistencyUair;
