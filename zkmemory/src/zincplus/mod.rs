//! Memory-consistency argument backed by the [Zinc+](https://github.com/NethermindEth/zinc-plus)
//! proof system (feature `zinc`).
//!
//! This module is an *optional, alternative* proof-system backend for the
//! same statement family as the Halo2 circuits in [`crate::constraints`]:
//! that a memory trace sorted by `(address, time_log)` is consistent (every
//! read returns the last value written to that address). It follows the
//! multi-backend layout of [`crate::nova`] and [`crate::supernova`] and is
//! selectable next to Halo2 through [`crate::backend`].
//!
//! # Quick start
//!
//! ```ignore
//! use zkmemory::zincplus::{prove_memory_consistency, verify_memory_consistency};
//!
//! let trace = machine.trace(); // Vec<TraceRecord<B256, B256, 32, 32>>
//! let proof = prove_memory_consistency(&trace)?;
//! verify_memory_consistency(&proof)?;
//! let bytes = proof.to_bytes()?; // transferable, succinct proof
//! ```
//!
//! # Security status — read before use
//!
//! * Zinc+ is a transparent, plausibly post-quantum **SNARK without
//!   zero-knowledge**: proofs are succinct but do **not** hide the witness.
//! * Upstream Zinc+ is unaudited research software; this integration pins
//!   one reviewed git revision.
//! * Zinc+ currently lacks a permutation/lookup argument, so — unlike the
//!   Halo2 [`crate::constraints`] circuit — the link between the sorted
//!   trace and the original time-ordered trace is *not* enforced in-SNARK.
//!
//! The full discussion, including the migration plan for when upstream
//! gains zero-knowledge and permutation support, lives in
//! [`src/zincplus/README.md`](https://github.com/orochi-network/orochimaru/blob/main/zkmemory/src/zincplus/README.md).

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
