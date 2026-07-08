//! Proof-system backend abstraction for the memory-consistency statement.
//!
//! zkMemory supports several proof systems for the same statement family:
//! the Halo2 (PLONK) circuits of [`crate::constraints`], the folding-scheme
//! provers of [`crate::nova`] / [`crate::supernova`], and — behind the
//! `zinc` feature — the Zinc+ SNARK of [`crate::zincplus`]. This module
//! provides the seam that lets callers pick a backend without changing how
//! they produce traces:
//!
//! ```ignore
//! use zkmemory::backend::{Halo2Backend, MemoryConsistencyBackend};
//!
//! let backend = Halo2Backend { k: 10 };
//! let proof = backend.prove(&machine.trace())?;
//! backend.verify(&proof)?;
//! ```
//!
//! Every backend consumes the *time-ordered* execution trace exactly as
//! returned by [`crate::machine::AbstractMachine::trace`] (`time_log`s
//! starting at zero and strictly increasing) and internally derives
//! whatever sorted/converted representation it needs. Both backends prove
//! the same composed statement — original-trace time consistency,
//! sorted-trace memory consistency and the permutation link between the two
//! orderings — but differ in the artifacts they produce and in their trust
//! profile:
//!
//! | backend | proof artifact | trusted setup | zero-knowledge | status |
//! |---------|----------------|---------------|----------------|--------|
//! | [`Halo2Backend`] | none (constraint-system check via `MockProver`) | n/a | n/a | reference semantics |
//! | [`ZincPlusBackend`] | succinct transparent SNARK ([`crate::zincplus::ZincMemoryProof`]) | none | **no** | optional, feature `zinc` |
//!
//! The Halo2 backend runs the full consistency circuit under
//! `halo2_proofs::dev::MockProver` — the same check the crate's own tests
//! and examples perform — because the crate does not yet wire a real Halo2
//! prover for the composed circuit (only the permutation sub-circuit has an
//! IPA prover, see [`crate::constraints::permutation_circuit`]). Its
//! "proof" therefore only attests local checking, not transferable
//! succinctness; producing a real Halo2 proof artifact is tracked as
//! follow-up work in `src/zincplus/README.md`.

extern crate alloc;
use alloc::{format, string::String, vec, vec::Vec};
use core::cmp::Ordering;
use core::marker::PhantomData;

use halo2_proofs::dev::MockProver;
use halo2curves::pasta::Fp;

use crate::{
    base::B256,
    constraints::consistency_check_circuit::MemoryConsistencyCircuit,
    machine::{AbstractTraceRecord, TraceRecord},
};

/// A pluggable proof-system backend for the memory-consistency statement:
/// "the given execution trace touches memory consistently" (every read
/// returns the last value written to the same address).
pub trait MemoryConsistencyBackend {
    /// The proof artifact produced by [`Self::prove`].
    type Proof;
    /// The error type of this backend.
    type Error;

    /// Prove that the *time-ordered* execution trace (as returned by
    /// [`crate::machine::AbstractMachine::trace`]) is memory-consistent.
    ///
    /// # Errors
    ///
    /// Fails when the trace is structurally invalid or inconsistent; the
    /// exact error surface is backend-specific.
    fn prove(&self, trace: &[TraceRecord<B256, B256, 32, 32>]) -> Result<Self::Proof, Self::Error>;

    /// Verify a proof produced by [`Self::prove`].
    ///
    /// # Errors
    ///
    /// Fails when the proof does not attest a consistent trace.
    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error>;
}

/// Sort a trace by `(address, time_log)` — the order the sorted-trace
/// consistency circuits expect.
fn sort_trace_by_address_time(
    trace: &[TraceRecord<B256, B256, 32, 32>],
) -> Vec<TraceRecord<B256, B256, 32, 32>> {
    let mut sorted = trace.to_vec();
    sorted.sort_by(|a, b| match a.address().cmp(&b.address()) {
        Ordering::Equal => a.time_log().cmp(&b.time_log()),
        ordering => ordering,
    });
    sorted
}

/// The Halo2 (PLONK) backend: checks the composed permutation +
/// original-memory + sorted-memory circuit of [`crate::constraints`] with
/// `MockProver`. See the module documentation for its limitations.
#[derive(Clone, Debug)]
pub struct Halo2Backend {
    /// Circuit size parameter: the circuit uses `2^k` rows. `k = 10`
    /// matches the crate's examples and accommodates the fixed lookup
    /// tables; it must satisfy `2^k > trace length + blinding rows`.
    pub k: u32,
}

/// The artifact of a successful [`Halo2Backend::prove`] call.
///
/// `MockProver` checks constraint satisfaction in memory and produces no
/// transferable proof object, so this artifact simply carries the checked
/// trace; [`Halo2Backend::verify`] re-runs the check.
#[derive(Clone, Debug)]
pub struct Halo2Attestation {
    /// The time-ordered trace whose consistency was checked.
    trace: Vec<TraceRecord<B256, B256, 32, 32>>,
    /// The circuit size parameter used for the check.
    k: u32,
}

impl Halo2Backend {
    /// Run the composed consistency circuit under `MockProver`.
    fn check(&self, trace: &[TraceRecord<B256, B256, 32, 32>]) -> Result<(), String> {
        let circuit = MemoryConsistencyCircuit::<Fp> {
            input: trace.to_vec(),
            shuffle: sort_trace_by_address_time(trace),
            marker: PhantomData,
        };
        let prover =
            MockProver::run(self.k, &circuit, vec![]).map_err(|e| format!("synthesis: {e}"))?;
        prover
            .verify()
            .map_err(|failures| format!("constraint check: {failures:?}"))
    }
}

impl MemoryConsistencyBackend for Halo2Backend {
    type Proof = Halo2Attestation;
    type Error = String;

    fn prove(&self, trace: &[TraceRecord<B256, B256, 32, 32>]) -> Result<Self::Proof, Self::Error> {
        self.check(trace)?;
        Ok(Halo2Attestation {
            trace: trace.to_vec(),
            k: self.k,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        Halo2Backend { k: proof.k }.check(&proof.trace)
    }
}

/// The Zinc+ backend: produces a succinct, transparent SNARK for the full
/// composed memory-consistency statement (original-trace time consistency,
/// sorted-trace consistency, and their permutation link via a deterministic
/// Beneš network). **Not zero-knowledge** — see [`crate::zincplus`] for the
/// security discussion.
#[cfg(feature = "zinc")]
#[derive(Clone, Debug, Default)]
pub struct ZincPlusBackend;

#[cfg(feature = "zinc")]
impl MemoryConsistencyBackend for ZincPlusBackend {
    type Proof = crate::zincplus::ZincMemoryProof;
    type Error = crate::zincplus::ZincMemoryError;

    fn prove(&self, trace: &[TraceRecord<B256, B256, 32, 32>]) -> Result<Self::Proof, Self::Error> {
        crate::zincplus::prove_memory_consistency(trace)
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        crate::zincplus::verify_memory_consistency(proof)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::machine::MemoryInstruction;

    fn sample_trace() -> Vec<TraceRecord<B256, B256, 32, 32>> {
        alloc::vec![
            TraceRecord::new(0, 0, MemoryInstruction::Write, B256::from(0), B256::from(7)),
            TraceRecord::new(
                1,
                0,
                MemoryInstruction::Write,
                B256::from(32),
                B256::from(8)
            ),
            TraceRecord::new(2, 0, MemoryInstruction::Read, B256::from(0), B256::from(7)),
            TraceRecord::new(3, 0, MemoryInstruction::Read, B256::from(32), B256::from(8)),
        ]
    }

    #[test]
    fn test_halo2_backend_accepts_consistent_trace() {
        let backend = Halo2Backend { k: 10 };
        let proof = backend
            .prove(&sample_trace())
            .expect("consistent trace proves");
        backend.verify(&proof).expect("attestation verifies");
    }

    #[test]
    fn test_halo2_backend_rejects_inconsistent_trace() {
        let mut trace = sample_trace();
        // The read at time 2 returns a value that was never written.
        trace[2] = TraceRecord::new(2, 0, MemoryInstruction::Read, B256::from(0), B256::from(9));
        let backend = Halo2Backend { k: 10 };
        assert!(backend.prove(&trace).is_err());
    }

    #[cfg(feature = "zinc")]
    #[test]
    fn test_zincplus_backend_accepts_consistent_trace() {
        let backend = ZincPlusBackend;
        let proof = backend
            .prove(&sample_trace())
            .expect("consistent trace proves");
        backend.verify(&proof).expect("proof verifies");
    }

    #[cfg(feature = "zinc")]
    #[test]
    fn test_zincplus_backend_rejects_inconsistent_trace() {
        let mut trace = sample_trace();
        trace[2] = TraceRecord::new(2, 0, MemoryInstruction::Read, B256::from(0), B256::from(9));
        let backend = ZincPlusBackend;
        if let Ok(proof) = backend.prove(&trace) {
            assert!(backend.verify(&proof).is_err());
        }
    }
}
