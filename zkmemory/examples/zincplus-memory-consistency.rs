//! Example: proving memory consistency with the Zinc+ backend.
//!
//! Run with:
//!
//! ```sh
//! cargo run -p zkmemory --example zincplus-memory-consistency --features zinc --release
//! ```
//!
//! The example builds a small execution trace by hand (the same
//! `TraceRecord` stream an abstract machine produces via `machine.trace()`),
//! then:
//!
//! 1. proves memory consistency with the Zinc+ SNARK and verifies the proof,
//! 2. serializes the proof to bytes and verifies the restored proof,
//! 3. runs the same trace through the backend-agnostic seam
//!    ([`zkmemory::backend`]) with both the Halo2 and the Zinc+ backends,
//! 4. shows that an inconsistent trace (a stale read) is rejected.
//!
//! Note: Zinc+ proofs are succinct and transparent but **not
//! zero-knowledge** — see `zkmemory/src/zincplus/README.md`.

use zkmemory::backend::{Halo2Backend, MemoryConsistencyBackend, ZincPlusBackend};
use zkmemory::base::B256;
use zkmemory::machine::{AbstractTraceRecord, MemoryInstruction, TraceRecord};
use zkmemory::zincplus::{prove_memory_consistency, verify_memory_consistency, ZincMemoryProof};

/// Shorthand for building one trace record (stack depth is unused here).
fn record(
    time_log: u64,
    instruction: MemoryInstruction,
    address: u64,
    value: u64,
) -> TraceRecord<B256, B256, 32, 32> {
    TraceRecord::new(
        time_log,
        0,
        instruction,
        B256::from(address),
        B256::from(value),
    )
}

fn main() {
    // A small, consistent read/write program over three 32-byte-aligned
    // addresses: every read returns the last value written to its address.
    let trace = vec![
        record(0, MemoryInstruction::Write, 0x00, 1368),
        record(1, MemoryInstruction::Write, 0x20, 979),
        record(2, MemoryInstruction::Read, 0x00, 1368),
        record(3, MemoryInstruction::Write, 0x40, 42),
        record(4, MemoryInstruction::Read, 0x20, 979),
        record(5, MemoryInstruction::Write, 0x00, 500),
        record(6, MemoryInstruction::Read, 0x00, 500),
        record(7, MemoryInstruction::Read, 0x40, 42),
    ];

    // 1. Prove and verify with the Zinc+ backend directly.
    let proof = prove_memory_consistency(&trace).expect("the trace is consistent");
    verify_memory_consistency(&proof).expect("the proof verifies");
    println!(
        "Zinc+ proof accepted (padded trace: 2^{} rows).",
        proof.num_vars()
    );

    // 2. Serialize / restore / re-verify: the proof is a transferable byte
    //    string, unlike the MockProver-based Halo2 check below.
    let bytes = proof.to_bytes().expect("serialization succeeds");
    let restored = ZincMemoryProof::from_bytes(&bytes).expect("deserialization succeeds");
    verify_memory_consistency(&restored).expect("the restored proof verifies");
    println!(
        "Serialized proof: {} bytes; restored proof verifies.",
        bytes.len()
    );

    // 3. The backend-agnostic seam: the same trace, two proof systems.
    let halo2 = Halo2Backend { k: 10 };
    let attestation = halo2.prove(&trace).expect("Halo2 accepts the trace");
    halo2
        .verify(&attestation)
        .expect("Halo2 attestation verifies");
    println!("Halo2 backend (MockProver) accepted the same trace.");

    let zinc = ZincPlusBackend;
    let zinc_proof = zinc.prove(&trace).expect("Zinc+ accepts the trace");
    zinc.verify(&zinc_proof).expect("Zinc+ proof verifies");
    println!("Zinc+ backend accepted the same trace through the backend trait.");

    // 4. Soundness demo: the read at time 6 now returns the overwritten
    //    value 1368 instead of 500 — the backend must reject it.
    let mut inconsistent = trace.clone();
    inconsistent[6] = record(6, MemoryInstruction::Read, 0x00, 1368);
    let rejected = match zinc.prove(&inconsistent) {
        Err(_) => true, // the honest prover already refuses the witness
        Ok(bad_proof) => zinc.verify(&bad_proof).is_err(),
    };
    assert!(rejected, "an inconsistent trace must never be accepted");
    println!("Inconsistent trace (stale read) rejected, as expected.");
}
