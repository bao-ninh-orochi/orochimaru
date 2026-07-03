//! Test cases of the Zinc+ memory-consistency backend.
//!
//! Mirrors the structure of [`crate::nova::testcases`] /
//! [`crate::supernova::testcases`]: positive prove/verify round trips plus
//! negative (soundness) cases where an inconsistent trace or a tampered
//! proof must be rejected. An inconsistent trace produces a witness that
//! violates the UAIR constraints, which the honest Zinc+ prover already
//! rejects; each negative test therefore accepts *either* a proving failure
//! *or* a verification failure, and only ever passes when the inconsistency
//! is caught.

extern crate alloc;
extern crate std;
use alloc::vec::Vec;

use crate::{
    base::B256,
    machine::{AbstractTraceRecord, MemoryInstruction, TraceRecord},
    zincplus::{prove_memory_consistency, verify_memory_consistency, ZincMemoryError},
};

/// Shorthand for building one trace record.
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

/// A consistent read/write program over three addresses.
fn consistent_trace() -> Vec<TraceRecord<B256, B256, 32, 32>> {
    alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 1368),
        record(1, MemoryInstruction::Write, 0x20, 979),
        record(2, MemoryInstruction::Read, 0x0, 1368),
        record(3, MemoryInstruction::Write, 0x40, 42),
        record(4, MemoryInstruction::Read, 0x20, 979),
        record(5, MemoryInstruction::Write, 0x0, 500),
        record(6, MemoryInstruction::Read, 0x0, 500),
        record(7, MemoryInstruction::Read, 0x40, 42),
    ]
}

/// A trace must prove and verify.
fn assert_accepted(trace: &[TraceRecord<B256, B256, 32, 32>]) {
    let proof = prove_memory_consistency(trace).expect("the trace is consistent; proving succeeds");
    verify_memory_consistency(&proof).expect("the proof is honest; verification succeeds");
}

/// An inconsistent trace must be caught, either at proving time (the honest
/// prover notices the violated constraints) or at verification time.
fn assert_rejected(trace: &[TraceRecord<B256, B256, 32, 32>]) {
    if let Ok(proof) = prove_memory_consistency(trace) {
        assert!(
            verify_memory_consistency(&proof).is_err(),
            "an inconsistent trace slipped through both the prover and the verifier"
        );
    }
}

#[test]
fn test_consistent_trace_roundtrip() {
    assert_accepted(&consistent_trace());
}

#[test]
fn test_single_write_trace() {
    // Smallest possible valid trace: one write. Also exercises maximal
    // padding (1 real row inside an 8-row trace).
    assert_accepted(&[record(0, MemoryInstruction::Write, 0xffff, u64::MAX)]);
}

#[test]
fn test_wide_addresses_and_values() {
    // Addresses/values spanning the high 32-bit limbs, so the lexicographic
    // comparison must fall through several equal limbs before deciding.
    let a = B256::from([0x11u8; 32]);
    let mut b_bytes = [0x11u8; 32];
    b_bytes[31] = 0x12; // differs from `a` only in the least significant limb
    let b = B256::from(b_bytes);
    let big = B256::from([0xabu8; 32]);

    let trace = alloc::vec![
        TraceRecord::new(0, 0, MemoryInstruction::Write, a, big),
        TraceRecord::new(1, 0, MemoryInstruction::Write, b, B256::from(7)),
        TraceRecord::new(2, 0, MemoryInstruction::Read, a, big),
        TraceRecord::new(3, 0, MemoryInstruction::Read, b, B256::from(7)),
    ];
    assert_accepted(&trace);
}

#[test]
fn test_power_of_two_length_trace() {
    // A trace whose length is already a power of two still gets one extra
    // padding row (the protocol-exempt last row must never hold a record).
    let mut trace = consistent_trace();
    trace.truncate(8);
    assert_eq!(trace.len(), 8);
    assert_accepted(&trace);
}

#[test]
fn test_proof_serialization_roundtrip() {
    let proof = prove_memory_consistency(&consistent_trace()).expect("proving succeeds");
    let bytes = proof.to_bytes().expect("serialization succeeds");
    let restored =
        crate::zincplus::ZincMemoryProof::from_bytes(&bytes).expect("deserialization succeeds");
    assert_eq!(proof, restored);
    verify_memory_consistency(&restored).expect("the restored proof verifies");
}

#[test]
fn test_tampered_proof_rejected() {
    let proof = prove_memory_consistency(&consistent_trace()).expect("proving succeeds");
    let bytes = proof.to_bytes().expect("serialization succeeds");
    // Flip one byte somewhere inside the proof body (past the num_vars
    // header) and require rejection.
    let mut tampered = bytes.clone();
    let target = 4 + (tampered.len() - 4) / 2;
    tampered[target] ^= 0x01;
    match crate::zincplus::ZincMemoryProof::from_bytes(&tampered) {
        // Either the proof no longer parses...
        Err(_) => {}
        // ...or it parses and must fail verification.
        Ok(p) => assert!(verify_memory_consistency(&p).is_err()),
    }
}

#[test]
fn test_read_before_any_write_rejected() {
    // The very first access of the sorted trace is a read.
    assert_rejected(&[record(0, MemoryInstruction::Read, 0x0, 0)]);
}

#[test]
fn test_read_of_unwritten_address_rejected() {
    // Address 0x40 is never written; its first access is a read.
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 11),
        record(1, MemoryInstruction::Read, 0x40, 11),
    ];
    assert_rejected(&trace);
}

#[test]
fn test_stale_read_value_rejected() {
    // The read at time 2 returns the overwritten value.
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 100),
        record(1, MemoryInstruction::Write, 0x0, 200),
        record(2, MemoryInstruction::Read, 0x0, 100),
    ];
    assert_rejected(&trace);
}

#[test]
fn test_wrong_read_value_high_limb_rejected() {
    // The wrong value differs from the written one only in the *most
    // significant* limb, so the violation must be caught by the limb-wise
    // value constraints rather than by the low limb alone.
    let written = B256::from(1);
    let mut wrong_bytes = [0u8; 32];
    wrong_bytes[0] = 1; // 2^248
    wrong_bytes[31] = 1;
    let wrong = B256::from(wrong_bytes);
    let a = B256::from(0x80u64);
    let trace = alloc::vec![
        TraceRecord::new(0, 0, MemoryInstruction::Write, a, written),
        TraceRecord::new(1, 0, MemoryInstruction::Read, a, wrong),
    ];
    assert_rejected(&trace);
}

#[test]
fn test_empty_trace_rejected() {
    assert_eq!(
        prove_memory_consistency(&[]),
        Err(ZincMemoryError::EmptyTrace)
    );
}

#[test]
fn test_duplicated_access_rejected() {
    // Two records with identical (address, time_log).
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 1),
        record(0, MemoryInstruction::Read, 0x0, 1),
    ];
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::DuplicatedAccess { time_log: 0 })
    );
}

#[test]
fn test_time_log_overflow_rejected() {
    // The padding rows would need time_logs beyond u64::MAX.
    let trace = alloc::vec![record(u64::MAX, MemoryInstruction::Write, 0x0, 1)];
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::TimeLogOverflow)
    );
}

#[test]
fn test_truncated_proof_rejected() {
    let proof = prove_memory_consistency(&consistent_trace()).expect("proving succeeds");
    let bytes = proof.to_bytes().expect("serialization succeeds");
    assert!(crate::zincplus::ZincMemoryProof::from_bytes(&bytes[..bytes.len() / 2]).is_err());
    assert!(crate::zincplus::ZincMemoryProof::from_bytes(&[]).is_err());
}
