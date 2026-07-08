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
//!
//! On top of the trace-level cases, the `tamper_*` tests attack individual
//! *witness columns* directly (through
//! [`super::prover::prove_from_uair_trace`]): they build an honest witness
//! and then corrupt exactly one cell of the permutation network, the
//! original trace, or the sorted trace, proving that each sub-statement of
//! the composed circuit — sorted consistency, original-trace time ordering
//! and the permutation link — is live.

extern crate alloc;
extern crate std;
use alloc::{format, vec::Vec};

use zinc_poly::univariate::binary::BinaryPoly;
use zinc_uair::UairTrace;

use crate::{
    base::B256,
    machine::{AbstractTraceRecord, MemoryInstruction, TraceRecord},
    zincplus::{
        prove_memory_consistency,
        prover::prove_from_uair_trace,
        types::{ZInt, D},
        uair::{
            build_uair_trace, build_uair_trace_any_start, NetLayout, PL_INSTR, PL_STACK_DEPTH,
            PL_VALUE,
        },
        verify_memory_consistency, ZincMemoryError,
    },
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
fn test_time_gaps_accepted() {
    // The original-trace contract requires strictly increasing time_logs
    // starting at 0 but allows gaps, exactly like the Halo2
    // `OriginalMemoryCircuit`.
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 7),
        record(5, MemoryInstruction::Read, 0x0, 7),
        record(1000, MemoryInstruction::Write, 0x20, 9),
        record((1 << 33) + 1, MemoryInstruction::Read, 0x20, 9),
    ];
    assert_accepted(&trace);
}

#[test]
fn test_nonzero_stack_depth_accepted() {
    // stack_depth rides the permutation network as payload; nonzero values
    // must round-trip.
    let trace = alloc::vec![
        TraceRecord::new(0, 3, MemoryInstruction::Write, B256::from(0), B256::from(1)),
        TraceRecord::new(1, 9, MemoryInstruction::Read, B256::from(0), B256::from(1)),
    ];
    assert_accepted(&trace);
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
    // padding row (the protocol-exempt last row must never hold a record),
    // pushing it to the next trace size (16 rows, 7 network layers).
    let trace = consistent_trace();
    assert_eq!(trace.len(), 8);
    let proof = prove_memory_consistency(&trace).expect("proving succeeds");
    assert_eq!(proof.num_vars(), 4);
    verify_memory_consistency(&proof).expect("verification succeeds");
}

#[test]
fn test_proof_serialization_roundtrip() {
    let trace = &consistent_trace()[..7];
    let proof = prove_memory_consistency(trace).expect("proving succeeds");
    let bytes = proof.to_bytes().expect("serialization succeeds");
    let restored =
        crate::zincplus::ZincMemoryProof::from_bytes(&bytes).expect("deserialization succeeds");
    assert_eq!(proof, restored);
    verify_memory_consistency(&restored).expect("the restored proof verifies");
}

#[test]
fn test_tampered_proof_rejected() {
    let proof = prove_memory_consistency(&consistent_trace()[..7]).expect("proving succeeds");
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
fn test_first_time_nonzero_rejected() {
    // The original trace must start at time_log 0 (Halo2
    // `OriginalMemoryCircuit` parity).
    assert_eq!(
        prove_memory_consistency(&[record(1, MemoryInstruction::Write, 0x0, 1)]),
        Err(ZincMemoryError::FirstTimeNonZero { time_log: 1 })
    );
}

#[test]
fn test_time_decreasing_rejected() {
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 1),
        record(2, MemoryInstruction::Write, 0x20, 2),
        record(1, MemoryInstruction::Write, 0x40, 3),
    ];
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::TimeNotIncreasing { time_log: 1 })
    );
}

#[test]
fn test_duplicated_access_rejected() {
    // Two records with the same time_log at the same address.
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
fn test_same_time_different_address_rejected() {
    // Halo2's original circuit demands *strictly* increasing time_logs, so
    // a shared time_log is rejected even across different addresses.
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 1),
        record(0, MemoryInstruction::Write, 0x20, 2),
    ];
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::DuplicatedAccess { time_log: 0 })
    );
}

#[test]
fn test_time_log_overflow_rejected() {
    // The padding rows would need time_logs beyond u64::MAX.
    let trace = alloc::vec![
        record(0, MemoryInstruction::Write, 0x0, 1),
        record(u64::MAX, MemoryInstruction::Write, 0x20, 2),
    ];
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::TimeLogOverflow)
    );
}

#[test]
fn test_truncated_proof_rejected() {
    let proof = prove_memory_consistency(&consistent_trace()[..7]).expect("proving succeeds");
    let bytes = proof.to_bytes().expect("serialization succeeds");
    assert!(crate::zincplus::ZincMemoryProof::from_bytes(&bytes[..bytes.len() / 2]).is_err());
    assert!(crate::zincplus::ZincMemoryProof::from_bytes(&[]).is_err());
}

// ---------------------------------------------------------------------------
// Witness-tampering soundness tests: corrupt exactly one witness cell of an
// otherwise honest witness and require rejection.
// ---------------------------------------------------------------------------

/// Build the honest witness for [`consistent_trace`] (7 records → 8 rows),
/// apply `mutate`, run the real prover and require rejection at proving or
/// verification time.
fn assert_tampered_witness_rejected(
    mutate: impl FnOnce(&mut UairTrace<'static, ZInt, ZInt, D, D>, &NetLayout),
) {
    let trace = consistent_trace();
    let (mut uair_trace, num_vars) =
        build_uair_trace(&trace[..7]).expect("the honest witness builds");
    let layout = NetLayout::new(num_vars);
    mutate(&mut uair_trace, &layout);
    match prove_from_uair_trace(&uair_trace, num_vars) {
        Err(ZincMemoryError::Prover(_)) => {}
        Err(other) => panic!("unexpected error kind: {other}"),
        Ok(proof) => assert!(
            verify_memory_consistency(&proof).is_err(),
            "a tampered witness slipped through both the prover and the verifier"
        ),
    }
}

/// Overwrite one binary-polynomial witness cell.
fn set_bp_cell(
    uair_trace: &mut UairTrace<'static, ZInt, ZInt, D, D>,
    col: usize,
    row: usize,
    value: u32,
) {
    uair_trace.binary_poly.to_mut()[col].evaluations[row] = BinaryPoly::from(value);
}

#[test]
fn test_tamper_original_trace_record_rejected() {
    // Corrupt one value limb of one *original-trace* record (the network
    // output side): the record multisets of the two orderings no longer
    // match, so the final network layer's swap equations must fail. This is
    // the permutation link at work — before it existed, the original-trace
    // columns were not committed at all.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        let col = layout.state_col(layout.original_state(), PL_VALUE + 7);
        set_bp_cell(uair_trace, col, 0, 0xdead_beef);
    });
}

#[test]
fn test_tamper_sorted_trace_record_rejected() {
    // Corrupt one stack_depth limb of one *sorted-trace* record (the
    // network input side). No sorted-consistency constraint reads
    // stack_depth — only the permutation network binds it — so rejection
    // proves the network covers the full record payload.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        let col = layout.state_col(0, PL_STACK_DEPTH + 1);
        set_bp_cell(uair_trace, col, 2, 7);
    });
}

#[test]
fn test_tamper_interior_network_state_rejected() {
    // Corrupt one cell of an interior routing state: the swap equations of
    // the two adjacent layers cannot both hold. Flip the instruction bit so
    // the tampered value is guaranteed to differ from the honest one.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        let col = layout.state_col(layout.num_layers / 2, PL_INSTR);
        let cell = &mut uair_trace.binary_poly.to_mut()[col].evaluations[1];
        let flipped = if *cell == BinaryPoly::from(1u32) {
            0u32
        } else {
            1u32
        };
        *cell = BinaryPoly::from(flipped);
    });
}

#[test]
fn test_tamper_switch_bit_rejected() {
    // Flip one switch bit without re-routing: the committed states no
    // longer satisfy that switch's swap equations.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        let col = layout.int_switch; // layer 0; row 0 is an upper wire
        let cell = &mut uair_trace.int.to_mut()[col].evaluations[0];
        *cell = 1 - *cell;
    });
}

#[test]
fn test_tamper_switch_bit_non_boolean_rejected() {
    // A non-boolean switch "mixes" the two records instead of swapping
    // them; the masked booleanity constraint must reject it.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        let col = layout.int_switch + 1; // layer 1; row 0 is an upper wire
        uair_trace.int.to_mut()[col].evaluations[0] = 2;
    });
}

#[test]
fn test_tamper_original_time_slack_rejected() {
    // Corrupt the original-trace time slack: the strict-increase relation
    // `o_hi·Δhi + o_lo·Δlo = 1 + r_O` must fail.
    assert_tampered_witness_rejected(|uair_trace, layout| {
        set_bp_cell(uair_trace, layout.bp_slack_original, 0, 41);
    });
}

#[test]
fn test_nonzero_start_time_rejected_in_circuit() {
    // A trace whose time_logs are shifted by +1 yields a witness where
    // *every* constraint holds except "the original trace starts at
    // time_log 0" — proving that constraint is enforced in-circuit and not
    // only by the input validation.
    let shifted: Vec<TraceRecord<B256, B256, 32, 32>> = consistent_trace()[..7]
        .iter()
        .map(|r| {
            TraceRecord::new(
                r.time_log() + 1,
                r.stack_depth(),
                r.instruction(),
                r.address(),
                r.value(),
            )
        })
        .collect();
    // The public API refuses it outright...
    assert_eq!(
        prove_memory_consistency(&shifted),
        Err(ZincMemoryError::FirstTimeNonZero { time_log: 1 })
    );
    // ...and so does the circuit itself when validation is bypassed.
    let (uair_trace, num_vars) =
        build_uair_trace_any_start(&shifted).expect("the shifted witness builds");
    match prove_from_uair_trace(&uair_trace, num_vars) {
        Err(ZincMemoryError::Prover(_)) => {}
        Err(other) => panic!("unexpected error kind: {other}"),
        Ok(proof) => assert!(
            verify_memory_consistency(&proof).is_err(),
            "a nonzero-start trace slipped through the circuit"
        ),
    }
}

#[test]
fn test_honest_witness_still_proves_after_helper_roundtrip() {
    // Guard for the tamper helpers themselves: an *unmodified* witness run
    // through the same internal entry point must still prove and verify, so
    // the tamper tests above cannot pass vacuously.
    let (uair_trace, num_vars) =
        build_uair_trace(&consistent_trace()[..7]).expect("the honest witness builds");
    let proof = prove_from_uair_trace(&uair_trace, num_vars).expect("honest witness proves");
    verify_memory_consistency(&proof).expect("honest proof verifies");
}

#[test]
fn test_trace_too_long_rejected() {
    // A trace beyond 2^MAX_NUM_VARS - 1 records must be rejected up front.
    // Build the length check input cheaply: the length test fires before
    // any witness work.
    let too_long = 1usize << crate::zincplus::uair::MAX_NUM_VARS;
    let trace: Vec<TraceRecord<B256, B256, 32, 32>> = (0..too_long as u64)
        .map(|t| record(t, MemoryInstruction::Write, 0x0, 1))
        .collect();
    assert_eq!(
        prove_memory_consistency(&trace),
        Err(ZincMemoryError::TraceTooLong)
    );
}

#[test]
fn test_error_display_is_informative() {
    // The user-facing error strings should carry the offending time_log.
    let message = format!("{}", ZincMemoryError::FirstTimeNonZero { time_log: 42 });
    assert!(message.contains("42"), "unhelpful message: {message}");
}
