//! Prover / verifier entry points of the Zinc+ memory-consistency backend.
//!
//! [`prove_memory_consistency`] takes the execution trace produced by an
//! abstract machine ([`crate::machine::AbstractMachine::trace`]), sorts it by
//! `(address, time_log)`, builds the UAIR witness and runs the Zinc+ prover.
//! [`verify_memory_consistency`] re-derives the (transparent) commitment
//! parameters and the public columns, then runs the Zinc+ verifier.
//!
//! Zinc+ has no trusted setup and the prover is deterministic: all
//! challenges, including the random prime-field modulus, are derived from
//! the Blake3 Fiat-Shamir transcript after the witness commitments and the
//! public columns are absorbed.

extern crate alloc;
use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};
use core::fmt;

use zinc_protocol::{Proof, ZincPlusPiop};
use zinc_uair::{ideal::DegreeOneIdeal, ideal_collector::IdealOrZero, Uair, UairTrace};
use zinc_utils::CHECKED;
use zip_plus::pcs_transcript::PcsProverTranscript;

use crate::{base::B256, machine::TraceRecord};

use super::{
    types::{setup_params, MemoryZincTypes, ZInt, D, F, QUARTER_D},
    uair::{build_uair_trace, is_first_column, MemoryConsistencyUair, MAX_NUM_VARS, MIN_NUM_VARS},
};

/// The fully-instantiated Zinc+ PIOP driving this backend.
type MemoryPiop = ZincPlusPiop<MemoryZincTypes, MemoryConsistencyUair, F, D, QUARTER_D>;

/// Errors of the Zinc+ memory-consistency backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZincMemoryError {
    /// The execution trace is empty; there is nothing to prove.
    EmptyTrace,
    /// The execution trace does not fit in `2^MAX_NUM_VARS - 1` rows.
    TraceTooLong,
    /// Two trace records share the same `(address, time_log)` pair. Traces
    /// produced by the abstract machine have globally unique `time_log`s.
    DuplicatedAccess {
        /// The duplicated `time_log`.
        time_log: u64,
    },
    /// Padding the trace to a power of two would overflow the `u64` time
    /// domain.
    TimeLogOverflow,
    /// Internal invariant violation: the sorted trace was not strictly
    /// increasing. This indicates a bug rather than a bad input.
    UnsortedTrace,
    /// The serialized proof is malformed.
    MalformedProof(String),
    /// The Zinc+ prover rejected the witness (an inconsistent trace fails
    /// here, at proving time).
    Prover(String),
    /// The Zinc+ verifier rejected the proof.
    Verifier(String),
}

impl fmt::Display for ZincMemoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTrace => write!(f, "the execution trace is empty"),
            Self::TraceTooLong => {
                write!(
                    f,
                    "the execution trace exceeds 2^{MAX_NUM_VARS} - 1 records"
                )
            }
            Self::DuplicatedAccess { time_log } => write!(
                f,
                "two trace records share the same (address, time_log = {time_log})"
            ),
            Self::TimeLogOverflow => {
                write!(f, "padding the trace would overflow the u64 time domain")
            }
            Self::UnsortedTrace => write!(f, "internal error: sorted trace is not increasing"),
            Self::MalformedProof(msg) => write!(f, "malformed proof: {msg}"),
            Self::Prover(msg) => write!(f, "Zinc+ prover error: {msg}"),
            Self::Verifier(msg) => write!(f, "Zinc+ verification failed: {msg}"),
        }
    }
}

/// A Zinc+ memory-consistency proof.
///
/// The proof attests that the prover knows a trace of `2^num_vars - 1` rows
/// (the actual records followed by benign padding rows) that is sorted by
/// `(address, time_log)` and memory-consistent — see
/// [`super::uair::MemoryConsistencyUair`] for the exact relation and
/// `src/zincplus/README.md` for what this does and does not imply.
///
/// The proof is *succinct* and *transparent* but — with the current
/// upstream Zinc+ — **not zero-knowledge**: assume the trace can be
/// reconstructed from the proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZincMemoryProof {
    /// The inner Zinc+ proof object.
    proof: Proof<F>,
    /// `log2` of the padded trace length the proof was produced for.
    num_vars: usize,
}

impl ZincMemoryProof {
    /// `log2` of the padded trace length this proof covers.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Serialize the proof to bytes: a little-endian `u32` `num_vars` prefix
    /// followed by the Zinc+ proof transcript.
    ///
    /// # Errors
    ///
    /// Returns [`ZincMemoryError::MalformedProof`] if the inner proof fails
    /// to serialize.
    pub fn to_bytes(&self) -> Result<Vec<u8>, ZincMemoryError> {
        let mut transcript = PcsProverTranscript::new_from_commitments(core::iter::empty());
        transcript
            .write(&self.proof)
            .map_err(|e| ZincMemoryError::MalformedProof(e.to_string()))?;
        let num_vars = u32::try_from(self.num_vars)
            .map_err(|_| ZincMemoryError::MalformedProof("num_vars overflow".to_string()))?;
        let mut bytes = num_vars.to_le_bytes().to_vec();
        bytes.extend_from_slice(transcript.stream.get_ref());
        Ok(bytes)
    }

    /// Deserialize a proof produced by [`Self::to_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`ZincMemoryError::MalformedProof`] if the buffer is truncated,
    /// declares an out-of-range `num_vars`, or the transcript fails to parse.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ZincMemoryError> {
        let (header, body) = bytes
            .split_first_chunk::<4>()
            .ok_or_else(|| ZincMemoryError::MalformedProof("buffer too short".to_string()))?;
        let num_vars = u32::from_le_bytes(*header) as usize;
        if !(MIN_NUM_VARS..=MAX_NUM_VARS).contains(&num_vars) {
            return Err(ZincMemoryError::MalformedProof(format!(
                "num_vars {num_vars} outside [{MIN_NUM_VARS}, {MAX_NUM_VARS}]"
            )));
        }
        let mut transcript = PcsProverTranscript::new_from_commitments(core::iter::empty());
        transcript.stream.get_mut().extend_from_slice(body);
        let mut transcript = transcript.into_verification_transcript();
        let proof: Proof<F> = transcript
            .read()
            .map_err(|e| ZincMemoryError::MalformedProof(e.to_string()))?;
        Ok(Self { proof, num_vars })
    }
}

/// Prove that an execution trace is memory-consistent with the Zinc+ proof
/// system.
///
/// The input is the *time-ordered* trace exactly as returned by
/// [`crate::machine::AbstractMachine::trace`]; sorting by
/// `(address, time_log)`, limb decomposition and padding happen internally.
/// An *inconsistent* trace (e.g. a read returning a stale value) makes the
/// witness violate the UAIR constraints and surfaces as
/// [`ZincMemoryError::Prover`].
///
/// # Errors
///
/// See [`ZincMemoryError`]; structurally invalid traces (empty, duplicated
/// `(address, time_log)`, too long) are rejected before proving starts.
pub fn prove_memory_consistency(
    trace: &[TraceRecord<B256, B256, 32, 32>],
) -> Result<ZincMemoryProof, ZincMemoryError> {
    let (uair_trace, num_vars) = build_uair_trace(trace)?;
    let params = setup_params(num_vars);
    let proof = MemoryPiop::prove::<false, CHECKED>(
        &params,
        &uair_trace,
        num_vars,
        zinc_protocol::project_scalar_fn,
    )
    .map_err(|e| ZincMemoryError::Prover(e.to_string()))?;
    Ok(ZincMemoryProof { proof, num_vars })
}

/// Verify a Zinc+ memory-consistency proof.
///
/// The verifier re-derives the transparent commitment parameters and the
/// public `is_first` column (`[1, 0, 0, ...]`) itself, so a proof is
/// accepted only for the exact public inputs this backend defines.
///
/// # Errors
///
/// Returns [`ZincMemoryError::Verifier`] when the proof does not verify.
pub fn verify_memory_consistency(proof: &ZincMemoryProof) -> Result<(), ZincMemoryError> {
    let num_vars = proof.num_vars;
    if !(MIN_NUM_VARS..=MAX_NUM_VARS).contains(&num_vars) {
        return Err(ZincMemoryError::MalformedProof(format!(
            "num_vars {num_vars} outside [{MIN_NUM_VARS}, {MAX_NUM_VARS}]"
        )));
    }
    let params = setup_params(num_vars);
    let public_trace: UairTrace<'static, ZInt, ZInt, D, D> = UairTrace {
        binary_poly: Vec::new().into(),
        arbitrary_poly: Vec::new().into(),
        int: alloc::vec![is_first_column(1usize << num_vars)].into(),
    };
    MemoryPiop::verify::<_, CHECKED>(
        &params,
        proof.proof.clone(),
        &public_trace,
        num_vars,
        zinc_protocol::project_scalar_fn,
        project_ideal,
        project_fq_ideal,
    )
    .map_err(|e| ZincMemoryError::Verifier(e.to_string()))
}

/// Project the UAIR's `Z[X]` ideals into the sampled prime field.
fn project_ideal(
    ideal: &IdealOrZero<<MemoryConsistencyUair as Uair>::Ideal>,
    field_cfg: &<F as crypto_primitives::HasPrimeFieldConfig>::Config,
) -> IdealOrZero<DegreeOneIdeal<F>> {
    ideal.map(|i| DegreeOneIdeal::from_with_cfg(i, field_cfg))
}

/// The memory-consistency UAIR declares no `F_q[X]` prime families, so this
/// projection can never be invoked at runtime.
fn project_fq_ideal(
    _ideal: &IdealOrZero<<MemoryConsistencyUair as Uair>::FqIdeal>,
    _field_cfg: &<F as crypto_primitives::HasPrimeFieldConfig>::Config,
) -> IdealOrZero<DegreeOneIdeal<F>> {
    unreachable!("the memory-consistency UAIR has no F_q[X] constraints")
}
