//! Concrete Zinc+ protocol type parameters used by the zkMemory backend.
//!
//! Zinc+ is heavily generic: the protocol is parameterized over the host
//! integer ring, the challenge/evaluation types, the randomly-sampled field
//! modulus and the linear codes used by the Zip+ polynomial commitment
//! scheme. This module pins one concrete, working instantiation, mirroring
//! the reference instantiation exercised by the upstream `zinc-protocol`
//! end-to-end tests:
//!
//! * host integer ring: [`i64`] (all integer cells used by the memory
//!   consistency UAIR are tiny: `{-1, 0, 1}`),
//! * field modulus: a randomly sampled prime of `3 x 64 = 192` bits
//!   ([`MontyField`] / [`Uint`] with [`FIELD_LIMBS`] limbs),
//! * linear code: IPRS (interleaved permuted repetition + systematic NTT
//!   code over `F_65537`) with repetition factor [`REP_FACTOR`],
//! * binary trace columns hold [`BinaryPoly`]`<32>` cells and are folded
//!   4x before commitment ([`FoldBinaryTrace4x`]).
//!
//! # Security parameters
//!
//! [`REP_FACTOR`] and `NUM_COLUMN_OPENINGS` are taken verbatim from the
//! upstream test/bench configuration. They are **research defaults**
//! published by the Zinc+ authors, not audited production parameters. See
//! `src/zincplus/README.md` for the full security discussion.

use crypto_bigint::U64;
use crypto_primitives::{
    crypto_bigint_int::Int, crypto_bigint_monty::MontyField, crypto_bigint_uint::Uint,
};
use zinc_poly::univariate::{
    binary::{BinaryPoly, BinaryPolyInnerProduct},
    dense::{DensePolyInnerProduct, DensePolynomial},
};
use zinc_primality::MillerRabin;
use zinc_protocol::{
    fold::{FoldBinaryTrace4x, FoldTrace},
    ZincTypes,
};
use zinc_utils::{
    inner_product::{MBSInnerProduct, ScalarProduct},
    CHECKED,
};
use zip_plus::{
    code::iprs::{IprsCode, PnttConfigF65537},
    pcs::structs::{ZipPlus, ZipPlusParams, ZipTypes},
};

/// Number of limbs of the host-platform word inside `crypto-bigint`'s [`U64`].
const INT_LIMBS: usize = U64::LIMBS;

/// Number of limbs of the randomly sampled field modulus (192 bits on
/// 64-bit platforms). The soundness of every ideal-membership check
/// performed by the verifier relies on this modulus being drawn from a
/// large enough space; see the module documentation.
pub(crate) const FIELD_LIMBS: usize = U64::LIMBS * 3;

/// Cell width (`DEGREE_PLUS_ONE`): every polynomial trace cell has strictly
/// fewer than [`D`] coefficients. This matches the 32-bit limb decomposition
/// used by the memory-consistency UAIR.
pub(crate) const D: usize = 32;
/// Intermediate width used by the 4x binary trace folding.
const HALF_D: usize = D / 2;
/// Folded cell width (`FOLDED_DEGREE_PLUS_ONE`) after the 4x binary fold.
pub(crate) const QUARTER_D: usize = D / 4;

/// Width (in limbs) of the wide combination ring used by Zip+ when taking
/// random linear combinations of committed rows.
const M: usize = INT_LIMBS * 8;

/// Repetition factor of the IPRS linear code (upstream research default).
const REP_FACTOR: usize = 8;

/// The prime field the Zinc+ PIOP projects all constraints into. The modulus
/// is sampled at proving time from the Fiat-Shamir transcript.
pub(crate) type F = MontyField<FIELD_LIMBS>;
/// Integer representation of the field modulus.
pub(crate) type Fmod = Uint<FIELD_LIMBS>;
/// Host integer ring for trace cells.
pub(crate) type ZInt = i64;

/// Zip+ type bundle for the *binary polynomial* trace columns.
#[derive(Debug, Clone)]
pub(crate) struct MemoryBinZipTypes;

impl ZipTypes for MemoryBinZipTypes {
    const NUM_COLUMN_OPENINGS: usize = 100;
    type Eval = BinaryPoly<QUARTER_D>;
    type Cw = DensePolynomial<ZInt, QUARTER_D>;
    type Fmod = Fmod;
    type PrimeTest = MillerRabin;
    type Chal = i128;
    type Pt = i128;
    type CombR = Int<M>;
    type Comb = DensePolynomial<Self::CombR, QUARTER_D>;
    type EvalDotChal = BinaryPolyInnerProduct<Self::Chal, QUARTER_D>;
    type CombDotChal =
        DensePolyInnerProduct<Self::CombR, Self::Chal, Self::CombR, MBSInnerProduct, QUARTER_D>;
    type ArrCombRDotChal = MBSInnerProduct;
}

/// Zip+ type bundle for the *arbitrary polynomial* trace columns.
///
/// The memory-consistency UAIR declares no arbitrary-polynomial columns,
/// but the Zinc+ prover/verifier still require the type bundle and (empty)
/// commitment parameters for this column kind.
#[derive(Debug, Clone)]
pub(crate) struct MemoryArbZipTypes;

impl ZipTypes for MemoryArbZipTypes {
    const NUM_COLUMN_OPENINGS: usize = 100;
    type Eval = DensePolynomial<ZInt, D>;
    type Cw = DensePolynomial<ZInt, D>;
    type Fmod = Fmod;
    type PrimeTest = MillerRabin;
    type Chal = i128;
    type Pt = i128;
    type CombR = Int<M>;
    type Comb = DensePolynomial<Self::CombR, D>;
    type EvalDotChal = DensePolyInnerProduct<ZInt, Self::Chal, Self::CombR, MBSInnerProduct, D>;
    type CombDotChal =
        DensePolyInnerProduct<Self::CombR, Self::Chal, Self::CombR, MBSInnerProduct, D>;
    type ArrCombRDotChal = MBSInnerProduct;
}

/// Zip+ type bundle for the *integer* trace columns.
#[derive(Debug, Clone)]
pub(crate) struct MemoryIntZipTypes;

impl ZipTypes for MemoryIntZipTypes {
    const NUM_COLUMN_OPENINGS: usize = 100;
    type Eval = ZInt;
    type Cw = i128;
    type Fmod = Fmod;
    type PrimeTest = MillerRabin;
    type Chal = i128;
    type Pt = i128;
    type CombR = Int<M>;
    type Comb = Self::CombR;
    type EvalDotChal = ScalarProduct;
    type CombDotChal = ScalarProduct;
    type ArrCombRDotChal = MBSInnerProduct;
}

/// The IPRS linear code type shared by all three column kinds.
type MemoryLc<Zt> = IprsCode<Zt, PnttConfigF65537, REP_FACTOR, CHECKED>;

/// The complete Zinc+ type instantiation used by the zkMemory backend.
#[derive(Debug, Clone)]
pub(crate) struct MemoryZincTypes;

impl ZincTypes<D, QUARTER_D> for MemoryZincTypes {
    type Int = ZInt;
    type Chal = i128;
    type Pt = i128;
    type CombR = Int<M>;
    type Fmod = Fmod;
    type PrimeTest = MillerRabin;

    type BinaryZt = MemoryBinZipTypes;
    type ArbitraryZt = MemoryArbZipTypes;
    type IntZt = MemoryIntZipTypes;

    type BinaryFold = FoldBinaryTrace4x<D, HALF_D, QUARTER_D>;

    type BinaryLc = MemoryLc<Self::BinaryZt>;
    type ArbitraryLc = MemoryLc<Self::ArbitraryZt>;
    type IntLc = MemoryLc<Self::IntZt>;
}

/// Zip+ public parameters for the three column kinds (binary, arbitrary,
/// integer). Zinc+ is *transparent*: these parameters are deterministic in
/// `num_vars`, so the prover and the verifier derive identical parameters
/// independently — there is no trusted setup.
pub(crate) type MemoryPcsParams = (
    ZipPlusParams<MemoryBinZipTypes, MemoryLc<MemoryBinZipTypes>>,
    ZipPlusParams<MemoryArbZipTypes, MemoryLc<MemoryArbZipTypes>>,
    ZipPlusParams<MemoryIntZipTypes, MemoryLc<MemoryIntZipTypes>>,
);

/// Build the IPRS code for MLE polynomials with `2^num_vars` evaluations.
fn make_iprs<Zt: ZipTypes>(num_vars: usize) -> MemoryLc<Zt> {
    let poly_size = 1usize << num_vars;
    IprsCode::new_with_optimal_depth(poly_size)
        .expect("IPRS code construction for a power-of-two size never fails")
}

/// Deterministically derive the Zip+ commitment parameters for a trace of
/// `2^num_vars` rows. Binary columns are folded 4x before commitment, so
/// their parameters cover `2^(num_vars + 2)` evaluations.
pub(crate) fn setup_params(num_vars: usize) -> MemoryPcsParams {
    let folding_factor = <MemoryZincTypes as ZincTypes<D, QUARTER_D>>::BinaryFold::FOLDING_FACTOR;
    let folded_num_vars = num_vars
        + usize::try_from(folding_factor.ilog2()).expect("log2 of a small constant fits in usize");

    let poly_size = 1usize << num_vars;
    let folded_poly_size = 1usize << folded_num_vars;
    (
        ZipPlus::<MemoryBinZipTypes, _>::setup(folded_poly_size, make_iprs(num_vars)),
        ZipPlus::<MemoryArbZipTypes, _>::setup(poly_size, make_iprs(num_vars)),
        ZipPlus::<MemoryIntZipTypes, _>::setup(poly_size, make_iprs(num_vars)),
    )
}
