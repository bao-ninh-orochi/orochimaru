//! The memory-consistency UAIR (Univariate AIR) and its witness builder.
//!
//! # The statement
//!
//! The UAIR constrains a *sorted* memory trace: the execution trace re-ordered
//! by `(address, time_log)`. Together the constraints enforce, for every pair
//! of adjacent rows `i -> i+1` (rows `0 .. 2^num_vars - 1`, the final row is a
//! protocol-level padding row exempted by Zinc+'s last-row selector):
//!
//! 1. the very first access of the trace is a write,
//! 2. every instruction is boolean (`0` = read, `1` = write),
//! 3. `(address, time_log)` strictly increases row to row (lexicographically),
//! 4. a read from an address returns the value of the previous access to the
//!    same address,
//! 5. the first access to every *new* address is a write.
//!
//! These are exactly the constraints of the Halo2 `SortedMemoryCircuit` in
//! [`crate::constraints`]. What this backend does **not** yet prove is the
//! permutation link between the sorted trace and the original time-ordered
//! trace — Zinc+ currently has no permutation/lookup argument. See
//! `src/zincplus/README.md` for the exact security consequences.
//!
//! # Column layout
//!
//! Addresses and values are 256-bit integers and `time_log` is a `u64`; all
//! are decomposed into 32-bit limbs held in *binary polynomial* columns
//! (`BinaryPoly<32>`, one boolean coefficient per bit). Zinc+'s built-in
//! booleanity argument guarantees every committed coefficient is a bit, so
//! `limb(2)` (the polynomial evaluated at `X = 2`) is a canonical `u32`:
//! range checks come for free and never need a lookup table.
//!
//! Binary-polynomial columns (flat indices `0..19`):
//!
//! | index | content |
//! |-------|---------|
//! | `0..8`  | address limbs, most-significant first |
//! | `8..10` | `time_log` limbs, most-significant first |
//! | `10..18`| value limbs, most-significant first |
//! | `18`    | `r`: slack of the strict lexicographic increase at `i -> i+1` |
//!
//! Integer columns (public columns precede witness columns):
//!
//! | index | content |
//! |-------|---------|
//! | `0` (public) | `is_first`: fixed pattern `[1, 0, 0, ...]` checked by the verifier |
//! | `1`   | instruction (`1` = write, `0` = read) |
//! | `2..12` | `s_0..s_9`: one-hot selector of the first differing limb of `(address, time)` at `i -> i+1` |
//! | `12`  | `w = (s_8 + s_9) * (instr[i+1] - 1)`: helper keeping every constraint at degree <= 2 |
//!
//! # Constraint soundness sketch
//!
//! Write `L_0..L_9` for the lexicographic limb vector `address || time_log`
//! of the current row, `L'_j` for the next row, and `d_j = L'_j - L_j`.
//!
//! * `s_j` boolean and `sum_j s_j = 1` force exactly one selected position
//!   `k`.
//! * `(1 - e_j) * d_j = 0` with `e_j = s_0 + ... + s_j` forces `d_j = 0`
//!   for every `j < k` (booleanity of the limbs makes "equal value" and
//!   "equal bit pattern" coincide).
//! * `sum_j s_j * d_j - 1 - r in (X - 2)` forces `d_k(2) = 1 + r(2)` with
//!   `r(2)` a canonical `u32`, i.e. `1 <= d_k(2)`: the first differing limb
//!   strictly increases, hence `(address, time)` strictly increases. A
//!   dishonest choice of `k` (before or after the true first difference)
//!   contradicts one of the two previous bullets.
//! * `a_same = s_8 + s_9` is therefore `1` exactly when the first difference
//!   lies in the time limbs, i.e. when both rows touch the same address.
//! * `w = a_same * (instr' - 1)` is `-1` exactly for a *read at an unchanged
//!   address* and `0` otherwise, so `w * (value'_j - value_j) = 0` pins each
//!   read to the previous value, and `(1 - a_same) * (instr' - 1) = 0`
//!   forces the first access of a new address to be a write.

extern crate alloc;
use alloc::{vec, vec::Vec};
use core::cmp::Ordering;

use zinc_poly::univariate::{binary::BinaryPoly, dense::DensePolynomial};
use zinc_uair::{
    ideal::{DegreeOneIdeal, ImpossibleIdeal},
    ConstraintBuilder, PublicColumnLayout, ShiftSpec, TotalColumnLayout, TraceRow, Uair,
    UairSignature, UairTrace,
};

use crate::{
    base::{Base, B256},
    machine::{AbstractTraceRecord, MemoryInstruction, TraceRecord},
};

use super::{
    types::{Fmod, ZInt, D},
    ZincMemoryError,
};

/// Number of 32-bit limbs of an address.
pub(crate) const NUM_ADDR_LIMBS: usize = 8;
/// Number of 32-bit limbs of a `time_log`.
pub(crate) const NUM_TIME_LIMBS: usize = 2;
/// Number of 32-bit limbs of a value.
pub(crate) const NUM_VALUE_LIMBS: usize = 8;
/// Number of limbs compared lexicographically: `address || time_log`.
pub(crate) const NUM_LEX_LIMBS: usize = NUM_ADDR_LIMBS + NUM_TIME_LIMBS;

/// First binary-polynomial column of the address limbs.
const BP_ADDR: usize = 0;
/// First binary-polynomial column of the `time_log` limbs.
const BP_TIME: usize = BP_ADDR + NUM_ADDR_LIMBS;
/// First binary-polynomial column of the value limbs.
const BP_VALUE: usize = BP_TIME + NUM_TIME_LIMBS;
/// Binary-polynomial column of the lexicographic slack `r`.
const BP_SLACK: usize = BP_VALUE + NUM_VALUE_LIMBS;
/// Total number of binary-polynomial columns.
pub(crate) const NUM_BP_COLS: usize = BP_SLACK + 1;

/// Integer column of the public `is_first` indicator.
const INT_IS_FIRST: usize = 0;
/// Integer column of the instruction.
const INT_INSTR: usize = 1;
/// First integer column of the one-hot selectors `s_0..s_9`.
const INT_S: usize = 2;
/// Integer column of the degree-reduction helper `w`.
const INT_W: usize = INT_S + NUM_LEX_LIMBS;
/// Total number of integer columns.
pub(crate) const NUM_INT_COLS: usize = INT_W + 1;

/// Index of the (single) shifted integer column inside `down.int`:
/// the next row's instruction.
const DOWN_INT_INSTR: usize = 0;

/// The memory-consistency UAIR. See the module documentation for the full
/// description of columns and constraints.
#[derive(Clone, Debug)]
pub struct MemoryConsistencyUair;

impl Uair for MemoryConsistencyUair {
    type Ideal = DegreeOneIdeal<ZInt>;
    type FqIdeal = ImpossibleIdeal;
    type Scalar = DensePolynomial<ZInt, D>;
    type Prime = Fmod;

    fn signature() -> UairSignature<Self::Prime> {
        let total = TotalColumnLayout::new(NUM_BP_COLS, 0, NUM_INT_COLS);
        // Only `is_first` (the leading integer column) is public.
        let public = PublicColumnLayout::new(0, 0, 1);
        // Shift every address/time/value limb column and the instruction
        // column down by one row, so constraints can compare adjacent rows.
        // `source_col` uses flat `binary_poly || arbitrary_poly || int`
        // indexing; the slack column `r` needs no shifted copy.
        let mut shifts: Vec<ShiftSpec> = (BP_ADDR..BP_SLACK)
            .map(|col| ShiftSpec::new(col, 1))
            .collect();
        shifts.push(ShiftSpec::new(NUM_BP_COLS + INT_INSTR, 1));
        UairSignature::new(total, public, shifts, vec![])
    }

    fn constrain_general<B, FromR, MulByScalar, IFromR, IFqFromR>(
        b: &mut B,
        up: TraceRow<'_, B::Expr>,
        down: TraceRow<'_, B::Expr>,
        from_ref: FromR,
        _mbs: MulByScalar,
        ideal_from_ref: IFromR,
        _fq_ideal_from_ref: IFqFromR,
    ) where
        B: ConstraintBuilder,
        FromR: Fn(&Self::Scalar) -> B::Expr,
        MulByScalar: Fn(&B::Expr, &Self::Scalar) -> Option<B::Expr>,
        IFromR: Fn(&Self::Ideal) -> B::Ideal,
        IFqFromR: Fn(&Self::FqIdeal) -> B::FqIdeal,
    {
        let one = from_ref(&DensePolynomial::new([1 as ZInt]));
        // Ideal (X - 2): membership means "the expression evaluates to zero
        // at X = 2", i.e. the base-2 recompositions of the involved binary
        // limbs satisfy the stated integer identity.
        let base2 = ideal_from_ref(&DegreeOneIdeal::new(2 as ZInt));

        let is_first = &up.int[INT_IS_FIRST];
        let instr = &up.int[INT_INSTR];
        let selectors = &up.int[INT_S..INT_S + NUM_LEX_LIMBS];
        let w = &up.int[INT_W];
        let slack = &up.binary_poly[BP_SLACK];
        let instr_next = &down.int[DOWN_INT_INSTR];

        let instr_minus_one = instr.clone() - &one;
        let instr_next_minus_one = instr_next.clone() - &one;

        // (1) The first access of the sorted trace must be a write:
        //     is_first * (instr - 1) = 0.
        // `is_first` is a *public* column whose `[1, 0, 0, ...]` pattern is
        // checked directly by the verifier (`verify_memory_consistency`).
        b.assert_zero(is_first.clone() * &instr_minus_one);

        // (2) Instructions are boolean: instr' * (instr' - 1) = 0.
        // Stated on the *next* row so it covers rows 1..2^num_vars-1; row 0
        // is already pinned to a write by (1).
        b.assert_zero(instr_next.clone() * &instr_next_minus_one);

        // (3) Selector booleanity: s_j * (s_j - 1) = 0.
        for s_j in selectors {
            let s_j_minus_one = s_j.clone() - &one;
            b.assert_zero(s_j.clone() * &s_j_minus_one);
        }

        // (4) Exactly one first-difference position: sum_j s_j = 1.
        let s_sum = selectors[1..]
            .iter()
            .fold(selectors[0].clone(), |acc, s_j| acc + s_j);
        b.assert_zero(s_sum - &one);

        // (5) Limbs before the first difference are equal:
        //     (1 - (s_0 + ... + s_j)) * (L'_j - L_j) = 0 for every lex limb j.
        // (6) The first differing limb strictly increases:
        //     sum_j s_j * (L'_j - L_j) - 1 - r  in  (X - 2).
        // At X = 2 the latter reads d_k(2) = 1 + r(2) with r(2) a canonical
        // u32, hence d_k(2) >= 1. The lexicographic limbs are the leading
        // NUM_LEX_LIMBS binary columns; zipping with `selectors` (of exactly
        // that length) walks them in order.
        let mut prefix: Option<B::Expr> = None;
        let mut increase: Option<B::Expr> = None;
        for (s_j, (up_limb, down_limb)) in selectors
            .iter()
            .zip(up.binary_poly.iter().zip(down.binary_poly.iter()))
        {
            let d_j = down_limb.clone() - up_limb;
            let e_j = match prefix.take() {
                None => s_j.clone(),
                Some(sum) => sum + s_j,
            };
            b.assert_zero((one.clone() - &e_j) * &d_j);
            prefix = Some(e_j);
            let term = s_j.clone() * &d_j;
            increase = Some(match increase.take() {
                None => term,
                Some(acc) => acc + &term,
            });
        }
        let increase = increase.expect("NUM_LEX_LIMBS is non-zero");
        b.assert_in_ideal(increase - &one - slack, &base2);

        // `a_same` = 1 iff the first difference lies in the time limbs,
        // i.e. the adjacent rows touch the same address.
        let a_same = selectors[NUM_ADDR_LIMBS].clone() + &selectors[NUM_ADDR_LIMBS + 1];

        // (7) Degree-reduction helper: w = a_same * (instr' - 1).
        let w_definition = a_same.clone() * &instr_next_minus_one;
        b.assert_zero(w.clone() - &w_definition);

        // (8) A read at an unchanged address returns the previous value:
        //     w * (value'_j - value_j) = 0 for every value limb j.
        for j in 0..NUM_VALUE_LIMBS {
            let dv_j = down.binary_poly[BP_VALUE + j].clone() - &up.binary_poly[BP_VALUE + j];
            b.assert_zero(w.clone() * &dv_j);
        }

        // (9) The first access to a new address must be a write:
        //     (1 - a_same) * (instr' - 1) = 0.
        let a_changed = one.clone() - &a_same;
        b.assert_zero(a_changed * &instr_next_minus_one);
    }
}

/// A sorted-trace row in 32-bit limb form (most-significant limb first).
#[derive(Clone, Debug, PartialEq, Eq)]
struct RowLimbs {
    /// Address limbs.
    addr: [u32; NUM_ADDR_LIMBS],
    /// `time_log` limbs.
    time: [u32; NUM_TIME_LIMBS],
    /// Value limbs.
    value: [u32; NUM_VALUE_LIMBS],
    /// Instruction (`1` = write, `0` = read).
    instr: ZInt,
}

impl RowLimbs {
    /// Decompose one trace record into 32-bit limbs.
    fn from_record(record: &TraceRecord<B256, B256, 32, 32>) -> Self {
        let addr = be_bytes_to_limbs(&record.address().fixed_be_bytes());
        let value = be_bytes_to_limbs(&record.value().fixed_be_bytes());
        let time_log = record.time_log();
        let time = [(time_log >> 32) as u32, time_log as u32];
        let instr = match record.instruction() {
            MemoryInstruction::Write => 1,
            MemoryInstruction::Read => 0,
        };
        Self {
            addr,
            time,
            value,
            instr,
        }
    }

    /// The lexicographic comparison vector `address || time_log`.
    fn lex_limb(&self, j: usize) -> u32 {
        if j < NUM_ADDR_LIMBS {
            self.addr[j]
        } else {
            self.time[j - NUM_ADDR_LIMBS]
        }
    }
}

/// Split a 32-byte big-endian buffer into eight `u32` limbs, most-significant
/// limb first.
fn be_bytes_to_limbs(bytes: &[u8; 32]) -> [u32; 8] {
    core::array::from_fn(|j| {
        u32::from_be_bytes([
            bytes[4 * j],
            bytes[4 * j + 1],
            bytes[4 * j + 2],
            bytes[4 * j + 3],
        ])
    })
}

/// Minimum trace size (`2^MIN_NUM_VARS` rows) accepted by the Zip+ codes.
pub(crate) const MIN_NUM_VARS: usize = 3;
/// Maximum trace size exponent accepted by [`build_uair_trace`] and by the
/// verifier; bounds allocation on both sides.
pub(crate) const MAX_NUM_VARS: usize = 24;

/// Sort `trace` by `(address, time_log)` and build the full UAIR witness.
///
/// Returns the witness trace together with the number of MLE variables
/// (`log2` of the padded row count). The trace is padded to `2^num_vars`
/// rows — with at least one padding row, so no real record ever occupies
/// the final row, which Zinc+ exempts from constraints — by replaying the
/// last record as reads with increasing `time_log`s, which keeps every
/// constraint satisfied.
///
/// # Errors
///
/// * [`ZincMemoryError::EmptyTrace`] for an empty input,
/// * [`ZincMemoryError::TraceTooLong`] for more than `2^MAX_NUM_VARS - 1` records,
/// * [`ZincMemoryError::DuplicatedAccess`] when two records share an
///   `(address, time_log)` pair (real machine traces have globally unique
///   `time_log`s),
/// * [`ZincMemoryError::TimeLogOverflow`] when the padding rows would
///   overflow the `u64` time domain.
#[allow(clippy::type_complexity)]
pub(crate) fn build_uair_trace(
    trace: &[TraceRecord<B256, B256, 32, 32>],
) -> Result<(UairTrace<'static, ZInt, ZInt, D, D>, usize), ZincMemoryError> {
    if trace.is_empty() {
        return Err(ZincMemoryError::EmptyTrace);
    }

    let mut sorted = trace.to_vec();
    sorted.sort_by(|a, b| match a.address().cmp(&b.address()) {
        Ordering::Equal => a.time_log().cmp(&b.time_log()),
        ordering => ordering,
    });

    for pair in sorted.windows(2) {
        if pair[0].address() == pair[1].address() && pair[0].time_log() == pair[1].time_log() {
            return Err(ZincMemoryError::DuplicatedAccess {
                time_log: pair[0].time_log(),
            });
        }
    }

    // Reserve at least one padding row (the protocol-exempt last row).
    let padded_len = sorted
        .len()
        .checked_add(1)
        .and_then(usize::checked_next_power_of_two)
        .ok_or(ZincMemoryError::TraceTooLong)?;
    let num_vars = padded_len.trailing_zeros() as usize;
    if num_vars > MAX_NUM_VARS {
        return Err(ZincMemoryError::TraceTooLong);
    }
    let num_vars = num_vars.max(MIN_NUM_VARS);
    let num_rows = 1usize << num_vars;

    // Limb-decompose the sorted records and append the padding rows: replay
    // the last record as reads with strictly increasing time_logs.
    let mut rows: Vec<RowLimbs> = sorted.iter().map(RowLimbs::from_record).collect();
    let last = sorted.last().expect("trace is non-empty");
    let mut padding_time = last.time_log();
    for _ in rows.len()..num_rows {
        padding_time = padding_time
            .checked_add(1)
            .ok_or(ZincMemoryError::TimeLogOverflow)?;
        let mut padding = RowLimbs::from_record(last);
        padding.time = [(padding_time >> 32) as u32, padding_time as u32];
        padding.instr = 0;
        rows.push(padding);
    }

    // Per-transition witnesses: the one-hot first-difference selectors s_j,
    // the lexicographic slack r and the degree-reduction helper w. The final
    // row has no successor and is exempted by the protocol; its transition
    // witnesses stay zero.
    let mut s_columns = vec![vec![0 as ZInt; num_rows]; NUM_LEX_LIMBS];
    let mut slack_column = vec![BinaryPoly::<D>::from(0u32); num_rows];
    let mut w_column = vec![0 as ZInt; num_rows];
    for i in 0..num_rows - 1 {
        let (cur, next) = (&rows[i], &rows[i + 1]);
        let k = (0..NUM_LEX_LIMBS)
            .find(|&j| cur.lex_limb(j) != next.lex_limb(j))
            // Unreachable: duplicates were rejected above and padding rows
            // strictly increase the time limbs.
            .ok_or(ZincMemoryError::DuplicatedAccess {
                time_log: sorted.get(i).map_or(0, |r| r.time_log()),
            })?;
        let diff = i64::from(next.lex_limb(k)) - i64::from(cur.lex_limb(k));
        if diff < 1 {
            // Unreachable: `rows` is sorted by exactly this limb order.
            return Err(ZincMemoryError::UnsortedTrace);
        }
        s_columns[k][i] = 1;
        slack_column[i] = BinaryPoly::from((diff - 1) as u32);
        if k >= NUM_ADDR_LIMBS {
            // Same address: w = instr' - 1.
            w_column[i] = rows[i + 1].instr - 1;
        }
    }

    // Assemble the columns in the signature's flat order.
    let mut binary_poly = Vec::with_capacity(NUM_BP_COLS);
    for j in 0..NUM_ADDR_LIMBS {
        binary_poly.push(bp_column(&rows, |row| row.addr[j]));
    }
    for j in 0..NUM_TIME_LIMBS {
        binary_poly.push(bp_column(&rows, |row| row.time[j]));
    }
    for j in 0..NUM_VALUE_LIMBS {
        binary_poly.push(bp_column(&rows, |row| row.value[j]));
    }
    binary_poly.push(slack_column.into_iter().collect());

    let mut int = Vec::with_capacity(NUM_INT_COLS);
    int.push(is_first_column(num_rows));
    int.push(rows.iter().map(|row| row.instr).collect());
    for s_column in s_columns {
        int.push(s_column.into_iter().collect());
    }
    int.push(w_column.into_iter().collect());

    Ok((
        UairTrace {
            binary_poly: binary_poly.into(),
            arbitrary_poly: Vec::new().into(),
            int: int.into(),
        },
        num_vars,
    ))
}

/// Build one binary-polynomial column from a per-row `u32` limb.
fn bp_column(
    rows: &[RowLimbs],
    limb: impl Fn(&RowLimbs) -> u32,
) -> zinc_poly::mle::DenseMultilinearExtension<BinaryPoly<D>> {
    rows.iter().map(|row| BinaryPoly::from(limb(row))).collect()
}

/// The public `is_first` column: `[1, 0, 0, ...]`.
pub(crate) fn is_first_column(num_rows: usize) -> zinc_poly::mle::DenseMultilinearExtension<ZInt> {
    (0..num_rows).map(|i| ZInt::from(i == 0)).collect()
}
