//! The memory-consistency UAIR (Univariate AIR) and its witness builder.
//!
//! # The statement
//!
//! The UAIR proves the *composed* memory-consistency statement — the same
//! statement as the Halo2 `MemoryConsistencyCircuit` in
//! [`crate::constraints`], which combines three sub-circuits:
//!
//! 1. **Original-trace consistency** (Halo2 `OriginalMemoryCircuit`): the
//!    time-ordered execution trace `O` starts at `time_log = 0` and its
//!    `time_log`s strictly increase row to row.
//! 2. **Sorted-trace consistency** (Halo2 `SortedMemoryCircuit`): the trace
//!    `S` obtained by sorting `O` by `(address, time_log)` is internally
//!    consistent — the first access overall and the first access of every
//!    new address are writes, instructions are boolean, `(address,
//!    time_log)` strictly increases lexicographically, and every read
//!    returns the value of the previous access to the same address.
//! 3. **Permutation link** (Halo2 `PermutationCircuit`): `S` is a
//!    permutation of `O`.
//!
//! Both traces are witnesses and there are no public inputs beyond fixed
//! selector patterns, matching the Halo2 composed circuit exactly.
//!
//! # The permutation argument: a Beneš network
//!
//! Zinc+ has no permutation/lookup argument and no verifier-randomness
//! (RAP-style) columns, and every committed cell must be a small integer
//! fixed *before* the random prime modulus is sampled — so the randomized
//! grand-product argument used by PLONK's shuffle is not expressible.
//! Instead the permutation is enforced **deterministically** with a Beneš
//! switching network (the classic challenge-free technique for RAM
//! checking in proof systems, cf. Pantry/Buffet/xJsnark):
//!
//! * every trace row is one network *wire*; the network has `2v - 1` layers
//!   (`v` = `num_vars`, `2^v` rows) laid out horizontally as `2v` *state*
//!   column groups of [`PAYLOAD_CELLS`] columns each — state `0` is `S`,
//!   state `2v - 1` is `O`;
//! * layer `ℓ` sits between states `ℓ` and `ℓ + 1` and pairs row `i` with
//!   row `i + 2^{k_ℓ}` for every `i` whose bit `k_ℓ` is zero (see
//!   [`super::benes`] for the stride schedule);
//! * each pair is a 2×2 conditional swap controlled by one boolean switch
//!   witness shared by all payload columns:
//!   `out₁ = in₁ + s·(in₂ - in₁)` and `out₂ = in₂ - s·(in₂ - in₁)`,
//!   anchored at the upper row and masked by the public indicator column
//!   `upper_k` (`upper_k[i] = 1` iff bit `k` of `i` is zero);
//! * the swap equations are *cell-exact* (coefficient-wise on the binary
//!   polynomials), so each state is an exact permutation of the previous
//!   one and `multiset(O) = multiset(S)` holds exactly — soundness never
//!   depends on how the prover routes, only completeness does.
//!
//! The routed payload is the complete record — address, `time_log`,
//! `stack_depth`, value and instruction limbs — so the permutation binds
//! full records, like the Halo2 shuffle's random linear compression does.
//!
//! # Column layout
//!
//! Addresses and values are 256-bit and `time_log` / `stack_depth` are
//! `u64`; all are decomposed into 32-bit limbs held in *binary polynomial*
//! columns (`BinaryPoly<32>`, one boolean coefficient per bit). Zinc+'s
//! built-in booleanity argument guarantees every committed coefficient is
//! a bit, so `limb(2)` (the polynomial evaluated at `X = 2`) is a canonical
//! `u32`: range checks come for free and never need a lookup table. The
//! instruction also lives in a binary-polynomial cell, pinned to a constant
//! `0`/`1` polynomial by its booleanity constraint.
//!
//! Binary-polynomial columns (flat indices):
//!
//! | index | content |
//! |-------|---------|
//! | `g·21 .. g·21+21` | network state `g` (`g = 0`: sorted trace `S`, `g = 2v-1`: original trace `O`); within a state: address limbs `0..8`, `time_log` limbs `8..10`, `stack_depth` limbs `10..12`, value limbs `12..20`, instruction `20` (most-significant limb first) |
//! | `42v`   | `r_S`: slack of the strict lexicographic `(address, time_log)` increase of `S` |
//! | `42v+1` | `r_O`: slack of the strict `time_log` increase of `O` |
//!
//! Integer columns (public columns precede witness columns):
//!
//! | index | content |
//! |-------|---------|
//! | `0` (public) | `is_first`: fixed pattern `[1, 0, 0, ...]` |
//! | `1..v+1` (public) | `upper_k`, `k = 0..v`: bit-`k`-is-zero indicator of the row index |
//! | `v+1..v+11` | `s_0..s_9`: one-hot selector of the first differing limb of `S`'s `(address, time)` at `i -> i+1` |
//! | `v+11` | `w = (s_8 + s_9) · (instr_S[i+1] - 1)`: degree-reduction helper |
//! | `v+12`, `v+13` | `o_hi`, `o_lo`: one-hot selector of the first differing `time_log` limb of `O` at `i -> i+1` |
//! | `v+14..3v+13` | one switch-bit column per network layer |
//!
//! All public columns are reconstructed by the verifier itself
//! ([`public_int_columns`]) and absorbed into the Fiat-Shamir transcript
//! before any challenge is drawn.
//!
//! # Constraint soundness sketch
//!
//! *Sorted trace* (state `0`; write `L_0..L_9` for the lexicographic limb
//! vector `address || time_log`, primes for the next row, `d_j = L'_j -
//! L_j`):
//!
//! * `s_j` boolean and `sum_j s_j = 1` force exactly one selected position
//!   `k`; `(1 - (s_0 + ... + s_j)) · d_j = 0` forces `d_j = 0` for `j < k`;
//!   `sum_j s_j·d_j - 1 - r_S in (X - 2)` forces `d_k(2) = 1 + r_S(2)` with
//!   `r_S(2)` a canonical `u32`, so `(address, time)` strictly increases.
//! * `a_same = s_8 + s_9` is `1` exactly when adjacent rows touch the same
//!   address; `w = a_same · (instr' - 1)` is `-1` exactly for a read at an
//!   unchanged address, so `w · (value'_j - value_j) = 0` pins each read to
//!   the previous value and `(1 - a_same) · (instr' - 1) = 0` forces the
//!   first access of a new address to be a write. `is_first · (instr - 1) =
//!   0` makes the very first access a write.
//!
//! *Original trace* (state `2v - 1`): `is_first` pins both `time_log` limbs
//! of row 0 to zero; `o_hi`/`o_lo` are a one-hot selector with `(1 - o_hi)
//! · (hi' - hi) = 0` and `o_hi·(hi' - hi) + o_lo·(lo' - lo) - 1 - r_O in (X
//! - 2)`, which is exactly "the `u64` `time_log` strictly increases" —
//! the same relation as Halo2's `GreaterThanConfig` on the original trace.
//!
//! *Network*: for every layer and every upper row, `upper_k` masks the
//! boolean-switch swap equations described above. Rows partition into
//! disjoint switch pairs per layer, so each state is a permutation of the
//! previous one. Row `2^v - 1` (all index bits set) is never an anchor row
//! of any switch, so Zinc+'s built-in last-row constraint exemption opens
//! no hole in the network; the `S`/`O` transition constraints reaching the
//! last row are anchored at row `2^v - 2`, which is not exempt.
//!
//! All per-row constraint expressions have coefficients that are tiny
//! relative to the ~192-bit sampled prime `q`, so their vanishing mod `q`
//! implies vanishing over the integers: the permutation and consistency
//! statements hold exactly, not just probabilistically.

extern crate alloc;
use alloc::{collections::BTreeMap, vec, vec::Vec};
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
    benes,
    types::{Fmod, ZInt, D},
    ZincMemoryError,
};

/// Number of 32-bit limbs of an address.
pub(crate) const NUM_ADDR_LIMBS: usize = 8;
/// Number of 32-bit limbs of a `time_log`.
pub(crate) const NUM_TIME_LIMBS: usize = 2;
/// Number of 32-bit limbs of a `stack_depth`.
pub(crate) const NUM_STACK_DEPTH_LIMBS: usize = 2;
/// Number of 32-bit limbs of a value.
pub(crate) const NUM_VALUE_LIMBS: usize = 8;
/// Number of limbs compared lexicographically: `address || time_log`.
pub(crate) const NUM_LEX_LIMBS: usize = NUM_ADDR_LIMBS + NUM_TIME_LIMBS;

/// Payload offset of the address limbs (also the start of the lex limbs).
pub(crate) const PL_ADDR: usize = 0;
/// Payload offset of the `time_log` limbs.
pub(crate) const PL_TIME: usize = PL_ADDR + NUM_ADDR_LIMBS;
/// Payload offset of the `stack_depth` limbs.
pub(crate) const PL_STACK_DEPTH: usize = PL_TIME + NUM_TIME_LIMBS;
/// Payload offset of the value limbs.
pub(crate) const PL_VALUE: usize = PL_STACK_DEPTH + NUM_STACK_DEPTH_LIMBS;
/// Payload offset of the instruction cell.
pub(crate) const PL_INSTR: usize = PL_VALUE + NUM_VALUE_LIMBS;
/// Number of binary-polynomial cells of one full record: the payload routed
/// through every switch of the permutation network.
pub(crate) const PAYLOAD_CELLS: usize = PL_INSTR + 1;

/// Minimum trace size (`2^MIN_NUM_VARS` rows) accepted by the Zip+ codes.
pub(crate) const MIN_NUM_VARS: usize = 3;
/// Maximum trace size exponent accepted by [`build_uair_trace`] and by the
/// verifier.
///
/// Bounded by practicality rather than protocol limits: the Beneš network
/// adds `~21·(2v)` committed columns and the verifier pays `O(2^{v-1})`
/// field operations per large-stride shifted column, so very large traces
/// belong to a future lookup-based permutation argument (see
/// `src/zincplus/README.md`).
pub(crate) const MAX_NUM_VARS: usize = 16;

/// The column layout of the memory-consistency UAIR for a given trace size,
/// shared by [`Uair::signature`], the constraint emission and the witness
/// builder so all three can never disagree.
pub(crate) struct NetLayout {
    /// `log2` of the (padded) row count.
    num_vars: usize,
    /// Number of Beneš layers: `2·num_vars - 1`.
    pub(crate) num_layers: usize,
    /// Number of network states: `num_layers + 1`; state `0` is the sorted
    /// trace, state `num_states - 1` the original trace.
    num_states: usize,
    /// Total binary-polynomial columns.
    pub(crate) num_bp_cols: usize,
    /// Total integer columns (public + witness).
    pub(crate) num_int_cols: usize,
    /// Leading integer columns that are public.
    pub(crate) num_public_int_cols: usize,
    /// Binary column of the sorted-trace lexicographic slack `r_S`.
    pub(crate) bp_slack_sorted: usize,
    /// Binary column of the original-trace time slack `r_O`.
    pub(crate) bp_slack_original: usize,
    /// Integer column of the public `is_first` indicator.
    int_is_first: usize,
    /// First of the `num_vars` public `upper_k` indicator columns.
    int_upper: usize,
    /// First of the [`NUM_LEX_LIMBS`] sorted-trace selector columns.
    int_s: usize,
    /// Integer column of the sorted-trace degree-reduction helper `w`.
    int_w: usize,
    /// Integer column of the original-trace high-limb selector `o_hi`.
    int_time_hi_sel: usize,
    /// Integer column of the original-trace low-limb selector `o_lo`.
    int_time_lo_sel: usize,
    /// First of the `num_layers` switch-bit columns.
    pub(crate) int_switch: usize,
    /// Every `(source_col, shift_amount)` pair, sorted; position `i` in this
    /// list is index `i` of the down row's binary-polynomial slice.
    shifts: Vec<(usize, usize)>,
}

impl NetLayout {
    /// Build the layout for `2^num_vars` rows.
    pub(crate) fn new(num_vars: usize) -> Self {
        assert!(
            (MIN_NUM_VARS..=MAX_NUM_VARS).contains(&num_vars),
            "num_vars {num_vars} outside [{MIN_NUM_VARS}, {MAX_NUM_VARS}]"
        );
        let num_layers = benes::num_layers(num_vars);
        let num_states = num_layers + 1;
        let payload_cols = num_states * PAYLOAD_CELLS;
        let bp_slack_sorted = payload_cols;
        let bp_slack_original = payload_cols + 1;
        let num_bp_cols = payload_cols + 2;

        let int_is_first = 0;
        let int_upper = 1;
        let int_s = int_upper + num_vars;
        let int_w = int_s + NUM_LEX_LIMBS;
        let int_time_hi_sel = int_w + 1;
        let int_time_lo_sel = int_time_hi_sel + 1;
        let int_switch = int_time_lo_sel + 1;
        let num_int_cols = int_switch + num_layers;
        let num_public_int_cols = 1 + num_vars;

        let mut layout = Self {
            num_vars,
            num_layers,
            num_states,
            num_bp_cols,
            num_int_cols,
            num_public_int_cols,
            bp_slack_sorted,
            bp_slack_original,
            int_is_first,
            int_upper,
            int_s,
            int_w,
            int_time_hi_sel,
            int_time_lo_sel,
            int_switch,
            shifts: Vec::new(),
        };
        layout.shifts = layout.build_shifts();
        layout
    }

    /// The flat binary column of payload cell `p` of network state `g`.
    pub(crate) fn state_col(&self, state: usize, payload: usize) -> usize {
        debug_assert!(state < self.num_states && payload < PAYLOAD_CELLS);
        state * PAYLOAD_CELLS + payload
    }

    /// Index of the original-trace state (the network output).
    pub(crate) fn original_state(&self) -> usize {
        self.num_states - 1
    }

    /// The row stride of network layer `layer`.
    fn stride(&self, layer: usize) -> usize {
        1usize << benes::stride_bit(self.num_vars, layer)
    }

    /// All `(source_col, shift_amount)` pairs, sorted by column then amount.
    ///
    /// * State `0` (the sorted trace) is consumed by layer `0` (stride
    ///   `2^{v-1}`) and by the sorted-trace transition constraints (shift
    ///   `1`, all payload cells except `stack_depth`, which no sorted-trace
    ///   constraint reads).
    /// * Interior state `g` is produced by layer `g - 1` and consumed by
    ///   layer `g`; each needs the corresponding stride.
    /// * The last state (the original trace) is produced by the final layer
    ///   and its `time_log` limbs feed the shift-`1` time-ordering
    ///   constraints.
    fn build_shifts(&self) -> Vec<(usize, usize)> {
        let mut shifts = Vec::new();
        let last = self.original_state();
        for state in 0..self.num_states {
            for payload in 0..PAYLOAD_CELLS {
                let col = self.state_col(state, payload);
                let amounts: [Option<usize>; 2] = if state == 0 {
                    let in_transitions = payload != PL_STACK_DEPTH && payload != PL_STACK_DEPTH + 1;
                    [in_transitions.then_some(1), Some(self.stride(0))]
                } else if state < last {
                    let (a, b) = (self.stride(state - 1), self.stride(state));
                    [Some(a.min(b)), Some(a.max(b))]
                } else {
                    let in_transitions = payload == PL_TIME || payload == PL_TIME + 1;
                    [
                        in_transitions.then_some(1),
                        Some(self.stride(self.num_layers - 1)),
                    ]
                };
                for amount in amounts.into_iter().flatten() {
                    shifts.push((col, amount));
                }
            }
        }
        debug_assert!(
            shifts.windows(2).all(|w| w[0] < w[1]),
            "shift list must be strictly sorted"
        );
        shifts
    }

    /// The signature's [`ShiftSpec`] list, in down-row order.
    fn shift_specs(&self) -> Vec<ShiftSpec> {
        self.shifts
            .iter()
            .map(|&(col, amount)| ShiftSpec::new(col, amount))
            .collect()
    }

    /// Index inside the down row's binary-polynomial slice of the virtual
    /// column "`col` shifted down by `amount`".
    fn down_idx(&self, col: usize, amount: usize) -> usize {
        self.shifts
            .binary_search(&(col, amount))
            .expect("every (column, shift) pair used by a constraint is declared")
    }
}

/// The memory-consistency UAIR for traces of `2^V` (padded) rows. See the
/// module documentation for the full description of columns and
/// constraints.
///
/// The trace-size exponent is a const generic because a
/// [`UairSignature`] is static per type while the Beneš network's column
/// count and row strides depend on the trace size; [`super::prover`]
/// dispatches over the supported range.
#[derive(Clone, Debug)]
pub struct MemoryConsistencyUair<const V: usize>;

impl<const V: usize> Uair for MemoryConsistencyUair<V> {
    type Ideal = DegreeOneIdeal<ZInt>;
    type FqIdeal = ImpossibleIdeal;
    type Scalar = DensePolynomial<ZInt, D>;
    type Prime = Fmod;

    fn signature() -> UairSignature<Self::Prime> {
        let layout = NetLayout::new(V);
        let total = TotalColumnLayout::new(layout.num_bp_cols, 0, layout.num_int_cols);
        // `is_first` and the `upper_k` bit indicators (the leading integer
        // columns) are public.
        let public = PublicColumnLayout::new(0, 0, layout.num_public_int_cols);
        UairSignature::new(total, public, layout.shift_specs(), vec![])
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
        let layout = NetLayout::new(V);
        let one = from_ref(&DensePolynomial::new([1 as ZInt]));
        // Ideal (X - 2): membership means "the expression evaluates to zero
        // at X = 2", i.e. the base-2 recompositions of the involved binary
        // limbs satisfy the stated integer identity.
        let base2 = ideal_from_ref(&DegreeOneIdeal::new(2 as ZInt));

        let is_first = &up.int[layout.int_is_first];
        // Down-row accessor: the virtual column "`col` shifted by `amount`".
        let down_bp = |col: usize, amount: usize| &down.binary_poly[layout.down_idx(col, amount)];

        // ------------------------------------------------------------------
        // Sorted trace (network state 0).
        // ------------------------------------------------------------------
        let instr_col = layout.state_col(0, PL_INSTR);
        let instr = &up.binary_poly[instr_col];
        let instr_next = down_bp(instr_col, 1);
        let selectors = &up.int[layout.int_s..layout.int_s + NUM_LEX_LIMBS];
        let w = &up.int[layout.int_w];
        let slack_sorted = &up.binary_poly[layout.bp_slack_sorted];

        let instr_minus_one = instr.clone() - &one;
        let instr_next_minus_one = instr_next.clone() - &one;

        // (S1) The first access of the sorted trace must be a write:
        //      is_first * (instr - 1) = 0.
        b.assert_zero(is_first.clone() * &instr_minus_one);

        // (S2) Instructions are boolean (and, as polynomial cells, constant):
        //      instr' * (instr' - 1) = 0. Stated on the *next* row so it
        //      covers rows 1..2^V - 1; row 0 is pinned to a write by (S1).
        b.assert_zero(instr_next.clone() * &instr_next_minus_one);

        // (S3) Selector booleanity: s_j * (s_j - 1) = 0.
        for s_j in selectors {
            let s_j_minus_one = s_j.clone() - &one;
            b.assert_zero(s_j.clone() * &s_j_minus_one);
        }

        // (S4) Exactly one first-difference position: sum_j s_j = 1.
        let s_sum = selectors[1..]
            .iter()
            .fold(selectors[0].clone(), |acc, s_j| acc + s_j);
        b.assert_zero(s_sum - &one);

        // (S5) Limbs before the first difference are equal:
        //      (1 - (s_0 + ... + s_j)) * (L'_j - L_j) = 0 for every lex limb.
        // (S6) The first differing limb strictly increases:
        //      sum_j s_j * (L'_j - L_j) - 1 - r_S  in  (X - 2).
        let mut prefix: Option<B::Expr> = None;
        let mut increase: Option<B::Expr> = None;
        for (j, s_j) in selectors.iter().enumerate() {
            let limb_col = layout.state_col(0, PL_ADDR + j);
            let d_j = down_bp(limb_col, 1).clone() - &up.binary_poly[limb_col];
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
        b.assert_in_ideal(increase - &one - slack_sorted, &base2);

        // `a_same` = 1 iff the first difference lies in the time limbs,
        // i.e. the adjacent rows touch the same address.
        let a_same = selectors[NUM_ADDR_LIMBS].clone() + &selectors[NUM_ADDR_LIMBS + 1];

        // (S7) Degree-reduction helper: w = a_same * (instr' - 1).
        let w_definition = a_same.clone() * &instr_next_minus_one;
        b.assert_zero(w.clone() - &w_definition);

        // (S8) A read at an unchanged address returns the previous value:
        //      w * (value'_j - value_j) = 0 for every value limb j.
        for j in 0..NUM_VALUE_LIMBS {
            let value_col = layout.state_col(0, PL_VALUE + j);
            let dv_j = down_bp(value_col, 1).clone() - &up.binary_poly[value_col];
            b.assert_zero(w.clone() * &dv_j);
        }

        // (S9) The first access to a new address must be a write:
        //      (1 - a_same) * (instr' - 1) = 0.
        let a_changed = one.clone() - &a_same;
        b.assert_zero(a_changed * &instr_next_minus_one);

        // ------------------------------------------------------------------
        // Original trace (the last network state): time_log starts at zero
        // and strictly increases — the Halo2 `OriginalMemoryConfig` relation.
        // ------------------------------------------------------------------
        let time_hi_col = layout.state_col(layout.original_state(), PL_TIME);
        let time_lo_col = layout.state_col(layout.original_state(), PL_TIME + 1);
        let time_hi = &up.binary_poly[time_hi_col];
        let time_lo = &up.binary_poly[time_lo_col];
        let hi_sel = &up.int[layout.int_time_hi_sel];
        let lo_sel = &up.int[layout.int_time_lo_sel];
        let slack_original = &up.binary_poly[layout.bp_slack_original];

        // (O1, O2) The first access happens at time_log = 0: both limbs of
        // row 0 vanish.
        b.assert_zero(is_first.clone() * time_hi);
        b.assert_zero(is_first.clone() * time_lo);

        // (O3) Selector booleanity and (O4) one-hotness.
        let hi_sel_minus_one = hi_sel.clone() - &one;
        b.assert_zero(hi_sel.clone() * &hi_sel_minus_one);
        let lo_sel_minus_one = lo_sel.clone() - &one;
        b.assert_zero(lo_sel.clone() * &lo_sel_minus_one);
        b.assert_zero(hi_sel.clone() + lo_sel - &one);

        // (O5) When the first difference is in the low limb, the high limbs
        // are equal: (1 - o_hi) * (hi' - hi) = 0.
        let d_hi = down_bp(time_hi_col, 1).clone() - time_hi;
        let d_lo = down_bp(time_lo_col, 1).clone() - time_lo;
        b.assert_zero((one.clone() - hi_sel) * &d_hi);

        // (O6) The selected limb strictly increases:
        //      o_hi*(hi' - hi) + o_lo*(lo' - lo) - 1 - r_O  in  (X - 2),
        // which together with (O5) is exactly "the u64 time_log strictly
        // increases".
        let selected = hi_sel.clone() * &d_hi + &(lo_sel.clone() * &d_lo);
        b.assert_in_ideal(selected - &one - slack_original, &base2);

        // ------------------------------------------------------------------
        // The Beneš network: state ℓ+1 is state ℓ with each switch pair
        // conditionally swapped.
        // ------------------------------------------------------------------
        for layer in 0..layout.num_layers {
            let stride = layout.stride(layer);
            let mask = &up.int[layout.int_upper + benes::stride_bit(V, layer)];
            let switch = &up.int[layout.int_switch + layer];

            // (N1) Switch booleanity at every anchor (upper) row:
            //      upper_k * s * (s - 1) = 0.
            let switch_minus_one = switch.clone() - &one;
            b.assert_zero(mask.clone() * &(switch.clone() * &switch_minus_one));

            // (N2, N3) Conditional swap, cell-exact per payload column:
            //      out₁ = in₁ + s·(in₂ - in₁),  out₂ = in₂ - s·(in₂ - in₁).
            for payload in 0..PAYLOAD_CELLS {
                let in_col = layout.state_col(layer, payload);
                let out_col = layout.state_col(layer + 1, payload);
                let in_1 = &up.binary_poly[in_col];
                let in_2 = down_bp(in_col, stride);
                let out_1 = &up.binary_poly[out_col];
                let out_2 = down_bp(out_col, stride);
                let diff = in_2.clone() - in_1;
                let switched = switch.clone() * &diff;
                b.assert_zero(mask.clone() * &(out_1.clone() - in_1 - &switched));
                b.assert_zero(mask.clone() * &(out_2.clone() - in_2 + &switched));
            }
        }
    }
}

/// One trace record in 32-bit limb form (most-significant limb first): the
/// payload routed through the permutation network.
#[derive(Clone, Debug, PartialEq, Eq)]
struct RowLimbs {
    /// Address limbs.
    addr: [u32; NUM_ADDR_LIMBS],
    /// `time_log` limbs.
    time: [u32; NUM_TIME_LIMBS],
    /// `stack_depth` limbs.
    stack_depth: [u32; NUM_STACK_DEPTH_LIMBS],
    /// Value limbs.
    value: [u32; NUM_VALUE_LIMBS],
    /// Instruction (`1` = write, `0` = read).
    instr: u32,
}

impl RowLimbs {
    /// Decompose one trace record into 32-bit limbs.
    fn from_record(record: &TraceRecord<B256, B256, 32, 32>) -> Self {
        let addr = be_bytes_to_limbs(&record.address().fixed_be_bytes());
        let value = be_bytes_to_limbs(&record.value().fixed_be_bytes());
        let time_log = record.time_log();
        let stack_depth = record.stack_depth();
        let instr = match record.instruction() {
            MemoryInstruction::Write => 1,
            MemoryInstruction::Read => 0,
        };
        Self {
            addr,
            time: [(time_log >> 32) as u32, time_log as u32],
            stack_depth: [(stack_depth >> 32) as u32, stack_depth as u32],
            value,
            instr,
        }
    }

    /// The payload cell `p` (see the module documentation's payload order).
    fn payload(&self, p: usize) -> u32 {
        match p {
            PL_ADDR..PL_TIME => self.addr[p - PL_ADDR],
            PL_TIME..PL_STACK_DEPTH => self.time[p - PL_TIME],
            PL_STACK_DEPTH..PL_VALUE => self.stack_depth[p - PL_STACK_DEPTH],
            PL_VALUE..PL_INSTR => self.value[p - PL_VALUE],
            PL_INSTR => self.instr,
            _ => unreachable!("payload index out of range"),
        }
    }

    /// The lexicographic comparison vector `address || time_log`.
    fn lex_limb(&self, j: usize) -> u32 {
        debug_assert!(j < NUM_LEX_LIMBS);
        self.payload(PL_ADDR + j)
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

/// Build the full UAIR witness for a *time-ordered* execution trace.
///
/// The input must satisfy the same contract the Halo2
/// `OriginalMemoryCircuit` enforces on the original trace: `time_log`s
/// start at `0` and strictly increase (gaps are allowed). The builder sorts
/// the trace by `(address, time_log)`, pads both orderings with benign
/// replay rows, routes the Beneš network linking them and assembles every
/// witness column.
///
/// Returns the witness trace together with the number of MLE variables
/// (`log2` of the padded row count). At least one padding row is always
/// kept, so no real record ever occupies the final row, which Zinc+
/// exempts from constraints. Padding rows replay the last *sorted* record
/// as reads with `time_log`s continuing past the global maximum, which
/// satisfies both orderings' constraints and keeps the two padded
/// multisets equal.
///
/// # Errors
///
/// * [`ZincMemoryError::EmptyTrace`] for an empty input,
/// * [`ZincMemoryError::FirstTimeNonZero`] when `time_log[0] != 0`,
/// * [`ZincMemoryError::DuplicatedAccess`] when two consecutive records
///   share a `time_log`,
/// * [`ZincMemoryError::TimeNotIncreasing`] when a `time_log` decreases,
/// * [`ZincMemoryError::TraceTooLong`] for more than `2^MAX_NUM_VARS - 1`
///   records,
/// * [`ZincMemoryError::TimeLogOverflow`] when the padding rows would
///   overflow the `u64` time domain.
#[allow(clippy::type_complexity)]
pub(crate) fn build_uair_trace(
    trace: &[TraceRecord<B256, B256, 32, 32>],
) -> Result<(UairTrace<'static, ZInt, ZInt, D, D>, usize), ZincMemoryError> {
    // Halo2-parity input contract (`OriginalMemoryCircuit`): the trace is
    // given in execution order, starting at time_log 0, strictly increasing.
    if let Some(first) = trace.first() {
        if first.time_log() != 0 {
            return Err(ZincMemoryError::FirstTimeNonZero {
                time_log: first.time_log(),
            });
        }
    }
    build_uair_trace_any_start(trace)
}

/// [`build_uair_trace`] without the `time_log[0] = 0` contract check.
///
/// The builder itself only needs strictly increasing `time_log`s; skipping
/// the start check lets soundness tests hand the circuit an otherwise
/// perfectly consistent witness whose *only* violation is the original
/// trace not starting at time zero, isolating that in-circuit constraint.
#[allow(clippy::type_complexity)]
pub(crate) fn build_uair_trace_any_start(
    trace: &[TraceRecord<B256, B256, 32, 32>],
) -> Result<(UairTrace<'static, ZInt, ZInt, D, D>, usize), ZincMemoryError> {
    if trace.is_empty() {
        return Err(ZincMemoryError::EmptyTrace);
    }
    for pair in trace.windows(2) {
        match pair[1].time_log().cmp(&pair[0].time_log()) {
            Ordering::Greater => {}
            Ordering::Equal => {
                return Err(ZincMemoryError::DuplicatedAccess {
                    time_log: pair[0].time_log(),
                })
            }
            Ordering::Less => {
                return Err(ZincMemoryError::TimeNotIncreasing {
                    time_log: pair[1].time_log(),
                })
            }
        }
    }

    // Reserve at least one padding row (the protocol-exempt last row).
    let padded_len = trace
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
    let layout = NetLayout::new(num_vars);

    let mut sorted = trace.to_vec();
    sorted.sort_by(|a, b| match a.address().cmp(&b.address()) {
        Ordering::Equal => a.time_log().cmp(&b.time_log()),
        ordering => ordering,
    });

    // Padding rows replay the last sorted record (the maximum address) as
    // reads with time_logs continuing past the global maximum, so they sit
    // at the tail of *both* orderings and the two multisets stay equal.
    let pad_base = *sorted.last().expect("trace is non-empty");
    let mut padding = Vec::with_capacity(num_rows - trace.len());
    let mut padding_time = trace.last().expect("trace is non-empty").time_log();
    for _ in trace.len()..num_rows {
        padding_time = padding_time
            .checked_add(1)
            .ok_or(ZincMemoryError::TimeLogOverflow)?;
        padding.push(TraceRecord::new(
            padding_time,
            pad_base.stack_depth(),
            MemoryInstruction::Read,
            pad_base.address(),
            pad_base.value(),
        ));
    }

    let original_rows: Vec<RowLimbs> = trace
        .iter()
        .chain(padding.iter())
        .map(RowLimbs::from_record)
        .collect();
    let sorted_rows: Vec<RowLimbs> = sorted
        .iter()
        .chain(padding.iter())
        .map(RowLimbs::from_record)
        .collect();

    // Sorted-trace transition witnesses: the one-hot first-difference
    // selectors s_j, the lexicographic slack r_S and the helper w. The final
    // row has no successor and is exempted by the protocol; its transition
    // witnesses stay zero.
    let mut s_columns = vec![vec![0 as ZInt; num_rows]; NUM_LEX_LIMBS];
    let mut slack_sorted_column = vec![BinaryPoly::<D>::from(0u32); num_rows];
    let mut w_column = vec![0 as ZInt; num_rows];
    for i in 0..num_rows - 1 {
        let (cur, next) = (&sorted_rows[i], &sorted_rows[i + 1]);
        let k = (0..NUM_LEX_LIMBS)
            .find(|&j| cur.lex_limb(j) != next.lex_limb(j))
            // Unreachable: input time_logs are strictly increasing (hence
            // globally unique) and padding rows extend them further.
            .ok_or(ZincMemoryError::UnsortedTrace)?;
        let diff = i64::from(next.lex_limb(k)) - i64::from(cur.lex_limb(k));
        if diff < 1 {
            // Unreachable: `sorted_rows` is sorted by exactly this limb order.
            return Err(ZincMemoryError::UnsortedTrace);
        }
        s_columns[k][i] = 1;
        slack_sorted_column[i] = BinaryPoly::from((diff - 1) as u32);
        if k >= NUM_ADDR_LIMBS {
            // Same address: w = instr' - 1.
            w_column[i] = ZInt::from(sorted_rows[i + 1].instr) - 1;
        }
    }

    // Original-trace transition witnesses: which time limb first differs,
    // and the slack of its strict increase.
    let mut hi_sel_column = vec![0 as ZInt; num_rows];
    let mut lo_sel_column = vec![0 as ZInt; num_rows];
    let mut slack_original_column = vec![BinaryPoly::<D>::from(0u32); num_rows];
    for i in 0..num_rows - 1 {
        let (cur, next) = (&original_rows[i], &original_rows[i + 1]);
        let (sel, diff) = if cur.time[0] != next.time[0] {
            (
                &mut hi_sel_column,
                i64::from(next.time[0]) - i64::from(cur.time[0]),
            )
        } else {
            (
                &mut lo_sel_column,
                i64::from(next.time[1]) - i64::from(cur.time[1]),
            )
        };
        if diff < 1 {
            // Unreachable: validated strictly increasing above.
            return Err(ZincMemoryError::UnsortedTrace);
        }
        sel[i] = 1;
        slack_original_column[i] = BinaryPoly::from((diff - 1) as u32);
    }

    // The permutation linking the orderings: original row j holds the same
    // record as sorted row perm[j]; time_logs are unique, so they key it.
    let sorted_pos_by_time: BTreeMap<u64, usize> = sorted
        .iter()
        .chain(padding.iter())
        .enumerate()
        .map(|(pos, record)| (record.time_log(), pos))
        .collect();
    let perm: Vec<usize> = trace
        .iter()
        .chain(padding.iter())
        .map(|record| sorted_pos_by_time[&record.time_log()])
        .collect();

    // Route the Beneš network and materialize every intermediate state's
    // payload columns; state 0 is the sorted trace, the final state must be
    // the original trace.
    let switch_layers = benes::route(&perm);
    let mut binary_poly = Vec::with_capacity(layout.num_bp_cols);
    let mut state = sorted_rows.clone();
    for layer in 0..=layout.num_layers {
        if layer > 0 {
            benes::apply_layer(&mut state, num_vars, layer - 1, &switch_layers[layer - 1]);
        }
        for payload in 0..PAYLOAD_CELLS {
            binary_poly.push(bp_column(&state, |row| row.payload(payload)));
        }
    }
    if state != original_rows {
        // Unreachable: `benes::route` realizes exactly this permutation.
        return Err(ZincMemoryError::UnsortedTrace);
    }
    binary_poly.push(slack_sorted_column.into_iter().collect());
    binary_poly.push(slack_original_column.into_iter().collect());
    debug_assert_eq!(binary_poly.len(), layout.num_bp_cols);

    // Assemble the integer columns: publics first (exactly as the verifier
    // rebuilds them), then the witness selectors and switch bits.
    let mut int = Vec::with_capacity(layout.num_int_cols);
    int.extend(public_int_columns(num_vars));
    for s_column in s_columns {
        int.push(s_column.into_iter().collect());
    }
    int.push(w_column.into_iter().collect());
    int.push(hi_sel_column.into_iter().collect());
    int.push(lo_sel_column.into_iter().collect());
    for bits in &switch_layers {
        int.push(bits.iter().map(|&bit| ZInt::from(bit)).collect());
    }
    debug_assert_eq!(int.len(), layout.num_int_cols);

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

/// The public integer columns, in signature order: `is_first`
/// (`[1, 0, 0, ...]`) followed by the `upper_k` bit indicators
/// (`upper_k[i] = 1` iff bit `k` of the row index `i` is zero), `k = 0 ..
/// num_vars`. The verifier reconstructs these itself, so a proof is only
/// accepted for exactly these public inputs.
pub(crate) fn public_int_columns(
    num_vars: usize,
) -> Vec<zinc_poly::mle::DenseMultilinearExtension<ZInt>> {
    let num_rows = 1usize << num_vars;
    let mut columns = Vec::with_capacity(1 + num_vars);
    columns.push((0..num_rows).map(|i| ZInt::from(i == 0)).collect());
    for k in 0..num_vars {
        columns.push((0..num_rows).map(|i| ZInt::from(i >> k & 1 == 0)).collect());
    }
    columns
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layout_shift_list_is_sorted_and_complete() {
        for num_vars in MIN_NUM_VARS..=6 {
            let layout = NetLayout::new(num_vars);
            assert!(layout.shifts.windows(2).all(|w| w[0] < w[1]));
            // Every constraint-side lookup must resolve.
            for layer in 0..layout.num_layers {
                let stride = layout.stride(layer);
                for payload in 0..PAYLOAD_CELLS {
                    layout.down_idx(layout.state_col(layer, payload), stride);
                    layout.down_idx(layout.state_col(layer + 1, payload), stride);
                }
            }
            for j in 0..NUM_LEX_LIMBS {
                layout.down_idx(layout.state_col(0, PL_ADDR + j), 1);
            }
            for j in 0..NUM_VALUE_LIMBS {
                layout.down_idx(layout.state_col(0, PL_VALUE + j), 1);
            }
            layout.down_idx(layout.state_col(0, PL_INSTR), 1);
            layout.down_idx(layout.state_col(layout.original_state(), PL_TIME), 1);
            layout.down_idx(layout.state_col(layout.original_state(), PL_TIME + 1), 1);
        }
    }

    #[test]
    fn test_signature_dimensions_match_layout() {
        let layout = NetLayout::new(3);
        let signature = <MemoryConsistencyUair<3> as Uair>::signature();
        assert_eq!(
            signature.total_cols().num_binary_poly_cols(),
            layout.num_bp_cols
        );
        assert_eq!(signature.total_cols().num_int_cols(), layout.num_int_cols);
        assert_eq!(
            signature.public_cols().num_int_cols(),
            layout.num_public_int_cols
        );
        assert_eq!(signature.shifts().len(), layout.shifts.len());
        // All shifted sources are binary columns, so the down row is pure
        // binary: its layout must place every virtual column there.
        assert_eq!(
            signature.down_cols().num_binary_poly_cols(),
            layout.shifts.len()
        );
        assert_eq!(signature.down_cols().num_int_cols(), 0);
    }
}
