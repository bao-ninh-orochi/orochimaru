# Zinc+ backend walkthrough

This document is the technical companion to [`README.md`](README.md). The README
is the reference for parameters, security status and the migration plan; this
walkthrough develops the constraint system itself, so that the constraint code
in [`uair.rs`](uair.rs) and [`benes.rs`](benes.rs) can be read with a precise
model of what each line enforces and why. Familiarity with the statement
zkMemory proves — that an execution trace is memory-consistent — is assumed;
familiarity with Zinc+ internals is not.

Contents:

1. **The running example** — the trace used in every table and figure.
2. **The statement** — the three sub-statements and how they map to Halo2.
3. **Constraint-system preliminaries** — the two Zinc+ properties that shape
   the design, and the two assertion forms.
4. **The trace table** — rows, columns, cells, and the full column layout.
5. **Recurring constraint techniques** — slack variables, evaluate-at-2,
   lexicographic selectors.
6. **Constraint ① — original-trace consistency.**
7. **Constraint ② — sorted-trace consistency.**
8. **Constraint ③ — the Beneš permutation network.**
9. **Composition** — how the three constraints combine, padding, and the
   complete example witness.
10. **Reviewer's map** — where each piece lives and what to verify.

A single running example is carried from start to finish. It is sized at
`num_vars = 3` (8 rows) — the smallest trace size the backend accepts
([`MIN_NUM_VARS`](uair.rs), required by the Zip+ linear codes). The structure
is identical at every size; only the number of rows, network states and layers
grows.

---

## 1. The running example

Seven memory operations over three addresses `A < B < C`:

| time | operation | note |
|-----:|-----------|------|
| 0 | **Write** `A` ← `10` | first access overall |
| 1 | **Write** `B` ← `20` | |
| 2 | **Read** `A` → `10` | returns the value written at time 0 |
| 3 | **Write** `A` ← `30` | overwrites `A` |
| 4 | **Read** `B` → `20` | |
| 5 | **Read** `A` → `30` | returns the overwritten value, not `10` |
| 6 | **Write** `C` ← `40` | |

The trace is padded to `2^3 = 8` rows; the witness builder always reserves at
least one padding row (§9). Each operation becomes a **record**, abbreviated
`A@0:W=10` for "address `A`, time 0, Write, value 10" and named by its address
and time:

```
rA0 = A@0:W=10   rB1 = B@1:W=20   rA2 = A@2:R=10   rA3 = A@3:W=30
rB4 = B@4:R=20   rA5 = A@5:R=30   rC6 = C@6:W=40   rC7 = C@7:R=40  (padding)
```

The padding record `rC7` replays the last *sorted* record (`rC6`) as a read at
the next time step; §9 explains why this construction satisfies every
constraint.

The backend operates on two orderings of these eight records:

- **`O` — the original trace**, in time order:
  `rA0, rB1, rA2, rA3, rB4, rA5, rC6, rC7`
- **`S` — the sorted trace**, sorted by `(address, time)`:
  `rA0, rA2, rA3, rA5, rB1, rB4, rC6, rC7`

The entire proof is a statement about these two lists.

---

## 2. The statement

The backend proves the same statement as Halo2's composed
`MemoryConsistencyCircuit`, which is the conjunction of three sub-statements:

| # | sub-statement | Halo2 circuit | section |
|---|---------------|---------------|:-------:|
| ① | **Original**: `O` is time-ordered — `time_log[0] = 0` and `time_log` strictly increases | `OriginalMemoryCircuit` | §6 |
| ② | **Sorted**: `S` is memory-consistent — grouped and ordered by `(address, time)`, the first access to each address is a write, and every read returns the last written value | `SortedMemoryCircuit` | §7 |
| ③ | **Permutation**: `S` is a permutation of `O` (the same multiset of records) | `PermutationCircuit` (randomized shuffle) | §8 |

The essential design difference is ③. Halo2 proves the permutation with a
*randomized* shuffle: each record is compressed with a verifier challenge and
the two compressed column products are compared. Zinc+ cannot express this:
its challenges — including the prime modulus the constraints are projected
into — are sampled *after* the witness is committed, and committed cells are
fixed small integers, so no verifier randomness can enter the witness.
Constraint ③ is therefore enforced **deterministically** by a **Beneš
switching network** (§8): a fixed circuit of conditional swaps that
rearranges `S` into `O` in-circuit. This construction has zero soundness
error and requires no challenge.

---

## 3. Constraint-system preliminaries

Zinc+ itself is described in [`README.md`](README.md) (section "What Zinc+
is"). This section records only what the constraint code depends on: two
protocol properties that dictate the backend's design, and the two assertion
forms the constraints are written in.

The two properties:

1. **No post-commitment randomness in cells.** All challenges are drawn from a
   Blake3 Fiat-Shamir transcript *after* commitment, so committed cells cannot
   depend on verifier randomness. This is why ③ is a Beneš network rather
   than a randomized shuffle.
2. **Binary-polynomial cells are range-checked by construction.** A
   binary-polynomial cell holds 32 coefficients, each proven to be a bit by
   Zinc+'s built-in booleanity argument. A cell is therefore simultaneously a
   32-bit value and a `u32` range check — no lookup tables are needed
   anywhere in this backend.

A constraint program (a **UAIR**) declares columns and asserts per-row
polynomial relations. Two assertion forms appear throughout:

- `assert_zero(expr)` — `expr` must be identically `0` on every
  (non-exempt) row.
- `assert_in_ideal(expr, X−2)` — `expr` must be divisible by `(X − 2)`,
  which by the factor theorem means `expr` evaluates to `0` at `X = 2`.
  Since a limb's *value* is its bit-polynomial evaluated at `X = 2`, this is
  the form in which integer identities about limb values are stated (§5.2).

---

## 4. The trace table

### 4.1 Rows, columns, cells

The whole proof commits to **one table** of `2^num_vars` rows. There are two
independent column families, each indexed from 0:

- **`binary_poly` columns** — each cell is a `BinaryPoly<32>` (32 bits).
  These hold the record fields and the two ordering slacks.
- **`int` columns** — each cell is a single integer (only `{−1, 0, 1}`
  occur). These hold the selectors and the switch bits.

Indices are per-family: "binary column 126" and "int column 0" address
different arrays; the number is an index into one family, not a global
address.

A row holds more than one record: because of the Beneš-network layout (§8),
row `i` contains position `i` of *several* orderings of the trace, side by
side (§4.3).

### 4.2 A record occupies 21 cells

One record is decomposed into 21 binary-polynomial cells (the `PL_*` payload
offsets in [`uair.rs`](uair.rs)). Each field is split into 32-bit limbs,
most-significant limb first, because one cell holds 32 bits:

```
  payload cell:      0 … 7      8  9        10  11     12 … 19     20
                  ┌─────────┬──────────┬─────────────┬─────────┬───────┐
                  │ address │ time_log │ stack_depth │  value  │ instr │
                  │ 8 limbs │ 2 limbs  │   2 limbs   │ 8 limbs │ 1 cell│
                  └─────────┴──────────┴─────────────┴─────────┴───────┘
                    256 bits    u64          u64       256 bits R=0 W=1
```

| offset | cells | field | meaning |
|--------|-------|-------|---------|
| 0–7 | 8 | **address** | which memory slot (256-bit) |
| 8–9 | 2 | **time_log** | global counter of when the access happened (`u64`) |
| 10–11 | 2 | **stack_depth** | call-stack depth (`u64`; carried through the network but never constrained) |
| 12–19 | 8 | **value** | the word read or written (256-bit) |
| 20 | 1 | **instruction** | Read (`0`) or Write (`1`) |

`8 + 2 + 2 + 8 + 1 = 21`. Each of the eight example records occupies 21 cells
of one row.

### 4.3 The network-state layout of the binary columns

The table stores the two orderings `S` and `O` — plus every intermediate
snapshot of the Beneš network — as horizontal blocks of 21 columns, all
sharing the same rows. Each block is a **network state**. With
`num_vars = 3` there are `2·num_vars = 6` states and `2·num_vars − 1 = 5`
layers between them, giving `6·21 + 2 = 128` binary columns:

```
    0 … 20   21 … 41   42 … 62   63 … 83   84 … 104 105 … 125  126   127
 ┌─────────┬─────────┬─────────┬─────────┬─────────┬─────────┬─────┬─────┐
 │ state 0 │ state 1 │ state 2 │ state 3 │ state 4 │ state 5 │ r_S │ r_O │
 │   = S   │         │         │         │         │   = O   │     │     │
 └─────────┴─────────┴─────────┴─────────┴─────────┴─────────┴─────┴─────┘
   21 cells  21 cells  21 cells  21 cells  21 cells  21 cells   1     1
           ▲         ▲         ▲         ▲         ▲
        layer 0   layer 1   layer 2   layer 3   layer 4
```

*Figure 1 — the binary-polynomial column family (`num_vars = 3`). Each `▲`
marks a Beneš layer: layer `ℓ` (§8) transforms state `ℓ` into state `ℓ+1`.*

- **State 0** (columns 0–20) is the **sorted trace `S`** — the network input.
- **State 5** (columns 105–125) is the **original trace `O`** — the network
  output.
- **States 1–4** are the Beneš intermediates (§8).
- **`r_S`** (column 126) and **`r_O`** (column 127) are the two ordering
  *slacks* (§5.1) — helper columns placed after all state blocks, not inside
  any record.

"The original trace" is therefore literally the block of 21 columns at
105–125, read top to bottom. Its two `time_log` limbs sit at columns
`105 + 8 = 113` and `105 + 9 = 114`.

### 4.4 The integer columns

With `num_vars = 3` there are 22 integer columns. The public columns come
first:

```
      0             1   2   3           4 … 13     14     15  16     17 … 21
 ┌──────────┬───────────────────────┬───────────┬─────┬───────────┬───────────┐
 │ is_first │upper_0 upper_1 upper_2│ s_0 … s_9 │  w  │ o_hi  o_lo│sw_0 … sw_4│
 └──────────┴───────────────────────┴───────────┴─────┴───────────┴───────────┘
 └───────────── public ────────────┘└─────────────── witness ────────────────┘
```

*Figure 2 — the integer column family (`num_vars = 3`). `sw_ℓ` is the switch
column of Beneš layer `ℓ`.*

| int col | name | public? | content |
|--------:|------|:-------:|---------|
| 0 | `is_first` | ✅ | `[1, 0, 0, 0, 0, 0, 0, 0]` — marks row 0 |
| 1 | `upper_0` | ✅ | "bit 0 of the row index is 0": `[1, 0, 1, 0, 1, 0, 1, 0]` |
| 2 | `upper_1` | ✅ | "bit 1 of the row index is 0": `[1, 1, 0, 0, 1, 1, 0, 0]` |
| 3 | `upper_2` | ✅ | "bit 2 of the row index is 0": `[1, 1, 1, 1, 0, 0, 0, 0]` |
| 4–13 | `s_0 … s_9` | | one-hot first-difference selector of the sorted trace (§7) |
| 14 | `w` | | read-consistency helper (§7) |
| 15 | `o_hi` | | original-trace high time-limb selector (§6) |
| 16 | `o_lo` | | original-trace low time-limb selector (§6) |
| 17–21 | `sw_0 … sw_4` | | Beneš switch bits, one column per layer (§8) |

The public columns (`is_first`, `upper_k`) are rebuilt by the verifier itself
([`uair.rs`](uair.rs) `public_int_columns`, consumed in
[`prover.rs`](prover.rs) `verify_memory_consistency`), so a proof only
validates against this exact, fixed selector pattern — there are no
trace-dependent public inputs.

### 4.5 The table as a whole

Combining both families, the committed table has the following shape
(schematically — the intermediate states are collapsed and the integer
columns abbreviated):

```
              binary-poly columns (128)               int columns (22)
         ┌──────┬───────────┬──────┬───┬───┐  ┌─────┬─────┬─────┬───┬───┬────┐
   row   │ st 0 │  st 1 … 4 │ st 5 │r_S│r_O│  │ i_f │ u_k │ s_j │ w │o_*│sw_ℓ│
         │ = S  │ (interm.) │ = O  │   │   │  │ pub │ pub │     │   │   │    │
    0    │ S[0] │     ·     │ O[0] │ · │ · │  │  1  │  ·  │  ·  │ · │ · │ ·  │
    1    │ S[1] │     ·     │ O[1] │ · │ · │  │  0  │  ·  │  ·  │ · │ · │ ·  │
    ⋮    │  ⋮   │     ⋮     │  ⋮   │   │   │  │  ⋮  │     │     │   │   │    │
    7    │ S[7] │     ·     │ O[7] │ · │ · │  │  0  │  ·  │  ·  │ · │ · │ ·  │
         └──────┴───────────┴──────┴───┴───┘  └─────┴─────┴─────┴───┴───┴────┘
```

*Figure 3 — the complete trace table (`num_vars = 3`): 8 rows, 128
binary-polynomial columns and 22 integer columns. `st g` = network state `g`,
each entry standing for the 21 cells of one record; `i_f` = `is_first`,
`u_k` = `upper_0..upper_2`, `s_j` = `s_0 … s_9`, `o_*` = `o_hi`/`o_lo`,
`sw_ℓ` = the five switch columns; `pub` marks the public columns. Every `·`
is a witness cell whose semantics are developed in §5–§8; exact column
indices are given in Figures 1 and 2. §9 shows this table fully populated
with the running example's witness.*

---

## 5. Recurring constraint techniques

Three techniques recur in every constraint group.

### 5.1 Expressing `<` as `= 0`: the slack variable

A constraint system can only assert that an expression equals zero, but
"strictly increasing" is an inequality. To prove `b > a` for two `u32`
values, introduce a witness `r` (the **slack**) and assert

```
b − a − 1 = r        with   r ≥ 0
```

`b − a − 1 = r ≥ 0` ⟺ `b − a ≥ 1` ⟺ `b > a`. The `−1` makes the
inequality strict; `r` absorbs any gap (a step `1 → 5` gives `r = 3`). The
condition `r ≥ 0` costs nothing extra: the slack lives in a binary-polynomial
column, so booleanity already proves its bits are in `{0, 1}` and hence its
value lies in `[0, 2³² − 1]`. No modular wraparound is possible: all involved
quantities are genuine small integers, tiny relative to the ~192-bit sampled
prime, so a negative difference can never satisfy `b − a − 1 = r` with `r`
non-negative.

### 5.2 Reading limb values: evaluation at 2

A limb is stored as bits; its value is the bit-polynomial evaluated at
`X = 2`. The equation `b − a − 1 − r = 0` over limb *values* is therefore
written `assert_in_ideal(b − a − 1 − r, X−2)`, i.e. "this polynomial
evaluates to 0 at `X = 2`" ([`uair.rs`](uair.rs), `base2`).

### 5.3 Comparing multi-limb keys: one-hot selector, lexicographic order

A slack range-checks only one `u32` at a time, so a multi-limb key is
compared **lexicographically**, most-significant limb first, with a
**one-hot selector** naming the first limb that differs. This pattern
appears twice: for the 2-limb `time_log` of `O` (§6, selector `o_hi`/`o_lo`)
and for the 10-limb `address ‖ time_log` of `S` (§7, selector `s_0 … s_9`).

---

## 6. Constraint ① — original-trace consistency

**Goal:** `O` (state 5) is time-ordered: `time_log[0] = 0` and `time_log`
strictly increases. Code: [`uair.rs`](uair.rs), constraints O1–O6.

**Columns read:** the two `time_log` limbs of state 5 (binary columns 113,
114), `is_first` (int 0), `o_hi`/`o_lo` (int 15/16), and the slack `r_O`
(binary column 127).

For the running example, state 5 = `O` with times `0, 1, …, 7`:

| row | record | time_hi | time_lo | is_first | o_hi | o_lo | r_O | |
|----:|:------:|--------:|--------:|:--------:|:----:|:----:|:---:|---|
| 0 | rA0 | 0 | 0 | **1** | 0 | 1 | 0 | |
| 1 | rB1 | 0 | 1 | 0 | 0 | 1 | 0 | |
| 2 | rA2 | 0 | 2 | 0 | 0 | 1 | 0 | |
| 3 | rA3 | 0 | 3 | 0 | 0 | 1 | 0 | |
| 4 | rB4 | 0 | 4 | 0 | 0 | 1 | 0 | |
| 5 | rA5 | 0 | 5 | 0 | 0 | 1 | 0 | |
| 6 | rC6 | 0 | 6 | 0 | 0 | 1 | 0 | |
| 7 | rC7 | 0 | 7 | 0 | 0 | 0 | 0 | ← exempt last row |

The selectors `o_hi`/`o_lo` and the slack `r_O` at row `i` describe the
transition `i → i+1`; the final row has no successor and is exempt (§9).

### `time_log[0] = 0` (O1, O2)

```
assert_zero(is_first · time_hi)      // O1
assert_zero(is_first · time_lo)      // O2
```

AIR constraints are uniform — the same expression holds on every row — so a
*boundary* condition is imposed by multiplying with a selector that is
nonzero only where the condition applies. `is_first = 1` only at row 0; on
rows 1–7 the product is trivially zero, and at row 0 it forces
`time_hi = time_lo = 0`.

### `time_log` strictly increases (O3–O6)

`time_log` is a `u64` in two limbs `(hi, lo)`, so the comparison is a 2-limb
lexicographic one. `o_hi`/`o_lo` (one-hot, enforced by O3/O4) name the limb
that first differs; with `d_hi = hi[i+1] − hi[i]` and
`d_lo = lo[i+1] − lo[i]`:

```
// O5: if lo differs first, hi must be equal
assert_zero((1 − o_hi) · d_hi)

// O6: the selected limb strictly increases
assert_in_ideal(o_hi·d_hi + o_lo·d_lo − 1 − r_O, X−2)
```

Both selector cases are correct:

- **`hi` differs** (`o_hi = 1`): O5 is vacuous and O6 forces `d_hi ≥ 1`. The
  low limb is left unconstrained — correct, because the upper 32 bits
  dominate the comparison.
- **`hi` equal, `lo` differs** (`o_lo = 1`): O5 forces `hi[i+1] = hi[i]` and
  O6 forces `d_lo ≥ 1`.

Together this is exactly "the `u64` strictly increased", and it is complete:
a low-limb step cannot overturn a high-limb step because each limb value is
below `2³²`. The selector cannot be misassigned either: claiming `o_lo` while
`hi` actually differs violates O5 (`d_hi ≠ 0`). In the example every step is
the `o_lo` case with `d_lo = 1` and `r_O = 0`.

> **Time gaps are permitted.** Had the operation at time 2 instead occurred
> at time 5, the step `1 → 5` would set `r_O = 5 − 1 − 1 = 3`; nothing else
> changes.

---

## 7. Constraint ② — sorted-trace consistency

**Goal:** `S` (state 0) is memory-consistent. Code: [`uair.rs`](uair.rs),
constraints S1–S9.

**Why sort by `(address, time)`?** Sorting groups every access to one address
into a contiguous, time-ordered run. "The previous access to this address"
then becomes simply *the row above*, so consistency reduces to checks between
**adjacent rows** — the only relation an AIR can inspect cheaply.

State 0 = `S`; the selector, slack and helper at row `i` describe the
transition `i → i+1`:

| row | record | addr | time | instr | value | first-diff | r_S | a_same | w | |
|----:|:------:|:----:|-----:|:-----:|------:|:----------:|:---:|:------:|:---:|---|
| 0 | rA0 | A | 0 | W | 10 | `s_9` (time_lo) | 1 | 1 | **−1** | |
| 1 | rA2 | A | 2 | R | 10 | `s_9` (time_lo) | 0 | 1 | 0 | |
| 2 | rA3 | A | 3 | W | 30 | `s_9` (time_lo) | 1 | 1 | **−1** | |
| 3 | rA5 | A | 5 | R | 30 | `s_7` (address) | 0 | 0 | 0 | |
| 4 | rB1 | B | 1 | W | 20 | `s_9` (time_lo) | 2 | 1 | **−1** | |
| 5 | rB4 | B | 4 | R | 20 | `s_7` (address) | 0 | 0 | 0 | |
| 6 | rC6 | C | 6 | W | 40 | `s_9` (time_lo) | 0 | 1 | **−1** | |
| 7 | rC7 | C | 7 | R | 40 | — | — | — | — | ← exempt last row |

(The slack values at the address boundaries, rows 3 and 5, assume `A`, `B`,
`C` are consecutive integers, so the differing address limb — the
least-significant one, selector `s_7` — increases by exactly 1.)

The nine constraints fall into three groups.

### Group 1 — ordering (S3–S6): the 10-limb analogue of O3–O6

The pattern of §6, with the key extended to `address ‖ time_log` = 10 limbs
(0–7 address, 8–9 time), the selector `s_0 … s_9` and the slack `r_S`. The
only mechanical difference is that "all more-significant limbs are equal" now
spans several limbs, expressed with the prefix sum `e_j = s_0 + … + s_j`:

```
// S5: limbs before the first difference are equal
assert_zero((1 − e_j) · d_j)

// S6: the selected limb strictly increases
assert_in_ideal(Σ s_j·d_j − 1 − r_S, X−2)
```

Result: `(address, time_log)` strictly increases lexicographically, so the
trace is grouped by address and time-ordered within each group. Note how the
slack absorbs within-group time gaps: `rB1 → rB4` steps time `1 → 4`, giving
`d = 3` and `r_S = 2`.

### Group 2 — address-boundary detection

Because the address occupies limbs 0–7 and the time limbs 8–9:

```
a_same = s_8 + s_9
```

If the first differing limb is a time limb (8 or 9), all address limbs were
equal by S5 — same address. If it is an address limb (0–7) — new address.
The ordering selector doubles as an address-boundary detector at no
additional cost (the Halo2 circuit requires a dedicated `IsZero` gadget for
the same purpose).

### Group 3 — memory consistency (S1, S9, S2, S7, S8)

**No read before a write:**

```
// S1: the very first access is a Write
assert_zero(is_first · (instr − 1))

// S9: the first access of each new address is a Write
assert_zero((1 − a_same) · (instr' − 1))

// S2: instructions are boolean (and pinned constant)
assert_zero(instr' · (instr' − 1))
```

(S2 is stated on the *next* row so it covers rows 1–7; row 0's instruction
is already pinned to Write by S1.)

**Reads return the last written value:**

```
// S7: define the helper w
assert_zero(w − a_same · (instr' − 1))

// S8: a same-address read echoes the previous value
for each value limb j:
    assert_zero(w · (value'[j] − value[j]))
```

`w = a_same · (instr' − 1)` equals `−1` exactly when the next row is a read
at an unchanged address, and `0` otherwise, so S8 pins a read's value to the
previous row's on all 8 value limbs — the full 256-bit word. (The Halo2
version drops the top limb via `skip(1)`; this one does not.) `w` exists
only to keep the constraint degree at 2 instead of 3.

**Reading the example:**

- S1 fires at row 0: `rA0` is a Write.
- `w = −1` at rows 0, 2, 4, 6 (the next row is a same-address read), so S8
  forces `value[1] = value[0] = 10`, `value[3] = value[2] = 30`,
  `value[5] = value[4] = 20` and `value[7] = value[6] = 40`.
- At row 1 the next access is a Write (`rA3`), so `w = 0` and S8 imposes
  nothing: the value may change from `10` to `30`. This is the overwrite
  of `A`.
- `a_same = 0` at rows 3 and 5 (address changes `A→B` and `B→C`), so S9
  forces the next records (`rB1`, `rC6`) to be Writes.

### Why adjacent checks suffice

Ordering makes each address's accesses contiguous and time-sorted. Within a
group, the first row is a Write (S1/S9) and every later Read echoes the row
above (S8). By induction along the group, every read equals the most recent
write — full memory consistency from neighbor comparisons alone.

> **The remaining gap:** S1–S9 prove that `S` is an internally valid,
> sorted, consistent trace — but not that it contains the same records as
> the real execution `O`. Closing that gap is constraint ③.

---

## 8. Constraint ③ — the Beneš permutation network

**Goal:** `S` (state 0) and `O` (state 5) are the same multiset of records.

### 8.1 Conditional-swap networks

The building block is a **2×2 conditional swap**: a fixed gadget on two wires
whose only degree of freedom is a boolean switch:

```
switch = 0 (pass-through)              switch = 1 (swap)
   in₁ ─────────── out₁ = in₁             in₁ ──╲  ╱── out₁ = in₂
   in₂ ─────────── out₂ = in₂             in₂ ──╱  ╲── out₂ = in₁
```

A single layer of such switches can only exchange elements within its fixed
pairs. A **Beneš network** stacks several layers with *different* pairings so
that every element can reach every position: a Beneš network on `2^v` wires
with `2v − 1` layers realizes **every** permutation of its inputs. The layer
count follows from the recursive construction — an entry layer, two
half-size Beneš networks, an exit layer: `layers(v) = 2 + layers(v−1)` with
`layers(1) = 1`, hence `2v − 1`.

The pairing of layer `ℓ` is determined by its **stride bit** `k_ℓ`
([`benes.rs`](benes.rs) `stride_bit`): the layer pairs row `i` with row
`i + 2^{k_ℓ}` for every `i` whose bit `k_ℓ` is zero (the **box top**). The
stride-bit sequence is `v−1, …, 1, 0, 1, …, v−1` — a butterfly followed by
an inverse butterfly. For 8 wires (`v = 3`) there are five layers:

| layer ℓ | stride bit k | stride 2^k | mask | box-top rows (bit k = 0) | boxes (top, bottom) |
|--------:|:------------:|:----------:|:---------:|:------------------------:|:--------------------|
| 0 | 2 | 4 | `upper_2` | 0, 1, 2, 3 | (0,4) (1,5) (2,6) (3,7) |
| 1 | 1 | 2 | `upper_1` | 0, 1, 4, 5 | (0,2) (1,3) (4,6) (5,7) |
| 2 | 0 | 1 | `upper_0` | 0, 2, 4, 6 | (0,1) (2,3) (4,5) (6,7) |
| 3 | 1 | 2 | `upper_1` | 0, 1, 4, 5 | (0,2) (1,3) (4,6) (5,7) |
| 4 | 2 | 4 | `upper_2` | 0, 1, 2, 3 | (0,4) (1,5) (2,6) (3,7) |

### 8.2 The layout and the example routing

The network is laid out horizontally in the trace table: each **row is a
wire**, each **state is a snapshot** (a 21-column block, Figure 1), and
**layer `ℓ` transforms state `ℓ` into state `ℓ+1`**. State 0 = `S` (input),
state 5 = `O` (output).

Routing the running example (`⇄` marks the two rows of a switched-ON box in
that layer):

| row | state 0 = `S` | L0 | state 1 | L1 | state 2 | L2 | state 3 | L3 | state 4 | L4 | state 5 = `O` |
|----:|:----:|:--:|:----:|:--:|:----:|:--:|:----:|:--:|:----:|:--:|:----:|
| 0 | rA0 |  | rA0 |  | rA0 |  | rA0 |  | rA0 |  | rA0 |
| 1 | rA2 |  | rA2 | ⇄ | rA5 |  | rA5 |  | rA5 | ⇄ | rB1 |
| 2 | rA3 |  | rA3 |  | rA3 | ⇄ | rA2 |  | rA2 |  | rA2 |
| 3 | rA5 |  | rA5 | ⇄ | rA2 | ⇄ | rA3 |  | rA3 |  | rA3 |
| 4 | rB1 |  | rB1 |  | rB1 | ⇄ | rB4 |  | rB4 |  | rB4 |
| 5 | rB4 |  | rB4 |  | rB4 | ⇄ | rB1 |  | rB1 | ⇄ | rA5 |
| 6 | rC6 |  | rC6 |  | rC6 |  | rC6 |  | rC6 |  | rC6 |
| 7 | rC7 |  | rC7 |  | rC7 |  | rC7 |  | rC7 |  | rC7 |

The corresponding switch-bit witness (`·` marks box-bottom rows, whose bits
are never read):

| layer | switch bits at rows 0 … 7 | ON boxes |
|------:|:--------------------------|:---------|
| 0 | `0 0 0 0 · · · ·` | — |
| 1 | `0 1 · · 0 0 · ·` | (1,3) |
| 2 | `0 · 1 · 1 · 0 ·` | (2,3), (4,5) |
| 3 | `0 0 · · 0 0 · ·` | — |
| 4 | `0 1 0 0 · · · ·` | (1,5) |

Two features of this routing are worth tracing. First, the permutation must
move two records across the boundary between the top half (rows 0–3) and the
bottom half (rows 4–7): `rA5` travels from sorted position 3 to original
position 5, and `rB1` from sorted position 4 to original position 1. Rows in
different halves share a box only in the stride-4 layers (0 and 4); the
router realizes both crossings through layer 4's single box (1,5), after
steering `rA5` up to row 1 (layer 1, box (1,3)) and `rB1` down to row 5
(layer 2, box (4,5)). Second, layer 2's box (2,3) restores the relative
order of `rA2` and `rA3`, which the layer-1 swap had displaced.

### 8.3 Two separate mechanisms: wiring versus settings

| question | decided by | fixed or chosen? |
|----------|-----------|------------------|
| Which rows a box connects | the layer's stride, and the `upper_k` mask marking box tops | **fixed and public** — the verifier rebuilds it |
| Whether a box swaps | the switch bit `s` | **prover witness** (the routing) |

The prover controls only the on/off bits, never the wiring. This separation
is what makes the argument sound (§8.5).

### 8.4 The constraints (N1–N3)

For each layer, with `mask = upper_k`, `switch = s`, and the partner row read
via the shifted column `down_bp(col, stride)` ([`uair.rs`](uair.rs) N1–N3):

```
// N1: the switch is a bit
assert_zero(mask · switch · (switch − 1))

// N2: out₁ = in₁ + s·(in₂ − in₁)
// N3: out₂ = in₂ − s·(in₂ − in₁)
for each of the 21 payload cells:
    switched = switch · (in₂ − in₁)
    assert_zero(mask · (out₁ − in₁ − switched))   // N2
    assert_zero(mask · (out₂ − in₂ + switched))   // N3
```

Three observations:

- **N1** forces `s ∈ {0, 1}`.
- **N2 + N3** are the conditional-swap equations: `s = 0` passes through,
  `s = 1` swaps. Given that `s` is a bit, they rigidly pin
  `{out₁, out₂} = {in₁, in₂}` — no fabricated record is expressible.
- **The mask** restricts the constraint to box-top rows; the box-bottom
  row's outputs are pinned by its top's N3, so every cell is constrained
  exactly once. The loop over the 21 payload cells moves the whole record as
  a unit, under one shared switch bit.

*Worked check.* Layer 1's ON box (1,3): `stride = 2`,
`mask = upper_1[1] = 1`, `s = 1`. Inputs: `in₁ =` state 1 row 1 = `rA2`,
`in₂ =` state 1 row 3 = `rA5`. N2 forces `out₁ = in₂ = rA5` (state 2 row 1
✓); N3 forces `out₂ = in₁ = rA2` (state 2 row 3 ✓) — on all 21 cells at
once. For an OFF box the equations reduce to `out = in`; layer 0 is entirely
off in this routing, so state 1 equals state 0.

### 8.5 Why this has zero soundness error

N1 makes `s` a bit, so N2 + N3 force each box's outputs to be exactly its
inputs, passed through or swapped — an exact integer identity (the
coefficients are tiny relative to the ~192-bit prime, so no wraparound is
possible). Each box therefore preserves its two records as a multiset,
regardless of `s`. A layer is a set of disjoint boxes covering all rows, so
it preserves the whole state's multiset; composing all `2v − 1` layers,
state 5 (`O`) contains exactly the same records as state 0 (`S`).

Note that the constraints never check that the routing is *correct* — only
that each box is a genuine conditional swap. A mis-routed network still
preserves the multiset; it merely delivers the records to state 5 in the
wrong order, which then violates constraint ① on state 5. A malicious
prover's options are therefore to route correctly and prove a true
statement, or to route incorrectly and fail — never to inject or drop a
record. Routing ([`benes.rs`](benes.rs) `route`) is a completeness-only
concern; the witness builder asserts that the routed output equals `O`
before proving ([`uair.rs`](uair.rs), `state != original_rows`).

---

## 9. Composition

The endpoints of the network are pinned to real, independently checked
orderings:

- **state 0 = `S`** must satisfy the sorted-trace constraints (②),
- **state 5 = `O`** must satisfy the original-trace constraints (①),
- the **network** (③) proves states 0 and 5 hold the same records.

Together: *there exist two orderings of one record multiset — one
time-ordered from 0 and strictly increasing, one `(address, time)`-sorted and
memory-consistent.* This is exactly the composed Halo2 statement. Both traces
are witnesses; as in the Halo2 circuit, there are no trace-dependent public
inputs.

**Padding and the exempt last row.** Zinc+ exempts the final row
(row `2^v − 1`) from every constraint, so the builder always keeps at least
one padding row — no real record ever occupies the exempt row. Padding rows
replay the last *sorted* record as reads with `time_log`s continuing past the
global maximum. This satisfies every constraint that does reach them:
transition constraints anchored at row `2^v − 2` (which is not exempt) still
bind the final row — in the example, `S`'s row-6→7 transition requires the
read `rC7` to echo `rC6`'s value (S8) and `O`'s requires time `6 → 7` to
increase (O6) — and appending identical records to both orderings preserves
the multiset equality. The exemption opens no hole in the network either:
row `2^v − 1` has every index bit set, so `upper_k[2^v − 1] = 0` for every
`k`; the final row is never a box top, and every box it participates in is
anchored, and therefore constrained, at its non-exempt top row.

**The complete example witness.** The table below is Figure 3 fully
populated for the running example — every column of §4, all 8 rows. Each
state entry stands for the 21 cells of one record; `s` and `o` name the
selector column set to 1 at that row; `sw` lists the five switch bits.

| row | st 0 = `S` | st 1 | st 2 | st 3 | st 4 | st 5 = `O` | r_S | r_O | is_first | u_0 u_1 u_2 | s | w | o | sw_0…sw_4 |
|----:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | rA0 | rA0 | rA0 | rA0 | rA0 | rA0 | 1 | 0 | 1 | 1 1 1 | s_9 | −1 | o_lo | 0 0 0 0 0 |
| 1 | rA2 | rA2 | rA5 | rA5 | rA5 | rB1 | 0 | 0 | 0 | 0 1 1 | s_9 | 0 | o_lo | 0 1 0 0 1 |
| 2 | rA3 | rA3 | rA3 | rA2 | rA2 | rA2 | 1 | 0 | 0 | 1 0 1 | s_9 | −1 | o_lo | 0 0 1 0 0 |
| 3 | rA5 | rA5 | rA2 | rA3 | rA3 | rA3 | 0 | 0 | 0 | 0 0 1 | s_7 | 0 | o_lo | 0 0 0 0 0 |
| 4 | rB1 | rB1 | rB1 | rB4 | rB4 | rB4 | 2 | 0 | 0 | 1 1 0 | s_9 | −1 | o_lo | 0 0 1 0 0 |
| 5 | rB4 | rB4 | rB4 | rB1 | rB1 | rA5 | 0 | 0 | 0 | 0 1 0 | s_7 | 0 | o_lo | 0 0 0 0 0 |
| 6 | rC6 | rC6 | rC6 | rC6 | rC6 | rC6 | 0 | 0 | 0 | 1 0 0 | s_9 | −1 | o_lo | 0 0 0 0 0 |
| 7 | rC7 | rC7 | rC7 | rC7 | rC7 | rC7 | 0 | 0 | 0 | 0 0 0 | — | 0 | — | 0 0 0 0 0 |

Reading it by column group: state 0 with `r_S`, `s` and `w` satisfies §7;
state 5 with `r_O` and `o` satisfies §6; each adjacent state pair with its
`sw` column satisfies §8; and row 7 — the exempt padding row — carries no
transition witnesses.

---

## 10. Reviewer's map

Where each piece lives:

| concern | file / symbol |
|---------|---------------|
| Column layout (all indices derived here) | [`uair.rs`](uair.rs) `NetLayout::new` |
| Constraint emission ①②③ | [`uair.rs`](uair.rs) `constrain_general` (O1–O6, S1–S9, N1–N3) |
| Witness builder (sort, pad, route, assemble) | [`uair.rs`](uair.rs) `build_uair_trace` |
| Public columns (verifier rebuilds) | [`uair.rs`](uair.rs) `public_int_columns` |
| Beneš topology and routing | [`benes.rs`](benes.rs) `stride_bit`, `num_layers`, `route`, `apply_layer` |
| Prove / verify entry points, proof (de)serialization | [`prover.rs`](prover.rs) |
| Concrete protocol parameters (field, codes, widths) | [`types.rs`](types.rs) |
| Positive and **negative (soundness)** tests | [`testcases.rs`](testcases.rs) |

What to verify at the constraint level:

- ① O1/O2 pin row 0's time to 0; O3–O6 form a complete 2-limb lexicographic
  strict increase (both selector cases sound, no exploitable branch).
- ② S3–S6 form the 10-limb lexicographic strict increase;
  `a_same = s_8 + s_9` is a faithful same-address flag; S1/S9 force
  writes before reads; S7/S8 pin reads to the previous value over **all 8**
  value limbs.
- ③ N1 makes the switch boolean; N2/N3 are the exact conditional swap over
  **all 21** payload cells; the mask anchors each box exactly once at its
  top row; the wiring (stride, `upper_k`) is public and data-independent.
- The negative tests in [`testcases.rs`](testcases.rs) tamper with slacks,
  selectors, switch bits and both trace orderings — confirm each makes
  proving or verification fail. They are the empirical counterpart of the
  soundness arguments above.

Known limitations (see [`README.md`](README.md) for the full discussion):

- **No zero-knowledge** — the proof may reveal the entire trace.
- **Unaudited upstream** — pinned to one reviewed revision, research-default
  parameters.
- **`MAX_NUM_VARS = 16`** (at most 65 535 records) — the verifier pays
  `O(2^{v−1})` field operations per large-stride shifted column; beyond this
  the permutation argument should migrate to a future lookup layer.
