# Zinc+ memory-consistency backend

This module integrates [Zinc+](https://github.com/NethermindEth/zinc-plus)
(NethermindEth) as an **optional proof-system backend** for zkMemory's
memory-consistency argument, alongside the existing Halo2 (PLONK) circuits in
[`src/constraints`](../constraints). It is gated behind the `zinc` cargo
feature and follows the multi-backend layout established by
[`src/nova`](../nova) and [`src/supernova`](../supernova).

```text
zkmemory/src/zincplus/
├── mod.rs        module root, public re-exports
├── types.rs      concrete Zinc+ protocol type parameters (field, codes, widths)
├── uair.rs       the memory-consistency UAIR + witness builder
├── prover.rs     prove / verify entry points, proof (de)serialization, errors
├── testcases.rs  positive and negative (soundness) tests
└── README.md     this file
```

## Quick start

```rust
use zkmemory::zincplus::{prove_memory_consistency, verify_memory_consistency};

let trace = machine.trace();                    // time-ordered execution trace
let proof = prove_memory_consistency(&trace)?;  // succinct, transparent SNARK
verify_memory_consistency(&proof)?;
let bytes = proof.to_bytes()?;                  // transferable proof bytes
```

Or through the backend-agnostic seam, which lets code switch between Halo2
and Zinc+ without changing how traces are produced:

```rust
use zkmemory::backend::{Halo2Backend, MemoryConsistencyBackend, ZincPlusBackend};

let halo2 = Halo2Backend { k: 10 };
halo2.verify(&halo2.prove(&trace)?)?;

let zinc = ZincPlusBackend;
zinc.verify(&zinc.prove(&trace)?)?;
```

Build with `cargo build -p zkmemory --features zinc`. The feature requires a
`std` environment and Rust ≥ 1.85 (Zinc+ is an edition-2024 workspace); the
repository toolchain is pinned accordingly in [`rust-toolchain`](../../../rust-toolchain).

## What Zinc+ is

Zinc+ ([eprint 2026/855](https://eprint.iacr.org/2026/855)) is a
**transparent, plausibly post-quantum SNARK for polynomial rings**. Instead
of embedding all constraints into one prime field, it expresses them over
`Q[X]`, `Z[X]` and several `F_q[X]` rings simultaneously, avoiding the
witness inflation of single-field SNARKs. Constraints are written in a
univariate-AIR (UAIR) dialect: per-row expressions over three column kinds
(binary polynomials, arbitrary polynomials, integers) with fixed row shifts
for transition constraints, compiled down to sumchecks and the Brakedown-style
Zip+ polynomial commitment scheme (Merkle trees + linear codes). There is
**no trusted setup**; all challenges — including the random ~192-bit prime
modulus the constraints are projected into — derive from a Blake3
Fiat-Shamir transcript.

## The statement proven

The prover commits to a memory trace of `2^num_vars − 1` rows (the machine's
records sorted by `(address, time_log)`, followed by benign padding rows) and
proves, for every pair of adjacent rows:

| # | constraint | meaning |
|---|-----------|---------|
| 1 | `is_first · (instr − 1) = 0` | the first access of the trace is a write |
| 2 | `instr' · (instr' − 1) = 0` | instructions are boolean (0 = read, 1 = write) |
| 3 | `s_j · (s_j − 1) = 0` | first-difference selectors are boolean |
| 4 | `Σ_j s_j = 1` | exactly one first-difference position |
| 5 | `(1 − Σ_{l≤j} s_l) · (L'_j − L_j) = 0` | limbs before the first difference are equal |
| 6 | `Σ_j s_j·(L'_j − L_j) − 1 − r ∈ (X − 2)` | the first differing limb strictly increases |
| 7 | `w = (s_8 + s_9) · (instr' − 1)` | helper: `w = −1` iff *read at unchanged address* |
| 8 | `w · (value'_j − value_j) = 0` | a read returns the previous value at that address |
| 9 | `(1 − s_8 − s_9) · (instr' − 1) = 0` | the first access to a new address is a write |

where `L_0..L_9` is the lexicographic limb vector `address ‖ time_log`
(32-bit limbs, most significant first) and primes denote the next row.
Constraints 3–6 together are a lookup-free strict lexicographic comparison:
`s` selects the first differing limb, everything before it must be equal, and
the selected limb must grow by `1 + r` where `r` is a committed 32-bit value.
These are semantically the same constraints as the Halo2
`SortedMemoryCircuit` (`src/constraints/sorted_memory_circuit.rs`).

Addresses, values and `time_log`s live in *binary polynomial* columns:
`BinaryPoly<32>` cells whose 32 coefficients are proven boolean by Zinc+'s
built-in booleanity argument, so every limb is range-checked to `u32` for
free — no lookup tables are needed anywhere.

Zinc+ exempts the very last row from constraints (its built-in last-row
selector); the witness builder therefore always keeps at least one padding
row, so **no real record ever occupies the exempt row**. Padding rows replay
the last record as reads with increasing `time_log`s, which satisfies every
constraint.

The only public input is the `is_first` column (`[1, 0, 0, …]`), which the
verifier reconstructs itself; it is absorbed into the Fiat-Shamir transcript
by the protocol before any challenge is drawn.

## Security status — differences from the Halo2 backend

Users must understand three deliberate limitations of this v1 integration:

1. **No zero-knowledge.** Zinc+ currently provides succinctness and
   transparency but no hiding: witness columns are committed and opened
   without masking. Treat the proof as potentially revealing the entire
   trace. Use the Halo2 backend when privacy is required.

2. **No in-SNARK permutation link.** The Halo2 circuit additionally proves
   that the sorted trace is a *permutation* of a time-ordered original trace
   (via PLONK's shuffle argument) and that the original trace's `time_log`s
   start at zero and strictly increase. Zinc+ has no permutation or lookup
   argument yet (upstream's lookup layer is scaffolded but explicitly
   unimplemented), so those two sub-statements are **not** enforced here.
   Note that the composed Halo2 circuit has *zero public inputs* — both
   traces are witnesses — so its externally visible statement is "the prover
   knows a consistent trace", which the Zinc+ backend also delivers. The gap
   matters once the memory argument must be *linked to an execution proof*
   (a zkVM composing CPU and memory arguments): that linkage needs the
   permutation argument and awaits upstream support.

3. **Research-grade upstream.** Zinc+ is unaudited and marked by its authors
   as for research/educational use. The dependency is pinned to one reviewed
   revision (see `[workspace.dependencies]`), and the security parameters in
   [`types.rs`](types.rs) (repetition factor 8, 100 column openings, 192-bit
   sampled prime) are the upstream research defaults, not audited production
   parameters.

Within those boundaries the encoding itself is designed to be sound; the
constraint-by-constraint argument is documented in [`uair.rs`](uair.rs)
(module docs, "Constraint soundness sketch") and exercised by negative tests
in [`testcases.rs`](testcases.rs) (stale reads, reads of unwritten
addresses, first-access reads, tampered/truncated proofs, duplicated
`time_log`s).

## Migration plan (tracking upstream Zinc+ maturity)

This integration deliberately isolates everything Zinc+-specific behind
`zkmemory::backend::MemoryConsistencyBackend` and this module, so upstream
progress can be adopted incrementally:

- **When Zinc+ gains zero-knowledge** (witness masking): bump the pinned
  revision, enable the hiding mode in `types.rs`/`prover.rs`; the UAIR and
  the public API stay unchanged.
- **When Zinc+ lands its lookup/LogUp layer**: add the permutation link —
  commit the time-ordered trace next to the sorted one and prove multiset
  equality plus the original-trace time ordering (`time[0] = 0`,
  `time[i+1] > time[i]`), reaching full parity with the Halo2 statement.
  The column layout in `uair.rs` was chosen so the original-trace columns
  can be appended without disturbing the existing indices.
- **When upstream publishes audited parameters**: update `types.rs`
  accordingly (`REP_FACTOR`, `NUM_COLUMN_OPENINGS`, field size).
- **Halo2 parity work in the other direction**: the Halo2 backend currently
  checks the composed circuit with `MockProver` only (the crate has a real
  prover just for the permutation sub-circuit); giving it a real
  transferable proof artifact would make the two backends fully
  interchangeable behind the trait.

## Performance notes

Proving is dominated by the Zip+ commitments over `2^num_vars` rows and
32 committed columns. The trace is padded to the next power of two (minimum
8 rows, maximum `2^24`); proving a few hundred records takes on the order of
seconds in release mode on commodity hardware, and verification is
milliseconds. Proof size is where the trade-off shows: linear-code
commitments have large constants (the 8-record example proof is ≈560 KiB —
"succinct" asymptotically, far bigger than a pairing-based SNARK proof).
The upstream `parallel` (rayon) and `simd` features can be forwarded later
if throughput becomes a concern.
