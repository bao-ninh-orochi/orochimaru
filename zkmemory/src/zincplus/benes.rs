//! Beneš-network routing for the deterministic permutation argument.
//!
//! A Beneš network on `2^v` wires consists of `2v - 1` layers of 2×2
//! conditional-swap switches arranged in a butterfly + inverse-butterfly
//! pattern and can realize *every* permutation of its inputs. The
//! memory-consistency UAIR ([`super::uair`]) lays the network out
//! horizontally — one trace row per wire, one column group per network
//! state — and constrains each layer with boolean-selected swap equations,
//! which proves that the sorted trace is an exact permutation of the
//! original (time-ordered) trace without any random challenge.
//!
//! This module contains the *prover-side* routing: computing switch
//! settings that realize a given permutation. Routing only affects
//! completeness — the UAIR constraints enforce that the committed states
//! form *some* permutation regardless of how the switches are set — so a
//! routing bug here can only make honest proving fail, never admit a false
//! statement.
//!
//! # Topology
//!
//! For `v ≥ 1`, layer `ℓ ∈ [0, 2v - 1)` pairs wire `i` with wire
//! `i + 2^{k_ℓ}` for every `i` whose bit `k_ℓ` is zero (the *upper* wire of
//! the switch), where
//!
//! ```text
//! k_ℓ = v - 1 - ℓ   for ℓ < v      (butterfly half)
//! k_ℓ = ℓ - v + 1   for ℓ ≥ v      (inverse-butterfly half)
//! ```
//!
//! i.e. the stride-bit sequence is `v-1, v-2, …, 1, 0, 1, …, v-1`. A switch
//! bit of `1` swaps the pair, `0` passes it through.
//!
//! The recursive structure: the outermost entry layer (`k = v-1`) splits
//! the wires into a *top* sub-network (wires with bit `v-1` = 0) and a
//! *bottom* sub-network (bit `v-1` = 1), each a Beneš network on `2^{v-1}`
//! wires; the outermost exit layer (`k = v-1` again) merges them. Because
//! sub-network wires share their fixed high bit, pairing by lower bits
//! never crosses sub-networks.

extern crate alloc;
use alloc::{vec, vec::Vec};

/// The stride-bit index `k_ℓ` of layer `ℓ` in a Beneš network on `2^v`
/// wires (see the module documentation).
///
/// # Panics
///
/// Panics when `v == 0` or `layer >= 2v - 1`; both indicate an internal
/// logic error in the caller.
pub(crate) fn stride_bit(v: usize, layer: usize) -> usize {
    assert!(v >= 1, "a Beneš network needs at least 2 wires");
    assert!(layer < 2 * v - 1, "layer {layer} out of range for v = {v}");
    if layer < v {
        v - 1 - layer
    } else {
        layer - v + 1
    }
}

/// Number of layers of a Beneš network on `2^v` wires.
pub(crate) fn num_layers(v: usize) -> usize {
    assert!(v >= 1, "a Beneš network needs at least 2 wires");
    2 * v - 1
}

/// Compute switch settings realizing `perm` on a Beneš network with
/// `perm.len() = 2^v` wires: after applying all layers to an input vector
/// `in`, the output satisfies `out[j] = in[perm[j]]`.
///
/// Returns one `Vec<bool>` per layer, indexed by wire; only the entries at
/// upper wires (bit `k_ℓ` clear) are meaningful, the rest stay `false`.
///
/// # Panics
///
/// Panics when `perm.len()` is not a power of two `≥ 2` or `perm` is not a
/// permutation of `0..perm.len()`; the caller (the witness builder)
/// guarantees both.
pub(crate) fn route(perm: &[usize]) -> Vec<Vec<bool>> {
    let n = perm.len();
    assert!(n >= 2 && n.is_power_of_two(), "wire count must be 2^v ≥ 2");
    let v = n.trailing_zeros() as usize;
    {
        let mut seen = vec![false; n];
        for &p in perm {
            assert!(p < n && !seen[p], "input is not a permutation");
            seen[p] = true;
        }
    }
    let mut layers = vec![vec![false; n]; num_layers(v)];
    route_block(perm, 0, 0, v, &mut layers);
    layers
}

/// Route one recursion block.
///
/// * `perm`: block-relative permutation (`out[j] = in[perm[j]]` within the
///   block).
/// * `base`: first wire of the block in absolute wire indices.
/// * `depth`: recursion depth; the block's entry layer is layer `depth` and
///   its exit layer is layer `2v - 2 - depth`.
/// * `v`: overall network size exponent.
fn route_block(perm: &[usize], base: usize, depth: usize, v: usize, layers: &mut [Vec<bool>]) {
    let m = perm.len();
    debug_assert!(m.is_power_of_two() && m >= 2);
    if m == 2 {
        // Base case: the middle layer (`k = 0`) with a single switch.
        let middle = v - 1;
        debug_assert_eq!(depth, middle, "middle block at wrong depth");
        layers[middle][base] = perm[0] == 1;
        return;
    }
    let h = m / 2;

    // 2-color the block inputs: color 0 routes through the top sub-network,
    // color 1 through the bottom. Constraints: entry pair mates (i, i+h)
    // get different colors, and exit pair mates (perm[j], perm[j+h]) get
    // different colors. The constraint graph is 2-regular (every input has
    // exactly one entry mate and one exit mate), i.e. a disjoint union of
    // even cycles, so greedy alternating walks 2-color it.
    let mut inv = vec![0usize; m];
    for (j, &i) in perm.iter().enumerate() {
        inv[i] = j;
    }
    let entry_mate = |i: usize| (i + h) % m;
    // The exit mate of input i: the input delivered to the exit-pair
    // partner of i's destination.
    let exit_mate = |i: usize| perm[(inv[i] + h) % m];

    let mut color = vec![u8::MAX; m];
    for start in 0..m {
        if color[start] != u8::MAX {
            continue;
        }
        // Walk the cycle through `start`, alternating colors and edge kinds
        // (entry mate must differ, exit mate must differ).
        let mut i = start;
        let mut c = 0u8;
        let mut via_entry = true;
        loop {
            color[i] = c;
            let next = if via_entry {
                entry_mate(i)
            } else {
                exit_mate(i)
            };
            via_entry = !via_entry;
            c ^= 1;
            if next == start {
                break;
            }
            debug_assert_eq!(color[next], u8::MAX, "coloring conflict");
            i = next;
        }
    }

    // Entry layer: upper wire a holds input a; switch bit 1 sends it to
    // the bottom sub-network (position a + h).
    let entry_layer = depth;
    for a in 0..h {
        layers[entry_layer][base + a] = color[a] == 1;
        debug_assert_ne!(color[a], color[a + h], "entry mates share a color");
    }

    // Exit layer: output j takes the bottom sub-network's wire j exactly
    // when its source input was colored bottom.
    let exit_layer = 2 * v - 2 - depth;
    for j in 0..h {
        layers[exit_layer][base + j] = color[perm[j]] == 1;
        debug_assert_ne!(
            color[perm[j]],
            color[perm[j + h]],
            "exit mates share a color"
        );
    }

    // Sub-permutations. Input i sits at sub-network position `i mod h` of
    // the sub-network chosen by its color; output j is fed from sub-network
    // position `j` (of the sub-network chosen by color[perm[j]]).
    let mut perm_top = vec![0usize; h];
    let mut perm_bot = vec![0usize; h];
    for j in 0..h {
        let (i0, i1) = (perm[j], perm[j + h]);
        let (top_src, bot_src) = if color[i0] == 0 { (i0, i1) } else { (i1, i0) };
        perm_top[j] = top_src % h;
        perm_bot[j] = bot_src % h;
    }
    route_block(&perm_top, base, depth + 1, v, layers);
    route_block(&perm_bot, base + h, depth + 1, v, layers);
}

/// Apply one network layer to a state vector, in place.
///
/// Generic over the wire payload so the witness builder can push whole
/// limb-decomposed records through the network.
pub(crate) fn apply_layer<T: Clone>(state: &mut [T], v: usize, layer: usize, bits: &[bool]) {
    let n = state.len();
    debug_assert_eq!(n, 1usize << v);
    debug_assert_eq!(bits.len(), n);
    let stride = 1usize << stride_bit(v, layer);
    for (i, &bit) in bits.iter().enumerate() {
        if i & stride == 0 && bit {
            state.swap(i, i + stride);
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use rand::{seq::SliceRandom, thread_rng};

    /// Simulate the full network on the identity input and return the
    /// output vector; `out[j]` must equal `perm[j]`.
    fn simulate(perm: &[usize]) -> Vec<usize> {
        let n = perm.len();
        let v = n.trailing_zeros() as usize;
        let layers = route(perm);
        let mut state: Vec<usize> = (0..n).collect();
        for (layer, bits) in layers.iter().enumerate() {
            apply_layer(&mut state, v, layer, bits);
        }
        state
    }

    fn check(perm: &[usize]) {
        assert_eq!(simulate(perm), perm, "network does not realize {perm:?}");
    }

    #[test]
    fn test_v1_both_permutations() {
        check(&[0, 1]);
        check(&[1, 0]);
    }

    #[test]
    fn test_v2_all_permutations() {
        // All 24 permutations of 4 wires.
        let mut perm = [0usize, 1, 2, 3];
        permute_all(&mut perm, 0);
    }

    fn permute_all(perm: &mut [usize; 4], k: usize) {
        if k == 4 {
            check(perm);
            return;
        }
        for i in k..4 {
            perm.swap(k, i);
            permute_all(perm, k + 1);
            perm.swap(k, i);
        }
    }

    #[test]
    fn test_identity_and_reversal() {
        for v in 1..=8 {
            let n = 1usize << v;
            let identity: Vec<usize> = (0..n).collect();
            let reversal: Vec<usize> = (0..n).rev().collect();
            check(&identity);
            check(&reversal);
        }
    }

    #[test]
    fn test_random_permutations() {
        let mut rng = thread_rng();
        for v in 1..=8 {
            let n = 1usize << v;
            for _ in 0..20 {
                let mut perm: Vec<usize> = (0..n).collect();
                perm.shuffle(&mut rng);
                check(&perm);
            }
        }
    }

    #[test]
    fn test_rotations() {
        // Cyclic shifts exercise long constraint-graph cycles.
        for v in 1..=7 {
            let n = 1usize << v;
            for s in 0..n {
                let perm: Vec<usize> = (0..n).map(|j| (j + s) % n).collect();
                check(&perm);
            }
        }
    }

    #[test]
    fn test_switch_bits_only_on_upper_wires() {
        let mut rng = thread_rng();
        let v = 5;
        let n = 1usize << v;
        let mut perm: Vec<usize> = (0..n).collect();
        perm.shuffle(&mut rng);
        let layers = route(&perm);
        assert_eq!(layers.len(), num_layers(v));
        for (layer, bits) in layers.iter().enumerate() {
            let stride = 1usize << stride_bit(v, layer);
            for (i, &bit) in bits.iter().enumerate() {
                if i & stride != 0 {
                    assert!(!bit, "switch bit set on lower wire {i} of layer {layer}");
                }
            }
        }
    }
}
