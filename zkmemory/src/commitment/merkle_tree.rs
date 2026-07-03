//! Circuit for proving the correctness of the Merkle tree commitment.

extern crate alloc;
use crate::commitment::commitment_scheme::CommitmentScheme;
use alloc::{format, vec, vec::Vec};
use core::marker::PhantomData;
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::pasta::{EqAffine, Fp},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Expression, Fixed, Instance, ProvingKey, Selector,
    },
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::{ProverIPA, VerifierIPA},
            strategy::SingleStrategy,
        },
        Rotation, VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use poseidon::circuit::PoseidonConfig;
use poseidon::gadgets::Hash as PoseidonHashChip;
use poseidon::poseidon_hash::{ConstantLength, Hash, OrchardNullifier, Spec};
use rand_core::OsRng;

#[derive(Clone, Debug)]
/// Merkle tree config
///
/// The correctness of each level's Poseidon hash is enforced *inside* the circuit
/// through an embedded [`PoseidonConfig`]. The running digest of a level is the
/// output cell of the in-circuit hash of the previous level, so a prover cannot
/// substitute a forged hash output (see issue #93).
pub struct MerkleTreeConfig<F: Field + PrimeField, const W: usize, const R: usize> {
    /// advice has 4 columns: `[digest, element, left, right]`.
    /// `digest` is the running digest coming up from the previous level,
    /// `element` is the sibling node of the current level, and `left`/`right`
    /// are the (possibly swapped) inputs of the Poseidon hash of this level.
    advice: [Column<Advice>; 4],
    /// the index bit of the current level (0 if the running digest is the left
    /// child, 1 if it is the right child).
    indices: Column<Advice>,
    /// the instance of the config, consisting of the leaf we would like to
    /// open, and the merkle root.
    pub instance: Column<Instance>,
    /// selector enabling the boolean + conditional-swap gate on every level row.
    selector: Selector,
    /// in-circuit Poseidon hash sub-configuration, used to actually constrain
    /// `output = poseidon(left, right)` for every level.
    poseidon_config: PoseidonConfig<F, W, R>,
}

impl<F: Field + PrimeField, const W: usize, const R: usize> MerkleTreeConfig<F, W, R> {
    fn configure<S: Spec<F, W, R>>(
        meta: &mut ConstraintSystem<F>,
        instance: Column<Instance>,
    ) -> Self {
        let advice = [0; 4].map(|_| meta.advice_column());
        let indices = meta.advice_column();
        let selector = meta.selector();
        for column in advice {
            meta.enable_equality(column);
        }

        let one = Expression::Constant(F::ONE);

        // For every level we constrain, in a single row:
        //   * the index bit is boolean,
        //   * `left`  = digest + bit * (element - digest),
        //   * `right` = element + bit * (digest - element).
        // i.e. (left, right) = (digest, element) when bit = 0, and the swapped
        // pair (element, digest) when bit = 1. This binds the hash inputs of the
        // level to the running digest and the sibling.
        meta.create_gate("boolean index bit and conditional swap", |meta| {
            let selector = meta.query_selector(selector);
            let digest = meta.query_advice(advice[0], Rotation::cur());
            let element = meta.query_advice(advice[1], Rotation::cur());
            let left = meta.query_advice(advice[2], Rotation::cur());
            let right = meta.query_advice(advice[3], Rotation::cur());
            let bit = meta.query_advice(indices, Rotation::cur());
            vec![
                selector.clone() * bit.clone() * (one.clone() - bit.clone()),
                selector.clone()
                    * (left - (digest.clone() + bit.clone() * (element.clone() - digest.clone()))),
                selector * (right - (element.clone() + bit * (digest - element))),
            ]
        });

        // Embed the in-circuit Poseidon hash configuration. Its gates enforce
        // that the squeezed output is the correct Poseidon hash of the absorbed
        // inputs, which is exactly the correctness property missing before.
        let state = (0..W)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>();
        let partial_sbox = meta.advice_column();
        let rc_a = (0..W)
            .map(|_| meta.fixed_column())
            .collect::<Vec<Column<Fixed>>>();
        let rc_b = (0..W)
            .map(|_| meta.fixed_column())
            .collect::<Vec<Column<Fixed>>>();
        meta.enable_constant(rc_b[0]);
        let poseidon_config = PoseidonConfig::<F, W, R>::configure::<S>(
            meta,
            state.try_into().expect("could not load poseidon state"),
            partial_sbox,
            rc_a.try_into().expect("could not load rc_a"),
            rc_b.try_into().expect("could not load rc_b"),
        );

        MerkleTreeConfig {
            advice,
            indices,
            instance,
            selector,
            poseidon_config,
        }
    }
}

#[derive(Default, Debug, Clone)]
/// Merkle tree circuit
pub struct MerkleTreeCircuit<
    S: Spec<F, W, R> + Clone,
    F: Field + PrimeField,
    const W: usize,
    const R: usize,
> {
    /// the leaf node we would like to open
    pub(crate) leaf: F,
    /// the values of the sibling nodes in the path
    pub(crate) elements: Vec<F>,
    /// the index of the path from the leaf to the merkle root
    pub(crate) indices: Vec<F>,
    _marker: PhantomData<S>,
}
impl<S: Spec<F, W, R> + Clone, F: Field + PrimeField, const W: usize, const R: usize> Circuit<F>
    for MerkleTreeCircuit<S, F, W, R>
{
    type Config = MerkleTreeConfig<F, W, R>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            leaf: F::ZERO,
            elements: vec![F::ZERO],
            indices: vec![F::ZERO],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        MerkleTreeConfig::<F, W, R>::configure::<S>(meta, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        assert_eq!(self.indices.len(), self.elements.len());

        // Load the leaf as the initial running digest and bind it to the first
        // public input.
        let mut digest = layouter.assign_region(
            || "load leaf",
            |mut region| {
                region.assign_advice(|| "leaf", config.advice[0], 0, || Value::known(self.leaf))
            },
        )?;
        layouter.constrain_instance(digest.cell(), config.instance, 0)?;

        // Walk up the tree. At each level we recompute the parent hash *inside*
        // the circuit and use its output cell as the new running digest, so a
        // prover cannot substitute a fake output.
        for i in 0..self.indices.len() {
            let index = self.indices[i];
            let element = self.elements[i];

            // Assign the swap row and derive the (left, right) inputs of the hash.
            let (left, right) = layouter.assign_region(
                || format!("merkle level {}", i),
                |mut region| {
                    config.selector.enable(&mut region, 0)?;

                    // Copy the running digest in; this constrains it to be equal
                    // to the previous level's hash output (or the leaf).
                    let digest_cell =
                        digest.copy_advice(|| "digest", &mut region, config.advice[0], 0)?;
                    let element_cell = region.assign_advice(
                        || "element",
                        config.advice[1],
                        0,
                        || Value::known(element),
                    )?;
                    region.assign_advice(|| "index", config.indices, 0, || Value::known(index))?;

                    // (left, right) = (digest, element) if bit == 0 else (element, digest).
                    let (left_val, right_val) = if index == F::ZERO {
                        (digest_cell.value().copied(), element_cell.value().copied())
                    } else {
                        (element_cell.value().copied(), digest_cell.value().copied())
                    };
                    let left =
                        region.assign_advice(|| "left input", config.advice[2], 0, || left_val)?;
                    let right = region.assign_advice(
                        || "right input",
                        config.advice[3],
                        0,
                        || right_val,
                    )?;
                    Ok((left, right))
                },
            )?;

            // Enforce digest = poseidon(left, right) with the in-circuit chip.
            let hasher = PoseidonHashChip::<F, S, ConstantLength<2>, W, R>::init(
                config.poseidon_config.clone(),
                layouter.namespace(|| format!("init poseidon {}", i)),
            )?;
            digest = hasher.hash(
                layouter.namespace(|| format!("poseidon hash {}", i)),
                [left, right],
            )?;
        }

        // The final running digest is the Merkle root; bind it to the second
        // public input.
        layouter.constrain_instance(digest.cell(), config.instance, 1)?;
        Ok(())
    }
}

#[derive(Clone)]
/// Witness for the Merkle tree
pub struct MerkleWitness {
    /// The leaf node
    pub leaf: u64,
    /// The elements in the path
    pub elements: Vec<u64>,
    /// The indices of the path
    pub indices: Vec<u64>,
}

impl MerkleWitness {
    /// Create a new Merkle witness
    pub fn new<T: AsRef<[u64]>>(leaf: u64, elements: T, indices: T) -> Self {
        Self {
            leaf,
            elements: elements.as_ref().to_vec(),
            indices: indices.as_ref().to_vec(),
        }
    }

    /// Convert to circuit-compatible format
    pub fn to_circuit_format<F: PrimeField>(&self) -> (F, Vec<F>, Vec<F>) {
        (
            F::from(self.leaf),
            self.elements.iter().map(|&x| F::from(x)).collect(),
            self.indices.iter().map(|&x| F::from(x)).collect(),
        )
    }
}

/// Prover for the Merkle tree
pub struct MerkleTreeProver {
    params: ParamsIPA<EqAffine>,
    pk: ProvingKey<EqAffine>,
    witness: MerkleWitness,
    circuit: MerkleTreeCircuit<OrchardNullifier, Fp, 3, 2>,
}

impl MerkleTreeProver {
    /// Initialize the parameters for the prover
    pub fn new(k: u32, witness: MerkleWitness) -> Self {
        let params = ParamsIPA::<EqAffine>::new(k);
        let (leaf, elements, indices) = witness.to_circuit_format::<Fp>();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf,
            elements,
            indices,
            _marker: PhantomData,
        };
        let vk = keygen_vk(&params, &circuit).expect("Cannot initialize verify key");
        let pk = keygen_pk(&params, vk, &circuit).expect("Cannot initialize proving key");
        Self {
            params,
            pk,
            witness,
            circuit,
        }
    }

    /// Create proof for the Merkle tree circuit
    pub fn create_proof(&self) -> Vec<u8> {
        let mut transcript =
            Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<EqAffine>>::init(vec![]);

        let public_inputs = [
            self.circuit.leaf,
            merkle_tree_commit_fp(
                &self.witness.leaf,
                &self.witness.elements,
                &self.witness.indices,
            ),
        ];

        create_proof::<
            IPACommitmentScheme<EqAffine>,
            ProverIPA<'_, EqAffine>,
            Challenge255<EqAffine>,
            OsRng,
            Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>,
            MerkleTreeCircuit<OrchardNullifier, Fp, 3, 2>,
        >(
            &self.params,
            &self.pk,
            core::slice::from_ref(&self.circuit),
            &[&[&public_inputs[..]]],
            OsRng,
            &mut transcript,
        )
        .expect("Failed to create proof");

        transcript.finalize()
    }

    /// Verify the proof
    pub fn verify(&self, proof: Vec<u8>, public_inputs: Vec<Fp>) -> bool {
        let strategy = SingleStrategy::new(&self.params);
        let mut transcript =
            Blake2bRead::<&[u8], EqAffine, Challenge255<EqAffine>>::init(&proof[..]);

        verify_proof::<
            IPACommitmentScheme<EqAffine>,
            VerifierIPA<'_, EqAffine>,
            Challenge255<EqAffine>,
            Blake2bRead<&[u8], EqAffine, Challenge255<EqAffine>>,
            SingleStrategy<'_, EqAffine>,
        >(
            &self.params,
            self.pk.get_vk(),
            strategy,
            &[&[&public_inputs[..]]],
            &mut transcript,
        )
        .is_ok()
    }
}

/// Compute the root of a merkle tree given the path and the sibling nodes
pub fn merkle_tree_commit_fp(leaf: &u64, elements: &[u64], indices: &[u64]) -> Fp {
    let k = elements.len();
    let mut digest = Fp::from(*leaf);
    let mut message: [Fp; 2];
    for i in 0..k {
        if indices[i] == 0 {
            message = [digest, Fp::from(elements[i])];
        } else {
            message = [Fp::from(elements[i]), digest];
        }
        digest = Hash::<Fp, OrchardNullifier, ConstantLength<2>, 3, 2>::init().hash(message);
    }
    digest
}

impl<S: Spec<Fp, W, R> + Clone, const W: usize, const R: usize> CommitmentScheme<Fp>
    for MerkleTreeCircuit<S, Fp, W, R>
{
    type Commitment = Fp;
    type Opening = Vec<u64>;
    type Witness = MerkleWitness;
    type PublicParams = ();

    fn setup(_k: Option<u32>) -> Self {
        Self {
            leaf: Fp::ZERO,
            elements: vec![Fp::ZERO],
            indices: vec![Fp::ZERO],
            _marker: PhantomData,
        }
    }

    fn commit(&self, witness: Self::Witness) -> Self::Commitment {
        merkle_tree_commit_fp(&witness.leaf, &witness.elements, &witness.indices)
    }

    fn open(&self, witness: Self::Witness) -> Self::Opening {
        witness.elements
    }

    fn verify(
        &self,
        commitment: Self::Commitment,
        opening: Self::Opening,
        witness: Self::Witness,
    ) -> bool {
        opening == witness.elements
            && commitment == merkle_tree_commit_fp(&witness.leaf, &opening, &witness.indices)
    }
}

#[cfg(test)]
mod tests {
    extern crate alloc;
    use super::MerkleTreeCircuit;
    use crate::commitment::commitment_scheme::CommitmentScheme;
    use crate::commitment::merkle_tree::{
        merkle_tree_commit_fp, MerkleTreeConfig, MerkleTreeProver, MerkleWitness,
    };
    use alloc::{vec, vec::Vec};
    use core::marker::PhantomData;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::pasta::{EqAffine, Fp},
        plonk::{create_proof, Circuit, ConstraintSystem, Error},
        poly::ipa::{commitment::IPACommitmentScheme, multiopen::ProverIPA},
        transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
    };
    use poseidon::poseidon_hash::*;
    use rand::{thread_rng, Rng};
    use rand_core::{OsRng, RngCore};

    #[test]
    fn test_correct_merkle_proof() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let root = merkle_tree_commit_fp(&leaf, &elements, &indices);
        let leaf_fp = Fp::from(leaf);
        let indices = indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_correct_merkle_proof_part2() {
        let mut rng = thread_rng();
        let leaf = rng.next_u64();
        let k = 10;
        let indices = [
            rng.gen_range(0..2),
            rng.gen_range(0..2),
            rng.gen_range(0..2),
            rng.gen_range(0..2),
            rng.gen_range(0..2),
        ];
        let elements = [
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ];
        let root = merkle_tree_commit_fp(&leaf, &elements, &indices);
        let leaf_fp = Fp::from(leaf);
        let indices = indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_merkle_proof_real_prover() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let witness = MerkleWitness::new(leaf, elements, indices);
        let prover = MerkleTreeProver::new(k, witness.clone());
        let proof = prover.create_proof();
        let root = prover.circuit.commit(witness.clone());
        let public_inputs = vec![Fp::from(leaf), root];
        let is_valid = prover.verify(proof, public_inputs);
        assert!(is_valid, "Merkle proof verification failed");
    }

    #[test]
    fn test_wrong_merkle_proof() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let root = Fp::from(0);
        let leaf_fp = Fp::from(leaf);
        let indices = indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_ne!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_wrong_merkle_part2() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let root = merkle_tree_commit_fp(&leaf, &elements, &indices);
        let false_indices = [1u64, 0u64, 1u64, 1u64];
        let leaf_fp = Fp::from(leaf);
        let false_indices = false_indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices: false_indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_ne!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_invalid_indices() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 2u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let root = Fp::from(0);
        let leaf_fp = Fp::from(leaf);
        let indices = indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_ne!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_invalid_indices_part2() {
        let leaf = 0u64;
        let k = 10;
        let indices = [2u64, 1u64, 3u64, 4u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let root = Fp::from(0);
        let leaf_fp = Fp::from(leaf);
        let indices = indices.iter().map(|x| Fp::from(*x)).collect();
        let elements = elements.iter().map(|x| Fp::from(*x)).collect();
        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2> {
            leaf: leaf_fp,
            indices,
            elements,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(leaf), root]])
            .expect("Cannot run the circuit");
        assert_ne!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_correct_merkle_proof_commitment_scheme_trait() {
        let leaf = 0u64;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        let witness = MerkleWitness::new(leaf, elements, indices);

        let circuit = MerkleTreeCircuit::<OrchardNullifier, Fp, 3, 2>::setup(None);
        let commitment = circuit.commit(witness.clone());
        let opening = circuit.open(witness.clone());
        let is_valid = circuit.verify(commitment, opening, witness);

        assert!(is_valid, "Verification should succeed for valid opening");
    }

    /// A circuit reproducing the attack from issue #93: it reuses the exact
    /// same constraint system as [`MerkleTreeCircuit`] but its `synthesize`
    /// ignores the Poseidon hash chain and constrains an arbitrary, forged root
    /// to the public instance. With the hash correctness now enforced inside the
    /// verifying key, a proof produced by this circuit (using the honest proving
    /// key) must be rejected by the verifier.
    #[derive(Clone)]
    struct FakeMerkleTreeCircuit {
        leaf: Fp,
        fake_root: Fp,
    }

    impl Circuit<Fp> for FakeMerkleTreeCircuit {
        type Config = MerkleTreeConfig<Fp, 3, 2>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            self.clone()
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            MerkleTreeConfig::<Fp, 3, 2>::configure::<OrchardNullifier>(meta, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let leaf_cell = layouter.assign_region(
                || "leaf",
                |mut region| {
                    region.assign_advice(|| "leaf", config.advice[0], 0, || Value::known(self.leaf))
                },
            )?;
            layouter.constrain_instance(leaf_cell.cell(), config.instance, 0)?;

            // Directly constrain a forged root to the public instance, without
            // ever computing a Poseidon hash.
            let root_cell = layouter.assign_region(
                || "fake root",
                |mut region| {
                    region.assign_advice(
                        || "fake root",
                        config.advice[0],
                        0,
                        || Value::known(self.fake_root),
                    )
                },
            )?;
            layouter.constrain_instance(root_cell.cell(), config.instance, 1)?;
            Ok(())
        }
    }

    #[test]
    fn test_fake_merkle_proof_is_rejected() {
        let leaf = 0u64;
        let k = 10;
        let indices = [0u64, 0u64, 1u64, 1u64];
        let elements = [3u64, 4u64, 5u64, 6u64];
        // The forged root the attacker wants the verifier to accept.
        let fake_root = Fp::from(42u64);

        // Honest setup: build the proving key from the real MerkleTreeCircuit.
        let witness = MerkleWitness::new(leaf, elements, indices);
        let prover = MerkleTreeProver::new(k, witness);

        // Attacker forges a proof for `fake_root` reusing the honest proving key.
        let fake_circuit = FakeMerkleTreeCircuit {
            leaf: Fp::from(leaf),
            fake_root,
        };
        let public_inputs = [Fp::from(leaf), fake_root];
        let mut transcript =
            Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<EqAffine>>::init(vec![]);
        create_proof::<
            IPACommitmentScheme<EqAffine>,
            ProverIPA<'_, EqAffine>,
            Challenge255<EqAffine>,
            OsRng,
            Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>,
            FakeMerkleTreeCircuit,
        >(
            &prover.params,
            &prover.pk,
            &[fake_circuit],
            &[&[&public_inputs[..]]],
            OsRng,
            &mut transcript,
        )
        .expect("Failed to create fake proof");
        let fake_proof = transcript.finalize();

        let is_valid = prover.verify(fake_proof, public_inputs.to_vec());
        assert!(!is_valid, "Fake merkle proof must be rejected");
    }
}
