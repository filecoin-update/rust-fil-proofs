use std::marker::PhantomData;

use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        multipack::pack_bits,
        num::AllocatedNum,
        sha256::sha256 as sha256_circuit,
        uint32::UInt32,
    },
    ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use filecoin_hashers::{poseidon::PoseidonHasher, sha256::Sha256Hasher, Hasher, R1CSHasher};
use generic_array::typenum::{U0, U2, U4, U8};
use nova_snark::{
    errors::NovaError,
    traits::circuit::{StepCircuit, TrivialTestCircuit},
    RecursiveSNARK,
};
use storage_proofs_core::{
    drgraph::BASE_DEGREE as DRG_PARENTS,
    gadgets::{encode::encode, por::por_no_challenge_input},
    merkle::{BinaryMerkleTree, LCTree, MerkleProofTrait, MerkleTreeTrait},
    nova::{self, NovaField},
    util::reverse_bit_numbering,
    SECTOR_NODES_16_KIB, SECTOR_NODES_16_MIB, SECTOR_NODES_1_KIB, SECTOR_NODES_2_KIB,
    SECTOR_NODES_32_GIB, SECTOR_NODES_32_KIB, SECTOR_NODES_4_KIB, SECTOR_NODES_512_MIB,
    SECTOR_NODES_64_GIB, SECTOR_NODES_8_KIB, SECTOR_NODES_8_MIB,
};

use crate::stacked::{
    circuit::hash_single_column,
    vanilla::{self, TOTAL_PARENTS as REPEATED_PARENTS},
    EXP_DEGREE as EXP_PARENTS,
};

pub const TOTAL_PARENTS: usize = DRG_PARENTS + EXP_PARENTS;

#[derive(Clone)]
pub struct CircuitConfig {
    pub sector_nodes: usize,
    pub base_arity: usize,
    pub sub_arity: usize,
    pub top_arity: usize,
    pub num_layers: usize,
    pub total_challenge_count: usize,
    pub challenges_per_step: usize,
}

impl CircuitConfig {
    pub fn new(
        sector_nodes: usize,
        num_layers: usize,
        total_challenge_count: usize,
        challenges_per_step: usize,
    ) -> Self {
        assert_eq!(total_challenge_count % challenges_per_step, 0);
        let (base_arity, sub_arity, top_arity) = match sector_nodes {
            SECTOR_NODES_1_KIB => (8, 4, 0),
            SECTOR_NODES_2_KIB => (8, 0, 0),
            SECTOR_NODES_4_KIB => (8, 2, 0),
            SECTOR_NODES_8_KIB => (8, 4, 0),
            SECTOR_NODES_16_KIB => (8, 8, 0),
            SECTOR_NODES_32_KIB => (8, 8, 2),
            SECTOR_NODES_8_MIB => (8, 0, 0),
            SECTOR_NODES_16_MIB => (8, 2, 0),
            SECTOR_NODES_512_MIB => (8, 0, 0),
            SECTOR_NODES_32_GIB => (8, 8, 0),
            SECTOR_NODES_64_GIB => (8, 8, 2),
            _ => unimplemented!(),
        };
        CircuitConfig {
            sector_nodes,
            num_layers,
            base_arity,
            sub_arity,
            top_arity,
            total_challenge_count,
            challenges_per_step,
        }
    }

    pub fn max_challenges_per_step(
        sector_nodes: usize,
        num_layers: usize,
        total_challenge_count: usize,
    ) -> Self {
        // 7 is the maxiumum number of 32-bit integers that can be packed into a 255-bit field element.
        let max_challenges_per_step = 7;

        // If we are using a test sector size, prove once challenge per step.
        let challenges_per_step = if total_challenge_count < max_challenges_per_step {
            total_challenge_count
        } else {
            // Get GCD of `total_challenge_count` that is less than or equal to 7.
            let mut challenges_per_step = max_challenges_per_step;
            while total_challenge_count % challenges_per_step != 0 {
                challenges_per_step -= 1;
            }
            challenges_per_step
        };

        CircuitConfig::new(
            sector_nodes,
            num_layers,
            total_challenge_count,
            challenges_per_step,
        )
    }

    pub fn num_steps(&self) -> usize {
        assert_eq!(self.total_challenge_count % self.challenges_per_step, 0);
        self.total_challenge_count / self.challenges_per_step
    }
}

#[derive(Clone)]
pub struct PublicInputs<F: NovaField> {
    pub replica_id: Option<F>,
    pub comm_d: Option<F>,
    pub comm_r: Option<F>,
    // All porep challenges.
    pub challenges: Vec<Option<u32>>,
    pub parents: Vec<Vec<Option<u32>>>,
}

impl<F: NovaField> PublicInputs<F> {
    pub fn blank(config: &CircuitConfig) -> Self {
        PublicInputs {
            replica_id: None,
            comm_d: None,
            comm_r: None,
            challenges: vec![None; config.total_challenge_count],
            parents: vec![vec![None; TOTAL_PARENTS]; config.total_challenge_count],
        }
    }

    pub fn z0(&self, config: &CircuitConfig) -> Vec<F> {
        assert_eq!(self.challenges.len(), config.total_challenge_count);
        assert_eq!(self.parents.len(), config.total_challenge_count);
        assert!(self
            .parents
            .iter()
            .all(|parents| parents.len() == TOTAL_PARENTS));
        assert_eq!(config.total_challenge_count % config.challenges_per_step, 0);

        let challenge_bit_len = config.sector_nodes.trailing_zeros() as usize;
        let num_challenge_inputs = config.num_steps();
        let num_parent_inputs = 2 * config.total_challenge_count;

        // 3 public inpus for `replica_id, comm_d, comm_r`.
        let num_inputs = 3 + num_challenge_inputs + num_parent_inputs;

        let mut z0 = Vec::<F>::with_capacity(num_inputs);
        z0.push(self.replica_id.expect("replica_id not set"));
        z0.push(self.comm_d.expect("comm_d not set"));
        z0.push(self.comm_r.expect("comm_r not set"));

        // For each step: append the step's packed challenges and each of those challenges' packed
        // parents; parents are packed 7 at a time as 7 is the maximum number of u32s that can be
        // packed into a 255-bit field element, coincedentally `TOTAL_PARENTS / 2` is 7.
        let mut parents = self.parents.iter();
        for challenges in self.challenges.chunks(config.challenges_per_step) {
            let mut packed_challenges_bits: Vec<bool> = challenges
                .iter()
                .flat_map(|challenge| {
                    let challenge = challenge.expect("challenge not set");
                    (0..challenge_bit_len)
                        .map(|i| challenge >> i & 1 == 1)
                        .collect::<Vec<bool>>()
                })
                .collect();
            assert!(packed_challenges_bits.len() <= 254);
            packed_challenges_bits.resize(256, false);

            let packed_challenges_bytes: Vec<u8> = packed_challenges_bits
                .chunks(8)
                .map(|bits| {
                    bits.iter()
                        .enumerate()
                        .fold(0u8, |acc, (i, bit)| acc + ((*bit as u8) << i))
                })
                .collect();
            assert_eq!(packed_challenges_bytes.len(), 32);

            let mut repr = F::Repr::default();
            repr.as_mut().copy_from_slice(&packed_challenges_bytes);
            let input =
                F::from_repr_vartime(repr).expect("packed challenges have invalid field repr");
            z0.push(input);

            for challenge_parents in (&mut parents).take(config.challenges_per_step) {
                for parents_half in challenge_parents.chunks(7) {
                    let mut packed_parents_bits: Vec<bool> = parents_half
                        .iter()
                        .flat_map(|parent| {
                            let parent = parent.expect("parent not set");
                            (0..challenge_bit_len)
                                .map(|i| parent >> i & 1 == 1)
                                .collect::<Vec<bool>>()
                        })
                        .collect();
                    assert!(packed_parents_bits.len() <= 254);
                    packed_parents_bits.resize(256, false);

                    let packed_parents_bytes: Vec<u8> = packed_parents_bits
                        .chunks(8)
                        .map(|bits| {
                            bits.iter()
                                .enumerate()
                                .fold(0u8, |acc, (i, bit)| acc + ((*bit as u8) << i))
                        })
                        .collect();
                    assert_eq!(packed_parents_bytes.len(), 32);

                    let mut repr = F::Repr::default();
                    repr.as_mut().copy_from_slice(&packed_parents_bytes);
                    let input =
                        F::from_repr_vartime(repr).expect("packed parents have invalid field repr");
                    z0.push(input);
                }
            }
        }

        z0
    }

    pub fn zs(&self, config: &CircuitConfig) -> Vec<Vec<F>> {
        let num_steps = config.num_steps();

        // 3 inputs for `replica_id, comm_d, comm_r`, 1 input for this step's packed challenges, and
        // 2 inputs per step challenge's packed parents.
        let num_inputs_used_per_step = 3 + 1 + 2 * config.challenges_per_step;

        let mut zs = Vec::<Vec<F>>::with_capacity(num_steps + 1);
        // Inputs to first circuit `z_0`.
        let z0 = self.z0(config);
        let num_inputs = z0.len();
        zs.push(z0);
        // Each subsequent circuit's inputs `z_i` are the previous circuit's outputs.
        for i in 0..num_steps {
            let mut zi = Vec::<F>::with_capacity(num_inputs);
            zi.extend_from_slice(&zs[0][..3]);
            zi.extend_from_slice(&zs[i][num_inputs_used_per_step..]);
            zi.resize(num_inputs, F::zero());
            zs.push(zi);
        }
        zs
    }
}

#[derive(Clone, Debug)]
pub struct ParentProof<F: NovaField> {
    pub column: Vec<Option<F>>,
    pub path_c: Vec<Vec<Option<F>>>,
}

impl<F: NovaField> ParentProof<F> {
    pub fn blank(config: &CircuitConfig) -> Self {
        let challenge_bit_len = config.base_arity.trailing_zeros() as usize;

        let mut base_challenge_bit_len = challenge_bit_len;
        if config.top_arity != 0 {
            base_challenge_bit_len -= config.top_arity.trailing_zeros() as usize;
        }
        if config.sub_arity != 0 {
            base_challenge_bit_len -= config.sub_arity.trailing_zeros() as usize;
        }
        let base_arity_bit_len = config.base_arity.trailing_zeros() as usize;
        assert_eq!(base_challenge_bit_len % base_arity_bit_len, 0);
        let base_path_len = base_challenge_bit_len / base_arity_bit_len;

        let mut path_c = Vec::<Vec<Option<F>>>::with_capacity(base_path_len + 2);
        for _ in 0..base_path_len {
            path_c.push(vec![None; config.base_arity - 1]);
        }
        if config.sub_arity != 0 {
            path_c.push(vec![None; config.sub_arity - 1]);
        }
        if config.top_arity != 0 {
            path_c.push(vec![None; config.top_arity - 1]);
        }

        ParentProof {
            column: vec![None; config.num_layers],
            path_c,
        }
    }
}

#[derive(Clone)]
pub struct ChallengeProof<F: NovaField> {
    pub leaf_d: Option<F>,
    pub path_d: Vec<Option<F>>,
    pub path_c: Vec<Vec<Option<F>>>,
    pub path_r: Vec<Vec<Option<F>>>,
    pub drg_parent_proofs: Vec<ParentProof<F>>,
    pub exp_parent_proofs: Vec<ParentProof<F>>,
}

impl<F: NovaField> ChallengeProof<F> {
    pub fn blank(config: &CircuitConfig) -> Self {
        let challenge_bit_len = config.base_arity.trailing_zeros() as usize;
        let parent_proof = ParentProof::blank(config);

        ChallengeProof {
            leaf_d: None,
            path_d: vec![None; challenge_bit_len],
            path_c: parent_proof.path_c.clone(),
            path_r: parent_proof.path_c.clone(),
            drg_parent_proofs: vec![parent_proof.clone(); DRG_PARENTS],
            exp_parent_proofs: vec![parent_proof; EXP_PARENTS],
        }
    }
}

#[derive(Clone)]
pub struct PrivateInputs<F: NovaField> {
    pub comm_c: Option<F>,
    pub root_r: Option<F>,
    // Partition challenges' proofs.
    pub challenge_proofs: Vec<ChallengeProof<F>>,
}

impl<F: NovaField> PrivateInputs<F> {
    pub fn blank(config: &CircuitConfig) -> Self {
        PrivateInputs {
            comm_c: None,
            root_r: None,
            challenge_proofs: vec![ChallengeProof::blank(config); config.total_challenge_count],
        }
    }
}

pub struct SdrPorepCircuit<Tree>
where
    Tree: MerkleTreeTrait,
    Tree::Field: NovaField,
{
    pub config: CircuitConfig,
    pub pub_inputs: PublicInputs<Tree::Field>,
    pub priv_inputs: PrivateInputs<Tree::Field>,
    pub _tree: PhantomData<Tree>,
}

pub type SdrPorepCircuit1Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U4, U0>>;
pub type SdrPorepCircuit2Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U0, U0>>;
pub type SdrPorepCircuit4Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U2, U0>>;
pub type SdrPorepCircuit8Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U4, U0>>;
pub type SdrPorepCircuit16Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U8, U0>>;
pub type SdrPorepCircuit32Kib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U8, U2>>;
pub type SdrPorepCircuit8Mib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U0, U0>>;
pub type SdrPorepCircuit16Mib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U2, U0>>;
pub type SdrPorepCircuit512Mib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U0, U0>>;
pub type SdrPorepCircuit32Gib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U8, U0>>;
pub type SdrPorepCircuit64Gib<F> = SdrPorepCircuit<LCTree<PoseidonHasher<F>, U8, U8, U2>>;

// We must manually implement `Clone` for all types generic over `MerkleTreeTrait` (as opposed to
// deriving `Clone`) because `#[derive(Clone)]` will only expand for `MerkleTreeTrait` types that
// implement `Clone` (which not all tree types do).
impl<Tree> Clone for SdrPorepCircuit<Tree>
where
    Tree: MerkleTreeTrait,
    Tree::Field: NovaField,
{
    fn clone(&self) -> Self {
        SdrPorepCircuit {
            config: self.config.clone(),
            pub_inputs: self.pub_inputs.clone(),
            priv_inputs: self.priv_inputs.clone(),
            _tree: PhantomData,
        }
    }
}

impl<Tree> StepCircuit<Tree::Field> for SdrPorepCircuit<Tree>
where
    Tree: MerkleTreeTrait,
    Tree::Hasher: R1CSHasher,
    Tree::Field: NovaField + PrimeFieldBits,
    Sha256Hasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
    PoseidonHasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
{
    fn arity(&self) -> usize {
        assert_eq!(
            self.pub_inputs.challenges.len(),
            self.config.total_challenge_count
        );
        assert_eq!(
            self.pub_inputs.parents.len(),
            self.config.total_challenge_count
        );
        assert!(self
            .pub_inputs
            .parents
            .iter()
            .all(|parents| parents.len() == TOTAL_PARENTS));

        // One public input per step containing the step's porep challenges.
        let total_challenge_inputs =
            self.config.total_challenge_count / self.config.challenges_per_step;

        // Two public inputs per porep challenge, each containing 7 of the challenge's 14 parents.
        let total_parent_inputs = 2 * self.config.total_challenge_count;

        // 3 public inputs for `replica_id, comm_d, comm_r`.
        3 + total_challenge_inputs + total_parent_inputs
    }

    fn synthesize<CS: ConstraintSystem<Tree::Field>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<Tree::Field>],
    ) -> Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError> {
        let SdrPorepCircuit {
            config,
            priv_inputs,
            ..
        } = self;

        let num_inputs = self.arity();
        assert_eq!(z.len(), num_inputs);
        let challenge_bit_len = config.sector_nodes.trailing_zeros() as usize;
        assert_eq!(
            priv_inputs.challenge_proofs[0].path_d.len(),
            challenge_bit_len
        );
        assert_eq!(
            priv_inputs.challenge_proofs[0].drg_parent_proofs[0]
                .column
                .len(),
            config.num_layers
        );
        let parent_inputs_per_step = 2 * config.challenges_per_step;

        let replica_id = &z[0];
        let comm_d = &z[1];
        let comm_r = &z[2];
        let challenges_input = &z[3];
        let parents_inputs = &z[4..4 + parent_inputs_per_step];

        let replica_id_bits =
            reverse_bit_numbering(replica_id.to_bits_le(cs.namespace(|| "replica_id_bits"))?);

        // Decompose a public input into this step's challenges' bits.
        let challenges_bits: Vec<Vec<AllocatedBit>> = {
            let challenges_bits: Vec<Option<bool>> = match challenges_input.get_value() {
                Some(f) => f.to_le_bits().into_iter().map(Some).collect(),
                None => vec![None; Tree::Field::NUM_BITS as usize],
            };

            let challenges_input_bit_len = config.challenges_per_step * challenge_bit_len;
            let challenges_bits = challenges_bits
                .iter()
                .take(challenges_input_bit_len)
                .enumerate()
                .map(|(i, bit)| {
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("challenges_input bit_{}", i)),
                        *bit,
                    )
                })
                .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()?;

            let mut lc = LinearCombination::zero();
            let mut coeff = Tree::Field::one();
            for bit in challenges_bits.iter() {
                lc = lc + (coeff, bit.get_variable());
                coeff = coeff.double();
            }
            cs.enforce(
                || "challenges_input binary decomposition",
                |_| lc,
                |lc| lc + CS::one(),
                |lc| lc + challenges_input.get_variable(),
            );

            challenges_bits
                .chunks(challenge_bit_len)
                .map(<[AllocatedBit]>::to_vec)
                .collect()
        };

        // Decompose public inputs into this step's challenges' parents' bits.
        let parents_bits: Vec<Vec<Vec<AllocatedBit>>> = {
            let parents_bits: Vec<Vec<Option<bool>>> = parents_inputs
                .iter()
                .map(|parents_input| match parents_input.get_value() {
                    Some(f) => f.to_le_bits().into_iter().map(Some).collect(),
                    None => vec![None; Tree::Field::NUM_BITS as usize],
                })
                .collect();

            let parents_input_bit_len = 7 * challenge_bit_len;
            let parents_bits = parents_bits
                .iter()
                .enumerate()
                .map(|(input_index, parents_bits)| {
                    parents_bits
                        .iter()
                        .take(parents_input_bit_len)
                        .enumerate()
                        .map(|(i, bit)| {
                            AllocatedBit::alloc(
                                cs.namespace(|| format!("parents_input_{} bit_{}", input_index, i)),
                                *bit,
                            )
                        })
                        .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
                })
                .collect::<Result<Vec<Vec<AllocatedBit>>, SynthesisError>>()?;

            for (input_index, (parents_input, parents_bits)) in
                parents_inputs.iter().zip(&parents_bits).enumerate()
            {
                let mut lc = LinearCombination::zero();
                let mut coeff = Tree::Field::one();
                for bit in parents_bits.iter() {
                    lc = lc + (coeff, bit.get_variable());
                    coeff = coeff.double();
                }
                cs.enforce(
                    || format!("parents_input_{} binary decomposition", input_index),
                    |_| lc,
                    |lc| lc + CS::one(),
                    |lc| lc + parents_input.get_variable(),
                );
            }

            parents_bits
                // Two parents inputs per challenge.
                .chunks(2)
                .map(|challenge_parents_bits| {
                    challenge_parents_bits
                        .iter()
                        .flat_map(|parents_bits| {
                            parents_bits
                                .chunks(challenge_bit_len)
                                .map(<[AllocatedBit]>::to_vec)
                                .collect::<Vec<Vec<AllocatedBit>>>()
                        })
                        .collect::<Vec<Vec<AllocatedBit>>>()
                })
                .collect()
        };

        // Witness roots of TreeC and TreeR.
        let comm_c = AllocatedNum::alloc(cs.namespace(|| "comm_c"), || {
            priv_inputs.comm_c.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let root_r = AllocatedNum::alloc(cs.namespace(|| "root_r"), || {
            priv_inputs.root_r.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Verify `comm_r == H(comm_c || root_r)`.
        let comm_r_calc =
            PoseidonHasher::hash2_circuit(cs.namespace(|| "comm_r_calc"), &comm_c, &root_r)?;
        cs.enforce(
            || "verify comm_r == comm_r_calc",
            |lc| lc + comm_r.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + comm_r_calc.get_variable(),
        );

        for (i, ((challenge_bits, challenge_proof), parents_bits)) in challenges_bits
            .iter()
            .zip(&priv_inputs.challenge_proofs)
            .zip(&parents_bits)
            .enumerate()
        {
            // Verify challenge's TreeD merkle proof.
            let leaf_d =
                AllocatedNum::alloc(cs.namespace(|| format!("challenge_{} leaf_d", i)), || {
                    challenge_proof
                        .leaf_d
                        .ok_or(SynthesisError::AssignmentMissing)
                })?;
            let path_d = challenge_proof
                .path_d
                .iter()
                .enumerate()
                .map(|(sib_index, sib)| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("challenge_{} path_d sib_{}", i, sib_index)),
                        || sib.ok_or(SynthesisError::AssignmentMissing),
                    )
                    .map(|sib| vec![sib])
                })
                .collect::<Result<Vec<Vec<AllocatedNum<Tree::Field>>>, SynthesisError>>()?;
            por_no_challenge_input::<BinaryMerkleTree<Sha256Hasher<Tree::Field>>, _>(
                cs.namespace(|| format!("challenge_{} tree_d merkle proof", i)),
                challenge_bits.to_vec(),
                leaf_d.clone(),
                path_d,
                comm_d.clone(),
            )?;

            let mut drg_parents_columns =
                Vec::<Vec<AllocatedNum<Tree::Field>>>::with_capacity(DRG_PARENTS);
            let mut exp_parents_columns =
                Vec::<Vec<AllocatedNum<Tree::Field>>>::with_capacity(EXP_PARENTS);

            // Veirfy DRG parents' TreeC Merkle proofs.
            for (parent_index, (parent_bits, parent_proof)) in parents_bits
                .iter()
                .zip(&challenge_proof.drg_parent_proofs)
                .enumerate()
            {
                // Compute parent's column hash, producing parent's leaf in TreeC.
                let column = parent_proof
                    .column
                    .iter()
                    .enumerate()
                    .map(|(layer_index, label)| {
                        AllocatedNum::alloc(
                            cs.namespace(|| {
                                format!(
                                    "challenge_{} drg_parent_{} layer_{} label",
                                    i, parent_index, layer_index
                                )
                            }),
                            || label.ok_or(SynthesisError::AssignmentMissing),
                        )
                    })
                    .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()?;

                let leaf_c = hash_single_column(
                    cs.namespace(|| {
                        format!("challenge_{} drg_parent_{} column hash", i, parent_index)
                    }),
                    &column,
                )?;

                let path_c = parent_proof
                    .path_c
                    .iter()
                    .enumerate()
                    .map(|(height, sibs)| {
                        sibs.iter()
                            .enumerate()
                            .map(|(sib_index, sib)| {
                                AllocatedNum::alloc(
                                    cs.namespace(|| {
                                        format!(
                                            "challenge_{} drg_parent_{} path_c height_{} sib_{}",
                                            i, parent_index, height, sib_index
                                        )
                                    }),
                                    || sib.ok_or(SynthesisError::AssignmentMissing),
                                )
                            })
                            .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()
                    })
                    .collect::<Result<Vec<Vec<AllocatedNum<Tree::Field>>>, SynthesisError>>()?;

                // Verify parent's TreeC merkle proof.
                por_no_challenge_input::<Tree, _>(
                    cs.namespace(|| {
                        format!(
                            "challenge_{} drg_parent_{} tree_c merkle proof",
                            i, parent_index
                        )
                    }),
                    parent_bits.to_vec(),
                    leaf_c.clone(),
                    path_c,
                    comm_c.clone(),
                )?;

                drg_parents_columns.push(column);
            }

            // Veirfy expander parents' TreeC Merkle proofs.
            for (parent_index, (parent_bits, parent_proof)) in parents_bits
                .iter()
                .zip(&challenge_proof.exp_parent_proofs)
                .enumerate()
            {
                // Compute parent's column hash, producing parent's leaf in TreeC.
                let column = parent_proof
                    .column
                    .iter()
                    .enumerate()
                    .map(|(layer_index, label)| {
                        AllocatedNum::alloc(
                            cs.namespace(|| {
                                format!(
                                    "challenge_{} exp_parent_{} layer_{} label",
                                    i, parent_index, layer_index
                                )
                            }),
                            || label.ok_or(SynthesisError::AssignmentMissing),
                        )
                    })
                    .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()?;

                let leaf_c = hash_single_column(
                    cs.namespace(|| {
                        format!("challenge_{} exp_parent_{} column hash", i, parent_index)
                    }),
                    &column,
                )?;

                let path_c = parent_proof
                    .path_c
                    .iter()
                    .enumerate()
                    .map(|(height, sibs)| {
                        sibs.iter()
                            .enumerate()
                            .map(|(sib_index, sib)| {
                                AllocatedNum::alloc(
                                    cs.namespace(|| {
                                        format!(
                                            "challenge_{} exp_parent_{} path_c height_{} sib_{}",
                                            i, parent_index, height, sib_index
                                        )
                                    }),
                                    || sib.ok_or(SynthesisError::AssignmentMissing),
                                )
                            })
                            .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()
                    })
                    .collect::<Result<Vec<Vec<AllocatedNum<Tree::Field>>>, SynthesisError>>()?;

                // Verify parent's TreeC merkle proof.
                por_no_challenge_input::<Tree, _>(
                    cs.namespace(|| {
                        format!(
                            "challenge_{} exp_parent_{} tree_c merkle proof",
                            i, parent_index
                        )
                    }),
                    parent_bits.to_vec(),
                    leaf_c.clone(),
                    path_c,
                    comm_c.clone(),
                )?;

                exp_parents_columns.push(column);
            }

            // Compute the challenge's label in each layer, i.e. its column.
            let mut column = Vec::<AllocatedNum<Tree::Field>>::with_capacity(config.num_layers);
            for layer_index in 0..config.num_layers {
                // Get the parent labels used to label the challenge.
                let mut parents_labels = Vec::<Vec<Boolean>>::with_capacity(TOTAL_PARENTS);

                // DRG parents are in the current layer.
                for (parent_index, parent_column) in drg_parents_columns.iter().enumerate() {
                    let parent_label = &parent_column[layer_index];
                    let parent_label_bits =
                        reverse_bit_numbering(parent_label.to_bits_le(cs.namespace(|| {
                            format!(
                                "challenge_{} layer_{} label drg_parent_{} bits",
                                i, layer_index, parent_index
                            )
                        }))?);
                    parents_labels.push(parent_label_bits);
                }
                // Expander parent are in the previous layer and only exist if we are labeling a
                // layer that is not the first layer.
                if layer_index != 0 {
                    for (parent_index, parent_column) in exp_parents_columns.iter().enumerate() {
                        let parent_label = &parent_column[layer_index - 1];
                        let parent_label_bits =
                            reverse_bit_numbering(parent_label.to_bits_le(cs.namespace(|| {
                                format!(
                                    "challenge_{} layer_{} label exp_parent_{} bits",
                                    i, layer_index, parent_index
                                )
                            }))?);
                        parents_labels.push(parent_label_bits);
                    }
                }

                // Repeat parent labels so labeling preimage meets its required length.
                let repeated_parents_labels: Vec<Vec<Boolean>> = parents_labels
                    .iter()
                    .cloned()
                    .cycle()
                    .take(REPEATED_PARENTS)
                    .collect();

                // Compute label.
                let label = create_label(
                    cs.namespace(|| format!("challenge_{} layer_{} label", i, layer_index)),
                    &replica_id_bits,
                    &repeated_parents_labels,
                    layer_index,
                    challenge_bits,
                )?;
                column.push(label);
            }

            // Compute the challenge's encoding (i.e. TreeR leaf); the encoding key is the
            // challenge's label in the last layer.
            let leaf_r = encode(
                cs.namespace(|| format!("challenge_{} leaf_r", i)),
                &column[config.num_layers - 1],
                &leaf_d,
            )?;

            let path_r = challenge_proof
                .path_r
                .iter()
                .enumerate()
                .map(|(height, sibs)| {
                    sibs.iter()
                        .enumerate()
                        .map(|(sib_index, sib)| {
                            AllocatedNum::alloc(
                                cs.namespace(|| {
                                    format!(
                                        "challenge_{} path_r height_{} sib_{}",
                                        i, height, sib_index
                                    )
                                }),
                                || sib.ok_or(SynthesisError::AssignmentMissing),
                            )
                        })
                        .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()
                })
                .collect::<Result<Vec<Vec<AllocatedNum<Tree::Field>>>, SynthesisError>>()?;

            // Verify the challenge's TreeR Merkle proof.
            por_no_challenge_input::<Tree, _>(
                cs.namespace(|| format!("challenge_{} tree_r merkle proof", i)),
                challenge_bits.to_vec(),
                leaf_r.clone(),
                path_r,
                root_r.clone(),
            )?;

            // Compute the challenge's TreeC leaf.
            let leaf_c = hash_single_column(
                cs.namespace(|| format!("challenge_{} column hash", i)),
                &column,
            )?;

            let path_c = challenge_proof
                .path_c
                .iter()
                .enumerate()
                .map(|(height, sibs)| {
                    sibs.iter()
                        .enumerate()
                        .map(|(sib_index, sib)| {
                            AllocatedNum::alloc(
                                cs.namespace(|| {
                                    format!(
                                        "challenge_{} path_c height_{} sib_{}",
                                        i, height, sib_index
                                    )
                                }),
                                || sib.ok_or(SynthesisError::AssignmentMissing),
                            )
                        })
                        .collect::<Result<Vec<AllocatedNum<Tree::Field>>, SynthesisError>>()
                })
                .collect::<Result<Vec<Vec<AllocatedNum<Tree::Field>>>, SynthesisError>>()?;

            // Verify the challenge's TreeC Merkle proof.
            por_no_challenge_input::<Tree, _>(
                cs.namespace(|| format!("challenge_{} tree_c merkle proof", i)),
                challenge_bits.to_vec(),
                leaf_c.clone(),
                path_c,
                comm_c.clone(),
            )?;
        }

        // Update public inputs.
        let mut z_out = Vec::<AllocatedNum<Tree::Field>>::with_capacity(self.arity());
        z_out.extend_from_slice(&z[..3]);
        z_out.extend_from_slice(&z[3 + 1 + parent_inputs_per_step..]);
        let zero = AllocatedNum::alloc(cs.namespace(|| "z_out zero"), || Ok(Tree::Field::zero()))?;
        for _ in 0..1 + parent_inputs_per_step {
            z_out.push(zero.clone());
        }
        Ok(z_out)
    }

    fn output(&self, z: &[Tree::Field]) -> Vec<Tree::Field> {
        let num_inputs = z.len();
        assert_eq!(num_inputs, self.arity());

        // 3 inputs for `replica_id, comm_d, comm_r`, 1 input for this step's packed challenges, and
        // 2 inputs per step challenge's packed parents.
        let num_inputs_used_per_step = 3 + 1 + 2 * self.config.challenges_per_step;

        let mut z_out = Vec::<Tree::Field>::with_capacity(num_inputs);
        z_out.extend_from_slice(&z[..3]);
        z_out.extend_from_slice(&z[num_inputs_used_per_step..]);
        z_out.resize(num_inputs, Tree::Field::zero());
        z_out
    }
}

fn create_label<F, CS>(
    mut cs: CS,
    replica_id: &[Boolean],
    repeated_parents_labels: &[Vec<Boolean>],
    layer_index: usize,
    // Least significant bit first.
    challenge: &[AllocatedBit],
) -> Result<AllocatedNum<F>, SynthesisError>
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    assert_eq!(replica_id.len(), 256);
    assert_eq!(repeated_parents_labels.len(), REPEATED_PARENTS);
    assert!(repeated_parents_labels
        .iter()
        .all(|label_bits| label_bits.len() == 256));
    let challenge_bit_len = challenge.len();
    assert!(challenge_bit_len <= 32);

    // Preimage is:
    // `replica_id || layer_index || 0u32 || challenge || [0u32; 5] || parent_labels`.
    let preimage_field_len = 2 + REPEATED_PARENTS;
    let preimage_bit_len = preimage_field_len * 256;
    let mut preimage = Vec::<Boolean>::with_capacity(preimage_bit_len);

    preimage.extend_from_slice(replica_id);

    // Layer indexes starts at 1 (not 0) and are appended to the preimage most significant bit
    // first.
    let layer_index = UInt32::constant(layer_index as u32 + 1);
    preimage.extend_from_slice(&layer_index.into_bits_be());

    // All porep challenges are 32 bits, however we represent them as 64-bit integers in the
    // preimage. Challenge bits are appended to the preimage most significant bit first.
    let challenge_leading_zeros = 64 - challenge_bit_len;
    for _ in 0..challenge_leading_zeros {
        preimage.push(Boolean::constant(false));
    }
    for bit in challenge.iter().cloned().rev() {
        preimage.push(Boolean::from(bit))
    }

    // Pad preimage to 512 bits.
    for _ in 0..160 {
        preimage.push(Boolean::constant(false));
    }
    assert_eq!(preimage.len(), 512);

    for parent_label in repeated_parents_labels {
        preimage.extend_from_slice(parent_label);
    }
    assert_eq!(preimage.len(), preimage_bit_len);

    // Compute Sha256
    let digest_bits = sha256_circuit(cs.namespace(|| "sha256"), &preimage)?;

    // Pack digest bits into a field element.
    let digest_bits = reverse_bit_numbering(digest_bits);
    // Truncate two most significant bits from field element's little-endian bits.
    let digest_bits = &digest_bits[..254];
    pack_bits(cs.namespace(|| "pack labeling digest"), digest_bits)
}

impl<Tree> SdrPorepCircuit<Tree>
where
    Tree: MerkleTreeTrait,
    Tree::Hasher: R1CSHasher,
    Tree::Field: NovaField + PrimeFieldBits,
    Sha256Hasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
    PoseidonHasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
{
    pub fn blank(config: &CircuitConfig) -> Self {
        SdrPorepCircuit {
            config: config.clone(),
            pub_inputs: PublicInputs::<Tree::Field>::blank(config),
            priv_inputs: PrivateInputs::<Tree::Field>::blank(config),
            _tree: PhantomData,
        }
    }

    #[inline]
    pub fn nova_params(&self) -> NovaParams<Tree> {
        nova::pub_params::<Tree::Field, Self>(self.clone())
    }

    pub fn z0(&self) -> Vec<Tree::Field> {
        self.pub_inputs.z0(&self.config)
    }
}

pub type NovaParams<Tree> = nova_snark::PublicParams<
    <<Tree as MerkleTreeTrait>::Field as NovaField>::C,
    <<Tree as MerkleTreeTrait>::Field as NovaField>::C2,
    SdrPorepCircuit<Tree>,
    TrivialTestCircuit<<<Tree as MerkleTreeTrait>::Field as NovaField>::F2>,
>;

pub type RecursiveProof<Tree> = RecursiveSNARK<
    <<Tree as MerkleTreeTrait>::Field as NovaField>::C,
    <<Tree as MerkleTreeTrait>::Field as NovaField>::C2,
    SdrPorepCircuit<Tree>,
    TrivialTestCircuit<<<Tree as MerkleTreeTrait>::Field as NovaField>::F2>,
>;

pub struct SdrPorepCompound<Tree: MerkleTreeTrait> {
    pub _tree: PhantomData<Tree>,
}

impl<Tree> SdrPorepCompound<Tree>
where
    Tree: MerkleTreeTrait,
    Tree::Hasher: R1CSHasher,
    Tree::Field: NovaField + PrimeFieldBits,
    Sha256Hasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
    PoseidonHasher<Tree::Field>: R1CSHasher<Field = Tree::Field>,
{
    pub fn create_circuits(
        vanilla_pub_inputs: &vanilla::PublicInputs<
            <PoseidonHasher<Tree::Field> as Hasher>::Domain,
            <Sha256Hasher<Tree::Field> as Hasher>::Domain,
        >,
        vanilla_partition_proofs: &[Vec<vanilla::Proof<Tree, Sha256Hasher<Tree::Field>>>],
        config: &CircuitConfig,
    ) -> Vec<SdrPorepCircuit<Tree>> {
        let replica_id: Tree::Field = vanilla_pub_inputs.replica_id.into();
        let tau = vanilla_pub_inputs.tau.clone().expect("tau not set");
        let comm_d: Tree::Field = tau.comm_d.into();
        let comm_r: Tree::Field = tau.comm_r.into();

        let vanilla_challenge_proofs = vanilla_partition_proofs
            .iter()
            .flat_map(|partition_proof| {
                partition_proof
                    .iter()
                    .collect::<Vec<&vanilla::Proof<_, _>>>()
            })
            .collect::<Vec<&vanilla::Proof<Tree, Sha256Hasher<Tree::Field>>>>();

        let challenges: Vec<Option<u32>> = vanilla_challenge_proofs
            .iter()
            .map(|challenge_proof| Some(challenge_proof.comm_d_proofs.path_index() as u32))
            .collect();
        let parents: Vec<Vec<Option<u32>>> = vanilla_challenge_proofs
            .iter()
            .map(|challenge_proof| {
                challenge_proof
                    .replica_column_proofs
                    .drg_parents
                    .iter()
                    .chain(&challenge_proof.replica_column_proofs.exp_parents)
                    .map(|column_proof| Some(column_proof.inclusion_proof.path_index() as u32))
                    .collect()
            })
            .collect();

        let comm_c: Tree::Field = vanilla_challenge_proofs[0]
            .replica_column_proofs
            .c_x
            .inclusion_proof
            .root()
            .into();
        let root_r: Tree::Field = vanilla_challenge_proofs[0].comm_r_last_proof.root().into();

        let challenge_proofs: Vec<ChallengeProof<Tree::Field>> = vanilla_challenge_proofs
            .iter()
            .map(|challenge_proof| {
                let leaf_d: Option<Tree::Field> = Some(challenge_proof.comm_d_proofs.leaf().into());

                let path_d: Vec<Option<Tree::Field>> = challenge_proof
                    .comm_d_proofs
                    .path()
                    .iter()
                    .map(|(sibs, _)| Some(sibs[0].into()))
                    .collect();

                let path_c: Vec<Vec<Option<Tree::Field>>> = challenge_proof
                    .replica_column_proofs
                    .c_x
                    .inclusion_proof
                    .path()
                    .iter()
                    .map(|(sibs, _)| sibs.iter().map(|&sib| Some(sib.into())).collect())
                    .collect();

                let path_r: Vec<Vec<Option<Tree::Field>>> = challenge_proof
                    .comm_r_last_proof
                    .path()
                    .iter()
                    .map(|(sibs, _)| sibs.iter().map(|&sib| Some(sib.into())).collect())
                    .collect();

                let drg_parent_proofs = challenge_proof
                    .replica_column_proofs
                    .drg_parents
                    .iter()
                    .map(|column_proof| {
                        let column: Vec<Option<Tree::Field>> = column_proof
                            .column
                            .rows
                            .iter()
                            .map(|&label| Some(label.into()))
                            .collect();
                        let path_c: Vec<Vec<Option<Tree::Field>>> = column_proof
                            .inclusion_proof
                            .path()
                            .iter()
                            .map(|(sibs, _)| sibs.iter().map(|&sib| Some(sib.into())).collect())
                            .collect();
                        ParentProof { column, path_c }
                    })
                    .collect::<Vec<ParentProof<Tree::Field>>>();

                let exp_parent_proofs = challenge_proof
                    .replica_column_proofs
                    .exp_parents
                    .iter()
                    .map(|column_proof| {
                        let column: Vec<Option<Tree::Field>> = column_proof
                            .column
                            .rows
                            .iter()
                            .map(|&label| Some(label.into()))
                            .collect();
                        let path_c: Vec<Vec<Option<Tree::Field>>> = column_proof
                            .inclusion_proof
                            .path()
                            .iter()
                            .map(|(sibs, _)| sibs.iter().map(|&sib| Some(sib.into())).collect())
                            .collect();
                        ParentProof { column, path_c }
                    })
                    .collect::<Vec<ParentProof<Tree::Field>>>();

                ChallengeProof {
                    leaf_d,
                    path_d,
                    path_c,
                    path_r,
                    drg_parent_proofs,
                    exp_parent_proofs,
                }
            })
            .collect();

        assert_eq!(challenges.len(), config.total_challenge_count);
        assert_eq!(config.total_challenge_count % config.challenges_per_step, 0);

        let pub_inputs = PublicInputs {
            replica_id: Some(replica_id),
            comm_d: Some(comm_d),
            comm_r: Some(comm_r),
            challenges,
            parents,
        };

        challenge_proofs
            .chunks(config.challenges_per_step)
            .map(|challenge_proofs| {
                let priv_inputs = PrivateInputs {
                    comm_c: Some(comm_c),
                    root_r: Some(root_r),
                    challenge_proofs: challenge_proofs.to_vec(),
                };
                SdrPorepCircuit {
                    config: config.clone(),
                    pub_inputs: pub_inputs.clone(),
                    priv_inputs,
                    _tree: PhantomData,
                }
            })
            .collect()
    }

    #[inline]
    pub fn gen_recursive_proof(
        params: &NovaParams<Tree>,
        circs: &[SdrPorepCircuit<Tree>],
    ) -> Result<RecursiveProof<Tree>, NovaError> {
        nova::gen_recursive_proof(params, circs, &circs[0].z0())
    }

    pub fn verify_recursive_proof(
        params: &NovaParams<Tree>,
        proof: &RecursiveProof<Tree>,
        config: &CircuitConfig,
        pub_inputs: &PublicInputs<Tree::Field>,
    ) -> Result<bool, NovaError> {
        let num_steps = config.num_steps();
        let zs = pub_inputs.zs(config);
        let z0 = zs[0].to_vec();
        let zn = &zs[num_steps];
        nova::verify_recursive_proof(params, proof, num_steps, z0, zn)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use filecoin_hashers::PoseidonArity;
    use halo2_proofs::pasta::Fp;
    use merkletree::store::StoreConfig;
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use storage_proofs_core::{
        api_version::ApiVersion, cache_key::CacheKey, merkle::DiskTree, proof::ProofScheme,
        test_helper::setup_replica, util::default_rows_to_discard, TEST_SEED,
    };
    use tempfile::tempdir;

    use crate::{
        stacked::{LayerChallenges, TemporaryAux, TemporaryAuxCache, BINARY_ARITY},
        PoRep,
    };

    type TreeR<F, U, V, W> = DiskTree<PoseidonHasher<F>, U, V, W>;

    fn test_inner<F, U, V, W>(sector_nodes: usize)
    where
        F: NovaField + PrimeFieldBits,
        U: PoseidonArity<F>,
        V: PoseidonArity<F>,
        W: PoseidonArity<F>,
        PoseidonHasher<F>: R1CSHasher<Field = F>,
        Sha256Hasher<F>: R1CSHasher<Field = F>,
    {
        let circ_config = if sector_nodes < SECTOR_NODES_32_GIB {
            let num_layers = 2;
            let total_challenge_count = 4;
            let challenges_per_step = 2;
            CircuitConfig::new(
                sector_nodes,
                num_layers,
                total_challenge_count,
                challenges_per_step,
            )
        } else {
            let num_layers = 10;
            let total_challenge_count = 180;
            CircuitConfig::max_challenges_per_step(sector_nodes, num_layers, total_challenge_count)
        };

        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        let replica_id = F::random(&mut rng);

        let sector_bytes = sector_nodes << 5;
        let mut data = Vec::<u8>::with_capacity(sector_bytes);
        for _ in 0..sector_nodes {
            data.extend_from_slice(F::random(&mut rng).to_repr().as_ref());
        }

        let cache_dir = tempdir().expect("failed to create tmp dir");

        // TreeD config.
        let config = StoreConfig::new(
            cache_dir.path(),
            CacheKey::CommDTree.to_string(),
            default_rows_to_discard(sector_nodes, BINARY_ARITY),
        );

        // Create replica.
        let replica_path = cache_dir.path().join("replica-path");
        let mut mmapped_data = setup_replica(&data, &replica_path);

        // Single vanilla partition.
        let layer_challenges =
            LayerChallenges::new(circ_config.num_layers, circ_config.total_challenge_count);

        let vanilla_setup_params = vanilla::SetupParams {
            nodes: sector_nodes,
            degree: DRG_PARENTS,
            expansion_degree: EXP_PARENTS,
            porep_id: [1; 32],
            layer_challenges,
            api_version: ApiVersion::V1_1_0,
        };

        let vanilla_pub_params =
            vanilla::StackedDrg::<TreeR<F, U, V, W>, Sha256Hasher<F>>::setup(&vanilla_setup_params)
                .expect("failed to create vanilla public params");

        let (tau, (p_aux, t_aux)) =
            vanilla::StackedDrg::<TreeR<F, U, V, W>, Sha256Hasher<F>>::replicate(
                &vanilla_pub_params,
                &replica_id.into(),
                (mmapped_data.as_mut()).into(),
                None,
                config,
                replica_path.clone(),
            )
            .expect("replication failed");

        // Store copy of original t_aux for later resource deletion.
        let t_aux_orig = t_aux.clone();

        // Convert TemporaryAux to TemporaryAuxCache, which instantiates all elements based on the
        // configs stored in TemporaryAux.
        let t_aux = TemporaryAuxCache::new(&t_aux, replica_path)
            .expect("failed to restore contents of t_aux");

        let vanilla_pub_inputs = vanilla::PublicInputs {
            replica_id: replica_id.into(),
            seed: rng.gen(),
            tau: Some(tau),
            k: Some(0),
        };

        let vanilla_priv_inputs = vanilla::PrivateInputs { p_aux, t_aux };

        let vanilla_partition_proof = vanilla::StackedDrg::prove(
            &vanilla_pub_params,
            &vanilla_pub_inputs,
            &vanilla_priv_inputs,
        )
        .expect("failed to generate vanilla partition proofs");

        let proof_is_valid = vanilla::StackedDrg::verify_all_partitions(
            &vanilla_pub_params,
            &vanilla_pub_inputs,
            &[vanilla_partition_proof.clone()],
        )
        .expect("failed to verify partition proof");
        assert!(proof_is_valid);

        // Discard cached Merkle trees that are no longer needed.
        TemporaryAux::clear_temp(t_aux_orig).expect("t_aux delete failed");

        // Create Nova circuits from vanilla artifacts.
        let circs = SdrPorepCompound::<TreeR<F, U, V, W>>::create_circuits(
            &vanilla_pub_inputs,
            &[vanilla_partition_proof],
            &circ_config,
        );

        // Create Nova parameters.
        let nova_params = circs[0].nova_params();
        // Generate recursive proof for circuits.

        let proof = SdrPorepCompound::gen_recursive_proof(&nova_params, &circs)
            .expect("failed to generate recursive proof");

        // Fails:
        let res = SdrPorepCompound::verify_recursive_proof(
            &nova_params,
            &proof,
            &circ_config,
            &circs[0].pub_inputs,
        );
        dbg!(&res);
        let is_valid = res.expect("nova proof verification failed");
        assert!(is_valid);
    }

    #[test]
    fn test_sdr_porep_1kib_nova() {
        test_inner::<Fp, U8, U4, U0>(SECTOR_NODES_1_KIB);
    }

    #[test]
    fn test_sdr_porep_2kib_nova() {
        test_inner::<Fp, U8, U0, U0>(SECTOR_NODES_2_KIB);
    }

    #[test]
    fn test_sdr_porep_4kib_nova() {
        test_inner::<Fp, U8, U2, U0>(SECTOR_NODES_4_KIB);
    }

    #[test]
    fn test_sdr_porep_8kib_nova() {
        test_inner::<Fp, U8, U4, U0>(SECTOR_NODES_8_KIB);
    }

    #[test]
    fn test_sdr_porep_16kib_nova() {
        test_inner::<Fp, U8, U8, U0>(SECTOR_NODES_16_KIB);
    }

    #[test]
    fn test_sdr_porep_32kib_nova() {
        test_inner::<Fp, U8, U8, U2>(SECTOR_NODES_32_KIB);
    }
}
