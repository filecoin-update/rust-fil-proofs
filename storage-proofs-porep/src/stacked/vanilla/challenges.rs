use filecoin_hashers::Domain;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[inline]
fn bigint_to_challenge(bigint: BigUint, sector_nodes: usize) -> usize {
    // Ensure that we don't challenge the first node.
    let non_zero_node = (bigint % (sector_nodes - 1)) + 1usize;
    // Assumes `sector_nodes` is less than 2^32.
    non_zero_node.to_u32_digits()[0] as usize
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LayerChallenges {
    /// How many layers we are generating challenges for.
    layers: usize,
    /// The maximum count of challenges
    max_count: usize,
}

impl LayerChallenges {
    pub const fn new(layers: usize, max_count: usize) -> Self {
        LayerChallenges { layers, max_count }
    }

    pub fn layers(&self) -> usize {
        self.layers
    }

    pub fn challenges_count_all(&self) -> usize {
        self.max_count
    }

    /// Derive all challenges.
    pub fn derive<D: Domain>(
        &self,
        leaves: usize,
        replica_id: &D,
        seed: &[u8; 32],
        k: u8,
    ) -> Vec<usize> {
        self.derive_internal(self.challenges_count_all(), leaves, replica_id, seed, k)
    }

    pub fn derive_internal<D: Domain>(
        &self,
        challenges_count: usize,
        leaves: usize,
        replica_id: &D,
        seed: &[u8; 32],
        k: u8,
    ) -> Vec<usize> {
        assert!(leaves > 2, "Too few leaves: {}", leaves);

        (0..challenges_count)
            .map(|i| {
                let j: u32 = ((challenges_count * k as usize) + i) as u32;

                let hash = Sha256::new()
                    .chain_update(replica_id.into_bytes())
                    .chain_update(seed)
                    .chain_update(&j.to_le_bytes())
                    .finalize();

                let bigint = BigUint::from_bytes_le(hash.as_ref());
                bigint_to_challenge(bigint, leaves)
            })
            .collect()
    }
}

#[derive(Debug, Default)]
pub struct ChallengeRequirements {
    pub minimum_challenges: usize,
}

pub mod synthetic {
    use super::*;

    use blstrs::Scalar as Fr;
    use chacha20::{
        cipher::{KeyIvInit, StreamCipher, StreamCipherSeek},
        ChaCha20,
    };
    use ff::PrimeField;

    const CHACHA20_NONCE: [u8; 12] = [0; 12];
    const CHACHA20_BLOCK_SIZE: u32 = 64;

    // The psuedo-random function used to generate synthetic challenges.
    pub enum Prf {
        Sha256 {
            replica_id: [u8; 32],
        },
        ChaCha20 {
            key: [u8; 32],
            chacha20: ChaCha20,
            next_challenge: Option<usize>,
        },
    }

    pub struct SynthChallenges {
        sector_nodes: usize,
        prf: Prf,
        num_synth_challenges: usize,
        i: usize,
    }

    impl Iterator for SynthChallenges {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
            if self.i >= self.num_synth_challenges {
                return None;
            }
            match self.prf {
                Prf::Sha256 { replica_id } => {
                    let digest = Sha256::new()
                        .chain_update(&replica_id)
                        .chain_update(&self.i.to_le_bytes())
                        .finalize();
                    let bigint = BigUint::from_bytes_le(digest.as_ref());
                    self.i += 1;
                    Some(bigint_to_challenge(bigint, self.sector_nodes))
                }
                Prf::ChaCha20 {
                    ref mut chacha20,
                    ref mut next_challenge,
                    ..
                } => {
                    if next_challenge.is_some() {
                        self.i += 2;
                        return next_challenge.take();
                    }
                    let mut rand_bytes = [0u8; 64];
                    chacha20.apply_keystream(&mut rand_bytes);
                    let bigint_1 = BigUint::from_bytes_le(&rand_bytes[..32]);
                    let bigint_2 = BigUint::from_bytes_le(&rand_bytes[32..]);
                    *next_challenge = Some(bigint_to_challenge(bigint_2, self.sector_nodes));
                    Some(bigint_to_challenge(bigint_1, self.sector_nodes))
                }
            }
        }
    }

    impl SynthChallenges {
        pub fn new_sha256(
            sector_nodes: usize,
            num_synth_challenges: usize,
            replica_id: &Fr,
        ) -> Self {
            assert!(
                num_synth_challenges < 1 << 32,
                "num_synth_challenges must not exceed u32"
            );

            SynthChallenges {
                sector_nodes,
                prf: Prf::Sha256 {
                    replica_id: replica_id.to_repr(),
                },
                num_synth_challenges,
                i: 0,
            }
        }

        pub fn new_chacha20(
            sector_nodes: usize,
            num_synth_challenges: usize,
            replica_id: &Fr,
        ) -> Self {
            assert_eq!(
                num_synth_challenges & 1,
                0,
                "num_synth_challenges must be even"
            );
            assert!(
                num_synth_challenges < 1 << 32,
                "num_synth_challenges must not exceed u32"
            );

            let replica_id_bytes: [u8; 32] = replica_id.to_repr();
            let replica_id_digest = Sha256::digest(&replica_id_bytes);

            let (key, chacha20) = {
                let mut key = [0u8; 32];
                key.copy_from_slice(replica_id_digest.as_ref());
                let chacha20 = ChaCha20::new(&key.into(), &CHACHA20_NONCE.into());
                (key, chacha20)
            };

            SynthChallenges {
                sector_nodes,
                prf: Prf::ChaCha20 {
                    key,
                    chacha20,
                    next_challenge: None,
                },
                num_synth_challenges,
                i: 0,
            }
        }

        pub fn gen_synth_challenge(&self, i: usize) -> usize {
            assert!(i < self.num_synth_challenges);
            match self.prf {
                Prf::Sha256 { ref replica_id } => {
                    let i = i as u32;
                    let digest = Sha256::new()
                        .chain_update(&replica_id)
                        .chain_update(&i.to_le_bytes())
                        .finalize();
                    let bigint = BigUint::from_bytes_le(digest.as_ref());
                    bigint_to_challenge(bigint, self.sector_nodes)
                }
                Prf::ChaCha20 { ref key, .. } => {
                    let block_index = (i >> 1) as u32;
                    let block_pos = block_index * CHACHA20_BLOCK_SIZE;
                    let mut chacha20 = ChaCha20::new(key.into(), &CHACHA20_NONCE.into());
                    chacha20
                        .try_seek(block_pos)
                        .expect("block position should not exceed keystream length");
                    let mut rand_bytes = [0u8; 64];
                    chacha20.apply_keystream(&mut rand_bytes);
                    let rand_bytes = if i & 1 == 0 {
                        &rand_bytes[..32]
                    } else {
                        &rand_bytes[32..]
                    };
                    let bigint = BigUint::from_bytes_le(rand_bytes);
                    bigint_to_challenge(bigint, self.sector_nodes)
                }
            }
        }

        pub fn gen_porep_challenges(&self, num_challenges: usize, rand: &[u8; 32]) -> Vec<usize> {
            let mut synth_challenge_indexes = Vec::<usize>::with_capacity(num_challenges);
            match self.prf {
                Prf::Sha256 { ref replica_id } => {
                    assert_eq!(
                        num_challenges & 0b11,
                        0,
                        "num_challenges must be divisible by 4"
                    );
                    for i in 0..num_challenges >> 2 {
                        let digest = Sha256::new()
                            .chain_update(&replica_id)
                            .chain_update(&rand)
                            .chain_update(&i.to_le_bytes())
                            .finalize();
                        let digest_bytes: &[u8] = digest.as_ref();
                        // TODO: why not take 8 `u32`s here, rather than 4?
                        for bytes in digest_bytes.chunks(4).take(4) {
                            let uint32 = bytes
                                .iter()
                                .rev()
                                .fold(0usize, |acc, byte| (acc << 8) + *byte as usize);
                            let synth_challenge_index = uint32 % self.num_synth_challenges;
                            synth_challenge_indexes.push(synth_challenge_index);
                        }
                    }
                }
                Prf::ChaCha20 { .. } => {
                    assert_eq!(
                        num_challenges & 0b1111,
                        0,
                        "num_challenges must be divisible by 16",
                    );
                    let mut chacha20 = ChaCha20::new(rand.into(), &CHACHA20_NONCE.into());
                    for _ in 0..num_challenges >> 4 {
                        let mut rand_bytes = [0u8; 64];
                        chacha20.apply_keystream(&mut rand_bytes);
                        for bytes in rand_bytes.chunks(4).take(16) {
                            let uint32 = bytes
                                .iter()
                                .rev()
                                .fold(0usize, |acc, byte| (acc << 8) + *byte as usize);
                            let synth_challenge_index = uint32 % self.num_synth_challenges;
                            synth_challenge_indexes.push(synth_challenge_index);
                        }
                    }
                }
            };
            synth_challenge_indexes
                .drain(..)
                .map(|i| self.gen_synth_challenge(i))
                .collect()
        }
    }
}

pub use synthetic::SynthChallenges;

#[cfg(test)]
mod test {
    use super::*;

    use std::collections::HashMap;

    use filecoin_hashers::sha256::Sha256Domain;
    use rand::{thread_rng, Rng};

    #[test]
    fn test_calculate_fixed_challenges() {
        let layer_challenges = LayerChallenges::new(10, 333);
        let expected = 333;

        let calculated_count = layer_challenges.challenges_count_all();
        assert_eq!(expected as usize, calculated_count);
    }

    #[test]
    fn challenge_derivation() {
        let n = 200;
        let layers = 100;

        let challenges = LayerChallenges::new(layers, n);
        let leaves = 1 << 30;
        let rng = &mut thread_rng();
        let replica_id: Sha256Domain = Sha256Domain::random(rng);
        let seed: [u8; 32] = rng.gen();
        let partitions = 5;
        let total_challenges = partitions * n;

        let mut layers_with_duplicates = 0;

        for _layer in 1..=layers {
            let mut histogram = HashMap::new();
            for k in 0..partitions {
                let challenges = challenges.derive(leaves, &replica_id, &seed, k as u8);

                for challenge in challenges {
                    let counter = histogram.entry(challenge).or_insert(0);
                    *counter += 1;
                }
            }
            let unique_challenges = histogram.len();
            if unique_challenges < total_challenges {
                layers_with_duplicates += 1;
            }
        }

        // If we generate 100 layers with 1,000 challenges in each, at most two layers can contain
        // any duplicates for this assertion to succeed.
        //
        // This test could randomly fail (anything's possible), but if it happens regularly something is wrong.
        assert!(layers_with_duplicates < 3);
    }

    #[test]
    // This test shows that partitioning (k = 0..partitions) generates the same challenges as
    // generating the same number of challenges with only one partition (k = 0).
    fn challenge_partition_equivalence() {
        let n = 40;
        let leaves = 1 << 30;
        let rng = &mut thread_rng();
        let replica_id: Sha256Domain = Sha256Domain::random(rng);
        let seed: [u8; 32] = rng.gen();
        let partitions = 5;
        let layers = 100;
        let total_challenges = n * partitions;

        for _layer in 1..=layers {
            let one_partition_challenges = LayerChallenges::new(layers, total_challenges).derive(
                leaves,
                &replica_id,
                &seed,
                0,
            );
            let many_partition_challenges = (0..partitions)
                .flat_map(|k| {
                    LayerChallenges::new(layers, n).derive(leaves, &replica_id, &seed, k as u8)
                })
                .collect::<Vec<_>>();

            assert_eq!(one_partition_challenges, many_partition_challenges);
        }
    }

    #[test]
    fn test_synthetic_challenges() {
        use blstrs::Scalar as Fr;
        let sector_nodes_1kib = 1 << 5;
        let replica_id = Fr::from(55);
        let num_synth_challenges = 6;

        let generator =
            SynthChallenges::new_chacha20(sector_nodes_1kib, num_synth_challenges, &replica_id);
        let synth_challenges: Vec<usize> = generator.collect();
        assert!(synth_challenges
            .iter()
            .all(|challenge| challenge < &sector_nodes_1kib));
        assert_eq!(synth_challenges, [19, 31, 6, 5, 2, 26]);

        let generator =
            SynthChallenges::new_chacha20(sector_nodes_1kib, num_synth_challenges, &replica_id);
        for (i, expected) in synth_challenges.into_iter().enumerate() {
            let challenge = generator.gen_synth_challenge(i);
            assert_eq!(challenge, expected);
        }
    }
}
