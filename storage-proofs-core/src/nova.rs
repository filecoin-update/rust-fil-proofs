use ff::{Field, PrimeField};
use halo2_proofs::pasta::{Ep, Eq, Fp, Fq};
use nova_snark::{
    errors::NovaError,
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    PublicParams, RecursiveSNARK,
};

// Prover [primiary] circuit's scalar field.
//
// Used to express a cycle of two elliptic curves (i.e. Pallas and Vesta).
pub trait NovaField: PrimeField {
    // Elliptic curve group for which `Self` is the scalar field (and `Self::F2` is the base field).
    type C: Group<Base = Self::F2, Scalar = Self>;

    // Scalar field of other elliptic curve in cycle.
    type F2: PrimeField;

    // Other elliptic curve group in cycle; `Self` is the base field and `Self::F2` is the scalar field.
    type C2: Group<Base = Self, Scalar = Self::F2>;
}

// Implement curves cycles:
//   - `Fp` is the scalar field of `Eq`
//   - `Fq` is the scalar fuield of `Ep`.
impl NovaField for Fp {
    type C = Eq;
    type F2 = Fq;
    type C2 = Ep;
}
impl NovaField for Fq {
    type C = Ep;
    type F2 = Fp;
    type C2 = Eq;
}

// Generate polynomial commitment scheme params for Nova given a [primary] circuit `Circ`
// over the field `F`; defaults the secondary circuit to `TrivialTestCircuit`.
pub fn pub_params<F, Circ>(circ: Circ) -> PublicParams<F::C, F::C2, Circ, TrivialTestCircuit<F::F2>>
where
    F: NovaField,
    Circ: StepCircuit<F>,
{
    PublicParams::setup(circ, TrivialTestCircuit::default())
}

// Generates a recursive proof for circuits `circs` and initial public inputs `z_0`.
pub fn gen_recursive_proof<F, Circ>(
    params: &PublicParams<F::C, F::C2, Circ, TrivialTestCircuit<F::F2>>,
    circs: &[Circ],
    z_0: &[F],
) -> Result<RecursiveSNARK<F::C, F::C2, Circ, TrivialTestCircuit<F::F2>>, NovaError>
where
    F: NovaField,
    Circ: StepCircuit<F>,
{
    assert!(!circs.is_empty());

    // Secondary (i.e. "sec") circuit does not change
    let circ_sec = TrivialTestCircuit::default();
    let z_sec = vec![F::F2::zero()];

    // Generate proof for first circuit.
    let circ_0 = &circs[0];
    let proof_0 = RecursiveSNARK::prove_step(
        params,
        None,
        circ_0.clone(),
        circ_sec.clone(),
        z_0.to_vec(),
        z_sec.clone(),
    )?;
    let mut proof_i = Some(proof_0);
    // Outputs of the first circuit are public inputs to the next circuit.
    let mut z_i = circ_0.output(z_0);

    // Add remaining circuit proofs to recursive proof.
    for circ_i in &circs[1..] {
        let proof = RecursiveSNARK::prove_step(
            params,
            proof_i.take(),
            circ_i.clone(),
            circ_sec.clone(),
            z_i.to_vec(),
            z_sec.clone(),
        )?;
        proof_i = Some(proof);
        z_i = circ_i.output(&z_i);
    }

    Ok(proof_i.expect("recursive proof should be set"))
}

// Verify a recursive proof `proof_i` that was generated from `num_steps` recursive proving steps.
// `z_0` are the public inputs to the first proof in the recursive chain; `z_i` are the outputs of
// the last circuit in the recursive chain.
pub fn verify_recursive_proof<F, Circ>(
    params: &PublicParams<F::C, F::C2, Circ, TrivialTestCircuit<F::F2>>,
    proof_i: &RecursiveSNARK<F::C, F::C2, Circ, TrivialTestCircuit<F::F2>>,
    num_steps: usize,
    z_0: Vec<F>,
    z_i: &[F],
) -> Result<bool, NovaError>
where
    F: NovaField,
    Circ: StepCircuit<F>,
{
    let z_sec = vec![F::F2::zero()];
    let (z_i_calc, z_sec_calc) = proof_i.verify(params, num_steps, z_0, z_sec.clone())?;
    Ok(z_i == z_i_calc && z_sec == z_sec_calc)
}
