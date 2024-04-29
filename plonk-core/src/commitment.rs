//! Useful commitment stuff
use ark_ec::{
    pairing::Pairing as PairingEngine, scalar_mul::variable_base::VariableBaseMSM,
    AffineRepr as AffineCurve,
};
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use ark_crypto_primitives::sponge::CryptographicSponge;

/// A homomorphic polynomial commitment
pub trait HomomorphicCommitment<F, S>:
    PolynomialCommitment<F, DensePolynomial<F>, S>
where
    F: PrimeField,
    Self::VerifierKey: core::fmt::Debug,
    S: CryptographicSponge,
{
    /// Combine a linear combination of homomorphic commitments
    fn multi_scalar_mul(commitments: &[Self::Commitment], scalars: &[F]) -> Self::Commitment;
}

/// The Default KZG-style commitment scheme
pub type KZG10<E, S> = SonicKZG10<E, DensePolynomial<<E as PairingEngine>::ScalarField>, S>;
/// A single KZG10 commitment
pub type KZG10Commitment<E, S> = <KZG10<E, S> as PolynomialCommitment<
    <E as PairingEngine>::ScalarField,
    DensePolynomial<<E as PairingEngine>::ScalarField>,
    S,
>>::Commitment;

impl<E, S> HomomorphicCommitment<E::ScalarField, S> for KZG10<E, S>
where
    E: PairingEngine,
    S: CryptographicSponge,
{
    fn multi_scalar_mul(
        commitments: &[KZG10Commitment<E, S>],
        scalars: &[E::ScalarField],
    ) -> KZG10Commitment<E, S> {
        let scalars_repr = scalars
            .iter()
            .map(<E::ScalarField as PrimeField>::into_bigint)
            .collect::<Vec<_>>();

        let points_repr = commitments.iter().map(|c| c.0).collect::<Vec<_>>();

        ark_poly_commit::kzg10::Commitment::<E>(
            VariableBaseMSM::multi_scalar_mul(&points_repr, &scalars_repr).into(),
        )
    }
}

/// Shortened type for Inner Product Argument polynomial commitment schemes
pub type IPA<G, D, S> = ark_poly_commit::ipa_pc::InnerProductArgPC<
    G,
    D,
    DensePolynomial<<G as ark_ec::AffineRepr>::ScalarField>,
    S,
>;
/// Shortened type for an Inner Product Argument polynomial commitment
pub type IPACommitment<G, D, S> = <IPA<G, D, S> as PolynomialCommitment<
    <G as AffineCurve>::ScalarField,
    DensePolynomial<<G as AffineCurve>::ScalarField>,
    S,
>>::Commitment;

use blake2::digest::Digest;
impl<G, D, S> HomomorphicCommitment<<G as ark_ec::AffineRepr>::ScalarField, S> for IPA<G, D, S>
where
    G: AffineCurve,
    D: Digest,
    S: CryptographicSponge,
{
    fn multi_scalar_mul(
        commitments: &[IPACommitment<G, D, S>],
        scalars: &[<G as ark_ec::AffineRepr>::ScalarField],
    ) -> IPACommitment<G, D, S> {
        let scalars_repr = scalars
            .iter()
            .map(<G as ark_ec::AffineRepr>::ScalarField::into_bigint)
            .collect::<Vec<_>>();

        let points_repr = commitments.iter().map(|c| c.comm).collect::<Vec<_>>();

        IPACommitment::<G, D, S> {
            comm: VariableBaseMSM::multi_scalar_mul(&points_repr, &scalars_repr).into(),
            shifted_comm: None, // TODO: support degree bounds?
        }
    }
}

/// Computes a linear combination of the polynomial evaluations and polynomial
/// commitments provided a challenge.
// TODO: complete doc & use util::lc for eval combination
pub fn linear_combination<F, H, S>(
    evals: &[F],
    commitments: &[H::Commitment],
    challenge: F,
) -> (H::Commitment, F)
where
    F: PrimeField,
    H: HomomorphicCommitment<F, S>,
    S: CryptographicSponge,
{
    assert_eq!(evals.len(), commitments.len());
    let powers = crate::util::powers_of(challenge)
        .take(evals.len())
        .collect::<Vec<_>>();
    let combined_eval = evals
        .iter()
        .zip(powers.iter())
        .map(|(&eval, power)| eval * power)
        .sum();
    let combined_commitment = H::multi_scalar_mul(commitments, &powers);
    (combined_commitment, combined_eval)
}

/// Aggregate polynomials
pub fn aggregate_polynomials<F: Field>(
    polynomials: &[DensePolynomial<F>],
    challenge: F,
) -> DensePolynomial<F> {
    use core::ops::Add;
    use num_traits::Zero;
    crate::util::powers_of(challenge)
        .zip(polynomials)
        .map(|(challenge, poly)| poly * challenge)
        .fold(Zero::zero(), Add::add)
}
