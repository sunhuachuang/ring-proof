use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{vec, vec::Vec};

use w3f_plonk_common::domain::Domain;
use w3f_plonk_common::gadgets::ec::AffineColumn;
use w3f_plonk_common::FieldColumn;
use w3f_pcs::pcs::PCS;

use crate::piop::{FixedColumnsCommitted, FixedColumns};

/// Plonk Interactive Oracle Proofs (PIOP) parameters.
#[derive(Clone, CanonicalDeserialize, CanonicalSerialize)]
pub struct PiopParams<F: PrimeField, Curve: TECurveConfig<BaseField = F>, CS: PCS<F>> {
    /// Domain over which the piop is represented.
    pub(crate) domain: Domain<F>,
    /// Number of bits used to represent a jubjub scalar.
    pub(crate) scalar_bitlen: usize,
    /// Length of the part of the column representing the public keys (including the padding).
    pub keyset_part_size: usize,
    /// Blinding base point.
    pub(crate) h: Affine<Curve>,
    /// Summation base point.
    pub(crate) seed: Affine<Curve>,
    /// The point used to pad the list of public keys.
    pub(crate) padding: Affine<Curve>,
    /// The power of 2 multiples h
    pub(crate) power_of_2_multiples_of_h: Vec<Affine<Curve>>,
    /// Binary column that highlights which rows of the table correspond to the ring.
    ring_selector: FieldColumn<F>,
    ring_selector_comm: CS::C,
}

impl<F: PrimeField, Curve: TECurveConfig<BaseField = F>, CS: PCS<F>> PiopParams<F, Curve, CS> {
    /// Initialize PIOP parameters.
    ///
    /// - `domain`: polynomials evaluation domain.
    /// - `h`: Blinding base point.
    /// - `seed`: Accumulation base point
    /// - `padding`: The point used to pad the list of public keys.
    ///
    /// All points should be of an unknown discrete log.
    pub fn setup(
        ck: &CS::CK,
        domain: Domain<F>,
        h: Affine<Curve>,
        seed: Affine<Curve>,
        padding: Affine<Curve>,
    ) -> Self {
        let scalar_bitlen = Curve::ScalarField::MODULUS_BIT_SIZE as usize;
        // 1 accounts for the last cells of the points and bits columns that remain unconstrained
        let keyset_part_size = domain.capacity - scalar_bitlen - 1;

        // 2 prepare ring selectors
        let ring_selector = [
            vec![F::one(); keyset_part_size],
            vec![F::zero(); scalar_bitlen],
        ].concat();

        let ring_selector = domain.public_column(ring_selector);
        let ring_selector_comm = CS::commit_evals(ck, &ring_selector.evals).unwrap();

        let mut p = Self {
            domain,
            scalar_bitlen,
            keyset_part_size,
            h,
            seed,
            padding,
            power_of_2_multiples_of_h: Vec::new(),
            ring_selector,
            ring_selector_comm,
        };
        p.power_of_2_multiples_of_h = p.power_of_2_multiples_of_h();
        p
    }

    pub fn commit(
        &self,
        ck: &CS::CK,
        keys: &[Affine<Curve>]
    ) -> (FixedColumns<F, Affine<Curve>>, FixedColumnsCommitted<F, CS::C>) {
        let points = self.points_column(&keys);

        let pcx = CS::commit_evals(ck, &points.xs.evals).unwrap();
        let pcy = CS::commit_evals(ck, &points.ys.evals).unwrap();

        let fc = FixedColumns {
            points,
            ring_selector: self.ring_selector.clone(),
        };

        let fcc = FixedColumnsCommitted {
            points: [pcx, pcy],
            ring_selector: self.ring_selector_comm.clone(),
            phantom: Default::default(),
        };

        (fc, fcc)
    }

    pub fn fixed_columns(&self, keys: &[Affine<Curve>]) -> FixedColumns<F, Affine<Curve>> {
        let points = self.points_column(&keys);
        FixedColumns {
            points,
            ring_selector: self.ring_selector.clone(),
        }
    }

    pub fn points_column(&self, keys: &[Affine<Curve>]) -> AffineColumn<F, Affine<Curve>> {
        assert!(keys.len() <= self.keyset_part_size);
        let padding_len = self.keyset_part_size - keys.len();
        let padding = vec![self.padding; padding_len];
        let points = [keys, &padding, &self.power_of_2_multiples_of_h].concat();
        assert_eq!(points.len(), self.domain.capacity - 1);
        AffineColumn::public_column(points, &self.domain)
    }

    pub fn power_of_2_multiples_of_h(&self) -> Vec<Affine<Curve>> {
        let mut h = self.h.into_group();
        let mut multiples = Vec::with_capacity(self.scalar_bitlen);
        multiples.push(h);
        for _ in 1..self.scalar_bitlen {
            h.double_in_place();
            multiples.push(h);
        }
        CurveGroup::normalize_batch(&multiples)
    }

    pub fn scalar_part(&self, e: Curve::ScalarField) -> Vec<bool> {
        let bits_with_trailing_zeroes = e.into_bigint().to_bits_le();
        let significant_bits = &bits_with_trailing_zeroes[..self.scalar_bitlen];
        significant_bits.to_vec()
    }

    pub fn keyset_part_selector(&self) -> Vec<F> {
        [
            vec![F::one(); self.keyset_part_size],
            vec![F::zero(); self.scalar_bitlen],
        ]
        .concat()
    }
}

#[cfg(test)]
mod tests {
    use ark_ed_on_bls12_381_bandersnatch::{BandersnatchConfig, EdwardsAffine, Fq, Fr};
    use ark_std::ops::Mul;
    use ark_std::{test_rng, UniformRand};

    use w3f_plonk_common::domain::Domain;
    use w3f_plonk_common::test_helpers::cond_sum;

    use crate::piop::params::PiopParams;

    #[test]
    fn test_powers_of_h() {
        let rng = &mut test_rng();
        let h = EdwardsAffine::rand(rng);
        let seed = EdwardsAffine::rand(rng);
        let padding = EdwardsAffine::rand(rng);
        let domain = Domain::new(1024, false);

        let params = PiopParams::<Fq, BandersnatchConfig>::setup(domain, h, seed, padding);
        let t = Fr::rand(rng);
        let t_bits = params.scalar_part(t);
        let th = cond_sum(&t_bits, &params.power_of_2_multiples_of_h());
        assert_eq!(th, params.h.mul(t));
    }
}
