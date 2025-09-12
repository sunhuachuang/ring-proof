use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ff::PrimeField;
use ark_std::{end_timer, start_timer};
use w3f_pcs::pcs::PCS;

use w3f_plonk_common::prover::PlonkProver;
use w3f_plonk_common::transcript::PlonkTranscript;

use crate::piop::params::PiopParams;
use crate::piop::{FixedColumns, PiopProver, ProverKey};
use crate::{ArkTranscript, RingProof};

pub struct RingProver<F, CS, Curve, T = ArkTranscript>
where
    F: PrimeField,
    CS: PCS<F>,
    Curve: TECurveConfig<BaseField = F>,
    T: PlonkTranscript<F, CS>,
{
    piop_params: PiopParams<F, Curve, CS>,
    fixed_columns: FixedColumns<F, Affine<Curve>>,
    k: usize,
    plonk_prover: PlonkProver<F, CS, T>,
}

impl<F, CS, Curve, T> RingProver<F, CS, Curve, T>
where
    F: PrimeField,
    CS: PCS<F>,
    Curve: TECurveConfig<BaseField = F>,
    T: PlonkTranscript<F, CS>,
{
    pub fn init(
        prover_key: ProverKey<F, CS, Affine<Curve>>,
        piop_params: PiopParams<F, Curve, CS>,
        k: usize,
        empty_transcript: T,
    ) -> Self {
        let ProverKey {
            pcs_ck,
            fixed_columns,
            verifier_key,
        } = prover_key;

        let plonk_prover = PlonkProver::init(pcs_ck, verifier_key, empty_transcript);

        Self {
            piop_params,
            fixed_columns,
            k,
            plonk_prover,
        }
    }

    pub fn prove(&self, t: Curve::ScalarField) -> RingProof<F, CS> {
        let t_witgen = start_timer!(|| "witgen");
        let piop = PiopProver::build(&self.piop_params, self.fixed_columns.clone(), self.k, t);
        end_timer!(t_witgen);
        self.plonk_prover.prove(piop)
    }

    pub fn piop_params(&self) -> &PiopParams<F, Curve, CS> {
        &self.piop_params
    }
}
