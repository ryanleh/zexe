use crate::fields::{cubic_extension::*, fp::AllocatedFp};
use algebra::fields::{CubicExtParameters, Fp3Parameters, Fp3ParamsWrapper};

pub type AllocatedFp3<P> =
    AllocatedCubicExt<AllocatedFp<<P as Fp3Parameters>::Fp>, Fp3ParamsWrapper<P>>;

impl<P: Fp3Parameters> AllocatedCubicExtParams<AllocatedFp<P::Fp>> for Fp3ParamsWrapper<P> {
    fn mul_base_field_vars_by_frob_coeff(
        c1: &mut AllocatedFp<P::Fp>,
        c2: &mut AllocatedFp<P::Fp>,
        power: usize,
    ) {
        *c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        *c2 *= Self::FROBENIUS_COEFF_C2[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
