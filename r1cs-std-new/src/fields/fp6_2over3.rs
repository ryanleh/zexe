use crate::fields::{fp3::AllocatedFp3, quadratic_extension::*};
use algebra::fields::{fp6_2over3::*, QuadExtParameters};

pub type AllocatedFp6<P> =
    AllocatedQuadExt<AllocatedFp3<<P as Fp6Parameters>::Fp3Params>, Fp6ParamsWrapper<P>>;

impl<P: Fp6Parameters> AllocatedQuadExtParams<AllocatedFp3<P::Fp3Params>> for Fp6ParamsWrapper<P> {
    fn mul_base_field_var_by_frob_coeff(fe: &mut AllocatedFp3<P::Fp3Params>, power: usize) {
        fe.c0 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c2 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
