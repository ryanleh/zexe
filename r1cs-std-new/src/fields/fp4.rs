use crate::fields::{fp2::AllocatedFp2, quadratic_extension::*};
use algebra::fields::{Fp4Parameters, Fp4ParamsWrapper, QuadExtParameters};

pub type AllocatedFp4<P> =
    AllocatedQuadExt<AllocatedFp2<<P as Fp4Parameters>::Fp2Params>, Fp4ParamsWrapper<P>>;

impl<P: Fp4Parameters> AllocatedQuadExtParams<AllocatedFp2<P::Fp2Params>> for Fp4ParamsWrapper<P> {
    fn mul_base_field_var_by_frob_coeff(fe: &mut AllocatedFp2<P::Fp2Params>, power: usize) {
        fe.c0 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
