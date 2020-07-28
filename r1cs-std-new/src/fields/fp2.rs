use crate::fields::{fp::AllocatedFp, quadratic_extension::*, AllocatedField};
use algebra::fields::{Fp2Parameters, Fp2ParamsWrapper, QuadExtParameters};

pub type AllocatedFp2<P> =
    AllocatedQuadExt<AllocatedFp<<P as Fp2Parameters>::Fp>, Fp2ParamsWrapper<P>>;

impl<AF: AllocatedField<P::Fp>, P: Fp2Parameters> AllocatedQuadExtParams<AF>
    for Fp2ParamsWrapper<P>
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut AF, power: usize) {
        *fe *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
