use crate::fields::{fp::AllocatedFp, quadratic_extension::AllocatedQuadExt};
use algebra::fields::{Fp2Parameters, Fp2ParamsWrapper};

pub type AllocatedFp2<P> =
    AllocatedQuadExt<AllocatedFp<<P as Fp2Parameters>::Fp>, Fp2ParamsWrapper<P>>;
