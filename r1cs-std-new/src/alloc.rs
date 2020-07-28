use crate::Vec;
use algebra::Field;
use core::borrow::Borrow;
use r1cs_core::{ConstraintSystemRef, SynthesisError};

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Copy, Clone)]
pub enum AllocationMode {
    Constant,
    Witness,
    Input,
}

pub trait AllocVar<V, F: Field>
where
    Self: Sized,
    V: ?Sized,
{
    fn new_variable<T: Borrow<V>>(
        cs: ConstraintSystemRef<F>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>;

    fn new_constant(cs: ConstraintSystemRef<F>, t: impl Borrow<V>) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, || Ok(t), AllocationMode::Constant)
    }

    fn new_input<T: Borrow<V>>(
        cs: ConstraintSystemRef<F>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, f, AllocationMode::Input)
    }

    fn new_witness<T: Borrow<V>>(
        cs: ConstraintSystemRef<F>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, f, AllocationMode::Witness)
    }
}

impl<I, F: Field, A: AllocVar<I, F>> AllocVar<[I], F> for Vec<A> {
    fn new_variable<T: Borrow<[I]>>(
        cs: ConstraintSystemRef<F>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::new_variable(cs.clone(), || Ok(value), mode)?);
        }
        Ok(vec)
    }
}
