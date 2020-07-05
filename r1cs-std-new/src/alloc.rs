use crate::Vec;
use algebra::Field;
use core::borrow::Borrow;
use r1cs_core::{ConstraintSystemRef, SynthesisError};

pub trait AllocVar<V, F: Field>
where
    Self: Sized,
    V: ?Sized,
{
    /// Allocate a constant variable in the constraint system.
    fn alloc_constant(
        cs: ConstraintSystemRef<F>,
        t: impl Borrow<V>,
    ) -> Result<Self, SynthesisError>;

    /// Allocate a constant variable in the constraint system.
    fn alloc_witness<Func, T>(cs: ConstraintSystemRef<F>, f: Func) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<V>,
    {
        Self::alloc_witness_checked(cs, f)
    }

    fn alloc_witness_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        f: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<V>;

    fn alloc_input<Func, T>(cs: ConstraintSystemRef<F>, f: Func) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<V>,
    {
        Self::alloc_input_checked(cs, f)
    }

    fn alloc_input_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        f: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<V>;
}

impl<I, F: Field, A: AllocVar<I, F>> AllocVar<[I], F> for Vec<A> {
    #[inline]
    fn alloc_constant(
        cs: ConstraintSystemRef<F>,
        t: impl Borrow<[I]>,
    ) -> Result<Self, SynthesisError> {
        let mut vec = Vec::new();
        for value in t.borrow().iter() {
            vec.push(A::alloc_constant(cs.clone(), value)?);
        }
        Ok(vec)
    }

    fn alloc_witness<Func, T>(cs: ConstraintSystemRef<F>, f: Func) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<[I]>,
    {
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::alloc_witness(cs.clone(), || Ok(value))?);
        }
        Ok(vec)
    }

    fn alloc_input<Func, T>(cs: ConstraintSystemRef<F>, f: Func) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<[I]>,
    {
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::alloc_input(cs.clone(), || Ok(value))?);
        }
        Ok(vec)
    }

    fn alloc_witness_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        f: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<[I]>,
    {
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::alloc_witness_checked(cs.clone(), || Ok(value))?);
        }
        Ok(vec)
    }

    fn alloc_input_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        f: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<[I]>,
    {
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::alloc_input_checked(cs.clone(), || Ok(value))?);
        }
        Ok(vec)
    }
}
