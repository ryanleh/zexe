use algebra::{
    fields::{Fp2, Fp2Parameters},
    PrimeField,
};
use core::{borrow::Borrow, marker::PhantomData};
use r1cs_core::{ConstraintSystemRef, SynthesisError};

use crate::{
    fields::{fp::AllocatedFp, AllocatedField},
    prelude::*,
    Vec,
};
use core::ops::{Mul, MulAssign};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "P: Fp2Parameters, F: PrimeField"),
    Clone(bound = "P: Fp2Parameters, F: PrimeField")
)]
#[must_use]
pub struct AllocatedFp2<P: Fp2Parameters<Fp = F>, F: PrimeField> {
    pub c0: AllocatedFp<F>,
    pub c1: AllocatedFp<F>,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> AllocatedFp2<P, F> {
    pub fn new(c0: AllocatedFp<F>, c1: AllocatedFp<F>) -> Self {
        Self {
            c0,
            c1,
            _params: PhantomData,
        }
    }

    /// Multiply a AllocatedFp by quadratic nonresidue P::NONRESIDUE.
    #[inline]
    pub fn mul_fp_by_nonresidue(fe: &AllocatedFp<F>) -> Result<AllocatedFp<F>, SynthesisError> {
        fe.mul_constant(P::NONRESIDUE)
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> R1CSVar<F> for AllocatedFp2<P, F> {
    fn cs(&self) -> Option<ConstraintSystemRef<F>> {
        [&self.c0, &self.c1].cs()
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> From<Boolean<F>> for AllocatedFp2<P, F> {
    fn from(other: Boolean<F>) -> Self {
        if let Some(cs) = other.cs() {
            let c0 = AllocatedFp::from(other);
            let c1 = AllocatedFp::alloc_constant(cs, P::Fp::zero()).unwrap();
            Self::new(c0, c1)
        } else {
            unreachable!("Cannot create a constant value")
        }
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> AllocatedField<Fp2<P>> for AllocatedFp2<P, F> {
    type ConstraintF = F;

    #[inline]
    fn value(&self) -> Result<Fp2<P>, SynthesisError> {
        match (self.c0.value, self.c1.value) {
            (Some(c0), Some(c1)) => Ok(Fp2::new(c0, c1)),
            (..) => Err(SynthesisError::AssignmentMissing),
        }
    }

    #[inline]
    fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.add(&other.c0)?;
        let c1 = self.c1.add(&other.c1)?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn sub(&self, other: &Self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.sub(&other.c0)?;
        let c1 = self.c1.sub(&other.c1)?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn negate(&self) -> Result<Self, SynthesisError> {
        let result = self.clone();
        result.c0.negate_in_place()?;
        result.c1.negate_in_place()?;
        Ok(result)
    }

    #[inline]
    fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        let mut result = self.clone();
        let v0 = &self.c0 * &other.c0;
        let v1 = &self.c1 * &other.c1;

        result.c1 += &self.c0;
        result.c1 *= &(other.c0 + &other.c1);
        result.c1 -= &v0;
        result.c1 -= &v1;
        result.c0 = &v0 + &v1 * P::NONRESIDUE;
        Ok(result)
    }

    #[inline]
    fn square(&self) -> Result<Self, SynthesisError> {
        // From Libsnark/fp2_gadget.tcc
        // Complex multiplication for Fp2:
        //     "Multiplication and Squaring on Pairing-Friendly Fields"
        //     Devegili, OhEigeartaigh, Scott, Dahab

        // v0 = c0 - c1
        let mut v0 = &self.c0 - &self.c1;
        // v3 = c0 - beta * c1
        let v3 = &self.c0 - (&self.c1 * P::NONRESIDUE);
        // v2 = c0 * c1
        let v2 = &self.c0 * &self.c1;

        // v0 = (v0 * v3) + v2
        v0 *= &v3;
        v0 += &v2;

        let c0 = &v0 + &(&v2 * P::NONRESIDUE);
        let c1 = v2.double()?;

        Ok(Self::new(c0, c1))
    }

    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        // Compute v1
        let mut v1 = &self.c1 * &other.c1;

        // Perform second check
        let non_residue_times_v1 = &v1 * P::NONRESIDUE;
        let rhs = &result.c0 - &non_residue_times_v1;
        self.c0.mul_equals(&other.c0, &rhs)?;

        // Last check
        let a0_plus_a1 = &self.c0 + &self.c1;
        let b0_plus_b1 = &other.c0 + &other.c1;
        let one_minus_non_residue_v1 = &v1 - &non_residue_times_v1;

        let tmp = &(&result.c1 + &result.c0) + &one_minus_non_residue_v1;
        a0_plus_a1.mul_equals(&b0_plus_b1, &tmp)?;

        Ok(())
    }

    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c1 = self.c1.mul_constant(P::FROBENIUS_COEFF_FP2_C1[power % 2])?;
        Ok(result)
    }

    #[inline]
    fn add_constant(&self, other: Fp2<P>) -> Result<Self, SynthesisError> {
        let result = self.clone();
        result.c0 = &self.c0 + other.c0;
        result.c1 = &self.c1 + other.c1;
        Ok(result)
    }

    #[inline]
    fn sub_constant(&self, other: Fp2<P>) -> Result<Self, SynthesisError> {
        let result = self.clone();
        result.c0 = &self.c0 - other.c0;
        result.c1 = &self.c1 - other.c1;
        Ok(result)
    }

    fn mul_constant(&self, fe: Fp2<P>) -> Result<Self, SynthesisError> {
        // Karatsuba multiplication (see mul above).
        // Doesn't need any constraints; returns linear combinations of
        // `self`'s variables.
        //
        // (The operations below are guaranteed to return linear combinations)
        let (a0, a1) = (&self.c0, &self.c1);
        let (b0, b1) = (fe.c0, fe.c1);
        let mut v0 = a0 * b0;
        let beta_v1 = a1 * (b1 * P::NONRESIDUE);

        v0 += &beta_v1;
        let c0 = v0;
        let c1 = &(a0 * b1) + &(a1 * b0);
        Ok(Self::new(c0, c1))
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> EqGadget<F> for AllocatedFp2<P, F> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let b0 = self.c0.is_eq(&other.c0)?;
        let b1 = self.c1.is_eq(&other.c1)?;
        b0.and(&b1)
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.c0.conditional_enforce_equal(&other.c0, condition)?;
        self.c1.conditional_enforce_equal(&other.c1, condition)?;
        Ok(())
    }

    #[inline]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        is_equal
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> ToBitsGadget<F> for AllocatedFp2<P, F> {
    fn to_bits(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut c0 = self.c0.to_bits()?;
        let mut c1 = self.c1.to_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bits()?;
        let mut c1 = self.c1.to_non_unique_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> ToBytesGadget<F> for AllocatedFp2<P, F> {
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut c0 = self.c0.to_bytes()?;
        let mut c1 = self.c1.to_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bytes()?;
        let mut c1 = self.c1.to_non_unique_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> CondSelectGadget<F> for AllocatedFp2<P, F> {
    #[inline]
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = AllocatedFp::conditionally_select(cond, &true_value.c0, &false_value.c0)?;
        let c1 = AllocatedFp::conditionally_select(cond, &true_value.c1, &false_value.c1)?;
        Ok(Self::new(c0, c1))
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> TwoBitLookupGadget<F> for AllocatedFp2<P, F> {
    type TableConstant = Fp2<P>;

    fn two_bit_lookup(b: &[Boolean<F>], c: &[Self::TableConstant]) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = AllocatedFp::two_bit_lookup(b, &c0s)?;
        let c1 = AllocatedFp::two_bit_lookup(b, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> ThreeBitCondNegLookupGadget<F>
    for AllocatedFp2<P, F>
{
    type TableConstant = Fp2<P>;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<F>],
        b0b1: &Boolean<F>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = AllocatedFp::three_bit_cond_neg_lookup(b, b0b1, &c0s)?;
        let c1 = AllocatedFp::three_bit_cond_neg_lookup(b, b0b1, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<P: Fp2Parameters<Fp = F>, F: PrimeField> AllocVar<Fp2<P>, F> for AllocatedFp2<P, F> {
    #[inline]
    fn alloc_constant(
        cs: ConstraintSystemRef<F>,
        t: impl Borrow<Fp2<P>>,
    ) -> Result<Self, SynthesisError> {
        let t = *t.borrow();
        let c0 = AllocatedFp::alloc_constant(cs, t.c0)?;
        let c1 = AllocatedFp::alloc_constant(cs, t.c1)?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn alloc_witness<FN, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Fp2<P>>,
    {
        let (c0, c1) = match value_gen() {
            Ok(fe) => {
                let fe = *fe.borrow();
                (Ok(fe.c0), Ok(fe.c1))
            }
            Err(_) => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let c0 = AllocatedFp::alloc_witness(cs, || c0)?;
        let c1 = AllocatedFp::alloc_witness(cs, || c1)?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn alloc_input<FN, T>(cs: ConstraintSystemRef<F>, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Fp2<P>>,
    {
        let (c0, c1) = match value_gen() {
            Ok(fe) => {
                let fe = *fe.borrow();
                (Ok(fe.c0), Ok(fe.c1))
            }
            Err(_) => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let c0 = AllocatedFp::alloc_input(cs, || c0)?;
        let c1 = AllocatedFp::alloc_input(cs, || c1)?;
        Ok(Self::new(c0, c1))
    }
}

// TODO: extend to FieldVar<Fp2> as well.
impl<'a, P: Fp2Parameters<Fp = F>, F: PrimeField> Mul<P::Fp> for &'a AllocatedFp2<P, F> {
    type Output = AllocatedFp2<P, F>;

    /// Multiply a `AllocatedFp2` by a constant `Fp` element.
    #[inline]
    fn mul(&self, fe: P::Fp) -> AllocatedFp2<P, F> {
        let c0 = &self.c0 * fe;
        let c1 = &self.c1 * fe;
        AllocatedFp2::new(c0, c1)
    }
}

// TODO: extend to FieldVar<Fp2> as well.
impl<P: Fp2Parameters<Fp = F>, F: PrimeField> MulAssign<P::Fp> for AllocatedFp2<P, F> {
    fn mul_assign(&mut self, other: P::Fp) {
        *self = &*self * other;
    }
}
