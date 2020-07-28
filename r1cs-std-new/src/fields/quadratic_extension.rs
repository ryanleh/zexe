use algebra::{
    fields::{Field, QuadExtField, QuadExtParameters},
    One, Zero,
};
use core::{borrow::Borrow, marker::PhantomData};
use r1cs_core::{ConstraintSystemRef, SynthesisError};

use crate::{fields::AllocatedField, prelude::*, Assignment, Vec};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>"),
    Clone(bound = "AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>")
)]
#[must_use]
pub struct AllocatedQuadExt<AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>> {
    pub c0: AF,
    pub c1: AF,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

pub trait AllocatedQuadExtParams<AF: AllocatedField<Self::BaseField>>: QuadExtParameters {
    fn mul_base_field_var_by_frob_coeff(fe: &mut AF, power: usize);
}

impl<AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>> AllocatedQuadExt<AF, P> {
    pub(crate) fn one(cs: ConstraintSystemRef<AF::ConstraintF>) -> Result<Self, SynthesisError> {
        Self::new_constant(cs, QuadExtField::one())
    }

    pub fn new(c0: AF, c1: AF) -> Self {
        Self {
            c0,
            c1,
            _params: PhantomData,
        }
    }

    /// Multiply a AF by quadratic nonresidue P::NONRESIDUE.
    #[inline]
    pub fn mul_base_field_by_nonresidue(fe: &AF) -> Result<AF, SynthesisError> {
        fe.mul_constant(P::NONRESIDUE)
    }

    #[inline]
    pub fn mul_by_base_field_constant(&self, fe: P::BaseField) -> Self {
        let c0 = self.c0.clone() * fe;
        let c1 = self.c1.clone() * fe;
        AllocatedQuadExt::new(c0, c1)
    }

    #[inline]
    pub fn mul_assign_by_base_field_constant(&mut self, fe: P::BaseField) {
        *self = (&*self).mul_by_base_field_constant(fe);
    }

    /// This is only to be used when the element is *known* to be in the cyclotomic subgroup.
    #[inline]
    pub fn unitary_inverse(&self) -> Result<Self, SynthesisError> {
        Ok(Self::new(self.c0.clone(), self.c1.negate()?))
    }

    /// This is only to be used when the element is *known* to be in the cyclotomic subgroup.
    #[inline]
    pub fn cyclotomic_exp(&self, exponent: impl AsRef<[u64]>) -> Result<Self, SynthesisError>
    where
        Self: AllocatedField<QuadExtField<P>, ConstraintF = AF::ConstraintF>,
    {
        use algebra::biginteger::arithmetic::find_wnaf;
        let cs = self.cs().unwrap();
        let mut res = Self::one(cs)?;
        let self_inverse = self.unitary_inverse()?;

        let mut found_nonzero = false;
        let naf = find_wnaf(exponent.as_ref());

        for &value in naf.iter().rev() {
            if found_nonzero {
                res.square_in_place()?;
            }

            if value != 0 {
                found_nonzero = true;

                if value > 0 {
                    res *= self;
                } else {
                    res *= &self_inverse;
                }
            }
        }

        Ok(res)
    }
}

impl<AF, P> R1CSVar<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn cs(&self) -> Option<ConstraintSystemRef<AF::ConstraintF>> {
        [&self.c0, &self.c1].cs()
    }
}

impl<AF, P> From<Boolean<AF::ConstraintF>> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn from(other: Boolean<AF::ConstraintF>) -> Self {
        if let Some(cs) = other.cs() {
            let c0 = AF::from(other);
            let c1 = AF::new_constant(cs, P::BaseField::zero()).unwrap();
            Self::new(c0, c1)
        } else {
            unreachable!("Cannot create a constant value")
        }
    }
}

impl<AF, P> AllocatedField<QuadExtField<P>> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
    P: AllocatedQuadExtParams<AF>,
{
    type ConstraintF = AF::ConstraintF;

    #[inline]
    fn value(&self) -> Result<QuadExtField<P>, SynthesisError> {
        match (self.c0.value(), self.c1.value()) {
            (Ok(c0), Ok(c1)) => Ok(QuadExtField::new(c0, c1)),
            (..) => Err(SynthesisError::AssignmentMissing),
        }
    }

    #[inline]
    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    fn negate(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c0.negate_in_place()?;
        result.c1.negate_in_place()?;
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
        let v3 = &self.c0 - &Self::mul_base_field_by_nonresidue(&self.c1)?;
        // v2 = c0 * c1
        let v2 = &self.c0 * &self.c1;

        // v0 = (v0 * v3) + v2
        v0 *= &v3;
        v0 += &v2;

        let c0 = &v0 + &Self::mul_base_field_by_nonresidue(&v2)?;
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
        let v1 = &self.c1 * &other.c1;

        // Perform second check
        let non_residue_times_v1 = Self::mul_base_field_by_nonresidue(&v1)?;
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
        result.c0.frobenius_map_in_place(power)?;
        result.c1.frobenius_map_in_place(power)?;
        P::mul_base_field_var_by_frob_coeff(&mut result.c1, power);
        Ok(result)
    }

    fn inverse(&self) -> Result<Self, SynthesisError> {
        let one = Self::new_constant(self.cs().get()?.clone(), QuadExtField::one())?;
        let inverse = Self::new_witness(self.cs().get()?.clone(), || {
            self.value().and_then(|val| val.inverse().get())
        })?;
        self.mul_equals(&inverse, &one)?;
        Ok(inverse)
    }
}

impl_bounded_ops!(
    AllocatedQuadExt<AF, P>, 
    QuadExtField<P>, 
    Add, 
    add, 
    AddAssign, 
    add_assign, 
    add_constant, 
    |this: &'a AllocatedQuadExt<AF, P>, other: &'a AllocatedQuadExt<AF, P>| {
        let c0 = &this.c0 + &other.c0;
        let c1 = &this.c1 + &other.c1;
        AllocatedQuadExt::new(c0, c1)
    },
    |this: &'a AllocatedQuadExt<AF, P>, other: QuadExtField<P>| {
        let c0 = &this.c0 + other.c0;
        let c1 = &this.c1 + other.c1;
        AllocatedQuadExt::new(c0, c1)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>),
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
);
impl_bounded_ops!(
    AllocatedQuadExt<AF, P>, 
    QuadExtField<P>, 
    Sub,
    sub, 
    SubAssign, 
    sub_assign, 
    sub_constant, 
    |this: &'a AllocatedQuadExt<AF, P>, other: &'a AllocatedQuadExt<AF, P>| {
        let c0 = &this.c0 - &other.c0;
        let c1 = &this.c1 - &other.c1;
        AllocatedQuadExt::new(c0, c1)
    },
    |this: &'a AllocatedQuadExt<AF, P>, other: QuadExtField<P>| {
        let c0 = &this.c0 - other.c0;
        let c1 = &this.c1 - other.c1;
        AllocatedQuadExt::new(c0, c1)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>),
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
);
impl_bounded_ops!(
    AllocatedQuadExt<AF, P>, 
    QuadExtField<P>, 
    Mul,
    mul, 
    MulAssign, 
    mul_assign, 
    mul_constant, 
    |this: &'a AllocatedQuadExt<AF, P>, other: &'a AllocatedQuadExt<AF, P>| {
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
        let mut result = this.clone();
        let v0 = &this.c0 * &other.c0;
        let v1 = &this.c1 * &other.c1;

        result.c1 += &this.c0;
        result.c1 *= &other.c0 + &other.c1;
        result.c1 -= &v0;
        result.c1 -= &v1;
        result.c0 = v0 + &AllocatedQuadExt::<AF, P>::mul_base_field_by_nonresidue(&v1).unwrap();
        result
    },
    |this: &'a AllocatedQuadExt<AF, P>, other: QuadExtField<P>| {
        // Karatsuba multiplication (see mul above).
        // Doesn't need any constraints; returns linear combinations of
        // `this`'s variables.
        //
        // (The operations below are guaranteed to return linear combinations)
        let (a0, a1) = (&this.c0, &this.c1);
        let (b0, b1) = (other.c0, other.c1);
        let mut v0 = a0 * b0;
        let beta_v1 = a1 * (b1 * &P::NONRESIDUE);

        v0 += &beta_v1;
        let c0 = v0;
        let c1 = (a0 * b1) + &(a1 * b0);
        AllocatedQuadExt::new(c0, c1)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedQuadExtParams<AF>),
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
);

impl<AF, P> EqGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<AF::ConstraintF>, SynthesisError> {
        let b0 = self.c0.is_eq(&other.c0)?;
        let b1 = self.c1.is_eq(&other.c1)?;
        b0.and(&b1)
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<AF::ConstraintF>,
    ) -> Result<(), SynthesisError> {
        self.c0.conditional_enforce_equal(&other.c0, condition)?;
        self.c1.conditional_enforce_equal(&other.c1, condition)?;
        Ok(())
    }

    #[inline]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<AF::ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        is_equal
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl<AF, P> ToBitsGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn to_bits(&self) -> Result<Vec<Boolean<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bits()?;
        let mut c1 = self.c1.to_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bits()?;
        let mut c1 = self.c1.to_non_unique_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<AF, P> ToBytesGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn to_bytes(&self) -> Result<Vec<UInt8<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bytes()?;
        let mut c1 = self.c1.to_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bytes()?;
        let mut c1 = self.c1.to_non_unique_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<AF, P> CondSelectGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    #[inline]
    fn conditionally_select(
        cond: &Boolean<AF::ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = AF::conditionally_select(cond, &true_value.c0, &false_value.c0)?;
        let c1 = AF::conditionally_select(cond, &true_value.c1, &false_value.c1)?;
        Ok(Self::new(c0, c1))
    }
}

impl<AF, P> TwoBitLookupGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>
        + TwoBitLookupGadget<
            <AF as AllocatedField<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    P: AllocatedQuadExtParams<AF>,
{
    type TableConstant = QuadExtField<P>;

    fn two_bit_lookup(
        b: &[Boolean<AF::ConstraintF>],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = AF::two_bit_lookup(b, &c0s)?;
        let c1 = AF::two_bit_lookup(b, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<AF, P> ThreeBitCondNegLookupGadget<AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>
        + ThreeBitCondNegLookupGadget<
            <AF as AllocatedField<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    P: AllocatedQuadExtParams<AF>,
{
    type TableConstant = QuadExtField<P>;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<AF::ConstraintF>],
        b0b1: &Boolean<AF::ConstraintF>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = AF::three_bit_cond_neg_lookup(b, b0b1, &c0s)?;
        let c1 = AF::three_bit_cond_neg_lookup(b, b0b1, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<AF, P> AllocVar<QuadExtField<P>, AF::ConstraintF> for AllocatedQuadExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedQuadExtParams<AF>,
{
    fn new_variable<T: Borrow<QuadExtField<P>>>(
        cs: ConstraintSystemRef<AF::ConstraintF>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let (c0, c1) = match f() {
            Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1)),
            Err(_) => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let c0 = AF::new_variable(cs.clone(), || c0, mode)?;
        let c1 = AF::new_variable(cs.clone(), || c1, mode)?;
        Ok(Self::new(c0, c1))
    }
}
