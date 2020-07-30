use algebra::{
    fields::{CubicExtField, CubicExtParameters, Field},
    One, Zero,
};
use core::{borrow::Borrow, marker::PhantomData};
use r1cs_core::{ConstraintSystemRef, SynthesisError};

use crate::{fields::AllocatedField, prelude::*, Assignment, Vec};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>"),
    Clone(bound = "AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>")
)]
#[must_use]
pub struct AllocatedCubicExt<AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>> {
    pub c0: AF,
    pub c1: AF,
    pub c2: AF,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

pub trait AllocatedCubicExtParams<AF: AllocatedField<Self::BaseField>>: CubicExtParameters {
    fn mul_base_field_vars_by_frob_coeff(c1: &mut AF, c2: &mut AF, power: usize);
}

impl<AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>> AllocatedCubicExt<AF, P> {
    #[inline]
    pub fn new(c0: AF, c1: AF, c2: AF) -> Self {
        let _params = PhantomData;
        Self {
            c0,
            c1,
            c2,
            _params,
        }
    }

    /// Multiply a AF by cubic nonresidue P::NONRESIDUE.
    #[inline]
    pub fn mul_base_field_by_nonresidue(fe: &AF) -> Result<AF, SynthesisError> {
        fe.mul_constant(P::NONRESIDUE)
    }

    /// Multiply a AllocatedCubicExt by an element of `P::BaseField`.
    #[inline]
    pub fn mul_by_base_field_constant(&self, fe: P::BaseField) -> Self {
        let c0 = self.c0.mul_constant(fe).unwrap();
        let c1 = self.c1.mul_constant(fe).unwrap();
        let c2 = self.c2.mul_constant(fe).unwrap();
        Self::new(c0, c1, c2)
    }

    #[inline]
    pub fn mul_assign_by_base_field_constant(&mut self, fe: P::BaseField) {
        *self = (&*self).mul_by_base_field_constant(fe);
    }
}

impl<AF, P> R1CSVar<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn cs(&self) -> Option<ConstraintSystemRef<AF::ConstraintF>> {
        [&self.c0, &self.c1, &self.c2].cs()
    }
}

impl<AF, P> From<Boolean<AF::ConstraintF>> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn from(other: Boolean<AF::ConstraintF>) -> Self {
        if let Some(cs) = other.cs() {
            let c0 = AF::from(other);
            let c1 = AF::new_constant(cs.clone(), P::BaseField::zero()).unwrap();
            let c2 = AF::new_constant(cs, P::BaseField::zero()).unwrap();
            Self::new(c0, c1, c2)
        } else {
            unreachable!("Cannot create a constant value")
        }
    }
}

impl<AF, P> AllocatedField<CubicExtField<P>> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    AF: core::ops::Mul<AF, Output = AF>,
    for<'b> AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
    P: AllocatedCubicExtParams<AF>,
{
    type ConstraintF = AF::ConstraintF;

    #[inline]
    fn value(&self) -> Result<CubicExtField<P>, SynthesisError> {
        match (self.c0.value(), self.c1.value(), self.c2.value()) {
            (Ok(c0), Ok(c1), Ok(c2)) => Ok(CubicExtField::new(c0, c1, c2)),
            (..) => Err(SynthesisError::AssignmentMissing),
        }
    }

    #[inline]
    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        let c2 = self.c2.double()?;
        Ok(Self::new(c0, c1, c2))
    }

    #[inline]
    fn negate(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c0.negate_in_place()?;
        result.c1.negate_in_place()?;
        result.c2.negate_in_place()?;
        Ok(result)
    }

    /// Use the Chung-Hasan asymmetric squaring formula.
    ///
    /// (Devegili OhEig Scott Dahab --- Multiplication and Squaring on
    /// Abstract Pairing-Friendly
    /// Fields.pdf; Section 4 (CH-SQR2))
    #[inline]
    fn square(&self) -> Result<Self, SynthesisError> {
        let a = self.c0.clone();
        let b = self.c1.clone();
        let c = self.c2.clone();

        let s0 = a.square()?;
        let ab = &a * &b;
        let s1 = ab.double()?;
        let s2 = (&a - &b + &c).square()?;
        let s3 = (&b * &c).double()?;
        let s4 = c.square()?;

        let c0 = Self::mul_base_field_by_nonresidue(&s3)? + &s0;
        let c1 = Self::mul_base_field_by_nonresidue(&s4)? + &s1;
        let c2 = s1 + &s2 + &s3 - &s0 - &s4;

        Ok(Self::new(c0, c1, c2))
    }

    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        // Karatsuba multiplication for cubic extensions:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     v2 = A.c2 * B.c2
        //     result.c0 = v0 + β((a1 + a2)(b1 + b2) − v1 − v2)
        //     result.c1 = (a0 + a1)(b0 + b1) − v0 − v1 + βv2
        //     result.c2 = (a0 + a2)(b0 + b2) − v0 + v1 − v2,
        // We enforce this with six constraints:
        //
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     v2 = A.c2 * B.c2
        //
        //     result.c0 - v0 + \beta*(v1 + v2) = β(a1 + a2)(b1 + b2))
        //     result.c1 + v0 + v1 - βv2        = (a0 + a1)(b0 + b1)
        //     result.c2 + v0 - v1 + v2         = (a0 + a2)(b0 + b2)
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        //
        // This implementation adapted from
        // https://github.com/ZencashOfficial/ginger-lib/blob/development/r1cs/gadgets/std/src/fields/fp3.rs
        let v0 = &self.c0 * &other.c0;
        let v1 = &self.c1 * &other.c1;
        let v2 = &self.c2 * &other.c2;

        // Check c0
        let nr_a1_plus_a2 = (&self.c1 + &self.c2) * P::NONRESIDUE;
        let b1_plus_b2 = &other.c1 + &other.c2;
        let nr_v1 = &v1 * P::NONRESIDUE;
        let nr_v2 = &v2 * P::NONRESIDUE;
        let to_check = &result.c0 - &v0 + &nr_v1 + &nr_v2;
        nr_a1_plus_a2.mul_equals(&b1_plus_b2, &to_check)?;

        // Check c1
        let a0_plus_a1 = &self.c0 + &self.c1;
        let b0_plus_b1 = &other.c0 + &other.c1;
        let to_check = &result.c1 - &nr_v2 + &v0 + &v1;
        a0_plus_a1.mul_equals(&b0_plus_b1, &to_check)?;

        // Check c2
        let a0_plus_a2 = &self.c0 + &self.c2;
        let b0_plus_b2 = &other.c0 + &other.c2;
        let to_check = &result.c2 + &v0 - &v1 + &v2;
        a0_plus_a2.mul_equals(&b0_plus_b2, &to_check)?;
        Ok(())
    }

    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c0.frobenius_map_in_place(power)?;
        result.c1.frobenius_map_in_place(power)?;
        result.c2.frobenius_map_in_place(power)?;

        P::mul_base_field_vars_by_frob_coeff(&mut result.c1, &mut result.c2, power);
        Ok(result)
    }

    fn inverse(&self) -> Result<Self, SynthesisError> {
        let cs = self.cs().get()?.clone();
        let one = Self::new_constant(cs.clone(), CubicExtField::one())?;
        let inverse = Self::new_witness(cs, || self.value().and_then(|v| v.inverse().get()))?;
        self.mul_equals(&inverse, &one)?;
        Ok(inverse)
    }
}

impl_bounded_ops!(
    AllocatedCubicExt<AF, P>,
    CubicExtField<P>,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a AllocatedCubicExt<AF, P>, other: &'a AllocatedCubicExt<AF, P>| {
        let c0 = &this.c0 + &other.c0;
        let c1 = &this.c1 + &other.c1;
        let c2 = &this.c2 + &other.c2;
        AllocatedCubicExt::new(c0, c1, c2)
    },
    |this: &'a AllocatedCubicExt<AF, P>, other: CubicExtField<P>| {
        let c0 = &this.c0 + other.c0;
        let c1 = &this.c1 + other.c1;
        let c2 = &this.c2 + other.c2;
        AllocatedCubicExt::new(c0, c1, c2)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>),
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
);
impl_bounded_ops!(
    AllocatedCubicExt<AF, P>,
    CubicExtField<P>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a AllocatedCubicExt<AF, P>, other: &'a AllocatedCubicExt<AF, P>| {
        let c0 = &this.c0 - &other.c0;
        let c1 = &this.c1 - &other.c1;
        let c2 = &this.c2 - &other.c2;
        AllocatedCubicExt::new(c0, c1, c2)
    },
    |this: &'a AllocatedCubicExt<AF, P>, other: CubicExtField<P>| {
        let c0 = &this.c0 - other.c0;
        let c1 = &this.c1 - other.c1;
        let c2 = &this.c2 - other.c2;
        AllocatedCubicExt::new(c0, c1, c2)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>),
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
);
impl_bounded_ops!(
    AllocatedCubicExt<AF, P>,
    CubicExtField<P>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a AllocatedCubicExt<AF, P>, other: &'a AllocatedCubicExt<AF, P>| {
        // Karatsuba multiplication for cubic extensions:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     v2 = A.c2 * B.c2
        //     result.c0 = v0 + β((a1 + a2)(b1 + b2) − v1 − v2)
        //     result.c1 = (a0 + a1)(b0 + b1) − v0 − v1 + βv2
        //     result.c2 = (a0 + a2)(b0 + b2) − v0 + v1 − v2,
        //
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        let v0 = &this.c0 * &other.c0;
        let v1 = &this.c1 * &other.c1;
        let v2 = &this.c2 * &other.c2;
        let c0 =
            (((&this.c1 + &this.c2) * (&other.c1 + &other.c2) - &v1 - &v2) * P::NONRESIDUE) + &v0 ;
        let c1 =
            (&this.c0 + &this.c1) * (&other.c0 + &other.c1) - &v0 - &v1 + (&v2 * P::NONRESIDUE);
        let c2 =
            (&this.c0 + &this.c2) * (&other.c0 + &other.c2) - &v0 + &v1 - &v2;

        AllocatedCubicExt::new(c0, c1, c2)
    },
    |this: &'a AllocatedCubicExt<AF, P>, other: CubicExtField<P>| {
        // Karatsuba multiplication for cubic extensions:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     v2 = A.c2 * B.c2
        //     result.c0 = v0 + β((a1 + a2)(b1 + b2) − v1 − v2)
        //     result.c1 = (a0 + a1)(b0 + b1) − v0 − v1 + βv2
        //     result.c2 = (a0 + a2)(b0 + b2) − v0 + v1 − v2,
        //
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        let v0 = &this.c0 * other.c0;
        let v1 = &this.c1 * other.c1;
        let v2 = &this.c2 * other.c2;
        let c0 =
            ((&this.c1 + &this.c2) * (other.c1 + &other.c2) - &v1 - &v2) * P::NONRESIDUE + &v0;
        let c1 =
            (&this.c0 + &this.c1) * (other.c0 + &other.c1) - &v0 - &v1 + (&v2 * P::NONRESIDUE);
        let c2 =
            (&this.c0 + &this.c2) * (other.c0 + &other.c2) - &v0 + &v1 - &v2;
        AllocatedCubicExt::new(c0, c1, c2)
    },
    (AF: AllocatedField<P::BaseField>, P: AllocatedCubicExtParams<AF>),
    for<'b> &'b AF: core::ops::Add<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<&'b AF, Output = AF>,
    for<'b> &'b AF: core::ops::Add<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Sub<P::BaseField, Output = AF>,
    for<'b> &'b AF: core::ops::Mul<P::BaseField, Output = AF>,
);

impl<AF, P> EqGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<AF::ConstraintF>, SynthesisError> {
        let b0 = self.c0.is_eq(&other.c0)?;
        let b1 = self.c1.is_eq(&other.c1)?;
        let b2 = self.c2.is_eq(&other.c2)?;
        b0.and(&b1)?.and(&b2)
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<AF::ConstraintF>,
    ) -> Result<(), SynthesisError> {
        self.c0.conditional_enforce_equal(&other.c0, condition)?;
        self.c1.conditional_enforce_equal(&other.c1, condition)?;
        self.c2.conditional_enforce_equal(&other.c2, condition)?;
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

impl<AF, P> ToBitsGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn to_bits(&self) -> Result<Vec<Boolean<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bits()?;
        let mut c1 = self.c1.to_bits()?;
        let mut c2 = self.c2.to_bits()?;
        c0.append(&mut c1);
        c0.append(&mut c2);
        Ok(c0)
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bits()?;
        let mut c1 = self.c1.to_non_unique_bits()?;
        let mut c2 = self.c2.to_non_unique_bits()?;
        c0.append(&mut c1);
        c0.append(&mut c2);
        Ok(c0)
    }
}

impl<AF, P> ToBytesGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn to_bytes(&self) -> Result<Vec<UInt8<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bytes()?;
        let mut c1 = self.c1.to_bytes()?;
        let mut c2 = self.c2.to_bytes()?;
        c0.append(&mut c1);
        c0.append(&mut c2);

        Ok(c0)
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<AF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bytes()?;
        let mut c1 = self.c1.to_non_unique_bytes()?;
        let mut c2 = self.c2.to_non_unique_bytes()?;

        c0.append(&mut c1);
        c0.append(&mut c2);

        Ok(c0)
    }
}

impl<AF, P> CondSelectGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    #[inline]
    fn conditionally_select(
        cond: &Boolean<AF::ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = AF::conditionally_select(cond, &true_value.c0, &false_value.c0)?;
        let c1 = AF::conditionally_select(cond, &true_value.c1, &false_value.c1)?;
        let c2 = AF::conditionally_select(cond, &true_value.c2, &false_value.c2)?;
        Ok(Self::new(c0, c1, c2))
    }
}

impl<AF, P> TwoBitLookupGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>
        + TwoBitLookupGadget<
            <AF as AllocatedField<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    P: AllocatedCubicExtParams<AF>,
{
    type TableConstant = CubicExtField<P>;

    fn two_bit_lookup(
        b: &[Boolean<AF::ConstraintF>],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c2s = c.iter().map(|f| f.c2).collect::<Vec<_>>();
        let c0 = AF::two_bit_lookup(b, &c0s)?;
        let c1 = AF::two_bit_lookup(b, &c1s)?;
        let c2 = AF::two_bit_lookup(b, &c2s)?;
        Ok(Self::new(c0, c1, c2))
    }
}

impl<AF, P> ThreeBitCondNegLookupGadget<AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>
        + ThreeBitCondNegLookupGadget<
            <AF as AllocatedField<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    P: AllocatedCubicExtParams<AF>,
{
    type TableConstant = CubicExtField<P>;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<AF::ConstraintF>],
        b0b1: &Boolean<AF::ConstraintF>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c2s = c.iter().map(|f| f.c2).collect::<Vec<_>>();
        let c0 = AF::three_bit_cond_neg_lookup(b, b0b1, &c0s)?;
        let c1 = AF::three_bit_cond_neg_lookup(b, b0b1, &c1s)?;
        let c2 = AF::three_bit_cond_neg_lookup(b, b0b1, &c2s)?;
        Ok(Self::new(c0, c1, c2))
    }
}

impl<AF, P> AllocVar<CubicExtField<P>, AF::ConstraintF> for AllocatedCubicExt<AF, P>
where
    AF: AllocatedField<P::BaseField>,
    P: AllocatedCubicExtParams<AF>,
{
    fn new_variable<T: Borrow<CubicExtField<P>>>(
        cs: ConstraintSystemRef<AF::ConstraintF>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        use SynthesisError::*;
        let (c0, c1, c2) = match f() {
            Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1), Ok(fe.borrow().c2)),
            Err(_) => (
                Err(AssignmentMissing),
                Err(AssignmentMissing),
                Err(AssignmentMissing),
            ),
        };

        let c0 = AF::new_variable(cs.clone(), || c0, mode)?;
        let c1 = AF::new_variable(cs.clone(), || c1, mode)?;
        let c2 = AF::new_variable(cs.clone(), || c2, mode)?;
        Ok(Self::new(c0, c1, c2))
    }
}
