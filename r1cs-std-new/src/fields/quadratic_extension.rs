use algebra::{
    fields::{Field, QuadExtField, QuadExtParameters},
    One,
};
use core::{borrow::Borrow, marker::PhantomData};
use r1cs_core::{ConstraintSystemRef, SynthesisError};

use crate::{
    fields::{ArithOpsBounds, FieldVar},
    prelude::*,
    Assignment, Vec,
};

#[derive(Derivative)]
#[derivative(Debug(bound = "BF: core::fmt::Debug"), Clone(bound = "BF: Clone"))]
#[must_use]
pub struct QuadExtVar<BF: FieldVar<P::BaseField>, P: QuadExtVarParams<BF>>
where
    for<'a> &'a BF: ArithOpsBounds<'a, P::BaseField, BF>,
{
    pub c0: BF,
    pub c1: BF,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

pub trait QuadExtVarParams<BF: FieldVar<Self::BaseField>>: QuadExtParameters
where
    for<'a> &'a BF: ArithOpsBounds<'a, Self::BaseField, BF>,
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut BF, power: usize);
}

impl<BF: FieldVar<P::BaseField>, P: QuadExtVarParams<BF>> QuadExtVar<BF, P>
where
    for<'a> &'a BF: ArithOpsBounds<'a, P::BaseField, BF>,
{
    pub fn new(c0: BF, c1: BF) -> Self {
        Self {
            c0,
            c1,
            _params: PhantomData,
        }
    }

    /// Multiply a BF by quadratic nonresidue P::NONRESIDUE.
    #[inline]
    pub fn mul_base_field_by_nonresidue(fe: &BF) -> Result<BF, SynthesisError> {
        Ok(fe * P::NONRESIDUE)
    }

    #[inline]
    pub fn mul_by_base_field_constant(&self, fe: P::BaseField) -> Self {
        let c0 = self.c0.clone() * fe;
        let c1 = self.c1.clone() * fe;
        QuadExtVar::new(c0, c1)
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
        Self: FieldVar<QuadExtField<P>, ConstraintF = BF::ConstraintF>,
    {
        use algebra::biginteger::arithmetic::find_wnaf;
        let mut res = Self::one();
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

impl<BF, P> R1CSVar<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'a> &'a BF: ArithOpsBounds<'a, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn cs(&self) -> Option<ConstraintSystemRef<BF::ConstraintF>> {
        [&self.c0, &self.c1].cs()
    }
}

impl<BF, P> From<Boolean<BF::ConstraintF>> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'a> &'a BF: ArithOpsBounds<'a, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn from(other: Boolean<BF::ConstraintF>) -> Self {
        let c0 = BF::from(other);
        let c1 = BF::zero();
        Self::new(c0, c1)
    }
}

impl<'a, BF, P> ArithOpsBounds<'a, QuadExtField<P>, QuadExtVar<BF, P>> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
}
impl<'a, BF, P> ArithOpsBounds<'a, QuadExtField<P>, QuadExtVar<BF, P>> for &'a QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
}

impl<BF, P> FieldVar<QuadExtField<P>> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'a> &'a BF: ArithOpsBounds<'a, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    type ConstraintF = BF::ConstraintF;

    fn constant(other: QuadExtField<P>) -> Self {
        let c0 = BF::constant(other.c0);
        let c1 = BF::constant(other.c1);
        Self::new(c0, c1)
    }

    fn zero() -> Self {
        let c0 = BF::zero();
        let c1 = BF::zero();
        Self::new(c0, c1)
    }

    fn one() -> Self {
        let c0 = BF::one();
        let c1 = BF::zero();
        Self::new(c0, c1)
    }

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
    QuadExtVar<BF, P>,
    QuadExtField<P>,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a QuadExtVar<BF, P>, other: &'a QuadExtVar<BF, P>| {
        let c0 = &this.c0 + &other.c0;
        let c1 = &this.c1 + &other.c1;
        QuadExtVar::new(c0, c1)
    },
    |this: &'a QuadExtVar<BF, P>, other: QuadExtField<P>| {
        this + QuadExtVar::constant(other)
    },
    (BF: FieldVar<P::BaseField>, P: QuadExtVarParams<BF>),
    for <'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>
);
impl_bounded_ops!(
    QuadExtVar<BF, P>,
    QuadExtField<P>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a QuadExtVar<BF, P>, other: &'a QuadExtVar<BF, P>| {
        let c0 = &this.c0 - &other.c0;
        let c1 = &this.c1 - &other.c1;
        QuadExtVar::new(c0, c1)
    },
    |this: &'a QuadExtVar<BF, P>, other: QuadExtField<P>| {
        this - QuadExtVar::constant(other)
    },
    (BF: FieldVar<P::BaseField>, P: QuadExtVarParams<BF>),
    for <'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>
);
impl_bounded_ops!(
    QuadExtVar<BF, P>,
    QuadExtField<P>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a QuadExtVar<BF, P>, other: &'a QuadExtVar<BF, P>| {
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
        result.c0 = v0 + &QuadExtVar::<BF, P>::mul_base_field_by_nonresidue(&v1).unwrap();
        result
    },
    |this: &'a QuadExtVar<BF, P>, other: QuadExtField<P>| {
        this * QuadExtVar::constant(other)
    },
    (BF: FieldVar<P::BaseField>, P: QuadExtVarParams<BF>),
    for <'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>
);

impl<BF, P> EqGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<BF::ConstraintF>, SynthesisError> {
        let b0 = self.c0.is_eq(&other.c0)?;
        let b1 = self.c1.is_eq(&other.c1)?;
        b0.and(&b1)
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<BF::ConstraintF>,
    ) -> Result<(), SynthesisError> {
        self.c0.conditional_enforce_equal(&other.c0, condition)?;
        self.c1.conditional_enforce_equal(&other.c1, condition)?;
        Ok(())
    }

    #[inline]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<BF::ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        is_equal
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl<BF, P> ToBitsGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn to_bits(&self) -> Result<Vec<Boolean<BF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bits()?;
        let mut c1 = self.c1.to_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<BF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bits()?;
        let mut c1 = self.c1.to_non_unique_bits()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<BF, P> ToBytesGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn to_bytes(&self) -> Result<Vec<UInt8<BF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_bytes()?;
        let mut c1 = self.c1.to_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<BF::ConstraintF>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bytes()?;
        let mut c1 = self.c1.to_non_unique_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<BF, P> CondSelectGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    #[inline]
    fn conditionally_select(
        cond: &Boolean<BF::ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = BF::conditionally_select(cond, &true_value.c0, &false_value.c0)?;
        let c1 = BF::conditionally_select(cond, &true_value.c1, &false_value.c1)?;
        Ok(Self::new(c0, c1))
    }
}

impl<BF, P> TwoBitLookupGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>
        + TwoBitLookupGadget<
            <BF as FieldVar<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    type TableConstant = QuadExtField<P>;

    fn two_bit_lookup(
        b: &[Boolean<BF::ConstraintF>],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = BF::two_bit_lookup(b, &c0s)?;
        let c1 = BF::two_bit_lookup(b, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<BF, P> ThreeBitCondNegLookupGadget<BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>
        + ThreeBitCondNegLookupGadget<
            <BF as FieldVar<P::BaseField>>::ConstraintF,
            TableConstant = P::BaseField,
        >,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    type TableConstant = QuadExtField<P>;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<BF::ConstraintF>],
        b0b1: &Boolean<BF::ConstraintF>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = BF::three_bit_cond_neg_lookup(b, b0b1, &c0s)?;
        let c1 = BF::three_bit_cond_neg_lookup(b, b0b1, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<BF, P> AllocVar<QuadExtField<P>, BF::ConstraintF> for QuadExtVar<BF, P>
where
    BF: FieldVar<P::BaseField>,
    for<'b> &'b BF: ArithOpsBounds<'b, P::BaseField, BF>,
    P: QuadExtVarParams<BF>,
{
    fn new_variable<T: Borrow<QuadExtField<P>>>(
        cs: ConstraintSystemRef<BF::ConstraintF>,
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

        let c0 = BF::new_variable(cs.clone(), || c0, mode)?;
        let c1 = BF::new_variable(cs.clone(), || c1, mode)?;
        Ok(Self::new(c0, c1))
    }
}
