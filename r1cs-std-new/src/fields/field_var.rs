use crate::prelude::*;
use crate::{fields::AllocatedField, Assignment, R1CSVar};
use algebra::{prelude::*, to_bytes, BitIterator, ToBytes};
use core::borrow::Borrow;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use r1cs_core::{ConstraintSystemRef, SynthesisError};

/// Represent variables corresponding to the field `F`.
#[derive(Clone, Debug)]
pub enum FieldVar<F: Field, V: AllocatedField<F>> {
    Constant(F),
    Var(V),
}

impl<F, V, ConstraintF> R1CSVar<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    fn cs(&self) -> Option<ConstraintSystemRef<ConstraintF>> {
        match self {
            Self::Constant(_) => None,
            Self::Var(a) => a.cs(),
        }
    }
}

impl<F, V> FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    pub fn value(&self) -> Result<F, SynthesisError> {
        match self {
            Self::Constant(v) => Ok(*v),
            Self::Var(v) => v.value(),
        }
    }

    pub fn zero() -> Self {
        Self::Constant(F::zero())
    }

    pub fn one() -> Self {
        Self::Constant(F::one())
    }

    pub fn constant(v: F) -> Self {
        Self::Constant(v)
    }

    pub fn double(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.double())),
            Self::Var(v) => Ok(Self::Var(v.double()?)),
        }
    }

    pub fn double_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.double()?;
        Ok(self)
    }

    pub fn negate(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(-*c)),
            Self::Var(v) => Ok(Self::Var(v.negate()?)),
        }
    }

    pub fn negate_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.negate()?;
        Ok(self)
    }

    pub fn square(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.square())),
            Self::Var(v) => Ok(Self::Var(v.square()?)),
        }
    }

    pub fn square_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.square()?;
        Ok(self)
    }

    /// Enforce that `self * other == result`.
    pub fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        use FieldVar::*;
        match (self, other, result) {
            (Constant(_), Constant(_), Constant(_)) => Ok(()),
            (Constant(_), Constant(_), _) | (Constant(_), Var(_), _) | (Var(_), Constant(_), _) => {
                result.enforce_equal(&(self * other))
            } // this multiplication should be free
            (Var(v1), Var(v2), Var(v3)) => v1.mul_equals(v2, v3),
            (Var(v1), Var(v2), Constant(f)) => {
                let cs = v1.cs().unwrap();
                let v3 = V::alloc_constant(cs.clone(), f).unwrap();
                v1.mul_equals(v2, &v3)
            }
        }
    }

    /// Enforce that `self * self == result`.
    pub fn square_equals(&self, result: &Self) -> Result<(), SynthesisError> {
        use FieldVar::*;
        match (self, result) {
            (Constant(_), Constant(_)) => Ok(()),
            (Constant(f), Var(r)) => {
                let cs = r.cs().unwrap();
                let v = V::alloc_witness(cs, || Ok(f))?;
                v.square_equals(&r)
            }
            (Var(v), Constant(f)) => {
                let cs = v.cs().unwrap();
                let r = V::alloc_witness(cs, || Ok(f))?;
                v.square_equals(&r)
            }
            (Var(v1), Var(v2)) => v1.square_equals(v2),
        }
    }

    pub fn inverse(&self) -> Result<Self, SynthesisError> {
        match self {
            FieldVar::Var(v) => v.inverse().map(FieldVar::Var),
            FieldVar::Constant(f) => f.inverse().get().map(FieldVar::Constant),
        }
    }

    /// Returns (self / denominator), but requires fewer constraints than
    /// self * denominator.inverse()
    /// It is up to the caller to ensure that denominator is non-zero,
    /// since in that case the result is unconstrained.
    pub fn mul_by_inverse(&self, denominator: &Self) -> Result<Self, SynthesisError> {
        use FieldVar::*;
        match (self, denominator) {
            (Constant(s), Constant(d)) => Ok(Constant(*s / *d)),
            (Var(s), Constant(d)) => s.mul_constant(d.inverse().get()?).map(Var),
            (Constant(s), Var(d)) => d.inverse()?.mul_constant(*s).map(Var),
            (Var(s), Var(d)) => Ok(Var(d.inverse()?.mul(s))),
        }
    }

    pub fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError> {
        match self {
            FieldVar::Var(v) => v.frobenius_map(power).map(FieldVar::Var),
            FieldVar::Constant(f) => {
                let mut f = *f;
                f.frobenius_map(power);
                Ok(FieldVar::Constant(f))
            }
        }
    }

    pub fn frobenius_map_in_place(&mut self, power: usize) -> Result<&mut Self, SynthesisError> {
        *self = self.frobenius_map(power)?;
        Ok(self)
    }

    /// Accepts as input a list of bits which, when interpreted in little-endian
    /// form, are a scalar.
    pub fn pow(&self, bits: &[Boolean<V::ConstraintF>]) -> Result<Self, SynthesisError> {
        let mut res = Self::one();
        for bit in bits.iter() {
            res.square_in_place()?;
            let tmp = &res * self;
            res = Self::conditionally_select(bit, &tmp, &res)?;
        }
        Ok(res)
    }

    pub fn pow_by_constant<S: AsRef<[u64]>>(&self, exp: S) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        let mut found_one = false;

        for bit in BitIterator::new(exp) {
            if found_one {
                res = res.square()?;
            }

            if bit {
                if found_one {
                    res *= self;
                }
                found_one = true;
            }
        }

        Ok(res)
    }
}

/****************************************************************************/
/****************************************************************************/

impl<'a, F, V> Add<&'a FieldVar<F, V>> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn add(self, other: Self) -> FieldVar<F, V> {
        use FieldVar::*;
        match (self, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + *c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(*c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    }
}

impl<'a, F, V> Sub<&'a FieldVar<F, V>> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn sub(self, other: Self) -> FieldVar<F, V> {
        use FieldVar::*;
        match (self, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 - *c2),
            (Constant(c), Var(v)) => Var(v.sub_constant(*c).unwrap().negate().unwrap()),
            (Var(v), Constant(c)) => Var(v.sub_constant(*c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.sub(v2).unwrap()),
        }
    }
}

impl<'a, F, V> Mul<&'a FieldVar<F, V>> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn mul(self, other: Self) -> FieldVar<F, V> {
        use FieldVar::*;
        match (self, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 * *c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.mul_constant(*c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.mul(v2).unwrap()),
        }
    }
}

impl<'a, F, V> AddAssign<&'a FieldVar<F, V>> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn add_assign(&mut self, other: &'a Self) {
        let result = &*self + other;
        *self = result
    }
}

impl<'a, F, V> SubAssign<&'a FieldVar<F, V>> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn sub_assign(&mut self, other: &'a Self) {
        let result = &*self - other;
        *self = result
    }
}

impl<'a, F, V> MulAssign<&'a FieldVar<F, V>> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn mul_assign(&mut self, other: &'a Self) {
        let result = &*self * other;
        *self = result
    }
}

/****************************************************************************/
/****************************************************************************/

impl<'a, F, V> Add<F> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn add(self, other: F) -> FieldVar<F, V> {
        self + &FieldVar::Constant(other)
    }
}

impl<'a, F, V> Sub<F> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn sub(self, other: F) -> FieldVar<F, V> {
        self - &FieldVar::Constant(other)
    }
}

impl<'a, F, V> Mul<F> for &'a FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    type Output = FieldVar<F, V>;

    fn mul(self, other: F) -> FieldVar<F, V> {
        self * &FieldVar::Constant(other)
    }
}

impl<'a, F, V> AddAssign<F> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn add_assign(&mut self, other: F) {
        let result = &*self + other;
        *self = result
    }
}

impl<'a, F, V> SubAssign<F> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn sub_assign(&mut self, other: F) {
        let result = &*self - other;
        *self = result
    }
}

impl<'a, F, V> MulAssign<F> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F>,
{
    fn mul_assign(&mut self, other: F) {
        let result = &*self * other;
        *self = result
    }
}

impl<F, V, ConstraintF> EqGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Boolean::Constant(c1 == c2)),
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs().unwrap();
                let c = V::alloc_constant(cs, c)?;
                c.is_eq(v)
            }
            (Self::Var(v1), Self::Var(v2)) => v1.is_eq(v2),
        }
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs().unwrap();
                let c = V::alloc_constant(cs, c)?;
                c.conditional_enforce_equal(v, should_enforce)
            }
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_equal(v2, should_enforce),
        }
    }

    #[inline]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs().unwrap();
                let c = V::alloc_constant(cs, c)?;
                c.conditional_enforce_not_equal(v, should_enforce)
            }
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_not_equal(v2, should_enforce),
        }
    }
}

impl<F, V, ConstraintF> ToBitsGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    /// Outputs the unique bit-wise decomposition of `self` in *big-endian*
    /// form.
    fn to_bits(&self) -> Result<Vec<Boolean<ConstraintF>>, SynthesisError> {
        match self {
            Self::Constant(_) => todo!(), //Ok(UInt8::constant_vec(&to_bytes![c]?)),
            Self::Var(v) => v.to_bits(),
        }
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<ConstraintF>>, SynthesisError> {
        match self {
            Self::Constant(_) => todo!(), //Ok(UInt8::constant_vec(&to_bytes![c]?)),
            Self::Var(v) => v.to_non_unique_bits(),
        }
    }
}

impl<F, V, ConstraintF> ToBytesGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    fn to_bytes(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes![c]?)),
            Self::Var(v) => v.to_bytes(),
        }
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes![c]?)),
            Self::Var(v) => v.to_non_unique_bytes(),
        }
    }
}

impl<F, V, ConstraintF> CondSelectGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    #[inline]
    fn conditionally_select(
        cond: &Boolean<ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        match cond {
            Boolean::Constant(true) => Ok(true_value.clone()),
            Boolean::Constant(false) => Ok(false_value.clone()),
            _ => {
                let cs = cond.cs().unwrap();
                let true_value = match true_value {
                    Self::Constant(f) => V::alloc_constant(cs.clone(), f)?,
                    Self::Var(v) => v.clone(),
                };
                let false_value = match false_value {
                    Self::Constant(f) => V::alloc_constant(cs.clone(), f)?,
                    Self::Var(v) => v.clone(),
                };
                V::conditionally_select(cond, &true_value, &false_value).map(Self::Var)
            }
        }
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<F, V, ConstraintF> TwoBitLookupGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>
        + TwoBitLookupGadget<ConstraintF, TableConstant = F>,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    type TableConstant = F;

    fn two_bit_lookup(
        b: &[Boolean<ConstraintF>],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 2);
        debug_assert!(c.len() == 4);
        if b.cs().is_some() {
            V::two_bit_lookup(b, c).map(Self::Var)
        } else {
            let lsb = b[0].value()? as usize;
            let msb = b[1].value()? as usize;
            let index = lsb + (1 << msb);
            Ok(Self::Constant(c[index]))
        }
    }
}

impl<F, V, ConstraintF> ThreeBitCondNegLookupGadget<ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>
        + ThreeBitCondNegLookupGadget<ConstraintF, TableConstant = F>,
    ConstraintF: Field,
{
    type TableConstant = F;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<ConstraintF>],
        b0b1: &Boolean<ConstraintF>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 2);
        debug_assert!(c.len() == 4);

        if b.cs().or(b0b1.cs()).is_some() {
            V::three_bit_cond_neg_lookup(b, b0b1, c).map(Self::Var)
        } else {
            let lsb = b[0].value()? as usize;
            let msb = b[1].value()? as usize;
            let index = lsb + (1 << msb);
            let intermediate = c[index];

            let is_negative = b[2].value()?;
            let y = if is_negative {
                -intermediate
            } else {
                intermediate
            };
            Ok(Self::Constant(y))
        }
    }
}

impl<F, V, ConstraintF> AllocVar<F, ConstraintF> for FieldVar<F, V>
where
    F: Field,
    V: AllocatedField<F, ConstraintF = ConstraintF>,
    ConstraintF: Field,
{
    #[inline]
    fn alloc_constant(
        _: ConstraintSystemRef<ConstraintF>,
        t: impl Borrow<F>,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::Constant(*t.borrow()))
    }

    #[inline]
    fn alloc_witness_checked<FN, T>(
        cs: ConstraintSystemRef<ConstraintF>,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        V::alloc_witness_checked(cs, value_gen).map(Self::Var)
    }

    #[inline]
    fn alloc_input_checked<FN, T>(
        cs: ConstraintSystemRef<ConstraintF>,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        V::alloc_input_checked(cs, value_gen).map(Self::Var)
    }
}
