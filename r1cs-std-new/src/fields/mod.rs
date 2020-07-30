use algebra::Field;
use core::{
    fmt::Debug,
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};
use r1cs_core::SynthesisError;

use crate::{prelude::*, Assignment};

#[macro_use]
pub mod macros;
pub mod cubic_extension;
pub mod field_var;
pub mod fp;
pub mod fp12;
pub mod fp2;
pub mod fp3;
pub mod fp4;
pub mod fp6_2over3;
pub mod fp6_3over2;
pub mod quadratic_extension;

pub trait AllocatedField<F: Field>:
    Sized
    + Clone
    + From<Boolean<<Self as AllocatedField<F>>::ConstraintF>>
    + R1CSVar<<Self as AllocatedField<F>>::ConstraintF>
    + EqGadget<<Self as AllocatedField<F>>::ConstraintF>
    + ToBitsGadget<<Self as AllocatedField<F>>::ConstraintF>
    + AllocVar<F, <Self as AllocatedField<F>>::ConstraintF>
    + ToBytesGadget<<Self as AllocatedField<F>>::ConstraintF>
    + CondSelectGadget<<Self as AllocatedField<F>>::ConstraintF>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
    + MulAssign<Self>
    + Add<F, Output = Self>
    + Sub<F, Output = Self>
    + Mul<F, Output = Self>
    + AddAssign<F>
    + SubAssign<F>
    + MulAssign<F>
    + Debug
{
    type ConstraintF: Field;

    fn value(&self) -> Result<F, SynthesisError>;

    fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(self.clone() + other)
    }

    fn sub(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(self.clone() - other)
    }

    fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(self.clone() * other)
    }

    fn add_constant(&self, other: F) -> Result<Self, SynthesisError> {
        Ok(self.clone() + other)
    }

    fn sub_constant(&self, other: F) -> Result<Self, SynthesisError> {
        Ok(self.clone() - other)
    }

    fn mul_constant(&self, other: F) -> Result<Self, SynthesisError> {
        Ok(self.clone() * other)
    }
    fn double(&self) -> Result<Self, SynthesisError> {
        self.add(self)
    }

    fn double_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.double()?;
        Ok(self)
    }

    fn negate(&self) -> Result<Self, SynthesisError>;

    #[inline]
    fn negate_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.negate()?;
        Ok(self)
    }

    fn square(&self) -> Result<Self, SynthesisError> {
        self.mul(self)
    }

    fn square_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.square()?;
        Ok(self)
    }

    /// Enforce that `self * other == result`.
    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        let actual_result = self.mul(other)?;
        result.enforce_equal(&actual_result)
    }

    /// Enforce that `self * self == result`.
    fn square_equals(&self, result: &Self) -> Result<(), SynthesisError> {
        let actual_result = self.square()?;
        result.enforce_equal(&actual_result)
    }

    fn inverse(&self) -> Result<Self, SynthesisError>;

    /// Returns (self / denominator), but requires fewer constraints than
    /// self * denominator.inverse()
    /// It is up to the caller to ensure that denominator is non-zero,
    /// since in that case the result is unconstrained.
    fn mul_by_inverse(&self, denominator: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness(self.cs().unwrap(), || {
            let denominator_inv_native = denominator.value()?.inverse().get()?;
            let result = self.value()? * &denominator_inv_native;
            Ok(result)
        })?;
        result.mul_equals(&denominator, &self)?;

        Ok(result)
    }

    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError>;

    fn frobenius_map_in_place(&mut self, power: usize) -> Result<&mut Self, SynthesisError> {
        *self = self.frobenius_map(power)?;
        Ok(self)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use rand::{self, SeedableRng};
    use rand_xorshift::XorShiftRng;

    use crate::{
        fields::{field_var::FieldVar, AllocatedField},
        prelude::*,
        Vec,
    };
    use algebra::{test_rng, BitIterator, Field, UniformRand};
    use r1cs_core::{ConstraintSystem, SynthesisError};

    type FV<F, AF> = FieldVar<F, AF>;

    #[allow(dead_code)]
    pub(crate) fn field_test<F: Field, AF: AllocatedField<F>>() -> Result<(), SynthesisError>
    where
        AF: crate::select::TwoBitLookupGadget<
            <AF as AllocatedField<F>>::ConstraintF,
            TableConstant = F,
        >,
    {
        let cs = ConstraintSystem::<AF::ConstraintF>::new_ref();

        let mut rng = test_rng();
        let a_native = F::rand(&mut rng);
        let b_native = F::rand(&mut rng);
        let a = FV::<F, AF>::new_witness(cs.ns("generate_a"), || Ok(a_native))?;
        let b = FV::<F, AF>::new_witness(cs.ns("generate_b"), || Ok(b_native))?;
        let b_const = FV::new_constant(cs.ns("b_as_constant"), b_native)?;

        let zero = FV::zero();
        let zero_native = zero.value()?;
        zero.enforce_equal(&zero)?;

        let one = FV::one();
        let one_native = one.value()?;
        one.enforce_equal(&one)?;

        one.enforce_not_equal(&zero)?;

        let one_dup = &zero + &one;
        one_dup.enforce_equal(&one)?;

        let two = &one + &one;
        two.enforce_equal(&two)?;
        two.enforce_equal(&one.double()?)?;
        two.enforce_not_equal(&one)?;
        two.enforce_not_equal(&zero)?;

        // a + 0 = a
        let a_plus_zero = &a + &zero;
        assert_eq!(a_plus_zero.value()?, a_native);
        a_plus_zero.enforce_equal(&a)?;
        a_plus_zero.enforce_not_equal(&a.double()?)?;

        // a - 0 = a
        let a_minus_zero = &a - &zero;
        assert_eq!(a_minus_zero.value()?, a_native);
        a_minus_zero.enforce_equal(&a)?;

        // a - a = 0
        let a_minus_a = &a - &a;
        assert_eq!(a_minus_a.value()?, zero_native);
        a_minus_a.enforce_equal(&zero)?;

        // a + b = b + a
        let a_b = &a + &b;
        let b_a = &b + &a;
        assert_eq!(a_b.value()?, a_native + &b_native);
        a_b.enforce_equal(&b_a)?;

        // (a + b) + a = a + (b + a)
        let ab_a = &a_b + &a;
        let a_ba = &a + &b_a;
        assert_eq!(ab_a.value()?, a_native + &b_native + &a_native);
        ab_a.enforce_equal(&a_ba)?;

        let b_times_a_plus_b = &a_b * &b;
        let b_times_b_plus_a = &b_a * &b;
        assert_eq!(
            b_times_a_plus_b.value()?,
            b_native * &(b_native + &a_native)
        );
        assert_eq!(
            b_times_a_plus_b.value()?,
            (b_native + &a_native) * &b_native
        );
        assert_eq!(
            b_times_a_plus_b.value()?,
            (a_native + &b_native) * &b_native
        );
        b_times_b_plus_a.enforce_equal(&b_times_a_plus_b)?;

        // a * 1 = a
        assert_eq!((&a * &one).value()?, a_native * &one_native);

        // a * b = b * a
        let ab = &a * &b;
        let ba = &b * &a;
        assert_eq!(ab.value()?, ba.value()?);
        assert_eq!(ab.value()?, a_native * &b_native);

        let ab_const = &a * &b_const;
        let b_const_a = &b_const * &a;
        assert_eq!(ab_const.value()?, b_const_a.value()?);
        assert_eq!(ab_const.value()?, ab.value()?);
        assert_eq!(ab_const.value()?, a_native * &b_native);

        // (a * b) * a = a * (b * a)
        let ab_a = &ab * &a;
        let a_ba = &a * &ba;
        assert_eq!(ab_a.value()?, a_ba.value()?);
        assert_eq!(ab_a.value()?, a_native * &b_native * &a_native);

        let aa = &a * &a;
        let a_squared = a.square()?;
        a_squared.enforce_equal(&aa)?;
        assert_eq!(aa.value()?, a_squared.value()?);
        assert_eq!(aa.value()?, a_native.square());

        let aa = &a * a.value()?;
        a_squared.enforce_equal(&aa)?;
        assert_eq!(aa.value()?, a_squared.value()?);
        assert_eq!(aa.value()?, a_native.square());

        let a_b2 = &a + b_native;
        a_b.enforce_equal(&a_b2)?;
        assert_eq!(a_b.value()?, a_b2.value()?);

        let a_inv = a.inverse()?;
        a_inv.mul_equals(&a, &one)?;
        assert_eq!(a_inv.value()?, a.value()?.inverse().unwrap());
        assert_eq!(a_inv.value()?, a_native.inverse().unwrap());

        let a_b_inv = a.mul_by_inverse(&b)?;
        a_b_inv.mul_equals(&b, &a)?;
        assert_eq!(a_b_inv.value()?, a_native * b_native.inverse().unwrap());

        // a * a * a = a^3
        let bits = BitIterator::new([0x3])
            .map(Boolean::constant)
            .collect::<Vec<_>>();
        assert_eq!(a_native.pow([0x3]), a.pow(&bits)?.value()?);

        // a * a * a = a^3
        assert_eq!(a_native.pow([0x3]), a.pow_by_constant(&[3])?.value()?);

        // a * a * a = a^3
        let mut constants = [F::zero(); 4];
        for c in &mut constants {
            *c = UniformRand::rand(&mut test_rng());
        }
        let bits = [
            Boolean::<AF::ConstraintF>::constant(false),
            Boolean::constant(true),
        ];
        let lookup_result: FV<F, AF> = FV::two_bit_lookup(&bits, constants.as_ref())?;
        assert_eq!(lookup_result.value()?, constants[2]);

        let negone: F = UniformRand::rand(&mut test_rng());

        let n = FV::<F, AF>::new_witness(cs.ns("alloc new var"), || Ok(negone)).unwrap();
        let _ = n.to_bytes()?;
        let _ = n.to_non_unique_bytes()?;

        let ab_false = &a + (FV::from(Boolean::Constant(false)) * b_native);
        assert_eq!(ab_false.value()?, a_native);
        let ab_true = &a + (FV::from(Boolean::Constant(true)) * b_native);
        assert_eq!(ab_true.value()?, a_native + &b_native);

        if !cs.is_satisfied().unwrap() {
            println!("{:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied().unwrap());
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn frobenius_tests<F: Field, AF: AllocatedField<F>>(
        maxpower: usize,
    ) -> Result<(), SynthesisError> {
        let cs = ConstraintSystem::<AF::ConstraintF>::new_ref();
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
        for i in 0..=maxpower {
            let mut a = F::rand(&mut rng);
            let mut a_gadget = AF::new_witness(cs.ns(format!("a_gadget_{:?}", i)), || Ok(a))?;
            a_gadget.frobenius_map_in_place(i)?;
            a.frobenius_map(i);

            assert_eq!(a_gadget.value()?, a);
        }

        assert!(cs.is_satisfied().unwrap());
        Ok(())
    }
}
