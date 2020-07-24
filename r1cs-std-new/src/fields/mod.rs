use algebra::Field;
use core::{
    fmt::Debug,
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};
use r1cs_core::SynthesisError;

use crate::{prelude::*, Assignment};

#[macro_use]
pub mod macros;
pub mod fp;
// pub mod field_var;
// pub mod fp12;
// pub mod fp2;
pub mod cubic_extension;
pub mod quadratic_extension;
// pub mod fp3;
// pub mod fp4;
// pub mod fp6_2over3;
// pub mod fp6_3over2;

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
        let result = Self::alloc_witness(self.cs().unwrap(), || {
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

    use crate::{prelude::*, test_constraint_system::TestConstraintSystem, Vec};
    use algebra::{test_rng, BitIterator, Field, UniformRand};
    use r1cs_core::ConstraintSystem;

    #[allow(dead_code)]
    pub(crate) fn field_test<FE: Field, ConstraintF: Field, F: FieldGadget<FE, ConstraintF>>() {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let mut rng = test_rng();
        let a_native = FE::rand(&mut rng);
        let b_native = FE::rand(&mut rng);
        let a = F::alloc(&mut cs.ns(|| "generate_a"), || Ok(a_native)).unwrap();
        let b = F::alloc(&mut cs.ns(|| "generate_b"), || Ok(b_native)).unwrap();
        let b_const = F::alloc_constant(&mut cs.ns(|| "generate_b_as_constant"), b_native).unwrap();

        let zero = F::zero(cs.ns(|| "zero")).unwrap();
        let zero_native = zero.value().unwrap();
        zero.enforce_equal(&mut cs.ns(|| "zero_equals?"), &zero)
            .unwrap();
        assert_eq!(zero, zero);

        let one = F::one(cs.ns(|| "one")).unwrap();
        let one_native = one.value().unwrap();
        assert_eq!(one, one);
        one.enforce_equal(&mut cs.ns(|| "one_equals?"), &one)
            .unwrap();
        assert_ne!(one, zero);

        let one_dup = zero.add(cs.ns(|| "zero_plus_one"), &one).unwrap();
        one_dup
            .enforce_equal(&mut cs.ns(|| "one_plus_zero_equals"), &one)
            .unwrap();
        assert_eq!(one_dup, one);

        let two = one.add(cs.ns(|| "one_plus_one"), &one).unwrap();
        two.enforce_equal(&mut cs.ns(|| "two_equals?"), &two)
            .unwrap();
        assert_eq!(two, two);
        assert_ne!(zero, two);
        assert_ne!(one, two);

        // a == a
        assert_eq!(a, a);

        // a + 0 = a
        let a_plus_zero = a.add(cs.ns(|| "a_plus_zero"), &zero).unwrap();
        assert_eq!(a_plus_zero, a);
        assert_eq!(a_plus_zero.value().unwrap(), a_native);
        a_plus_zero
            .enforce_equal(&mut cs.ns(|| "a_plus_zero_equals?"), &a)
            .unwrap();

        // a - 0 = a
        let a_minus_zero = a.sub(cs.ns(|| "a_minus_zero"), &zero).unwrap();
        assert_eq!(a_minus_zero, a);
        assert_eq!(a_minus_zero.value().unwrap(), a_native);
        a_minus_zero
            .enforce_equal(&mut cs.ns(|| "a_minus_zero_equals?"), &a)
            .unwrap();

        // a - a = 0
        let a_minus_a = a.sub(cs.ns(|| "a_minus_a"), &a).unwrap();
        assert_eq!(a_minus_a, zero);
        assert_eq!(a_minus_a.value().unwrap(), zero_native);
        a_minus_a
            .enforce_equal(&mut cs.ns(|| "a_minus_a_equals?"), &zero)
            .unwrap();

        // a + b = b + a
        let a_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
        let b_a = b.add(cs.ns(|| "b_plus_a"), &a).unwrap();
        assert_eq!(a_b, b_a);
        assert_eq!(a_b.value().unwrap(), a_native + &b_native);
        a_b.enforce_equal(&mut cs.ns(|| "a+b == b+a"), &b_a)
            .unwrap();

        // (a + b) + a = a + (b + a)
        let ab_a = a_b.add(cs.ns(|| "a_b_plus_a"), &a).unwrap();
        let a_ba = a.add(cs.ns(|| "a_plus_b_a"), &b_a).unwrap();
        assert_eq!(ab_a, a_ba);
        assert_eq!(ab_a.value().unwrap(), a_native + &b_native + &a_native);
        ab_a.enforce_equal(&mut cs.ns(|| "a+b + a == a+ b+a"), &a_ba)
            .unwrap();

        let b_times_a_plus_b = a_b.mul(cs.ns(|| "b * (a + b)"), &b).unwrap();
        let b_times_b_plus_a = b_a.mul(cs.ns(|| "b * (b + a)"), &b).unwrap();
        assert_eq!(b_times_b_plus_a, b_times_a_plus_b);
        assert_eq!(
            b_times_a_plus_b.value().unwrap(),
            b_native * &(b_native + &a_native)
        );
        assert_eq!(
            b_times_a_plus_b.value().unwrap(),
            (b_native + &a_native) * &b_native
        );
        assert_eq!(
            b_times_a_plus_b.value().unwrap(),
            (a_native + &b_native) * &b_native
        );
        b_times_b_plus_a
            .enforce_equal(&mut cs.ns(|| "b*(a+b) == b * (b+a)"), &b_times_a_plus_b)
            .unwrap();

        // a * 0 = 0
        assert_eq!(a.mul(cs.ns(|| "a_times_zero"), &zero).unwrap(), zero);

        // a * 1 = a
        assert_eq!(a.mul(cs.ns(|| "a_times_one"), &one).unwrap(), a);
        assert_eq!(
            a.mul(cs.ns(|| "a_times_one2"), &one)
                .unwrap()
                .value()
                .unwrap(),
            a_native * &one_native
        );

        // a * b = b * a
        let ab = a.mul(cs.ns(|| "a_times_b"), &b).unwrap();
        let ba = b.mul(cs.ns(|| "b_times_a"), &a).unwrap();
        assert_eq!(ab, ba);
        assert_eq!(ab.value().unwrap(), a_native * &b_native);

        let ab_const = a.mul(cs.ns(|| "a_times_b_const"), &b_const).unwrap();
        let b_const_a = b_const.mul(cs.ns(|| "b_const_times_a"), &a).unwrap();
        assert_eq!(ab_const, b_const_a);
        assert_eq!(ab_const, ab);
        assert_eq!(ab_const.value().unwrap(), a_native * &b_native);

        // (a * b) * a = a * (b * a)
        let ab_a = ab.mul(cs.ns(|| "ab_times_a"), &a).unwrap();
        let a_ba = a.mul(cs.ns(|| "a_times_ba"), &ba).unwrap();
        assert_eq!(ab_a, a_ba);
        assert_eq!(ab_a.value().unwrap(), a_native * &b_native * &a_native);

        let aa = a.mul(cs.ns(|| "a * a"), &a).unwrap();
        let a_squared = a.square(cs.ns(|| "a^2")).unwrap();
        a_squared
            .enforce_equal(&mut cs.ns(|| "a^2 == a*a"), &aa)
            .unwrap();
        assert_eq!(aa, a_squared);
        assert_eq!(aa.value().unwrap(), a_native.square());

        let aa = a
            .mul_by_constant(cs.ns(|| "a * a via mul_by_const"), &a.value().unwrap())
            .unwrap();
        a_squared
            .enforce_equal(&mut cs.ns(|| "a^2 == a*a via mul_by_const"), &aa)
            .unwrap();
        assert_eq!(aa, a_squared);
        assert_eq!(aa.value().unwrap(), a_native.square());

        let a_b2 = a
            .add_constant(cs.ns(|| "a + b via add_const"), &b.value().unwrap())
            .unwrap();
        a_b.enforce_equal(&mut cs.ns(|| "a + b == a + b via add_const"), &a_b2)
            .unwrap();
        assert_eq!(a_b, a_b2);

        let a_inv = a.inverse(cs.ns(|| "a_inv")).unwrap();
        a_inv
            .mul_equals(cs.ns(|| "check a_inv * a = 1"), &a, &one)
            .unwrap();
        assert_eq!(
            a_inv.value().unwrap(),
            a.value().unwrap().inverse().unwrap()
        );
        assert_eq!(a_inv.value().unwrap(), a_native.inverse().unwrap());

        let a_b_inv = a.mul_by_inverse(cs.ns(|| "a_b_inv"), &b).unwrap();
        a_b_inv
            .mul_equals(cs.ns(|| "check a_b_inv * b = a"), &b, &a)
            .unwrap();
        assert_eq!(
            a_b_inv.value().unwrap(),
            a_native * b_native.inverse().unwrap()
        );

        // a * a * a = a^3
        let bits = BitIterator::new([0x3])
            .map(Boolean::constant)
            .collect::<Vec<_>>();
        assert_eq!(
            a_native * &(a_native * &a_native),
            a.pow(cs.ns(|| "test_pow"), &bits).unwrap().value().unwrap()
        );

        // a * a * a = a^3
        assert_eq!(
            a_native * &(a_native * &a_native),
            a.pow_by_constant(cs.ns(|| "test_constant_pow"), &[3])
                .unwrap()
                .value()
                .unwrap()
        );

        // a * a * a = a^3
        let mut constants = [FE::zero(); 4];
        for c in &mut constants {
            *c = UniformRand::rand(&mut test_rng());
            println!("Current c[i]: {:?}", c);
        }
        let bits = [Boolean::constant(false), Boolean::constant(true)];
        let lookup_result =
            F::two_bit_lookup(cs.ns(|| "Lookup"), &bits, constants.as_ref()).unwrap();
        assert_eq!(lookup_result.value().unwrap(), constants[2]);

        let negone: FE = UniformRand::rand(&mut test_rng());

        let n = F::alloc(&mut cs.ns(|| "alloc new var"), || Ok(negone)).unwrap();
        let _ = n.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
        let _ = n
            .to_non_unique_bytes(&mut cs.ns(|| "ToBytes Strict"))
            .unwrap();

        let ab_false = a
            .conditionally_add_constant(
                cs.ns(|| "Add bool with coeff false"),
                &Boolean::constant(false),
                b_native,
            )
            .unwrap();
        assert_eq!(ab_false.value().unwrap(), a_native);
        let ab_true = a
            .conditionally_add_constant(
                cs.ns(|| "Add bool with coeff true"),
                &Boolean::constant(true),
                b_native,
            )
            .unwrap();
        assert_eq!(ab_true.value().unwrap(), a_native + &b_native);

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }

    #[allow(dead_code)]
    pub(crate) fn frobenius_tests<
        FE: Field,
        ConstraintF: Field,
        F: FieldGadget<FE, ConstraintF>,
    >(
        maxpower: usize,
    ) {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
        for i in 0..=maxpower {
            let mut a = FE::rand(&mut rng);
            let mut a_gadget = F::alloc(cs.ns(|| format!("a_gadget_{:?}", i)), || Ok(a)).unwrap();
            a_gadget = a_gadget
                .frobenius_map(cs.ns(|| format!("frob_map_{}", i)), i)
                .unwrap();
            a.frobenius_map(i);

            assert_eq!(a_gadget.value().unwrap(), a);
        }

        assert!(cs.is_satisfied());
    }
}
