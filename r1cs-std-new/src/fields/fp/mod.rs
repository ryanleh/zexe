use algebra::{bytes::ToBytes, FpParameters, PrimeField};
use r1cs_core::{lc, ConstraintSystemRef, LinearCombination, SynthesisError, Variable};

use core::borrow::Borrow;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::fields::AllocatedField;
use crate::{boolean::AllocatedBit, prelude::*, Assignment, Vec};

// pub mod cmp;

#[derive(Debug, Clone)]
pub struct AllocatedFp<F: PrimeField> {
    pub value: Option<F>,
    pub variable: Variable,
    cs: ConstraintSystemRef<F>,
}

impl<F: PrimeField> AllocatedFp<F> {
    pub fn new(value: Option<F>, variable: Variable, cs: ConstraintSystemRef<F>) -> Self {
        Self {
            value,
            variable,
            cs,
        }
    }
}

impl<F: PrimeField> R1CSVar<F> for AllocatedFp<F> {
    fn cs(&self) -> Option<ConstraintSystemRef<F>> {
        Some(self.cs.clone())
    }
}

impl<F: PrimeField> From<Boolean<F>> for AllocatedFp<F> {
    fn from(other: Boolean<F>) -> Self {
        if let Some(cs) = other.cs() {
            let variable = cs.new_lc(other.lc());
            Self::new(other.value().ok().map(|b| F::from(b as u8)), variable, cs)
        } else {
            unreachable!("Cannot create a constant value")
        }
    }
}

impl<F: PrimeField> AllocatedField<F> for AllocatedFp<F> {
    type ConstraintF = F;

    fn value(&self) -> Result<F, SynthesisError> {
        self.value.get()
    }

    fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        let value = match (self.value, other.value) {
            (Some(val1), Some(val2)) => Some(val1 + &val2),
            (..) => None,
        };

        let variable = self.cs.new_lc(lc!() + self.variable + other.variable);
        Ok(AllocatedFp::new(value, variable, self.cs.clone()))
    }

    fn sub(&self, other: &Self) -> Result<Self, SynthesisError> {
        let value = match (self.value, other.value) {
            (Some(val1), Some(val2)) => Some(val1 - &val2),
            (..) => None,
        };

        let variable = self.cs.new_lc(lc!() + self.variable - other.variable);
        Ok(AllocatedFp::new(value, variable, self.cs.clone()))
    }

    fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        let product = AllocatedFp::alloc_witness(self.cs.clone(), || {
            Ok(self.value.get()? * &other.value.get()?)
        })
        .unwrap();
        self.cs
            .enforce_constraint(
                lc!() + self.variable,
                lc!() + other.variable,
                lc!() + product.variable,
            )
            .unwrap();
        Ok(product)
    }

    fn add_constant(&self, other: F) -> Result<Self, SynthesisError> {
        let value = self.value.map(|val| val + other);
        let variable = self
            .cs
            .new_lc(lc!() + self.variable + (other, Variable::One));
        Ok(AllocatedFp::new(value, variable, self.cs.clone()))
    }

    fn sub_constant(&self, other: F) -> Result<Self, SynthesisError> {
        let value = self.value.map(|val| val - other);
        let variable = self
            .cs
            .new_lc(lc!() + self.variable - (other, Variable::One));
        Ok(AllocatedFp::new(value, variable, self.cs.clone()))
    }

    fn mul_constant(&self, other: F) -> Result<Self, SynthesisError> {
        let value = self.value.map(|val| val * other);
        let variable = self.cs.new_lc(lc!() + (other, self.variable));
        Ok(AllocatedFp::new(value, variable, self.cs.clone()))
    }

    fn double(&self) -> Result<Self, SynthesisError> {
        let value = self.value.map(|val| val.double());
        let variable = self.cs.new_lc(lc!() + self.variable + self.variable);
        Ok(Self::new(value, variable, self.cs.clone()))
    }

    #[inline]
    fn negate(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.negate_in_place()?;
        Ok(result)
    }

    #[inline]
    fn negate_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        self.value.as_mut().map(|val| *val = -(*val));
        self.variable = self.cs.new_lc(lc!() - self.variable);
        Ok(self)
    }

    #[inline]
    fn inverse(&self) -> Result<Self, SynthesisError> {
        let inverse = Self::alloc_witness(self.cs.clone(), || {
            self.value
                .get()?
                .inverse()
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + inverse.variable,
            lc!() + Variable::One,
        )?;
        Ok(inverse)
    }

    fn frobenius_map(&self, _: usize) -> Result<Self, SynthesisError> {
        Ok(self.clone())
    }

    fn frobenius_map_in_place(&mut self, _: usize) -> Result<&mut Self, SynthesisError> {
        Ok(self)
    }

    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + other.variable,
            lc!() + result.variable,
        )
    }

    fn square_equals(&self, result: &Self) -> Result<(), SynthesisError> {
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + self.variable,
            lc!() + result.variable,
        )
    }
}

/****************************************************************************/
/****************************************************************************/

impl<'a, F: PrimeField> Add<&'a AllocatedFp<F>> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn add(self, other: Self) -> AllocatedFp<F> {
        AllocatedField::add(self, other).unwrap()
    }
}

impl<'a, F: PrimeField> Sub<&'a AllocatedFp<F>> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn sub(self, other: Self) -> AllocatedFp<F> {
        AllocatedField::sub(self, other).unwrap()
    }
}

impl<'a, F: PrimeField> Mul<&'a AllocatedFp<F>> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn mul(self, other: Self) -> AllocatedFp<F> {
        AllocatedField::mul(self, other).unwrap()
    }
}

impl<'a, F: PrimeField> AddAssign<&'a AllocatedFp<F>> for AllocatedFp<F> {
    fn add_assign(&mut self, other: &'a Self) {
        let result = &*self + other;
        *self = result
    }
}

impl<'a, F: PrimeField> SubAssign<&'a AllocatedFp<F>> for AllocatedFp<F> {
    fn sub_assign(&mut self, other: &'a Self) {
        let result = &*self - other;
        *self = result
    }
}

impl<'a, F: PrimeField> MulAssign<&'a AllocatedFp<F>> for AllocatedFp<F> {
    fn mul_assign(&mut self, other: &'a Self) {
        let result = &*self - other;
        *self = result
    }
}

/****************************************************************************/
/****************************************************************************/

impl<'a, F: PrimeField> Add<F> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn add(self, other: F) -> AllocatedFp<F> {
        self.add_constant(other).unwrap()
    }
}

impl<'a, F: PrimeField> Sub<F> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn sub(self, other: F) -> AllocatedFp<F> {
        self.sub_constant(other).unwrap()
    }
}

impl<'a, F: PrimeField> Mul<F> for &'a AllocatedFp<F> {
    type Output = AllocatedFp<F>;

    fn mul(self, other: F) -> AllocatedFp<F> {
        self.mul_constant(other).unwrap()
    }
}

impl<F: PrimeField> AddAssign<F> for AllocatedFp<F> {
    fn add_assign(&mut self, other: F) {
        let result = &*self + other;
        *self = result
    }
}

impl<F: PrimeField> SubAssign<F> for AllocatedFp<F> {
    fn sub_assign(&mut self, other: F) {
        let result = &*self - other;
        *self = result
    }
}

impl<F: PrimeField> MulAssign<F> for AllocatedFp<F> {
    fn mul_assign(&mut self, other: F) {
        let result = &*self - other;
        *self = result
    }
}

/****************************************************************************/
/****************************************************************************/

/****************************************************************************/
/****************************************************************************/

impl<F: PrimeField> EqGadget<F> for AllocatedFp<F> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let is_equal =
            Boolean::alloc_witness(self.cs.clone(), || Ok(self.value()? == other.value()?))?;

        let multiplier = Self::alloc_witness(self.cs.clone(), || {
            if is_equal.value()? {
                let difference = self.value()? - other.value()?;
                difference
                    .inverse()
                    .ok_or(SynthesisError::AssignmentMissing)
            } else {
                Ok(F::zero())
            }
        })?;
        self.cs.enforce_constraint(
            lc!() + self.variable - other.variable,
            lc!() + multiplier.variable,
            is_equal.lc(),
        )?;
        Ok(is_equal)
    }

    #[inline]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.cs.enforce_constraint(
            lc!() + self.variable - other.variable,
            lc!() + should_enforce.lc(),
            lc!(),
        )
    }

    #[inline]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        let multiplier = Self::alloc_witness(self.cs.clone(), || {
            if should_enforce.value()? {
                let difference = self.value()? - other.value()?;
                difference
                    .inverse()
                    .ok_or(SynthesisError::AssignmentMissing)
            } else {
                Ok(F::zero())
            }
        })?;

        self.cs.enforce_constraint(
            lc!() + self.variable - other.variable,
            lc!() + multiplier.variable,
            should_enforce.lc(),
        )?;
        Ok(())
    }
}

impl<F: PrimeField> ToBitsGadget<F> for AllocatedFp<F> {
    /// Outputs the unique bit-wise decomposition of `self` in *big-endian*
    /// form.
    fn to_bits(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let bits = self.to_non_unique_bits()?;
        Boolean::enforce_in_field(&bits)?;
        Ok(bits)
    }

    fn to_non_unique_bits(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = self.cs.clone();
        let num_bits = F::Params::MODULUS_BITS;
        use algebra::BitIterator;
        let bit_values = match self.value {
            Some(value) => {
                let mut field_char = BitIterator::new(F::characteristic());
                let mut tmp = Vec::with_capacity(num_bits as usize);
                let mut found_one = false;
                for b in BitIterator::new(value.into_repr()) {
                    // Skip leading bits
                    found_one |= field_char.next().unwrap();
                    if !found_one {
                        continue;
                    }

                    tmp.push(Some(b));
                }

                assert_eq!(tmp.len(), num_bits as usize);

                tmp
            }
            None => vec![None; num_bits as usize],
        };

        let mut bits = vec![];
        for b in bit_values {
            bits.push(AllocatedBit::alloc_witness(cs.clone(), || b.get())?);
        }

        let mut lc = LinearCombination::zero();
        let mut coeff = F::one();

        for bit in bits.iter().rev() {
            lc += (coeff, bit.variable());

            coeff.double_in_place();
        }

        lc = lc - &self.variable;

        cs.enforce_constraint(lc!(), lc!(), lc)?;

        Ok(bits.into_iter().map(Boolean::from).collect())
    }
}

impl<F: PrimeField> ToBytesGadget<F> for AllocatedFp<F> {
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let bytes = self.to_non_unique_bytes()?;
        Boolean::enforce_in_field(
            &bytes.iter()
                .flat_map(|b| b.into_bits_le())
                // This reverse maps the bits into big-endian form, as required by `enforce_in_field`.
                .rev()
                .collect::<Vec<_>>(),
        )?;

        Ok(bytes)
    }

    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let cs = self.cs.clone();
        let byte_values = match self.value {
            Some(value) => to_bytes![&value.into_repr()]?
                .into_iter()
                .map(Some)
                .collect::<Vec<_>>(),
            None => {
                let default = F::default();
                let default_len = to_bytes![&default].unwrap().len();
                vec![None; default_len]
            }
        };

        let bytes = UInt8::alloc_witness_vec(cs.clone(), &byte_values)?;

        let mut lc = LinearCombination::zero();
        let mut coeff = F::one();

        for bit in bytes.iter().flat_map(|b| b.bits.clone()) {
            match bit {
                Boolean::Is(bit) => {
                    lc += (coeff, bit.variable());
                    coeff.double_in_place();
                }
                Boolean::Constant(_) | Boolean::Not(_) => unreachable!(),
            }
        }

        lc = lc - &self.variable;

        cs.enforce_constraint(lc!(), lc!(), lc)?;

        Ok(bytes)
    }
}

impl<F: PrimeField> CondSelectGadget<F> for AllocatedFp<F> {
    #[inline]
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        match cond {
            Boolean::Constant(true) => Ok(true_value.clone()),
            Boolean::Constant(false) => Ok(false_value.clone()),
            _ => {
                let cs = cond.cs().unwrap();
                let result = Self::alloc_witness(cs.clone(), || {
                    cond.value()
                        .and_then(|c| if c { true_value } else { false_value }.value())
                })?;
                // a = self; b = other; c = cond;
                //
                // r = c * a + (1  - c) * b
                // r = b + c * (a - b)
                // c * (a - b) = r - b
                cs.enforce_constraint(
                    cond.lc(),
                    lc!() + true_value.variable - false_value.variable,
                    lc!() + result.variable - false_value.variable,
                )?;

                Ok(result)
            }
        }
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<F: PrimeField> TwoBitLookupGadget<F> for AllocatedFp<F> {
    type TableConstant = F;
    fn two_bit_lookup(b: &[Boolean<F>], c: &[Self::TableConstant]) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 2);
        debug_assert!(c.len() == 4);
        if let Some(cs) = b.cs() {
            let result = Self::alloc_witness(cs.clone(), || {
                let lsb = b[0].value()? as usize;
                let msb = b[1].value()? as usize;
                let index = lsb + (1 << msb);
                Ok(c[index])
            })?;
            let one = Variable::One;
            cs.enforce_constraint(
                lc!() + b[1].lc() * (c[3] - &c[2] - &c[1] + &c[0]) + (c[1] - &c[0], one),
                lc!() + b[0].lc(),
                lc!() + result.variable - (c[0], one) + b[1].lc() * (c[0] - &c[2]),
            )?;

            Ok(result)
        } else {
            unreachable!("must provide a way to obtain a ConstraintSystemRef")
        }
    }
}

impl<F: PrimeField> ThreeBitCondNegLookupGadget<F> for AllocatedFp<F> {
    type TableConstant = F;

    fn three_bit_cond_neg_lookup(
        b: &[Boolean<F>],
        b0b1: &Boolean<F>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 3);
        debug_assert!(c.len() == 4);

        if let Some(cs) = b.cs() {
            let result = Self::alloc_witness(cs.clone(), || {
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
                Ok(y)
            })?;

            let y_lc = b0b1.lc() * (c[3] - &c[2] - &c[1] + &c[0])
                + b[0].lc() * (c[1] - &c[0])
                + b[1].lc() * (c[2] - &c[0])
                + (c[0], Variable::One);
            cs.enforce_constraint(
                y_lc.clone() + y_lc.clone(),
                b[2].lc(),
                y_lc.clone() - result.variable,
            )?;

            Ok(result)
        } else {
            unreachable!("must provide a way to obtain a ConstraintSystemRef")
        }
    }
}

impl<F: PrimeField> AllocVar<F, F> for AllocatedFp<F> {
    #[inline]
    fn alloc_constant(
        cs: ConstraintSystemRef<F>,
        t: impl Borrow<F>,
    ) -> Result<Self, SynthesisError> {
        let v = *t.borrow();
        let lc = cs.new_lc(lc!() + (v, Variable::One));
        Ok(Self::new(Some(v), lc, cs))
    }

    #[inline]
    fn alloc_witness_checked<FN, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        let mut value = None;
        let variable = cs.new_witness_variable(|| {
            value = Some(*value_gen()?.borrow());
            value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        Ok(Self::new(value, variable, cs.clone()))
    }

    #[inline]
    fn alloc_input_checked<FN, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        let mut value = None;
        let variable = cs.new_input_variable(|| {
            value = Some(*value_gen()?.borrow());
            value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        Ok(Self::new(value, variable, cs.clone()))
    }
}
