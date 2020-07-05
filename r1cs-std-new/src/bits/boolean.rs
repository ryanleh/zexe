use algebra::{BitIterator, Field};

use crate::{prelude::*, Assignment, Vec};
use core::borrow::Borrow;
use r1cs_core::{lc, ConstraintSystemRef, LinearCombination, SynthesisError, Variable};

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllocatedBit<F: Field> {
    variable: Variable,
    value: Option<bool>,
    cs: ConstraintSystemRef<F>,
}

// TODO: bool to field
fn bool_to_f<F: Field>(val: bool) -> F {
    if val {
        F::one()
    } else {
        F::zero()
    }
}

impl<F: Field> AllocatedBit<F> {
    /// Get the assigned value for `self`.
    pub fn value(&self) -> Result<bool, SynthesisError> {
        self.value.get()
    }

    /// Get the R1CS variable for `self`.
    pub fn variable(&self) -> Variable {
        self.variable
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::alloc_witness(self.cs.clone(), || Ok(self.value()? ^ b.value()?))?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c
        self.cs.enforce_constraint(
            lc!() + self.variable + self.variable,
            lc!() + b.variable,
            lc!() + self.variable + b.variable - result.variable,
        )?;

        Ok(result)
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::alloc_witness(self.cs.clone(), || Ok(self.value()? & b.value()?))?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }

    /// Performs an OR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn or(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::alloc_witness(self.cs.clone(), || Ok(self.value()? | b.value()?))?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        self.cs.enforce_constraint(
            lc!() + Variable::One - self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + Variable::One - result.variable,
        )?;

        Ok(result)
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::alloc_witness(self.cs.clone(), || Ok(self.value()? & !b.value()?))?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::alloc_witness(self.cs.clone(), || Ok(!(self.value()? | b.value()?)))?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        self.cs.enforce_constraint(
            lc!() + Variable::One - self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }
}

impl<F: Field> R1CSVar<F> for AllocatedBit<F> {
    fn cs(&self) -> Option<ConstraintSystemRef<F>> {
        Some(self.cs.clone())
    }
}

impl<F: Field> AllocVar<bool, F> for AllocatedBit<F> {
    fn alloc_constant(
        cs: ConstraintSystemRef<F>,
        t: impl Borrow<bool>,
    ) -> Result<Self, SynthesisError> {
        let value = *t.borrow();
        let variable = if value { Variable::One } else { Variable::Zero };
        Ok(Self {
            variable,
            value: Some(value),
            cs,
        })
    }

    fn alloc_witness_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        let mut value = None;
        let variable = cs.new_witness_variable(|| {
            value = Some(*value_gen()?.borrow());
            value.get().map(bool_to_f)
        })?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce_named_constraint(
            "Booleanity check",
            lc!() + Variable::One - variable,
            lc!() + variable,
            lc!(),
        )?;

        Ok(Self {
            variable,
            value,
            cs,
        })
    }

    fn alloc_input_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        let mut value = None;
        let variable = cs.new_input_variable(|| {
            value = Some(*value_gen()?.borrow());
            value.get().map(bool_to_f)
        })?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce_named_constraint(
            "Booleanity check",
            lc!() + Variable::One - variable,
            lc!() + variable,
            lc!(),
        )?;

        Ok(Self {
            variable,
            value,
            cs,
        })
    }
}

impl<F: Field> CondSelectGadget<F> for AllocatedBit<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_val: &Self,
        false_val: &Self,
    ) -> Result<Self, SynthesisError> {
        let res = Boolean::conditionally_select(
            cond,
            &true_val.clone().into(),
            &false_val.clone().into(),
        )?;
        match res {
            Boolean::Is(a) => Ok(a),
            _ => unreachable!("Impossible"),
        }
    }
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Boolean<F: Field> {
    /// Existential view of the boolean variable
    Is(AllocatedBit<F>),
    /// Negated view of the boolean variable
    Not(AllocatedBit<F>),
    /// Constant (not an allocated variable)
    Constant(bool),
}

impl<F: Field> R1CSVar<F> for Boolean<F> {
    fn cs(&self) -> Option<ConstraintSystemRef<F>> {
        match self {
            Self::Is(a) | Self::Not(a) => a.cs(),
            _ => None,
        }
    }
}

impl<F: Field> Boolean<F> {
    pub fn value(&self) -> Result<bool, SynthesisError> {
        match self {
            Boolean::Constant(c) => Ok(*c),
            Boolean::Is(ref v) => v.value(),
            Boolean::Not(ref v) => v.value().map(|b| !b),
        }
    }

    pub fn lc(&self) -> LinearCombination<F> {
        match self {
            Boolean::Constant(false) => lc!(),
            Boolean::Constant(true) => lc!() + Variable::One,
            Boolean::Is(v) => v.variable().into(),
            Boolean::Not(v) => lc!() + Variable::One - v.variable(),
        }
    }

    /// Construct a boolean vector from a vector of u8
    pub fn constant_vec_from_bytes(values: &[u8]) -> Vec<Self> {
        let mut input_bits = vec![];
        for input_byte in values {
            for bit_i in (0..8).rev() {
                input_bits.push(Self::Constant(((input_byte >> bit_i) & 1u8) == 1u8));
            }
        }
        input_bits
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match *self {
            Boolean::Constant(c) => Boolean::Constant(!c),
            Boolean::Is(ref v) => Boolean::Not(v.clone()),
            Boolean::Not(ref v) => Boolean::Is(v.clone()),
        }
    }
}
impl<F: Field> Boolean<F> {
    /// Perform XOR over two boolean operands
    pub fn xor<'a>(&'a self, b: &'a Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, b) {
            (&Constant(false), x) | (x, &Constant(false)) => Ok(x.clone()),
            (&Constant(true), x) | (x, &Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Is(_), not @ &Not(_)) | (not @ &Not(_), is @ &Is(_)) => {
                Ok(is.xor(&not.not())?.not())
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Is(ref a), &Is(ref b)) | (&Not(ref a), &Not(ref b)) => Ok(Is(a.xor(b)?)),
        }
    }

    /// Perform OR over two boolean operands
    pub fn or<'a>(&'a self, b: &'a Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, b) {
            (&Constant(false), x) | (x, &Constant(false)) => Ok(x.clone()),
            (&Constant(true), _) | (_, &Constant(true)) => Ok(Constant(true)),
            // a OR b = NOT ((NOT a) AND b)
            (a @ &Is(_), b @ &Not(_)) | (b @ &Not(_), a @ &Is(_)) | (b @ &Not(_), a @ &Not(_)) => {
                Ok(a.not().and(&b.not())?.not())
            }
            (&Is(ref a), &Is(ref b)) => a.or(b).map(From::from),
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a>(&'a self, b: &'a Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, b) {
            // false AND x is always false
            (&Constant(false), _) | (_, &Constant(false)) => Ok(Constant(false)),
            // true AND x is always x
            (&Constant(true), x) | (x, &Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Is(ref is), &Not(ref not)) | (&Not(ref not), &Is(ref is)) => Ok(Is(is.and_not(not)?)),
            // (NOT a) AND (NOT b) = a NOR b
            (&Not(ref a), &Not(ref b)) => Ok(Is(a.nor(b)?)),
            // a AND b
            (&Is(ref a), &Is(ref b)) => Ok(Is(a.and(b)?)),
        }
    }

    pub fn kary_and(bits: &[Self]) -> Result<Self, SynthesisError> {
        assert!(!bits.is_empty());
        let mut cur: Option<Self> = None;
        for next in bits {
            cur = if let Some(b) = cur {
                Some(b.and(next)?)
            } else {
                Some(next.clone())
            };
        }

        Ok(cur.expect("should not be 0"))
    }

    pub fn kary_or(bits: &[Self]) -> Result<Self, SynthesisError> {
        assert!(!bits.is_empty());
        let mut cur: Option<Self> = None;
        for next in bits {
            cur = if let Some(b) = cur {
                Some(b.or(next)?)
            } else {
                Some(next.clone())
            };
        }

        Ok(cur.expect("should not be 0"))
    }

    pub fn kary_nand(bits: &[Self]) -> Result<Self, SynthesisError> {
        Ok(Self::kary_and(bits)?.not())
    }

    /// Assert that at least one input is false.
    fn enforce_kary_nand(bits: &[Self]) -> Result<(), SynthesisError> {
        use Boolean::*;
        let r = Self::kary_nand(bits)?;
        match r {
            Constant(true) => Ok(()),
            Constant(false) => Err(SynthesisError::AssignmentMissing),
            Is(_) | Not(_) => r.cs().unwrap().enforce_constraint(
                r.lc(),
                lc!() + Variable::One,
                lc!() + Variable::One,
            ),
        }
    }

    /// Asserts that this bit_gadget representation is "in
    /// the field" when interpreted in big endian.
    pub fn enforce_in_field(bits: &[Self]) -> Result<(), SynthesisError> {
        // b = char() - 1
        let mut b = F::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1;
        let run = Self::enforce_smaller_or_equal_than(bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(())
    }

    /// Asserts that this bit_gadget representation is smaller
    /// or equal than the provided element
    pub fn enforce_smaller_or_equal_than(
        bits: &[Self],
        element: impl AsRef<[u64]>,
    ) -> Result<Vec<Self>, SynthesisError> {
        let mut bits_iter = bits.iter();
        let b: &[u64] = element.as_ref();

        // Runs of ones in r
        let mut last_run = Boolean::constant(true);
        let mut current_run = vec![];

        let mut found_one = false;

        let char_num_bits = {
            let mut leading_zeros = 0;
            let mut total_bits = 0;
            let mut found_one = false;
            for b in BitIterator::new(b.clone()) {
                total_bits += 1;
                if !b && !found_one {
                    leading_zeros += 1
                }
                if b {
                    found_one = true;
                }
            }

            total_bits - leading_zeros
        };

        if bits.len() > char_num_bits {
            let num_extra_bits = bits.len() - char_num_bits;
            let mut or_result = Boolean::constant(false);
            for should_be_zero in &bits[0..num_extra_bits] {
                or_result = or_result.or(should_be_zero)?;
                let _ = bits_iter.next().unwrap();
            }
            or_result.enforce_equal(&Boolean::constant(false))?;
        }

        for b in BitIterator::new(b) {
            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                continue;
            }

            let a = bits_iter.next().unwrap();

            if b {
                // This is part of a run of ones.
                current_run.push(a.clone());
            } else {
                if !current_run.is_empty() {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    current_run.push(last_run.clone());
                    last_run = Self::kary_and(&current_run)?;
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.
                //
                // Ergo, at least one of `last_run` and `a` must be false.
                Self::enforce_kary_nand(&[last_run.clone(), a.clone()])?;
            }
        }
        assert!(bits_iter.next().is_none());

        Ok(current_run)
    }
}

impl<F: Field> From<AllocatedBit<F>> for Boolean<F> {
    fn from(b: AllocatedBit<F>) -> Self {
        Boolean::Is(b)
    }
}

impl<F: Field> AllocVar<bool, F> for Boolean<F> {
    fn alloc_constant(
        _: ConstraintSystemRef<F>,
        t: impl Borrow<bool>,
    ) -> Result<Self, SynthesisError> {
        Ok(Boolean::constant(*t.borrow()))
    }

    fn alloc_witness_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        AllocatedBit::alloc_witness_checked(cs, value_gen).map(Boolean::from)
    }

    fn alloc_input_checked<Func, T>(
        cs: ConstraintSystemRef<F>,
        value_gen: Func,
    ) -> Result<Self, SynthesisError>
    where
        Func: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        AllocatedBit::alloc_input_checked(cs, value_gen).map(Boolean::from)
    }
}

impl<F: Field> EqGadget<F> for Boolean<F> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        use Boolean::*;
        match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => {
                Ok(Constant(true))
            }
            // false != true
            (Constant(_), Constant(_)) => Ok(Constant(false)),
            (_, _) => {
                let cs = self.cs().or(other.cs()).unwrap();
                let is_equal =
                    Self::alloc_witness(cs.clone(), || Ok(self.value()? == other.value()?))?;

                let multiplier = cs.new_witness_variable(|| {
                    if is_equal.value()? {
                        let diff = bool_to_f::<F>(self.value()?) - bool_to_f::<F>(other.value()?);
                        diff.inverse().ok_or(SynthesisError::AssignmentMissing)
                    } else {
                        Ok(F::zero())
                    }
                })?;
                cs.enforce_constraint(
                    lc!() + self.lc() - other.lc(),
                    lc!() + multiplier,
                    is_equal.lc(),
                )?;
                Ok(is_equal)
            }
        }
    }

    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;
        let difference = match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // false != true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
            // 1 - a
            (Constant(true), Is(a)) | (Is(a), Constant(true)) => lc!() + one - a.variable(),
            // a - 0 = a
            (Constant(false), Is(a)) | (Is(a), Constant(false)) => lc!() + a.variable(),
            // 1 - !a = 1 - (1 - a) = a
            (Constant(true), Not(a)) | (Not(a), Constant(true)) => lc!() + a.variable(),
            // !a - 0 = !a = 1 - a
            (Constant(false), Not(a)) | (Not(a), Constant(false)) => lc!() + one - a.variable(),
            // b - a,
            (Is(a), Is(b)) => lc!() + b.variable() - a.variable(),
            // !b - a = (1 - b) - a
            (Is(a), Not(b)) | (Not(b), Is(a)) => lc!() + one - b.variable() - a.variable(),
            // !b - !a = (1 - b) - (1 - a) = a - b,
            (Not(a), Not(b)) => lc!() + a.variable() - b.variable(),
        };

        if condition != &Constant(false) {
            let cs = self.cs().or(other.cs()).or(condition.cs()).unwrap();
            cs.enforce_constraint(lc!() + difference, condition.lc(), lc!())?;
        }
        Ok(())
    }

    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;
        let difference = match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // false != true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
            // 1 - a
            (Constant(true), Is(a)) | (Is(a), Constant(true)) => lc!() + one - a.variable(),
            // a - 0 = a
            (Constant(false), Is(a)) | (Is(a), Constant(false)) => lc!() + a.variable(),
            // 1 - !a = 1 - (1 - a) = a
            (Constant(true), Not(a)) | (Not(a), Constant(true)) => lc!() + a.variable(),
            // !a - 0 = !a = 1 - a
            (Constant(false), Not(a)) | (Not(a), Constant(false)) => lc!() + one - a.variable(),
            // b - a,
            (Is(a), Is(b)) => lc!() + b.variable() - a.variable(),
            // !b - a = (1 - b) - a
            (Is(a), Not(b)) | (Not(b), Is(a)) => lc!() + one - b.variable() - a.variable(),
            // !b - !a = (1 - b) - (1 - a) = a - b,
            (Not(a), Not(b)) => lc!() + a.variable() - b.variable(),
        };

        if should_enforce != &Constant(false) {
            let cs = self
                .cs()
                .or(other.cs())
                .or(should_enforce.cs())
                .ok_or(SynthesisError::UnconstrainedVariable)?;
            cs.enforce_constraint(difference, should_enforce.lc(), should_enforce.lc())?;
        }
        Ok(())
    }
}

impl<F: Field> ToBytesGadget<F> for Boolean<F> {
    /// Outputs `1u8` if `self` is true, and `0u8` otherwise.
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut bits = vec![Boolean::constant(false); 7];
        bits.push(self.clone());
        bits.reverse();
        let value = self.value().map(|val| val as u8).ok();
        let byte = UInt8 { bits, value };
        Ok(vec![byte])
    }
}

impl<F: Field> CondSelectGadget<F> for Boolean<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_val: &Self,
        false_val: &Self,
    ) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match cond {
            Constant(true) => Ok(true_val.clone()),
            Constant(false) => Ok(false_val.clone()),
            cond @ Not(_) => Self::conditionally_select(&cond.not(), false_val, true_val),
            cond @ Is(_) => match (true_val, false_val) {
                (x, &Constant(false)) => cond.and(x),
                (&Constant(false), x) => cond.not().and(x),
                (&Constant(true), x) => cond.or(x),
                (x, &Constant(true)) => cond.not().or(x),
                (a, b) => {
                    let cs = cond.cs().unwrap();
                    let result = Boolean::alloc_witness(cs.clone(), || {
                        let cond = cond.value()?;
                        Ok(if cond { a.value()? } else { b.value()? })
                    })?;
                    // a = self; b = other; c = cond;
                    //
                    // r = c * a + (1  - c) * b
                    // r = b + c * (a - b)
                    // c * (a - b) = r - b
                    cs.enforce_constraint(
                        cond.lc(),
                        lc!() + a.lc() - b.lc(),
                        lc!() + result.lc() - b.lc(),
                    )?;

                    Ok(result)
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::{AllocatedBit, Boolean};
    use crate::{prelude::*, test_constraint_system::TestConstraintSystem};
    use algebra::{bls12_381::Fr, BitIterator, Field, One, PrimeField, UniformRand, Zero};
    use core::str::FromStr;
    use r1cs_core::ConstraintSystem;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_boolean_to_byte() {
        for val in [true, false].iter() {
            let mut cs = TestConstraintSystem::<Fr>::new();
            let a: Boolean<F> = AllocatedBit::alloc(&mut cs, || Ok(*val)).unwrap().into();
            let bytes = a.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
            assert_eq!(bytes.len(), 1);
            let byte = &bytes[0];
            assert_eq!(byte.value.unwrap(), *val as u8);

            for (i, bit_gadget) in byte.bits.iter().enumerate() {
                assert_eq!(
                    bit_gadget.value().unwrap(),
                    (byte.value.unwrap() >> i) & 1 == 1
                );
            }
        }
    }

    #[test]
    fn test_allocated_bit() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        AllocatedBit::alloc(&mut cs, || Ok(true)).unwrap();
        assert!(cs.get("boolean") == Fr::one());
        assert!(cs.is_satisfied());
        cs.set("boolean", Fr::zero());
        assert!(cs.is_satisfied());
        cs.set("boolean", Fr::from_str("2").unwrap());
        assert!(!cs.is_satisfied());
        assert!(cs.which_is_unsatisfied() == Some("boolean constraint"));
    }

    #[test]
    fn test_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(*b_val)).unwrap();
                let c = AllocatedBit::xor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_or() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(*b_val)).unwrap();
                let c = AllocatedBit::or(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val | *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Fr::one() } else { Fr::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Fr::one() } else { Fr::zero() });
            }
        }
    }

    #[test]
    fn test_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(*b_val)).unwrap();
                let c = AllocatedBit::and(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Fr::one() } else { Fr::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Fr::one() } else { Fr::zero() });
                assert!(
                    cs.get("and result")
                        == if *a_val & *b_val {
                            Fr::one()
                        } else {
                            Fr::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and result",
                    if *a_val & *b_val {
                        Fr::zero()
                    } else {
                        Fr::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and_not() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(*b_val)).unwrap();
                let c = AllocatedBit::and_not(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Fr::one() } else { Fr::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Fr::one() } else { Fr::zero() });
                assert!(
                    cs.get("and not result")
                        == if *a_val & !*b_val {
                            Fr::one()
                        } else {
                            Fr::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and not result",
                    if *a_val & !*b_val {
                        Fr::zero()
                    } else {
                        Fr::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_nor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(*b_val)).unwrap();
                let c = AllocatedBit::nor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Fr::one() } else { Fr::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Fr::one() } else { Fr::zero() });
                assert!(
                    cs.get("nor result")
                        == if !*a_val & !*b_val {
                            Fr::one()
                        } else {
                            Fr::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "nor result",
                    if !*a_val & !*b_val {
                        Fr::zero()
                    } else {
                        Fr::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_enforce_equal() {
        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        let mut cs = TestConstraintSystem::<Fr>::new();

                        let mut a: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(a_bool))
                            .unwrap()
                            .into();
                        let mut b: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(b_bool))
                            .unwrap()
                            .into();

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        a.enforce_equal(&mut cs, &b).unwrap();

                        assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                    }
                }
            }
        }
    }

    #[test]
    fn test_conditional_enforce_equal() {
        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        let mut cs = TestConstraintSystem::<Fr>::new();

                        // First test if constraint system is satisfied
                        // when we do want to enforce the condition.
                        let mut a: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(a_bool))
                            .unwrap()
                            .into();
                        let mut b: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(b_bool))
                            .unwrap()
                            .into();

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        a.conditional_enforce_equal(&mut cs, &b, &Boolean::constant(true))
                            .unwrap();

                        assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));

                        // Now test if constraint system is satisfied even
                        // when we don't want to enforce the condition.
                        let mut cs = TestConstraintSystem::<Fr>::new();

                        let mut a: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "a"), || Ok(a_bool))
                            .unwrap()
                            .into();
                        let mut b: Boolean<F> = AllocatedBit::alloc(cs.ns(|| "b"), || Ok(b_bool))
                            .unwrap()
                            .into();

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        let false_cond = AllocatedBit::alloc(cs.ns(|| "cond"), || Ok(false))
                            .unwrap()
                            .into();
                        a.conditional_enforce_equal(&mut cs, &b, &false_cond)
                            .unwrap();

                        assert!(cs.is_satisfied());
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_negation() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, || Ok(true)).unwrap());

        match b {
            Boolean::Is(_) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Not(_) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Is(_) => {}
            _ => panic!("unexpected value"),
        }

        b = Boolean::constant(true);

        match b {
            Boolean::Constant(true) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Constant(false) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Constant(true) => {}
            _ => panic!("unexpected value"),
        }
    }

    #[derive(Copy, Clone, Debug)]
    enum OperandType {
        True,
        False,
        AllocatedTrue,
        AllocatedFalse,
        NegatedAllocatedTrue,
        NegatedAllocatedFalse,
    }

    #[test]
    fn test_boolean_xor() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Fr>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.ns(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::xor(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    _ => panic!("this should never be encountered"),
                }
            }
        }
    }

    #[test]
    fn test_boolean_cond_select() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for condition in variants.iter().cloned() {
            for first_operand in variants.iter().cloned() {
                for second_operand in variants.iter().cloned() {
                    let mut cs = TestConstraintSystem::<Fr>::new();

                    let cond;
                    let a;
                    let b;

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.ns(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap())
                                        .not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap())
                                        .not()
                                }
                            }
                        };

                        cond = dyn_construct(condition, "cond");
                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                    }

                    let before = cs.num_constraints();
                    let c = Boolean::conditionally_select(&mut cs, &cond, &a, &b).unwrap();
                    let after = cs.num_constraints();

                    assert!(
                        cs.is_satisfied(),
                        "failed with operands: cond: {:?}, a: {:?}, b: {:?}",
                        condition,
                        first_operand,
                        second_operand,
                    );
                    assert_eq!(
                        c.value(),
                        if cond.value().unwrap() {
                            a.value()
                        } else {
                            b.value()
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn test_boolean_or() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Fr>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.ns(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::or(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Constant(true)) => {}
                    (
                        OperandType::True,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Constant(true),
                    ) => {}
                    (
                        OperandType::True,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Constant(true),
                    ) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::True,
                        Boolean::Constant(true),
                    ) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::True,
                        Boolean::Constant(true),
                    ) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    _ => panic!(
                        "this should never be encountered, in case: (a = {:?}, b = {:?}, c = {:?})",
                        a, b, c
                    ),
                }
            }
        }
    }

    #[test]
    fn test_boolean_and() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Fr>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.ns(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, || Ok(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::and(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Constant(false),
                    ) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Fr::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Fr::one());
                        assert_eq!(v.value, Some(true));
                    }

                    _ => {
                        panic!(
                            "unexpected behavior at {:?} AND {:?}",
                            first_operand, second_operand
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_enforce_in_field() {
        {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let mut bits = vec![];
            for (i, b) in BitIterator::new(Fr::characteristic()).skip(1).enumerate() {
                bits.push(Boolean::from(
                    AllocatedBit::alloc(cs.ns(|| format!("bit_gadget {}", i)), || Ok(b)).unwrap(),
                ));
            }

            Boolean::enforce_in_field::<_, _, Fr>(&mut cs, &bits).unwrap();

            assert!(!cs.is_satisfied());
        }

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..1000 {
            let r = Fr::rand(&mut rng);
            let mut cs = TestConstraintSystem::<Fr>::new();

            let mut bits = vec![];
            for (i, b) in BitIterator::new(r.into_repr()).skip(1).enumerate() {
                bits.push(Boolean::from(
                    AllocatedBit::alloc(cs.ns(|| format!("bit_gadget {}", i)), || Ok(b)).unwrap(),
                ));
            }

            Boolean::enforce_in_field::<_, _, Fr>(&mut cs, &bits).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_enforce_nand() {
        {
            let mut cs = TestConstraintSystem::<Fr>::new();

            assert!(Boolean::enforce_kary_nand(&[Boolean::constant(false)]).is_ok());
            assert!(Boolean::enforce_kary_nand(&[Boolean::constant(true)]).is_err());
        }

        for i in 1..5 {
            // with every possible assignment for them
            for mut b in 0..(1 << i) {
                // with every possible negation
                for mut n in 0..(1 << i) {
                    let mut cs = TestConstraintSystem::<Fr>::new();

                    let mut expected = true;

                    let mut bits = vec![];
                    for j in 0..i {
                        expected &= b & 1 == 1;

                        if n & 1 == 1 {
                            bits.push(Boolean::from(
                                AllocatedBit::alloc(cs.ns(|| format!("bit_gadget {}", j)), || {
                                    Ok(b & 1 == 1)
                                })
                                .unwrap(),
                            ));
                        } else {
                            bits.push(
                                Boolean::from(
                                    AllocatedBit::alloc(
                                        cs.ns(|| format!("bit_gadget {}", j)),
                                        || Ok(b & 1 == 0),
                                    )
                                    .unwrap(),
                                )
                                .not(),
                            );
                        }

                        b >>= 1;
                        n >>= 1;
                    }

                    let expected = !expected;

                    Boolean::enforce_nand(&mut cs, &bits).unwrap();

                    if expected {
                        assert!(cs.is_satisfied());
                    } else {
                        assert!(!cs.is_satisfied());
                    }
                }
            }
        }
    }

    #[test]
    fn test_kary_and() {
        // test different numbers of operands
        for i in 1..15 {
            // with every possible assignment for them
            for mut b in 0..(1 << i) {
                let mut cs = TestConstraintSystem::<Fr>::new();

                let mut expected = true;

                let mut bits = vec![];
                for j in 0..i {
                    expected &= b & 1 == 1;

                    bits.push(Boolean::from(
                        AllocatedBit::alloc(cs.ns(|| format!("bit_gadget {}", j)), || {
                            Ok(b & 1 == 1)
                        })
                        .unwrap(),
                    ));
                    b >>= 1;
                }

                let r = Boolean::kary_and(&mut cs, &bits).unwrap();

                assert!(cs.is_satisfied());

                match r {
                    Boolean::Is(ref r) => {
                        assert_eq!(r.value.unwrap(), expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
