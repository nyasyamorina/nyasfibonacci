// see: "rev_pow.rs: 74"
/* #![feature(min_specialization)] */


use std::{fmt, ops::AddAssign, slice};

mod helpers;


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UBig {
    data: Vec<u64>,
}
impl UBig {
    pub fn zero() -> UBig {
        UBig { data: vec![] }
    }
    pub fn one() -> UBig {
        UBig { data: vec![1] }
    }
    pub fn from_u64(x: u64) -> UBig {
        UBig { data: vec![x] }
    }
    pub fn from_vec(data: Vec<u64>) -> UBig {
        UBig { data }
    }
    pub fn to_vec(self) -> Vec<u64> {
        self.data
    }

    pub fn truncate(&mut self) {
        //! remove the extra 0s
        let mut len = 0;
        for (index, x) in self.data.iter().enumerate().rev() {
            if *x != 0 {
                len = index + 1;
                break;
            }
        }
        self.data.truncate(len); // note this method will not realloc memory
    }

    pub fn shl1(&mut self) {
        if self.data.is_empty() {
            return;
        }

        let mut carry = 0;
        for x in &mut self.data {
            (carry, *x) = (*x >> 63, (*x << 1) | carry);
        }
        if carry != 0 {
            // carry overflow
            self.data.push(1);
        }
    }
}

impl fmt::Display for UBig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.data.iter().rev();
        match iter.next() {
            None => write!(f, "0x0")?,
            Some(x) => write!(f, "{:#X}", x)?,
        };
        for x in iter {
            write!(f, "_{:#016X}", x)?;
        }
        Ok(())
    }
}

impl AddAssign<&UBig> for UBig {
    fn add_assign(&mut self, rhs: &UBig) {
        use helpers::*;

        let carry = unsafe {
            if self.data.len() >= rhs.data.len() {
                let lhs_slice = slice::from_raw_parts(self.data.as_ptr(), self.data.len());
                addcarry_ubig_lhs_longer(Carry::zero(), lhs_slice, &rhs.data, self.data.as_mut_ptr())
            } else {
                self.data.reserve(rhs.data.len());
                let lhs_slice = slice::from_raw_parts(self.data.as_ptr(), self.data.len());
                let carry = addcarry_ubig_lhs_longer(Carry::zero(), &rhs.data, lhs_slice, self.data.as_mut_ptr());
                self.data.set_len(rhs.data.len());
                carry
            }
        };

        if carry.has() {
            // carry overflow
            self.data.push(1);
        }
    }
}

pub mod mul;
pub use mul::UBigMul;

pub mod recursion;
pub mod iteration;
pub mod matrix_pow;
pub mod small_matrix;
pub mod rev_pow;


#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn it_works() {
        let fib = recursion::fibonacci(37);
        assert_eq!(fib.data.len(), 1);
        assert_eq!(fib.data[0], 24157817u64);

        assert_eq!(iteration::fibonacci(37), fib);
        let fib = iteration::fibonacci(100_000);

        assert_eq!(matrix_pow::fibonacci::<mul::ElementarySchool>(100_000), fib);
        assert_eq!(small_matrix::fibonacci::<mul::ElementarySchool>(100_000), fib);
        assert_eq!(rev_pow::fibonacci::<mul::ElementarySchool>(100_000), fib);
        assert_eq!(rev_pow::fibonacci_removed_matrix_abstract::<mul::ElementarySchool>(100_000), fib);

        assert_eq!(matrix_pow::fibonacci::<mul::Karatsuba>(100_000), fib);
        assert_eq!(small_matrix::fibonacci::<mul::Karatsuba>(100_000), fib);
        assert_eq!(rev_pow::fibonacci::<mul::Karatsuba>(100_000), fib);
        assert_eq!(rev_pow::fibonacci_removed_matrix_abstract::<mul::Karatsuba>(100_000), fib);

        assert_eq!(matrix_pow::fibonacci::<mul::KaratsubaAnyLength>(100_000), fib);
        assert_eq!(small_matrix::fibonacci::<mul::KaratsubaAnyLength>(100_000), fib);
        assert_eq!(rev_pow::fibonacci::<mul::KaratsubaAnyLength>(100_000), fib);
        assert_eq!(rev_pow::fibonacci_removed_matrix_abstract::<mul::KaratsubaAnyLength>(100_000), fib);
    }
}