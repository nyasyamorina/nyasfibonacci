use std::{cmp::min, fmt, ops::AddAssign, ptr};

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
        // addition in overlap length
        let overlap = min(self.data.len(), rhs.data.len());
        let mut carry = add_into(&mut self.data[..overlap], &rhs.data[..overlap]);

        if rhs.data.len() > self.data.len() {
            // copy extra data from `rhs` to `self`
            self.data.reserve(rhs.data.len()); // make sure `self` can hold the extra data
            let dst = self.data.as_mut_ptr().wrapping_add(overlap);
            let src = rhs.data.as_ptr().wrapping_add(overlap);
            unsafe { // copy data and set length
                ptr::copy_nonoverlapping(src, dst, rhs.data.len() - overlap);
                self.data.set_len(rhs.data.len());
            }
        }

        // handle the carry from overlap addition
        if carry.has() {
            carry = add1_into(&mut self.data[overlap..]);
            if carry.has() {
                // carry overflow
                self.data.push(1);
            }
        }

        use helpers::{addcarry, add1, Carry};

        fn add_into(lhs: &mut [u64], rhs: &[u64]) -> Carry {
            let len = lhs.len();
            let lhs = lhs.as_mut_ptr();
            let rhs = rhs.as_ptr();
            unsafe { addcarry(Carry::zero(), lhs, rhs, lhs, len) }
        }
        fn add1_into(lhs: &mut [u64]) -> Carry {
            let len = lhs.len();
            let lhs = lhs.as_mut_ptr();
            unsafe { add1(lhs, lhs, len) }
        }
    }
}

pub mod mul;
pub use mul::{UBigMul, ElementarySchoolMul};

pub mod recursion;
pub mod iteration;
pub mod matrix_pow;
pub mod small_matrix;
pub mod rev_pow;


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn it_works() {
        let fib = recursion::fibonacci(37);
        assert_eq!(fib.data.len(), 1);
        assert_eq!(fib.data[0], 24157817u64);

        assert_eq!(iteration::fibonacci(37), fib);

        let fib = iteration::fibonacci(100_000);
        assert_eq!(matrix_pow::fibonacci::<ElementarySchoolMul>(100_000), fib);
        assert_eq!(small_matrix::fibonacci::<ElementarySchoolMul>(100_000), fib);
        assert_eq!(rev_pow::fibonacci::<ElementarySchoolMul>(100_000), fib);
        assert_eq!(rev_pow::fibonacci_removed_matrix_abstrat::<ElementarySchoolMul>(100_000), fib);
    }
}