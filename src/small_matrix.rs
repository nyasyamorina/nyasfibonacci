use super::{UBig, UBigMul};

pub fn fibonacci<M: UBigMul>(mut n: u64) -> UBig {
    let mut a = SmallMatrix::iden();
    let mut b = SmallMatrix::fib_trans();

    loop { // `loop` in `Rust` is equal to `while (true)` in other languages.
        if n & 1 != 0 {
            // a <- a * b
            a = a.mul::<M>(&b);
        }

        n >>= 1;
        if n == 0 {
            return a.curr; // result
        } else {
            // b <- b^2
            b = b.sqr::<M>();
        }
    }
}


/// the matrix of
/// [prev       curr;
///  curr  prev+curr]
pub struct SmallMatrix {
    pub prev: UBig,
    pub curr: UBig,
}
impl SmallMatrix {
    pub fn iden() -> SmallMatrix {
        SmallMatrix { prev: UBig::one(), curr: UBig::zero() }
    }

    pub fn fib_trans() -> SmallMatrix {
        SmallMatrix { prev: UBig::zero(), curr: UBig::one() }
    }
}
impl SmallMatrix {
    pub fn mul<M: UBigMul>(&self, rhs: &SmallMatrix) -> SmallMatrix {
        // prev = self.prev * rhs.prev + self.curr * rhs.curr
        let mut prev = M::mul(&self.prev, &rhs.prev);
        let tmp = M::mul(&self.curr, &rhs.curr);
        prev += &tmp;
        // curr = self.prev * rhs.curr + self.curr * rhs.prev + self.curr * rhs.curr
        let mut curr = M::mul(&self.prev, &rhs.curr);
        curr += &tmp;
        let tmp = M::mul(&self.curr, &rhs.prev);
        curr += &tmp;

        SmallMatrix { prev, curr }
    }

    pub fn sqr<M: UBigMul>(mut self) -> SmallMatrix {
        // prev = self.prev^2 + self.curr^2
        let mut prev = M::sqr(&self.prev);
        let tmp = M::sqr(&self.curr);
        prev += &tmp;
        // curr = self.curr * (2 * self.prev + self.curr)
        self.prev.shl1();
        self.prev += &self.curr;
        let curr = M::mul(&self.curr, &self.prev);

        SmallMatrix { prev, curr }
    }
}
