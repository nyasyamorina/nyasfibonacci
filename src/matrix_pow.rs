use crate::{UBig, UBigMul};

pub fn fibonacci<M: UBigMul>(mut n: u64) -> UBig {
    let mut a = Matrix::iden();
    let mut b = Matrix::fib_trans();

    loop { // `loop` in `Rust` is equal to `while (true)` in other languages.
        if n & 1 != 0 {
            // a <- a * b
            a = a.mul::<M>(&b);
        }

        n >>= 1;
        if n == 0 {
            return a.tr; // result
        } else {
            // b <- b^2
            b = b.sqr::<M>();
        }
    }
}


/// the matrix of
/// [   top-left     top-right;
///  bottom-left  bottom-right]
pub struct Matrix {
    pub tl: UBig, pub tr: UBig,
    pub bl: UBig, pub br: UBig,
}
impl Matrix {
    // I = M^0
    pub fn iden() -> Matrix {
        Matrix {
            tl: UBig::one(),  tr: UBig::zero(),
            bl: UBig::zero(), br: UBig::one(),
        }
    }

    // [0 1; 1 1]
    pub fn fib_trans() -> Matrix {
        Matrix {
            tl: UBig::zero(), tr: UBig::one(),
            bl: UBig::one(),  br: UBig::one(),
        }
    }
}
impl Matrix {
    /// self * rhs
    pub fn mul<M: UBigMul>(&self, rhs: &Matrix) -> Matrix {
        // tl = self.tl * rhs.tl + self.tr * rhs.bl
        let mut tl = M::mul(&self.tl, &rhs.tl);
        tl += &M::mul(&self.tr, &rhs.bl);
        // tr = self.tl * rhs.tr + self.tr * rhs.br
        let mut tr = M::mul(&self.tl, &rhs.tr);
        tr += &M::mul(&self.tr, &rhs.br);
        // bl = self.bl * rhs.tl + self.br * rhs.bl
        let mut bl = M::mul(&self.bl, &rhs.tl);
        bl += &M::mul(&self.br, &rhs.bl);
        // br = self.bl * rhs.tr + self.br * rhs.br
        let mut br = M::mul(&self.bl, &rhs.tr);
        br += &M::mul(&self.br, &rhs.br);

        Matrix { tl, tr, bl, br }
    }

    /// self^2
    pub fn sqr<M: UBigMul>(mut self) -> Matrix {
        let tmp = M::mul(&self.tr, &self.bl);
        // tl = self.tl^2 + self.tr * self.bl
        let mut tl = M::sqr(&self.tl);
        tl += &tmp;
        // br = self.br^2 + self.tr * self.bl
        let mut br = M::sqr(&self.br);
        br += &tmp;

        self.tl += &self.br; // use self.tl as tmp buffer
        // tr = self.tr * (self.rl + self.br)
        let tr = M::mul(&self.tr, &self.tl);
        // bl = self.bl * (self.rl + self.br)
        let bl = M::mul(&self.bl, &self.tl);

        Matrix { tl, tr, bl, br }
    }
}
