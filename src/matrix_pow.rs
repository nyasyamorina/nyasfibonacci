use super::{UBig, UBigMul};

pub fn fibonacci<M: UBigMul>(mut n: u64) -> UBig {
    let mut a = Matrix::iden();
    let mut b = Matrix::fib_trans();

    loop { // `loop` in `Rust` is equal to `while (true)` in other languages.
        if n & 1 != 0 {
            // a <- a * b
            a = a.mul::<M>(&mut b);
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
    fn mul<M: UBigMul>(&mut self, rhs: &mut Matrix) -> Matrix {
        // tl = self.tl * rhs.tl + self.tr * rhs.bl
        let mut tl = M::mul(&mut self.tl, &mut rhs.tl);
        tl += &M::mul(&mut self.tr, &mut rhs.bl);
        // tr = self.tl * rhs.tr + self.tr * rhs.br
        let mut tr = M::mul(&mut self.tl, &mut rhs.tr);
        tr += &M::mul(&mut self.tr, &mut rhs.br);
        // bl = self.bl * rhs.tl + self.br * rhs.bl
        let mut bl = M::mul(&mut self.bl, &mut rhs.tl);
        bl += &M::mul(&mut self.br, &mut rhs.bl);
        // br = self.bl * rhs.tr + self.br * rhs.br
        let mut br = M::mul(&mut self.bl, &mut rhs.tr);
        br += &M::mul(&mut self.br, &mut rhs.br);

        Matrix { tl, tr, bl, br }
    }

    /// self^2
    fn sqr<M: UBigMul>(mut self) -> Matrix {
        let tmp = M::mul(&mut self.tr, &mut self.bl);
        // tl = self.tl^2 + self.tr * self.bl
        let mut tl = M::sqr(&mut self.tl);
        tl += &tmp;
        // br = self.br^2 + self.tr * self.bl
        let mut br = M::sqr(&mut self.br);
        br += &tmp;

        self.tl += &self.br; // use self.tl as tmp buffer
        // tr = self.tr * (self.rl + self.br)
        let tr = M::mul(&mut self.tr, &mut self.tl);
        // bl = self.bl * (self.rl + self.br)
        let bl = M::mul(&mut self.bl, &mut self.tl);

        Matrix { tl, tr, bl, br }
    }
}
