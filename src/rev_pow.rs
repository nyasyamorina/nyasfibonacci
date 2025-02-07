

use super::{UBig, UBigMul};
use super::small_matrix::SmallMatrix;

pub fn fibonacci<M: UBigMul>(n: u64) -> UBig {
    return fib_mat::<M>(n).curr;

    #[inline]
    fn fib_mat<M: UBigMul>(n: u64) -> SmallMatrix {
        if n == 0 {
            return SmallMatrix::iden();
        } else if n == 1 {
            return SmallMatrix::fib_trans();
        }

        // m = S_floor(n/2)
        let m = fib_mat::<M>(n >> 1);
        // m <- m^2
        let mut m = m.sqr::<M>();
        if n & 1 != 0 {
            // m <- m * M
            m.prev += &m.curr;
            (m.prev, m.curr) = (m.curr, m.prev);
        }
        return m;
    }
}


pub fn fibonacci_removed_matrix_abstrat<M: UBigMul>(n: u64) -> UBig {
    return fib_pair::<M>(n).1;

    // return (F_{n-1}, F_{n})
    fn fib_pair<M: UBigMul>(n: u64) -> (UBig, UBig) {
        if n == 0 {
            return (UBig::one(), UBig::zero());
        } else if n == 1 {
            return (UBig::zero(), UBig::one());
        }

        let (mut _prev, mut _curr) = fib_pair::<M>(n >> 1);

        // F_{2n-1} = F_{n-1}^2 + F_{n}^2
        let mut prev = M::sqr(&mut _prev);
        M::sqr_addto(&mut _curr, &mut prev);

        // F_{2n} = F_{n} * (2F_{n-1} + F_{n})
        _prev.shl1(); _prev += &_curr;
        let mut curr = M::mul(&mut _curr, &mut _prev);

        if n & 1 != 0 {
            // F_{n+1} = F_{n-1} + F_{n}
            prev += &curr;
            (prev, curr) = (curr, prev);
        }
        (prev, curr)
    }


    trait SqrAddto {
        // out += x^2
        fn sqr_addto(x: &mut UBig, out: &mut UBig);
    }

    impl<M: UBigMul> SqrAddto for M {
        /* default */ fn sqr_addto(x: &mut UBig, out: &mut UBig) {
            let tmp = Self::sqr(x);
            *out += &tmp;
        }
    }


    // if you are using nightly rust and enabled feature `specialization` or `min_specialization`,
    // then you can use the code below, and also need to uncomment the `default` before `sqr_addto` above.

    /* impl SqrAddto for super::ElementarySchoolMul {
        // this impl is slitly faster then the default impl
        fn sqr_addto(x: &mut UBig, out: &mut UBig) {
            use super::helpers::*;

            let out_len = 2 * x.data.len();
            if out.data.len() < out_len {
                out.data.resize(out_len, 0);
            }

            unsafe {
                // this is where the magic happens: `out += lhs * rhs`
                let carry = mul_ubig_addto(&x.data, &x.data, out.data.as_mut_ptr());

                if carry.has() {
                    let o = out.data.as_mut_ptr().wrapping_add(out_len);
                    let carry = add1(o, o, out.data.len() - out_len);
                    if carry.has() {
                        out.data.push(1);
                    }
                }
            }

            out.truncate();
        }
    } */
}
