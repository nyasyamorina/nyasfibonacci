use super::UBig;
use super::helpers::*;

pub trait UBigMul {
    /// lhs * rhs
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig;
    /// x^2
    fn sqr(x: &UBig) -> UBig;
}

pub enum ElementarySchoolMul {}
impl UBigMul for ElementarySchoolMul {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        let (llen, rlen) = (lhs.data.len(), rhs.data.len());
        if llen == 0 || rlen == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        // the out buffer and tmp buffer
        let mut vec = vec![0; (llen + rlen) + (llen + 1)];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(llen + rlen);

        unsafe { mul_ubig(&lhs.data, &rhs.data, out, tmp); }

        vec.truncate(llen + rlen); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }

    fn sqr(x: &UBig) -> UBig {
        let len = x.data.len();
        if len == 0 {
            return UBig::zero();
        }

        // the out buffer and tmp buffer
        let mut vec = vec![0; 3 * len + 1];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(2 * len);

        unsafe { mul_ubig(&x.data, &x.data, out, tmp); }

        vec.truncate(2 * len);
        let mut res = UBig::from_vec(vec);
        res.truncate();
        res
    }
}


pub enum KaratsubaMul {}
impl KaratsubaMul {
    fn properlen(len: usize) -> usize {
        //! the minimum integer power of 2 that is greater than or equal to the input
        if len == 0 {
            return 0;
        }
        let mut n = len - 1;
        n |= n >> 1;
        n |= n >> 2;
        n |= n >> 4;
        n |= n >> 8;
        n |= n >> 16;
        if size_of::<usize>() > 32/8 {
            n |= n >> 32;
        }
        n + 1
    }
}
impl UBigMul for KaratsubaMul {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        use std::{cmp::max, ptr};
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let len = KaratsubaMul::properlen(max(lhs.data.len(), rhs.data.len()));

        let mut vec = vec![0; 2*len/*for out*/ + 2*len/*for tmp*/+ len/*for lhs*/ + len/*for rhs*/];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(2 * len);
        let a = tmp.wrapping_add(2 * len);
        let b = a.wrapping_add(len);

        unsafe {
            ptr::copy_nonoverlapping(lhs.data.as_ptr(), a, lhs.data.len());
            ptr::copy_nonoverlapping(rhs.data.as_ptr(), b, rhs.data.len());

            karatsuba_mul(a, b, out, tmp, len);
        }

        vec.truncate(2 * len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }

    fn sqr(x: &UBig) -> UBig {
        use std::ptr;
        if x.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let len = KaratsubaMul::properlen(x.data.len());

        let mut vec = vec![0; 2*len/*for out*/ + 2*len/*for tmp*/+ len/*for xx*/];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(2 * len);
        let xx = tmp.wrapping_add(2 * len);

        unsafe {
            ptr::copy_nonoverlapping(x.data.as_ptr(), xx, x.data.len());

            karatsuba_mul(xx, xx, out, tmp, len);
        }

        vec.truncate(2 * len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}
