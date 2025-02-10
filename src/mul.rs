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
impl UBigMul for KaratsubaMul {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        use std::{cmp::max, ptr};
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let len = max(lhs.data.len(), rhs.data.len()).next_power_of_two();

        let mut vec = vec![0; 2*len/*for out*/ + 2*len/*for tmp*/+ len/*for lhs*/ + len/*for rhs*/];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(2 * len);
        let a = tmp.wrapping_add(2 * len);
        let b = a.wrapping_add(len);

        unsafe {
            ptr::copy_nonoverlapping(lhs.data.as_ptr(), a, lhs.data.len());
            ptr::copy_nonoverlapping(rhs.data.as_ptr(), b, rhs.data.len());

            karatsuba_mul_power_of_two_len(a, b, out, tmp, len);
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

        let len = x.data.len().next_power_of_two();

        let mut vec = vec![0; 2*len/*for out*/ + 2*len/*for tmp*/+ len/*for xx*/];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(2 * len);
        let xx = tmp.wrapping_add(2 * len);

        unsafe {
            ptr::copy_nonoverlapping(x.data.as_ptr(), xx, x.data.len());

            karatsuba_mul_power_of_two_len(xx, xx, out, tmp, len);
        }

        vec.truncate(2 * len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}

pub enum KaratsubaMulAnyLength {}
impl UBigMul for KaratsubaMulAnyLength {
    fn mul<'a>(mut lhs: &'a UBig, mut rhs: &'a UBig) -> UBig {
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }
        if lhs.data.len() < rhs.data.len() {
            (lhs, rhs) = (rhs, lhs); // always `lhs` is longer than `rhs`
        }

        let out_len = lhs.data.len() + rhs.data.len();
        let tmp_len = karatsuba_anylen_tmp_len(lhs.data.len(), rhs.data.len());

        let mut vec = vec![0; out_len + tmp_len];
        let out = vec.as_mut_ptr();
        let _tmp = out.wrapping_add(out_len);

        unsafe {
            karatsuba_mul_lhs_longer_stack(&lhs.data, &rhs.data, out, _tmp);
        }

        vec.truncate(out_len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }

    fn sqr(x: &UBig) -> UBig {
        if x.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let in_len = x.data.len();
        let out_len = in_len << 1;
        let tmp_len = in_len.next_power_of_two() << 1;

        let mut vec = vec![0; out_len + tmp_len];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(out_len);

        unsafe {
            let x = x.data.as_ptr();
            karatsuba_mul_equal_len(x, x, out, in_len, tmp);
        }

        vec.truncate(out_len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}

