use super::UBig;
use super::helpers::*;

pub trait UBigMul {
    /// lhs * rhs
    fn mul(lhs: &mut UBig, rhs: &mut UBig) -> UBig;
    /// x^2
    fn sqr(x: &mut UBig) -> UBig;
}

pub enum ElementarySchoolMul {}
impl UBigMul for ElementarySchoolMul {
    fn mul(lhs: &mut UBig, rhs: &mut UBig) -> UBig {
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

    fn sqr(x: &mut UBig) -> UBig {
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
