use crate::{UBig, UBigMul};
use crate::helpers::*;


pub enum ElementarySchool {}
impl ElementarySchool {
    unsafe fn ptr_mul(lhs: &[u64], rhs: &[u64], out: *mut u64, tmp: *mut u64) {
        //! # Safety
        //!
        //! `out.len() = lhs.len() + rhs.len()` and `tmp.len() = lhs.len() + 1`.
        //! `out` must init with all 0s.
        for index in 0..rhs.len() {
            let r = rhs.get_unchecked(index);
            let o = out.wrapping_add(index);
            mul_ubig_u64(lhs, *r, tmp);
            let carry = addcarry_ubig_equal_len(Carry::zero(), o, tmp, o, lhs.len() + 1);
            debug_assert!(!carry.has());
        }
    }
}

impl UBigMul for ElementarySchool {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        let (llen, rlen) = (lhs.data.len(), rhs.data.len());
        if llen == 0 || rlen == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        // the out buffer and tmp buffer
        let mut vec = vec![0; (llen + rlen) + (llen + 1)];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(llen + rlen);

        unsafe { ElementarySchool::ptr_mul(&lhs.data, &rhs.data, out, tmp); }

        vec.truncate(llen + rlen); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}
