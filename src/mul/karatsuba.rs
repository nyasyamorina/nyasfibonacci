use crate::{UBig, UBigMul};
use crate::helpers::*;

use std::slice;


pub enum Karatsuba {}
impl Karatsuba {
    #[inline]
    unsafe fn ptr_mul(lhs: *const u64, rhs: *const u64, out: *mut u64, tmp: *mut u64, len: usize) {
        //! # Safety
        //!
        //! lhs.len() = b.len() = len, out.len() = tmp.len() = 2*len,
        //! len must be a power of 2.
        debug_assert!(len.is_power_of_two() && len > 0);
        if len == 1 {
            let [low64, high64] = mul_u64(*lhs, *rhs);
            *out.wrapping_add(0) = low64;
            *out.wrapping_add(1) = high64;
            return;
        }

        let half_len = len >> 1;
        let (l0, l1) = (lhs, lhs.wrapping_add(half_len));
        let (r0, r1) = (rhs, rhs.wrapping_add(half_len));
        let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
        let (o0, o1) = (out, out.wrapping_add(half_len));
        let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

        // l_ = l0 + l1
        let l_ = o0;
        let l_carry = addcarry_ubig_equal_len(Carry::zero(), l0, l1, l_, half_len);
        // r_ = r0 + r1
        let r_ = o1;
        let r_carry = addcarry_ubig_equal_len(Carry::zero(), r0, r1, r_, half_len);
        // z_ = l_ * r_
        let z_ = t0;
        let overflow = Karatsuba::ptr_mulcarry(l_, l_carry, r_, r_carry, z_, next_tmp, half_len);

        // z0 = l0 * r0
        let z0 = o0;
        Karatsuba::ptr_mul(l0, r0, z0, next_tmp, half_len);
        // z2 = l1 * r1
        let z2 = o2;
        Karatsuba::ptr_mul(l1, r1, z2, next_tmp, half_len);

        // z1 = z_ - z0 - z2;
        let z1 = t0;
        let borrow0 = subborrow_ubig_equal_len(Borrow::zero(), z_, z0, z1, len);
        let borrow1 = subborrow_ubig_equal_len(Borrow::zero(), z1, z2, z1, len);
        let z1_carry = sub_borrow_from_overflow_to_carry(overflow, borrow0, borrow1);

        // out += z1 << half_len
        let no_carry1 = add_carry_to_ubig(z1_carry, o3, o3, half_len);
        let carry = addcarry_ubig_equal_len(Carry::zero(), o1, z1, o1, len);
        let no_carry2 = add_carry_to_ubig(carry, o3, o3, half_len);

        debug_assert!(!no_carry1.has() && !no_carry2.has());
    }

    #[inline]
    unsafe fn ptr_mulcarry(
        lhs: *const u64, lhs_carry: Carry,
        rhs: *const u64, rhs_carry: Carry,
        out: *mut u64, tmp: *mut u64, len: usize
    ) -> u8 {
        //! # Safety
        //!
        //! a.len() = b.len() = len, out.len() = tmp.len() = 2*len,
        //! len must be a power of 2.
        debug_assert!(len.is_power_of_two() && len > 0);
        if len == 1 {
            let [low64, high64] = mul_u64(*lhs, *rhs);
            let (out_low, out_high) = (out, out.wrapping_add(1));
            *out_low  = low64;
            *out_high = high64;

            let mut overflow = (lhs_carry & rhs_carry).as_u8();
            if lhs_carry.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *rhs, out_high).as_u8(); }
            if rhs_carry.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *lhs, out_high).as_u8(); }
            return overflow;
        }

        let half_len = len >> 1;
        let (l0, l1) = (lhs, lhs.wrapping_add(half_len));
        let (r0, r1) = (rhs, rhs.wrapping_add(half_len));
        let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
        let (o0, o1) = (out, out.wrapping_add(half_len));
        let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

        // l_ = l0 + l1
        let l_ = o0;
        let l_carry = addcarry_ubig_equal_len(Carry::zero(), l0, l1, l_, half_len);
        // r_ = r0 + r1
        let r_ = o1;
        let r_carry = addcarry_ubig_equal_len(Carry::zero(), r0, r1, r_, half_len);
        // z_ = a_ * b_
        let z_ = t0;
        let overflow = Karatsuba::ptr_mulcarry(l_, l_carry, r_, r_carry, z_, next_tmp, half_len);

        // z0 = a0 * b0
        let z0 = o0;
        Karatsuba::ptr_mul(l0, r0, z0, next_tmp, half_len);
        // z2 = a1 * b1
        let z2 = o2;
        Karatsuba::ptr_mul(l1, r1, z2, next_tmp, half_len);

        // z1 = z_ - z0 - z2;
        let z1 = t0;
        let borrow0 = subborrow_ubig_equal_len(Borrow::zero(), z_, z0, z1, len);
        let borrow1 = subborrow_ubig_equal_len(Borrow::zero(), z1, z2, z1, len);
        let z1_carry = sub_borrow_from_overflow_to_carry(overflow, borrow0, borrow1);

        // add z1 to out
        let mut overflow = (lhs_carry & rhs_carry).as_u8();
        overflow += add_carry_to_ubig(z1_carry, o3, o3, half_len).as_u8();
        let carry = addcarry_ubig_equal_len(Carry::zero(), o1, z1, o1, len);
        overflow += add_carry_to_ubig(carry, o3, o3, half_len).as_u8();
        // extra addition
        if lhs_carry.has() { overflow += addcarry_ubig_equal_len(Carry::zero(), o2, rhs, o2, len).as_u8(); }
        if rhs_carry.has() { overflow += addcarry_ubig_equal_len(Carry::zero(), o2, lhs, o2, len).as_u8(); }

        debug_assert!(overflow < 4);
        return overflow;
    }
}

impl UBigMul for Karatsuba {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        use std::{cmp::max, ptr};
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let in_len = max(lhs.data.len(), rhs.data.len()).next_power_of_two();
        let out_len = 2 * in_len;
        let tmp_len = out_len;

        let mut vec = vec![0; out_len + tmp_len + in_len + in_len];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(out_len);
        let a = tmp.wrapping_add(tmp_len);
        let b = a.wrapping_add(in_len);

        unsafe {
            ptr::copy_nonoverlapping(lhs.data.as_ptr(), a, lhs.data.len());
            ptr::copy_nonoverlapping(rhs.data.as_ptr(), b, rhs.data.len());

            Karatsuba::ptr_mul(a, b, out, tmp, in_len);
        }

        vec.truncate(out_len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }

    fn sqr(x: &UBig) -> UBig {
        use std::ptr;
        if x.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }

        let in_len = x.data.len().next_power_of_two();
        let out_len = 2 * in_len;
        let tmp_len = out_len;

        let mut vec = vec![0; out_len + tmp_len + in_len];
        let out = vec.as_mut_ptr();
        let tmp = out.wrapping_add(out_len);
        let xx = tmp.wrapping_add(tmp_len);

        unsafe {
            ptr::copy_nonoverlapping(x.data.as_ptr(), xx, x.data.len());

            Karatsuba::ptr_mul(xx, xx, out, tmp, in_len);
        }

        vec.truncate(out_len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}


pub enum KaratsubaAnyLength {}
impl KaratsubaAnyLength {
    #[inline]
    unsafe fn ptr_mul_eqlen(lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize, tmp: *mut u64) {
        //! # Safety
        //!
        //! lhs.len() = rhs.len() = len; out.len() = 2*len; tmp.len() = 2*next_power_of_two(len)
        debug_assert!(len > 0);
        if len.is_power_of_two() {
            return Karatsuba::ptr_mul(lhs, rhs, out, tmp, len);
        }

        let full_len = len.next_power_of_two();
        let half_len = full_len >> 1;
        let extra_len = len - half_len;
        debug_assert!(half_len > extra_len);

        let (l0, l1) = (lhs, lhs.wrapping_add(half_len));
        let (r0, r1) = (rhs, rhs.wrapping_add(half_len));
        let next_tmp = tmp.wrapping_add(full_len);

        // l_ = l0 + l1
        let l_ = out;
        let l_carry = {
            let l0_slice = slice::from_raw_parts(l0, half_len);
            let l1_slice = slice::from_raw_parts(l1, extra_len);
            addcarry_ubig_lhs_longer(Carry::zero(), l0_slice, l1_slice, l_)
        };
        // r_ = r0 + r1
        let r_ = out.wrapping_add(half_len);
        let r_carry = {
            let r0_slice = slice::from_raw_parts(r0, half_len);
            let r1_slice = slice::from_raw_parts(r1, extra_len);
            addcarry_ubig_lhs_longer(Carry::zero(), r0_slice, r1_slice, r_)
        };

        // z_ = l_ * r_
        let z_ = tmp;
        let overflow = Karatsuba::ptr_mulcarry(l_, l_carry, r_, r_carry, z_, next_tmp, half_len);

        // z0 = l0 * r0
        let z0 = out;
        Karatsuba::ptr_mul(l0, r0, z0, next_tmp, half_len);
        // z2 = l1 * r1
        let z2 = out.wrapping_add(full_len);
        KaratsubaAnyLength::ptr_mul_eqlen(l1, r1, z2, extra_len, next_tmp);

        // z1 = z_ - z0 - z1
        let z1 = z_;
        let borrow0 = subborrow_ubig_equal_len(Borrow::zero(), z_, z0, z_, full_len);
        let borrow1 = {
            let z1_slice = slice::from_raw_parts(z1, full_len);
            let z2_slice = slice::from_raw_parts(z2, extra_len << 1);
            subborrow_ubig_lhs_longer(Borrow::zero(), z1_slice, z2_slice, z1)
        };
        debug_assert!(overflow == borrow0.as_u8() + borrow1.as_u8());
        // and also elements above z1[len] should all be 0s
        let z1_carry = *(z1.wrapping_add(len));
        debug_assert!(z1_carry == 0 || z1_carry == 1);
        let z1_carry = Carry::from_u8(z1_carry as u8);

        // out += z1 << half_len
        let o1 = out.wrapping_add(half_len);
        let o3 = o1.wrapping_add(len);
        let no_carry1 = add_carry_to_ubig(z1_carry, o3, o3, extra_len);
        let carry = addcarry_ubig_equal_len(Carry::zero(), o1, z1, o1, len);
        let no_carry2 = add_carry_to_ubig(carry, o3, o3, extra_len);

        debug_assert!(!no_carry1.has() && !no_carry2.has());
    }

    #[allow(dead_code)] // this method is not used because it may cause stack overflow, see `ptr_mul_anylen_stack` below.
    #[inline]
    unsafe fn ptr_mul_anylen(lhs: &[u64], rhs: &[u64], out: *mut u64, tmp: *mut u64) {
        //! # Warn
        //!
        //! if `rhs.len()` is way smaller than `lhs.len()`, than this recursion function may cause stack overflow.
        //!
        //! # Safety
        //!
        //! lhs.len() > rhs.len(); out.len() = lhs.len() + rhs.len(); tmp.len() = karatsuba_tmp_len(lhs.len(), rhs.len())
        debug_assert!(lhs.len() >= rhs.len());

        if rhs.len() == 0 {
            for index in 0..lhs.len() {
                *(out.wrapping_add(index)) = 0;
            }
            return;
        } else if rhs.len() == 1 {
            let r = rhs.get_unchecked(0);
            return mul_ubig_u64(lhs, *r, out);
        }

        let half_len = rhs.len();
        let extra_len = lhs.len() - half_len;

        let (l0, l1) = (lhs.as_ptr(), &lhs[half_len..]);
        let r0 = rhs.as_ptr();

        // z0 = l0 * r0
        let z0 = out;
        KaratsubaAnyLength::ptr_mul_eqlen(l0, r0, z0, half_len, tmp);

        // z1 = l1 * r0
        if extra_len == 0 {
            return;
        }
        let z1 = tmp;
        let next_tmp = tmp.wrapping_add(lhs.len());
        if extra_len >= half_len {
            KaratsubaAnyLength::ptr_mul_anylen(l1, rhs, z1, next_tmp);
        } else {
            KaratsubaAnyLength::ptr_mul_anylen(rhs, l1, z1, next_tmp);
        }

        // out += z1 << half_len
        let o1 = out.wrapping_add(half_len);
        let o2 = o1.wrapping_add(half_len);
        core::ptr::copy_nonoverlapping(z1.wrapping_add(half_len), o2, extra_len);
        let no_carry = {
            let o1_slice = slice::from_raw_parts(o1, lhs.len());
            let z1 = slice::from_raw_parts(z1, half_len);
            addcarry_ubig_lhs_longer(Carry::zero(), o1_slice, z1, o1)
        };

        debug_assert!(!no_carry.has());
    }

    unsafe fn ptr_mul_anylen_stack<'a>(mut lhs: &'a [u64], mut rhs: &'a [u64], mut out: *mut u64, mut tmp: *mut u64) {
        //! # Safety
        //!
        //! lhs.len() > rhs.len(); out.len() = lhs.len() + rhs.len(); tmp.len() = karatsuba_tmp_len(lhs.len(), rhs.len())
        debug_assert!(lhs.len() >= rhs.len());

        // break the recursion into stack (data struct)
        let mut stack = vec![];
        loop {
            if rhs.len() == 0 {
                for index in 0..lhs.len() {
                    *(out.wrapping_add(index)) = 0;
                }
                break;
            } else if rhs.len() == 1 {
                let r = rhs.get_unchecked(0);
                mul_ubig_u64(lhs, *r, out);
                break;
            }

            let half_len = rhs.len();
            let extra_len = lhs.len() - half_len;

            let (l0, l1) = (lhs.as_ptr(), &lhs[half_len..]);
            let r0 = rhs.as_ptr();

            // z0 = l0 * r0
            let z0 = out;
            KaratsubaAnyLength::ptr_mul_eqlen(l0, r0, z0, half_len, tmp);

            // z1 = l1 * r0
            if extra_len == 0 {
                break;
            }
            let z1 = tmp;
            let next_tmp = tmp.wrapping_add(lhs.len());

            stack.push((half_len, extra_len, out, z1));

            if extra_len > half_len {
                (lhs, rhs, out, tmp) = (l1, rhs, z1, next_tmp);
            } else {
                (lhs, rhs, out, tmp) = (rhs, l1, z1, next_tmp);
            }
        }

        while let Some((half_len, extra_len, out, z1)) = stack.pop() {
            let o1 = out.wrapping_add(half_len);
            let o2 = o1 .wrapping_add(half_len);
            core::ptr::copy_nonoverlapping(z1.wrapping_add(half_len), o2, extra_len);
            let no_carry = {
                let o1_slice = slice::from_raw_parts(o1, half_len + extra_len);
                let z1 = slice::from_raw_parts(z1, half_len);
                addcarry_ubig_lhs_longer(Carry::zero(), o1_slice, z1, o1)
            };

            debug_assert!(!no_carry.has());
        }
    }

    #[inline]
    /// calculate the length of tmp used in `ptr_mul_anylen`
    fn tmp_len(lhs_len: usize, rhs_len: usize) -> usize {
        if rhs_len < 2 {
            return 0;
        }
        let z0_len = rhs_len.next_power_of_two() << 1;
        // assume: lhs_len = n * rhs_len + m
        let (n, m) = (lhs_len / rhs_len, lhs_len % rhs_len);
        let curr = n * m + (n * (n + 1) / 2) * rhs_len;
        let next = KaratsubaAnyLength::tmp_len(rhs_len, m);
        curr + z0_len + next
    }
}

impl UBigMul for KaratsubaAnyLength {
    fn mul<'a>(mut lhs: &'a UBig, mut rhs: &'a UBig) -> UBig {
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero(); // everything mul by 0 is 0
        }
        if lhs.data.len() < rhs.data.len() {
            (lhs, rhs) = (rhs, lhs); // make sure `lhs` is always longer than `rhs`
        }

        let out_len = lhs.data.len() + rhs.data.len();
        let tmp_len = KaratsubaAnyLength::tmp_len(lhs.data.len(), rhs.data.len());

        let mut vec = vec![0; out_len + tmp_len];
        let out = vec.as_mut_ptr();
        let _tmp = out.wrapping_add(out_len);

        unsafe {
            KaratsubaAnyLength::ptr_mul_anylen_stack(&lhs.data, &rhs.data, out, _tmp);
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
            KaratsubaAnyLength::ptr_mul_eqlen(x, x, out, in_len, tmp);
        }

        vec.truncate(out_len); // truncate the tmp buffer
        let mut res = UBig::from_vec(vec);
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}