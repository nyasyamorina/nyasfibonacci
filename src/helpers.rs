use std::{ops::{BitAnd, BitOr, BitOrAssign}, slice};

//================================    not x86_64    ================================//

#[cfg(not(target_arch = "x86_64"))]
#[derive(Debug, Clone, Copy)]
pub struct Carry(bool);
#[cfg(not(target_arch = "x86_64"))]
impl Carry {
    #[inline(always)]
    pub fn zero() -> Carry {
        Carry(false)
    }
    #[inline(always)]
    pub fn from(carry: bool) -> Carry {
        Carry(carry)
    }

    #[inline(always)]
    pub fn has(&self) -> bool {
        self.0
    }
    #[inline(always)]
    pub fn get(&self) -> bool {
        self.0
    }

    #[inline(always)]
    pub fn as_u8(&self) -> u8 {
        if self.0 { 1 } else { 0 }
    }
    #[inline(always)]
    pub unsafe fn from_u8(x: u8) -> Carry {
        debug_assert!(x == 0 || x == 1);
        Carry(x != 0)
    }
}

#[inline(always)] // used in karatsuba mul
#[cfg(not(target_arch = "x86_64"))]
fn sub_borrow_from_overflow_to_carry(overflow: u8, borrow0: Borrow, borrow1: Borrow) -> Carry {
    let borrow = borrow0.as_u8() + borrow1.as_u8();
    debug_assert!(overflow == borrow || overflow == borrow + 1);
    unsafe { Carry::from(overflow > borrow) }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub unsafe fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: *mut u64) -> Carry {
    let tmp = lhs + carry.as_u8();
    *out = tmp + rhs;
    unsafe { Carry::from(tmp < lhs || *out < tmp) }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub unsafe fn subborrow_u64(borrow: Borrow, lhs: u64, rhs: u64, out: *mut u64) -> Borrow {
    let tmp = lhs - borrow.as_u8();
    *out = tmp - rhs;
    unsafe { Borrow::from(tmp > lhs || *out > tmp) }
}

#[allow(dead_code)]
pub unsafe fn addcarry_u64_rust(carry: bool, lhs: u64, rhs: u64, out: *mut u64) -> bool {
    let (c0, c1);
    (*out, c0) = lhs.overflowing_add(if carry { 1 } else { 0 });
    (*out, c1) = rhs.overflowing_add(*out);
    c0 || c1
}

//================================      x86_64      ================================//

#[cfg(target_arch = "x86_64")]
#[derive(Debug, Clone, Copy)]
pub struct Carry(u8);
#[cfg(target_arch = "x86_64")]
impl Carry {
    #[inline(always)]
    pub fn zero() -> Carry {
        Carry(0)
    }
    #[inline(always)]
    pub unsafe fn from(carry: u8) -> Carry {
        Carry(carry)
    }

    #[inline(always)]
    pub fn has(&self) -> bool {
        self.0 != 0
    }
    #[inline(always)]
    pub unsafe fn get(&self) -> u8 {
        self.0
    }

    #[inline(always)]
    pub fn as_u8(&self) -> u8 {
        self.0
    }
    #[inline(always)]
    pub unsafe fn from_u8(x: u8) -> Carry {
        debug_assert!(x == 0 || x == 1);
        Carry(x)
    }
}

#[inline(always)] // used in karatsuba mul
#[cfg(target_arch = "x86_64")]
fn sub_borrow_from_overflow_to_carry(overflow: u8, borrow0: Borrow, borrow1: Borrow) -> Carry {
    let borrow = borrow0.as_u8() + borrow1.as_u8();
    debug_assert!(overflow == borrow || overflow == borrow + 1);
    let carry = overflow - borrow;
    unsafe { Carry::from(carry) }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub unsafe fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: *mut u64) -> Carry {
    //! note that in this version of `addcarry_u64`, the carry is a `u8` rather than a `bool`,
    //! because Rust cannot convert a `u8` to a `bool` without doing a comparison.
    unsafe { Carry::from(core::arch::x86_64::_addcarry_u64(carry.get(), lhs, rhs, &mut *out)) }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub unsafe fn subborrow_u64(borrow: Borrow, lhs: u64, rhs: u64, out: *mut u64) -> Borrow {
    //! note that in this version of `subborrow_u64`, the borrow is a `u8` rather than a `bool`,
    //! because Rust cannot convert a `u8` to a `bool` without doing a comparison.
    unsafe { Carry::from(core::arch::x86_64::_subborrow_u64(borrow.get(), lhs, rhs, &mut *out)) }
}

//================================      common      ================================//

impl BitOr<Carry> for Carry {
    type Output = Carry;

    fn bitor(self, rhs: Carry) -> Self::Output {
        unsafe { Carry::from(self.0 | rhs.0) }
    }
}
impl BitOrAssign<Carry> for Carry {
    fn bitor_assign(&mut self, rhs: Carry) {
        self.0 |= rhs.0;
    }
}
impl BitAnd<Carry> for Carry {
    type Output = Carry;

    fn bitand(self, rhs: Carry) -> Self::Output {
        unsafe { Carry::from(self.0 & rhs.0) }
    }
}

pub type Borrow = Carry;


#[inline]
pub unsafe fn addcarry_ubig_equal_len(mut carry: Carry, lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize) -> Carry {
    //! # Safety
    //!
    //! the length of `lhs`, `rhs` and `out` must be equal to `len`.
    for index in 0..len {
        let l = lhs.wrapping_add(index);
        let r = rhs.wrapping_add(index);
        let o = out.wrapping_add(index);
        carry = addcarry_u64(carry, *l, *r, o);
    }
    carry
}

#[inline]
pub unsafe fn addcarry_ubig_lhs_longer(mut carry: Carry, lhs: &[u64], rhs: &[u64], out: *mut u64) -> Carry {
    //! # Safety
    //!
    //! `lhs` must be longer than `rhs`, and the length of `out` must equal to the length of `lhs`.
    debug_assert!(lhs.len() >= rhs.len());
    carry = addcarry_ubig_equal_len(carry, lhs.as_ptr(), rhs.as_ptr(), out, rhs.len());
    return add_carry_to_ubig(carry, lhs.as_ptr().wrapping_add(rhs.len()), out.wrapping_add(rhs.len()), lhs.len() - rhs.len());
}

#[inline]
pub unsafe fn add_carry_to_ubig(mut carry: Carry, src: *const u64, dst: *mut u64, len: usize) -> Carry {
    //! # Safety
    //!
    //! the length of `src` and `dst` must be equal to `len`.
    for index in 0..len {
        let s = src.wrapping_add(index);
        let d = dst.wrapping_add(index);
        carry = addcarry_u64(carry, *s, 0, d);
    }
    carry
}


#[inline]
pub unsafe fn subborrow_ubig_equal_len(mut borrow: Borrow, lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize) -> Borrow {
    //! # Safety
    //!
    //! the length of `lhs`, `rhs` and `out` must be equal to `len`.
    for index in 0..len {
        let l = lhs.wrapping_add(index);
        let r = rhs.wrapping_add(index);
        let o = out.wrapping_add(index);
        borrow = subborrow_u64(borrow, *l, *r, o);
    }
    borrow
}

#[inline]
pub unsafe fn subborrow_ubig_lhs_longer(mut borrow: Borrow, lhs: &[u64], rhs: &[u64], out: *mut u64) -> Borrow {
    //! # Safety
    //!
    //! `lhs` must be longer than `rhs`, and the length of `out` must equal to the length of `lhs`.
    debug_assert!(lhs.len() >= rhs.len());
    borrow = subborrow_ubig_equal_len(borrow, lhs.as_ptr(), rhs.as_ptr(), out, rhs.len());
    return sub_borrow_from_ubig(borrow, lhs.as_ptr().wrapping_add(rhs.len()), out.wrapping_add(rhs.len()), lhs.len() - rhs.len());
}

#[inline]
pub unsafe fn sub_borrow_from_ubig(mut borrow: Borrow, src: *const u64, dst: *mut u64, len: usize) -> Borrow {
    //! # Safety
    //!
    //! the length of `src` and `dst` must be equal to `len`.
    for index in 0..len {
        let s = src.wrapping_add(index);
        let d = dst.wrapping_add(index);
        borrow = subborrow_u64(borrow, *s, 0, d);
    }
    borrow
}


#[inline(always)]
pub fn mul_u64(lhs: u64, rhs: u64) -> [u64; 2] {
    let res = lhs as u128 * rhs as u128;
    let low64 = res & (u64::MAX as u128);
    let high64 = res >> 64;
    [low64 as u64, high64 as u64]
}

#[allow(dead_code)]
pub fn mul_u64_no_u128(lhs: u64, rhs: u64) -> [u64; 2] {
    const LOW32: u64 = u32::MAX as u64;

    let (l0, l1) = (lhs & LOW32, lhs >> 32);
    let (r0, r1) = (rhs & LOW32, rhs >> 32);

    let m00 = l0 * r0; // * (2^32)^0
    let m10 = l1 * r0; // * (2^32)^1
    let m01 = l0 * r1; // * (2^32)^1
    let m11 = l1 * r1; // * (2^32)^2

    // carry from low64 to high64
    let carry = ((m00 >> 32) + (m10 & LOW32) + (m01 & LOW32)) >> 32;

    let low64 = m00 + (m10 << 32) + (m01 << 32);
    let high64 = m11 + (m10 >> 32) + (m01 >> 32) + carry;
    [low64, high64]
}

pub unsafe fn mul_ubig_u64(lhs: &[u64], rhs: u64, out: *mut u64) {
    //! # Safety
    //!
    //! the length of `out` must be `lhs.len()) + 1`.
    let mut carry = Carry::zero();
    let mut high64_from_lower = 0;
    for index in 0..lhs.len() {
        let l = lhs.get_unchecked(index);
        let o = out.wrapping_add(index);
        let [low64, high64] = mul_u64(*l, rhs);
        carry = addcarry_u64(carry, low64, high64_from_lower, o);
        high64_from_lower = high64;
    }
    // high64 from highest part
    let o = out.wrapping_add(lhs.len());
    carry = addcarry_u64(carry, 0, high64_from_lower, o);
    debug_assert!(!carry.has());
}

pub unsafe fn mul_ubig(lhs: &[u64], rhs: &[u64], out: *mut u64, tmp: *mut u64) {
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


pub unsafe fn mul_ubig_u64_addto(lhs: &[u64], rhs: u64, mut out: *mut u64) -> Carry {
    //! #Safety
    //!
    //! `out.len() = lhs.len() + 1`
    let (mut c0, mut c1) = (Carry::zero(), Carry::zero());
    for l in lhs {
        let [low64, high64] = mul_u64(*l, rhs);
        c0 = addcarry_u64(c0, *out, low64, out);
        out = out.wrapping_add(1);
        c0 = addcarry_u64(c0, *out, high64, out);
        (c0, c1) = (c1, c0);
    }
    c0 = addcarry_u64(c0, *out, 0, out);
    c0 | c1
}

#[allow(dead_code)]
pub unsafe fn mul_ubig_addto(lhs: &[u64], rhs: &[u64], mut out: *mut u64) -> Carry {
    //! #Safety
    //!
    //! `out.len() = lhs.len() + rhs.len()`
    let mut end_carry = Carry::zero();
    for r in rhs {
        let last_end = out.wrapping_add(lhs.len());
        end_carry = addcarry_u64(end_carry, *last_end, 0, last_end);

        end_carry |= mul_ubig_u64_addto(lhs, *r, out);

        out = out.wrapping_add(1);
    }
    end_carry
}


#[allow(dead_code)]
pub fn next_power_of_two(x: usize) -> usize {
    if x == 0 {
        return 0;
    }
    let mut y = x - 1;
    y |= y >> 1;
    y |= y >> 2;
    y |= y >> 4;
    y |= y >> 8;
    y |= y >> 16;
    if size_of::<usize>() > 32/8 {
        y |= y >> 32;
    }
    return y + 1;
}

#[inline(never)]
pub unsafe fn karatsuba_mul_power_of_two_len(lhs: *const u64, rhs: *const u64, out: *mut u64, tmp: *mut u64, len: usize) {
    //! # Safety
    //!
    //! lhs.len() = b.len() = len, out.len() = tmp.len() = 2*len,
    //! len must be a power of 2.
    debug_assert!(len.is_power_of_two() && len > 0);
    if len == 1 {
        let [low64, high64] = mul_u64(*lhs, *rhs);
        *out = low64;
        *(out.wrapping_add(1)) = high64;
        return;
    }

    let half_len = len >> 1;
    let (l0, l1) = (lhs, lhs.wrapping_add(half_len));
    let (r0, r1) = (rhs, rhs.wrapping_add(half_len));
    let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
    let (o0, o1) = (out, out.wrapping_add(half_len));
    let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

    // a_ = a0 + a1
    let a_ = o0;
    let a_carry = addcarry_ubig_equal_len(Carry::zero(), l0, l1, a_, half_len);
    // b_ = b0 + b1
    let b_ = o1;
    let b_carry = addcarry_ubig_equal_len(Carry::zero(), r0, r1, b_, half_len);
    // z_ = a_ * b_
    let z_ = t0;
    let overflow = karatsuba_mulcarry_power_of_two_len(a_, a_carry, b_, b_carry, z_, next_tmp, half_len);

    // z0 = a0 * b0
    let z0 = o0;
    karatsuba_mul_power_of_two_len(l0, r0, z0, next_tmp, half_len);
    // z2 = a1 * b1
    let z2 = o2;
    karatsuba_mul_power_of_two_len(l1, r1, z2, next_tmp, half_len);

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

#[inline(never)]
unsafe fn karatsuba_mulcarry_power_of_two_len(
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
        let out_high = out.wrapping_add(1);
        *out = low64;
        *out_high = high64;

        let mut overflow = (lhs_carry & rhs_carry).as_u8();
        if lhs_carry.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *rhs, out_high).as_u8(); }
        if rhs_carry.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *lhs, out_high).as_u8(); }
        return overflow;
    }

    let half_len = len >> 1;
    let (a0, a1) = (lhs, lhs.wrapping_add(half_len));
    let (b0, b1) = (rhs, rhs.wrapping_add(half_len));
    let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
    let (o0, o1) = (out, out.wrapping_add(half_len));
    let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

    // a_ = a0 + a1
    let a_ = o0;
    let a_carry = addcarry_ubig_equal_len(Carry::zero(), a0, a1, a_, half_len);
    // b_ = b0 + b1
    let b_ = o1;
    let b_carry = addcarry_ubig_equal_len(Carry::zero(), b0, b1, b_, half_len);
    // z_ = a_ * b_
    let z_ = t0;
    let overflow = karatsuba_mulcarry_power_of_two_len(a_, a_carry, b_, b_carry, z_, next_tmp, half_len);

    // z0 = a0 * b0
    let z0 = o0;
    karatsuba_mul_power_of_two_len(a0, b0, z0, next_tmp, half_len);
    // z2 = a1 * b1
    let z2 = o2;
    karatsuba_mul_power_of_two_len(a1, b1, z2, next_tmp, half_len);

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


#[inline(never)]
pub unsafe fn karatsuba_mul_equal_len(lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize, tmp: *mut u64) {
    //! # Safety
    //!
    //! lhs.len() = rhs.len() = len; out.len() = 2*len; tmp.len() = 2*next_power_of_two(len)
    debug_assert!(len > 0);
    if len.is_power_of_two() {
        return karatsuba_mul_power_of_two_len(lhs, rhs, out, tmp, len);
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
        let l0 = slice::from_raw_parts(l0, half_len);
        let l1 = slice::from_raw_parts(l1, extra_len);
        addcarry_ubig_lhs_longer(Carry::zero(), l0, l1, l_)
    };
    // r_ = r0 + r1
    let r_ = out.wrapping_add(half_len);
    let r_carry = {
        let r0 = slice::from_raw_parts(r0, half_len);
        let r1 = slice::from_raw_parts(r1, extra_len);
        addcarry_ubig_lhs_longer(Carry::zero(), r0, r1, r_)
    };

    // z_ = l_ * r_
    let z_ = tmp;
    let overflow = karatsuba_mulcarry_power_of_two_len(l_, l_carry, r_, r_carry, z_, next_tmp, half_len);

    // z0 = l0 * r0
    let z0 = out;
    karatsuba_mul_power_of_two_len(l0, r0, z0, next_tmp, half_len);
    // z2 = l1 * r1
    let z2 = out.wrapping_add(full_len);
    karatsuba_mul_equal_len(l1, r1, z2, extra_len, next_tmp);

    // z1 = z_ - z0 - z1
    let z1 = z_;
    let borrow0 = subborrow_ubig_equal_len(Borrow::zero(), z_, z0, z_, full_len);
    let borrow1 = {
        let z1_slice = slice::from_raw_parts(z1, full_len);
        let z2 = slice::from_raw_parts(z2, extra_len << 1);
        subborrow_ubig_lhs_longer(Borrow::zero(), z1_slice, z2, z1)
    };
    debug_assert!(overflow == borrow0.as_u8() + borrow1.as_u8());
    // and also should all elements above z1[len] are 0s
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

#[allow(dead_code)]
#[inline]
pub unsafe fn karatsuba_mul_lhs_longer(lhs: &[u64], rhs: &[u64], out: *mut u64, tmp: *mut u64) {
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
    karatsuba_mul_equal_len(l0, r0, z0, half_len, tmp);

    // z1 = l1 * r0
    if extra_len == 0 {
        return;
    }
    let z1 = tmp;
    let next_tmp = tmp.wrapping_add(lhs.len());
    if extra_len >= half_len {
        karatsuba_mul_lhs_longer(l1, rhs, z1, next_tmp);
    } else {
        karatsuba_mul_lhs_longer(rhs, l1, z1, next_tmp);
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

#[inline]
pub fn karatsuba_anylen_tmp_len(lhs_len: usize, rhs_len: usize) -> usize {
    if rhs_len < 2 {
        return 0;
    }
    let z0_len = rhs_len.next_power_of_two() << 1;
    // assume: lhs_len = n * rhs_len + m
    let (n, m) = (lhs_len / rhs_len, lhs_len % rhs_len);
    let curr = n * m + (n * (n + 1) / 2) * rhs_len;
    let next = karatsuba_anylen_tmp_len(rhs_len, m);
    curr + z0_len + next
}


pub unsafe fn karatsuba_mul_lhs_longer_stack<'a>(mut lhs: &'a [u64], mut rhs: &'a [u64], mut out: *mut u64, mut tmp: *mut u64) {
    //! # Safety
    //!
    //! lhs.len() > rhs.len(); out.len() = lhs.len() + rhs.len(); tmp.len() = karatsuba_tmp_len(lhs.len(), rhs.len())
    debug_assert!(lhs.len() >= rhs.len());

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
        karatsuba_mul_equal_len(l0, r0, z0, half_len, tmp);

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
