use std::ops::{BitOr, BitOrAssign, BitAnd};

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
    pub fn one() -> Carry {
        Carry(true)
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
    pub fn one() -> Carry {
        Carry(1)
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
pub unsafe fn addcarry(mut carry: Carry, lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize) -> Carry {
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
pub unsafe fn add1(src: *const u64, dst: *mut u64, len: usize) -> Carry {
    //! # Safety
    //!
    //! the length of `src` and `dst` must be equal to `len`.
    let mut carry = Carry::one();
    for index in 0..len {
        let s = src.wrapping_add(index);
        let d = dst.wrapping_add(index);
        carry = addcarry_u64(carry, *s, 0, d);
    }
    carry
}


#[inline]
pub unsafe fn subborrow(mut borrow: Borrow, lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize) -> Borrow {
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
        let carry = addcarry(Carry::zero(), o, tmp, o, lhs.len() + 1);
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


#[inline]
pub unsafe fn karatsuba_mul(a: *const u64, b: *const u64, out: *mut u64, tmp: *mut u64, len: usize) {
    //! # Safety
    //!
    //! a.len() = b.len() = len, out.len() = tmp.len() = 2*len,
    //! len must be a power of 2.
    debug_assert!(len & (len - 1) == 0 && len != 0);
    if len == 1 {
        let [low64, high64] = mul_u64(*a, *b);
        *out = low64;
        *(out.wrapping_add(1)) = high64;
        return;
    }

    let half_len = len >> 1;
    let (a0, a1) = (a, a.wrapping_add(half_len));
    let (b0, b1) = (b, b.wrapping_add(half_len));
    let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
    let (o0, o1) = (out, out.wrapping_add(half_len));
    let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

    // a_ = a0 + a1
    let a_ = o0;
    let a_carry = addcarry(Carry::zero(), a0, a1, a_, half_len);
    // b_ = b0 + b1
    let b_ = o1;
    let b_carry = addcarry(Carry::zero(), b0, b1, b_, half_len);
    // z_ = a_ * b_
    let z_ = t0;
    let overflow = karatsuba_mulcarry(a_, a_carry, b_, b_carry, z_, next_tmp, half_len);

    // z0 = a0 * b0
    let z0 = o0;
    karatsuba_mul(a0, b0, z0, next_tmp, half_len);
    // z2 = a1 * b1
    let z2 = o2;
    karatsuba_mul(a1, b1, z2, next_tmp, half_len);

    // z1 = z_ - z0 - z2;
    let z1 = t0;
    let borrow0 = subborrow(Borrow::zero(), z_, z0, z1, len);
    let borrow1 = subborrow(Borrow::zero(), z1, z2, z1, len);
    let z1_carry = sub_borrow_from_overflow_to_carry(overflow, borrow0, borrow1);

    // add z1 to out
    if z1_carry.has() {
        let carry = add1(o3, o3, half_len);
        debug_assert!(!carry.has());
    }
    let carry = addcarry(Carry::zero(), o1, z1, o1, len);
    if carry.has() {
        let carry = add1(o3, o3, half_len);
        debug_assert!(!carry.has());
    }
}

#[inline]
unsafe fn karatsuba_mulcarry(a: *const u64, a_c: Carry, b: *const u64, b_c: Carry, out: *mut u64, tmp: *mut u64, len: usize) -> u8 {
    //! # Safety
    //!
    //! a.len() = b.len() = len, out.len() = tmp.len() = 2*len,
    //! len must be a power of 2.
    debug_assert!(len & (len - 1) == 0 && len != 0);
    if len == 1 {
        let [low64, high64] = mul_u64(*a, *b);
        let out_high = out.wrapping_add(1);
        *out = low64;
        *out_high = high64;

        let mut overflow = (a_c & b_c).as_u8();
        if a_c.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *b, out_high).as_u8(); }
        if b_c.has() { overflow += addcarry_u64(Carry::zero(), *out_high, *a, out_high).as_u8(); }
        return overflow;
    }

    let half_len = len >> 1;
    let (a0, a1) = (a, a.wrapping_add(half_len));
    let (b0, b1) = (b, b.wrapping_add(half_len));
    let (t0, next_tmp) = (tmp, tmp.wrapping_add(len));
    let (o0, o1) = (out, out.wrapping_add(half_len));
    let (o2, o3) = (out.wrapping_add(len), out.wrapping_add(len + half_len));

    // a_ = a0 + a1
    let a_ = o0;
    let a_carry = addcarry(Carry::zero(), a0, a1, a_, half_len);
    // b_ = b0 + b1
    let b_ = o1;
    let b_carry = addcarry(Carry::zero(), b0, b1, b_, half_len);
    // z_ = a_ * b_
    let z_ = t0;
    let overflow = karatsuba_mulcarry(a_, a_carry, b_, b_carry, z_, next_tmp, half_len);

    // z0 = a0 * b0
    let z0 = o0;
    karatsuba_mul(a0, b0, z0, next_tmp, half_len);
    // z2 = a1 * b1
    let z2 = o2;
    karatsuba_mul(a1, b1, z2, next_tmp, half_len);

    // z1 = z_ - z0 - z2;
    let z1 = t0;
    let borrow0 = subborrow(Borrow::zero(), z_, z0, z1, len);
    let borrow1 = subborrow(Borrow::zero(), z1, z2, z1, len);
    let z1_carry = sub_borrow_from_overflow_to_carry(overflow, borrow0, borrow1);

    // add z1 to out
    let mut overflow = (a_c & b_c).as_u8();
    if z1_carry.has() { overflow += add1(o3, o3, half_len).as_u8(); }
    let carry = addcarry(Carry::zero(), o1, z1, o1, len);
    if carry.has() { overflow += add1(o3, o3, half_len).as_u8(); }
    // extra addition
    if a_c.has() { overflow += addcarry(Carry::zero(), o2, b, o2, len).as_u8(); }
    if b_c.has() { overflow += addcarry(Carry::zero(), o2, a, o2, len).as_u8(); }

    debug_assert!(overflow < 4);
    return overflow;
}
