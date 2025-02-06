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
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: &mut u64) -> Carry {
    let carry = if carry.has() { 1 } else { 0 };
    let tmp = lhs + carry;
    *out = tmp + rhs;
    Carry::from(tmp < lhs || *out < tmp)
}

#[allow(dead_code)]
pub fn addcarry_u64_rust(carry: bool, lhs: u64, rhs: u64, out: &mut u64) -> bool {
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
    pub fn from(carry: u8) -> Carry {
        Carry(carry)
    }

    #[inline(always)]
    pub fn has(&self) -> bool {
        self.0 != 0
    }
    #[inline(always)]
    pub fn get(&self) -> u8 {
        self.0
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub unsafe fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: &mut u64) -> Carry {
    //! note that in this version of `addcarry_u64`, the carry is a `u8` rather than a `bool`,
    //! because Rust cannot convert a `u8` to a `bool` without doing a comparison.
    Carry::from(core::arch::x86_64::_addcarry_u64(carry.get(), lhs, rhs, out))
}

//================================      common      ================================//


#[inline]
pub unsafe fn addcarry(mut carry: Carry, lhs: *const u64, rhs: *const u64, out: *mut u64, len: usize) -> Carry {
    //! # Safety
    //!
    //! the length of `lhs`, `rhs` and `out` must be equal to `len`.
    for index in 0..len {
        let l = lhs.wrapping_add(index);
        let r = rhs.wrapping_add(index);
        let o = out.wrapping_add(index);
        carry = addcarry_u64(carry, *l, *r, &mut *o);
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
        carry = addcarry_u64(carry, *s, 0, &mut *d);
    }
    carry
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

pub unsafe fn mul_ubig_u64(lhs: *const u64, rhs: u64, out: *mut u64, len: usize) {
    //! # Safety
    //!
    //! the length of lhs must be `len`, the length of `out` must be `len+1`.
    let mut carry = Carry::zero();
    let mut high64_from_lower = 0;
    for index in 0..len {
        let l = lhs.wrapping_add(index);
        let o = out.wrapping_add(index);
        let [low64, high64] = mul_u64(*l, rhs);
        carry = addcarry_u64(carry, low64, high64_from_lower, &mut *o);
        high64_from_lower = high64;
    }
    // high64 from highest part
    let o = out.wrapping_add(len);
    carry = addcarry_u64(carry, 0, high64_from_lower, &mut *o);
    debug_assert!(!carry.has());
}

pub unsafe fn mul_ubig(lhs: *const u64, llen: usize, rhs: *const u64, rlen: usize, out: *mut u64, tmp: *mut u64) {
    //! # Safety
    //!
    //! lhs.len() = llen, rhs.len() = rlen, out.len() = llen+rlen, tmp.len() = llen+1.
    //! `out` must init with all 0s.
    for index in 0..rlen {
        let r = rhs.wrapping_add(index);
        let o = out.wrapping_add(index);
        mul_ubig_u64(lhs, *r, tmp, llen);
        let carry = addcarry(Carry::zero(), o, tmp, o, llen + 1);
        debug_assert!(!carry.has());
    }
}
