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

#[allow(unused)]
pub fn addcarry_u64_rust(carry: bool, lhs: u64, rhs: u64, out: &mut u64) -> bool {
    let (mut c0, mut c1);
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
