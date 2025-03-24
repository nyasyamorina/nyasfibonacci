use std::ops::{BitAnd, BitOr, BitOrAssign};

//================================    not x86_64    ================================//

#[cfg(not(target_arch = "x86_64"))]
#[derive(Debug, Clone, Copy)]
/// It seems that there is no way in Rust to convert u8 (0 and 1) directly to bool without performance loss.
/// This `Carry` struct holds bool when using "normal" mod, and holds u8 when using x86 instructions.
pub struct Carry(bool);
#[cfg(not(target_arch = "x86_64"))]
impl Carry {
    #[inline(always)]
    /// the 0 carry (no carrh)
    pub fn zero() -> Carry {
        Carry(false)
    }
    #[inline(always)]
    /// the 1 carry (has carrh)
    pub fn one() -> Carry {
        Carry(true)
    }

    #[inline(always)]
    /// construct carry directly from inside value
    pub unsafe fn from(carry: bool) -> Carry {
        Carry(carry)
    }
    #[inline(always)]
    /// get the value inside, `bool` for "normal" mode, `u8` for x86
    pub fn get(&self) -> bool {
        self.0
    }

    #[inline(always)]
    /// returns a bool to indicate whether there is a carry
    pub fn has(&self) -> bool {
        self.0
    }

    #[inline(always)]
    /// returns a u8, 0 for no carry, 1 for carry
    pub fn as_u64(&self) -> u64 {
        if self.0 { 1 } else { 0 }
    }
    #[inline(always)]
    /// returns a u8, 0 for no carry, 1 for carry
    pub fn as_u8(&self) -> u8 {
        if self.0 { 1 } else { 0 }
    }
    #[inline(always)]
    /// convert u8 to carry, 0 for no carry, 1 for carry.
    /// there is performance loss.
    pub unsafe fn from_u8(x: u8) -> Carry {
        debug_assert!(x == 0 || x == 1);
        Carry(x != 0)
    }
}

#[inline(always)] // used in karatsuba mul
#[cfg(not(target_arch = "x86_64"))]
pub fn sub_borrow_from_overflow_to_carry(overflow: u8, borrow0: Borrow, borrow1: Borrow) -> Carry {
    let borrow = borrow0.as_u8() + borrow1.as_u8();
    debug_assert!(overflow == borrow || overflow == borrow + 1);
    unsafe { Carry::from(overflow > borrow) }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
/// *out = lhs + rhs + carry, returns carry
pub unsafe fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: *mut u64) -> Carry {
    let tmp = lhs + carry.as_u8();
    *out = tmp + rhs;
    unsafe { Carry::from(tmp < lhs || *out < tmp) }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
/// *out = lhs - rhs - borrow, returns borrow
pub unsafe fn subborrow_u64(borrow: Borrow, lhs: u64, rhs: u64, out: *mut u64) -> Borrow {
    let tmp = lhs - borrow.as_u8();
    *out = tmp - rhs;
    unsafe { Borrow::from(tmp > lhs || *out > tmp) }
}

#[allow(dead_code)]
/// impl `addcarry_u64` using `u64::overflowing_add` built in rust
pub unsafe fn addcarry_u64_rust(carry: bool, lhs: u64, rhs: u64, out: *mut u64) -> bool {
    let (c0, c1);
    (*out, c0) = lhs.overflowing_add(if carry { 1 } else { 0 });
    (*out, c1) = rhs.overflowing_add(*out);
    c0 || c1
}

//================================      x86_64      ================================//


#[cfg(target_arch = "x86_64")]
#[derive(Debug, Clone, Copy)]
/// It seems that there is no way in Rust to convert u8 (0 and 1) directly to bool without performance loss.
/// This `Carry` struct holds bool when using "normal" mod, and holds u8 when using x86 instructions.
pub struct Carry(u8);
#[cfg(target_arch = "x86_64")]
impl Carry {
    #[inline(always)]
    /// the 0 carry (no carrh)
    pub fn zero() -> Carry {
        Carry(0)
    }
    #[inline(always)]
    /// the 1 carry (has carrh)
    pub fn one() -> Carry {
        Carry(1)
    }

    #[inline(always)]
    /// construct carry directly from inside value
    pub unsafe fn from(carry: u8) -> Carry {
        Carry(carry)
    }
    #[inline(always)]
    /// get the value inside, `bool` for "normal" mode, `u8` for x86
    pub fn get(&self) -> u8 {
        self.0
    }

    #[inline(always)]
    /// returns a bool to indicate whether there is a carry.
    /// there may be a performance loss if not used in conditional branches.
    pub fn has(&self) -> bool {
        self.0 != 0
    }

    #[inline(always)]
    /// returns a u8, 0 for no carry, 1 for carry
    pub fn as_u64(&self) -> u64 {
        self.0 as u64
    }
    #[inline(always)]
    /// returns a u8, 0 for no carry, 1 for carry
    pub fn as_u8(&self) -> u8 {
        self.0
    }
    #[inline(always)]
    /// convert u8 to carry, 0 for no carry, 1 for carry
    pub unsafe fn from_u8(x: u8) -> Carry {
        debug_assert!(x == 0 || x == 1);
        Carry(x)
    }
}

#[inline(always)] // used in karatsuba mul
#[cfg(target_arch = "x86_64")]
pub fn sub_borrow_from_overflow_to_carry(overflow: u8, borrow0: Borrow, borrow1: Borrow) -> Carry {
    let borrow = borrow0.as_u8() + borrow1.as_u8();
    debug_assert!(overflow == borrow || overflow == borrow + 1);
    let carry = overflow - borrow;
    unsafe { Carry::from(carry) }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
/// *out = lhs + rhs + carry, returns carry
pub unsafe fn addcarry_u64(carry: Carry, lhs: u64, rhs: u64, out: *mut u64) -> Carry {
    //! note that in this version of `addcarry_u64`, the carry is a `u8` rather than a `bool`,
    //! because Rust cannot convert a `u8` to a `bool` without doing a comparison.
    unsafe { Carry::from(core::arch::x86_64::_addcarry_u64(carry.get(), lhs, rhs, &mut *out)) }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
/// *out = lhs - rhs - borrow, returns borrow
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
/// returns `lhs * rhs` as 2 u64s
pub fn mul_u64(lhs: u64, rhs: u64) -> [u64; 2] {
    let res = lhs as u128 * rhs as u128;
    let low64 = res & (u64::MAX as u128);
    let high64 = res >> 64;
    [low64 as u64, high64 as u64]
}

#[allow(dead_code)]
/// impl `mul_u64` without using u128
pub fn mul_u64_no_u128(lhs: u64, rhs: u64) -> [u64; 2] {
    const LOW32: u64 = u32::MAX as u64;

    let (l0, l1) = (lhs & LOW32, lhs >> 32);
    let (r0, r1) = (rhs & LOW32, rhs >> 32);

    let m00 = l0 * r0; // * (2^32)^0
    let m10 = l1 * r0; // * (2^32)^1
    let m01 = l0 * r1; // * (2^32)^1
    let m11 = l1 * r1; // * (2^32)^2

    // overflow from low64 to high64
    let overflow = ((m00 >> 32) + (m10 & LOW32) + (m01 & LOW32)) >> 32;

    let low64 = m00 + (m10 << 32) + (m01 << 32);
    let high64 = m11 + (m10 >> 32) + (m01 >> 32) + overflow;
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

#[allow(dead_code)] // used in `fibonacci_removed_matrix_abstract::<ElementarySchool>` at "rev_pow.rs: 84"
/// *out += lhs * rhs
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


pub unsafe fn set_to_zeros(mut x: *mut u64, len: usize) {
    // looks like rust does not have memset function.
    let stop = x.wrapping_add(len);
    while x < stop {
        *x = 0;
        x = x.wrapping_add(1);
    }
}

pub unsafe fn is_all_zeros(mut x: *const u64, len: usize) -> bool {
    let stop = x.wrapping_add(len);
    while x < stop {
        if *x != 0 {
            return false;
        }
        x = x.wrapping_add(1);
    }
    true
}


const _: () = assert!(usize::BITS == 32 || usize::BITS == 64);
const USIZE_HAS_64BITS: bool = usize::BITS == 64;

#[allow(dead_code)]
/// return the next power of 2 that is greater than or equal to x.
/// of cause everyone use `usize::next_power_of_two` in rust.
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
    if USIZE_HAS_64BITS {
        y |= y >> 32;
    }
    return y + 1;
}

#[allow(dead_code)]
/// reverse the bits inside integer.
/// of cause everyone use `usize::reverse_bits` in rust.
pub fn reverse_bits(x: usize) -> usize {
    if USIZE_HAS_64BITS {
        let low32 = reverse_bits_u32((x & u32::MAX as usize) as u32) as usize;
        let high32 = reverse_bits_u32((x >> 32) as u32) as usize;
        return (low32 << 32) | high32;
    } else {
        return reverse_bits_u32(x as u32) as usize;
    }

    fn reverse_bits_u32(x: u32) -> u32 {
        let x = ((x & 0b11111111111111110000000000000000) >> 16) | ((x & 0b00000000000000001111111111111111) << 16);
        let x = ((x & 0b11111111000000001111111100000000) >>  8) | ((x & 0b00000000111111110000000011111111) <<  8);
        let x = ((x & 0b11110000111100001111000011110000) >>  4) | ((x & 0b00001111000011110000111100001111) <<  4);
        let x = ((x & 0b11001100110011001100110011001100) >>  2) | ((x & 0b00110011001100110011001100110011) <<  2);
        let x = ((x & 0b10101010101010101010101010101010) >>  1) | ((x & 0b01010101010101010101010101010101) <<  1);
        x
    }
}

pub trait IntegerBits {
    fn bits(&self) -> u32;
}
impl IntegerBits for usize {
    fn bits(&self) -> u32 {
        Self::BITS - self.leading_zeros()
    }
}

pub trait ShrCeil {
    /// find `k` that `k*2^n >= x`.
    fn shr_ceil(&self, n: u32) -> Self;
}
impl ShrCeil for usize {
    fn shr_ceil(&self, n: u32) -> Self {
        let mask = (1 << n) - 1;
        (self >> n) + (if self & mask != 0 { 1 } else { 0 })
    }
}
