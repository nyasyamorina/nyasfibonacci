use crate::{UBig, UBigMul};
use crate::mul::karatsuba::KaratsubaEqualLength;
use crate::helpers::*;

use std::ptr;


#[allow(non_snake_case)]
struct SchönhageStrassenOps {
    N: usize,
    L: usize,
    l: u32,
    n: usize,
    M: usize,
    y: usize,

    log2_inv_L: u64,
}
//#[allow(non_snake_case)]
impl SchönhageStrassenOps {
    const FASTER_CONVERGENCE_COND: bool = true;

    #[cfg(debug_assertions)]
    const MINIMUM_N: usize = if Self::FASTER_CONVERGENCE_COND { 30 } else { 9 };
    #[cfg(not(debug_assertions))]
    const MINIMUM_N: usize = 256;

    #[allow(non_snake_case)]
    fn convergence_cond(N: usize, M: usize) -> bool {
        if Self::FASTER_CONVERGENCE_COND {
            M.bits() < N.bits()
        } else {
            M < N
        }
    }

    #[allow(non_snake_case)]
    fn first_init(min_len: usize) -> Option<Self> {
        if min_len < Self::MINIMUM_N {
            return None;
        }

        let l = min_len.bits() >> 1;
        let L = 1 << l;
        let n = min_len.shr_ceil(l);
        let N = n << l;
        let y = (l as usize + (n << 1)).shr_ceil(l);
        let M = y << l;
        let log2_inv_L = (M as u64 * (2 * u64::BITS) as u64) - l as u64;
        debug_assert!(Self::convergence_cond(N, M));
        Some(SchönhageStrassenOps { N, L, l, n, M, y, log2_inv_L })
    }

    #[allow(non_snake_case)]
    fn recursion_init(upper_M: usize) -> Option<SchönhageStrassenOps> {
        if upper_M < Self::MINIMUM_N {
            return None;
        }

        let l = upper_M.bits() >> 1;
        let L = 1 << l;
        let n = upper_M >> l;
        debug_assert!(upper_M == n << l);
        let y = (l as usize + (n << 1)).shr_ceil(l);
        let M = y << l;
        let log2_inv_L = (M as u64 * (2 * u64::BITS) as u64) - l as u64;
        //debug_assert!(M.bits() < upper_M.bits());
        debug_assert!(Self::convergence_cond(upper_M, M));
        Some(SchönhageStrassenOps { N: upper_M, L, l, n, M, y, log2_inv_L })
    }

    fn num_len(&self) -> usize {
        self.N + 1
    }

    fn ele_len(&self) -> usize {
        self.M + 1
    }

    fn arr_len(&self) -> usize {
        self.ele_len() << self.l
    }

    fn shift_buff_len(&self) -> usize {
        self.M << 1
    }

    fn mul_tmp_len(&self) -> usize {
        let len = self.arr_len() << 1; // for two arrays
        let len = len + self.shift_buff_len();
        len
    }

    fn sqr_tmp_len(&self) -> usize {
        let len = self.arr_len(); // for one array
        let len = len + self.shift_buff_len();
        len
    }

    #[allow(dead_code)]
    unsafe fn print_num(&self, num: *const u64) {
        print!("---- num begin");
        print_ubig(num, self.N);
        println!("\n---- num end");
    }

    #[allow(dead_code)]
    unsafe fn print_arr(&self, arr: *const u64) {
        let mut ele = arr;
        print!("---- arr begin");
        for k in 0..self.L {
            print!("\n  -- {k}");
            print_ubig(ele, self.ele_len());
            ele = ele.wrapping_add(self.M);
        }
        println!("\n---- arr end");
    }

    #[allow(dead_code)]
    unsafe fn print_ele(&self, ele: *const u64) {
        print!("---- ele begin");
        print_ubig(ele, self.M);
        println!("\n---- ele end");
    }

    unsafe fn for_each_eles<F>(&self, arr: *mut u64, mut f: F) where
        F: FnMut(*mut u64, usize),
    {
        let mut element = arr;
        for k in 0..self.L {
            f(element, k);
            element = element.wrapping_add(self.ele_len());
        }
    }

    unsafe fn for_each_ele_pairs<F>(&self, arr1: *mut u64, arr2: *mut u64, mut f: F) where
        F: FnMut(*mut u64, *mut u64, usize),
    {
        let mut ele1 = arr1;
        let mut ele2 = arr2;
        for k in 0..self.L {
            f(ele1, ele2, k);
            ele1 = ele1.wrapping_add(self.ele_len());
            ele2 = ele2.wrapping_add(self.ele_len());
        }
    }

    unsafe fn divide_num_to_arr(&self, num: *const u64, arr: *mut u64) {
        let mut num_part = num;
        let mut ele = arr;

        for _ in 0..self.L {
            ptr::copy_nonoverlapping(num_part, ele, self.n);

            set_to_zeros(ele.wrapping_add(self.n), self.ele_len() - self.n);

            num_part = num_part.wrapping_add(self.n);
            ele = ele.wrapping_add(self.ele_len());
        }
    }

    unsafe fn combine_arr_to_num(&self, num: *mut u64, arr: *mut u64) {
        set_to_zeros(num, self.num_len());
        let mut ele = arr;
        for k in 0..self.L {

            // there must be some simpler way to check element should be negative or not.
            let checking = ele.wrapping_add(self.n << 1);
            let should_be_negative = *checking > k as u64 ||
                !is_all_zeros(checking.wrapping_add(1), self.M - (self.n << 1));

            let borrow = self.pull_back_ele(ele, should_be_negative);
            self.add_ele_into_num(num, k, ele, borrow);

            ele = ele.wrapping_add(self.ele_len());
        }
    }

    unsafe fn pull_back_ele(&self, ele: *mut u64, should_be_negative: bool) -> Borrow {
        //! element must be not 0 and less than 2^(64\*M+1).
        let highest = ele.wrapping_add(self.M);
        if !should_be_negative {
            return Borrow::zero();
        }

        // subtract 2^(64*M)+1 from element
        let borrow = sub_borrow_from_ubig(Borrow::one(), ele, ele, self.M);
        let borrow = if *highest > borrow.as_u64() { Borrow::zero() } else { Borrow::one() };
        *highest = 0;
        borrow
    }

    unsafe fn add_ele_into_num(&self, num: *mut u64, k: usize, mut ele: *const u64, mut borrow: Borrow) {
        //! $num += (ele - borrow\*2^(64\*M)) \* 2^(64\*n\*k)$
        let num_highest = num.wrapping_add(self.num_len() - 1);
        let ele_highest = ele.wrapping_add(self.ele_len() - 1);
        let ring = RingOps { N: self.N };

        let mut num_ptr = num.wrapping_add(self.n * k);
        let mut carry = Carry::zero();

        loop {
            if ele == ele_highest {
                let extra_len = num_highest.offset_from(num_ptr) as usize;
                if borrow.has() && !carry.has() {
                    borrow = sub_borrow_from_ubig(borrow, num_ptr, num_ptr, extra_len);
                } else if !borrow.has() && carry.has() {
                    add_carry_to_ubig(carry, num_ptr, num_ptr, extra_len + 1);
                } else {
                    borrow = Borrow::zero();
                }
                ring.reduce(num, borrow.as_u64());
                return;

            } else if num_ptr == num_highest {
                num_ptr = num;
                *num_highest += carry.as_u64();

                let mut borrow2 = Borrow::zero();
                loop {
                    if ele == ele_highest {
                        let extra_len = num_highest.offset_from(num_ptr) as usize;
                        if borrow.has() && !borrow2.has() {
                            add_carry_to_ubig(Carry::one(), num_ptr, num_ptr, extra_len + 1);
                        } else if !borrow.has() && borrow2.has() {
                            borrow2 = sub_borrow_from_ubig(borrow2, num_ptr, num_ptr, extra_len);
                        } else {
                            borrow2 = Borrow::zero();
                        }
                        ring.reduce(num, borrow2.as_u64());
                        return;
                    }

                    borrow2 = subborrow_u64(borrow2, *num_ptr, *ele, num_ptr);
                    num_ptr = num_ptr.wrapping_add(1);
                    ele = ele.wrapping_add(1);
                }
            }

            carry = addcarry_u64(carry, *num_ptr, *ele, num_ptr);
            num_ptr = num_ptr.wrapping_add(1);
            ele = ele.wrapping_add(1);
        }
    }

    unsafe fn shift_in(&self, ele: *mut u64, k: usize, tmp: *mut u64) {
        //! $a \*≡ 2^(64 \* y\*k)$, note that this method guarantee $0 <= a <= 2^(64\*M)$
        if k == 0 { return; }
        RingOps { N: self.M }.shl_u64(ele, k * self.y, ele, tmp);
    }

    unsafe fn shift_out(&self, ele: *mut u64, k: usize, tmp: *mut u64) {
        //! $a /≡ 2^(64 \* y\*k)$, note that this method guarantee $0 <= a <= 2^(64\*M)$
        if k == 0 { return; }
        RingOps { N: self.M }.shl_u64(ele, k * ((self.M << 1) - self.y), ele, tmp);
    }

    unsafe fn fft(&self, arr: *mut u64, tmp: *mut u64) {
        let reindex = |index: usize| self.fft_reindex(index);
        self.apply_radix_2(arr, reindex, self.y << 1, tmp);
    }

    unsafe fn ifft(&self, arr: *mut u64, tmp: *mut u64) {
        let reindex = |index| index; // fft_reindex(fft_reindex(x)) = x
        self.apply_radix_2(arr, reindex, (self.M - self.y) << 1, tmp);
    }

    fn fft_reindex(&self, index: usize) -> usize {
        index.reverse_bits() >> (usize::BITS - self.l)
    }

    unsafe fn apply_radix_2<F: Fn(usize) -> usize>(&self, arr: *mut u64, reindexing: F, log2_root: usize, tmp: *mut u64) {
        let ring = RingOps { N: self.M };

        let mut log2_root = log2_root << (self.l - 1);
        let mut group_size = 1usize;
        let mut n_groups = self.L >> 1;
        for _layer in 0..self.l {

            let mut group_start = 0;
            for _group in 0..n_groups {

                let mut shift_u64s = 0;
                for index in 0..group_size {

                    let l_index = group_start + index;
                    let h_index = l_index + group_size;

                    let l_ele = self.get_ele(arr, reindexing(l_index));
                    let h_ele = self.get_ele(arr, reindexing(h_index));

                    ring.shl_u64(h_ele, shift_u64s, tmp, tmp);
                    ring.sub(l_ele, tmp, h_ele);
                    ring.add(l_ele, tmp, l_ele);

                    shift_u64s += log2_root;
                }
                group_start += group_size << 1;
            }
            group_size <<= 1;
            n_groups >>= 1;
            log2_root >>= 1;
        }
    }

    unsafe fn div_by_arr_len(&self, ele: *mut u64, tmp: *mut u64) {
        ptr::copy_nonoverlapping(ele, tmp, self.ele_len());
        RingOps { N: self.M }.shl_bit(ele, self.log2_inv_L, ele, tmp);
    }

    unsafe fn get_ele(&self, arr: *mut u64, k: usize) -> *mut u64 {
        arr.wrapping_add(k * self.ele_len())
    }
}


pub struct SchönhageStrassen {
    num_len: usize,
    buff: Vec<u64>,
    opss: Vec<SchönhageStrassenOps>,
}
#[allow(non_snake_case)]
impl SchönhageStrassen {
    fn init(len: usize) -> Self {
        let num_len;
        let mut tmp_len;
        let mut opss = vec![];

        if let Some(ops) = SchönhageStrassenOps::first_init(len) {
            num_len = ops.N + 1;
            tmp_len = ops.mul_tmp_len();

            let mut M = ops.M;
            opss.push(ops);

            while let Some(ops) = SchönhageStrassenOps::recursion_init(M) {
                tmp_len += ops.mul_tmp_len();
                M = ops.M;
                opss.push(ops);
            }

            tmp_len += M << 1; // for karatsuba output
            tmp_len += KaratsubaEqualLength::tmp_len(M);
        } else {
            num_len = len + 1;
            tmp_len = len << 1; // for karatsuba output
            tmp_len += KaratsubaEqualLength::tmp_len(len);
        }

        let buff = vec![0; tmp_len + (num_len << 1)];
        SchönhageStrassen { num_len, buff, opss }
    }

    fn run(&mut self, lhs: &[u64], rhs: &[u64]) {
        let a = self.buff.as_mut_ptr();
        let b = a.wrapping_add(self.num_len);
        let tmp = b.wrapping_add(self.num_len);

        unsafe {
            // copy numbers to buff
            ptr::copy_nonoverlapping(lhs.as_ptr(), a, lhs.len());
            ptr::copy_nonoverlapping(rhs.as_ptr(), b, rhs.len());
            set_to_zeros(a.wrapping_add(lhs.len()), self.num_len - lhs.len());
            set_to_zeros(b.wrapping_add(rhs.len()), self.num_len - rhs.len());

            self.exec(a, b, self.num_len - 1, tmp, 0);
        }
    }

    fn output(mut self) -> Vec<u64> {
        self.buff.truncate(self.num_len);
        self.buff
    }

    unsafe fn exec(&self, a: *mut u64, b: *const u64, N: usize, tmp: *mut u64, depth: usize) {
        //! a and b must be less than or equal to $2^(64\*N)$
        let a_highest = a.wrapping_add(N);
        let b_highest = b.wrapping_add(N);

        if *a_highest != 0 {
            if *b_highest != 0 {
                // 2^(64*N) * 2^(64\*N) ≡ 1
                *a_highest = 0;
                *a = 1;
            } else {
                RingOps{ N }.neg_to(b, a);
            }
            return;
        } else if *b_highest != 0 {
            RingOps{ N }.neg_to(a, a);
            return;
        }

        match self.opss.get(depth) {
            None => {
                let c_len = N << 1;
                let c = tmp;
                let next_tmp = c.wrapping_add(c_len);

                // c = a * b
                KaratsubaEqualLength::ptr_mul_eqlen(a, b, c, N, next_tmp);

                // a = c % (2^(64*N) + 1)
                RingOps { N }.combine_shift_tmp(c, a, false);
            },
            Some(ops) => {
                let A = tmp;
                let B = A.wrapping_add(ops.arr_len());
                let ops_tmp = B.wrapping_add(ops.arr_len());
                let next_tmp = ops_tmp.wrapping_add(ops.shift_buff_len());
                let C = A;
                let c = a;

                ops.divide_num_to_arr(a, A);
                ops.divide_num_to_arr(b, B);

                ops.for_each_eles(A, |A_k, k| ops.shift_in(A_k, k, ops_tmp));
                ops.for_each_eles(B, |B_k, k| ops.shift_in(B_k, k, ops_tmp));
                ops.fft(A, ops_tmp);
                ops.fft(B, ops_tmp);

                // recursion mul per elements
                ops.for_each_ele_pairs(A, B, |A_k, B_k, _|
                    self.exec(A_k, B_k, ops.M, next_tmp, depth + 1)
                );

                ops.ifft(C, ops_tmp);
                ops.for_each_eles(C, |C_k, k| {
                    ops.div_by_arr_len(C_k, ops_tmp);
                    ops.shift_out(C_k, k, ops_tmp);
                });

                ops.combine_arr_to_num(c, C);
            },
        }
    }
}

impl UBigMul for SchönhageStrassen {
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig {
        if lhs.data.len() == 0 || rhs.data.len() == 0 {
            return UBig::zero();
        }
        let out_len = lhs.data.len() + rhs.data.len();
        let mut ss = Self::init(out_len);

        ss.run(&lhs.data, &rhs.data);

        let mut res = UBig::from_vec(ss.output());
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }

    fn sqr(x: &UBig) -> UBig {
        if x.data.len() == 0 {
            return UBig::zero();
        }
        let out_len = x.data.len() << 1;
        let mut ss = SchönhageStrassenSqr::init(out_len);

        ss.run(&x.data);

        let mut res = UBig::from_vec(ss.output());
        res.truncate(); // the highest part can be 0 in mul, remove it if it is 0
        res
    }
}


// special edition for number square $x^2$
struct SchönhageStrassenSqr {
    num_len: usize,
    buff: Vec<u64>,
    opss: Vec<SchönhageStrassenOps>,
}
#[allow(non_snake_case)]
impl SchönhageStrassenSqr {
    fn init(len: usize) -> Self {
        let num_len;
        let mut tmp_len;
        let mut opss = vec![];

        if let Some(ops) = SchönhageStrassenOps::first_init(len) {
            num_len = ops.N + 1;
            tmp_len = ops.sqr_tmp_len();

            let mut M = ops.M;
            opss.push(ops);

            while let Some(ops) = SchönhageStrassenOps::recursion_init(M) {
                tmp_len += ops.sqr_tmp_len();
                M = ops.M;
                opss.push(ops);
            }

            tmp_len += M << 1; // for karatsuba output
            tmp_len += KaratsubaEqualLength::tmp_len(M);
        } else {
            num_len = len + 1;
            tmp_len = len << 1; // for karatsuba output
            tmp_len += KaratsubaEqualLength::tmp_len(len);
        }

        let buff = vec![0; tmp_len + num_len];
        SchönhageStrassenSqr { num_len, buff, opss }
    }

    fn run(&mut self, x: &[u64]) {
        let a = self.buff.as_mut_ptr();
        let tmp = a.wrapping_add(self.num_len);

        // copy number to buff
        unsafe {
            ptr::copy_nonoverlapping(x.as_ptr(), a, x.len());
            set_to_zeros(a.wrapping_add(x.len()), self.num_len - x.len());

            self.exec(a, self.num_len - 1, tmp, 0);
        }
    }

    fn output(mut self) -> Vec<u64> {
        self.buff.truncate(self.num_len);
        self.buff
    }

    unsafe fn exec(&self, a: *mut u64, N: usize, tmp: *mut u64, depth: usize) {
        //! a must be less than or equal to $2^(64\*N)$
        let a_highest = a.wrapping_add(N);

        if *a_highest != 0 {
            // 2^(64*N)^2 ≡ 1
            *a_highest = 0;
            *a = 1;
            return;
        }

        match self.opss.get(depth) {
            None => {
                let c_len = N << 1;
                let c = tmp;
                let next_tmp = c.wrapping_add(c_len);

                // c = a * b
                KaratsubaEqualLength::ptr_mul_eqlen(a, a, c, N, next_tmp);

                // a = c % (2^(64*N) + 1)
                RingOps { N }.combine_shift_tmp(c, a, false);
            },
            Some(ops) => {
                let A = tmp;
                let ops_tmp = A.wrapping_add(ops.arr_len());
                let next_tmp = ops_tmp.wrapping_add(ops.shift_buff_len());
                let C = A;
                let c = a;

                ops.divide_num_to_arr(a, A);

                ops.for_each_eles(A, |A_k, k| ops.shift_in(A_k, k, ops_tmp));
                ops.fft(A, ops_tmp);

                // recursion mul per elements
                ops.for_each_eles(A, |A_k, _|
                    self.exec(A_k, ops.M, next_tmp, depth + 1)
                );

                ops.ifft(C, ops_tmp);
                ops.for_each_eles(C, |C_k, k| {
                    ops.div_by_arr_len(C_k, ops_tmp);
                    ops.shift_out(C_k, k, ops_tmp);
                });

                ops.combine_arr_to_num(c, C);
            },
        }
    }
}


/// operations in ring $ℤ / (2^(64*N)+1) * ℤ$
#[allow(non_snake_case)]
struct RingOps {
    N: usize,
}
impl RingOps {
    unsafe fn neg_to(&self, mut x: *const u64, out: *mut u64) {
        //! $out ≡ -x (mod 2^(64\*N) + 1)$, and `input` is less than $2^(64\*N)$.
        let stop = out.wrapping_add(self.N);

        // note that (!x) + 1 = 2^(64*N) - x, so -x ≡ 2^(64\*N) + 1 - x = (!x) + 2
        let mut carry = addcarry_u64(Carry::one(), !*x, 1, out);
        *stop = 0;
        if carry.has() {
            x = x.wrapping_add(1);
            let mut iter = out.wrapping_add(1);
            while x < stop {
                carry = addcarry_u64(carry, !*x, 0, out);
                x = x.wrapping_add(1);
                iter = iter.wrapping_add(1);
            }

            if carry.has() { // x < 2
                if *out == 0 { // x = 1
                    *stop = 1;
                } else {       // x = 0
                    *out = 0;
                }
            }
        }
    }

    unsafe fn make_shift_tmp(&self, input: *const u64, r: usize, tmp: *mut u64) {
        //! $tmp = input << (64*r)$
        //!
        //! # Safety
        //!
        //! input and tmp cannot overlap.
        debug_assert!(r < self.N);

        ptr::copy_nonoverlapping(input, tmp.wrapping_add(r), self.N + 1);
        set_to_zeros(tmp, r);
        set_to_zeros(tmp.wrapping_add(self.N + 1 + r), (self.N << 1) - (self.N + 1 + r));
    }

    unsafe fn combine_shift_tmp(&self, tmp: *const u64, out: *mut u64, swap_sign: bool) {
        //! $out ≡ (-1)^swap_sign * (t0 - t1) (mod 2^(64*N) + 1), t0 + t1*2^(64*N) = tmp$
        if swap_sign {
            self.sub_without_highest(tmp.wrapping_add(self.N), tmp, out);
        } else {
            self.sub_without_highest(tmp, tmp.wrapping_add(self.N), out);
        }
    }

    unsafe fn shl_u64(&self, input: *const u64, n: usize, out: *mut u64, tmp: *mut u64) {
        //! $out ≡ input * 2^(64*n) (mod 2^(64*N) + 1)$
        //!
        //! # Safety
        //!
        //! input and tmp cannot overlap.
        let (d, r) = (n / self.N, n % self.N);
        self.make_shift_tmp(input, r, tmp);
        self.combine_shift_tmp(tmp, out, d & 1 != 0);
    }

    unsafe fn shl_bit(&self, input: *const u64, n: u64, out: *mut u64, tmp: *mut u64) {
        //! $out ≡ input * 2^n (mod 2^(64*N) + 1)$
        //!
        //! # Safety
        //!
        //! input and tmp cannot overlap.
        let (shift_u64s, shift_bits) = (n / u64::BITS as u64, n % u64::BITS as u64);
        let (shift_u64s, shift_bits) = (shift_u64s as usize, shift_bits as u32);

        // shift u64s
        let (d, r) = (shift_u64s / self.N, shift_u64s % self.N);
        self.make_shift_tmp(input, r, tmp);

        // shift bits
        let mut p = tmp.wrapping_add((self.N << 1) - 1);
        while p > tmp {
            let (prev, curr) = (*p.wrapping_sub(1), *p);
            *p = (curr << shift_bits) | (prev >> (u64::BITS - shift_bits));
            p = p.wrapping_sub(1);
        }
        *p <<= shift_bits;

        self.combine_shift_tmp(tmp, out, d & 1 != 0);
    }

    unsafe fn reduce(&self, x: *mut u64, borrows_at_highest: u64) {
        //! reduce number from range $[0, 2^(64\*(N+1)))$ to $[0, 2^(64\*N)+1)$,
        //! the `borrows` is at the highest byte in x, but it is negative.
        let highest = x.wrapping_add(self.N);
        let second = x.wrapping_add(1);

        if *highest > borrows_at_highest {

            let borrow = subborrow_u64(Borrow::zero(), *x, *highest - borrows_at_highest, x);
            *highest = 0;
            if borrow.has() {
                let borrow = sub_borrow_from_ubig(borrow, second, second, self.N - 1);

                if borrow.has() {
                    add_carry_to_ubig(Carry::one(), x, x, self.N + 1);
                }
            }
        } else if *highest < borrows_at_highest {

            let carry = addcarry_u64(Carry::zero(), *x, borrows_at_highest - *highest, x);
            *highest = 0;
            if carry.has() {
                add_carry_to_ubig(carry, second, second, self.N);
            }
        } else {
            *highest = 0;
        }
    }

    unsafe fn add(&self, lhs: *const u64, rhs: *const u64, out: *mut u64) {
        //! $out ≡ lhs + rhs (mod 2^(64\*N) + 1)$
        let carry = addcarry_ubig_equal_len(Carry::zero(), lhs, rhs, out, self.N + 1);
        debug_assert!(!carry.has());

        self.reduce(out, 0);
        debug_assert!(*out.wrapping_add(self.N) < 2);
    }

    unsafe fn sub(&self, lhs: *const u64, rhs: *const u64, out: *mut u64) {
        //! $out ≡ lhs - rhs (mod 2^(64\*N) + 1)$
        let lhs_highest = lhs.wrapping_add(self.N);
        let rhs_highest = rhs.wrapping_add(self.N);
        let out_highest = out.wrapping_add(self.N);
        debug_assert!(*lhs_highest < 2);
        debug_assert!(*rhs_highest < 2);

        let borrow = subborrow_ubig_equal_len(Carry::zero(), lhs, rhs, out, self.N);
        *out_highest = *lhs_highest;
        let borrows = *rhs_highest + borrow.as_u64();

        self.reduce(out, borrows);
        debug_assert!(*out_highest < 2);
    }

    unsafe fn sub_without_highest(&self, lhs: *const u64, rhs: *const u64, out: *mut u64) {
        //! $out ≡ lhs - rhs (mod 2^(64\*N) + 1)$,
        //! similar to `sub`, but the length of `lhs` and `rhs` is equal to `N` instead of `N+1`.
        let out_highest = out.wrapping_add(self.N);

        let borrow = subborrow_ubig_equal_len(Borrow::zero(), lhs, rhs, out, self.N);
        *out_highest = 0;

        if borrow.has() { // has borrow at 2^(64*N) means we need to subtract 2^(64*N) from the result.
            add_carry_to_ubig(Carry::one(), out, out, self.N + 1); // -2^(64*N) ≡ 1
        }
    }
}

#[allow(dead_code, non_snake_case)]
unsafe fn print_ubig(a: *const u64, N: usize) {
    let mut iter = a.wrapping_add(N);
    let mut index = 0;
    while iter >= a {
        if index % 8 == 0 {
            print!("\n    ");
        }
        print!("{:016X}_", *iter);
        index += 1;
        iter = iter.wrapping_sub(1);
    }
}
