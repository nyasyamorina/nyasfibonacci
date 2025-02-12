use crate::UBig;

pub fn fibonacci(mut n: u64) -> UBig {
    if n == 0 {
        return UBig::zero();
    }
    n -= 1;
    let (mut a, mut b) = (UBig::zero(), UBig::one());
    while n > 0 {
        a += &b;
        (a, b) = (b, a); // `std::swap` in C/C++
        n -= 1;
    }
    b
}