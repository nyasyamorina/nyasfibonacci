use crate::UBig;

pub fn fibonacci(n: u64) -> UBig {
    if n == 0 {
        UBig::zero()
    } else if n == 1 {
        UBig::one()
    } else {
        let mut prev = fibonacci(n - 1);
        prev += &fibonacci(n - 2);
        prev
    }
}