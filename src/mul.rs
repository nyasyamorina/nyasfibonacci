use crate::UBig;

pub trait UBigMul {
    /// lhs * rhs
    fn mul(lhs: &UBig, rhs: &UBig) -> UBig;
    /// x^2
    fn sqr(x: &UBig) -> UBig;
}


mod elementary_school;
pub use elementary_school::ElementarySchool;

mod karatsuba;
pub use karatsuba::{Karatsuba, KaratsubaAnyLength};
