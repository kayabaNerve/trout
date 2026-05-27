mod c;
use c::c;

mod reduction;
pub(super) use reduction::{partial_reduce, reduce};

mod composition;
pub(super) use composition::{add, double};

mod uint;
mod boxed_uint;
