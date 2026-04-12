mod generic;
use generic::{partial_reduce, reduce};

mod stack;
pub use stack::CryptoBigintStackElement;

mod heap;
pub use heap::CryptoBigintHeapElement;
