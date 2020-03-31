pub mod bitstr;
pub mod parse;

pub mod prelude {
	pub use crate::bitstr::block::Block;
	pub use crate::bitstr::BitString;
	pub use crate::parse;
}
