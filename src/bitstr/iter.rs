//! Iterator types for `BitString`.

use super::block::Block;
use super::BitString;

/// A block which may only be partially filled with valid data.
///
/// # Fields
///
/// * `value` holds the block of data which may only be partially filled
///
/// * `len` describes the number of bits in `value` which hold valid data. Only
/// the bottom `len` bits hold actual data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialBlock<B: Block> {
	/// The block value.
	///
	/// Only `len` bits in this value hold valid data.
	pub value: B,

	/// The number of bits in `value` which hold valid data.
	pub len: usize,
}

impl<B: Block> PartialBlock<B> {
	/// Transforms the partial block by applying a function to the `value` field.
	pub fn map<F: Fn(B) -> B>(self, f: F) -> Self {
		let len = self.len;
		let value = f(self.value);
		PartialBlock { value, len }
	}
}

/// Iterator over the blocks in a `BitString`.
pub struct Iter<'a, B: Block> {
	b: &'a BitString<B>,
	index: usize,
}

impl<'a, B: Block> Iter<'a, B> {
	/// Constructs a new `Iter` over `b`.
	pub fn new(b: &'a BitString<B>) -> Self {
		Iter { b, index: 0 }
	}
}

/// Returns the partial block at `index` in `b`.
fn partial_block<B: Block>(b: &BitString<B>, index: usize) -> Option<PartialBlock<B>> {
	let bit_len = b.len();
	let whole_block_count = bit_len / B::BLOCK_SIZE;
	let partial_offset = bit_len % B::BLOCK_SIZE;

	if index < whole_block_count {
		Some(PartialBlock{ value: b.vec[index], len: B::BLOCK_SIZE })
	} else if index == whole_block_count && partial_offset != 0 {
		Some(PartialBlock{ value: b.vec[index], len: partial_offset })
	} else {
		None
	}
}

impl<'a, B: Block> Iterator for Iter<'a, B> {
	type Item = PartialBlock<B>;

	/// The next block in the iteration.
	fn next(&mut self) -> Option<Self::Item> {
		let index = self.index;
		self.index += 1;
		partial_block(self.b, index)
	}
}

/// Iterator over the blocks in a `BitString`
pub struct IntoIter<B: Block> {
	b: BitString<B>,
	index: usize,
}

impl<B: Block> IntoIter<B> {
	/// Constructs a new `IntoIter` over `b`.
	pub fn new(b: BitString<B>) -> Self {
		IntoIter { b, index: 0 }
	}
}

impl<B: Block> Iterator for IntoIter<B> {
	type Item = PartialBlock<B>;

	fn next(&mut self) -> Option<Self::Item> {
		let index = self.index;
		self.index += 1;
		partial_block(&self.b, index)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn block_iter_over_empty_bitstring() {
		let b = BitString::<u64>::new();
		let mut iter = b.blocks();
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn block_iter_with_only_partial_block() {
		let b = BitString::<u16>::from_blocks_truncated(&[12], 7);
		let mut iter = b.blocks();
		assert_eq!(iter.next(), Some(PartialBlock { value: 12, len: 7 }));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn block_iter_with_partial_block() {
		let b = BitString::<u8>::from_blocks_truncated(&[1, 2, 3, 4], 30);
		let mut iter = b.blocks();
		assert_eq!(iter.next(), Some(PartialBlock { value: 1, len: 8 }));
		assert_eq!(iter.next(), Some(PartialBlock { value: 2, len: 8 }));
		assert_eq!(iter.next(), Some(PartialBlock { value: 3, len: 8 }));
		assert_eq!(iter.next(), Some(PartialBlock { value: 4, len: 6 }));
		assert_eq!(iter.next(), None);
	}
}
