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

impl<'a, B: Block> Iterator for Iter<'a, B> {
	type Item = PartialBlock<B>;

	/// The next block in the iteration.
	fn next(&mut self) -> Option<Self::Item> {
		let block_count = self.b.vec.len();
		if self.index >= block_count {
			return None;
		}

		let value = self.b.vec[self.index];

		// Only the last block may be partial.
		let bit_len = self.b.len();
		let has_partial_block = (bit_len % B::BLOCK_SIZE) != 0;
		let len = if self.index == block_count - 1 && has_partial_block {
			bit_len % B::BLOCK_SIZE
		} else {
			B::BLOCK_SIZE
		};

		self.index += 1;

		Some(PartialBlock { value, len })
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
		let block_count = self.b.vec.len();
		if self.index >= block_count {
			return None;
		}

		let value = self.b.vec[self.index];

		// Only the last block may be partial.
		let bit_len = self.b.len();
		let has_partial_block = (bit_len % B::BLOCK_SIZE) != 0;
		let len = if self.index == block_count - 1 && has_partial_block {
			bit_len % B::BLOCK_SIZE
		} else {
			B::BLOCK_SIZE
		};

		self.index += 1;

		Some(PartialBlock { value, len })
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
