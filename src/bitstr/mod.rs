//! Defines the generic `BitString` type.

pub mod block;
pub mod iter;

use block::Block;
use iter::{IntoIter, Iter};
use std::iter::FromIterator;
use std::ops::{Add, BitAnd, BitOr, BitXor, Not, Shl};

pub use iter::PartialBlock;
use block::FromSlice;

#[derive(Clone, Debug)]
pub struct BitString<B: Block> {
	vec: Vec<B>,
	bit_len: usize,
}

impl<B: Block> BitString<B> {
	/// Constructs a new, empty `BitString`.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::BitString;
	/// let mut b: BitString<u64> = BitString::new();
	/// ```
	pub fn new() -> Self {
		BitString {
			vec: Vec::new(),
			bit_len: 0,
		}
	}

	/// Constructs a new, empty `BitString` with enough space to store `n` bits
	/// without having to reallocate.
	///
	/// If `n` is 0, nothing will be allocated.
	pub fn with_capacity(n: usize) -> Self {
		let cap = required_blocks::<B>(n);
		BitString {
			vec: Vec::with_capacity(cap),
			bit_len: 0,
		}
	}

	/// Constructs a `BitString` from a slice of blocks.
	/// 
	/// Blocks in a bit string are arranged in a little endian fashion.
	///
	/// The length of the resultant string is equivalent to the length of the
	/// block slice multiplied by the number of bits in a block.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::BitString;
	/// let b: BitString<u64> = BitString::from_blocks(&[1, 2, 3, 4]);
	/// assert_eq!(b.len(), 256);
	/// ```
	pub fn from_blocks(blocks: &[B]) -> Self {
		let len = blocks.len() * B::BLOCK_SIZE;
		BitString {
			vec: Vec::from(blocks),
			bit_len: len,
		}
	}

	/// Constructs a `BitString` from a slice of blocks truncating the length to
	/// `n` bits.
	///
	/// # Panics
	///
	/// Panics if `n` is larger than the number of bits contained in `blocks`.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::BitString;
	/// let b: BitString<u64> = BitString::from_blocks_truncated(&[1, 2, 3, 4], 240);
	/// assert_eq!(b.len(), 240);
	/// ```
	pub fn from_blocks_truncated(blocks: &[B], n: usize) -> Self {
		let available_len = blocks.len() * B::BLOCK_SIZE;
		if n > available_len {
			panic!("not enough bits");
		}

		// Copy the smallest possible sub-slice in order to not waste memory.
		let block_count = required_blocks::<B>(n);
		BitString {
			vec: Vec::from(&blocks[0..block_count]),
			bit_len: n,
		}
	}

	/// Takes the contents of `other` and converts them into a new bit string with
	/// a different block type. The observable state of the object will not have
	/// changed. That is, the length of the bit string along with the positions of
	/// each bits will be the same as they were before the block conversion.
	/// 
	/// Note that currently only conversions to larger block sizes are supported.
	/// For example, converting `BitString<u8>` into `BitString<u64>` but not the
	/// other way around. Support for such an operation may be added at a later
	/// date.
	/// 
	/// See also the counterpart method [`cast`].
	/// 
	/// [`cast`]: ./struct.BitString.html#method.cast
	/// 
	/// # Examples
	/// 
	/// ```
	/// # use bix::bitstr::BitString;
	/// let a = BitString::<u8>::from_blocks(&[0x21, 0x43]);
	/// assert_eq!(
	/// 	BitString::from_blocks(&[0x4321u16]),
	/// 	BitString::<u16>::from(a)
	/// );
	/// ```
	/// 
	/// Note that blocks in a bit string are arranged in a little endian fashion
	/// meaning that the larger block, in the case of this example a u16, is
	/// 0x4321 instead of 0x2143.
	pub fn from<A: Block>(other: BitString<A>) -> Self
	where
		B: FromSlice<A>,
	{
		if other.is_empty() {
			return Self::new();
		}

		let n = required_slice_len::<A, B>();
		let len = other.len();
		let mut vec = other.vec;

		// Pad vec with zero elements to ensure that we can construct full blocks.
		for _ in 0..(n - (vec.len() % n)) {
			vec.push(A::zero());
		}

		let mut new_vec = Vec::<B>::new();
		for i in (0..vec.len()).step_by(n) {
			new_vec.push(B::from_slice(&vec[i..(i + n)]));
		}

		BitString {
			vec: new_vec,
			bit_len: len,
		}
	}

	/// The length of the bit string (i.e., the number of bits it contains).
	#[inline]
	pub fn len(&self) -> usize {
		self.bit_len
	}

	/// Returns `true` if the bit string is empty.
	#[inline]
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Returns an immutable iterator over the blocks in the string.
	///
	/// Note that depending on the length of the bitstring, not all bits in the
	/// last block may contain valid data.
	///
	/// # Example
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let b: BitString<u64> = BitString::from_blocks(&[1, 2]);
	/// let mut iter = b.blocks();
	///
	/// assert_eq!(iter.next(), Some(PartialBlock { value: 1, len: 64 }));
	/// assert_eq!(iter.next(), Some(PartialBlock { value: 2, len: 64 }));
	/// assert_eq!(iter.next(), None);
	/// ```
	#[inline]
	pub fn blocks(&self) -> Iter<'_, B> {
		Iter::new(&self)
	}

	/// Returns an iterator over the blocks in the string.
	///
	/// Note that depending on the length of the bitstring, not all bits in the
	/// last block may contain valid data.
	///
	/// # Example
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let b: BitString<u64> = BitString::from_blocks(&[1, 2]);
	/// let mut iter = b.into_blocks();
	///
	/// assert_eq!(iter.next(), Some(PartialBlock { value: 1, len: 64 }));
	/// assert_eq!(iter.next(), Some(PartialBlock { value: 2, len: 64 }));
	/// assert_eq!(iter.next(), None);
	#[inline]
	pub fn into_blocks(self) -> IntoIter<B> {
		IntoIter::new(self)
	}

	/// Casts the bit string into a new bit string with a different block type.
	/// 
	/// Currently, only casts to larger block types (e.g., u8 -> u16) are 
	/// supported.
	/// 
	/// See the corresponding [`from`] method for a bit more information.
	/// 
	/// [`from`]: ./struct.BitString.html#method.from
	#[inline]
	pub fn cast<A: Block>(self) -> BitString<A> 
		where A: FromSlice<B>
	{
		BitString::<A>::from(self)
	}
}

impl<B: Block> FromIterator<PartialBlock<B>> for BitString<B> {
	/// Constructs a `BitString` from an iterator over partial blocks.
	fn from_iter<T: IntoIterator<Item = PartialBlock<B>>>(iter: T) -> Self {
		let mut vec = Vec::new();
		let mut bit_len = 0;
		for x in iter {
			vec.push(x.value);
			bit_len += x.len;
		}
		BitString { vec, bit_len }
	}
}

impl<B: Block> Not for BitString<B> {
	type Output = BitString<B>;

	/// Performs a bitwise not on the bitstring flipping all of its bits.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let a = BitString::<u8>::from_blocks_truncated(&[0x01, 0x02], 10);
	/// assert_eq!(10, a.len());
	///
	/// let b = !a;
	/// assert_eq!(10, b.len());
	///
	/// let mut iter = b.blocks();
	/// assert_eq!(Some(PartialBlock { value: 0xfe, len: 8 }), iter.next());
	/// assert_eq!(Some(PartialBlock { value: 0xfd, len: 2 }), iter.next());
	/// assert_eq!(None, iter.next());
	/// ```
	fn not(self) -> Self::Output {
		self.into_blocks()
			.map(|p| p.map(|v| B::from(v.not())))
			.collect()
	}
}

macro_rules! impl_binary_op {
	($trait_name:ident, $fn_name:tt) => {
		impl<B: Block> $trait_name for BitString<B> {
			type Output = BitString<B>;

			fn $fn_name(self, rhs: Self) -> Self::Output {
				let len: usize = self.len();
				if len != rhs.len() {
					panic!("bitstring length mismatch");
				}
				if len == 0 {
					return self;
				}

				let left_iter = self.into_blocks();
				let mut right_iter = rhs.into_blocks();
				let mut new_blocks = Vec::new();
				for partial_left_block in left_iter {
					let left_block = partial_left_block.value;
					let right_block = right_iter.next().unwrap().value;
					let new_block = B::from(left_block.$fn_name(right_block));
					new_blocks.push(new_block);
				}

				Self::from_blocks_truncated(&new_blocks, len)
			}
		}
	};
}

impl_binary_op!(BitOr, bitor);
impl_binary_op!(BitAnd, bitand);
impl_binary_op!(BitXor, bitxor);

impl<B: Block> Shl<usize> for BitString<B> {
	type Output = BitString<B>;

	/// Performs a bitwise left shift on the bitstring, shifting all bits left
	/// (forward) by a fixed amount.
	///
	/// Currently only shifts <= the block size are supported.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let a = BitString::<u8>::from_blocks(&[0xaf, 0x08]);
	/// assert_eq!(16, a.len());
	///
	/// let b = a << 1;
	/// assert_eq!(16, b.len());
	///
	/// let mut iter = b.blocks();
	/// assert_eq!(Some(PartialBlock { value: 0x5e, len: 8 }), iter.next());
	/// assert_eq!(Some(PartialBlock { value: 0x11, len: 8 }), iter.next());
	/// assert_eq!(None, iter.next());
	/// ```
	fn shl(self, rhs: usize) -> Self::Output {
		// TODO: Add support shifts greater than the block size.
		let len = self.len();
		if len == 0 {
			return self;
		}

		let mut new_blocks = Vec::new();
		let mut carry_in = B::zero();
		for partial_block in self.into_blocks() {
			let block = partial_block.value;
			let (new_block, carry_out) = block.carried_shl(rhs, carry_in);
			carry_in = carry_out;
			new_blocks.push(new_block);
		}

		Self::from_blocks_truncated(&new_blocks, len)
	}
}

impl<B: Block> Add for BitString<B> {
	type Output = BitString<B>;

	/// Adds two bit strings together.
	fn add(self, rhs: BitString<B>) -> Self::Output {
		let len = self.len();
		if len == 0 {
			return self;
		}

		if len != rhs.len() {
			panic!("bitstring length mismatch")
		}

		let mut new_blocks = Vec::new();
		let mut carry_in = false;
		let mut rhs_iter = rhs.into_blocks();
		for partial_block in self.into_blocks() {
			let left_block = partial_block.value;
			let right_block = rhs_iter.next().unwrap().value;
			let (new_block, carry_out) = left_block.carried_add(right_block, carry_in);
			carry_in = carry_out;
			new_blocks.push(new_block);
		}

		Self::from_blocks_truncated(&new_blocks, len)
	}
}

impl<B: Block> PartialEq for BitString<B> {
	fn eq(&self, other: &Self) -> bool {
		if self.len() != other.len() {
			return false;
		}

		let mut other_iter = other.blocks();
		for PartialBlock {
			value: l_block,
			len: block_len,
		} in self.blocks()
		{
			let r_block = other_iter.next().unwrap().value;

			// Mask off bits which don't contain valid data.
			let mask = B::mask(block_len);
			let l_block = l_block.bitand(mask);
			let r_block = r_block.bitand(mask);
			if l_block != r_block {
				return false;
			}
		}

		return true;
	}
}

impl<B: Block> Eq for BitString<B> {}

/// Returns the required number of blocks needed to store `n` bits.
#[inline]
fn required_blocks<B: Block>(n: usize) -> usize {
	if n % B::BLOCK_SIZE == 0 {
		n / B::BLOCK_SIZE
	} else {
		(n / B::BLOCK_SIZE) + 1
	}
}

/// Returns the required number of blocks of type `A` needed to construct a
/// block of type `B`. If `B` is a smaller type than `A`, then this function
/// will panic.
#[inline]
fn required_slice_len<A: Block, B: Block>() -> usize {
	if B::BLOCK_SIZE < A::BLOCK_SIZE {
		panic!("cannot construct a smaller block from larger ones")
	}
	B::BLOCK_SIZE / A::BLOCK_SIZE
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn equal() {
		let a = BitString::<u64>::from_blocks_truncated(&[1, 2, 3, 4], 201);
		let b = BitString::from_blocks_truncated(&[1, 2, 3, 4], 201);
		assert_eq!(a, b);
	}

	#[test]
	fn equal_up_to_len() {
		let a = BitString::<u8>::from_blocks_truncated(&[0xff, 0xff], 12);
		let b = BitString::from_blocks_truncated(&[0xff, 0x0f], 12);
		assert_eq!(a, b);
	}

	#[test]
	fn not_equal() {
		let a = BitString::<u64>::from_blocks_truncated(&[1, 2, 3, 400], 201);
		let b = BitString::from_blocks_truncated(&[1, 2, 3, 4], 201);
		assert_ne!(a, b);
	}

	#[test]
	fn mismatch_len_not_equal() {
		let a = BitString::<u64>::from_blocks_truncated(&[1, 2, 3, 4], 201);
		let b = BitString::from_blocks_truncated(&[1, 2, 3, 4], 200);
		assert_ne!(a, b);
	}

	#[test]
	fn not_empty() {
		let a = BitString::<u32>::new();
		assert!(a.is_empty());
		let b = !a;
		assert!(b.is_empty());
	}

	#[test]
	fn not_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0x01, 0xf2]);
		assert_eq!(BitString::from_blocks(&[0xfe, 0x0d]), !a);
	}

	#[test]
	fn not_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0x01, 0x02], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0xfe, 0x01], 10), !a);
	}

	#[test]
	fn or_empty() {
		let a = BitString::<u16>::new();
		let b = BitString::new();
		let c = a | b;
		assert!(c.is_empty());
	}

	#[test]
	#[should_panic(expected = "length mismatch")]
	fn or_mismatch_len() {
		let a = BitString::<u16>::from_blocks(&[0]);
		let b = BitString::new();
		let _ = a | b;
	}

	#[test]
	fn or_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0xa0, 0xf2]);
		let b = BitString::from_blocks(&[0x17, 0x70]);
		assert_eq!(BitString::from_blocks(&[0xb7, 0xf2]), a | b);
	}

	#[test]
	fn or_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0xa0, 0xf2], 10);
		let b = BitString::from_blocks_truncated(&[0x17, 0x70], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0xb7, 0x02], 10), a | b);
	}

	#[test]
	fn and_empty() {
		let a = BitString::<u16>::new();
		let b = BitString::new();
		let c = a & b;
		assert!(c.is_empty());
	}

	#[test]
	#[should_panic(expected = "length mismatch")]
	fn and_mismatch_len() {
		let a = BitString::<u16>::from_blocks(&[0]);
		let b = BitString::new();
		let _ = a & b;
	}

	#[test]
	fn and_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0xa0, 0xf2]);
		let b = BitString::from_blocks(&[0x17, 0x70]);
		assert_eq!(BitString::from_blocks(&[0x00, 0x70]), a & b);
	}

	#[test]
	fn and_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0xa0, 0x02], 10);
		let b = BitString::from_blocks_truncated(&[0x17, 0x03], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0x00, 0x02], 10), a & b);
	}

	#[test]
	fn xor_empty() {
		let a = BitString::<u16>::new();
		let b = BitString::new();
		let c = a ^ b;
		assert!(c.is_empty());
	}

	#[test]
	#[should_panic(expected = "length mismatch")]
	fn xor_mismatch_len() {
		let a = BitString::<u16>::from_blocks(&[0]);
		let b = BitString::new();
		let _ = a ^ b;
	}

	#[test]
	fn xor_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0xa0, 0xf2]);
		let b = BitString::from_blocks(&[0x17, 0x70]);
		assert_eq!(BitString::from_blocks(&[0xb7, 0x82]), a ^ b);
	}

	#[test]
	fn xor_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0xa0, 0xf2], 10);
		let b = BitString::from_blocks_truncated(&[0x17, 0x70], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0xb7, 0x02], 10), a ^ b);
	}

	#[test]
	fn shl_empty() {
		let a = BitString::<u32>::new();
		let b = a << 16;
		assert!(b.is_empty());
	}

	#[test]
	fn shl_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0x81, 0xc0]);
		assert_eq!(BitString::from_blocks(&[0x04, 0x02]), a << 2);
	}

	#[test]
	fn shl_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0x81, 0xc0], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0x04, 0x02], 10), a << 2);
	}

	#[test]
	fn add_empty() {
		let a = BitString::<u16>::new();
		let b = BitString::new();
		let c = a + b;
		assert!(c.is_empty());
	}

	#[test]
	#[should_panic]
	fn add_mismatch_len() {
		let a = BitString::<u64>::from_blocks(&[1]);
		let b = BitString::<u64>::from_blocks_truncated(&[2], 62);
		let _ = a + b;
	}

	#[test]
	fn add_whole_blocks() {
		let a = BitString::<u8>::from_blocks(&[0xf8, 0x07]);
		let b = BitString::from_blocks(&[0x08, 0x00]);
		assert_eq!(BitString::from_blocks(&[0x00, 0x08]), a + b);
	}

	#[test]
	fn add_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0xf8, 0x07], 12);
		let b = BitString::from_blocks_truncated(&[0x08, 0x00], 12);
		assert_eq!(BitString::from_blocks_truncated(&[0x00, 0x08], 12), a + b);
	}

	#[test]
	fn block_conversion_u8_to_u64() {
		let a = BitString::<u8>::from_blocks_truncated(&[0x21, 0x43, 0x65], 20);
		assert_eq!(
			BitString::from_blocks_truncated(&[0x654321], 20),
			BitString::<u64>::from(a)
		);
	}
}
