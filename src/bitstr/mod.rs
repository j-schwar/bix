//! Defines the generic `BitString` type.

pub mod block;

use block::Block;
use std::fmt::{Display, Formatter};
use std::iter::FromIterator;
use std::ops::{
	Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl,
	ShlAssign, Shr, ShrAssign,
};

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

	/// Constructs a `BitString` of length `n` with all bits set to zero.
	pub fn zero(n: usize) -> Self {
		let cap = required_blocks::<B>(n);
		BitString {
			vec: std::iter::repeat(B::zero()).take(cap).collect(),
			bit_len: n,
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

	/// Returns an iterator over the blocks in `self`.
	///
	/// Since the number of bits in the bit string may not be a perfect multiple
	/// of the block size the last block in the bit string may only partially
	/// contain valid data. As such, the iterator returns the number of valid bits
	/// in the block along with the actual block itself.
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let b = BitString::<u64>::from_blocks_truncated(&[1, 2, 3], 130);
	/// let mut iter = b.blocks();
	/// assert_eq!(Some((1, 64)), iter.next());
	/// assert_eq!(Some((2, 64)), iter.next());
	///
	/// // Only the bottom two bits of this block contain valid data, the rest is
	/// // garbage.
	/// assert_eq!(Some((3, 2)), iter.next());
	///
	/// assert_eq!(None, iter.next());
	/// ```
	#[inline]
	pub fn blocks(&self) -> Blocks<'_, B> {
		Blocks::new(&self)
	}

	/// Returns an owning iterator over the blocks in `self`.
	///
	/// Like with [`blocks`], the number of valid bits are also returned along
	/// with each block when iterating.
	///
	/// [`blocks`]: ./struct.BitString.html#method.blocks
	///
	/// # Examples
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let b = BitString::<u64>::from_blocks_truncated(&[1, 2, 3], 130);
	/// let mut iter = b.into_blocks();
	/// assert_eq!(Some((1, 64)), iter.next());
	/// assert_eq!(Some((2, 64)), iter.next());
	///
	/// // Only the bottom two bits of this block contain valid data, the rest is
	/// // garbage.
	/// assert_eq!(Some((3, 2)), iter.next());
	///
	/// assert_eq!(None, iter.next());
	#[inline]
	pub fn into_blocks(self) -> IntoBlocks<B> {
		IntoBlocks::new(self)
	}

	/// Returns an iterator over the bits in the string.
	///
	/// # Example
	///
	/// ```
	/// # use bix::bitstr::*;
	/// let b = BitString::<u8>::from_blocks_truncated(&[0x06], 3);
	/// let mut iter = b.bits();
	/// assert_eq!(Some(false), iter.next());
	/// assert_eq!(Some(true), iter.next());
	/// assert_eq!(Some(true), iter.next());
	/// assert_eq!(None, iter.next());
	/// ```
	#[inline]
	pub fn bits(&self) -> Bits<'_, B> {
		Bits::new(self)
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
	where
		A: FromSlice<B>,
	{
		BitString::<A>::from(self)
	}

	/// Returns the number of one bits in `self`.
	pub fn pop_count(&self) -> usize {
		self.blocks().fold(0, |acc, (block, len)| {
			let masked = block & B::mask(len);
			acc + masked.pop_count()
		})
	}
}

impl<B: Block> FromIterator<(B, usize)> for BitString<B> {
	fn from_iter<T: IntoIterator<Item = (B, usize)>>(iter: T) -> Self {
		// TODO: Should assert that only the last block may be partial. That or
		// 	implement this in such a way that we can handle combining multiple
		//	partial blocks.
		let mut vec = Vec::new();
		let mut bit_len = 0;
		for x in iter {
			vec.push(x.0);
			bit_len += x.1;
		}
		BitString { vec, bit_len }
	}
}

impl<B: Block> Not for BitString<B> {
	type Output = BitString<B>;

	fn not(self) -> Self::Output {
		self.into_blocks().map(|(b, l)| (!b, l)).collect()
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
				for (left_block, _) in left_iter {
					let (right_block, _) = right_iter.next().unwrap();
					let new_block = B::from(left_block.$fn_name(right_block));
					new_blocks.push(new_block);
				}

				BitString {
					vec: new_blocks,
					bit_len: len,
				}
			}
		}
	};
}

impl_binary_op!(BitOr, bitor);
impl_binary_op!(BitAnd, bitand);
impl_binary_op!(BitXor, bitxor);

macro_rules! impl_binary_op_assign {
	($trait_name:ident, $fn_name:tt) => {
		impl<B: Block> $trait_name<BitString<B>> for BitString<B> {
			fn $fn_name(&mut self, rhs: BitString<B>) {
				if self.len() != rhs.len() {
					panic!("bitstring length mismatch");
				}

				for (i, (block, _)) in rhs.blocks().enumerate() {
					self.vec[i].$fn_name(block);
				}
			}
		}

		impl<'a, B: Block> $trait_name<&'a BitString<B>> for BitString<B> {
			fn $fn_name(&mut self, rhs: &'a BitString<B>) {
				if self.len() != rhs.len() {
					panic!("bitstring length mismatch");
				}

				for (i, (block, _)) in rhs.blocks().enumerate() {
					self.vec[i].$fn_name(block);
				}
			}
		}
	};
}

impl_binary_op_assign!(BitOrAssign, bitor_assign);
impl_binary_op_assign!(BitAndAssign, bitand_assign);
impl_binary_op_assign!(BitXorAssign, bitxor_assign);

impl<B: Block> Shl<usize> for BitString<B> {
	type Output = BitString<B>;

	fn shl(self, rhs: usize) -> Self::Output {
		// TODO: Add support for shifts greater than the block size.
		let len = self.len();
		if len == 0 {
			return self;
		}

		let mut new_blocks = Vec::new();
		let mut carry_in = B::zero();
		for (block, _) in self.into_blocks() {
			let (new_block, carry_out) = block.carried_shl(rhs, carry_in);
			carry_in = carry_out;
			new_blocks.push(new_block);
		}

		BitString {
			vec: new_blocks,
			bit_len: len,
		}
	}
}

impl<B: Block> ShlAssign<usize> for BitString<B> {
	fn shl_assign(&mut self, rhs: usize) {
		// TODO: Add support for shifts greater than the block size.
		let mut carry_in = B::zero();
		for i in 0..self.vec.len() {
			let block: B = self.vec[i];
			let (new_block, carry_out) = block.carried_shl(rhs, carry_in);
			carry_in = carry_out;
			self.vec[i] = new_block;
		}
	}
}

impl<B: Block> Shr<usize> for BitString<B> {
	type Output = BitString<B>;

	fn shr(self, rhs: usize) -> Self::Output {
		// TODO: Add support for shifts greater than the block size.
		let len = self.len();
		if len == 0 {
			return self;
		}

		let mut new_blocks = Vec::new();
		let mut iter = self.vec.iter().rev();
		let mut carry_in = B::zero();

		// Since the last block may only partially contain good data, in order to
		// ensure that garbage data does not get shifted into the range of good data
		// we must mask off part of the last block.
		if len % B::BLOCK_SIZE != 0 {
			let mask = B::mask(len % B::BLOCK_SIZE);
			// Bit string is not empty so there is at least one block.
			let last_block = *iter.next().unwrap() & mask;
			let (new_last_block, carry_out) = last_block.carried_shr(rhs, B::zero());
			carry_in = carry_out;
			new_blocks.push(new_last_block);
		}

		for block in iter {
			let (new_block, carry_out) = block.carried_shr(rhs, carry_in);
			carry_in = carry_out;
			new_blocks.push(new_block);
		}

		// Since we iterated in reverse, new_blocks is in reverse order.
		new_blocks.reverse();

		BitString {
			vec: new_blocks,
			bit_len: len,
		}
	}
}

impl<B: Block> ShrAssign<usize> for BitString<B> {
	fn shr_assign(&mut self, rhs: usize) {
		if self.is_empty() {
			return;
		}

		let mut iter = (0..self.vec.len()).rev();
		let mut carry_in = B::zero();

		// Mask off garbage data in the last block if necessary.
		let len = self.len();
		if len % B::BLOCK_SIZE != 0 {
			let mask = B::mask(len % B::BLOCK_SIZE);
			// Self is not empty so there must be at least one block.
			let index = iter.next().unwrap();
			let last_block = self.vec[index] & mask;
			let (new_last_block, carry_out) = last_block.carried_shr(rhs, carry_in);
			carry_in = carry_out;
			self.vec[index] = new_last_block;
		}

		for index in iter {
			let block = self.vec[index];
			let (new_block, carry_out) = block.carried_shr(rhs, carry_in);
			carry_in = carry_out;
			self.vec[index] = new_block;
		}
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
		for (left_block, _) in self.into_blocks() {
			let (right_block, _) = rhs_iter.next().unwrap();
			let (new_block, carry_out) = left_block.carried_add(right_block, carry_in);
			carry_in = carry_out;
			new_blocks.push(new_block);
		}

		BitString {
			vec: new_blocks,
			bit_len: len,
		}
	}
}

impl<B: Block> AddAssign for BitString<B> {
	fn add_assign(&mut self, rhs: BitString<B>) {
		if self.len() != rhs.len() {
			panic!("bitstring length mismatch");
		}

		let mut carry_in = false;
		for (i, (block, _)) in rhs.blocks().enumerate() {
			let (new_block, carry_out) = block.carried_add(self.vec[i], carry_in);
			carry_in = carry_out;
			self.vec[i] = new_block;
		}
	}
}

impl<B: Block> PartialEq for BitString<B> {
	fn eq(&self, other: &Self) -> bool {
		if self.len() != other.len() {
			return false;
		}

		let mut other_iter = other.blocks();
		for (l_block, block_len) in self.blocks() {
			let (r_block, _) = other_iter.next().unwrap();

			// TODO: We are assuming that both the left and right block have the same
			// 	number of valid bits, we should assert that this case is true either
			// 	here, or in our constructors (e.g., from_iter).

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

impl<B: Block> Display for BitString<B> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let width = if let Some(width) = f.width() {
			width
		} else {
			self.len()
		};

		let mut iter = self.bits();
		for _ in 0..width {
			if iter.next().unwrap() {
				write!(f, "1")?;
			} else {
				write!(f, ".")?;
			}
		}

		Ok(())
	}
}

/// Iterator over the bits in a `BitString`.
///
/// See the [`bits`] method for more information.
///
/// [`bits`]: ./struct.BitString.html#method.bits
pub struct Bits<'a, B: Block> {
	b: &'a BitString<B>,
	bit_index: usize,
}

impl<'a, B: Block> Bits<'a, B> {
	/// Constructs a new iterator over `b`.
	pub fn new(b: &'a BitString<B>) -> Self {
		Bits { b, bit_index: 0 }
	}
}

impl<'a, B: Block> Iterator for Bits<'a, B> {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		if self.bit_index >= self.b.len() {
			return None;
		}

		let block_index = self.bit_index / B::BLOCK_SIZE;
		let bit_offset = self.bit_index % B::BLOCK_SIZE;
		let result = self.b.vec[block_index].get_bit(bit_offset);
		self.bit_index += 1;

		Some(result)
	}
}

/// Returns the block at `index` in `b` along with the number of valid bits it
/// contains.
fn block_at<B: Block>(b: &BitString<B>, index: usize) -> Option<(B, usize)> {
	let bit_len = b.len();
	let whole_block_count = bit_len / B::BLOCK_SIZE;
	let partial_offset = bit_len % B::BLOCK_SIZE;

	if index < whole_block_count {
		Some((b.vec[index], B::BLOCK_SIZE))
	} else if index == whole_block_count && partial_offset != 0 {
		Some((b.vec[index], partial_offset))
	} else {
		None
	}
}

/// Iterator over the blocks in a [`BitString`].
///
/// See the [`blocks`] method for more information.
///
/// [`BitString`]: ./struct.BitString.html
/// [`blocks`]: ./struct.BitString.html#method.blocks
pub struct Blocks<'a, B: Block> {
	b: &'a BitString<B>,
	index: usize,
}

impl<'a, B: Block> Blocks<'a, B> {
	/// Constructs a new iterator over `b`.
	pub fn new(b: &'a BitString<B>) -> Self {
		Blocks { b, index: 0 }
	}
}

impl<'a, B: Block> Iterator for Blocks<'a, B> {
	type Item = (B, usize);

	fn next(&mut self) -> Option<Self::Item> {
		let index = self.index;
		self.index += 1;
		block_at(self.b, index)
	}
}

/// Owning iterator over the blocks in a [`BitString`].
///
/// See the [`into_blocks`] method for more information.
///
/// [`BitString`]: ./struct.BitString.html
/// [`into_blocks`]: ./struct.BitString.html#method.into_blocks
pub struct IntoBlocks<B: Block> {
	b: BitString<B>,
	index: usize,
}

impl<B: Block> IntoBlocks<B> {
	/// Constructs a new iterator over `b`.
	pub fn new(b: BitString<B>) -> Self {
		IntoBlocks { b, index: 0 }
	}
}

impl<B: Block> Iterator for IntoBlocks<B> {
	type Item = (B, usize);

	fn next(&mut self) -> Option<Self::Item> {
		let index = self.index;
		self.index += 1;
		block_at(&self.b, index)
	}
}

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
	fn not_u16_with_partial_block() {
		let a = BitString::<u16>::from_blocks_truncated(&[0x1804], 14);
		assert_eq!(BitString::from_blocks_truncated(&[0xe7fb], 14), !a.clone());
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
	fn shr_empty() {
		let a = BitString::<u32>::new();
		let b = a << 16;
		assert!(b.is_empty());
	}

	#[test]
	fn shr_whole_blocks() {
		// c281 >> 2 = 30A0
		let a = BitString::<u8>::from_blocks(&[0x81, 0xc2]);
		assert_eq!(BitString::from_blocks(&[0xa0, 0x30]), a >> 2);
	}

	#[test]
	fn shr_with_partial_block() {
		let a = BitString::<u8>::from_blocks_truncated(&[0x81, 0xfe], 10);
		assert_eq!(BitString::from_blocks_truncated(&[0xa0, 0x00], 10), a >> 2);
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

	#[test]
	fn small_bit_iterator() {
		let b = BitString::<u8>::from_blocks_truncated(&[0x06], 3);
		let mut iter = b.bits();
		assert_eq!(Some(false), iter.next());
		assert_eq!(Some(true), iter.next());
		assert_eq!(Some(true), iter.next());
		assert_eq!(None, iter.next());
	}

	#[test]
	fn pop_count() {
		let b = BitString::<u64>::from_blocks_truncated(&[0b11010011101, 0b10000001110111011], 70);
		assert_eq!(12, b.pop_count());
	}

	mod property {
		use super::*;
		use quickcheck::TestResult;
		use quickcheck_macros::quickcheck;

		fn not_length_equivalence<B: Block>(src: Vec<B>, len: usize) -> TestResult {
			if len > (src.len() * B::BLOCK_SIZE) {
				return TestResult::discard();
			}

			let b = BitString::<B>::from_blocks_truncated(&src[..], len);
			let expected = b.len();
			TestResult::from_bool((!b).len() == expected)
		}

		#[quickcheck]
		fn not_length_equivalence_u8(src: Vec<u8>, len: usize) -> TestResult {
			not_length_equivalence(src, len)
		}

		#[quickcheck]
		fn not_length_equivalence_u16(src: Vec<u16>, len: usize) -> TestResult {
			not_length_equivalence(src, len)
		}

		#[quickcheck]
		fn not_length_equivalence_u32(src: Vec<u32>, len: usize) -> TestResult {
			not_length_equivalence(src, len)
		}

		#[quickcheck]
		fn not_length_equivalence_u64(src: Vec<u64>, len: usize) -> TestResult {
			not_length_equivalence(src, len)
		}

		fn whole_block_cast_length_equivalence<Src, Dst>(src: Vec<Src>) -> bool
		where
			Src: Block,
			Dst: Block + FromSlice<Src>,
		{
			let a = BitString::from_blocks(&src[..]);
			let len = a.len();
			let b = a.cast::<Dst>();
			b.len() == len
		}

		#[quickcheck]
		fn whole_block_cast_length_equivalence_u8_u16(src: Vec<u8>) -> bool {
			whole_block_cast_length_equivalence::<u8, u16>(src)
		}

		#[quickcheck]
		fn whole_block_cast_length_equivalence_u8_u32(src: Vec<u8>) -> bool {
			whole_block_cast_length_equivalence::<u8, u32>(src)
		}

		#[quickcheck]
		fn whole_block_cast_length_equivalence_u8_u64(src: Vec<u8>) -> bool {
			whole_block_cast_length_equivalence::<u8, u64>(src)
		}
	}
}
