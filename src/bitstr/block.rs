//! Defines the `Block` trait and implements if the for fundament unsigned
//! integer types as well as `__m128` and `__m256` data types for SSE and AVX
//! architectures respectively.
//!
//! Blocks are the fundamental building blocks of [`BitString`]s.
//!
//! [`BitString`]: ../struct.BitString/html

use std::convert::TryInto;
use std::fmt::Debug;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

/// The `Block` trait unifies all of the required operations needed for bit
/// string operations.
pub trait Block:
	Sized
	+ Clone
	+ Copy
	+ Debug
	+ Send
	+ PartialEq
	+ Eq
	+ Not<Output = Self>
	+ BitOr<Output = Self>
	+ BitAnd<Output = Self>
	+ BitXor<Output = Self>
	+ BitOrAssign
	+ BitAndAssign
	+ BitXorAssign
	+ 'static
{
	/// Size of this block in bits.
	const BLOCK_SIZE: usize = std::mem::size_of::<Self>() * 8;

	/// Zero value for this block (i.e., a value with all bits set to 0).
	fn zero() -> Self;

	/// Returns a new block with the bottom `n` bits set to 1 and all other bits
	/// set to 0.
	///
	/// # Panics
	///
	/// This function panics if `n` > `Self::BLOCK_SIZE`.
	///
	/// # Examples
	///
	/// For example, consider the `u8` block implementation:
	///
	/// ```
	/// # use bix::bitstr::block::Block;
	/// assert_eq!(0b00000000, u8::mask(0));
	/// assert_eq!(0b00000001, u8::mask(1));
	/// assert_eq!(0b00000011, u8::mask(2));
	/// // ...
	/// assert_eq!(0b01111111, u8::mask(7));
	/// assert_eq!(0b11111111, u8::mask(8));
	/// // u8::mask(9) -- panics
	/// ```
	#[inline]
	fn mask(n: usize) -> Self {
		if n > Self::BLOCK_SIZE {
			panic!("mask size must be <= the block size");
		}

		Self::zero().not().shr(Self::BLOCK_SIZE - n)
	}

	/// Addition with carry in/out.
	///
	/// Computes the following returning the result along with the carry out bit:
	///
	/// ```text
	/// self + rhs + (carry_in ? 1 : 0)
	/// ```
	///
	/// The carry out bit should be `true` if the unsigned addition overflowed
	/// and `false` otherwise.
	fn carried_add(self, rhs: Self, carry_in: bool) -> (Self, bool);

	/// Logical left shift with carry in/out.
	///
	/// Computes the following:
	///
	/// ```text
	/// let carry_out = self >> (Self::BLOCK_SIZE - shift);
	/// let result = (self << shift) | carry_in;
	/// (result, carry_out)
	/// ```
	///
	/// # Panics
	///
	/// This method panics if `shift` is > `Self::BLOCK_SIZE`.
	fn carried_shl(self, shift: usize, carry_in: Self) -> (Self, Self);

	/// Logical left shift.
	#[inline]
	fn shl(self, shift: usize) -> Self {
		let (result, _) = self.carried_shl(shift, Self::zero());
		result
	}

	/// Logical right shift with carry in/out.
	///
	/// Computes the following:
	///
	/// ```text
	/// let carry_out = self << (Self::BLOCK_SIZE - shift);
	/// let result = (self >> shift) | carry_in;
	/// (result, carry_out)
	/// ```
	///
	/// # Panics
	///
	/// This method panics if `shift` is > `Self::BLOCK_SIZE`.
	fn carried_shr(self, shift: usize, carry_in: Self) -> (Self, Self);

	/// Logical right shift.
	#[inline]
	fn shr(self, shift: usize) -> Self {
		let (result, _) = self.carried_shr(shift, Self::zero());
		result
	}

	/// Returns the value of the `i`th bit.
	///
	/// # Panics
	///
	/// This method should panic if `i` is >= to the block size of `Self`.
	fn get_bit(&self, i: usize) -> bool;

	/// Returns the number of ones in the binary representation of `self`.
	fn pop_count(&self) -> usize;
}

macro_rules! impl_block {
	( $( $t:ty ),* ) => {
		$(
			impl Block for $t {
				#[inline(always)]
				fn zero() -> Self {
					0
				}

				#[inline]
				fn carried_add(self, rhs: Self, carry_in: bool) -> (Self, bool) {
					let c = if carry_in { 1 } else { 0 };
					self.overflowing_add(rhs + c)
				}

				fn carried_shl(self, shift: usize, carry_in: Self) -> (Self, Self) {
					if shift > Self::BLOCK_SIZE {
						panic!("shifts larger than the block size are illegal");
					}

					if shift == 0 {
						return (self, 0x00)
					}

					if shift == Self::BLOCK_SIZE {
						return (carry_in, self)
					}

					let carry_out = self >> (Self::BLOCK_SIZE - shift);
					let result = (self << shift) | carry_in;
					return (result, carry_out);
				}

				fn carried_shr(self, shift: usize, carry_in: Self) -> (Self, Self) {
					if shift > Self::BLOCK_SIZE {
						panic!("shifts larger than the block size are illegal");
					}

					if shift == 0 {
						return (self, 0x00)
					}

					if shift == Self::BLOCK_SIZE {
						return (carry_in, self)
					}

					let carry_out = self << (Self::BLOCK_SIZE - shift);
					let result = (self >> shift) | carry_in;
					return (result, carry_out);
				}

				#[inline]
				fn get_bit(&self, i: usize) -> bool {
					if i >= Self::BLOCK_SIZE {
						panic!("index out of bounds")
					}

					((self >> i) & 1) != 0
				}

				#[inline(always)]
				fn pop_count(&self) -> usize {
					self.count_ones() as usize
				}
			}
		)*
	};
}

impl_block!(u8, u16, u32, u64);

/// Trait allowing the construction of a block from a slice of smaller blocks in
/// a little endian fashion.
pub trait FromSlice<T> {
	/// Copies the required number of blocks from the beginning of `slice` and
	/// combines them in a little endian fashion to create a new, larger block.
	///
	/// The exact number of required blocks is:
	///
	/// ```text
	/// Self::BLOCK_SIZE / T::BLOCK_SIZE
	/// ```
	///
	/// # Panics
	///
	/// This method should panic if there are not enough blocks in `slice` to
	/// construct a new block.
	fn from_slice(slice: &[T]) -> Self;
}

impl<B: Block> FromSlice<B> for B {
	fn from_slice(slice: &[B]) -> Self {
		slice[0]
	}
}

impl FromSlice<u8> for u16 {
	fn from_slice(slice: &[u8]) -> Self {
		u16::from_le_bytes((&slice[0..2]).try_into().expect("slice too small"))
	}
}

impl FromSlice<u8> for u32 {
	fn from_slice(slice: &[u8]) -> Self {
		u32::from_le_bytes((&slice[0..4]).try_into().expect("slice too small"))
	}
}

impl FromSlice<u16> for u32 {
	fn from_slice(slice: &[u16]) -> Self {
		let a = slice[0].to_le_bytes();
		let b = slice[1].to_le_bytes();
		let bytes = [a, b].concat();
		u32::from_le_bytes(bytes[..].try_into().unwrap())
	}
}

impl FromSlice<u8> for u64 {
	fn from_slice(slice: &[u8]) -> Self {
		u64::from_le_bytes((&slice[0..8]).try_into().expect("slice too small"))
	}
}

impl FromSlice<u16> for u64 {
	fn from_slice(slice: &[u16]) -> Self {
		let a = slice[0].to_le_bytes();
		let b = slice[1].to_le_bytes();
		let c = slice[2].to_le_bytes();
		let d = slice[3].to_le_bytes();
		let bytes = [a, b, c, d].concat();
		u64::from_le_bytes(bytes[..].try_into().unwrap())
	}
}

impl FromSlice<u32> for u64 {
	fn from_slice(slice: &[u32]) -> Self {
		let a = slice[0].to_le_bytes();
		let b = slice[1].to_le_bytes();
		let bytes = [a, b].concat();
		u64::from_le_bytes(bytes[..].try_into().unwrap())
	}
}

#[cfg(test)]
mod test {
	use super::*;

	mod u8 {
		use super::*;

		#[test]
		fn carried_add() {
			assert_eq!(255u8.carried_add(0, true), (0, true));
			assert_eq!(254u8.carried_add(1, true), (0, true));
			assert_eq!(253u8.carried_add(1, true), (255u8, false));
			assert_eq!(0u8.carried_add(0, false), (0u8, false));
		}

		#[test]
		fn carried_shl_with_no_carry() {
			assert_eq!(0xffu8.carried_shl(4, 0x00), (0xf0, 0x0f));
		}

		#[test]
		fn carried_shl_with_carry() {
			assert_eq!(0xffu8.carried_shl(4, 0x0f), (0xff, 0x0f));
		}

		#[test]
		fn carried_shl_null_shift() {
			assert_eq!(0x12u8.carried_shl(0, 0xff), (0x12, 0x00));
		}

		#[test]
		fn carried_shl_full_block_shift() {
			assert_eq!(0x12u8.carried_shl(8, 0xff), (0xff, 0x12));
		}

		#[test]
		fn carried_shr_with_no_carry() {
			assert_eq!(0xffu8.carried_shr(4, 0x00), (0x0f, 0xf0));
		}

		#[test]
		fn carried_shr_with_carry() {
			assert_eq!(0xffu8.carried_shr(4, 0xf0), (0xff, 0xf0));
		}

		#[test]
		fn carried_shr_null_shift() {
			assert_eq!(0x12u8.carried_shr(0, 0xff), (0x12, 0x00));
		}

		#[test]
		fn carried_shr_full_block_shift() {
			assert_eq!(0x12u8.carried_shr(8, 0xff), (0xff, 0x12));
		}
	}

	#[test]
	fn u16_from_u8_slice() {
		assert_eq!(u16::from_slice(&[0x34u8, 0x12, 0x00]), 0x1234);
	}

	#[test]
	#[should_panic]
	fn u16_from_u8_slice_not_enough_data() {
		let _ = u16::from_slice(&[1u8]);
	}

	#[test]
	fn u32_from_u8_slice() {
		assert_eq!(
			u32::from_slice(&[0x78u8, 0x56, 0x34, 0x12, 0xff]),
			0x12345678
		);
	}

	#[test]
	#[should_panic]
	fn u32_from_u8_slice_not_enough_data() {
		let _ = u32::from_slice(&[1u8, 2, 3]);
	}

	#[test]
	fn u32_from_u16_slice() {
		assert_eq!(u32::from_slice(&[0x5678u16, 0x1234, 1]), 0x12345678);
	}

	#[test]
	#[should_panic]
	fn u32_from_u16_slice_not_enough_data() {
		let _ = u32::from_slice(&[1u16]);
	}

	#[test]
	fn u64_from_u8_slice() {
		assert_eq!(
			u64::from_slice(&[0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]),
			0x0123456789abcdef
		);
	}

	#[test]
	#[should_panic]
	fn u64_from_u8_slice_not_enough_data() {
		let _ = u64::from_slice(&[1u8, 2, 3, 4, 5, 6, 7]);
	}

	#[test]
	fn u64_from_u16_slice() {
		assert_eq!(
			u64::from_slice(&[0xcdefu16, 0x89ab, 0x4567, 0x0123]),
			0x0123456789abcdef
		);
	}

	#[test]
	#[should_panic]
	fn u64_from_u16_slice_not_enough_data() {
		let _ = u64::from_slice(&[1u16, 2, 3]);
	}

	#[test]
	fn u64_from_u32_slice() {
		assert_eq!(
			u64::from_slice(&[0x89abcdefu32, 0x01234567]),
			0x0123456789abcdef
		);
	}

	#[test]
	#[should_panic]
	fn u64_from_u32_slice_not_enough_data() {
		let _ = u64::from_slice(&[1u32]);
	}
}
