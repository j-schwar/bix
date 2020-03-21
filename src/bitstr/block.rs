//! Defines the `Block` trait and implements if the for fundament unsigned
//! integer types as well as `__m128` and `__m256` data types for SSE and AVX
//! architectures respectively.
//! 
//! Blocks are the fundamental building blocks of [`BitString`]s.
//! 
//! [`BitString`]: ../struct.BitString/html

/// The `Block` trait unifies al of the required operations needed for bit
/// string operations.
pub trait Block: Sized + Clone + Copy {
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

	/// Bitwise not.
	fn not(self) -> Self;

	/// Bitwise or.
	fn bitor(self, rhs: Self) -> Self;

	/// Bitwise and.
	fn bitand(self, rhs: Self) -> Self;

	/// Bitwise xor.
	fn bitxor(self, rhs: Self) -> Self;

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

	/// Equality comparison operator.
	fn eq(&self, rhs: &Self) -> bool;

	/// Returns the value of the `i`th bit.
	///
	/// # Panics
	///
	/// This method should panic if `i` is >= to the block size of `Self`.
	fn get_bit(&self, i: usize) -> bool;
}

macro_rules! impl_block {
	( $( $t:ty ),* ) => {
		$(
			impl Block for $t {
				#[inline]
				fn zero() -> Self {
					0
				}

				#[inline]
				fn not(self) -> Self {
					!self
				}

				#[inline]
				fn bitor(self, rhs: Self) -> Self {
					self | rhs
				}

				#[inline]
				fn bitand(self, rhs: Self) -> Self {
					self & rhs
				}

				#[inline]
				fn bitxor(self, rhs: Self) -> Self {
					self ^ rhs
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
				fn eq(&self, rhs: &Self) -> bool {
					self == rhs
				}

				#[inline]
				fn get_bit(&self, i: usize) -> bool {
					if i >= Self::BLOCK_SIZE {
						panic!("index out of bounds")
					}

					((self >> i) & 1) != 0
				}
			}
		)*
	};
}

impl_block!(u8, u16, u32, u64);

/// Returns the required number of blocks needed to store `n` bits.
///
/// # Examples
///
/// ```
/// # use bix::bitstr::block;
/// assert_eq!(block::required_blocks::<u8>(7), 1);
/// assert_eq!(block::required_blocks::<u16>(37), 3);
/// ```
pub fn required_blocks<B: Block>(n: usize) -> usize {
	if n % B::BLOCK_SIZE == 0 {
		n / B::BLOCK_SIZE
	} else {
		(n / B::BLOCK_SIZE) + 1
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
	}
}
