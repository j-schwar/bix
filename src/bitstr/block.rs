//! Defines the `Block` trait and implements if the for fundament unsigned
//! integer types as well as `__m128` and `__m256` data types for SSE and AVX
//! architectures respectively.
//!
//! Blocks are the fundamental building blocks of [`BitString`]s.
//!
//! [`BitString`]: ../struct.BitString/html

/// The `Block` trait unifies al of the required operations needed for bit
/// string operations.
pub trait Block: Sized + Clone + Copy + PartialEq + Eq {
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

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[derive(Copy, Clone, Debug)]
pub struct U256(core::arch::x86_64::__m256i);

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
impl PartialEq for U256 {
	#[inline]
	fn eq(&self, rhs: &Self) -> bool {
		use core::arch::x86_64::*;
		unsafe {
			let packed_cmp = U256(_mm256_cmpeq_epi64(self.0, rhs.0));
			let ones = Self::zero().not();
			_mm256_testc_si256(packed_cmp.0, ones.0) == 1
		}
	}
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
impl Eq for U256 {}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
impl Block for U256 {
	#[inline]
	fn zero() -> Self {
		use core::arch::x86_64::*;
		unsafe {
			U256(_mm256_setzero_si256())
		}
	}

	#[inline]
	fn not(self) -> Self {
		use core::arch::x86_64::*;
		unsafe {
			let ones = _mm256_set1_epi8(-1);
			U256(_mm256_xor_si256(self.0, ones))
		}
	}

	#[inline]
	fn bitor(self, rhs: Self) -> Self {
		use core::arch::x86_64::*;
		unsafe {
			U256(_mm256_or_si256(self.0, rhs.0))
		}
	}

	#[inline]
	fn bitand(self, rhs: Self) -> Self {
		use core::arch::x86_64::*;
		unsafe {
			U256(_mm256_and_si256(self.0, rhs.0))
		}
	}

	#[inline]
	fn bitxor(self, rhs: Self) -> Self {
		use core::arch::x86_64::*;
		unsafe {
			U256(_mm256_xor_si256(self.0, rhs.0))
		}
	}

	fn carried_add(self, rhs: Self, carry_in: bool) -> (Self, bool) {
		use core::arch::x86_64::*;
		unsafe {
			let parts_sum = _mm256_add_epi64(self.0, rhs.0);
			return (U256(parts_sum), carry_in);
		}
	}

	fn carried_shl(self, _rhs: usize, _carry_in: Self) -> (Self, Self) {
		unimplemented!();
	}

	fn carried_shr(self, _rhs: usize, _carry_in: Self) -> (Self, Self) {
		unimplemented!();
	}

	fn get_bit(&self, _i: usize) -> bool {
		unimplemented!();
	}
}

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

	#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
	mod u256 {
		use super::*;

		/// Constructs a `U256` from 64-bit parts.
		/// 
		/// As per Intel's documentation, the bit layout of the resultant `U256` is:
		/// 
		/// ```text
		/// dst[63:0] := d
		/// dst[127:64] := c
		/// dst[191:128] := b
		/// dst[255:192] := a
		/// dst[MAX:256] := 0
		/// ```
		fn u256_from_parts(a: i64, b: i64, c: i64, d: i64) -> U256 {
			use core::arch::x86_64::*;
			unsafe {
				U256(_mm256_set_epi64x(a, b, c, d))
			}
		}

		#[test]
		fn zero_equals_zero() {
			let a = U256::zero();
			let b = U256::zero();
			assert!(a.eq(&b));
		}

		#[test]
		fn zero_not_equal_all_ones() {
			let a = U256::zero();
			let b = U256::zero().not();
			assert!(!a.eq(&b));
		}

		#[test]
		fn equal() {
			let a = u256_from_parts(531356, 134, -01135, 351643);
			let b = a;
			assert_eq!(a, b);
		}

		#[test]
		fn not_equal() {
			let a = u256_from_parts(531356, 134, -01135, 351643);
			let b = u256_from_parts(531356, 135, -01135, 351643);
			assert!(!a.eq(&b));
		}

		#[test]
		fn carried_add_no_carry_in() {
			let a = u256_from_parts(0, -1, -1, -1);
			let b = u256_from_parts(0, 0, 0, 1);
			let expected = u256_from_parts(1, 0, 0, 0);
			assert_eq!(a.carried_add(b, false), (expected, false));
		}
	}
}
