//! Defines and implements `Block` and associated traits for integers and SIMD
//! types which may be used as the base for bit strings.

use std::convert::TryInto;
use std::ops::*;

/// The `Block` trait unifies al of the required operations needed for bit
/// string operations.
pub trait Block:
	Sized
	+ Clone
	+ Copy
	+ Default
	+ PartialEq
	+ Eq
	+ Not
	+ BitAnd
	+ BitAndAssign
	+ BitOr
	+ BitOrAssign
	+ BitXor
	+ BitXorAssign
	+ CarriedAdd
	+ CarriedAddAssign
	+ CarriedShl
	+ CarriedShlAssign
	+ CarriedShr
	+ CarriedShrAssign
	+ FromLittleEndianByteSlice
{
	/// Size of this block in bits.
	const BLOCK_SIZE: usize = std::mem::size_of::<Self>() * 8;
}

impl<B> Block for B where
	B: Sized
		+ Clone
		+ Copy
		+ Default
		+ PartialEq
		+ Eq
		+ Not
		+ BitAnd
		+ BitAndAssign
		+ BitOr
		+ BitOrAssign
		+ BitXor
		+ BitXorAssign
		+ CarriedAdd
		+ CarriedAddAssign
		+ CarriedShl
		+ CarriedShlAssign
		+ CarriedShr
		+ CarriedShrAssign
		+ FromLittleEndianByteSlice
{
}

/// Addition with carry in/out.
///
/// # Semantics
///
/// Adds the sum of `rhs` and `carry_in` to `self` returning the result along
/// with the carry out (overflow) bit.
pub trait CarriedAdd: Sized {
	fn carried_add(self, rhs: Self, carry_in: bool) -> (Self, bool);
}

macro_rules! impl_carried_add {
	( $( $x:ty ),* ) => {
		$(
			impl CarriedAdd for $x {
				#[inline]
				fn carried_add(self, rhs: Self, carry_in: bool) -> (Self, bool) {
					let c = if carry_in { 1 } else { 0 };
					self.overflowing_add(rhs + c)
				}
			}
		)*
	};
}

impl_carried_add!(u8, u16, u32, u64);

/// An assignment variant of [`CarriedAdd`].
///
/// [`CarriedAdd`]: ./trait.CarriedAdd.html
pub trait CarriedAddAssign: Sized {
	fn carried_add_assign(&mut self, rhs: Self, carry_in: bool) -> bool;
}

impl<I> CarriedAddAssign for I
where
	I: CarriedAdd + Copy,
{
	#[inline]
	fn carried_add_assign(&mut self, rhs: Self, carry_in: bool) -> bool {
		let (x, carry_out) = self.carried_add(rhs, carry_in);
		*self = x;
		return carry_out;
	}
}

/// Left shift with carry in/out.
pub trait CarriedShl: Sized {
	fn carried_shl(self, shift: usize, carry_in: Self) -> (Self, Self);
}

macro_rules! impl_carried_shl {
	( $( $x:ty ),* ) => {
		$(
			impl CarriedShl for $x {
				#[inline]
				fn carried_shl(self, shift: usize, carry_in: Self) -> (Self, Self) {
					if shift > Self::BLOCK_SIZE {
						panic!("shift too large: only shifts of less than block size are supported");
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
			}
		)*
	};
}

impl_carried_shl!(u8, u16, u32, u64);

/// An assignment variant of [`CarriedShl`].
///
/// [`CarriedShl`]: ./trait.CarriedShl.html
pub trait CarriedShlAssign: Sized {
	fn carried_shl_assign(&mut self, shift: usize, carry_in: Self) -> Self;
}

impl<I> CarriedShlAssign for I
where
	I: CarriedShl + Copy,
{
	#[inline]
	fn carried_shl_assign(&mut self, shift: usize, carry_in: Self) -> Self {
		let (result, carry_out) = self.carried_shl(shift, carry_in);
		*self = result;
		return carry_out;
	}
}

/// Right shift with carry in/out.
pub trait CarriedShr: Sized {
	fn carried_shr(self, shift: usize, carry_in: Self) -> (Self, Self);
}

macro_rules! impl_carried_shr {
	( $( $x:ty ),* ) => {
		$(
			impl CarriedShr for $x {
				#[inline]
				fn carried_shr(self, shift: usize, carry_in: Self) -> (Self, Self) {
					if shift > Self::BLOCK_SIZE {
						panic!("shift too large: only shifts of less than block size are supported");
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
			}
		)*
	};
}

impl_carried_shr!(u8, u16, u32, u64);

/// An assignment variant of [`CarriedShr`].
///
/// [`CarriedShr`]: ./trait.CarriedShl.html
pub trait CarriedShrAssign: Sized {
	fn carried_shr_assign(&mut self, shift: usize, carry_in: Self) -> Self;
}

impl<I> CarriedShrAssign for I
where
	I: CarriedShr + Copy,
{
	#[inline]
	fn carried_shr_assign(&mut self, shift: usize, carry_in: Self) -> Self {
		let (result, carry_out) = self.carried_shr(shift, carry_in);
		*self = result;
		return carry_out;
	}
}

/// Constructs an object from a sequence of bytes interpreting them as a little
/// endian encoded version of this type.
pub trait FromLittleEndianByteSlice {
	/// Constructs an instance of this type from a slice of bytes.
	///
	/// For rust's built in types, this function maps to the type's corresponding
	/// `from_le_bytes` function.
	///
	/// # Panics
	///
	/// Implementations may panic if `slice` does not contain the exact amount of
	/// bytes required to construct this type.
	fn from_le_byte_slice(slice: &[u8]) -> Self;
}

impl FromLittleEndianByteSlice for u8 {
	fn from_le_byte_slice(slice: &[u8]) -> Self {
		if slice.len() != 1 {
			panic!("incorrect number of bytes");
		}

		slice[0]
	}
}

macro_rules! impl_from_le_byte_slice {
	( $( ($t:ty, $n:tt) ),* ) => {
		$(
			impl FromLittleEndianByteSlice for $t {
				fn from_le_byte_slice(slice: &[u8]) -> Self {
					Self::from_le_bytes(slice[0..$n].try_into().expect("incorrect number of bytes"))
				}
			}
		)*
	}
}

impl_from_le_byte_slice![(u16, 2), (u32, 4), (u64, 8)];

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
		fn carried_add_assign() {
			let mut x = 254u8;
			let carry_out = x.carried_add_assign(1, true);
			assert_eq!((x, carry_out), (0, true));

			let mut y = 64u8;
			let carry_out = y.carried_add_assign(4, false);
			assert_eq!((y, carry_out), (68, false));
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
