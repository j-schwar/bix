//! Parsing functions which make use of bit strings.

use crate::bitstr::block::FromSlice;
use crate::prelude::{BitString, Block};
use std::ops::Index;
use std::borrow::Borrow;
use std::sync::Arc;

/// A collections of bit strings idiomatically referring to the 8 bit strings
/// which make up the contents of some text.
///
/// All bit strings in the set must be the same length. This invariant is
/// enforced by the `new` constructor.
pub struct BasisSet<B: Block>([BitString<B>; 8]);

impl<B: Block> BasisSet<B> {
	pub fn new(arr: [BitString<B>; 8]) -> Self {
		let len = arr[0].len();
		for i in 1..8 {
			if arr[i].len() != len {
				panic!("All bit strings in a BasisSet must be the same length");
			}
		}
		BasisSet(arr)
	}

	/// The length of the bit strings in the basis set.
	///
	/// Not to be confused with the number of strings in the set.
	pub fn len(&self) -> usize {
		self.0[0].len()
	}

	/// The number of strings in the basis set.
	pub fn count(&self) -> usize {
		8
	}
}

impl<B: Block> Index<usize> for BasisSet<B> {
	type Output = BitString<B>;

	fn index(&self, index: usize) -> &Self::Output {
		&self.0[index]
	}
}

/// Returns the `n` bits in each byte of `x` packed together as a u8.
fn packed_nth_bits_in_bytes(x: u64, n: usize) -> u8 {
	let op = |y| (y >> n) & 0x01;
	let b = x.to_le_bytes();
	let b = [
		op(b[0]),
		op(b[1]),
		op(b[2]),
		op(b[3]),
		op(b[4]),
		op(b[5]),
		op(b[6]),
		op(b[7]),
	];

	let mut result = 0u8;
	for i in 0..8 {
		result |= b[i] << i;
	}
	return result;
}

/// Computes the `i`th basis string from `b`.
fn basis_string<B>(b: BitString<u64>, i: usize) -> BitString<B>
where
	B: Block + FromSlice<u8>
{
	b.into_blocks()
		.map(|(block, len)| (packed_nth_bits_in_bytes(block, i), len / 8))
		.collect::<BitString<u8>>()
		.cast()
}

/// Computes the basis set for `src`.
pub fn basis<B>(src: &[u8]) -> BasisSet<B>
where
	B: Block + FromSlice<u8>
{
	let src = BitString::from_blocks(src).cast::<u64>();
	let arr = [
		basis_string(src.clone(), 0),
		basis_string(src.clone(), 1),
		basis_string(src.clone(), 2),
		basis_string(src.clone(), 3),
		basis_string(src.clone(), 4),
		basis_string(src.clone(), 5),
		basis_string(src.clone(), 6),
		basis_string(src.clone(), 7),
	];

	BasisSet::new(arr)
}

/// Computes the `i`th basis string from `b`.
async fn async_basis_string<Src, B>(b: Src, i: usize) -> BitString<B>
where
	Src: Borrow<BitString<u64>>,
	B: Block + FromSlice<u8>
{
	b.borrow()
		.clone()
		.into_blocks()
		.map(|(block, len)| (packed_nth_bits_in_bytes(block, i), len / 8))
		.collect::<BitString<u8>>()
		.cast()
}

/// Asynchronously computes the basis set for `src`.
pub async fn async_basis<B>(bytes: &[u8]) -> BasisSet<B>
where
	B: Block + FromSlice<u8>,
{
	let src = Arc::new(BitString::from_blocks(bytes).cast::<u64>());
	let (b0, b1, b2, b3, b4, b5, b6, b7) = tokio::try_join!(
		tokio::spawn(async_basis_string(src.clone(), 0)),
		tokio::spawn(async_basis_string(src.clone(), 1)),
		tokio::spawn(async_basis_string(src.clone(), 2)),
		tokio::spawn(async_basis_string(src.clone(), 3)),
		tokio::spawn(async_basis_string(src.clone(), 4)),
		tokio::spawn(async_basis_string(src.clone(), 5)),
		tokio::spawn(async_basis_string(src.clone(), 6)),
		tokio::spawn(async_basis_string(src.clone(), 7)),
	)
	.expect("Failed to processes basis strings");

	BasisSet::new([b0, b1, b2, b3, b4, b5, b6, b7])
}

/// Returns a bit string with 1 bits marking the positions of `c` in `basis`.
pub fn byte<B: Block>(c: u8, basis: &BasisSet<B>) -> BitString<B> {
	let mut result = !BitString::zero(basis[0].len());
	for i in 0..8 {
		if c.get_bit(i) {
			result &= &basis[i];
		} else {
			let neg = !basis[i].clone();
			result &= neg;
		}
	}
	return result;
}

async fn async_bit<B: Block>(c: u8, i: usize, basis: Arc<BasisSet<B>>) -> BitString<B> {
	if c.get_bit(i) {
		basis[i].clone()
	} else {
		!basis[i].clone()
	}
}

/// Returns a bit string with 1 bits marking the positions of `c` in `basis`.
pub async fn async_byte<B: Block>(c: u8, basis: Arc<BasisSet<B>>) -> BitString<B> {
	let (s0, s1, s2, s3, s4, s5, s6, s7) = tokio::try_join!(
		tokio::spawn(async_bit(c, 0, basis.clone())),
		tokio::spawn(async_bit(c, 1, basis.clone())),
		tokio::spawn(async_bit(c, 2, basis.clone())),
		tokio::spawn(async_bit(c, 3, basis.clone())),
		tokio::spawn(async_bit(c, 4, basis.clone())),
		tokio::spawn(async_bit(c, 5, basis.clone())),
		tokio::spawn(async_bit(c, 6, basis.clone())),
		tokio::spawn(async_bit(c, 7, basis.clone())),
	).expect("Failed to process strings");

	s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7
}

pub fn byte_seq<B: Block>(seq: &[u8], basis: &BasisSet<B>) -> BitString<B> {
	if seq.len() == 0 {
		return !BitString::zero(basis[0].len());
	}

	let mut result = byte(seq[0], basis);
	for b in &seq[1..] {
		result <<= 1;
		result &= byte(*b, basis);
	}
	return result;
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_parallel_nth_bit() {
		assert_eq!(
			0b10010001,
			packed_nth_bits_in_bytes(0x40_80_bf_ff_00_02_03_44, 6)
		);
	}

	#[tokio::test]
	async fn basis_length_equivalence() {
		let b = async_basis::<u16>(&[0, 0, 0, 0, 0, 0, 0, 0]).await;
		for i in 0..8 {
			assert_eq!(8, b[i].len());
		}
	}
}
