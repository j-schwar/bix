//! Parsing functions which make use of bit strings.

use crate::bitstr::block::FromSlice;
use crate::prelude::{BitString, Block};
use std::ops::Index;

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

async fn n_bit<B: Block + FromSlice<u8>>(b: BitString<u64>, i: usize) -> BitString<B> {
	b.into_blocks()
		.map(|(block, len)| (packed_nth_bits_in_bytes(block, i), len / 8))
		.collect::<BitString<u8>>()
		.cast()
}

pub async fn basis<B>(bytes: &[u8]) -> BasisSet<B>
where
	B: Block + FromSlice<u8>,
{
	let src = BitString::from_blocks(bytes).cast::<u64>();
	let (b0, b1, b2, b3, b4, b5, b6, b7) = tokio::try_join!(
		tokio::spawn(n_bit(src.clone(), 0)),
		tokio::spawn(n_bit(src.clone(), 1)),
		tokio::spawn(n_bit(src.clone(), 2)),
		tokio::spawn(n_bit(src.clone(), 3)),
		tokio::spawn(n_bit(src.clone(), 4)),
		tokio::spawn(n_bit(src.clone(), 5)),
		tokio::spawn(n_bit(src.clone(), 6)),
		tokio::spawn(n_bit(src.clone(), 7)),
	)
	.expect("Failed to processes basis strings");

	BasisSet::new([b0, b1, b2, b3, b4, b5, b6, b7])
}

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
		let b = basis::<u16>(&[0, 0, 0, 0, 0, 0, 0, 0]).await;
		for i in 0..8 {
			assert_eq!(8, b[i].len());
		}
	}
}
