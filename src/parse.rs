//! Parsing functions which make use of bit strings.

use crate::bitstr::block::FromSlice;
use crate::prelude::{BitString, Block};
// use futures::join;
use tokio::runtime;

pub type BasisSet<B> = [BitString<B>; 8];

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

pub fn basis<B: Block>(bytes: &[u8]) -> BasisSet<B>
where
	B: FromSlice<u8>,
{
	let src = BitString::from_blocks(bytes).cast::<u64>();

	let f = async {
		tokio::join!(
			tokio::spawn(n_bit(src.clone(), 0)),
			tokio::spawn(n_bit(src.clone(), 1)),
			tokio::spawn(n_bit(src.clone(), 2)),
			tokio::spawn(n_bit(src.clone(), 3)),
			tokio::spawn(n_bit(src.clone(), 4)),
			tokio::spawn(n_bit(src.clone(), 5)),
			tokio::spawn(n_bit(src.clone(), 6)),
			tokio::spawn(n_bit(src.clone(), 7)),
		)
	};

	let mut rt = runtime::Runtime::new().expect("Failed to construct runtime");
	let (b0, b1, b2, b3, b4, b5, b6, b7) = rt.block_on(f);

	[b0.expect(""), b1.expect(""), b2.expect(""), b3.expect(""), b4.expect(""), b5.expect(""), b6.expect(""), b7.expect("")]
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

	#[test]
	fn basis_length_equivalence() {
		let b = basis::<u16>(&[0, 0, 0, 0, 0, 0, 0, 0]);
		for i in 0..8 {
			assert_eq!(8, b[i].len());
		}
	}

	mod property {
		use super::*;
		use crate::bitstr::block::FromSlice;
		use quickcheck_macros::quickcheck;

		fn basis_length_equivalence<B>(src: Vec<u8>) -> bool
		where
			B: Block + FromSlice<u8>,
		{
			let len = src.len();
			let basis = basis::<B>(&src[..]);
			for i in 0..8 {
				if basis[i].len() != len {
					return false;
				}
			}

			return true;
		}

		#[quickcheck]
		fn basis_length_equivalence_u16(src: Vec<u8>) -> bool {
			basis_length_equivalence::<u16>(src)
		}

		#[quickcheck]
		fn basis_length_equivalence_u32(src: Vec<u8>) -> bool {
			basis_length_equivalence::<u32>(src)
		}

		#[quickcheck]
		fn basis_length_equivalence_u64(src: Vec<u8>) -> bool {
			basis_length_equivalence::<u64>(src)
		}
	}
}
