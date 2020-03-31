#![feature(test)]

extern crate test;

use bix::bitstr::block::Block;
use bix::parse;
use bix::BitString;
use test::Bencher;

/// The size of bit string to use for benchmarking in bytes.
const BENCH_BYTE_COUNT: usize = 1048576;

macro_rules! bench_or {
	( $block:ty, $bencher:ident ) => {
		let block_count = BENCH_BYTE_COUNT / std::mem::size_of::<$block>();
		let blocks: Vec<$block> = std::iter::repeat(<$block>::zero())
			.take(block_count)
			.collect();
		// We can't just benchmark the `|` operation because it doesn't work on
		// references, so instead we have to benchmark the construction as well.
		$bencher.iter(|| {
			let x = BitString::<$block>::from_blocks(&blocks);
			let y = BitString::from_blocks(&blocks);
			x | y
			});
	};
}

#[bench]
fn bench_u8_or(b: &mut Bencher) {
	bench_or!(u8, b);
}

#[bench]
fn bench_u16_or(b: &mut Bencher) {
	bench_or!(u16, b);
}

#[bench]
fn bench_u32_or(b: &mut Bencher) {
	bench_or!(u32, b);
}

#[bench]
fn bench_u64_or(b: &mut Bencher) {
	bench_or!(u64, b);
}

macro_rules! bench_shl {
	( $block:ty, $bencher:ident ) => {
		let block_count = BENCH_BYTE_COUNT / std::mem::size_of::<$block>();
		let blocks: Vec<$block> = std::iter::repeat(1).take(block_count).collect();
		$bencher.iter(|| {
			let x = BitString::<$block>::from_blocks(&blocks);
			x << 1
			});
	};
}

#[bench]
fn bench_u8_shl(b: &mut Bencher) {
	bench_shl!(u8, b);
}

#[bench]
fn bench_u16_shl(b: &mut Bencher) {
	bench_shl!(u16, b);
}

#[bench]
fn bench_u32_shl(b: &mut Bencher) {
	bench_shl!(u32, b);
}

#[bench]
fn bench_u64_shl(b: &mut Bencher) {
	bench_shl!(u64, b);
}

macro_rules! bench_add {
	( $block:ty, $bencher:ident ) => {
		let block_count = BENCH_BYTE_COUNT / std::mem::size_of::<$block>();
		let blocks: Vec<$block> = std::iter::repeat(42).take(block_count).collect();
		$bencher.iter(|| {
			let x = BitString::<$block>::from_blocks(&blocks);
			let y = BitString::<$block>::from_blocks(&blocks);
			x + y
			});
	};
}

#[bench]
fn bench_u8_add(b: &mut Bencher) {
	bench_add!(u8, b);
}

#[bench]
fn bench_u16_add(b: &mut Bencher) {
	bench_add!(u16, b);
}

#[bench]
fn bench_u32_add(b: &mut Bencher) {
	bench_add!(u32, b);
}

#[bench]
fn bench_u64_add(b: &mut Bencher) {
	bench_add!(u64, b);
}

#[bench]
fn basis_u64(b: &mut Bencher) {
	let src: Vec<u8> = std::iter::repeat(0xabu8).take(BENCH_BYTE_COUNT).collect();
	b.iter(|| {
		let _ = parse::basis::<u64>(&src[..]);
	});
}

#[bench]
fn byte_u64(b: &mut Bencher) {
	let src: Vec<u8> = std::iter::repeat(0xabu8).take(BENCH_BYTE_COUNT).collect();
	let basis = parse::basis::<u64>(&src[..]);
	b.iter(|| {
		let _ = parse::byte(0xab, &basis);
	});
}

#[bench]
fn byte_seq_u64(b: &mut Bencher) {
	let src: Vec<u8> = std::iter::repeat(0xabu8).take(BENCH_BYTE_COUNT).collect();
	let basis = parse::basis::<u64>(&src[..]);
	b.iter(|| {
		let _ = parse::byte_seq(&[0xab, 0xab, 0xab, 0xab], &basis);
	});
}
