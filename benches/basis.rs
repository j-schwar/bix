#![feature(test)]

extern crate test;

use bix::prelude::*;
use test::Bencher;

const N: usize = 1_000_000;

#[inline]
fn compute_source(size: usize) -> Vec<u8> {
	let mut src = Vec::new();
	for i in 0..size {
		src.push((i % 256) as u8);
	}
	return src;
}

#[bench]
fn basis_u8(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let _ = parse::basis::<u8>(&src[..]);
	});
}

#[bench]
fn basis_u16(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let _ = parse::basis::<u16>(&src[..]);
	});
}

#[bench]
fn basis_u32(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let _ = parse::basis::<u32>(&src[..]);
	});
}

#[bench]
fn basis_u64(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let _ = parse::basis::<u64>(&src[..]);
	});
}

#[bench]
fn byte_u8(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = parse::basis::<u8>(&src[..]);
	b.iter(|| {
		let _ = parse::byte::<u8>(b'a', &basis);
	});
}

#[bench]
fn byte_u16(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = parse::basis::<u16>(&src[..]);
	b.iter(|| {
		let _ = parse::byte::<u16>(b'a', &basis);
	});
}

#[bench]
fn byte_u32(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = parse::basis::<u32>(&src[..]);
	b.iter(|| {
		let _ = parse::byte::<u32>(b'a', &basis);
	});
}

#[bench]
fn byte_u64(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = parse::basis::<u64>(&src[..]);
	b.iter(|| {
		let _ = parse::byte::<u64>(b'a', &basis);
	});
}
