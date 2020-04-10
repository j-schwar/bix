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

fn runtime() -> tokio::runtime::Runtime {
	tokio::runtime::Builder::new()
		.threaded_scheduler()
		.build()
		.expect("Failed to construct runtime")
}

#[bench]
fn basis_u8(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let mut rt = runtime();
		let _ = rt.block_on(parse::basis::<u8>(&src[..]));
	});
}

#[bench]
fn basis_u16(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let mut rt = runtime();
		let _ = rt.block_on(parse::basis::<u16>(&src[..]));
	});
}

#[bench]
fn basis_u32(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let mut rt = runtime();
		let _ = rt.block_on(parse::basis::<u32>(&src[..]));
	});
}

#[bench]
fn basis_u64(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let mut rt = runtime();
		let _ = rt.block_on(parse::basis::<u64>(&src[..]));
	});
}
