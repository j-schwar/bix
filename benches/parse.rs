#![feature(test)]

extern crate test;

use bix::prelude::*;
use test::Bencher;
use std::sync::Arc;

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
fn basis_u64(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let _ = parse::basis::<u64>(&src[..]);
	});
}

#[bench]
fn async_basis_u64(b: &mut Bencher) {
	let src = compute_source(N);
	b.iter(|| {
		let mut rt = runtime();
		let _ = rt.block_on(parse::async_basis::<u64>(&src[..]));
	});
}

#[bench]
fn byte_u64(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = {
		let mut rt = runtime();
		rt.block_on(parse::async_basis::<u64>(&src[..]))
	};

	b.iter(|| {
		let _ = parse::byte(b'a', &basis);
	})
}

#[bench]
fn async_byte_u64(b: &mut Bencher) {
	let src = compute_source(N);
	let basis = {
		let mut rt = runtime();
		rt.block_on(parse::async_basis::<u64>(&src[..]))
	};
	let basis = Arc::new(basis);

	b.iter(|| {
		let mut rt = runtime();
		rt.block_on(parse::async_byte(b'a', basis.clone()));
	});
}
