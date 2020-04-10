use bix::prelude::*;
use parse::BasisSet;
use std::fs;
use structopt::StructOpt;

type BlockType = u64;

/// Byte, word, and line counter implemented using bit-string-parsing.
#[derive(Debug, StructOpt)]
struct Opt {
	/// Count bytes
	#[structopt(short = "c")]
	bytes: bool,

	/// Count words
	#[structopt(short = "w")]
	words: bool,

	/// Count lines
	#[structopt(short = "l")]
	lines: bool,

	/// Set of input files to read from
	input_files: Vec<String>,
}

/// Counts the number of words in a string represented by `basis`.
fn count_words<B: Block>(basis: &BasisSet<B>) -> usize {
	let start = !(!BitString::zero(basis[0].len()) << 1);
	let spaces = parse::byte(b' ', basis);
	let new_lines = parse::byte(b'\n', basis);
	let tabs = parse::byte(b'\t', basis);
	let word_delimiters = spaces | new_lines | tabs;
	let words = !word_delimiters.clone();
	let word_starts = words & (start | (word_delimiters << 1));
	word_starts.pop_count()
}

/// Counts the number of lines in a string represented by `basis`.
fn count_lines<B: Block>(basis: &BasisSet<B>) -> usize {
	parse::byte(b'\n', basis).pop_count()
}

#[tokio::main]
async fn main() {
	let mut opt = Opt::from_args();

	if !opt.bytes && !opt.words && !opt.lines {
		opt.bytes = true;
		opt.words = true;
		opt.lines = true;
	}

	if opt.input_files.is_empty() {
		println!("please supply an input file");
		return;
	}

	let mut total_line_count = 0;
	let mut total_word_count = 0;
	let mut total_byte_count = 0;
	for file in &opt.input_files {
		match fs::read(&file) {
			Ok(contents) => {
				let basis = parse::async_basis::<BlockType>(&contents[..]).await;

				if opt.lines {
					let line_count = count_lines(&basis);
					print!("{:8}", line_count);
					total_line_count += line_count;
				}

				if opt.words {
					let word_count = count_words(&basis);
					print!("{:8}", word_count);
					total_word_count += word_count;
				}

				if opt.bytes {
					let byte_count = contents.len();
					print!("{:8}", byte_count);
					total_byte_count += byte_count;
				}

				println!(" {}", file);
			}
			Err(e) => {
				println!("unable to open {}: {}", file, e);
				return;
			}
		}
	}

	if opt.input_files.len() > 1 {
		if opt.lines {
			print!("{:8}", total_line_count);
		}
		if opt.words {
			print!("{:8}", total_word_count);
		}
		if opt.bytes {
			print!("{:8}", total_byte_count);
		}
		println!(" total");
	}
}
