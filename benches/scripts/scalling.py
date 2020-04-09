from typing import Dict, Tuple, List
import matplotlib.pyplot as plt
import numpy as np
import re
import subprocess


def run_benchmarks(name=None):
	"""
	Compiles and runs benchmarks returning the created process.

	If given a name, only benchmarks containing that name will be run.

	Keyword Arguments:
	name -- an optional filter to pass to cargo bench (default None)
	"""
	args = ["rustup", "run", "nightly", "cargo", "bench"]
	if name is not None:
		args.append(name)
	return subprocess.run(args, capture_output=True, text=True)


def bench_result_to_tuple(line: str) -> Tuple[str, int]:
	"""
	Converts a benchmark output line into a tuple containing the name of the
	benchmark along with the recorded execution time.
	"""
	split = list(filter(lambda x: x != "", line.split(" ")))
	return (split[1], int(split[4].replace(",", "")))


def split_name_and_type(benchmark_name: str) -> Tuple[str, str]:
	"""
	Splits the name of a benchmark from the type that it is testing.

	For example, the function name `my_benchmark_u64` will be split into
	`my_benchmark` and `u64`. Since we want to compare the timings between the
	same function with different typings, our benchmarks will be named in this
	format.

	If the benchmark name does not fall into this format, then `None` is returned.
	"""
	m = re.search(r'^(.*)_(u[\d]{1,3})$', benchmark_name)
	if m is None:
		return None
	return (m.group(1), m.group(2))


def type_width(ty: str) -> int:
	"""
	Returns the width of an unsigned integer type as an int.

	For example, returns 8 for `u8`, 16 for `u16`, etc.
	"""
	m = re.search(r'^u([\d]{1,3})$', ty)
	if m is None:
		return None
	return int(m.group(1))


def construct_suites(bench_results: str) -> Dict[str, List[Tuple[str, int]]]:
	"""
	Takes the contents of stdout of a benchmark process, parses it and returns
	graphable results.

	The keys of the dictionary are the names of benchmarks without the type suffix
	and the values are the type suffixes paired with the execution time for the
	corresponding function.

	Timings are assumed to be sorted in ascending order based on the width of the
	type suffix.
	"""
	lines = bench_results.split('\n')
	filtered = filter(lambda x: "bench:" in x, lines)
	suites = dict()
	for name, time in map(bench_result_to_tuple, filtered):
		n = split_name_and_type(name)
		if n is None:
			continue
		suite, ty = n
		if suite not in suites:
			suites[suite] = [(ty, time)]
		else:
			suites[suite].append((ty, time))
	return suites


def graph_timings(ax, timings):
	"""Plots timings on a given axis."""
	x_values, y_values = zip(*timings)
	return ax.plot(x_values, y_values, "b-", label="Time")


def speedup(timings: List[Tuple[str, int]]) -> List[Tuple[str, float]]:
	"""Converts a list of timings into a list of speedup factors."""
	normalize = lambda x: float(x[1])
	base = normalize(timings[0])
	return list(map(lambda x: (x[0], (base / normalize(x))), timings))


def graph_speedup(ax, timings):
	"""Plots speedup on a given axis."""
	s = speedup(timings)
	x_values, y_values = zip(*s)
	return ax.plot(x_values, y_values, "r-", label="Speedup")


results = run_benchmarks()
suites = construct_suites(results.stdout)

plt.ioff()

for name, timings in suites.items():
	timings.sort(key=lambda x: type_width(x[0]))
	# Each suite gets its own plot.
	fig, host = plt.subplots()
	speedup_ax = host.twinx()
	host.set_title(name)
	host.set_xlabel("Block Type")
	host.set_ylabel("Time (ns)")
	speedup_ax.set_ylabel("Speedup")
	p1 = graph_timings(host, timings)
	p2 = graph_speedup(speedup_ax, timings)
	fig.legend()

plt.show()
