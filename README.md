# OrthoLoq V6

A satisfiability solver for Birkhoff–von Neumann quantum logic, with support for model generation.

OrthoLoq decides **weak satisfiability** of Birkhoff–von Neumann formulae over a specified finite-dimensional complex Hilbert space. It combines lattice- and dimension-based reasoning with an exact algebraic backend. For supported satisfiable instances, it can also output a concrete model in the form of orthogonal projectors.

## Requirements

- A C++20 compiler (`clang++` by default)
- `make`
- The Z3 runtime library (`libz3`) for exact solving

On Ubuntu, you can install these dependencies with:

```bash
sudo apt update
sudo apt install clang make build-essential libz3-4
```

Z3 is loaded dynamically at runtime, so its development headers are not required to compile OrthoLoq. If Z3 is unavailable, some instances cannot be decided by the complete solver.

## Build

Run the following command from the project directory (the directory containing `Makefile`):

```bash
make
```

This creates the executable `ortholoq`. To remove the executable and object files, run:

```bash
make clean
```

## Run

Pass a `.qlcir` input file to the executable:

```bash
./ortholoq benchmarks/original84/physics/interference_2path_d2.qlcir
```

For this example, the solver returns:

```text
SAT
```

To request a model, add `--model`:

```bash
./ortholoq --model benchmarks/original84/physics/interference_2path_d2.qlcir
```

One verified output for this benchmark is:

```text
SAT
model dimension: 2
path1 projector:
  [ 1/2 -1/2]
  [-1/2  1/2]
psi projector:
  [1/2 1/2]
  [1/2 1/2]
path0 projector:
  [1/5 2/5]
  [2/5 4/5]
output projector:
  [1/2 1/2]
  [1/2 1/2]
```

The exact matrices may differ between valid models. Model generation currently supports selected constructive witnesses; OrthoLoq can establish `SAT` even when a concrete model cannot be printed.

For solver statistics, use:

```bash
./ortholoq --stats benchmarks/original84/physics/interference_2path_d2.qlcir
```

Other options include `--fast-only` (abstract reasoning only; may return `UNKNOWN`) and `--exact-only` (direct exact solving). Their syntax is:

```text
ortholoq [--model] [--stats] [--fast-only|--exact-only] <file.qlcir>
```

## Benchmarks

The `benchmarks/` directory contains **133 instances**: 84 original instances in `original84/` and 49 scaling instances in `scaling49/`. The inputs use the QLCIR-G1 format and retain their `.qlcir` extension.

## Notes

The provided `Makefile` targets Linux-like environments and links against `libdl` for dynamic library loading. The solver's source code is C++20; the benchmark inputs are separate from the compiled executable.
