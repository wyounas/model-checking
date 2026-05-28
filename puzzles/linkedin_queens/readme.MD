# Quick Start: LinkedIn-Queens and puzzle.fizz

## Blog Post 

This repository contains code for the LinkedIn-Queens puzzle, documented in this blog post:  
[Exploring All Solutions to LinkedIn Queens Puzzle with a SAT Solver and Two Model Checkers](https://wyounas.github.io/model-checking/puzzles/2025/10/18/exploring-all-solutions-to-linkedin-queens-puzzle-with-a-sat-solver-and-two-model-checkers/)


## Details

This directory contains:

* **queensfourbyfour.pml**: Promela model for the LinkedIn-Queens puzzle, for a 4x4 grid.
* **queensninebynine.pml**: Promela model for the LinkedIn-Queens puzzle, for a 9x9 grid.
* **queensninebynine.pml**: Promela model for the LinkedIn-Queens puzzle, for a 9x9 grid.
* **queens_wo_region.pml**: Promela model for the LinkedIn-Queens puzzle, without the region constraint.
* **puzzle.fizz**: FizzBee model of the LinkedIn-Queens puzzle.

## Prerequisites

* **Spin** model checker
* **FizzBee** (see [https://github.com/fizzbee-io/fizzbee](https://github.com/fizzbee-io/fizzbee) for install)

### Installing PyEDA (macOS, Python ≥3.12)

I had to suppress a strict compiler warning during installation, so please proceed with caution.

Run the following inside your virtual environment:

```bash

pip install --upgrade pip setuptools wheel

export CFLAGS="-Wno-incompatible-function-pointer-types"
pip install --no-cache-dir "pyeda==0.29.0"
unset CFLAGS
```

## Run the Promela Model

```bash
# Run the model:
spin -run queensfourbyfour.pml
```

```bash
# Exhaustively search and record all counterexamples:
./pan -E -c0 -e
```


## View a Specific Trail

```bash
spin -p -t5242 queens_wo_region.pml
```

## Run with FizzBee

After installing FizzBee, execute:

```bash
fizz puzzle.fizz
```

This will invoke FizzBee's model checker on `puzzle.fizz` and display results.
