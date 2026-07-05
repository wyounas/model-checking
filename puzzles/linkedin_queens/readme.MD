# Quick Start: LinkedIn Queens

## Blog Post

This repository contains code for solving the LinkedIn Queens puzzle with Promela, Python, and FizzBee, as documented in this blog post:
[Finding All Solutions to LinkedIn Queens with a SAT Solver and Model Checkers](https://wyounas.github.io/model-checking/puzzles/2026/06/06/finding-all-solutions-to-linkedin-queens-with-a-sat-solver-and-model-checkers/)


## Details

This directory contains:

* queenfourbyfour.pml: Promela model for a 4x4 LinkedIn Queens grid.
* queenninebynine.pml: Promela model for a 9x9 LinkedIn Queens grid.
* queens_wo_region.pml: Promela model without the region constraint.
* queens.py: Python SAT solver for the LinkedIn Queens puzzle.
* queens.fizz: FizzBee model for the LinkedIn Queens puzzle.

## Prerequisites

* Python and PyEDA. The SAT solver was tested with Python 3.14.3.
* Spin model checker. Tested with Spin 6.5.2.
* FizzBee. See [https://github.com/fizzbee-io/fizzbee](https://github.com/fizzbee-io/fizzbee) for installation instructions.

### Running the SAT Solver: Installing PyEDA (macOS, Python >= 3.12)

To run the SAT solver in Python, install PyEDA.

I had to suppress a strict compiler warning during installation, so please proceed with caution.

Run the following inside your virtual environment:

```bash

$ pip install --upgrade pip setuptools wheel

$ export CFLAGS="-Wno-incompatible-function-pointer-types"
$ pip install --no-cache-dir "pyeda==0.29.0"
$ unset CFLAGS
```

Then run the Python program:
```bash
$ python3 queens.py
```

## Running the Spin/Promela Model

```bash
$ spin -a queenfourbyfour.pml
$ gcc -o pan pan.c
$ ./pan -E -c0 -e
```


### View a Specific Trail

```bash
$ spin -p -t -k queenfourbyfour.pml.trail queenfourbyfour.pml
```

## Running FizzBee

After installing FizzBee, execute:

```bash
$ fizz queens.fizz
```

This invokes FizzBee's model checker on `queens.fizz` and displays the results.
