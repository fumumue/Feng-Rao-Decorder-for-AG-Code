# BBGS E2 Basic ECP Decoder (characteristic 2)

## Overview

This program implements a coordinate-monomial ECP construction for the BBGS
E2 trace-equation point set over GF(2^n), with odd extension degrees
`n = 3, 5, 7, 9, 11, 13`.

The curve equation used by the program is

\[
\operatorname{Tr}_{j}\left(\frac{y}{x^{2^k}}\right)
+
\operatorname{Tr}_{k}\left(\frac{y^{2^j}}{x}\right)=1,\quad x\ne0,
\]

where `n=2m+1`, `j=m` when `m` is odd and `j=m+1` otherwise, and `k=n-j`.

The evaluation spaces are generated from all coordinate monomials `X^a Y^b`
of total degree at most `r` for `A` and `B`, and at most `2r` for `H`.
The code is `C = ker(H)`. Decoding computes the ECP syndrome matrix, obtains
the kernel used for locator/support candidates, solves the error values, and
checks the corrected word against `H`.

This is **not** the complete one-point Riemann-Roch basis of E2. It is a
coordinate-monomial ECP code on the enumerated affine rational point set.

## Build

```sh
cc -O2 -std=c11 -Wall -Wextra -Wpedantic \
  -o bbgs_e2_basic_locator bbgs_e2_basic_locator.c
```

## Examples

```sh
./bbgs_e2_basic_locator --n 7 --errors 4 --trials 30 --verbose
./bbgs_e2_basic_locator --n 9 --errors 5 --trials 1
./bbgs_e2_basic_locator --help
```

`--n` selects the extension degree. `--errors` is the number of injected
nonzero error symbols in the test. There is no artificial decoder setting
such as a fixed `MAX_ERRORS`; the only input bound is the code length.
However, the mathematical support-recovery argument for this coordinate
construction guarantees recovery for `e <= r`, where `r=(n-1)/2+1`.
Successful experiments outside that range do not establish a general
guarantee.

## Field polynomials

The implementation checks that the selected polynomial generates the full
multiplicative cycle before proceeding:

| n | Polynomial |
|---:|---:|
| 3 | `0x0B` |
| 5 | `0x25` |
| 7 | `0x89` |
| 9 | `0x211` |
| 11 | `0x805` |
| 13 | `0x201B` |

The field element type is 16-bit so that GF(2^13) elements fit.

## Verified results in this build

- `n=3`, `e=2`, 3 trials: PASS (3/3)
- `n=5`, `e=3`, 3 trials: PASS (3/3)
- `n=7`, `e=4`, 10 trials: PASS (10/10)
- `n=7`, `e=5`, 2 exploratory trials: PASS (2/2; outside the stated general guarantee)
- `n=9`, `e=5`, 1 trial: PASS (1/1)

The n=11 and n=13 field polynomials are included and validated by the
primitive-cycle check, but full coordinate-matrix construction is currently
stopped by conservative memory/computation guards. The dense row-reduction
approach needs a sparse or streaming redesign for those sizes. Therefore this
release does **not** claim complete E2 decoding at n=11 or n=13.

## Important implementation choices

- The finite-field symbol type was widened from 8-bit to 16-bit.
- Field tables now support up to `2^13` elements.
- Monomial and evaluation matrices use dynamically sized allocations.
- Codeword generation uses RREF directly instead of storing a dense
  `(length - rank) x length` nullspace basis.
- Point enumeration checks its predicted capacity.
- The program reports the mathematical support-recovery range separately
  from the command-line error-count input.
