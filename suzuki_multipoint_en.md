# Suzuki curve: two-point AG code and basic syndrome decoder

## What is implemented

This is a first **two-point** implementation, with
\[
G=aP_{00}+bP_\infty.
\]
It is not yet a general s-point divisor with arbitrary affine places.

- Curve: \(y^8-y=x^2(x^8-x)\) over \(\mathrm{GF}(8)\).
- Field: \(\mathrm{GF}(2)[z]/(z^3+z+1)\).
- \(P_{00}=(0,0)\) and \(P_\infty\) are the two divisor places.
- Evaluation support: the other 63 affine rational points.
- The code is the dual of the evaluation span of \(L(2G)\):
  \[
  C=\{c\in\mathrm{GF}(8)^{63}:\sum_{Q\in D}c_Qh(Q)=0
  \text{ for every }h\in L(2G)\}.
  \]
  This choice makes every product \(f_if_j\), for \(f_i,f_j\in L(G)\), a parity-check function.

## Basic decoding

For a received word \(r=c+e\), form
\[
S_{ij}=\sum_{Q\in D}r_Q f_i(Q)f_j(Q).
\]
The codeword contribution vanishes. The right kernel of \(S\) gives linear combinations of the \(L(G)\) basis functions; their common zeros on the evaluation support are used as error-location candidates. Error values are then recovered from the first syndrome column by a finite-field linear system.

The implementation constructs the two-point Riemann--Roch spaces from the two-point Weierstrass semigroup data for the \(q=8\) Suzuki function field, and keeps linearly independent evaluation functions. The pair-gap generators and corresponding functions are based on the two-point semigroup description in Gretchen L. Matthews, *Codes from the Suzuki Function Field*.

## Build and run

\`\`\`sh
cc -O2 -std=c11 -Wall -Wextra -o suzuki_multipoint suzuki_multipoint.c
./suzuki_multipoint
\`\`\`

The default run is equivalent to:

\`\`\`sh
./suzuki_multipoint --a 14 --b 14 --errors 3 --seed 7
\`\`\`

Options:

- \`--a N\`: coefficient of \(P_{00}\) in \(G\)
- \`--b N\`: coefficient of \(P_\infty\) in \(G\)
- \`--errors T\`: number of nonzero error coordinates to inject (1--12)
- \`--seed N\`: seed for reproducible test errors
- \`--help\`: show command-line usage

For the current 63-point support, the program requires \(a,b\geq1\) and \(a+b\leq31\), so that \(\deg(2G)<63\). These are implementation bounds, not a claim that every allowed parameter/seed combination is guaranteed to decode the requested number of errors. The decoder checks the actual result and exits with failure if the locator candidates or correction verification do not match.

## Example output (default parameters)

- \(n=63\)
- \(\ell(G)=15\)
- \(\ell(2G)=43\)
- dual evaluation code dimension \(20\)
- three injected errors located and corrected
- final result: \`PASS\`

The program prints all evaluation points, injected and decoded error locations/values, the codeword, error vector, and corrected word.

## Scope and limitations

This is a compact, algebraic demonstration over \(\mathrm{GF}(8)\), not a performance-optimized decoder. It implements the two-point case \(G=aP_{00}+bP_\infty\); it does not yet accept an arbitrary list of affine divisor places \(P_i\), nor arbitrary field sizes. The random test is a demonstration, not a proof of a universal decoding radius.