# Suzuki curve: two AG codes and ECP decoding

## Build and run

```sh
cc -O2 -std=c11 suzuki_two_codes.c -o suzuki_two_codes
./suzuki_two_codes
```

Optional arguments are `G-degree`, `number-of-errors`, and `seed`:

```sh
./suzuki_two_codes 60 3 123
```

The current ECP pair is fixed at `A = 30 P_inf - Q` and `B = 30 P_inf`.
Therefore `G-degree` must be at least 60, and the guaranteed test error count is at most 3.

## Construction

The program uses the Suzuki curve over GF(2^12), with

- `q = 8`, `q0 = 2`;
- `y^8 + y = x^2 (x^8 + x)`;
- genus `g = 14`;
- 5888 affine rational points.

Three fibres are reserved, and the common evaluation set `D` consists of all affine
points outside those fibres. The selected points are `Q`, `P1`, and `P2`, in distinct
reserved fibres. The two divisors are

\[
G_1=mP_\infty+P_1-Q,\qquad G_2=mP_\infty+P_2-Q.
\]

They have the same degree `m`. The decoded codes are

\[
C_i=C_L(D,G_i)^\perp.
\]

For the ECP pair the program uses

\[
A=30P_\infty-Q,\qquad B=30P_\infty.
\]

Since `A+B = 60 P_inf - Q <= G_i` when `m >= 60`, pointwise products
`C_L(D,A) * C_L(D,B)` lie in `C_L(D,G_i) = C_i^perp`. Also
`dim L(A)=16 > 3`, and the AG lower bound gives
`d(C_L(D,B)^perp) >= 30 - 2*14 + 2 = 4`. Thus the ECP condition supports
correction of up to 3 errors.

## Decoder

For a received word `r`, the decoder forms the linear map

\[
T_r:L(A)\longrightarrow L(B)^*,\quad
 a\longmapsto\left(b\mapsto\sum_{P\in D}r_Pa(P)b(P)\right).
\]

The kernel supplies functions vanishing at the error positions. The common zero set
is used as the error support; error values are then recovered from the syndromes
against a basis of `L(G_i)`. Finally, all parity checks are recomputed.

## What the output establishes

- both divisors have the same degree;
- both evaluation codes have the same computed dimension;
- `G1-G2` is tested for principality by the implemented Riemann--Roch routine;
- the two evaluation row spaces are compared directly;
- the Schur-product containment required by this ECP construction is checked directly;
- a random word in each dual code is generated, errors are injected, and exact recovery is checked.

The reported `d >= m-2g+2` is a common designed lower bound for the dual codes, not
an exact minimum-distance computation. Likewise, non-principal divisors and distinct
coordinate row spaces establish that these are distinct constructions in the fixed
coordinate system; this program does not prove that the codes are inequivalent under
all monomial coordinate transformations.
