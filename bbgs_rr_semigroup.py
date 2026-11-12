#!/usr/bin/env python3
"""Compute the one-point Weierstrass semigroup at P1 for BBGS E2/GF(32).

Parameters: q=2, c=5, a=3, b=2 (a+b=c, gcd(a,b)=1).
The calculation uses the explicit monomial basis for L(v P1) from
C. Hu, IEEE Trans. Inf. Theory 63 (2017), 7237-7246, Section III.

This is a lattice-point/Riemann-Roch dimension calculation, not a
finite-field point search.  It is intentionally specialized to the
published a=b+1 case q=2,c=5.
"""
Q, C, A, B = 2, 5, 3, 2
NC = (Q**C - 1) // (Q - 1)
NB = (Q**B - 1) // (Q - 1)
GENUS = ((Q**C - 2) * (Q**(A - 1) + Q**(B - 1) - 2)
         + (Q**C - Q)) // 2


def ceil_div(n: int, d: int) -> int:
    """Ceiling of n/d for positive d."""
    return -((-n) // d)


def rr_dimension(v: int) -> int:
    """Dimension l(v P1), counted from Hu's monomial basis.

    For r=s=t=0 the exponent triples (i,j,k) satisfy
      i >= -v,
      0 <= i + (q^c-1)k < q^c-1,
      0 <= -q^a i + (q^c-1)j < q^c-1,
      0 <= q^(a-1)N_b i - q^(b-1)N_c j
           - (q^(a-1)-1)N_c k.

    The two half-open interval inequalities uniquely give
      j = ceil(q^a i / N_c), k = ceil(-i / N_c).
    For each residue i0 modulo N_c, write i=i0+t N_c (t>=0).
    Then j increases by q^a, k decreases by 1, and the final
    expression decreases by exactly N_c. Thus the number of
    admissible t is floor(T(i0)/N_c)+1 when T(i0)>=0.
    """
    if v < 0:
        return 0
    total = 0
    for i0 in range(-v, -v + NC):
        j = ceil_div(Q**A * i0, NC)
        k = ceil_div(-i0, NC)
        T = (Q**(A - 1) * NB * i0
             - Q**(B - 1) * NC * j
             - (Q**(A - 1) - 1) * NC * k)
        if T >= 0:
            total += T // NC + 1
    return total


def main() -> None:
    assert (Q, C, A, B, NC, NB, GENUS) == (2, 5, 3, 2, 31, 3, 75)

    # l(0)=1 and l(-P1)=0.
    previous = 0
    gaps = []
    nongaps = {0}
    for n in range(0, 2 * GENUS):
        current = rr_dimension(n)
        jump = current - previous
        assert jump in (0, 1), (n, previous, current)
        if n > 0:
            if jump == 0:
                gaps.append(n)
            else:
                nongaps.add(n)
        previous = current

    assert len(gaps) == GENUS, (len(gaps), GENUS)
    assert rr_dimension(2 * GENUS - 1) == GENUS
    for n in range(2 * GENUS - 1, 2 * GENUS + 50):
        assert rr_dimension(n) == n + 1 - GENUS

    conductor = max(gaps) + 1
    # By definition of conductor, every n >= conductor is a non-gap.
    nongaps.update(range(conductor, 2 * conductor))
    minimal_generators = []
    for n in range(1, 2 * conductor):
        if n not in nongaps:
            continue
        if not any(a in nongaps and n - a in nongaps
                   for a in range(1, n)):
            minimal_generators.append(n)

    # Check that these generators reproduce the semigroup through 2c-1.
    generated = {0}
    for n in range(1, 2 * conductor):
        if any(g <= n and n - g in generated
               for g in minimal_generators):
            generated.add(n)
    assert generated == nongaps.intersection(range(0, 2 * conductor))

    print("BBGS E2 over GF(32): q=2, c=5, a=3, b=2")
    print(f"genus = {GENUS}")
    print(f"N_c = {NC}, N_b = {NB}")
    print(f"number of Weierstrass gaps = {len(gaps)}")
    print(f"conductor = {conductor}")
    print("minimal generators =", ", ".join(map(str, minimal_generators)))
    print("gaps =", ", ".join(map(str, gaps)))
    print("Riemann-Roch check: l((2g-1)P1) =", rr_dimension(2 * GENUS - 1))


if __name__ == "__main__":
    main()
