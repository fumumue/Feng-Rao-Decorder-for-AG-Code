/*
 * BBGS E2 rational-place enumerator over GF(8).
 *
 * Reference tower parameters:
 *   p=q=2, n=3, j=1, k=2, gcd(j,k)=1.
 *   Tr_j(y / x^(q^k)) + Tr_k(y^(q^j) / x) = 1.
 *
 * The first stage is E1=GF(8)(x), E2=E1(y).
 * We enumerate the 28 rational places above x=beta != 0.
 * This is not yet an RR-basis generator or a decoder.
 */
#include <stdio.h>
#include <string.h>

typedef unsigned char gf8;
#define GF8_MOD 0x0Bu /* a^3 + a + 1 */

static gf8 add(gf8 x, gf8 y) { return (gf8)((x ^ y) & 7u); }

static gf8 mul(gf8 x, gf8 y)
{
    gf8 r = 0;
    x &= 7u; y &= 7u;
    while (y) {
        if (y & 1u) r ^= x;
        y >>= 1;
        x <<= 1;
        if (x & 8u) x ^= GF8_MOD;
    }
    return (gf8)(r & 7u);
}

static gf8 power(gf8 x, unsigned e)
{
    gf8 r = 1;
    while (e) {
        if (e & 1u) r = mul(r, x);
        x = mul(x, x);
        e >>= 1;
    }
    return r;
}

static gf8 inverse(gf8 x) { return x ? power(x, 6u) : 0; }

static gf8 trace_q(gf8 x, unsigned a)
{
    gf8 s = 0;
    unsigned i;
    for (i = 0; i < a; ++i) {
        s = add(s, x);
        x = mul(x, x); /* q-Frobenius, q=2 */
    }
    return s;
}

static gf8 div_nonzero(gf8 a, gf8 b)
{
    return mul(a, inverse(b));
}

/* BBGS defining equation for q=2, j=1, k=2. */
static gf8 bbgs_lhs(gf8 x, gf8 y)
{
    gf8 first = div_nonzero(y, power(x, 4u));
    gf8 second = div_nonzero(power(y, 2u), x);
    return add(trace_q(first, 1u), trace_q(second, 2u));
}

static int enumerate_points(int print_points)
{
    unsigned x, y, count = 0;
    unsigned per_x[8] = {0};

    for (x = 1; x < 8; ++x) {
        for (y = 0; y < 8; ++y) {
            if (bbgs_lhs((gf8)x, (gf8)y) == 1u) {
                ++count;
                ++per_x[x];
                if (print_points)
                    printf("  P%02u: x=%u, y=%u\n", count, x, y);
            }
        }
    }

    printf("Rational places above x in GF(8)^*: %u\n", count);
    for (x = 1; x < 8; ++x) {
        printf("  x=%u: %u points\n", x, per_x[x]);
        if (per_x[x] != 4u) {
            fprintf(stderr, "split-count check failed for x=%u\n", x);
            return 1;
        }
    }
    return count == 28u ? 0 : 1;
}

static int self_test(void)
{
    unsigned x;
    for (x = 1; x < 8; ++x)
        if (mul((gf8)x, inverse((gf8)x)) != 1u) return 1;

    puts("GF(8) arithmetic: PASS");
    if (enumerate_points(0)) return 1;
    puts("BBGS E2 splitting test: PASS (7 fibers x 4 points = 28)");
    puts("Theoretical genus from BBGS Corollary 2.7: g(E2)=6");
    puts("One-point divisor choice: G=11Q, deg(G)=11, n=28");
    puts("Riemann-Roch dimension: l(11Q)=11+1-6=6");
    puts("Designed distance lower bound: d >= 28-11=17");
    puts("Guaranteed unique-decoding radius from this bound: t=8");
    puts("Note: explicit RR basis and Feng-Rao order are not yet implemented.");
    return 0;
}

int main(int argc, char **argv)
{
    if (argc > 1 && strcmp(argv[1], "--self-test") == 0)
        return self_test();

    puts("BBGS tower E2 over GF(8)");
    puts("p=q=2, n=3, j=1, k=2");
    puts("Equation: Tr_1(y/x^4) + Tr_2(y^2/x) = 1");
    puts("GF(8)=GF(2)[a]/(a^3+a+1), element bits encode 1,a,a^2");
    puts("Enumerating rational places above x != 0:");
    if (enumerate_points(1)) return 1;
    puts("Genus: g=6 (BBGS Corollary 2.7)");
    puts("Chosen one-point parameters: n=28, m=11, k_RR=6, d>=17, t=8");
    puts("RR basis construction and Feng-Rao decoding remain future stages.");
    return 0;
}
