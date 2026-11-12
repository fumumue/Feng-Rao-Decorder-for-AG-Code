/*
 * BBGS tower prototype: finite-field kernel for the first test case.
 * Field: GF(2^3) = GF(2)[a]/(a^3 + a + 1).
 * BBGS split: n = 3 = j + k = 1 + 2, q = 2.
 *
 * This file deliberately implements only the verified field layer.
 * The BBGS recursive relation, place normalization, and decoder are
 * separate stages and are not claimed to be implemented here.
 */
#include <stdio.h>
#include <string.h>

typedef unsigned char gf8;
#define GF8_MOD 0x0Bu /* a^3 + a + 1 */

static gf8 gf_add(gf8 x, gf8 y) { return (gf8)((x ^ y) & 7u); }

static gf8 gf_mul(gf8 x, gf8 y)
{
    gf8 r = 0;
    x &= 7u;
    y &= 7u;
    while (y) {
        if (y & 1u) r ^= x;
        y >>= 1;
        x <<= 1;
        if (x & 8u) x ^= GF8_MOD;
    }
    return (gf8)(r & 7u);
}

static gf8 gf_pow(gf8 x, unsigned e)
{
    gf8 r = 1;
    while (e) {
        if (e & 1u) r = gf_mul(r, x);
        x = gf_mul(x, x);
        e >>= 1;
    }
    return r;
}

static gf8 gf_inv(gf8 x) { return x ? gf_pow(x, 6u) : 0; }
static gf8 gf_frob2(gf8 x) { return gf_mul(x, x); }

/* Tr_a(x) = x + x^q + ... + x^(q^(a-1)), q=2. */
static gf8 gf_trace_a(gf8 x, unsigned a)
{
    gf8 sum = 0;
    unsigned i;
    for (i = 0; i < a; ++i) {
        sum = gf_add(sum, x);
        x = gf_frob2(x);
    }
    return sum;
}

static void print_elem(gf8 x)
{
    int first = 1;
    if (x == 0) { putchar('0'); return; }
    if (x & 1u) { printf("1"); first = 0; }
    if (x & 2u) { printf(first ? "a" : "+a"); first = 0; }
    if (x & 4u) { printf(first ? "a^2" : "+a^2"); }
}

static int self_test(void)
{
    unsigned x, y;
    for (x = 1; x < 8; ++x) {
        if (gf_mul((gf8)x, gf_inv((gf8)x)) != 1u) {
            fprintf(stderr, "inverse test failed at %u\n", x);
            return 1;
        }
    }
    for (x = 0; x < 8; ++x) {
        gf8 z = (gf8)x;
        for (y = 0; y < 3; ++y) z = gf_frob2(z);
        if (z != x) {
            fprintf(stderr, "Frobenius period test failed at %u\n", x);
            return 1;
        }
    }
    puts("GF(8) self-test: PASS");
    puts("  modulus: a^3 + a + 1");
    puts("  all 7 nonzero elements have verified inverses");
    puts("  Frobenius x -> x^2 has period dividing 3");
    return 0;
}

int main(int argc, char **argv)
{
    unsigned x;
    if (argc > 1 && strcmp(argv[1], "--self-test") == 0)
        return self_test();

    puts("BBGS prototype field layer");
    puts("  characteristic p = 2, q = 2, n = 3, j = 1, k = 2");
    puts("  K = GF(8) = GF(2)[a]/(a^3+a+1)");
    puts("  table: x | Tr_1(x) | Tr_2(x) | inverse(x)");
    for (x = 0; x < 8; ++x) {
        printf("  %u | ", x);
        print_elem(gf_trace_a((gf8)x, 1));
        printf(" | ");
        print_elem(gf_trace_a((gf8)x, 2));
        printf(" | ");
        if (x == 0) putchar('-'); else print_elem(gf_inv((gf8)x));
        putchar('\n');
    }
    puts("Note: curve points and decoding are not implemented in this stage.");
    return 0;
}
