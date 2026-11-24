
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>


#define MAXT 512
#define MAXP (2 * MAXT + 4)

typedef uint16_t fe;

static unsigned M, T;
static uint32_t MOD;
static uint32_t FMASK;
static uint64_t rng;

/* ---------------- Random ---------------- */

static uint64_t random64(void)
{
    rng += 0x9e3779b97f4a7c15ULL;
    uint64_t z = rng;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static fe randfe(void)
{
    return (fe)(random64() & FMASK);
}

/* ---------------- GF(2^m) ---------------- */

static fe add(fe a, fe b)
{
    return a ^ b;
}

static fe mul(fe a, fe b)
{
    uint32_t r = 0;
    uint32_t x = a;
    uint32_t y = b;
    uint32_t top = 1u << M;

    while (y) {
        if (y & 1)
            r ^= x;

        y >>= 1;
        x <<= 1;

        if (x & top)
            x ^= MOD;
    }

    return (fe)(r & FMASK);
}

static fe power(fe a, uint64_t n)
{
    fe r = 1;

    while (n) {
        if (n & 1)
            r = mul(r, a);

        a = mul(a, a);
        n >>= 1;
    }

    return r;
}

static fe inverse(fe a)
{
    return power(a, ((uint64_t)1 << M) - 2);
}

/* ---------------- Polynomial ---------------- */

typedef struct {
    fe c[MAXP];
} poly;

static void clear(poly *a)
{
    memset(a, 0, sizeof(*a));
}

static int degree(const poly *a, int limit)
{
    for (int i = limit; i >= 0; i--)
        if (a->c[i])
            return i;

    return -1;
}

/* Polynomial multiplication modulo monic f */
static void multiply_mod(
    poly *out,
    const poly *a,
    const poly *b,
    const poly *f)
{
    poly tmp;
    clear(&tmp);

    for (int i = 0; i < (int)T; i++)
        for (int j = 0; j < (int)T; j++)
            tmp.c[i+j] ^= mul(a->c[i], b->c[j]);

    for (int k = 2*(int)T-2; k >= (int)T; k--) {
        fe v = tmp.c[k];

        if (!v)
            continue;

        for (int j = 0; j < (int)T; j++)
            tmp.c[k-(int)T+j] ^=
                mul(v, f->c[j]);

        tmp.c[k] = 0;
    }

    clear(out);

    for (int i = 0; i < (int)T; i++)
        out->c[i] = tmp.c[i];
}

/* Raise polynomial to q-th power modulo f */
static void frobenius(poly *a, const poly *f)
{
    poly r = *a;
    poly tmp;

    for (unsigned i = 0; i < M; i++) {
        multiply_mod(&tmp, &r, &r, f);
        r = tmp;
    }

    *a = r;
}

/* Polynomial remainder */
static void remainder(poly *a, const poly *b)
{
    int db = degree(b, MAXP-1);

    if (db < 0)
        return;

    int da;

    while ((da = degree(a, MAXP-1)) >= db) {
        fe v = mul(a->c[da], inverse(b->c[db]));
        int shift = da - db;

        for (int j = 0; j <= db; j++)
            a->c[j+shift] ^=
                mul(v, b->c[j]);
    }
}

/* Polynomial GCD */
static int gcd_is_one(poly a, poly b)
{
    while (degree(&b, MAXP-1) >= 0) {
        poly r = a;
        remainder(&r, &b);
        a = b;
        b = r;
    }

    int d = degree(&a, MAXP-1);

    return d == 0 && a.c[0] != 0;
}

/* ---------------- Irreducibility ---------------- */

static int is_irreducible(const poly *f)
{
    poly x, h, d;

    clear(&x);
    x.c[1] = 1;

    h = x;

    /* Prime divisors of T */
    unsigned n = T;

    for (unsigned p = 2; p*p <= n; p++) {
        if (n % p)
            continue;

        unsigned steps = T / p;

        for (unsigned i = 0; i < steps; i++)
            frobenius(&h, f);

        d = h;
        d.c[1] ^= 1;

        if (!gcd_is_one(d, *f))
            return 0;

        h = x;

        while (n % p == 0)
            n /= p;
    }

    if (n > 1) {
        unsigned steps = T / n;

        for (unsigned i = 0; i < steps; i++)
            frobenius(&h, f);

        d = h;
        d.c[1] ^= 1;

        if (!gcd_is_one(d, *f))
            return 0;

        h = x;
    }

    /* Final condition: X^(q^T) = X */
    for (unsigned i = 0; i < T; i++)
        frobenius(&h, f);

    return memcmp(h.c, x.c, sizeof(h.c)) == 0;
}

/* ---------------- Generate Goppa polynomial ---------------- */

static int generate(poly *g, uint64_t *attempts)
{
    for (uint64_t k = 1; k <= 1000000; k++) {
        clear(g);

        for (unsigned i = 0; i < T; i++)
            g->c[i] = randfe();

        /* Monic polynomial */
        g->c[T] = 1;

        /* Avoid zero constant coefficient */
        if (!g->c[0])
            continue;

        (*attempts)++;

        if (is_irreducible(g))
            return 1;
    }

    return 0;
}

/* ---------------- Main ---------------- */

int main(void)
{
    unsigned m, t;
    unsigned long long seed;
    unsigned poly_input;

    printf("Base field degree m [13]: ");
    if (scanf("%u", &m) != 1)
        return 1;

    printf("Binary field polynomial (hex, e.g. 201b): ");
    if (scanf("%x", &poly_input) != 1)
        return 1;

    printf("Goppa polynomial degree t: ");
    if (scanf("%u", &t) != 1)
        return 1;

    printf("Random seed (0 = automatic): ");
    if (scanf("%llu", &seed) != 1)
        return 1;

    if (m < 2 || m > 13 || t < 1 || t > MAXT) {
        printf("Invalid parameters.\n");
        return 1;
    }

    M = m;
    T = t;
    MOD = poly_input;
    FMASK = (1u << M) - 1;

    if ((MOD >> M) != 1 || !(MOD & 1)) {
        printf("Invalid field polynomial format.\n");
        return 1;
    }

    if (!seed)
        seed = (uint64_t)time(NULL);

    rng = seed;

    printf("\nGF(2^%u) = GF(%u)\n", M, 1u << M);
    printf("Goppa degree: %u\n", T);
    printf("Seed: %llu\n\n", seed);

    poly g;
    uint64_t attempts = 0;

    clock_t start = clock();

    if (!generate(&g, &attempts)) {
        printf("Generation failed: attempt limit reached.\n");
        return 1;
    }

    double elapsed =
        (double)(clock() - start) / CLOCKS_PER_SEC;

    printf("Goppa polynomial generated!\n\n");

    printf("g(x) = x^%u", T);

    for (int i = (int)T-1; i >= 0; i--)
        printf(" + (%04x)x^%d", g.c[i], i);

    printf("\n\n");
    printf("Irreducible: YES\n");
    printf("Attempts: %llu\n", attempts);
    printf("Time: %.6f seconds\n", elapsed);

    return 0;
}
