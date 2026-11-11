/*
 * Suzuki curve over GF(2^12), with q = 8 and q0 = 2.
 *
 * Affine equation:
 *      y^q + y = x^q0 (x^q + x)
 *
 * The field GF(2^12) is represented in the polynomial basis modulo
 * X^12 + X^6 + X^4 + X + 1 (0x1053).
 *
 * This is a standalone point enumerator.  It does not depend on mp.c or
 * the Miura-curve implementation.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki suzuki.c
 * Run:   ./suzuki
 *
 * For q=8 the affine point count is 5888; including the unique point at
 * infinity, the Suzuki curve has 5889 rational points over GF(2^12).
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define FIELD_M 12
#define FIELD_SIZE (1u << FIELD_M)
#define FIELD_MASK (FIELD_SIZE - 1u)
#define FIELD_POLY 0x1053u

#define SUZUKI_Q 8u
#define SUZUKI_Q0 2u
#define MAX_FIBER 8u

typedef struct {
    uint16_t x;
    uint16_t y;
} Point;

static uint16_t gf_mul(uint16_t a, uint16_t b)
{
    uint16_t result = 0;

    while (b != 0) {
        if (b & 1u)
            result ^= a;
        b >>= 1;
        a <<= 1;
        if (a & FIELD_SIZE)
            a ^= FIELD_POLY;
    }
    return (uint16_t)(result & FIELD_MASK);
}

static uint16_t gf_pow(uint16_t a, unsigned int n)
{
    uint16_t result = 1;

    while (n != 0) {
        if (n & 1u)
            result = gf_mul(result, a);
        a = gf_mul(a, a);
        n >>= 1;
    }
    return result;
}

static uint16_t q_power(uint16_t a)
{
    return gf_pow(a, SUZUKI_Q);
}

int main(void)
{
    /*
     * The map L(y) = y^q + y is GF(q)-linear.  Build its fibers once,
     * then look up the at most eight y-values for each right-hand side.
     */
    static uint16_t fiber[FIELD_SIZE][MAX_FIBER];
    static uint8_t fiber_count[FIELD_SIZE];
    uint32_t affine_count = 0;

    for (uint32_t y = 0; y < FIELD_SIZE; ++y) {
        uint16_t value = (uint16_t)(q_power((uint16_t)y) ^ y);
        uint8_t n = fiber_count[value];

        if (n >= MAX_FIBER) {
            fprintf(stderr, "Unexpected fiber size at value %u\n", value);
            return EXIT_FAILURE;
        }
        fiber[value][n] = (uint16_t)y;
        fiber_count[value] = (uint8_t)(n + 1);
    }

    puts("# Suzuki curve: y^8 + y = x^2 (x^8 + x)");
    puts("# Field: GF(2^12), modulus X^12 + X^6 + X^4 + X + 1");
    puts("# Affine points (x,y), represented as polynomial-basis integers:");

    for (uint32_t x = 0; x < FIELD_SIZE; ++x) {
        uint16_t xq = q_power((uint16_t)x);
        uint16_t xq0 = gf_pow((uint16_t)x, SUZUKI_Q0);
        uint16_t rhs = gf_mul(xq0, (uint16_t)(xq ^ x));

        for (uint8_t j = 0; j < fiber_count[rhs]; ++j) {
            printf("%u,%u\n", x, fiber[rhs][j]);
            ++affine_count;
        }
    }

    printf("# Affine point count: %u\n", affine_count);
    printf("# Including the unique point at infinity: %u\n",
           affine_count + 1u);

    if (affine_count != 5888u) {
        fprintf(stderr, "Point-count check failed (expected 5888).\n");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
