/*
 * Miura C_{3,4} curve: basic syndrome-matrix decoding demo over GF(64).
 *
 * Curve: y^3 = x(x-1)(x-alpha)(x-beta), alpha=2, beta=3
 * Field: GF(64) = GF(2)[z]/(z^6+z+1)
 * Pole orders at P_inf: -v(x)=3, -v(y)=4; genus g=3.
 *
 * B = {x^i y^j : 3i+4j <= 12, 0<=j<3} = L(12 P_inf).
 * The parity checks are evaluations of distinct products B*B.
 * The decoder builds S[a,b] = sum r(P) f_a(P) f_b(P), finds its
 * right kernel, and uses the common zeros to locate errors.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -Werror -o miura_basic miura_basic.c
 * Run:   ./miura_basic --errors 3 --seed 7
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 64
#define MAX_POINTS 64
#define MAX_ROWS 64
#define MAX_COLS 64
#define MAX_BASIS 16
#define MAX_ERRORS 9
#define FIELD_POLY 0x43u

typedef struct { uint8_t x, y; } Point;
typedef struct { uint8_t ix, iy; } Monomial;

static uint8_t gf_mul(uint8_t a, uint8_t b)
{
    uint8_t r = 0;
    while (b) {
        if (b & 1u) r ^= a;
        b >>= 1;
        a <<= 1;
        if (a & 0x40u) a ^= FIELD_POLY;
    }
    return (uint8_t)(r & 63u);
}

static uint8_t gf_pow(uint8_t a, unsigned n)
{
    uint8_t r = 1;
    while (n) {
        if (n & 1u) r = gf_mul(r, a);
        a = gf_mul(a, a);
        n >>= 1;
    }
    return r;
}

static uint8_t gf_inv(uint8_t a)
{
    return a ? gf_pow(a, 62) : 0;
}

static uint8_t eval_monomial(Point p, Monomial m)
{
    return gf_mul(gf_pow(p.x, m.ix), gf_pow(p.y, m.iy));
}

/* RREF over GF(64); pivots[] receives pivot columns. */
static int rref(uint8_t a[MAX_ROWS][MAX_COLS], int rows, int cols,
                int pivots[MAX_ROWS])
{
    int rank = 0;
    for (int col = 0; col < cols && rank < rows; ++col) {
        int pivot = rank;
        while (pivot < rows && a[pivot][col] == 0) ++pivot;
        if (pivot == rows) continue;

        if (pivot != rank) {
            for (int j = 0; j < cols; ++j) {
                uint8_t tmp = a[rank][j];
                a[rank][j] = a[pivot][j];
                a[pivot][j] = tmp;
            }
        }

        uint8_t scale = gf_inv(a[rank][col]);
        for (int j = 0; j < cols; ++j)
            a[rank][j] = gf_mul(a[rank][j], scale);

        for (int i = 0; i < rows; ++i) {
            if (i == rank || a[i][col] == 0) continue;
            uint8_t factor = a[i][col];
            for (int j = 0; j < cols; ++j)
                a[i][j] ^= gf_mul(factor, a[rank][j]);
        }
        pivots[rank++] = col;
    }
    return rank;
}

static int nullspace(const uint8_t input[MAX_ROWS][MAX_COLS],
                     int rows, int cols,
                     uint8_t basis[MAX_COLS][MAX_COLS])
{
    uint8_t a[MAX_ROWS][MAX_COLS] = {{0}};
    int pivots[MAX_ROWS] = {0};
    int is_pivot[MAX_COLS] = {0};

    for (int i = 0; i < rows; ++i)
        for (int j = 0; j < cols; ++j)
            a[i][j] = input[i][j];

    int rank = rref(a, rows, cols, pivots);
    for (int i = 0; i < rank; ++i) is_pivot[pivots[i]] = 1;

    int count = 0;
    for (int free_col = 0; free_col < cols; ++free_col) {
        if (is_pivot[free_col]) continue;
        memset(basis[count], 0, MAX_COLS);
        basis[count][free_col] = 1;
        for (int row = 0; row < rank; ++row)
            basis[count][pivots[row]] = a[row][free_col];
        ++count;
    }
    return count;
}

/* Solve A*x=s with possibly more equations than unknowns. */
static int solve_values(const uint8_t evals[MAX_BASIS][MAX_POINTS],
                        const uint8_t syndrome[MAX_BASIS][MAX_BASIS],
                        const uint8_t *positions, int nerr,
                        uint8_t *values, int basis_count)
{
    uint8_t aug[MAX_ROWS][MAX_COLS] = {{0}};
    int pivots[MAX_ROWS] = {0};

    for (int row = 0; row < basis_count; ++row) {
        for (int col = 0; col < nerr; ++col)
            aug[row][col] = evals[row][positions[col]];
        aug[row][nerr] = syndrome[row][0];
    }

    int rank = rref(aug, basis_count, nerr + 1, pivots);
    if (rank < nerr) return 0;
    for (int row = 0; row < rank; ++row)
        if (pivots[row] == nerr) return 0;

    for (int row = rank; row < basis_count; ++row)
        if (aug[row][nerr] != 0) return 0;

    for (int col = 0; col < nerr; ++col) values[col] = 0;
    for (int row = 0; row < rank; ++row)
        values[pivots[row]] = aug[row][nerr];
    return 1;
}

static uint64_t rng_state = UINT64_C(0x9e3779b97f4a7c15);
static uint32_t random_u32(void)
{
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return (uint32_t)(rng_state >> 16);
}

static int check_word(const uint8_t h[MAX_ROWS][MAX_POINTS],
                      int checks, int n, const uint8_t *word)
{
    for (int row = 0; row < checks; ++row) {
        uint8_t sum = 0;
        for (int p = 0; p < n; ++p)
            sum ^= gf_mul(h[row][p], word[p]);
        if (sum) return 0;
    }
    return 1;
}

static int parse_arg(const char *arg, const char *name, int *out)
{
    size_t n = strlen(name);
    if (strncmp(arg, name, n) != 0 || arg[n] != '=') return 0;
    char *end = NULL;
    long v = strtol(arg + n + 1, &end, 10);
    if (!end || *end || v < 0 || v > 1000000) return -1;
    *out = (int)v;
    return 1;
}

int main(int argc, char **argv)
{
    int errors = 3, seed = 7;
    for (int i = 1; i < argc; ++i) {
        int matched = parse_arg(argv[i], "--errors", &errors);
        if (!matched) matched = parse_arg(argv[i], "--seed", &seed);
        if (matched < 0) {
            fprintf(stderr, "Invalid option value: %s\n", argv[i]);
            return EXIT_FAILURE;
        }
        if (!matched) {
            fprintf(stderr, "Usage: %s [--errors=N] [--seed=N]\n", argv[0]);
            return EXIT_FAILURE;
        }
    }
    if (errors < 1 || errors > MAX_ERRORS) {
        fprintf(stderr, "errors must be between 1 and %d\n", MAX_ERRORS);
        return EXIT_FAILURE;
    }

    rng_state ^= (uint64_t)(unsigned)seed + UINT64_C(0x517cc1b727220a95);

    /* Curve: y^3 = x(x-1)(x-2)(x-3), with four distinct roots. */
    const uint8_t roots[4] = {0, 1, 2, 3};
    Point points[MAX_POINTS];
    int npoints = 0;
    for (int x = 0; x < Q; ++x) {
        uint8_t rhs = 1;
        for (int i = 0; i < 4; ++i) rhs = gf_mul(rhs, (uint8_t)(x ^ roots[i]));
        for (int y = 0; y < Q; ++y) {
            if (gf_pow((uint8_t)y, 3) == rhs) {
                if (npoints >= MAX_POINTS) {
                    fprintf(stderr, "Support exceeds configured capacity.\n");
                    return EXIT_FAILURE;
                }
                points[npoints++] = (Point){(uint8_t)x, (uint8_t)y};
            }
        }
    }
    if (npoints != 64) {
        fprintf(stderr, "Expected 64 affine rational points, got %d.\n", npoints);
        return EXIT_FAILURE;
    }

    /* B = L(12 P_inf), with pole orders ord(x)=-3 and ord(y)=-4. */
    Monomial basis[MAX_BASIS];
    int basis_count = 0;
    for (int j = 0; j < 3; ++j)
        for (int i = 0; 3 * i + 4 * j <= 12; ++i)
            basis[basis_count++] = (Monomial){(uint8_t)i, (uint8_t)j};

    uint8_t evals[MAX_BASIS][MAX_POINTS] = {{0}};
    for (int a = 0; a < basis_count; ++a)
        for (int p = 0; p < npoints; ++p)
            evals[a][p] = eval_monomial(points[p], basis[a]);

    /* Construct distinct products B*B as parity-check functions. */
    Monomial products[MAX_ROWS];
    int check_count = 0;
    for (int a = 0; a < basis_count; ++a) {
        for (int b = 0; b < basis_count; ++b) {
            Monomial m = {
                (uint8_t)(basis[a].ix + basis[b].ix),
                (uint8_t)(basis[a].iy + basis[b].iy)
            };
            int found = 0;
            for (int k = 0; k < check_count; ++k)
                if (products[k].ix == m.ix && products[k].iy == m.iy)
                    found = 1;
            if (!found) products[check_count++] = m;
        }
    }

    uint8_t h[MAX_ROWS][MAX_COLS] = {{0}};
    for (int row = 0; row < check_count; ++row)
        for (int p = 0; p < npoints; ++p)
            h[row][p] = eval_monomial(points[p], products[row]);

    uint8_t code_basis[MAX_COLS][MAX_COLS] = {{0}};
    int code_dimension = nullspace(h, check_count, npoints, code_basis);
    if (code_dimension <= 3) {
        fprintf(stderr, "Unexpected code dimension: %d\n", code_dimension);
        return EXIT_FAILURE;
    }

    /* Deterministic nonzero codeword in ker(H). */
    uint8_t codeword[MAX_POINTS] = {0};
    for (int p = 0; p < npoints; ++p)
        codeword[p] = code_basis[0][p]
                    ^ gf_mul(2, code_basis[1][p])
                    ^ gf_mul(7, code_basis[2][p]);
    if (!check_word(h, check_count, npoints, codeword)) {
        fprintf(stderr, "Generated codeword failed the parity checks.\n");
        return EXIT_FAILURE;
    }

    uint8_t received[MAX_POINTS];
    memcpy(received, codeword, sizeof(received));
    uint8_t injected_positions[MAX_ERRORS] = {0};
    uint8_t injected_values[MAX_ERRORS] = {0};
    int used[MAX_POINTS] = {0};
    for (int e = 0; e < errors; ++e) {
        int pos;
        do { pos = (int)(random_u32() % (uint32_t)npoints); } while (used[pos]);
        used[pos] = 1;
        injected_positions[e] = (uint8_t)pos;
        injected_values[e] = (uint8_t)(1 + random_u32() % 63u);
        received[pos] ^= injected_values[e];
    }

    /* Basic syndrome matrix S[a,b] = sum r(P) f_a(P) f_b(P). */
    uint8_t syndrome[MAX_ROWS][MAX_COLS] = {{0}};
    for (int a = 0; a < basis_count; ++a)
        for (int b = 0; b < basis_count; ++b)
            for (int p = 0; p < npoints; ++p)
                syndrome[a][b] ^= gf_mul(received[p],
                    gf_mul(evals[a][p], evals[b][p]));

    uint8_t syndrome_kernel[MAX_COLS][MAX_COLS] = {{0}};
    int kernel_dim = nullspace(syndrome, basis_count, basis_count, syndrome_kernel);

    /* The common zeros of kernel functions are the error positions. */
    uint8_t decoded_positions[MAX_ERRORS] = {0};
    int decoded_count = 0;
    for (int p = 0; p < npoints; ++p) {
        int common_zero = 1;
        for (int v = 0; v < kernel_dim && common_zero; ++v) {
            uint8_t value = 0;
            for (int a = 0; a < basis_count; ++a)
                value ^= gf_mul(syndrome_kernel[v][a], evals[a][p]);
            if (value) common_zero = 0;
        }
        if (common_zero) {
            if (decoded_count >= MAX_ERRORS) {
                fprintf(stderr, "Too many locator candidates.\n");
                return EXIT_FAILURE;
            }
            decoded_positions[decoded_count++] = (uint8_t)p;
        }
    }
    if (decoded_count != errors) {
        fprintf(stderr, "Locator returned %d candidates; expected %d.\n",
                decoded_count, errors);
        return EXIT_FAILURE;
    }

    uint8_t decoded_values[MAX_ERRORS] = {0};
    if (!solve_values(evals, syndrome, decoded_positions, decoded_count,
                      decoded_values, basis_count)) {
        fprintf(stderr, "Error-value system is singular or inconsistent.\n");
        return EXIT_FAILURE;
    }

    uint8_t corrected[MAX_POINTS];
    memcpy(corrected, received, sizeof(corrected));
    for (int e = 0; e < decoded_count; ++e)
        corrected[decoded_positions[e]] ^= decoded_values[e];

    if (memcmp(corrected, codeword, sizeof(codeword)) != 0 ||
        !check_word(h, check_count, npoints, corrected)) {
        fprintf(stderr, "Correction verification failed.\n");
        return EXIT_FAILURE;
    }

    puts("Miura C_{3,4} curve: basic syndrome-matrix decoding");
    puts("Curve: y^3 = x(x-1)(x-2)(x-3) over GF(64)");
    puts("Field polynomial: z^6 + z + 1");
    printf("Affine support: %d points\n", npoints);
    printf("Function basis size dim L(12P_inf): %d\n", basis_count);
    printf("Distinct product checks: %d\n", check_count);
    printf("Code dimension: %d\n", code_dimension);
    printf("Syndrome-kernel dimension: %d\n", kernel_dim);
    printf("Injected errors: %d (seed %d)\n", errors, seed);

    puts("Decoded errors (support index : (x,y) : value):");
    for (int e = 0; e < decoded_count; ++e) {
        Point p = points[decoded_positions[e]];
        printf("  %u : (%u,%u) : %u\n",
               decoded_positions[e], p.x, p.y, decoded_values[e]);
    }
    puts("PASS: original codeword recovered and all parity checks satisfied.");
    return EXIT_SUCCESS;
}
