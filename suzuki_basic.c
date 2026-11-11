/*
 * Multi-point AG-code / basic syndrome-matrix decoding demo
 * on the Suzuki curve over GF(2^6).
 *
 * Curve: y^8 + y = x^10 + x^3 = x^2 (x^8 + x)
 * Field: GF(64) = GF(2)[X]/(X^6 + X + 1)
 *
 * The 64 affine rational points are used as the evaluation support.
 * B = {x^i y^j : 8i + 10j <= 24, 0 <= j < 8}.
 * The parity-check space is spanned by pairwise products B*B, and
 * the code is its evaluation dual (the kernel of that check matrix).
 *
 * The decoder forms S[a,b] = sum r(P) f_a(P) f_b(P), finds the
 * nullspace, and tests its common zeros on the support. Error values
 * are then recovered from the first syndrome column.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki_basic suzuki_basic.c
 * Run:   ./suzuki_basic
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FIELD_SIZE 64
#define FIELD_MASK 63
#define FIELD_POLY 0x43u       /* X^6 + X + 1 */
#define MAX_POINTS 64
#define MAX_BASIS 16
#define MAX_CHECKS 64
#define ERROR_COUNT 3

typedef struct {
    uint8_t x;
    uint8_t y;
} Point;

typedef struct {
    uint8_t x_exp;
    uint8_t y_exp;
} Monomial;

static uint8_t gf_mul(uint8_t a, uint8_t b)
{
    uint8_t result = 0;

    while (b != 0) {
        if (b & 1u)
            result ^= a;
        b >>= 1;
        a <<= 1;
        if (a & 0x40u)
            a ^= FIELD_POLY;
    }
    return (uint8_t)(result & FIELD_MASK);
}

static uint8_t gf_pow(uint8_t a, unsigned int n)
{
    uint8_t result = 1;

    while (n != 0) {
        if (n & 1u)
            result = gf_mul(result, a);
        a = gf_mul(a, a);
        n >>= 1;
    }
    return result;
}

static uint8_t gf_inv(uint8_t a)
{
    return a == 0 ? 0 : gf_pow(a, 62);
}

static uint8_t eval_monomial(Point p, Monomial m)
{
    return gf_mul(gf_pow(p.x, m.x_exp), gf_pow(p.y, m.y_exp));
}

static int same_monomial(Monomial a, Monomial b)
{
    return a.x_exp == b.x_exp && a.y_exp == b.y_exp;
}

/* Reduced row echelon form over GF(64). Returns the rank. */
static int rref(uint8_t a[MAX_CHECKS][MAX_POINTS],
                int rows, int cols, int pivots[MAX_CHECKS])
{
    int rank = 0;

    for (int col = 0; col < cols && rank < rows; ++col) {
        int pivot = rank;

        while (pivot < rows && a[pivot][col] == 0)
            ++pivot;
        if (pivot == rows)
            continue;

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
            if (i == rank || a[i][col] == 0)
                continue;
            uint8_t factor = a[i][col];
            for (int j = 0; j < cols; ++j)
                a[i][j] ^= gf_mul(factor, a[rank][j]);
        }

        pivots[rank] = col;
        ++rank;
    }

    return rank;
}

/*
 * Return a basis of the right nullspace.
 * basis[k][j] is coordinate j of nullspace vector k.
 */
static int nullspace(const uint8_t input[MAX_CHECKS][MAX_POINTS],
                     int rows, int cols,
                     uint8_t basis[MAX_POINTS][MAX_POINTS])
{
    uint8_t a[MAX_CHECKS][MAX_POINTS] = {{0}};
    int pivots[MAX_CHECKS] = {0};
    int is_pivot[MAX_POINTS] = {0};
    int rank;

    for (int i = 0; i < rows; ++i)
        for (int j = 0; j < cols; ++j)
            a[i][j] = input[i][j];

    rank = rref(a, rows, cols, pivots);
    for (int i = 0; i < rank; ++i)
        is_pivot[pivots[i]] = 1;

    int count = 0;
    for (int free_col = 0; free_col < cols; ++free_col) {
        if (is_pivot[free_col])
            continue;

        memset(basis[count], 0, MAX_POINTS);
        basis[count][free_col] = 1;

        for (int row = 0; row < rank; ++row)
            basis[count][pivots[row]] = a[row][free_col];

        ++count;
    }

    return count;
}

static uint8_t dot_product(const uint8_t *a, const uint8_t *b, int n)
{
    uint8_t sum = 0;
    for (int i = 0; i < n; ++i)
        sum ^= gf_mul(a[i], b[i]);
    return sum;
}

static int check_word(const uint8_t h[MAX_CHECKS][MAX_POINTS],
                      int checks, int n, const uint8_t *word)
{
    for (int row = 0; row < checks; ++row) {
        if (dot_product(h[row], word, n) != 0)
            return 0;
    }
    return 1;
}

int main(void)
{
    Point points[MAX_POINTS];
    int point_count = 0;
    Monomial basis[MAX_BASIS];
    int basis_count = 0;
    Monomial checks_monomials[MAX_CHECKS];
    int check_count = 0;
    uint8_t h[MAX_CHECKS][MAX_POINTS] = {{0}};
    uint8_t code_nullspace[MAX_POINTS][MAX_POINTS] = {{0}};
    uint8_t codeword[MAX_POINTS] = {0};
    uint8_t received[MAX_POINTS] = {0};
    uint8_t evals[MAX_BASIS][MAX_POINTS] = {{0}};
    uint8_t syndrome[MAX_CHECKS][MAX_POINTS] = {{0}};
    uint8_t syndrome_nullspace[MAX_POINTS][MAX_POINTS] = {{0}};
    uint8_t error_positions[ERROR_COUNT] = {5, 23, 51};
    uint8_t injected_values[ERROR_COUNT] = {7, 11, 29};
    uint8_t decoded_values[ERROR_COUNT] = {0};

    /* Enumerate all affine points on y^8+y=x^2(x^8+x). */
    for (int x = 0; x < FIELD_SIZE; ++x) {
        uint8_t xq = gf_pow((uint8_t)x, 8);
        uint8_t rhs = gf_mul(gf_pow((uint8_t)x, 2), (uint8_t)(xq ^ x));

        for (int y = 0; y < FIELD_SIZE; ++y) {
            uint8_t lhs = (uint8_t)(gf_pow((uint8_t)y, 8) ^ y);
            if (lhs == rhs) {
                if (point_count >= MAX_POINTS) {
                    fprintf(stderr, "Too many affine points.\n");
                    return EXIT_FAILURE;
                }
                points[point_count++] = (Point){(uint8_t)x, (uint8_t)y};
            }
        }
    }

    if (point_count != 64) {
        fprintf(stderr, "Expected 64 affine points, found %d.\n", point_count);
        return EXIT_FAILURE;
    }

    /*
     * Suzuki curve pole orders: ord_inf(x)=-8, ord_inf(y)=-10.
     * Use the monomial basis 8*i + 10*j <= 24, j < 8.
     */
    for (int j = 0; j < 8; ++j) {
        for (int i = 0; 8 * i + 10 * j <= 24; ++i) {
            if (basis_count >= MAX_BASIS) {
                fprintf(stderr, "Basis capacity exceeded.\n");
                return EXIT_FAILURE;
            }
            basis[basis_count++] = (Monomial){(uint8_t)i, (uint8_t)j};
        }
    }

    /* Build the distinct products B*B as parity-check monomials. */
    for (int a = 0; a < basis_count; ++a) {
        for (int b = 0; b < basis_count; ++b) {
            Monomial m = {
                (uint8_t)(basis[a].x_exp + basis[b].x_exp),
                (uint8_t)(basis[a].y_exp + basis[b].y_exp)
            };
            int found = 0;

            for (int k = 0; k < check_count; ++k) {
                if (same_monomial(checks_monomials[k], m)) {
                    found = 1;
                    break;
                }
            }
            if (!found) {
                if (check_count >= MAX_CHECKS) {
                    fprintf(stderr, "Check-space capacity exceeded.\n");
                    return EXIT_FAILURE;
                }
                checks_monomials[check_count++] = m;
            }
        }
    }

    /* Evaluation table for the decoding basis. */
    for (int a = 0; a < basis_count; ++a)
        for (int p = 0; p < point_count; ++p)
            evals[a][p] = eval_monomial(points[p], basis[a]);

    /* Parity-check matrix H: evaluate every product monomial at all points. */
    for (int row = 0; row < check_count; ++row) {
        for (int p = 0; p < point_count; ++p)
            h[row][p] = eval_monomial(points[p], checks_monomials[row]);
    }

    int code_dimension = nullspace(h, check_count, point_count, code_nullspace);
    int check_rank = point_count - code_dimension;

    if (code_dimension < 3) {
        fprintf(stderr, "Unexpectedly small code dimension.\n");
        return EXIT_FAILURE;
    }

    /* Make a deterministic, nonzero codeword from three nullspace vectors. */
    for (int p = 0; p < point_count; ++p) {
        codeword[p] = code_nullspace[0][p]
                    ^ gf_mul(2, code_nullspace[1][p])
                    ^ gf_mul(7, code_nullspace[2][p]);
    }

    int nonzero_codeword = 0;
    for (int p = 0; p < point_count; ++p)
        nonzero_codeword |= (codeword[p] != 0);

    if (!nonzero_codeword || !check_word(h, check_count, point_count, codeword)) {
        fprintf(stderr, "Codeword construction failed.\n");
        return EXIT_FAILURE;
    }

    memcpy(received, codeword, sizeof(received));

    /* Inject three known errors at three distinct support positions. */
    for (int e = 0; e < ERROR_COUNT; ++e)
        received[error_positions[e]] ^= injected_values[e];

    /*
     * Basic syndrome matrix:
     * S[a,b] = sum_P received(P) * f_a(P) * f_b(P).
     * Since every f_a*f_b is a parity check, the codeword part vanishes.
     */
    for (int a = 0; a < basis_count; ++a) {
        for (int b = 0; b < basis_count; ++b) {
            uint8_t sum = 0;
            for (int p = 0; p < point_count; ++p) {
                uint8_t product = gf_mul(evals[a][p], evals[b][p]);
                sum ^= gf_mul(received[p], product);
            }
            syndrome[a][b] = sum;
        }
    }

    /* Compute the right kernel of the syndrome matrix. */
    int syndrome_kernel_dim = nullspace(
        syndrome, basis_count, basis_count, syndrome_nullspace);
    int syndrome_rank = basis_count - syndrome_kernel_dim;

    /* The common zeros of all kernel functions identify error locations. */
    uint8_t decoded_positions[ERROR_COUNT] = {0};
    int decoded_count = 0;

    for (int p = 0; p < point_count; ++p) {
        int common_zero = 1;

        for (int v = 0; v < syndrome_kernel_dim; ++v) {
            uint8_t value = 0;
            for (int a = 0; a < basis_count; ++a)
                value ^= gf_mul(syndrome_nullspace[v][a], evals[a][p]);
            if (value != 0) {
                common_zero = 0;
                break;
            }
        }

        if (common_zero) {
            if (decoded_count >= ERROR_COUNT) {
                fprintf(stderr, "More error candidates than expected.\n");
                return EXIT_FAILURE;
            }
            decoded_positions[decoded_count++] = (uint8_t)p;
        }
    }

    if (decoded_count != ERROR_COUNT) {
        fprintf(stderr, "Locator found %d candidates; expected %d.\n",
                decoded_count, ERROR_COUNT);
        return EXIT_FAILURE;
    }

    /*
     * Recover error values from S[a,0] = sum e(P) f_a(P),
     * because basis[0] is the constant function 1.
     */
    uint8_t augmented[MAX_CHECKS][MAX_POINTS] = {{0}};
    for (int row = 0; row < ERROR_COUNT; ++row) {
        for (int col = 0; col < ERROR_COUNT; ++col)
            augmented[row][col] = evals[row][decoded_positions[col]];
        augmented[row][ERROR_COUNT] = syndrome[row][0];
    }

    int value_pivots[MAX_CHECKS] = {0};
    int value_rank = rref(augmented, ERROR_COUNT, ERROR_COUNT + 1,
                          value_pivots);

    if (value_rank != ERROR_COUNT ||
        value_pivots[0] != 0 ||
        value_pivots[1] != 1 ||
        value_pivots[2] != 2) {
        fprintf(stderr, "Error-value system is singular.\n");
        return EXIT_FAILURE;
    }

    for (int e = 0; e < ERROR_COUNT; ++e)
        decoded_values[e] = augmented[e][ERROR_COUNT];

    /* Correct and verify the received word. */
    uint8_t corrected[MAX_POINTS];
    memcpy(corrected, received, sizeof(corrected));
    for (int e = 0; e < ERROR_COUNT; ++e)
        corrected[decoded_positions[e]] ^= decoded_values[e];

    if (memcmp(corrected, codeword, sizeof(codeword)) != 0 ||
        !check_word(h, check_count, point_count, corrected)) {
        fprintf(stderr, "Correction verification failed.\n");
        return EXIT_FAILURE;
    }

    puts("Suzuki curve multi-point basic decoding demo");
    puts("Curve: y^8 + y = x^10 + x^3 over GF(64)");
    puts("Field polynomial: X^6 + X + 1");
    printf("Affine support points: %d\n", point_count);
    printf("Function basis size: %d\n", basis_count);
    printf("Distinct product checks: %d\n", check_count);
    printf("Check-matrix rank: %d\n", check_rank);
    printf("Code dimension: %d\n", code_dimension);
    printf("Syndrome-matrix rank: %d\n", syndrome_rank);
    printf("Syndrome-kernel dimension: %d\n", syndrome_kernel_dim);

    puts("\nInjected errors (support index : (x,y) : value):");
    for (int e = 0; e < ERROR_COUNT; ++e) {
        Point p = points[error_positions[e]];
        printf("  %u : (%u,%u) : %u\n",
               error_positions[e], p.x, p.y, injected_values[e]);
    }

    puts("\nDecoded errors:");
    for (int e = 0; e < decoded_count; ++e) {
        Point p = points[decoded_positions[e]];
        printf("  %u : (%u,%u) : %u\n",
               decoded_positions[e], p.x, p.y, decoded_values[e]);
    }

    puts("\nResult: PASS (all three errors corrected; codeword recovered)");
    return EXIT_SUCCESS;
}
