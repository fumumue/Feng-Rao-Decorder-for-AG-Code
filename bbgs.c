
/*
 * BBGS seven-term curve: evaluation-code / ECP decoder
 *
 * Field:
 *   GF(64) = GF(2)[T] / (T^6 + T + 1)
 *   primitive polynomial = 0x43
 *
 * Curve terms:
 *   {x exponent, y exponent, z exponent, coefficient}
 *
 * The supplied seven terms have z exponent 0.
 * Therefore the affine equation is F(x,y)=0.
 *
 * Code construction:
 *   A = span of independent evaluations of x^i y^j, i+j <= da
 *   B = span of independent evaluations of x^i y^j, i+j <= db
 *   H = span of coordinatewise products A_i * B_j
 *   C = H^perp
 *
 * Decoder:
 *   S_ij = sum_P r(P) A_i(P) B_j(P)
 *   Compute the right kernel of S^T.
 *   Find common zeros of kernel functions on evaluation points.
 *   Solve for error values and verify the corrected word.
 *
 * Build:
 *   cc -O2 -std=c11 -Wall -Wextra bbgs_ecp64.c -o bbgs_ecp64
 *
 * Run:
 *   ./bbgs_ecp64 --da 8 --db 8 --errors 30 --trials 100 --seed 7
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 64
#define FIELD_POLY 0x43u
#define NTERMS 7
#define MAX_MONOMIALS 512

typedef uint8_t GF;

/*
 * Explicit curve definition.
 *
 * Each row:
 *   {x degree, y degree, z degree, coefficient}
 */
static const unsigned short BBGS_EQUATION[NTERMS][4] = {
    {31,  8, 0, 1},
    {30, 16, 0, 1},
    {28, 32, 0, 1},
    {24,  1, 0, 1},
    {16,  2, 0, 1},
    { 0,  4, 0, 1},
    {32,  0, 0, 1}
};

/* ============================================================
 * GF(64)
 * ============================================================ */

static GF expt[2 * (Q - 1)];
static int logt[Q];

static GF gf_mul_slow(GF a, GF b)
{
    unsigned aa = a;
    unsigned bb = b;
    unsigned r = 0;

    while (bb) {
        if (bb & 1u)
            r ^= aa;

        bb >>= 1;
        aa <<= 1;

        if (aa & Q)
            aa ^= FIELD_POLY;
    }

    return (GF)(r & (Q - 1));
}

static int gf_init(void)
{
    GF x = 1;

    for (int i = 0; i < Q; ++i)
        logt[i] = -1;

    for (int i = 0; i < Q - 1; ++i) {
        if (x == 0 || logt[x] >= 0)
            return 0;

        expt[i] = x;
        logt[x] = i;
        x = gf_mul_slow(x, 2);
    }

    if (x != 1)
        return 0;

    for (int i = Q - 1; i < 2 * (Q - 1); ++i)
        expt[i] = expt[i - (Q - 1)];

    return 1;
}

static inline GF gf_mul(GF a, GF b)
{
    if (!a || !b)
        return 0;

    return expt[logt[a] + logt[b]];
}

static inline GF gf_inv(GF a)
{
    if (!a)
        return 0;

    return expt[(Q - 1) - logt[a]];
}

static GF gf_pow(GF a, unsigned n)
{
    if (n == 0)
        return 1;

    if (!a)
        return 0;

    return expt[
        ((unsigned)logt[a] * (n % (Q - 1))) % (Q - 1)
    ];
}

/* ============================================================
 * Curve and affine rational points
 * ============================================================ */

typedef struct {
    GF x;
    GF y;
} Point;

static Point *D = NULL;
static int nD = 0;

static GF eval_curve(GF x, GF y)
{
    GF f = 0;

    for (int i = 0; i < NTERMS; ++i) {
        const unsigned short *t = BBGS_EQUATION[i];

        if (t[2] != 0) {
            fprintf(stderr,
                    "This adapter currently expects z-degree 0.\n");
            exit(EXIT_FAILURE);
        }

        GF v = (GF)t[3];

        v = gf_mul(v, gf_pow(x, t[0]));
        v = gf_mul(v, gf_pow(y, t[1]));

        f ^= v;
    }

    return f;
}

static int enumerate_points(void)
{
    D = malloc((size_t)Q * Q * sizeof(*D));

    if (!D)
        return 0;

    nD = 0;

    for (int x = 0; x < Q; ++x) {
        for (int y = 0; y < Q; ++y) {
            if (eval_curve((GF)x, (GF)y) == 0) {
                D[nD++] = (Point){(GF)x, (GF)y};
            }
        }
    }

    return nD;
}

/* ============================================================
 * Linear algebra over GF(64)
 * ============================================================ */

/* Reduced row echelon form. */
static int rref(GF *m, int rows, int cols, int *piv)
{
    int rank = 0;

    for (int col = 0; col < cols && rank < rows; ++col) {
        int p = rank;

        while (p < rows &&
               m[(size_t)p * cols + col] == 0)
            ++p;

        if (p == rows)
            continue;

        if (p != rank) {
            for (int j = 0; j < cols; ++j) {
                GF t = m[(size_t)rank * cols + j];

                m[(size_t)rank * cols + j] =
                    m[(size_t)p * cols + j];

                m[(size_t)p * cols + j] = t;
            }
        }

        GF s = gf_inv(m[(size_t)rank * cols + col]);

        for (int j = 0; j < cols; ++j) {
            m[(size_t)rank * cols + j] =
                gf_mul(m[(size_t)rank * cols + j], s);
        }

        for (int i = 0; i < rows; ++i) {
            if (i == rank)
                continue;

            GF f = m[(size_t)i * cols + col];

            if (!f)
                continue;

            for (int j = 0; j < cols; ++j) {
                m[(size_t)i * cols + j] ^=
                    gf_mul(f, m[(size_t)rank * cols + j]);
            }
        }

        piv[rank++] = col;
    }

    return rank;
}

/* ============================================================
 * Row space
 * ============================================================ */

typedef struct {
    int nrows;
    int ncols;
    int cap;

    GF *echelon;
    GF *raw;
    int *piv;
} RowSpace;

static int rs_init(RowSpace *s, int cap, int ncols)
{
    memset(s, 0, sizeof(*s));

    s->cap = cap;
    s->ncols = ncols;

    s->echelon = calloc((size_t)cap * ncols, 1);
    s->raw = calloc((size_t)cap * ncols, 1);
    s->piv = malloc((size_t)cap * sizeof(int));

    return s->echelon && s->raw && s->piv;
}

static int rs_add(RowSpace *s, const GF *v)
{
    GF *w = malloc((size_t)s->ncols);

    if (!w)
        return -1;

    memcpy(w, v, (size_t)s->ncols);

    for (int r = 0; r < s->nrows; ++r) {
        GF f = w[s->piv[r]];

        if (!f)
            continue;

        const GF *e =
            s->echelon + (size_t)r * s->ncols;

        for (int j = 0; j < s->ncols; ++j)
            w[j] ^= gf_mul(f, e[j]);
    }

    int p = 0;

    while (p < s->ncols && !w[p])
        ++p;

    if (p == s->ncols) {
        free(w);
        return 0;
    }

    if (s->nrows >= s->cap) {
        free(w);
        return -1;
    }

    GF inv = gf_inv(w[p]);

    GF *e =
        s->echelon + (size_t)s->nrows * s->ncols;

    for (int j = 0; j < s->ncols; ++j)
        e[j] = gf_mul(w[j], inv);

    memcpy(
        s->raw + (size_t)s->nrows * s->ncols,
        v,
        (size_t)s->ncols
    );

    s->piv[s->nrows++] = p;

    free(w);
    return 1;
}

static void rs_free(RowSpace *s)
{
    free(s->echelon);
    free(s->raw);
    free(s->piv);

    memset(s, 0, sizeof(*s));
}

/* ============================================================
 * Evaluation bases
 * ============================================================ */

typedef struct {
    int count;

    GF *v;       /* count x nD evaluation matrix */

    int *ex;
    int *ey;
} EvalBasis;

/*
 * Build an independent evaluation basis from monomials x^i y^j
 * with total degree <= degree.
 *
 * This is an evaluation-space basis, not yet a proven
 * Riemann-Roch basis ordered by pole order.
 */
static int build_monomial_basis(int degree, EvalBasis *out)
{
    int cap = (degree + 1) * (degree + 2) / 2;

    if (cap > MAX_MONOMIALS)
        return 0;

    RowSpace rs;

    if (!rs_init(&rs, cap, nD))
        return 0;

    out->v = calloc((size_t)cap * nD, 1);
    out->ex = malloc((size_t)cap * sizeof(int));
    out->ey = malloc((size_t)cap * sizeof(int));

    if (!out->v || !out->ex || !out->ey) {
        rs_free(&rs);
        return 0;
    }

    out->count = 0;

    GF *v = malloc((size_t)nD);

    if (!v) {
        rs_free(&rs);
        return 0;
    }

    for (int d = 0; d <= degree; ++d) {
        for (int j = 0; j <= d; ++j) {
            int i = d - j;

            for (int p = 0; p < nD; ++p) {
                v[p] = gf_mul(
                    gf_pow(D[p].x, (unsigned)i),
                    gf_pow(D[p].y, (unsigned)j)
                );
            }

            int added = rs_add(&rs, v);

            if (added < 0) {
                free(v);
                rs_free(&rs);
                return 0;
            }

            if (added) {
                int k = out->count++;

                memcpy(
                    out->v + (size_t)k * nD,
                    v,
                    (size_t)nD
                );

                out->ex[k] = i;
                out->ey[k] = j;
            }
        }
    }

    free(v);
    rs_free(&rs);

    return 1;
}

/*
 * Construct H = span{ A_i * B_j }.
 * Products are coordinatewise products of evaluation vectors.
 */
static int build_product_basis(
    const EvalBasis *A,
    const EvalBasis *B,
    EvalBasis *H)
{
    RowSpace rs;

    if (!rs_init(&rs, nD, nD))
        return 0;

    GF *v = malloc((size_t)nD);

    if (!v) {
        rs_free(&rs);
        return 0;
    }

    for (int i = 0; i < A->count; ++i) {
        for (int j = 0; j < B->count; ++j) {
            for (int p = 0; p < nD; ++p) {
                v[p] = gf_mul(
                    A->v[(size_t)i * nD + p],
                    B->v[(size_t)j * nD + p]
                );
            }

            int added = rs_add(&rs, v);

            if (added < 0) {
                free(v);
                rs_free(&rs);
                return 0;
            }
        }
    }

    H->count = rs.nrows;
    H->v = rs.raw;
    H->ex = NULL;
    H->ey = NULL;

    rs.raw = NULL;

    free(v);
    rs_free(&rs);

    return 1;
}

/* ============================================================
 * Nullspace
 * ============================================================ */

/* Right nullspace basis of matrix (rows x cols). */
static GF *nullspace(
    const GF *in,
    int rows,
    int cols,
    int *dim)
{
    GF *m = malloc((size_t)rows * cols);
    int *piv = malloc((size_t)(rows + 1) * sizeof(int));
    uint8_t *is_pivot = calloc((size_t)cols, 1);

    if (!m || !piv || !is_pivot) {
        free(m);
        free(piv);
        free(is_pivot);
        return NULL;
    }

    memcpy(m, in, (size_t)rows * cols);

    int rank = rref(m, rows, cols, piv);

    for (int i = 0; i < rank; ++i)
        is_pivot[piv[i]] = 1;

    *dim = cols - rank;

    GF *basis = calloc((size_t)(*dim) * cols, 1);

    if (!basis) {
        free(m);
        free(piv);
        free(is_pivot);
        return NULL;
    }

    int d = 0;

    for (int fc = 0; fc < cols; ++fc) {
        if (is_pivot[fc])
            continue;

        basis[(size_t)d * cols + fc] = 1;

        for (int r = 0; r < rank; ++r) {
            basis[(size_t)d * cols + piv[r]] =
                m[(size_t)r * cols + fc];
        }

        ++d;
    }

    free(m);
    free(piv);
    free(is_pivot);

    return basis;
}

/* ============================================================
 * Code membership and random codeword
 * ============================================================ */

static int in_code(const EvalBasis *H, const GF *word)
{
    for (int i = 0; i < H->count; ++i) {
        GF s = 0;

        for (int p = 0; p < nD; ++p) {
            s ^= gf_mul(
                H->v[(size_t)i * nD + p],
                word[p]
            );
        }

        if (s)
            return 0;
    }

    return 1;
}

static int random_codeword(
    const EvalBasis *H,
    GF *word,
    uint64_t *state)
{
    GF *m = malloc((size_t)H->count * nD);
    int *piv = malloc((size_t)(H->count + 1) * sizeof(int));
    uint8_t *isp = calloc((size_t)nD, 1);

    if (!m || !piv || !isp) {
        free(m);
        free(piv);
        free(isp);
        return 0;
    }

    memcpy(m, H->v, (size_t)H->count * nD);

    int rank = rref(m, H->count, nD, piv);

    for (int r = 0; r < rank; ++r)
        isp[piv[r]] = 1;

    for (int p = 0; p < nD; ++p) {
        if (isp[p]) {
            word[p] = 0;
        } else {
            *state += 0x9E3779B97F4A7C15ULL;

            uint64_t z = *state;

            z = (z ^ (z >> 30)) *
                0xBF58476D1CE4E5B9ULL;

            z = (z ^ (z >> 27)) *
                0x94D049BB133111EBULL;

            z ^= z >> 31;

            word[p] = (GF)(z & 63u);
        }
    }

    for (int r = 0; r < rank; ++r) {
        GF s = 0;

        for (int p = 0; p < nD; ++p) {
            if (!isp[p]) {
                s ^= gf_mul(
                    m[(size_t)r * nD + p],
                    word[p]
                );
            }
        }

        word[piv[r]] = s;
    }

    int ok = in_code(H, word);

    free(m);
    free(piv);
    free(isp);

    return ok;
}

/* ============================================================
 * ECP-style decoder
 * ============================================================ */
/*
 * Syndrome-only ECP decoder.
 *
 * Input:
 *   A, B : evaluation bases
 *   S    : syndrome matrix (k1 x k2)
 *
 * Output:
 *   error_vec : recovered error vector (length nD)
 *   nerr      : number of nonzero error values
 *
 * The decoder does NOT receive:
 *   - received word
 *   - original codeword
 *   - actual error positions
 *   - actual error values
 *
 * Return:
 *   1 = unique solution recovered
 *   0 = decoding failure or ambiguous solution
 */
static int decode(
    const EvalBasis *A,
    const EvalBasis *B,
    const GF *S,
    GF *error_vec,
    int *nerr
)
{
    int k1 = A->count;
    int k2 = B->count;

    memset(error_vec, 0, (size_t)nD);
    *nerr = 0;

    /* Check whether syndrome is zero. */
    int allzero = 1;

    for (int i = 0; i < k1 * k2; ++i) {
        if (S[i]) {
            allzero = 0;
            break;
        }
    }

    if (allzero)
        return 1;

    /*
     * Find right kernel of S^T.
     *
     * S^T has dimensions k2 x k1.
     */
    GF *ST = malloc((size_t)k2 * k1);

    if (!ST)
        return 0;

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {
            ST[(size_t)j * k1 + i] =
                S[(size_t)i * k2 + j];
        }
    }

    int dim = 0;

    GF *ker = nullspace(ST, k2, k1, &dim);

    free(ST);

    if (!ker || dim == 0) {
        free(ker);
        return 0;
    }

    /*
     * Find common zeros of all kernel functions.
     */
    int *cand = malloc((size_t)nD * sizeof(int));

    if (!cand) {
        free(ker);
        return 0;
    }

    int nc = 0;

    for (int p = 0; p < nD; ++p) {
        int common_zero = 1;

        for (int v = 0; v < dim; ++v) {
            GF z = 0;

            for (int i = 0; i < k1; ++i) {
                z ^= gf_mul(
                    ker[(size_t)v * k1 + i],
                    A->v[(size_t)i * nD + p]
                );
            }

            if (z) {
                common_zero = 0;
                break;
            }
        }

        if (common_zero)
            cand[nc++] = p;
    }

    free(ker);

    /*
     * Reject impossible or excessively large candidate sets.
     */
    if (nc == 0 || nc > k1 * k2) {
        free(cand);
        return 0;
    }

    /*
     * Solve:
     *
     * S[i,j] = sum_c e_c A_i(P_c) B_j(P_c)
     *
     * Unknowns are only the error values e_c.
     */
    int rows = k1 * k2;
    int cols = nc + 1;

    GF *aug = calloc((size_t)rows * cols, 1);
    int *piv = malloc((size_t)rows * sizeof(int));

    if (!aug || !piv) {
        free(aug);
        free(piv);
        free(cand);
        return 0;
    }

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {

            int r = i * k2 + j;

            for (int c = 0; c < nc; ++c) {
                int p = cand[c];

                aug[(size_t)r * cols + c] =
                    gf_mul(
                        A->v[(size_t)i * nD + p],
                        B->v[(size_t)j * nD + p]
                    );
            }

            aug[(size_t)r * cols + nc] =
                S[(size_t)i * k2 + j];
        }
    }

    /*
     * Solve the augmented linear system.
     */
    int rank = rref(aug, rows, cols, piv);

    /*
     * Unique solution requires:
     *   rank = nc
     *   RHS column is not a pivot.
     */
    int good = (rank == nc);

    for (int r = 0; r < rank && good; ++r) {
        if (piv[r] == nc)
            good = 0;
    }

    if (good) {
        for (int c = 0; c < nc; ++c) {
            GF e = aug[(size_t)c * cols + nc];

            error_vec[cand[c]] = e;

            if (e)
                ++*nerr;
        }

        /*
         * Independent algebraic consistency check:
         * reconstruct the entire syndrome from error_vec.
         */
        for (int i = 0; i < k1 && good; ++i) {
            for (int j = 0; j < k2 && good; ++j) {

                GF check = 0;

                for (int p = 0; p < nD; ++p) {
                    if (!error_vec[p])
                        continue;

                    check ^= gf_mul(
                        error_vec[p],
                        gf_mul(
                            A->v[(size_t)i * nD + p],
                            B->v[(size_t)j * nD + p]
                        )
                    );
                }

                if (check != S[(size_t)i * k2 + j])
                    good = 0;
            }
        }
    }

    if (!good) {
        memset(error_vec, 0, (size_t)nD);
        *nerr = 0;
    }
    //free(error_vec);
    free(aug);
    free(piv);
    free(cand);

    return good;
}

/* ============================================================
 * Random generator and command-line interface
 * ============================================================ */

static uint64_t rng_next(uint64_t *s)
{
    uint64_t z =
        (*s += 0x9E3779B97F4A7C15ULL);

    z = (z ^ (z >> 30)) *
        0xBF58476D1CE4E5B9ULL;

    z = (z ^ (z >> 27)) *
        0x94D049BB133111EBULL;

    return z ^ (z >> 31);
}

static int parse_int(const char *s, int *v)
{
    char *e = NULL;
    long x = strtol(s, &e, 10);

    if (!s[0] || !e || *e ||
        x < 0 || x > 1000000)
        return 0;

    *v = (int)x;
    return 1;
}

static void free_basis(EvalBasis *b)
{
    free(b->v);
    free(b->ex);
    free(b->ey);

    memset(b, 0, sizeof(*b));
}

static void compute_syndrome(
    const EvalBasis *A,
    const EvalBasis *B,
    const GF *received,
    GF *S
)
{
    int k1 = A->count;
    int k2 = B->count;

    memset(S, 0, (size_t)k1 * k2);

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {

            GF s = 0;

            for (int p = 0; p < nD; ++p) {
                s ^= gf_mul(
                    received[p],
                    gf_mul(
                        A->v[(size_t)i * nD + p],
                        B->v[(size_t)j * nD + p]
                    )
                );
            }

            S[(size_t)i * k2 + j] = s;
        }
    }
}

/* ============================================================
 * Main
 * ============================================================ */

int main(int argc, char **argv)
{
    int da = 2;
    int db = 2;
    int errors = 1;
    int trials = 1;
    int seed = 1;

    for (int i = 1; i < argc; ++i) {
        int *dst = NULL;
    
    if (!strcmp(argv[i], "--da"))
            dst = &da;
        else if (!strcmp(argv[i], "--db"))
            dst = &db;
        else if (!strcmp(argv[i], "--errors"))
            dst = &errors;
        else if (!strcmp(argv[i], "--trials"))
            dst = &trials;
        else if (!strcmp(argv[i], "--seed"))
            dst = &seed;
        else if (!strcmp(argv[i], "--help") ||
                 !strcmp(argv[i], "-h")) {
            printf(
                "Usage: %s [--da N] [--db N] "
                "[--errors N] [--trials N] [--seed N]\n",
                argv[0]
            );
            return 0;
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            return 2;
        }

        if (i + 1 >= argc ||
            !parse_int(argv[++i], dst)) {
            fprintf(stderr, "Invalid option value\n");
            return 2;
        }
    }

    if (da > 30 || db > 30 ||
        errors < 0 || trials < 1) {
        fprintf(stderr, "Invalid parameters.\n");
        return 2;
    }

    if (!gf_init()) {
        fprintf(
            stderr,
            "GF(64) initialization failed for polynomial 0x43\n"
        );
        return 1;
    }

    nD = enumerate_points();

    if (nD <= 0) {
        fprintf(stderr, "Point enumeration failed\n");
        return 1;
    }

    printf("Curve: seven-term BBGS input over GF(64)\n");

    printf(
        "F(x,y) = x^31*y^8 + x^30*y^16 "
        "+ x^28*y^32 + x^24*y "
        "+ x^16*y^2 + y^4 + x^32\n"
    );

    printf("Affine rational points: %d\n", nD);

    EvalBasis A = {0};
    EvalBasis B = {0};
    EvalBasis H = {0};

    if (!build_monomial_basis(da, &A) ||
        !build_monomial_basis(db, &B) ||
        !build_product_basis(&A, &B, &H)) {

        fprintf(
            stderr,
            "Basis construction failed.\n"
        );

        free_basis(&A);
        free_basis(&B);
        free_basis(&H);
        free(D);

        return 1;
    }

    printf(
        "A basis: %d independent monomials "
        "(total degree <= %d)\n",
        A.count, da
    );

    printf(
        "B basis: %d independent monomials "
        "(total degree <= %d)\n",
        B.count, db
    );

    printf(
        "H basis: %d independent products; C = H^perp\n",
        H.count
    );

    printf(
        "Code length n=%d; parity-check rank=%d; dimension k=%d\n",
        nD, H.count, nD - H.count
    );

    GF *cw = malloc((size_t)nD);
    GF *received = malloc((size_t)nD);
    GF *decoded = malloc((size_t)nD);
    GF *error_vec = calloc((size_t)nD, 1);
    GF *injected = calloc((size_t)nD, 1);

    int *order = malloc((size_t)nD * sizeof(int));
if (!cw || !received || !decoded || !order || !injected || !error_vec) {
    fprintf(stderr, "Allocation failed\n");
    return 1;
}
    uint64_t rng =
        (uint64_t)(unsigned)seed +
        0x123456789abcdefULL;

    int success = 0;
    int fail = 0;
    int miscorrect = 0;

    for (int tr = 0; tr < trials; ++tr) {
        memset(injected, 0, (size_t)nD);
        if (!random_codeword(&H, cw, &rng)) {
            fprintf(
                stderr,
                "Could not construct a codeword in ker(H)\n"
            );
            return 1;
        }

        memcpy(received, cw, (size_t)nD);

        for (int p = 0; p < nD; ++p)
            order[p] = p;

        for (int e = 0; e < errors; ++e) {
            int j = e +
                (int)(rng_next(&rng) % (uint64_t)(nD - e));

            int tmp = order[e];
            order[e] = order[j];
            order[j] = tmp;

            GF value =
                (GF)(1 + rng_next(&rng) % (Q - 1));
            received[order[e]] ^= value;
            injected[order[e]] ^= value;
            //received[order[e]] ^= value;
        }


//GF *error_vec = calloc((size_t)nD, 1);

GF *S = calloc(
    (size_t)A.count * B.count,
    sizeof(GF)
);

//GF *error_vec = calloc((size_t)nD, sizeof(GF));

if (!S || !error_vec) {
    fprintf(stderr, "Allocation failed\n");
    return 1;
}

/* Verification side: calculate syndrome. */
compute_syndrome(&A, &B, received, S);

/* Decoder receives ONLY syndrome. */
int recovered = 0;

int ok = decode(
    &A,
    &B,
    S,
    error_vec,
    &recovered
);

int mismatch = 0;

for (int p = 0; p < nD; ++p) {
    if (injected[p] != error_vec[p]) {
        printf("MISMATCH position=%d injected=0x%02X decoded=0x%02X\n",
               p, injected[p], error_vec[p]);
        mismatch++;
    }
}

printf("Mismatch positions/values: %d\n", mismatch);

//exit(1);

/* Verification side: correct received word. */
memcpy(decoded, received, (size_t)nD);

for (int p = 0; p < nD; ++p)
    decoded[p] ^= error_vec[p];

        int same =
            ok && memcmp(cw, decoded, (size_t)nD) == 0;

        if (same)
            ++success;
        else if (ok)
            ++miscorrect;
        else
            ++fail;

        if (trials == 1) {
            printf("\nInjected error vector:\n");


printf("\nInjected error locations and values:\n");

for (int p = 0; p < nD; ++p) {
    if (injected[p])
        printf("  position=%d value=0x%02X\n",
               p, injected[p]);
}

printf("\nDecoded error locations and values:\n");

for (int p = 0; p < nD; ++p) {
    if (error_vec[p])
        printf("  position=%d value=0x%02X\n",
               p, error_vec[p]);
}

printf("\nDecoded error vector:\n");

for (int i = 0; i < nD; ++i) {
    GF e = received[i] ^ decoded[i];

    if (e)
        printf("  position=%d value=0x%02X\n", i, e);
}
            printf(
                "Trial: %s; injected errors=%d; "
                "recovered nonzero corrections=%d\n",
                same ? "PASS" :
                (ok ? "MISCORRECTION" : "FAIL"),
                errors,
                recovered
            );
        }
    free(S);
    }

    if (trials > 1) {
        printf(
            "Trials=%d: success=%d, miscorrection=%d, failure=%d\n",
            trials, success, miscorrect, fail
        );
    }
    

    free(injected);
    free(cw);
    free(received);
    free(decoded);
    free(order);

    free_basis(&A);
    free_basis(&B);
    free_basis(&H);

    free(D);

    return (success == trials) ? 0 : 1;
}
