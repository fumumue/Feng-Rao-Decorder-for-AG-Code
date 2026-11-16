
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

#define FIELD_POLY 0x89
#define NTERMS 8
#define MAX_MONOMIALS 512

#define M 7
#define Q 128
//#define PRIMITIVE_POLY 0x89
#define N Q
typedef uint8_t GF;

typedef struct
{

  unsigned short n[3];
  unsigned short a;

} mterm;


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
  //gf256 g=1 elliptic
  unsigned short el[4][4] =
    { {0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1} };
  //gf256 g=1 elloptic
  unsigned short el2[5][4] =
    { {0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1}, {2, 0, 1, 1} };
  //gf8 g=6 Generalized Hermitian
  unsigned short sc[4][4] =
    { {3, 2, 0, 1}, {2, 4, 0, 1}, {0, 1, 0, 1}, {4, 0, 0, 1} };
  //gf8 g=3 klein
  unsigned short kl[3][4] = { {3, 1, 0, 1}, {0, 3, 0, 1}, {1, 0, 0, 1} };
  //gfQ*Q Hermitian
  unsigned short he[3][4] = { {Q + 1, 0, 0, 1}, {0, Q, 0, 1}, {0, 1, 0, 1} };
  //gf16 g=21 #N=121 Generalized Hermitian
  unsigned short gu[5][4] =
    { {7, 4, 0, 1}, {6, 8, 0, 1}, {4, 1, 0, 1}, {0, 2, 0, 1}, {8, 0, 0, 1} };
  //gf32 g=75 #N=497 Generalized Hermitian
  unsigned short ge[6][4] =
    { {15, 8, 0, 1}, {14, 16, 0, 1}, {12, 1, 0, 1}, {8, 2, 0, 1}, {0, 4, 0,
								   1}, {16, 0,
									0,
									1} };
  //gf64 g=212 #N=2017 Generalized Hermitian
  unsigned short gg[7][4] =
    { {31, 8, 0, 1}, {30, 16, 0, 1}, {28, 32, 0, 1}, {24, 1, 0, 1}, {16, 2, 0,
								     1}, {0,
									  4,
									  0,
									  1},
    {32, 0, 0, 1} };
  //gf256 g=2413 Generalized Hermitian
  unsigned short gd[9][4] =
    { {127, 8, 0, 1}, {126, 16, 0, 1}, {124, 32, 0, 1}, {120, 64, 0, 1}, {112,
									  128,
									  0,
									  1},
    {96, 1, 0, 1}, {64, 2, 0, 1}, {0, 4, 0, 1}, {128, 0, 0, 1} };
  //gf128 g=315 Generalized Hermitian
  unsigned short cc[8][4] =
    { {63, 8, 0, 1}, {62, 16, 0, 1}, {60, 32, 0, 1}, {56, 64, 0, 1}, {48, 1,
								      0, 1},
    {32, 2, 0, 1}, {0, 4, 0, 1}, {64, 0, 0, 1} };
  //gf256 y^(Q+1)=X^8+x^4+x^2+x kummer
  unsigned short ku[5][4] =
    { {0, 17, 0, 1}, {8, 0, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };
  //gf16 kummer
  unsigned short ku3[5][4] =
    { {0, 5, 0, 1}, {12, 0, 0, 1}, {9, 0, 0, 1}, {6, 0, 0, 1}, {3, 0, 0, 1} };
  //gf64 kummer g=56
  unsigned short ku4[5][4] =
    { {0, 9, 0, 1}, {40, 0, 0, 1}, {33, 0, 0, 1}, {12, 0, 0, 1}, {5, 0, 0,
								  1} };
  unsigned short lo[3][4] = { {2, 0, 0, 1}, {1, 0, 0, 3}, {0, 1, 0, 6} };
  unsigned short lk[6][4] =
    { {0, 2, 0, 1}, {0, 1, 0, 3}, {0, 0, 1, 6}, {3, 1, 0, 1}, {0, 3, 1, 1},
    {1, 0, 3, 1} };
  //gf32 g=26 #N=157
  unsigned short ts[3][4] = { {2, 2, 5, 1}, {7, 0, 2, 1}, {0, 9, 0, 1} };
  //gf128 g=78 #N=891
  unsigned short tt[3][4] = { {3, 1, 0, 1}, {13, 0, 0, 1}, {0, 14, 0, 1} };
  //gf512 Generalized Hermitian
  unsigned short gt[10][4] =
    { {255, 16, 0, 1}, {254, 32, 0, 1}, {252, 64, 0, 1}, {248, 128, 0, 1},
    {240, 256, 0, 1}, {224, 1, 0, 1}, {192, 2, 0, 1}, {128, 4, 0, 1}, {0, 8,
								       0, 1},
    {256, 0, 0, 1} };
  //over gf128 suzuki #N=16384
  unsigned short su[4][4] =
    { {0, 128, 0, 1}, {0, 1, 0, 1}, {136, 0, 0, 1}, {9, 0, 0, 1} };
  //gf32 suzuki #N=1024
  unsigned short s2[4][4] =
    { {0, 32, 0, 1}, {0, 1, 0, 1}, {36, 0, 0, 1}, {5, 0, 0, 1} };
  //gf8 suzuki 
  unsigned short s3[4][4] =
    { {0, 8, 0, 1}, {0, 1, 0, 1}, {10, 0, 0, 1}, {3, 0, 0, 1} };
  //y9 = x4 + x2 + x gf64 kummer
  unsigned short ku2[4][4] =
    { {0, 9, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };
  //y^9=x^2+x gf64 g=4
  unsigned short ku5[3][4] = { {0, 9, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };

  unsigned int bb[256][2] = { 0 };	//{{0,0},{1,0},{0,1},{2,0},{1,1},{0,2},{3,0},{2,1},{1,2},{0,3},{4,0},{3,1},{2,2},{1,3},{0,4},{5,0},{4,1},{3,2},{2,3},{1,4},{6,0},{5,1},{4,2},{3,3},{2,4},{7,0},{6,1},{5,2},{4,3},{3,4}};
  mterm aa[1256] = { 0 };
  mterm oo = { 0 };
  unsigned int d[256][2] = { 0 };

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

        if (aa & 0x80)
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

    for (int i = 0; i < 8; ++i) {
        const unsigned short *t = cc[i]; //BBGS_EQUATION[i];

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


static int g_xmax = 1 << 20;   /* x の指数の上限。既定は制限なし */

static int build_monomial_basis(int degree, EvalBasis *out)
{
    int xm = g_xmax < degree ? g_xmax : degree;

    int cap = 0;
    for (int i = 0; i <= xm; ++i)
        cap += degree - i + 1;

    if (cap > MAX_MONOMIALS)
        return 0;

    memset(out, 0, sizeof(*out));

    out->v  = calloc((size_t)cap * nD, 1);
    out->ex = malloc((size_t)cap * sizeof(int));
    out->ey = malloc((size_t)cap * sizeof(int));

    GF *xp = malloc((size_t)(xm + 1) * nD);
    GF *yp = malloc((size_t)(degree + 1) * nD);

    if (!out->v || !out->ex || !out->ey || !xp || !yp) {
        free(out->v); free(out->ex); free(out->ey);
        free(xp); free(yp);
        memset(out, 0, sizeof(*out));
        return 0;
    }

    /* x^i, y^j の表(点ごと) */
    for (int p = 0; p < nD; ++p) {
        xp[p] = 1;
        yp[p] = 1;
    }
    for (int i = 1; i <= xm; ++i)
        for (int p = 0; p < nD; ++p)
            xp[(size_t)i * nD + p] =
                gf_mul(xp[(size_t)(i - 1) * nD + p], D[p].x);
    for (int j = 1; j <= degree; ++j)
        for (int p = 0; p < nD; ++p)
            yp[(size_t)j * nD + p] =
                gf_mul(yp[(size_t)(j - 1) * nD + p], D[p].y);

    /* 全次数 d ごとに (d,0), (d-1,1), ... の順。x の指数が上限を超えるものは飛ばす */
    int count = 0;
    for (int d = 0; d <= degree; ++d) {
        for (int k = 0; k <= d; ++k) {
            int i = d - k;
            int j = k;

            if (i > xm)
                continue;

            GF *row = out->v + (size_t)count * nD;

            for (int p = 0; p < nD; ++p)
                row[p] = gf_mul(xp[(size_t)i * nD + p],
                                yp[(size_t)j * nD + p]);

            out->ex[count] = i;
            out->ey[count] = j;
            ++count;
        }
    }
    out->count = count;

    free(xp);
    free(yp);

#ifdef CHECK_INDEP
    /* 確認用: 評価ベクトルが独立かを調べる(コンパイル時に -DCHECK_INDEP) */
    {
        RowSpace rs;
        if (rs_init(&rs, count, nD)) {
            for (int k = 0; k < count; ++k)
                if (rs_add(&rs, out->v + (size_t)k * nD) == 0)
                    fprintf(stderr, "dependent: x^%d y^%d\n",
                            out->ex[k], out->ey[k]);
            rs_free(&rs);
        }
    }
#endif

    return 1;
}

/*
 * Build an independent evaluation basis from monomials x^i y^j
 * with total degree <= degree.
 *
 * This is an evaluation-space basis, not yet a proven
 * Riemann-Roch basis ordered by pole order.
 */
static int build_monomial_basis2(int degree, EvalBasis *out)
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

mterm
obase (int a, int b)
{
  int i, j, k;
  mterm c = { 0 };

  c.n[0] = a;
  c.n[1] = b;


  return c;
}




int
mkbase (mterm * aa)
{
  int i, j, k, l, count;
  int d[256][2] = { 0 };
  int bb[256][2] = { 0 };


  count = 1;

  for (i = 0; i < 20; i++)
    {
      k = 0;
      j = i;
      while ((d[i][0] + d[i][1]) < i && i < 5)
	{
	  d[k][1] = k;
	  d[k][0] = j - k;
	  printf ("k1=%d %d\n", j - k, k);
	  k++;

	}
      for (l = 0; l < k; l++)
	{
	  bb[count][0] = d[l][0];
	  bb[count++][1] = d[l][1];
	  //    printf("a%d %d\n",d[l][0],d[l][1]);
	}

      if (i > 4)
	{
	  l = i - 4;
	  j = 4;
	  while (d[i][0] + d[i][1] < i && l < N - 1)
	    {
	      d[k][0] = j;
	      d[k][1] = l;
	      k++;
	      j--;
	      l++;
	      printf ("k2=%d", k);
	      if (j < 0)
		break;
	    }
	  for (l = 0; l < k; l++)
	    {
	      bb[count][0] = d[l][0];
	      bb[count++][1] = d[l][1];
	      //    printf("a%d %d\n",d[l][0],d[l][1]);
	    }
	}


    }

  for (i = 0; i < 15 * 15; i++)
    printf ("d=%d %d\n", bb[i][0], bb[i][1]);
  // exit(1);


  for (i = 0; i < 15 * 15; i++)
    {
      printf ("%d %d\n", bb[i][0], bb[i][1]);
      //for(j=0;j<N-1;j++){
      //  if(bb[i][0]+bb[i][1]<10){
      aa[i] = obase (bb[i][0], bb[i][1]);
      aa[i].a = 1;
      //      }
      // }
    }
  // exit(1);

  return count;
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
    int da = 0;
    int db = 0;
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
        
        int xmaxopt = 1 << 20;
         if (!strcmp(argv[i], "--xmax")) dst = &xmaxopt;
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
//exit(1);

    printf("Curve: seven-term BBGS input over GF(64)\n");

    printf(
        "F(x,y) = x^31*y^8 + x^30*y^16 "
        "+ x^28*y^32 + x^24*y "
        "+ x^16*y^2 + y^4 + x^32\n"
    );

    printf("Affine rational points: %d\n", nD);
    //exit(1);


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
    free(error_vec);

    free_basis(&A);
    free_basis(&B);
    free_basis(&H);

    free(D);

    return (success == trials) ? 0 : 1;
}
