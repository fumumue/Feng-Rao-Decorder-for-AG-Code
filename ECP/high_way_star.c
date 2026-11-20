/*
 * BBGS / 一般化エルミート曲線: 評価符号とECP型復号器
 * GF(2^m), m <= 8
 *
 * Build:
 *   cc -O2 -std=c11 -Wall -Wextra bbgs.c -o bbgs
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>


#define MAXQ 256
#define MAX_MONOMIALS 8192

typedef uint8_t GF;

static int gQ = 128;
static unsigned gpoly = 0x89;
#define Q gQ

static int g_verbose = 0;
static int g_full = 0;

static int g_w2 = 0, g_pole = -1;


/* ============================================================
 * Curves
 * ============================================================ */

static const unsigned short sc[4][4] = {
    {3,2,0,1}, {2,4,0,1}, {0,1,0,1}, {4,0,0,1}
};
static const unsigned short kl[3][4] = {
    {3,1,0,1}, {0,3,0,1}, {1,0,0,1}
};
static const unsigned short s3[4][4] = {
    {0,8,0,1}, {0,1,0,1}, {10,0,0,1}, {3,0,0,1}
};

static const unsigned short gu[5][4] = {
    {7,4,0,1}, {6,8,0,1}, {4,1,0,1}, {0,2,0,1}, {8,0,0,1}
};
static const unsigned short ku3[5][4] = {
    {0,5,0,1}, {12,0,0,1}, {9,0,0,1}, {6,0,0,1}, {3,0,0,1}
};

static const unsigned short ge[6][4] = {
    {15,8,0,1}, {14,16,0,1}, {12,1,0,1},
    {8,2,0,1}, {0,4,0,1}, {16,0,0,1}
};
static const unsigned short s2[4][4] = {
    {0,32,0,1}, {0,1,0,1}, {36,0,0,1}, {5,0,0,1}
};
static const unsigned short ts[3][4] = {
    {2,2,5,1}, {7,0,2,1}, {0,9,0,1}
};

static const unsigned short gg[7][4] = {
    {31,8,0,1}, {30,16,0,1}, {28,32,0,1},
    {24,1,0,1}, {16,2,0,1}, {0,4,0,1}, {32,0,0,1}
};
static const unsigned short ku2[4][4] = {
    {0,9,0,1}, {4,0,0,1}, {2,0,0,1}, {1,0,0,1}
};
static const unsigned short ku4[5][4] = {
    {0,9,0,1}, {40,0,0,1}, {33,0,0,1}, {12,0,0,1}, {5,0,0,1}
};
static const unsigned short ku5[3][4] = {
    {0,9,0,1}, {2,0,0,1}, {1,0,0,1}
};

static const unsigned short cc[8][4] = {
    {63,8,0,1}, {62,16,0,1}, {60,32,0,1}, {56,64,0,1},
    {48,1,0,1}, {32,2,0,1}, {0,4,0,1}, {64,0,0,1}
};
static const unsigned short tt[3][4] = {
    {3,1,0,1}, {13,0,0,1}, {0,14,0,1}
};
static const unsigned short su[4][4] = {
    {0,128,0,1}, {0,1,0,1}, {136,0,0,1}, {9,0,0,1}
};

static const unsigned short gd[9][4] = {
    {127,8,0,1}, {126,16,0,1}, {124,32,0,1},
    {120,64,0,1}, {112,128,0,1}, {96,1,0,1},
    {64,2,0,1}, {0,4,0,1}, {128,0,0,1}
};
static const unsigned short ku[5][4] = {
    {0,17,0,1}, {8,0,0,1}, {4,0,0,1}, {2,0,0,1}, {1,0,0,1}
};
static const unsigned short el[4][4] = {
    {0,2,1,1}, {1,1,1,1}, {3,0,0,1}, {0,0,3,1}
};
static const unsigned short el2[5][4] = {
    {0,2,1,1}, {1,1,1,1}, {3,0,0,1}, {0,0,3,1}, {2,0,1,1}
};

static unsigned short he_buf[3][4];

typedef struct {
    const char *name;
    int m;
    unsigned poly;
    int nterms;
    const unsigned short (*t)[4];
} CurveDef;

#define NT(a) ((int)(sizeof(a) / sizeof((a)[0])))

static const CurveDef CURVES[] = {
    {"sc",3,0x0B,NT(sc),sc},
    {"kl",3,0x0B,NT(kl),kl},
    {"s3",3,0x0B,NT(s3),s3},
    {"gu",4,0x13,NT(gu),gu},
    {"ku3",4,0x13,NT(ku3),ku3},
    {"ge",5,0x25,NT(ge),ge},
    {"s2",5,0x25,NT(s2),s2},
    {"ts",5,0x25,NT(ts),ts},
    {"gg",6,0x43,NT(gg),gg},
    {"ku2",6,0x43,NT(ku2),ku2},
    {"ku4",6,0x43,NT(ku4),ku4},
    {"ku5",6,0x43,NT(ku5),ku5},
    {"cc",7,0x89,NT(cc),cc},
    {"su",7,0x89,NT(su),su},
    {"tt",7,0x89,NT(tt),tt},
    {"gd",8,0x11D,NT(gd),gd},
    {"ku",8,0x11D,NT(ku),ku},
    {"el",8,0x11D,NT(el),el},
    {"el2",8,0x11D,NT(el2),el2},
    {"he",0,0,3,(const unsigned short (*)[4])he_buf}
};
#define NCURVES ((int)(sizeof(CURVES) / sizeof(CURVES[0])))

static CurveDef cur_local;
static const CurveDef *curve;

static const CurveDef *find_curve(const char *name)
{
    for (int i = 0; i < NCURVES; ++i)
        if (!strcmp(CURVES[i].name, name))
            return &CURVES[i];
    return NULL;
}

static int curve_degree(void)
{
    int d = 0;
    for (int i = 0; i < curve->nterms; ++i) {
        int x = curve->t[i][0] + curve->t[i][1];
        if (x > d) d = x;
    }
    return d;
}

/* ============================================================
 * GF(2^m)
 * ============================================================ */

static GF expt[2 * (MAXQ - 1)];
static int logt[MAXQ];
static GF mt[MAXQ][MAXQ];

static GF gf_mul_slow(GF a, GF b)
{
    unsigned x = a, y = b, r = 0;
    while (y) {
        if (y & 1u) r ^= x;
        y >>= 1;
        x <<= 1;
        if (x & (unsigned)Q) x ^= gpoly;
    }
    return (GF)(r & (unsigned)(Q - 1));
}

static int gf_init(int m, unsigned poly)
{
    gQ = 1 << m;
    gpoly = poly;

    GF x = 1;
    for (int i = 0; i < Q; ++i)
        logt[i] = -1;

    for (int i = 0; i < Q - 1; ++i) {
        if (!x || logt[x] >= 0)
            return 0;
        expt[i] = x;
        logt[x] = i;
        x = gf_mul_slow(x, 2);
    }
    if (x != 1) return 0;

    for (int i = Q - 1; i < 2 * (Q - 1); ++i)
        expt[i] = expt[i - (Q - 1)];

    for (int a = 0; a < Q; ++a)
        for (int b = 0; b < Q; ++b)
            mt[a][b] = (a && b) ? expt[logt[a] + logt[b]] : 0;

    return 1;
}

static inline GF gf_mul(GF a, GF b) { return mt[a][b]; }

static inline GF gf_inv(GF a)
{
    return a ? expt[(Q - 1) - logt[a]] : 0;
}

static GF gf_pow(GF a, unsigned n)
{
    if (!n) return 1;
    if (!a) return 0;
    return expt[((unsigned)logt[a] * (n % (unsigned)(Q - 1)))
                % (unsigned)(Q - 1)];
}

/* ============================================================
 * Curve points
 * ============================================================ */

typedef struct { GF x, y; } Point;

static Point *D;
static int nD;

static GF eval_curve(GF x, GF y)
{
    GF f = 0;
    for (int i = 0; i < curve->nterms; ++i) {
        const unsigned short *t = curve->t[i];
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
    if (!D) return 0;

    nD = 0;
    for (int x = 0; x < Q; ++x)
        for (int y = 0; y < Q; ++y)
            if (!eval_curve((GF)x, (GF)y))
                D[nD++] = (Point){(GF)x, (GF)y};

    return nD;
}

/* ============================================================
 * Incremental row echelon basis
 *
 * ピボット列を昇順に保持する。
 * 各行は先頭のピボットを1に正規化した行階段形。
 * ============================================================ */

typedef struct {
    int nrows, ncols, cap;
    GF *echelon;
    int *piv;
    GF *w;
} RowSpace;

static int rs_init(RowSpace *s, int cap, int ncols)
{
    memset(s, 0, sizeof(*s));
    s->cap = cap;
    s->ncols = ncols;

    s->echelon = calloc((size_t)(cap ? cap : 1) * ncols, 1);
    s->piv = malloc((size_t)(cap ? cap : 1) * sizeof(int));
    s->w = malloc((size_t)ncols);

    if (!s->echelon || !s->piv || !s->w) {
        free(s->echelon);
        free(s->piv);
        free(s->w);
        memset(s, 0, sizeof(*s));
        return 0;
    }
    return 1;
}

static void rs_free(RowSpace *s)
{
    free(s->echelon);
    free(s->piv);
    free(s->w);
    memset(s, 0, sizeof(*s));
}

/* 1: 独立行を追加, 0: 従属, -1: 容量不足 */
static int rs_add(RowSpace *s, const GF *v)
{
    GF *w = s->w;
    memcpy(w, v, (size_t)s->ncols);

    /* 既存ピボットを昇順に消去 */
    for (int r = 0; r < s->nrows; ++r) {
        int p = s->piv[r];
        GF f = w[p];
        if (!f) continue;

        const GF *e = s->echelon + (size_t)r * s->ncols;
        for (int j = p; j < s->ncols; ++j)
            w[j] ^= gf_mul(f, e[j]);
    }

    int p = 0;
    while (p < s->ncols && !w[p]) ++p;
    if (p == s->ncols) return 0;
    if (s->nrows >= s->cap) return -1;

    GF inv = gf_inv(w[p]);
    for (int j = p; j < s->ncols; ++j)
        w[j] = gf_mul(w[j], inv);

    /* ピボット列の昇順位置に挿入 */
    int pos = 0;
    while (pos < s->nrows && s->piv[pos] < p)
        ++pos;

    if (pos < s->nrows) {
        memmove(s->echelon + (size_t)(pos + 1) * s->ncols,
                s->echelon + (size_t)pos * s->ncols,
                (size_t)(s->nrows - pos) * s->ncols);
        memmove(s->piv + pos + 1, s->piv + pos,
                (size_t)(s->nrows - pos) * sizeof(int));
    }

    memcpy(s->echelon + (size_t)pos * s->ncols, w,
           (size_t)s->ncols);
    s->piv[pos] = p;
    ++s->nrows;

    return 1;
}

/* ============================================================
 * Nullspace
 *
 * RREFを作らず、行階段形から後退代入で右核を構成する。
 * ============================================================ */

static GF *nullspace(const GF *in, int rows, int cols, int *dim)
{
    RowSpace rs;
    if (!rs_init(&rs, rows, cols))
        return NULL;

    for (int i = 0; i < rows; ++i) {
        int r = rs_add(&rs, in + (size_t)i * cols);
        if (r < 0) {
            rs_free(&rs);
            return NULL;
        }
    }

    int rank = rs.nrows;
    *dim = cols - rank;

    GF *basis = calloc((size_t)(*dim > 0 ? *dim : 1) * cols, 1);
    if (!basis) {
        rs_free(&rs);
        return NULL;
    }

    uint8_t *is_pivot = calloc((size_t)cols, 1);
    if (!is_pivot) {
        free(basis);
        rs_free(&rs);
        return NULL;
    }

    for (int r = 0; r < rank; ++r)
        is_pivot[rs.piv[r]] = 1;

    int d = 0;
    for (int f = 0; f < cols; ++f) {
        if (is_pivot[f]) continue;

        GF *x = basis + (size_t)d * cols;
        x[f] = 1;

        /* x[p] = sum_{j>p} row[j] x[j] */
        for (int r = rank - 1; r >= 0; --r) {
            int p = rs.piv[r];
            const GF *e = rs.echelon + (size_t)r * cols;
            GF v = 0;

            for (int j = p + 1; j < cols; ++j)
                v ^= gf_mul(e[j], x[j]);

            x[p] = v;
        }
        ++d;
    }

    free(is_pivot);
    rs_free(&rs);
    return basis;
}

/* ============================================================
 * Evaluation bases
 * ============================================================ */

typedef struct {
    int count;
    GF *v;
    int *ex, *ey;
} EvalBasis;

static void free_basis(EvalBasis *b)
{
    free(b->v);
    free(b->ex);
    free(b->ey);
    memset(b, 0, sizeof(*b));
}

static int build_basis_from_list(int (*lst)[2], int n, EvalBasis *out)
{
    memset(out, 0, sizeof(*out));
    if (n <= 0 || n > MAX_MONOMIALS)
        return 0;

    int xm = 0, ym = 0, maxdeg = 0;
    for (int k = 0; k < n; ++k) {
        if (lst[k][0] > xm) xm = lst[k][0];
        if (lst[k][1] > ym) ym = lst[k][1];
        if (lst[k][0] + lst[k][1] > maxdeg)
            maxdeg = lst[k][0] + lst[k][1];
    }

    int dF = curve_degree();
    int known = maxdeg < dF && (long)nD > (long)maxdeg * dF;
    int use_rs = !known;

    RowSpace rs;
    int rs_ok = 0;
    int ok = 1;

    GF *xp = malloc((size_t)(xm + 1) * nD);
    GF *yp = malloc((size_t)(ym + 1) * nD);
    GF *row = malloc((size_t)nD);

    out->v = calloc((size_t)n * nD, 1);
    out->ex = malloc((size_t)n * sizeof(int));
    out->ey = malloc((size_t)n * sizeof(int));

    if (!xp || !yp || !row || !out->v || !out->ex || !out->ey)
        ok = 0;

    if (ok && use_rs) {
        rs_ok = rs_init(&rs, n, nD);
        if (!rs_ok) ok = 0;
    }

    if (ok) {
        for (int p = 0; p < nD; ++p) {
            xp[p] = 1;
            yp[p] = 1;
        }

        for (int i = 1; i <= xm; ++i)
            for (int p = 0; p < nD; ++p)
                xp[(size_t)i * nD + p] =
                    gf_mul(xp[(size_t)(i - 1) * nD + p], D[p].x);

        for (int j = 1; j <= ym; ++j)
            for (int p = 0; p < nD; ++p)
                yp[(size_t)j * nD + p] =
                    gf_mul(yp[(size_t)(j - 1) * nD + p], D[p].y);

        int count = 0;
        for (int k = 0; k < n; ++k) {
            int i = lst[k][0], j = lst[k][1];

            for (int p = 0; p < nD; ++p)
                row[p] = gf_mul(xp[(size_t)i * nD + p],
                                yp[(size_t)j * nD + p]);

            if (use_rs) {
                int added = rs_add(&rs, row);
                if (added < 0) {
                    ok = 0;
                    break;
                }
                if (!added) continue;
            }

            memcpy(out->v + (size_t)count * nD, row, (size_t)nD);
            out->ex[count] = i;
            out->ey[count] = j;
            ++count;
        }
        out->count = count;
    }

    if (rs_ok) rs_free(&rs);
    free(xp);
    free(yp);
    free(row);

    if (!ok) {
        free_basis(out);
        return 0;
    }
    return 1;
}

static int build_monomial_basis(int degree, int xm, EvalBasis *out)
{
    if (xm > degree) xm = degree;

    int cap = 0;
    for (int i = 0; i <= xm; ++i)
        cap += degree - i + 1;

    if (cap > MAX_MONOMIALS) {
        memset(out, 0, sizeof(*out));
        return 0;
    }

    int (*lst)[2] = malloc((size_t)cap * sizeof(*lst));
    if (!lst) {
        memset(out, 0, sizeof(*out));
        return 0;
    }

    int n = 0;
    for (int d = 0; d <= degree; ++d)
        for (int k = 0; k <= d; ++k)
            if (d - k <= xm) {
                lst[n][0] = d - k;
                lst[n][1] = k;
                ++n;
            }

    int r = build_basis_from_list(lst, n, out);
    free(lst);
    return r;
}

/* ============================================================
 * mkbase
 * ============================================================ */

#define MK_XMAX 8
#define MK_MAXDEG 100
#define MK_BBCAP ((MK_XMAX + 1) * (MK_MAXDEG + 1))

#include "mkbase2.h"

static int mkbase(int bb[][2])
{
    int count = 0;
    for (int dg = 0; dg <= MK_MAXDEG; ++dg) {
        int x0 = dg < MK_XMAX ? dg : MK_XMAX;
        for (int x = x0; x >= 0; --x) {
            bb[count][0] = x;
            bb[count][1] = dg - x;
            ++count;
        }
    }
    return count;
}

static int build_mk_basis(int degree, EvalBasis *out)
{
    static int bb[MK_BBCAP][2];
    int cnt = mkbase(bb);
    int n = 0;

    while (n < cnt && bb[n][0] + bb[n][1] <= degree)
        ++n;

    return build_basis_from_list(bb, n, out);
}

static int mk_count(int degree)
{
    static int bb[MK_BBCAP][2];
    int cnt = mkbase(bb), n = 0;

    while (n < cnt && bb[n][0] + bb[n][1] <= degree)
        ++n;

    return n;
}


static int basis_count(int d)
{ return g_w2 ? mk2_count(d) : (g_full ? (d+1)*(d+2)/2 : mk_count(d)); }

static int build_ab_basis(int d, EvalBasis *o)
{ return g_w2 ? build_mk2_basis(d, 1, o)
              : (g_full ? build_monomial_basis(d, d, o) : build_mk_basis(d, o)); }

static int basis_xmax(int d)
{ return g_w2 ? d : (g_full ? d : (MK_XMAX < d ? MK_XMAX : d)); }

static int build_h_basis(int da, int db, int xa, int xb, EvalBasis *o)
{ return g_w2 ? build_mk2_basis(da + db, 2, o)
              : build_monomial_basis(da + db, xa + xb, o); }

static int max_deg(void) { return g_w2 ? MK2_MAXW : MK_MAXDEG; }



/* ============================================================
 * Random generator
 * ============================================================ */

static uint64_t rng_next(uint64_t *s)
{
    uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* ============================================================
 * Codeword generation
 * ============================================================ */

typedef struct {
    GF *m;
    int *piv;
    uint8_t *isp;
    int rank;
} CodeGen;

static void codegen_free(CodeGen *g)
{
    free(g->m);
    free(g->piv);
    free(g->isp);
    memset(g, 0, sizeof(*g));
}

static int codegen_init(CodeGen *g, const EvalBasis *H)
{
    memset(g, 0, sizeof(*g));

    RowSpace rs;
    if (!rs_init(&rs, H->count, nD))
        return 0;

    for (int i = 0; i < H->count; ++i) {
        if (rs_add(&rs, H->v + (size_t)i * nD) < 0) {
            rs_free(&rs);
            return 0;
        }
    }

    g->rank = rs.nrows;
    g->m = malloc((size_t)g->rank * nD);
    g->piv = malloc((size_t)(g->rank ? g->rank : 1) * sizeof(int));
    g->isp = calloc((size_t)nD, 1);

    if (!g->m || !g->piv || !g->isp) {
        codegen_free(g);
        rs_free(&rs);
        return 0;
    }

    memcpy(g->m, rs.echelon, (size_t)g->rank * nD);
    memcpy(g->piv, rs.piv, (size_t)g->rank * sizeof(int));

    for (int r = 0; r < g->rank; ++r)
        g->isp[g->piv[r]] = 1;

    rs_free(&rs);
    return 1;
}

/* 自由変数を決め、後退代入で H * word = 0 を満たす */
static void random_codeword(const CodeGen *g, GF *word, uint64_t *state)
{
    for (int p = 0; p < nD; ++p)
        word[p] = g->isp[p] ? 0 : (GF)(rng_next(state) & (uint64_t)(Q - 1));

    for (int r = g->rank - 1; r >= 0; --r) {
        int p = g->piv[r];
        const GF *row = g->m + (size_t)r * nD;
        GF s = 0;

        for (int j = p + 1; j < nD; ++j)
            s ^= gf_mul(row[j], word[j]);

        word[p] = s;
    }
}

static int in_code(const EvalBasis *H, const GF *word)
{
    for (int i = 0; i < H->count; ++i) {
        GF s = 0;
        for (int p = 0; p < nD; ++p)
            s ^= gf_mul(H->v[(size_t)i * nD + p], word[p]);
        if (s) return 0;
    }
    return 1;
}

/* ============================================================
 * Syndrome
 * ============================================================ */

static void compute_syndrome(const EvalBasis *A, const EvalBasis *B,
                             const GF *received, GF *S, GF *tmp)
{
    int k1 = A->count, k2 = B->count;

    for (int i = 0; i < k1; ++i) {
        for (int p = 0; p < nD; ++p)
            tmp[p] = gf_mul(received[p], A->v[(size_t)i * nD + p]);

        for (int j = 0; j < k2; ++j) {
            GF s = 0;
            for (int p = 0; p < nD; ++p)
                s ^= gf_mul(tmp[p], B->v[(size_t)j * nD + p]);
            S[(size_t)i * k2 + j] = s;
        }
    }
}

/* ============================================================
 * Solve Mx=b by incremental Gaussian elimination.
 *
 * 戻り値1: 一意解あり
 * 戻り値0: 不整合、または解が一意でない
 * ============================================================ */

static int solve_unique(const GF *M, const GF *b,
                        int rows, int cols, GF *x)
{
    int cap = rows < cols ? rows : cols;

    RowSpace rs;
    if (!rs_init(&rs, cap, cols))
        return 0;

    GF *brhs = calloc((size_t)(cap ? cap : 1), 1);
    if (!brhs) {
        rs_free(&rs);
        return 0;
    }

    int consistent = 1;

    for (int i = 0; i < rows; ++i) {
        memcpy(rs.w, M + (size_t)i * cols, (size_t)cols);
        GF value = b[i];

        /* 既存ピボットで係数と右辺を同時に消去 */
        for (int r = 0; r < rs.nrows; ++r) {
            int p = rs.piv[r];
            GF f = rs.w[p];
            if (!f) continue;

            const GF *e = rs.echelon + (size_t)r * cols;
            for (int j = p; j < cols; ++j)
                rs.w[j] ^= gf_mul(f, e[j]);

            value ^= gf_mul(f, brhs[r]);
        }

        int p = 0;
        while (p < cols && !rs.w[p]) ++p;

        if (p == cols) {
            if (value) consistent = 0;
            continue;
        }

        if (rs.nrows >= cap) {
            consistent = 0;
            continue;
        }

        /* ピボットを1に正規化 */
        GF inv = gf_inv(rs.w[p]);
        for (int j = p; j < cols; ++j)
            rs.w[j] = gf_mul(rs.w[j], inv);
        value = gf_mul(value, inv);

        /* ピボット列の昇順位置に挿入 */
        int pos = 0;
        while (pos < rs.nrows && rs.piv[pos] < p)
            ++pos;

        if (pos < rs.nrows) {
            memmove(rs.echelon + (size_t)(pos + 1) * cols,
                    rs.echelon + (size_t)pos * cols,
                    (size_t)(rs.nrows - pos) * cols);
            memmove(rs.piv + pos + 1, rs.piv + pos,
                    (size_t)(rs.nrows - pos) * sizeof(int));
            memmove(brhs + pos + 1, brhs + pos,
                    (size_t)(rs.nrows - pos) * sizeof(GF));
        }

        memcpy(rs.echelon + (size_t)pos * cols, rs.w, (size_t)cols);
        rs.piv[pos] = p;
        brhs[pos] = value;
        ++rs.nrows;
    }

    int good = consistent && rs.nrows == cols;

    if (good) {
        memset(x, 0, (size_t)cols);

        for (int r = rs.nrows - 1; r >= 0; --r) {
            int p = rs.piv[r];
            const GF *e = rs.echelon + (size_t)r * cols;
            GF v = brhs[r];

            for (int j = p + 1; j < cols; ++j)
                v ^= gf_mul(e[j], x[j]);

            x[p] = v;
        }
    }

    free(brhs);
    rs_free(&rs);
    return good;
}

/* ============================================================
 * Decoder
 * ============================================================ */

static int decode(const EvalBasis *A, const EvalBasis *B, const GF *S,
                  int maxnc, GF *error_vec, int *nerr)
{
    int k1 = A->count, k2 = B->count;

    memset(error_vec, 0, (size_t)nD);
    *nerr = 0;

    int allzero = 1;
    for (int i = 0; i < k1 * k2; ++i)
        if (S[i]) {
            allzero = 0;
            break;
        }
    if (allzero) return 1;

    /* S^T の右核 */
    GF *ST = malloc((size_t)k2 * k1);
    if (!ST) return 0;

    for (int i = 0; i < k1; ++i)
        for (int j = 0; j < k2; ++j)
            ST[(size_t)j * k1 + i] = S[(size_t)i * k2 + j];

    int dim = 0;
    GF *ker = nullspace(ST, k2, k1, &dim);
    free(ST);

    if (g_verbose)
        fprintf(stderr, "kernel dim=%d (A.count=%d)\n", dim, k1);

    if (!ker || dim == 0) {
        free(ker);
        return 0;
    }

    /* 核の関数すべての共通零点 */
    int *cand = malloc((size_t)nD * sizeof(int));
    if (!cand) {
        free(ker);
        return 0;
    }

    int nc = 0;
    for (int p = 0; p < nD; ++p) {
        int common_zero = 1;

        for (int v = 0; v < dim && common_zero; ++v) {
            GF z = 0;
            for (int i = 0; i < k1; ++i)
                z ^= gf_mul(ker[(size_t)v * k1 + i],
                            A->v[(size_t)i * nD + p]);
            if (z) common_zero = 0;
        }

        if (common_zero)
            cand[nc++] = p;
    }
    free(ker);

    if (g_verbose)
        fprintf(stderr, "candidates nc=%d (limit %d)\n", nc, maxnc);

    if (nc == 0 || nc > maxnc) {
        free(cand);
        return 0;
    }

    /* M e = S を構成 */
    int rows = k1 * k2;
    GF *M = calloc((size_t)rows * nc, 1);
    GF *rhs = malloc((size_t)rows);
    GF *solution = calloc((size_t)nc, 1);

    if (!M || !rhs || !solution) {
        free(M);
        free(rhs);
        free(solution);
        free(cand);
        return 0;
    }

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {
            int r = i * k2 + j;
            rhs[r] = S[(size_t)i * k2 + j];

            for (int c = 0; c < nc; ++c) {
                int p = cand[c];
                M[(size_t)r * nc + c] =
                    gf_mul(A->v[(size_t)i * nD + p],
                           B->v[(size_t)j * nD + p]);
            }
        }
    }

    int good = solve_unique(M, rhs, rows, nc, solution);

    if (good) {
        for (int c = 0; c < nc; ++c) {
            error_vec[cand[c]] = solution[c];
            if (solution[c]) ++*nerr;
        }

        /* シンドロームを再構成して検証 */
        for (int i = 0; i < k1 && good; ++i) {
            for (int j = 0; j < k2 && good; ++j) {
                GF check = 0;

                for (int c = 0; c < nc; ++c) {
                    int p = cand[c];
                    if (!solution[c]) continue;

                    check ^= gf_mul(solution[c],
                        gf_mul(A->v[(size_t)i * nD + p],
                               B->v[(size_t)j * nD + p]));
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

    free(M);
    free(rhs);
    free(solution);
    free(cand);
    return good;
}

/* ============================================================
 * Command line
 * ============================================================ */

static int parse_int(const char *s, int *v)
{
    char *e = NULL;
    long x = strtol(s, &e, 10);

    if (!s[0] || !e || *e || x < 0 || x > 1000000)
        return 0;

    *v = (int)x;
    return 1;
}

static double now(void)
{
    return (double)clock() / CLOCKS_PER_SEC;
}

int main(int argc, char **argv)
{
    int da = 2, db = 2, errors = 1, trials = 1, seed = 1;
    int auto_mode = 0, margin = 0;
    int hm = 6;
    const char *cname = "cc";

    for (int i = 1; i < argc; ++i) {
        int *dst = NULL;

        if (!strcmp(argv[i], "--curve")) {
            if (++i >= argc) {
                fprintf(stderr, "missing curve name\n");
                return 2;
            }
            cname = argv[i];
            continue;
        } else if (!strcmp(argv[i], "--verbose")) {
            g_verbose = 1;
            continue;
        } else if (!strcmp(argv[i], "--full")) {
            g_full = 1;
            continue;
        } else if (!strcmp(argv[i], "--auto")) {
            auto_mode = 1;
            continue;
        } else if (!strcmp(argv[i], "--w2")) { 
            g_w2 = 1;  
            continue;
        }
        else if (!strcmp(argv[i], "--pole")) dst = &g_pole;

        else if (!strcmp(argv[i], "--margin")) dst = &margin;
        else if (!strcmp(argv[i], "--m")) dst = &hm;
        else if (!strcmp(argv[i], "--da")) dst = &da;
        else if (!strcmp(argv[i], "--db")) dst = &db;
        else if (!strcmp(argv[i], "--errors")) dst = &errors;
        else if (!strcmp(argv[i], "--trials")) dst = &trials;
        else if (!strcmp(argv[i], "--seed")) dst = &seed;
        else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            printf("Usage: %s --curve NAME [--m N] [--da N] [--db N]\n"
                   "          [--errors N] [--trials N] [--seed N]\n"
                   "          [--auto [--margin N]] [--full] [--verbose]\n",
                   argv[0]);
            printf("Curves:");
            for (int k = 0; k < NCURVES; ++k)
                printf(" %s", CURVES[k].name);
            printf("\n");
            return 0;
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            return 2;
        }

        if (i + 1 >= argc || !parse_int(argv[++i], dst)) {
            fprintf(stderr, "Invalid option value\n");
            return 2;
        }
    }

    if (da > max_deg() || db > max_deg() ||
        errors < 0 || trials < 1) {
        fprintf(stderr, "Invalid parameters (da, db <= %d).\n",
                MK_MAXDEG);
        return 2;
    }

    const CurveDef *c = find_curve(cname);
    if (!c) {
        fprintf(stderr, "Unknown curve: %s (use --help)\n", cname);
        return 2;
    }
    cur_local = *c;
    if (g_w2 && !mk2_init(g_pole)) {
    fprintf(stderr, "mkbase2: この曲線には一点基底がありません\n");
    return 1;
    }
    
    if (!strcmp(cname, "he")) {
        static const unsigned P[9] =
            {0,0,0x07,0x0B,0x13,0x25,0x43,0x89,0x11D};

        if (hm % 2 || hm < 2 || hm > 8) {
            fprintf(stderr, "--m must be even, 2..8\n");
            return 2;
        }

        unsigned q = 1u << (hm / 2);
        unsigned short h[3][4] = {
            {(unsigned short)(q + 1),0,0,1},
            {0,(unsigned short)q,0,1},
            {0,1,0,1}
        };

        memcpy(he_buf, h, sizeof h);
        cur_local.m = hm;
        cur_local.poly = P[hm];
    }

    curve = &cur_local;
    if (g_w2 && !mk2_init(g_pole)) {
        fprintf(stderr, "mkbase2: この曲線には一点基底がありません\n");
        return 1;
    }
    if (!gf_init(curve->m, curve->poly)) {
        fprintf(stderr, "GF(2^%d) init failed for polynomial 0x%X\n",
                curve->m, curve->poly);
        return 1;
    }

    double t0 = now();
    nD = enumerate_points();
    if (g_w2) nD = mk2_filter_points();
    
    if (nD <= 0) {
        fprintf(stderr, "Point enumeration failed\n");
        return 1;
    }

    fprintf(stderr, "[time] points: %.2fs\n", now() - t0);

    if (errors > nD) {
        fprintf(stderr, "errors > n\n");
        free(D);
        return 2;
    }

    printf("Curve %s over GF(%d)\nF(x,y) =", cname, Q);
    for (int i = 0; i < curve->nterms; ++i)
        printf("%s%u*x^%u*y^%u", i ? " + " : " ",
               curve->t[i][3], curve->t[i][0], curve->t[i][1]);

    printf("\nAffine rational points: %d\n", nD);

    int need_a = errors + 2 + margin;
    int need_b = errors + margin;

    if (auto_mode) {
        da = db = -1;

        for (int d = 0; d <= max_deg(); ++d) {
            if (da < 0 && basis_count(d) >= need_a) da = d;
            if (db < 0 && basis_count(d) >= need_b) db = d;
        }

        if (da < 0 || db < 0) {
            fprintf(stderr,
                    "errors=%d (margin %d) is too large: "
                    "A.count is at most %d for da <= %d\n",
                    errors, margin, basis_count(max_deg()),
                    max_deg());
            free(D);
            return 2;
        }
    }

    EvalBasis A = {0}, B = {0}, H = {0};
    int xa, xb;

    t0 = now();

    for (;;) {
        free_basis(&A);
        free_basis(&B);
        free_basis(&H);

        xa = basis_xmax(da);
        xb = basis_xmax(db);
        
        if (g_w2) mk2_set_shift(da, db);
        if (!build_ab_basis(da, &A) ||
            !build_ab_basis(db, &B) ||
            !build_h_basis(da , db, xa , xb, &H)) {
            fprintf(stderr, "Basis construction failed.\n");
            free_basis(&A);
            free_basis(&B);
            free_basis(&H);
            free(D);
            return 1;
        }

        if (!auto_mode) break;

        int short_a = A.count < need_a;
        int short_b = B.count < need_b;

        if (!short_a && !short_b) break;

        if (short_a) ++da;
        if (short_b) ++db;

        if (da > max_deg() || db > max_deg()) {
            fprintf(stderr, "auto: da/db would exceed %d\n",
                    max_deg());
            free_basis(&A);
            free_basis(&B);
            free_basis(&H);
            free(D);
            return 2;
        }
    }

    fprintf(stderr, "[time] basis: %.2fs\n", now() - t0);

    if (auto_mode)
        printf("auto: errors=%d margin=%d -> da=%d db=%d\n",
               errors, margin, da, db);

    printf("A basis: %d independent monomials "
           "(total degree <= %d, x <= %d)\n", A.count, da, xa);
    printf("B basis: %d independent monomials "
           "(total degree <= %d, x <= %d)\n", B.count, db, xb);
    printf("H basis: %d independent products; C = H^perp\n",
           H.count);
    printf("Code length n=%d; parity-check rank=%d; dimension k=%d\n",
           nD, H.count, nD - H.count);

    CodeGen cg = {0};

    GF *cw = malloc((size_t)nD);
    GF *received = malloc((size_t)nD);
    GF *decoded = malloc((size_t)nD);
    GF *error_vec = calloc((size_t)nD, 1);
    GF *injected = calloc((size_t)nD, 1);
    GF *tmp = malloc((size_t)nD);
    GF *S = calloc((size_t)A.count * B.count, 1);
    int *order = malloc((size_t)nD * sizeof(int));

    if (!cw || !received || !decoded || !error_vec ||
        !injected || !tmp || !S || !order) {
        fprintf(stderr, "Allocation failed\n");
        free(cw); free(received); free(decoded);
        free(error_vec); free(injected); free(tmp);
        free(S); free(order);
        free_basis(&A); free_basis(&B); free_basis(&H);
        free(D);
        return 1;
    }

    t0 = now();

    if (!codegen_init(&cg, &H)) {
        fprintf(stderr, "Code generator allocation failed\n");
        free(cw); free(received); free(decoded);
        free(error_vec); free(injected); free(tmp);
        free(S); free(order);
        free_basis(&A); free_basis(&B); free_basis(&H);
        free(D);
        return 1;
    }

    fprintf(stderr, "[time] codegen: %.2fs\n", now() - t0);

    uint64_t rng =
        (uint64_t)(unsigned)seed + 0x123456789abcdefULL;

    int success = 0, fail = 0, miscorrect = 0;
    double t_dec = 0;

    for (int tr = 0; tr < trials; ++tr) {
        memset(injected, 0, (size_t)nD);

        random_codeword(&cg, cw, &rng);

        if (!in_code(&H, cw)) {
            fprintf(stderr,
                    "Could not construct a codeword in ker(H)\n");
            codegen_free(&cg);
            free(cw); free(received); free(decoded);
            free(error_vec); free(injected); free(tmp);
            free(S); free(order);
            free_basis(&A); free_basis(&B); free_basis(&H);
            free(D);
            return 1;
        }

        memcpy(received, cw, (size_t)nD);

        for (int p = 0; p < nD; ++p)
            order[p] = p;

        for (int e = 0; e < errors; ++e) {
            int j = e + (int)(rng_next(&rng) %
                              (uint64_t)(nD - e));

            int t = order[e];
            order[e] = order[j];
            order[j] = t;

            GF value = (GF)(1 + rng_next(&rng) %
                            (uint64_t)(Q - 1));

            received[order[e]] ^= value;
            injected[order[e]] ^= value;
        }

        compute_syndrome(&A, &B, received, S, tmp);

        double t1 = now();
        int recovered = 0;
        int ok = decode(&A, &B, S, H.count,
                        error_vec, &recovered);
        t_dec += now() - t1;

        int mismatch = 0;

        for (int p = 0; p < nD; ++p) {
            if (injected[p] != error_vec[p]) {
                if (trials == 1)
                    printf("MISMATCH position=%d "
                           "injected=0x%02X decoded=0x%02X\n",
                           p, injected[p], error_vec[p]);
                ++mismatch;
            }
        }

        memcpy(decoded, received, (size_t)nD);
        for (int p = 0; p < nD; ++p)
            decoded[p] ^= error_vec[p];

        int same = ok && memcmp(cw, decoded, (size_t)nD) == 0;

        if (same) ++success;
        else if (ok) ++miscorrect;
        else ++fail;

        if (trials == 1) {
            printf("Mismatch positions/values: %d\n", mismatch);

            printf("\nInjected error locations and values:\n");
            for (int p = 0; p < nD; ++p)
                if (injected[p])
                    printf("  position=%d value=0x%02X\n",
                           p, injected[p]);

            printf("\nDecoded error locations and values:\n");
            for (int p = 0; p < nD; ++p)
                if (error_vec[p])
                    printf("  position=%d value=0x%02X\n",
                           p, error_vec[p]);

            printf("Trial: %s; injected errors=%d; "
                   "recovered nonzero corrections=%d\n",
                   same ? "PASS" :
                   (ok ? "MISCORRECTION" : "FAIL"),
                   errors, recovered);
        }
    }

    if (trials > 1)
        printf("Trials=%d: success=%d, miscorrection=%d, failure=%d\n",
               trials, success, miscorrect, fail);

    fprintf(stderr, "[time] decode total: %.2fs\n", t_dec);

    codegen_free(&cg);

    free(injected);
    free(cw);
    free(received);
    free(decoded);
    free(order);
    free(error_vec);
    free(tmp);
    free(S);

    free_basis(&A);
    free_basis(&B);
    free_basis(&H);
    free(D);

    return success == trials ? 0 : 1;
}