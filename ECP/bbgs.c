/*
 * BBGS / 一般化エルミート曲線
 * 評価符号と ECP 型復号器
 *
 * GF(2^m), m <= 8
 *
 * Build:
 *   cc -O2 -std=c11 -Wall -Wextra bbgs.c -o bbgs
 *
 * BBGS:
 *   ./bbgs --bbgs q a b --da 2 --db 2 --errors 1
 *
 * Existing curves:
 *   ./bbgs --curve cc --da 2 --db 2 --errors 1
 *
 * Options:
 *   --bbgs q a b
 *   --curve NAME
 *   --m N
 *   --da N
 *   --db N
 *   --errors N
 *   --trials N
 *   --seed N
 *   --auto
 *   --margin N
 *   --full
 *   --verbose
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>
#include <errno.h>

#define MAXQ 256
#define MAX_MONOMIALS 8192
#define BBGS_MAX_TERMS 256

typedef uint8_t GF;

/* ============================================================
 * BBGS curve generator
 * ============================================================ */

#define BBGS_V 3

static const GF *g_injected = NULL;   /* 検査用: 注入した誤り (任意) */

typedef struct {
    unsigned short n[BBGS_V];
    unsigned short a;
} mterm;

typedef struct {
    mterm x[BBGS_MAX_TERMS];
} MP;

static int pow_u64(uint64_t q, unsigned int n, uint64_t *r)
{
    uint64_t v = 1;

    for (unsigned int i = 0; i < n; ++i) {
        if (q && v > UINT64_MAX / q)
            return 0;
        v *= q;
    }

    *r = v;
    return 1;
}

static int get_characteristic(unsigned int q, unsigned int *p)
{
    if (q < 2 || !p)
        return 0;

    unsigned int prime = 0;

    for (unsigned int d = 2; d <= q / d; ++d) {
        if (q % d == 0) {
            prime = d;
            break;
        }
    }

    if (!prime)
        prime = q;

    unsigned int n = q;

    while (n % prime == 0)
        n /= prime;

    if (n != 1)
        return 0;

    *p = prime;
    return 1;
}

static unsigned int gcd_int(unsigned int a, unsigned int b)
{
    while (b) {
        unsigned int r = a % b;
        a = b;
        b = r;
    }

    return a;
}

static int generate_bbgs_curve(
    unsigned int q,
    unsigned int a,
    unsigned int b,
    MP *curve_out)
{
    if (!curve_out || q < 2 || a == 0 || b == 0)
        return 0;

    if (a > UINT_MAX - b)
        return 0;

    unsigned int p;

    if (!get_characteristic(q, &p))
        return 0;

    unsigned int c = a + b;

    if (gcd_int(a, b) != 1)
        return 0;

    if (c >= BBGS_MAX_TERMS)
        return 0;

    uint64_t qpower;  // degree of bbgs curve

    if (!pow_u64(q, c-1, &qpower))
        return 0;

    if (qpower > USHRT_MAX)
        return 0;

    memset(curve_out, 0, sizeof(*curve_out));

    unsigned int t = 0;
    uint64_t xq, yq;

    /*
     * 第1群:
     *
     * x^(Q-q^i) y^(q^(a+i))
     *
     * i = 0,...,b-1
     */

    for (unsigned int i = 0; i < b; ++i) {
        if (!pow_u64(q, i, &xq) ||
            !pow_u64(q, a + i, &yq))
            return 0;

        if (xq > qpower || yq > USHRT_MAX)
            return 0;

        curve_out->x[t].n[0] =
            (unsigned short)(qpower - xq);
        curve_out->x[t].n[1] = (unsigned short)yq;
        curve_out->x[t].n[2] = 0;
        curve_out->x[t].a = 1;

        ++t;
    }

    /*
     * 第2群:
     *
     * x^(Q-q^(b+i)) y^(q^i)
     *
     * i = 0,...,a-1
     */

    for (unsigned int i = 0; i < a; ++i) {
        if (!pow_u64(q, b + i, &xq) ||
            !pow_u64(q, i, &yq))
            return 0;

        if (xq > qpower || yq > USHRT_MAX)
            return 0;

        curve_out->x[t].n[0] =
            (unsigned short)(qpower - xq);
        curve_out->x[t].n[1] = (unsigned short)yq;
        curve_out->x[t].n[2] = 0;
        curve_out->x[t].a = 1;

        ++t;
    }

    /*
     * 最終項:
     *
     * -x^Q
     */

    curve_out->x[t].n[0] = (unsigned short)qpower;
    curve_out->x[t].n[1] = 0;
    curve_out->x[t].n[2] = 0;
    curve_out->x[t].a = (unsigned short)(p - 1);

    ++t;

    return (int)t;
}

/* ============================================================
 * Existing curve definitions
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
    {7,4,0,1}, {6,8,0,1}, {4,1,0,1},
    {0,2,0,1}, {8,0,0,1}
};

static const unsigned short ku3[5][4] = {
    {0,5,0,1}, {12,0,0,1}, {9,0,0,1},
    {6,0,0,1}, {3,0,0,1}
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
    {24,1,0,1}, {16,2,0,1}, {0,4,0,1},
    {32,0,0,1}
};

static const unsigned short ku2[4][4] = {
    {0,9,0,1}, {4,0,0,1}, {2,0,0,1}, {1,0,0,1}
};

static const unsigned short ku4[5][4] = {
    {0,9,0,1}, {40,0,0,1}, {33,0,0,1},
    {12,0,0,1}, {5,0,0,1}
};

static const unsigned short ku5[3][4] = {
    {0,9,0,1}, {2,0,0,1}, {1,0,0,1}
};

static const unsigned short cc[8][4] = {
    {63,8,0,1}, {62,16,0,1}, {60,32,0,1},
    {56,64,0,1}, {48,1,0,1}, {32,2,0,1},
    {0,4,0,1}, {64,0,0,1}
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
    {0,17,0,1}, {8,0,0,1}, {4,0,0,1},
    {2,0,0,1}, {1,0,0,1}
};

static const unsigned short el[4][4] = {
    {0,2,1,1}, {1,1,1,1}, {3,0,0,1}, {0,0,3,1}
};

static const unsigned short el2[5][4] = {
    {0,2,1,1}, {1,1,1,1}, {3,0,0,1},
    {0,0,3,1}, {2,0,1,1}
};

static unsigned short he_buf[3][4];
static unsigned short bbgs_buf[BBGS_MAX_TERMS][4];

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

static int g_verbose = 0;
static int g_full = 0;
static int g_show_poly = 0;
static int g_slow_syn = 0;
static int g_zero_cw = 0;

static const CurveDef *find_curve(const char *name)
{
    for (int i = 0; i < NCURVES; ++i)
        if (!strcmp(CURVES[i].name, name))
            return &CURVES[i];

    return NULL;
}

/*
 * BBGS生成結果を CurveDef に接続する。
 *
 * q は基礎体の位数。
 * Q = q^(a+b) が実際の有限体の位数。
 *
 * 現在の有限体演算は標数2なので q=2^r に限定。
 * Q <= 256 に限定。
 */

static int make_bbgs_curve(
    unsigned int q,
    unsigned int a,
    unsigned int b,
    CurveDef *out)
{
    if (!out)
        return 0;

    if (q < 2 || (q & (q - 1)) != 0)
        return 0;

    unsigned int p;

    if (!get_characteristic(q, &p) || p != 2)
        return 0;

    MP mp;

    int n = generate_bbgs_curve(q, a, b, &mp);

    if (n <= 0 || n > BBGS_MAX_TERMS)
        return 0;

    unsigned int c = a + b;
    uint64_t qpower;

    if (!pow_u64(q, c, &qpower)) // field_size
        return 0;

    if (qpower > MAXQ)
        return 0;

    /*
     * Q は2のべき乗でなければならない。
     * m = log2(Q)
     */

    unsigned int v = (unsigned int)qpower;
    int m = 0;

    while (v > 1 && (v & 1u) == 0) {
        v >>= 1;
        ++m;
    }

    if (v != 1 || m < 1 || m > 8)
        return 0;

    static const unsigned poly_table[9] = {
        0x00,
        0x03,
        0x07,
        0x0B,
        0x13,
        0x25,
        0x43,
        0x89,
        0x11D
    };

    for (int i = 0; i < n; ++i) {
        bbgs_buf[i][0] = mp.x[i].n[0];
        bbgs_buf[i][1] = mp.x[i].n[1];
        bbgs_buf[i][2] = mp.x[i].n[2];
        bbgs_buf[i][3] = mp.x[i].a;
    }

    out->name = "bbgs";
    out->m = m;
    out->poly = poly_table[m];
    out->nterms = n;
    out->t = bbgs_buf;

    return 1;
}

static int curve_degree(void)
{
    int d = 0;

    for (int i = 0; i < curve->nterms; ++i) {
        int x = curve->t[i][0] + curve->t[i][1];
        if (x > d)
            d = x;
    }

    return d;
}

/* ============================================================
 * GF(2^m)
 * ============================================================ */

static int gQ = 128;
static unsigned gpoly = 0x89;

#define Q gQ

static GF expt[2 * (MAXQ - 1)];
static int logt[MAXQ];
static GF mt[MAXQ][MAXQ];

static GF gf_mul_slow(GF a, GF b)
{
    unsigned x = a;
    unsigned y = b;
    unsigned r = 0;

    while (y) {
        if (y & 1u)
            r ^= x;

        y >>= 1;
        x <<= 1;

        if (x & (unsigned)Q)
            x ^= gpoly;
    }

    return (GF)(r & (unsigned)(Q - 1));
}

static int gf_init(int m, unsigned poly)
{
    if (m < 1 || m > 8)
        return 0;

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

    if (x != 1)
        return 0;

    for (int i = Q - 1; i < 2 * (Q - 1); ++i)
        expt[i] = expt[i - (Q - 1)];

    for (int a = 0; a < Q; ++a) {
        for (int b = 0; b < Q; ++b) {
            mt[a][b] = (a && b)
                ? expt[logt[a] + logt[b]]
                : 0;
        }
    }

    return 1;
}

static inline GF gf_mul(GF a, GF b)
{
    return mt[a][b];
}

static inline GF gf_inv(GF a)
{
    return a ? expt[(Q - 1) - logt[a]] : 0;
}

static GF gf_pow(GF a, unsigned n)
{
    if (!n)
        return 1;

    if (!a)
        return 0;

    return expt[
        ((unsigned)logt[a] * (n % (unsigned)(Q - 1)))
        % (unsigned)(Q - 1)
    ];
}

/* ============================================================
 * Curve points
 * ============================================================ */

typedef struct {
    GF x, y;
} Point;

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

    if (!D)
        return 0;

    nD = 0;

    for (int x = 0; x < Q; ++x) {
        for (int y = 0; y < Q; ++y) {
            if (!eval_curve((GF)x, (GF)y)) {
                D[nD++] = (Point){(GF)x, (GF)y};
            }
        }
    }

    return nD;
}

/* ============================================================
 * Incremental row echelon basis
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

    s->echelon = calloc(
        (size_t)(cap ? cap : 1) * ncols, 1);

    s->piv = malloc(
        (size_t)(cap ? cap : 1) * sizeof(int));

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

/* 1: 独立行, 0: 従属, -1: 容量不足 */

static int rs_add(RowSpace *s, const GF *v)
{
    GF *w = s->w;

    memcpy(w, v, (size_t)s->ncols);

    for (int r = 0; r < s->nrows; ++r) {
        int p = s->piv[r];
        GF f = w[p];

        if (!f)
            continue;

        const GF *e =
            s->echelon + (size_t)r * s->ncols;

        for (int j = p; j < s->ncols; ++j)
            w[j] ^= gf_mul(f, e[j]);
    }

    int p = 0;

    while (p < s->ncols && !w[p])
        ++p;

    if (p == s->ncols)
        return 0;

    if (s->nrows >= s->cap)
        return -1;

    GF inv = gf_inv(w[p]);

    for (int j = p; j < s->ncols; ++j)
        w[j] = gf_mul(w[j], inv);

    int pos = 0;

    while (pos < s->nrows && s->piv[pos] < p)
        ++pos;

    if (pos < s->nrows) {
        memmove(
            s->echelon + (size_t)(pos + 1) * s->ncols,
            s->echelon + (size_t)pos * s->ncols,
            (size_t)(s->nrows - pos) * s->ncols);

        memmove(
            s->piv + pos + 1,
            s->piv + pos,
            (size_t)(s->nrows - pos) * sizeof(int));
    }

    memcpy(
        s->echelon + (size_t)pos * s->ncols,
        w,
        (size_t)s->ncols);

    s->piv[pos] = p;
    ++s->nrows;

    return 1;
}

/* ============================================================
 * Nullspace
 * ============================================================ */

static GF *nullspace(
    const GF *in,
    int rows,
    int cols,
    int *dim)
{
    RowSpace rs;

    if (!rs_init(&rs, rows, cols))
        return NULL;

    for (int i = 0; i < rows; ++i) {
        int r = rs_add(
            &rs,
            in + (size_t)i * cols);

        if (r < 0) {
            rs_free(&rs);
            return NULL;
        }
    }

    int rank = rs.nrows;

    *dim = cols - rank;

    GF *basis = calloc(
        (size_t)(*dim > 0 ? *dim : 1) * cols, 1);

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
        if (is_pivot[f])
            continue;

        GF *x = basis + (size_t)d * cols;

        x[f] = 1;

        for (int r = rank - 1; r >= 0; --r) {
            int p = rs.piv[r];

            const GF *e =
                rs.echelon + (size_t)r * cols;

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

static int build_basis_from_list(
    int (*lst)[2],
    int n,
    EvalBasis *out)
{
    memset(out, 0, sizeof(*out));

    if (n <= 0 || n > MAX_MONOMIALS)
        return 0;

    int xm = 0, ym = 0, maxdeg = 0;

    for (int k = 0; k < n; ++k) {
        if (lst[k][0] > xm)
            xm = lst[k][0];

        if (lst[k][1] > ym)
            ym = lst[k][1];

        if (lst[k][0] + lst[k][1] > maxdeg)
            maxdeg = lst[k][0] + lst[k][1];
    }

    int dF = curve_degree();

    int known =
        maxdeg < dF &&
        (long)nD > (long)maxdeg * dF;

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

    if (!xp || !yp || !row ||
        !out->v || !out->ex || !out->ey)
        ok = 0;

    if (ok && use_rs) {
        rs_ok = rs_init(&rs, n, nD);
        if (!rs_ok)
            ok = 0;
    }

    if (ok) {
        for (int p = 0; p < nD; ++p) {
            xp[p] = 1;
            yp[p] = 1;
        }

        for (int i = 1; i <= xm; ++i) {
            for (int p = 0; p < nD; ++p) {
                xp[(size_t)i * nD + p] =
                    gf_mul(
                        xp[(size_t)(i - 1) * nD + p],
                        D[p].x);
            }
        }

        for (int j = 1; j <= ym; ++j) {
            for (int p = 0; p < nD; ++p) {
                yp[(size_t)j * nD + p] =
                    gf_mul(
                        yp[(size_t)(j - 1) * nD + p],
                        D[p].y);
            }
        }

        int count = 0;

        for (int k = 0; k < n; ++k) {
            int i = lst[k][0];
            int j = lst[k][1];

            for (int p = 0; p < nD; ++p) {
                row[p] =
                    gf_mul(
                        xp[(size_t)i * nD + p],
                        yp[(size_t)j * nD + p]);
            }

            if (use_rs) {
                int added = rs_add(&rs, row);

                if (added < 0) {
                    ok = 0;
                    break;
                }

                if (!added)
                    continue;
            }

            memcpy(
                out->v + (size_t)count * nD,
                row,
                (size_t)nD);

            out->ex[count] = i;
            out->ey[count] = j;

            ++count;
        }

        out->count = count;
    }

    if (rs_ok)
        rs_free(&rs);

    free(xp);
    free(yp);
    free(row);

    if (!ok) {
        free_basis(out);
        return 0;
    }

    return 1;
}

static int build_monomial_basis(
    int degree,
    int xm,
    EvalBasis *out)
{
    if (xm > degree)
        xm = degree;

    int cap = 0;

    for (int i = 0; i <= xm; ++i)
        cap += degree - i + 1;

    if (cap > MAX_MONOMIALS) {
        memset(out, 0, sizeof(*out));
        return 0;
    }

    int (*lst)[2] =
        malloc((size_t)cap * sizeof(*lst));

    if (!lst) {
        memset(out, 0, sizeof(*out));
        return 0;
    }

    int n = 0;

    for (int d = 0; d <= degree; ++d) {
        for (int k = 0; k <= d; ++k) {
            if (d - k <= xm) {
                lst[n][0] = d - k;
                lst[n][1] = k;
                ++n;
            }
        }
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

    while (n < cnt &&
           bb[n][0] + bb[n][1] <= degree)
        ++n;

    return build_basis_from_list(bb, n, out);
}

static int mk_count(int degree)
{
    static int bb[MK_BBCAP][2];

    int cnt = mkbase(bb);
    int n = 0;

    while (n < cnt &&
           bb[n][0] + bb[n][1] <= degree)
        ++n;

    return n;
}

static int basis_count(int degree)
{
    return g_full
        ? (degree + 1) * (degree + 2) / 2
        : mk_count(degree);
}

static int build_ab_basis(int degree, EvalBasis *out)
{
    return g_full
        ? build_monomial_basis(degree, degree, out)
        : build_mk_basis(degree, out);
}

static int basis_xmax(int degree)
{
    return g_full
        ? degree
        : (MK_XMAX < degree ? MK_XMAX : degree);
}

/* ============================================================
 * Random generator
 * ============================================================ */

static uint64_t rng_next(uint64_t *s)
{
    uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);

    z = (z ^ (z >> 30)) *
        0xBF58476D1CE4E5B9ULL;

    z = (z ^ (z >> 27)) *
        0x94D049BB133111EBULL;

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
        if (rs_add(
                &rs,
                H->v + (size_t)i * nD) < 0) {
            rs_free(&rs);
            return 0;
        }
    }

    g->rank = rs.nrows;

    g->m = malloc((size_t)g->rank * nD);

    g->piv = malloc(
        (size_t)(g->rank ? g->rank : 1) * sizeof(int));

    g->isp = calloc((size_t)nD, 1);

    if (!g->m || !g->piv || !g->isp) {
        codegen_free(g);
        rs_free(&rs);
        return 0;
    }

    memcpy(g->m, rs.echelon,
           (size_t)g->rank * nD);

    memcpy(g->piv, rs.piv,
           (size_t)g->rank * sizeof(int));

    for (int r = 0; r < g->rank; ++r)
        g->isp[g->piv[r]] = 1;

    rs_free(&rs);

    return 1;
}

static void random_codeword(
    const CodeGen *g,
    GF *word,
    uint64_t *state)
{
    for (int p = 0; p < nD; ++p) {
        word[p] = g->isp[p]
            ? 0
            : (GF)(rng_next(state) & (uint64_t)(Q - 1));
    }

    for (int r = g->rank - 1; r >= 0; --r) {
        int p = g->piv[r];

        const GF *row =
            g->m + (size_t)r * nD;

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

        for (int p = 0; p < nD; ++p) {
            s ^= gf_mul(
                H->v[(size_t)i * nD + p],
                word[p]);
        }

        if (s)
            return 0;
    }

    return 1;
}

/* ============================================================
 * Syndrome
 * ============================================================ */

static void compute_syndrome_slow(
    const EvalBasis *A,
    const EvalBasis *B,
    const GF *received,
    GF *S,
    GF *tmp)
{
    int k1 = A->count;
    int k2 = B->count;

    for (int i = 0; i < k1; ++i) {
        for (int p = 0; p < nD; ++p) {
            tmp[p] = gf_mul(
                received[p],
                A->v[(size_t)i * nD + p]);
        }

        for (int j = 0; j < k2; ++j) {
            GF s = 0;

            for (int p = 0; p < nD; ++p) {
                s ^= gf_mul(
                    tmp[p],
                    B->v[(size_t)j * nD + p]);
            }

            S[(size_t)i * k2 + j] = s;
        }
    }
}
 /*
 * モーメント方式のシンドローム計算。
 * A_i = x^ex_i y^ey_i, B_j = x^fx_j y^fy_j (単項式) なので
 *   S[i][j] = m[ex_i+fx_j][ey_i+fy_j],
 *   m[u][v] = sum_p r_p x_p^u y_p^v
 * 異なる (u,v) だけ計算すればよい。
 */
static void compute_syndrome(
    const EvalBasis *A,
    const EvalBasis *B,
    const GF *received,
    GF *S,
    GF *tmp)
{
    if (g_slow_syn) {
        compute_syndrome_slow(A, B, received, S, tmp);
        return;
    }

    int k1 = A->count;
    int k2 = B->count;

    int maxu = 0, maxv = 0;

    for (int i = 0; i < k1; ++i) {
        if (A->ex[i] > maxu) maxu = A->ex[i];
        if (A->ey[i] > maxv) maxv = A->ey[i];
    }

    int bu = 0, bv = 0;

    for (int j = 0; j < k2; ++j) {
        if (B->ex[j] > bu) bu = B->ex[j];
        if (B->ey[j] > bv) bv = B->ey[j];
    }

    maxu += bu;
    maxv += bv;

    size_t NU = (size_t)maxu + 1;
    size_t NV = (size_t)maxv + 1;

    GF *xp = malloc(NU * nD);
    GF *yp = malloc(NV * nD);
    uint8_t *need = calloc(NU * NV, 1);
    GF *mom = calloc(NU * NV, 1);

    if (!xp || !yp || !need || !mom) {
        free(xp);
        free(yp);
        free(need);
        free(mom);
        compute_syndrome_slow(A, B, received, S, tmp);
        return;
    }

    /* x^u(p), y^v(p) の表 */

    for (int p = 0; p < nD; ++p) {
        xp[p] = 1;
        yp[p] = 1;
    }

    for (size_t u = 1; u < NU; ++u)
        for (int p = 0; p < nD; ++p)
            xp[u * nD + p] =
                gf_mul(xp[(u - 1) * nD + p], D[p].x);

    for (size_t v = 1; v < NV; ++v)
        for (int p = 0; p < nD; ++p)
            yp[v * nD + p] =
                gf_mul(yp[(v - 1) * nD + p], D[p].y);

    /* 必要な (u,v) に印をつける */

    for (int i = 0; i < k1; ++i)
        for (int j = 0; j < k2; ++j)
            need[(size_t)(A->ex[i] + B->ex[j]) * NV
                 + (size_t)(A->ey[i] + B->ey[j])] = 1;

    /* モーメントを計算 (tmp = r_p * y^v(p)) */

    for (size_t v = 0; v < NV; ++v) {
        int any = 0;

        for (size_t u = 0; u < NU && !any; ++u)
            any = need[u * NV + v];

        if (!any)
            continue;

        for (int p = 0; p < nD; ++p)
            tmp[p] = gf_mul(received[p], yp[v * nD + p]);

        for (size_t u = 0; u < NU; ++u) {
            if (!need[u * NV + v])
                continue;

            GF s = 0;

            for (int p = 0; p < nD; ++p)
                s ^= gf_mul(xp[u * nD + p], tmp[p]);

            mom[u * NV + v] = s;
        }
    }

    /* S を並べる */

    for (int i = 0; i < k1; ++i)
        for (int j = 0; j < k2; ++j)
            S[(size_t)i * k2 + j] =
                mom[(size_t)(A->ex[i] + B->ex[j]) * NV
                    + (size_t)(A->ey[i] + B->ey[j])];

    free(xp);
    free(yp);
    free(need);
    free(mom);
}
 

/* ============================================================
 * Solve Mx=b
 * ============================================================ */

static int solve_unique(
    const GF *M,
    const GF *b,
    int rows,
    int cols,
    GF *x)
{
    int cap = rows < cols ? rows : cols;

    RowSpace rs;

    if (!rs_init(&rs, cap, cols))
        return 0;

    GF *brhs = calloc(
        (size_t)(cap ? cap : 1), 1);

    if (!brhs) {
        rs_free(&rs);
        return 0;
    }

    int consistent = 1;

    for (int i = 0; i < rows; ++i) {
        memcpy(
            rs.w,
            M + (size_t)i * cols,
            (size_t)cols);

        GF value = b[i];

        for (int r = 0; r < rs.nrows; ++r) {
            int p = rs.piv[r];

            GF f = rs.w[p];

            if (!f)
                continue;

            const GF *e =
                rs.echelon + (size_t)r * cols;

            for (int j = p; j < cols; ++j)
                rs.w[j] ^= gf_mul(f, e[j]);

            value ^= gf_mul(f, brhs[r]);
        }

        int p = 0;

        while (p < cols && !rs.w[p])
            ++p;

        if (p == cols) {
            if (value)
                consistent = 0;

            continue;
        }

        if (rs.nrows >= cap) {
            consistent = 0;
            continue;
        }

        GF inv = gf_inv(rs.w[p]);

        for (int j = p; j < cols; ++j)
            rs.w[j] = gf_mul(rs.w[j], inv);

        value = gf_mul(value, inv);

        int pos = 0;

        while (pos < rs.nrows &&
               rs.piv[pos] < p)
            ++pos;

        if (pos < rs.nrows) {
            memmove(
                rs.echelon + (size_t)(pos + 1) * cols,
                rs.echelon + (size_t)pos * cols,
                (size_t)(rs.nrows - pos) * cols);

            memmove(
                rs.piv + pos + 1,
                rs.piv + pos,
                (size_t)(rs.nrows - pos) * sizeof(int));

            memmove(
                brhs + pos + 1,
                brhs + pos,
                (size_t)(rs.nrows - pos) * sizeof(GF));
        }

        memcpy(
            rs.echelon + (size_t)pos * cols,
            rs.w,
            (size_t)cols);

        rs.piv[pos] = p;
        brhs[pos] = value;

        ++rs.nrows;
    }

    int good = consistent && rs.nrows == cols;

    if (good) {
        memset(x, 0, (size_t)cols);

        for (int r = rs.nrows - 1; r >= 0; --r) {
            int p = rs.piv[r];

            const GF *e =
                rs.echelon + (size_t)r * cols;

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


/*
 * 誤り位置関数の表示。
 * ker は S^T の右核の基底 (dim 本、各 k1 成分)。
 * 各ベクトルは A の単項式 x^ex y^ey の係数列なので、
 * L(x,y) = sum_i ker[i] * x^ex[i] * y^ey[i] として出力する。
 * 係数は GF(2^m) の原始元 a (= 多項式 x) のべきで表す。
 */
static void print_locator_polys(
    const EvalBasis *A,
    const GF *ker,
    int dim)
{
    int k1 = A->count;

    printf("\nError locator functions "
           "(kernel of S^T, dim=%d; a = primitive element):\n",
           dim);

    for (int v = 0; v < dim; ++v) {
        printf("  L%d(x,y) =", v + 1);

        int first = 1;

        for (int i = 0; i < k1; ++i) {
            GF c = ker[(size_t)v * k1 + i];

            if (!c)
                continue;

            printf("%s", first ? " " : " + ");
            first = 0;

            int ex = A->ex[i];
            int ey = A->ey[i];
            int wrote = 0;

            if (c != 1) {
                printf("a^%d", logt[c]);
                wrote = 1;
            }

            if (ex) {
                printf("%sx", wrote ? "*" : "");
                if (ex > 1)
                    printf("^%d", ex);
                wrote = 1;
            }

            if (ey) {
                printf("%sy", wrote ? "*" : "");
                if (ey > 1)
                    printf("^%d", ey);
                wrote = 1;
            }

            if (!wrote)
                printf("1");
        }

        if (first)
            printf(" 0");

        printf("\n");
    }
}


/*
 * 誤り位置関数の零点を検査する。
 *  - 各 L_v が零になる点の数
 *  - 全 L_v の共通零点 (= 誤り位置の候補)
 *  - g_injected があれば、注入した誤り位置がすべて
 *    共通零点に含まれるかを判定する
 */
static void check_locator_zeros(
    const EvalBasis *A,
    const GF *ker,
    int dim)
{
    int k1 = A->count;
    int common = 0;
    int missed = 0;
    int injected_n = 0;

    for (int v = 0; v < dim; ++v) {
        int zeros = 0;

        for (int p = 0; p < nD; ++p) {
            GF z = 0;

            for (int i = 0; i < k1; ++i) {
                z ^= gf_mul(
                    ker[(size_t)v * k1 + i],
                    A->v[(size_t)i * nD + p]);
            }

            if (!z)
                ++zeros;
        }

        printf("  L%d: zeros at %d of %d points\n",
               v + 1, zeros, nD);
    }

    printf("  common zeros:");

    for (int p = 0; p < nD; ++p) {
        int allzero = 1;

        for (int v = 0; v < dim && allzero; ++v) {
            GF z = 0;

            for (int i = 0; i < k1; ++i) {
                z ^= gf_mul(
                    ker[(size_t)v * k1 + i],
                    A->v[(size_t)i * nD + p]);
            }

            if (z)
                allzero = 0;
        }

        if (allzero) {
            ++common;

            if (common <= 64)
                printf(" %d", p);
        }
    }

    if (common > 64)
        printf(" ... (%d in total)", common);
    else
        printf(" (%d in total)", common);

    printf("\n");

    if (g_injected) {
        for (int p = 0; p < nD; ++p) {
            if (!g_injected[p])
                continue;

            ++injected_n;

            int allzero = 1;

            for (int v = 0; v < dim && allzero; ++v) {
                GF z = 0;

                for (int i = 0; i < k1; ++i) {
                    z ^= gf_mul(
                        ker[(size_t)v * k1 + i],
                        A->v[(size_t)i * nD + p]);
                }

                if (z)
                    allzero = 0;
            }

            if (!allzero) {
                ++missed;
                printf("  NG: injected position %d "
                       "is NOT a common zero\n", p);
            }
        }

        printf("  check: %d of %d injected positions "
               "are common zeros -> %s\n",
               injected_n - missed, injected_n,
               missed ? "NG" : "OK");
    }
}

/* ============================================================
 * Decoder
 * ============================================================ */

static int decode(
    const EvalBasis *A,
    const EvalBasis *B,
    const GF *S,
    int maxnc,
    GF *error_vec,
    int *nerr)
{
    int k1 = A->count;
    int k2 = B->count;

    memset(error_vec, 0, (size_t)nD);
    *nerr = 0;

    int allzero = 1;

    for (int i = 0; i < k1 * k2; ++i) {
        if (S[i]) {
            allzero = 0;
            break;
        }
    }

    if (allzero)
        return 1;

    /* S^T の右核 */

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

    if (g_verbose) {
        fprintf(stderr,
                "kernel dim=%d (A.count=%d)\n",
                dim, k1);
    }
    if (g_show_poly){
        print_locator_polys(A, ker, dim);
        check_locator_zeros(A, ker, dim);
    }
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

            for (int i = 0; i < k1; ++i) {
                z ^= gf_mul(
                    ker[(size_t)v * k1 + i],
                    A->v[(size_t)i * nD + p]);
            }

            if (z)
                common_zero = 0;
        }

        if (common_zero)
            cand[nc++] = p;
    }

    free(ker);

    if (g_verbose) {
        fprintf(stderr,
                "candidates nc=%d (limit %d)\n",
                nc, maxnc);
    }

    if (nc == 0 || nc > maxnc) {
        free(cand);
        return 0;
    }

    /* M e = S */

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
                    gf_mul(
                        A->v[(size_t)i * nD + p],
                        B->v[(size_t)j * nD + p]);
            }
        }
    }

    int good = solve_unique(
        M, rhs, rows, nc, solution);

    if (good) {
        for (int c = 0; c < nc; ++c) {
            error_vec[cand[c]] = solution[c];

            if (solution[c])
                ++*nerr;
        }

        /* シンドローム再構成による検証 */

        for (int i = 0; i < k1 && good; ++i) {
            for (int j = 0; j < k2 && good; ++j) {
                GF check = 0;

                for (int c = 0; c < nc; ++c) {
                    int p = cand[c];

                    if (!solution[c])
                        continue;

                    check ^= gf_mul(
                        solution[c],
                        gf_mul(
                            A->v[(size_t)i * nD + p],
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
    errno = 0;

    long x = strtol(s, &e, 10);

    if (!s[0] || errno == ERANGE ||
        !e || *e || x < 0 || x > 1000000)
        return 0;

    *v = (int)x;

    return 1;
}

static int parse_uint(
    const char *s,
    unsigned int *v)
{
    char *e = NULL;

    if (!s[0] || s[0] == '-')
        return 0;

    errno = 0;

    unsigned long x = strtoul(s, &e, 10);

    if (errno == ERANGE || !e || *e ||
        x > UINT_MAX)
        return 0;

    *v = (unsigned int)x;

    return 1;
}

static double now(void)
{
    return (double)clock() / CLOCKS_PER_SEC;
}

/* ============================================================
 * Main
 * ============================================================ */

int main(int argc, char **argv)
{
    int da = 40;
    int db = 40;
    int errors = 1;
    int trials = 1;
    int seed = 1;

    int auto_mode = 0;
    int margin = 0;
    int hm = 6;

    int use_bbgs = 0;
    int curve_option = 0;

    unsigned int bq = 0;
    unsigned int ba = 0;
    unsigned int bb = 0;

    const char *cname = "cc";

    /* --------------------------------------------------------
     * Arguments
     * -------------------------------------------------------- */

    for (int i = 1; i < argc; ++i) {
        int *dst = NULL;

        if (!strcmp(argv[i], "--curve")) {
            if (++i >= argc) {
                fprintf(stderr, "missing curve name\n");
                return 2;
            }

            cname = argv[i];
            curve_option = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--bbgs")) {
            if (i + 3 >= argc) {
                fprintf(stderr,
                        "--bbgs requires q a b\n");
                return 2;
            }

            if (!parse_uint(argv[++i], &bq) ||
                !parse_uint(argv[++i], &ba) ||
                !parse_uint(argv[++i], &bb)) {
                fprintf(stderr,
                        "Invalid BBGS parameters\n");
                return 2;
            }

            use_bbgs = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--verbose")) {
            g_verbose = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--full")) {
            g_full = 1;
            continue;
        } 
        else if (!strcmp(argv[i], "--zero-cw")) {
            g_zero_cw = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--slow-syndrome")) {
            g_slow_syn = 1;
            continue;
        }
        else if (!strcmp(argv[i], "--poly")) {
            g_show_poly = 1;
            continue;
        }
        else if (!strcmp(argv[i], "--auto")) {
            auto_mode = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--margin"))
            dst = &margin;

        else if (!strcmp(argv[i], "--m"))
            dst = &hm;

        else if (!strcmp(argv[i], "--da"))
            dst = &da;

        else if (!strcmp(argv[i], "--db"))
            dst = &db;

        else if (!strcmp(argv[i], "--errors"))
            dst = &errors;

        else if (!strcmp(argv[i], "--trials"))
            dst = &trials;

        else if (!strcmp(argv[i], "--seed"))
            dst = &seed;

        else if (!strcmp(argv[i], "-h") ||
                 !strcmp(argv[i], "--help")) {

            printf(
                "Usage:\n"
                "  %s --curve NAME [options]\n"
                "  %s --bbgs q a b [options]\n\n"
                "Options:\n"
                "  --m N\n"
                "  --da N\n"
                "  --db N\n"
                "  --errors N\n"
                "  --trials N\n"
                "  --seed N\n"
                "  --auto [--margin N]\n"
                "  --full\n"
                "  --poly\n"
                "  --slow-syndrome\n"
                "  --verbose\n\n"
                "Curves:",
                argv[0], argv[0]);

            for (int k = 0; k < NCURVES; ++k)
                printf(" %s", CURVES[k].name);

            printf("\n");

            return 0;
        }

        else {
            fprintf(stderr,
                    "Unknown option: %s\n",
                    argv[i]);
            return 2;
        }

        if (i + 1 >= argc ||
            !parse_int(argv[++i], dst)) {
            fprintf(stderr,
                    "Invalid option value\n");
            return 2;
        }
    }

    if (use_bbgs && curve_option) {
        fprintf(stderr,
                "Use either --bbgs or --curve, not both.\n");
        return 2;
    }

    if (da > MK_MAXDEG ||
        db > MK_MAXDEG ||
        errors < 0 ||
        trials < 1 ||
        margin > MK_MAXDEG) {

        fprintf(stderr,
                "Invalid parameters (da, db <= %d).\n",
                MK_MAXDEG);

        return 2;
    }

    /* --------------------------------------------------------
     * Curve selection
     * -------------------------------------------------------- */

    if (use_bbgs) {
        if (!make_bbgs_curve(
                bq, ba, bb, &cur_local)) {

            fprintf(stderr,
                    "BBGS curve generation failed.\n"
                    "Requirements:\n"
                    "  q must be a power of 2\n"
                    "  gcd(a,b) must be 1\n"
                    "  Q=q^(a+b) must be <= 256\n"
                    "  a,b must be positive\n");

            return 2;
        }
    }

    else {
        const CurveDef *c = find_curve(cname);

        if (!c) {
            fprintf(stderr,
                    "Unknown curve: %s (use --help)\n",
                    cname);
            return 2;
        }

        cur_local = *c;
    }

    /* --------------------------------------------------------
     * Hermite curve
     * -------------------------------------------------------- */

    if (!use_bbgs && !strcmp(cname, "he")) {
        static const unsigned poly_table[9] = {
            0, 0, 0x07, 0x0B, 0x13,
            0x25, 0x43, 0x89, 0x11D
        };

        if (hm % 2 || hm < 2 || hm > 8) {
            fprintf(stderr,
                    "--m must be even, 2..8\n");
            return 2;
        }

        unsigned int q = 1u << (hm / 2);

        unsigned short h[3][4] = {
            {(unsigned short)(q + 1),0,0,1},
            {0,(unsigned short)q,0,1},
            {0,1,0,1}
        };

        memcpy(he_buf, h, sizeof(h));

        cur_local.m = hm;
        cur_local.poly = poly_table[hm];
    }

    curve = &cur_local;

    /* --------------------------------------------------------
     * Finite field
     * -------------------------------------------------------- */

    if (!gf_init(curve->m, curve->poly)) {
        fprintf(stderr,
                "GF(2^%d) init failed for polynomial 0x%X\n",
                curve->m, curve->poly);
        return 1;
    }

    /* --------------------------------------------------------
     * Enumerate affine points
     * -------------------------------------------------------- */

    double t0 = now();

    nD = enumerate_points();

    if (nD <= 0) {
        fprintf(stderr,
                "Point enumeration failed\n");
        free(D);
        return 1;
    }

    fprintf(stderr,
            "[time] points: %.2fs\n",
            now() - t0);

    if (errors > nD) {
        fprintf(stderr, "errors > n\n");
        free(D);
        return 2;
    }

    /* --------------------------------------------------------
     * Curve information
     * -------------------------------------------------------- */

    printf("Curve %s over GF(%d)\n",
           curve->name, Q);

    if (use_bbgs) {
        unsigned int c = ba + bb;
        uint64_t qpower = 0;

        pow_u64(bq, c, &qpower);

        printf("BBGS parameters:\n");
        printf("q = %u\n", bq);
        printf("a = %u\n", ba);
        printf("b = %u\n", bb);
        printf("c = %u\n", c);
        printf("Q = %llu\n",
               (unsigned long long)qpower);
    }

    printf("GF polynomial = 0x%X\n",
           curve->poly);

    printf("F(x,y) =");

    for (int i = 0; i < curve->nterms; ++i) {
        printf("%s%u*x^%u*y^%u",
               i ? " + " : " ",
               curve->t[i][3],
               curve->t[i][0],
               curve->t[i][1]);
    }

    printf("\nAffine rational points: %d\n", nD);

    /* --------------------------------------------------------
     * Automatic degree selection
     * -------------------------------------------------------- */

    int need_a = errors + 2 + margin;
    int need_b = errors + margin;

    if (auto_mode) {
        da = -1;
        db = -1;

        for (int d = 0; d <= MK_MAXDEG; ++d) {
            if (da < 0 && basis_count(d) >= need_a)
                da = d;

            if (db < 0 && basis_count(d) >= need_b)
                db = d;
        }

        if (da < 0 || db < 0) {
            fprintf(stderr,
                    "errors=%d (margin %d) is too large: "
                    "A.count is at most %d for da <= %d\n",
                    errors,
                    margin,
                    basis_count(MK_MAXDEG),
                    MK_MAXDEG);

            free(D);
            return 2;
        }
    }

    /* --------------------------------------------------------
     * Build A, B, H
     * -------------------------------------------------------- */

    EvalBasis A = {0};
    EvalBasis B = {0};
    EvalBasis H = {0};

    int xa, xb;

    t0 = now();

    for (;;) {
        free_basis(&A);
        free_basis(&B);
        free_basis(&H);

        xa = basis_xmax(da);
        xb = basis_xmax(db);

        if (!build_ab_basis(da, &A) ||
            !build_ab_basis(db, &B) ||
            !build_monomial_basis(
                da + db, xa + xb, &H)) {

            fprintf(stderr,
                    "Basis construction failed.\n");

            free_basis(&A);
            free_basis(&B);
            free_basis(&H);
            free(D);

            return 1;
        }

        if (!auto_mode)
            break;

        int short_a = A.count < need_a;
        int short_b = B.count < need_b;

        if (!short_a && !short_b)
            break;

        if (short_a)
            ++da;

        if (short_b)
            ++db;

        if (da > MK_MAXDEG ||
            db > MK_MAXDEG) {

            fprintf(stderr,
                    "auto: da/db would exceed %d\n",
                    MK_MAXDEG);

            free_basis(&A);
            free_basis(&B);
            free_basis(&H);
            free(D);

            return 2;
        }
    }

    fprintf(stderr,
            "[time] basis: %.2fs\n",
            now() - t0);

    if (auto_mode) {
        printf("auto: errors=%d margin=%d -> da=%d db=%d\n",
               errors, margin, da, db);
    }

    printf(
        "A basis: %d independent monomials "
        "(total degree <= %d, x <= %d)\n",
        A.count, da, xa);

    printf(
        "B basis: %d independent monomials "
        "(total degree <= %d, x <= %d)\n",
        B.count, db, xb);

    printf(
        "H basis: %d independent products; C = H^perp\n",
        H.count);

    printf(
        "Code length n=%d; parity-check rank=%d; dimension k=%d\n",
        nD, H.count, nD - H.count);

    /* --------------------------------------------------------
     * Allocate buffers
     * -------------------------------------------------------- */

    CodeGen cg = {0};

    GF *cw = malloc((size_t)nD);
    GF *received = malloc((size_t)nD);
    GF *decoded = malloc((size_t)nD);
    GF *error_vec = calloc((size_t)nD, 1);
    GF *injected = calloc((size_t)nD, 1);
    GF *tmp = malloc((size_t)nD);

    GF *S = calloc(
        (size_t)A.count * B.count, 1);

    int *order = malloc(
        (size_t)nD * sizeof(int));

    if (!cw || !received || !decoded ||
        !error_vec || !injected ||
        !tmp || !S || !order) {

        fprintf(stderr, "Allocation failed\n");

        free(cw);
        free(received);
        free(decoded);
        free(error_vec);
        free(injected);
        free(tmp);
        free(S);
        free(order);

        free_basis(&A);
        free_basis(&B);
        free_basis(&H);
        free(D);

        return 1;
    }

    /* --------------------------------------------------------
     * Code generator
     * -------------------------------------------------------- */

    t0 = now();
    if (!g_zero_cw) {
        /* 既存の codegen_init とその失敗処理、[time] codegen の表示 */
    if (!codegen_init(&cg, &H)) {
        fprintf(stderr,
                "Code generator allocation failed\n");
        }
        
        free(cw);
        free(received);
        free(decoded);
        free(error_vec);
        free(injected);
        free(tmp);
        free(S);
        free(order);

        free_basis(&A);
        free_basis(&B);
        free_basis(&H);
        free(D);

        return 1;
    }

    fprintf(stderr,
            "[time] codegen: %.2fs\n",
            now() - t0);

    /* --------------------------------------------------------
     * Trials
     * -------------------------------------------------------- */

    uint64_t rng =
        (uint64_t)(unsigned)seed +
        0x123456789abcdefULL;

    int success = 0;
    int fail = 0;
    int miscorrect = 0;

    double t_dec = 0;

    for (int tr = 0; tr < trials; ++tr) {
        memset(injected, 0, (size_t)nD);

        random_codeword(&cg, cw, &rng);

        if (!in_code(&H, cw)) {
            fprintf(stderr,
                    "Could not construct a codeword in ker(H)\n");

            codegen_free(&cg);

            free(cw);
            free(received);
            free(decoded);
            free(error_vec);
            free(injected);
            free(tmp);
            free(S);
            free(order);

            free_basis(&A);
            free_basis(&B);
            free_basis(&H);
            free(D);

            return 1;
        }

        memcpy(received, cw, (size_t)nD);

        for (int p = 0; p < nD; ++p)
            order[p] = p;

        for (int e = 0; e < errors; ++e) {
            int j = e + (int)(
                rng_next(&rng) % (uint64_t)(nD - e));

            int t = order[e];
            order[e] = order[j];
            order[j] = t;

            GF value = (GF)(
                1 + rng_next(&rng) % (uint64_t)(Q - 1));

            received[order[e]] ^= value;
            injected[order[e]] ^= value;
        }
        double ts = now();
        compute_syndrome(&A, &B, received, S, tmp);
        fprintf(stderr, "[time] syndrome: %.3fs\n", now() - ts);

        double t1 = now();

        int recovered = 0;

        int ok = decode(
            &A, &B, S,
            H.count,
            error_vec,
            &recovered);

        t_dec += now() - t1;

        int mismatch = 0;

        for (int p = 0; p < nD; ++p) {
            if (injected[p] != error_vec[p]) {
                if (trials == 1) {
                    printf(
                        "MISMATCH position=%d "
                        "injected=0x%02X decoded=0x%02X\n",
                        p,
                        injected[p],
                        error_vec[p]);
                }

                ++mismatch;
            }
        }

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
            printf(
                "Mismatch positions/values: %d\n",
                mismatch);

            printf(
                "\nInjected error locations and values:\n");

            for (int p = 0; p < nD; ++p) {
                if (injected[p]) {
                    printf(
                        "  position=%d value=0x%02X\n",
                        p, injected[p]);
                }
            }

            printf(
                "\nDecoded error locations and values:\n");

            for (int p = 0; p < nD; ++p) {
                if (error_vec[p]) {
                    printf(
                        "  position=%d value=0x%02X\n",
                        p, error_vec[p]);
                }
            }

            printf(
                "Trial: %s; injected errors=%d; "
                "recovered nonzero corrections=%d\n",
                same ? "PASS" :
                (ok ? "MISCORRECTION" : "FAIL"),
                errors,
                recovered);
        }
    }

    if (trials > 1) {
        printf(
            "Trials=%d: success=%d, miscorrection=%d, failure=%d\n",
            trials, success, miscorrect, fail);
    }

    fprintf(stderr,
            "[time] decode total: %.2fs\n",
            t_dec);

    /* --------------------------------------------------------
     * Cleanup
     * -------------------------------------------------------- */

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