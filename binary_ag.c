/*
 * BBGS / 一般化エルミート曲線
 * 評価符号と ECP 型復号器
 *
 * GF(2^m), m <= 8
 *
 * Build:
 *   cc -O3 -march=native -std=c11 -Wall -Wextra bbgs.c -o bbgs
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
 *   --zero-cw        符号語を全0にする (符号語生成を省略)
 *   --poly           誤り位置関数と零点検査を表示
 *   --slow-syndrome  従来のシンドローム計算 (比較用)
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

    uint64_t qpower;  /* 曲線の式の指数 Q = q^(c-1) (体の位数 q^c ではない) */

    if (!pow_u64(q, c - 1, &qpower))
        return 0;

    if (qpower > USHRT_MAX)
        return 0;

    memset(curve_out, 0, sizeof(*curve_out));

    unsigned int t = 0;
    uint64_t xq, yq;

    /* 第1群: x^(Q-q^i) y^(q^(a+i)), i = 0,...,b-1 */

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

    /* 第2群: x^(Q-q^(b+i)) y^(q^i), i = 0,...,a-1 */

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

    /* 最終項: -x^Q */

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
static int g_binary = 0;
static int g_binrank = 0;

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
 * 定義体の位数は q^(a+b)。曲線の式の指数は q^(a+b-1)。
 *
 * 現在の有限体演算は標数2なので q=2^r に限定。
 * q^(a+b) <= 256 に限定。
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
    uint64_t field_size;

    if (!pow_u64(q, c, &field_size))
        return 0;

    if (field_size > MAXQ)
        return 0;

    unsigned int v = (unsigned int)field_size;
    int m = 0;

    while (v > 1 && (v & 1u) == 0) {
        v >>= 1;
        ++m;
    }

    if (v != 1 || m < 1 || m > 8)
        return 0;

    static const unsigned poly_table[9] = {
        0x00, 0x03, 0x07, 0x0B, 0x13,
        0x25, 0x43, 0x89, 0x11D
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
 *
 * 最適化: 消去の内側ループでは係数 f が固定なので、
 * 乗算表の1行 mt[f] (256B) を引いて使う。
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
    const int ncols = s->ncols;

    memcpy(w, v, (size_t)ncols);

    for (int r = 0; r < s->nrows; ++r) {
        int p = s->piv[r];
        GF f = w[p];

        if (!f)
            continue;

        const GF *e = s->echelon + (size_t)r * ncols;
        const GF *mf = mt[f];

        for (int j = p; j < ncols; ++j)
            w[j] ^= mf[e[j]];
    }

    int p = 0;

    while (p < ncols && !w[p])
        ++p;

    if (p == ncols)
        return 0;

    if (s->nrows >= s->cap)
        return -1;

    const GF *mi = mt[gf_inv(w[p])];

    for (int j = p; j < ncols; ++j)
        w[j] = mi[w[j]];

    int pos = 0;

    while (pos < s->nrows && s->piv[pos] < p)
        ++pos;

    if (pos < s->nrows) {
        memmove(
            s->echelon + (size_t)(pos + 1) * ncols,
            s->echelon + (size_t)pos * ncols,
            (size_t)(s->nrows - pos) * ncols);

        memmove(
            s->piv + pos + 1,
            s->piv + pos,
            (size_t)(s->nrows - pos) * sizeof(int));
    }

    memcpy(
        s->echelon + (size_t)pos * ncols,
        w,
        (size_t)ncols);

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

    /* 高速版 (列選択 + LU): fast=1 のとき使う */
    int fast;
    const EvalBasis *H;
    int *pcol;          /* 選んだ独立列 (rank 個) */
    GF *lu;             /* rank x rank, 行入れ替え済みの LU */
    int *lperm;         /* 消去中の行入れ替え記録 */
    GF *udiag_inv;      /* U の対角の逆元 */
    GF *rhs;            /* 作業領域 (rank) */
} CodeGen;

static void codegen_free(CodeGen *g)
{
    free(g->m);
    free(g->piv);
    free(g->isp);
    free(g->pcol);
    free(g->lu);
    free(g->lperm);
    free(g->udiag_inv);
    free(g->rhs);
    memset(g, 0, sizeof(*g));
}

static int codegen_init_slow(CodeGen *g, const EvalBasis *H)
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

    g->m = malloc((size_t)(g->rank ? g->rank : 1) * nD);

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

static void random_codeword_slow(
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

/*
 * 高速な符号語生成。
 *  1. 列をランダムな順に調べ、H の独立な rank 列 (pivot 列) を選ぶ
 *  2. その rank x rank の部分行列 HP を LU 分解 (1回だけ)
 *  3. 符号語: pivot 以外の座標をランダムに決め、
 *       HP * w_P = H_F * w_F  を LU で解いて pivot 座標を求める
 * 行階段形を全長 n で作る従来法 (約 r^2 n / 2) より
 * 約 r^3 / 3 + 試行ごとに r n で済む。
 * 失敗 (行が従属など) のときは 0 を返し、従来法に切り替える。
 */
static int codegen_init_fast(CodeGen *g, const EvalBasis *H)
{
    memset(g, 0, sizeof(*g));

    const int r = H->count;

    if (r <= 0 || r > nD)
        return 0;

    int *perm = malloc((size_t)nD * sizeof(int));
    GF *col = malloc((size_t)r);
    int *sel = malloc((size_t)r * sizeof(int));
    RowSpace rs;

    if (!perm || !col || !sel || !rs_init(&rs, r, r)) {
        free(perm);
        free(col);
        free(sel);
        return 0;
    }

    /* 列の順序をランダムにする (固定の乱数。符号語の乱数とは独立) */

    uint64_t st = 0x5DEECE66DULL;

    for (int p = 0; p < nD; ++p)
        perm[p] = p;

    for (int p = nD - 1; p > 0; --p) {
        int j = (int)(rng_next(&st) % (uint64_t)(p + 1));
        int t = perm[p];
        perm[p] = perm[j];
        perm[j] = t;
    }

    int ns = 0;

    for (int t = 0; t < nD && ns < r; ++t) {
        int j = perm[t];

        for (int i = 0; i < r; ++i)
            col[i] = H->v[(size_t)i * nD + j];

        int res = rs_add(&rs, col);

        if (res < 0)
            break;

        if (res > 0)
            sel[ns++] = j;
    }

    rs_free(&rs);
    free(col);
    free(perm);

    if (ns < r) {
        free(sel);
        return 0;
    }

    /* HP[i][k] = H[i][sel[k]] を作り、LU 分解 */

    GF *lu = malloc((size_t)r * r);
    int *lperm = malloc((size_t)r * sizeof(int));
    GF *dinv = malloc((size_t)r);
    GF *rhs = malloc((size_t)r);
    uint8_t *isp = calloc((size_t)nD, 1);

    if (!lu || !lperm || !dinv || !rhs || !isp) {
        free(lu);
        free(lperm);
        free(dinv);
        free(rhs);
        free(isp);
        free(sel);
        return 0;
    }

    for (int i = 0; i < r; ++i)
        for (int k = 0; k < r; ++k)
            lu[(size_t)i * r + k] =
                H->v[(size_t)i * nD + sel[k]];

    int okLU = 1;

    for (int k = 0; k < r && okLU; ++k) {
        int p = k;

        while (p < r && !lu[(size_t)p * r + k])
            ++p;

        if (p == r) {
            okLU = 0;
            break;
        }

        lperm[k] = p;

        if (p != k) {
            GF *a = lu + (size_t)k * r;
            GF *b = lu + (size_t)p * r;

            for (int j = 0; j < r; ++j) {
                GF t = a[j];
                a[j] = b[j];
                b[j] = t;
            }
        }

        GF *rk = lu + (size_t)k * r;
        GF inv = gf_inv(rk[k]);
        const GF *mi = mt[inv];

        dinv[k] = inv;

        for (int i = k + 1; i < r; ++i) {
            GF *ri = lu + (size_t)i * r;

            if (!ri[k])
                continue;

            GF f = mi[ri[k]];     /* f = ri[k] / rk[k] */
            const GF *mf = mt[f];

            ri[k] = f;            /* L の要素を保存 */

            for (int j = k + 1; j < r; ++j)
                ri[j] ^= mf[rk[j]];
        }
    }

    if (!okLU) {
        free(lu);
        free(lperm);
        free(dinv);
        free(rhs);
        free(isp);
        free(sel);
        return 0;
    }

    for (int k = 0; k < r; ++k)
        isp[sel[k]] = 1;

    g->fast = 1;
    g->H = H;
    g->rank = r;
    g->pcol = sel;
    g->lu = lu;
    g->lperm = lperm;
    g->udiag_inv = dinv;
    g->rhs = rhs;
    g->isp = isp;

    return 1;
}

static void random_codeword_fast(
    const CodeGen *g,
    GF *word,
    uint64_t *state)
{
    const int r = g->rank;
    const EvalBasis *H = g->H;

    for (int p = 0; p < nD; ++p) {
        word[p] = g->isp[p]
            ? 0
            : (GF)(rng_next(state) & (uint64_t)(Q - 1));
    }

    /* rhs = H * word  (pivot 座標は 0 なので、自由座標の寄与だけ) */

    GF *b = g->rhs;

    for (int i = 0; i < r; ++i) {
        const GF *hi = H->v + (size_t)i * nD;
        GF s = 0;

        for (int j = 0; j < nD; ++j)
            s ^= mt[hi[j]][word[j]];

        b[i] = s;
    }

    /* 行の入れ替えを b に適用してから、前進代入 (L は単位下三角) */

    for (int k = 0; k < r; ++k) {
        int p = g->lperm[k];

        if (p != k) {
            GF t = b[k];
            b[k] = b[p];
            b[p] = t;
        }
    }

    for (int k = 0; k < r; ++k) {
        GF bk = b[k];

        if (!bk)
            continue;

        const GF *mb = mt[bk];

        for (int i = k + 1; i < r; ++i)
            b[i] ^= mb[g->lu[(size_t)i * r + k]];
    }

    /* 後退代入 (U) : x = U^-1 b。char 2 なので符号は不要 */

    for (int k = r - 1; k >= 0; --k) {
        const GF *rk = g->lu + (size_t)k * r;
        GF v = b[k];

        for (int j = k + 1; j < r; ++j)
            v ^= mt[rk[j]][word[g->pcol[j]]];

        word[g->pcol[k]] = mt[g->udiag_inv[k]][v];
    }
}

static int codegen_init(CodeGen *g, const EvalBasis *H)
{
    if (codegen_init_fast(g, H))
        return 1;

    codegen_free(g);

    if (g_verbose)
        fprintf(stderr, "codegen: fast method failed, using slow\n");

    return codegen_init_slow(g, H);
}

static void random_codeword(
    const CodeGen *g,
    GF *word,
    uint64_t *state)
{
    if (g->fast)
        random_codeword_fast(g, word, state);
    else
        random_codeword_slow(g, word, state);
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
 *
 * A_i = x^ex_i y^ey_i, B_j = x^fx_j y^fy_j (単項式) なので
 *   S[i][j] = m[ex_i+fx_j][ey_i+fy_j]
 *   m[u][v] = sum_p r_p x_p^u y_p^v
 * 異なる (u,v) だけ計算すればよい。
 * x^u(p), y^v(p) の表は A,B が同じ間は使い回す。
 * 受信語が疎 (--zero-cw のとき誤りの位置だけ非零) なら、
 * 非零位置だけを足し合わせる。
 * ============================================================ */

typedef struct {
    int ready;
    size_t NU, NV;
    GF *xp, *yp;
    uint8_t *need;      /* NU*NV */
    uint8_t *vany;      /* NV: その v に必要な (u,v) があるか */
    GF *mom;            /* NU*NV */
    int *pos;           /* 非零位置の一覧 (nD) */
} SynCache;

static SynCache g_syn;

static void syn_free(void)
{
    free(g_syn.xp);
    free(g_syn.yp);
    free(g_syn.need);
    free(g_syn.vany);
    free(g_syn.mom);
    free(g_syn.pos);
    memset(&g_syn, 0, sizeof(g_syn));
}

static int syn_prepare(const EvalBasis *A, const EvalBasis *B)
{
    syn_free();

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

    g_syn.NU = (size_t)maxu + 1;
    g_syn.NV = (size_t)maxv + 1;

    size_t NU = g_syn.NU;
    size_t NV = g_syn.NV;

    g_syn.xp = malloc(NU * nD);
    g_syn.yp = malloc(NV * nD);
    g_syn.need = calloc(NU * NV, 1);
    g_syn.vany = calloc(NV, 1);
    g_syn.mom = calloc(NU * NV, 1);
    g_syn.pos = malloc((size_t)nD * sizeof(int));

    if (!g_syn.xp || !g_syn.yp || !g_syn.need ||
        !g_syn.vany || !g_syn.mom || !g_syn.pos) {
        syn_free();
        return 0;
    }

    for (int p = 0; p < nD; ++p) {
        g_syn.xp[p] = 1;
        g_syn.yp[p] = 1;
    }

    for (size_t u = 1; u < NU; ++u)
        for (int p = 0; p < nD; ++p)
            g_syn.xp[u * nD + p] =
                gf_mul(g_syn.xp[(u - 1) * nD + p], D[p].x);

    for (size_t v = 1; v < NV; ++v)
        for (int p = 0; p < nD; ++p)
            g_syn.yp[v * nD + p] =
                gf_mul(g_syn.yp[(v - 1) * nD + p], D[p].y);

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {
            size_t u = (size_t)(A->ex[i] + B->ex[j]);
            size_t v = (size_t)(A->ey[i] + B->ey[j]);

            g_syn.need[u * NV + v] = 1;
            g_syn.vany[v] = 1;
        }
    }

    g_syn.ready = 1;

    return 1;
}

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

    if (!g_syn.ready && !syn_prepare(A, B)) {
        compute_syndrome_slow(A, B, received, S, tmp);
        return;
    }

    const size_t NU = g_syn.NU;
    const size_t NV = g_syn.NV;
    const int k1 = A->count;
    const int k2 = B->count;

    /* 非零位置 */

    int nnz = 0;

    for (int p = 0; p < nD; ++p)
        if (received[p])
            g_syn.pos[nnz++] = p;

    const int *pos = g_syn.pos;

    if ((long)nnz * 8 <= (long)nD) {
        /* 疎: tmp[k] = r * y^v を非零位置だけ作る */

        for (size_t v = 0; v < NV; ++v) {
            if (!g_syn.vany[v])
                continue;

            for (int k = 0; k < nnz; ++k)
                tmp[k] = gf_mul(
                    received[pos[k]],
                    g_syn.yp[v * nD + pos[k]]);

            for (size_t u = 0; u < NU; ++u) {
                if (!g_syn.need[u * NV + v])
                    continue;

                const GF *xr = g_syn.xp + u * nD;
                GF s = 0;

                for (int k = 0; k < nnz; ++k)
                    s ^= gf_mul(xr[pos[k]], tmp[k]);

                g_syn.mom[u * NV + v] = s;
            }
        }
    }
    else {
        /* 密 */

        for (size_t v = 0; v < NV; ++v) {
            if (!g_syn.vany[v])
                continue;

            const GF *yr = g_syn.yp + v * nD;

            for (int p = 0; p < nD; ++p)
                tmp[p] = gf_mul(received[p], yr[p]);

            for (size_t u = 0; u < NU; ++u) {
                if (!g_syn.need[u * NV + v])
                    continue;

                const GF *xr = g_syn.xp + u * nD;
                GF s = 0;

                for (int p = 0; p < nD; ++p)
                    s ^= gf_mul(xr[p], tmp[p]);

                g_syn.mom[u * NV + v] = s;
            }
        }
    }

    for (int i = 0; i < k1; ++i)
        for (int j = 0; j < k2; ++j)
            S[(size_t)i * k2 + j] =
                g_syn.mom[(size_t)(A->ex[i] + B->ex[j]) * NV
                          + (size_t)(A->ey[i] + B->ey[j])];
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
            const GF *mf = mt[f];

            for (int j = p; j < cols; ++j)
                rs.w[j] ^= mf[e[j]];

            value ^= mf[brhs[r]];
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

        const GF *mi = mt[gf_inv(rs.w[p])];

        for (int j = p; j < cols; ++j)
            rs.w[j] = mi[rs.w[j]];

        value = mi[value];

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

/* ============================================================
 * Locator functions: common zeros, display, check
 * ============================================================ */

/*
 * 核の全関数の共通零点を cand に入れて個数を返す。
 * v=0 の関数は A_i の行を連続アクセスして全点を評価し、
 * 残った候補だけ他の関数で確かめる。
 * z は長さ nD の作業領域。
 */
static int common_zeros(
    const EvalBasis *A,
    const GF *ker,
    int dim,
    int *cand,
    GF *z)
{
    const int k1 = A->count;

    memset(z, 0, (size_t)nD);

    for (int i = 0; i < k1; ++i) {
        GF c = ker[i];

        if (!c)
            continue;

        const GF *mf = mt[c];
        const GF *ap = A->v + (size_t)i * nD;

        for (int p = 0; p < nD; ++p)
            z[p] ^= mf[ap[p]];
    }

    int nc = 0;

    for (int p = 0; p < nD; ++p)
        if (!z[p])
            cand[nc++] = p;

    for (int v = 1; v < dim && nc > 0; ++v) {
        const GF *kv = ker + (size_t)v * k1;
        int m = 0;

        for (int c = 0; c < nc; ++c) {
            int p = cand[c];
            GF s = 0;

            for (int i = 0; i < k1; ++i)
                s ^= gf_mul(kv[i], A->v[(size_t)i * nD + p]);

            if (!s)
                cand[m++] = p;
        }

        nc = m;
    }

    return nc;
}

/*
 * 誤り位置関数の表示。
 * ker は S^T の右核の基底 (dim 本、各 k1 成分)。
 * L(x,y) = sum_i ker[i] * x^ex[i] * y^ey[i]
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
 * 零点の検査。
 *  - 各 L_v が零になる点の数
 *  - 共通零点 (cand, nc 個)
 *  - g_injected があれば、注入した誤り位置が共通零点に
 *    すべて含まれるか
 */
static void check_locator_zeros(
    const EvalBasis *A,
    const GF *ker,
    int dim,
    const int *cand,
    int nc)
{
    const int k1 = A->count;

    GF *z = malloc((size_t)nD);

    if (z) {
        for (int v = 0; v < dim; ++v) {
            memset(z, 0, (size_t)nD);

            for (int i = 0; i < k1; ++i) {
                GF c = ker[(size_t)v * k1 + i];

                if (!c)
                    continue;

                const GF *mf = mt[c];
                const GF *ap = A->v + (size_t)i * nD;

                for (int p = 0; p < nD; ++p)
                    z[p] ^= mf[ap[p]];
            }

            int zeros = 0;

            for (int p = 0; p < nD; ++p)
                if (!z[p])
                    ++zeros;

            printf("  L%d: zeros at %d of %d points\n",
                   v + 1, zeros, nD);
        }
    }

    free(z);

    printf("  common zeros:");

    for (int c = 0; c < nc && c < 64; ++c)
        printf(" %d", cand[c]);

    if (nc > 64)
        printf(" ... (%d in total)", nc);
    else
        printf(" (%d in total)", nc);

    printf("\n");

    if (g_injected) {
        uint8_t *is_common = calloc((size_t)nD, 1);

        if (!is_common)
            return;

        for (int c = 0; c < nc; ++c)
            is_common[cand[c]] = 1;

        int injected_n = 0;
        int missed = 0;

        for (int p = 0; p < nD; ++p) {
            if (!g_injected[p])
                continue;

            ++injected_n;

            if (!is_common[p]) {
                ++missed;

                if (missed <= 20)
                    printf("  NG: injected position %d "
                           "is NOT a common zero\n", p);
            }
        }

        printf("  check: %d of %d injected positions "
               "are common zeros -> %s\n",
               injected_n - missed, injected_n,
               missed ? "NG" : "OK");

        free(is_common);
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

    if (!ker || dim == 0) {
        free(ker);
        return 0;
    }

    /* 核の関数すべての共通零点 */

    int *cand = malloc((size_t)nD * sizeof(int));
    GF *zbuf = malloc((size_t)nD);

    if (!cand || !zbuf) {
        free(cand);
        free(zbuf);
        free(ker);
        return 0;
    }

    int nc = common_zeros(A, ker, dim, cand, zbuf);

    free(zbuf);

    if (g_show_poly) {
        print_locator_polys(A, ker, dim);
        check_locator_zeros(A, ker, dim, cand, nc);
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

    /*
     * M e = S
     * 行 (i,j) の係数は x^(ex_i+fx_j) y^(ey_i+fy_j) の評価で、
     * 右辺も同じ (u,v) のモーメントなので、(u,v) が同じ行は
     * 同一。代表行だけを使う。
     */

    int maxu = 0, maxv = 0, bu = 0, bv = 0;

    for (int i = 0; i < k1; ++i) {
        if (A->ex[i] > maxu) maxu = A->ex[i];
        if (A->ey[i] > maxv) maxv = A->ey[i];
    }

    for (int j = 0; j < k2; ++j) {
        if (B->ex[j] > bu) bu = B->ex[j];
        if (B->ey[j] > bv) bv = B->ey[j];
    }

    maxu += bu;
    maxv += bv;

    size_t NU = (size_t)maxu + 1;
    size_t NV = (size_t)maxv + 1;

    uint8_t *seen = calloc(NU * NV, 1);
    int *ri = malloc(NU * NV * sizeof(int));
    int *rj = malloc(NU * NV * sizeof(int));

    if (!seen || !ri || !rj) {
        free(seen);
        free(ri);
        free(rj);
        free(cand);
        return 0;
    }

    int rows = 0;

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {
            size_t key =
                (size_t)(A->ex[i] + B->ex[j]) * NV +
                (size_t)(A->ey[i] + B->ey[j]);

            if (seen[key])
                continue;

            seen[key] = 1;
            ri[rows] = i;
            rj[rows] = j;
            ++rows;
        }
    }

    free(seen);

    GF *M = calloc((size_t)rows * nc, 1);
    GF *rhs = malloc((size_t)rows);
    GF *solution = calloc((size_t)nc, 1);

    if (!M || !rhs || !solution) {
        free(M);
        free(rhs);
        free(solution);
        free(ri);
        free(rj);
        free(cand);
        return 0;
    }

    for (int r = 0; r < rows; ++r) {
        int i = ri[r];
        int j = rj[r];

        rhs[r] = S[(size_t)i * k2 + j];

        for (int c = 0; c < nc; ++c) {
            int p = cand[c];

            M[(size_t)r * nc + c] =
                gf_mul(
                    A->v[(size_t)i * nD + p],
                    B->v[(size_t)j * nD + p]);
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

        /* シンドローム再構成による検証 (代表行) */

        for (int r = 0; r < rows && good; ++r) {
            int i = ri[r];
            int j = rj[r];

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

    if (!good) {
        memset(error_vec, 0, (size_t)nD);
        *nerr = 0;
    }

    free(M);
    free(rhs);
    free(solution);
    free(ri);
    free(rj);
    free(cand);

    return good;
}

/* ============================================================
 * 二元部分体部分符号の冗長度
 *
 * GF(2^m) の加算は XOR なので、二元の c について
 *   sum_p c_p H[i][p] = 0   <=>   各ビット面 k で XOR が 0
 * よって二元の検査行列は H の各行のビット面 (m 枚) を並べたもの。
 * その階数を、先頭ビットによる行階段形で求める。
 * ============================================================ */

static double my_log2(double x)
{
    /* x > 0。libm を使わない簡易版 */
    int e = 0;

    while (x >= 2.0) { x /= 2.0; ++e; }
    while (x < 1.0)  { x *= 2.0; --e; }

    double y = (x - 1.0) / (x + 1.0);
    double y2 = y * y;
    double term = y;
    double sum = 0.0;

    for (int k = 1; k < 60; k += 2) {
        sum += term / k;
        term *= y2;
    }

    return (double)e + 2.0 * sum / 0.69314718055994530942;
}

/* log2 C(n,t) */
static double log2_binom(int n, int t)
{
    double s = 0.0;

    for (int i = 1; i <= t; ++i)
        s += my_log2((double)(n - t + i)) - my_log2((double)i);

    return s;
}

static int binary_rank(const EvalBasis *H, int m)
{
    const int words = (nD + 63) / 64;
    const int maxrows = H->count * m < nD ? H->count * m : nD;

    uint64_t *rows = malloc((size_t)maxrows * words * sizeof(uint64_t));
    int *pivrow = malloc((size_t)nD * sizeof(int));
    uint64_t *w = malloc((size_t)words * sizeof(uint64_t));

    if (!rows || !pivrow || !w) {
        free(rows);
        free(pivrow);
        free(w);
        return -1;
    }

    for (int p = 0; p < nD; ++p)
        pivrow[p] = -1;

    int rank = 0;

    for (int i = 0; i < H->count; ++i) {
        for (int k = 0; k < m; ++k) {
            memset(w, 0, (size_t)words * sizeof(uint64_t));

            const GF *hi = H->v + (size_t)i * nD;

            for (int p = 0; p < nD; ++p)
                if ((hi[p] >> k) & 1u)
                    w[p >> 6] |= 1ULL << (p & 63);

            int start = 0;

            for (;;) {
                while (start < words && !w[start])
                    ++start;

                if (start == words)
                    break;

                int col = (start << 6) + __builtin_ctzll(w[start]);
                int pr = pivrow[col];

                if (pr < 0) {
                    memcpy(rows + (size_t)rank * words, w,
                           (size_t)words * sizeof(uint64_t));
                    pivrow[col] = rank++;
                    break;
                }

                const uint64_t *e = rows + (size_t)pr * words;

                for (int x = start; x < words; ++x)
                    w[x] ^= e[x];
            }
        }
    }

    free(rows);
    free(pivrow);
    free(w);

    return rank;
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

    int rc = 0;

    EvalBasis A = {0};
    EvalBasis B = {0};
    EvalBasis H = {0};
    CodeGen cg = {0};

    GF *cw = NULL;
    GF *received = NULL;
    GF *decoded = NULL;
    GF *error_vec = NULL;
    GF *injected = NULL;
    GF *tmp = NULL;
    GF *S = NULL;
    int *order = NULL;

    int xa, xb;
    double t0;

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

        else if (!strcmp(argv[i], "--binary")) {
            g_binary = 1;
            continue;
        }

        else if (!strcmp(argv[i], "--binrank")) {
            g_binrank = 1;
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
                "  --zero-cw        all-zero codeword (skip codegen)\n"
                "  --binary         binary errors (all error values = 1)\n"
                "  --binrank        redundancy of the binary subfield subcode, then exit\n"
                "  --poly           show locator functions and zero check\n"
                "  --slow-syndrome  old syndrome computation\n"
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
                    "  q^(a+b) must be <= 256\n"
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

    /* Hermite curve */

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

    /* Finite field */

    if (!gf_init(curve->m, curve->poly)) {
        fprintf(stderr,
                "GF(2^%d) init failed for polynomial 0x%X\n",
                curve->m, curve->poly);
        return 1;
    }

    /* Enumerate affine points */

    t0 = now();

    nD = enumerate_points();

    if (nD <= 0) {
        fprintf(stderr,
                "Point enumeration failed\n");
        rc = 1;
        goto cleanup;
    }

    fprintf(stderr,
            "[time] points: %.2fs\n",
            now() - t0);

    if (errors > nD) {
        fprintf(stderr, "errors > n\n");
        rc = 2;
        goto cleanup;
    }

    /* Curve information */

    printf("Curve %s over GF(%d)\n",
           curve->name, Q);

    if (use_bbgs) {
        unsigned int c = ba + bb;
        uint64_t field_size = 0, expo = 0;

        pow_u64(bq, c, &field_size);
        pow_u64(bq, c - 1, &expo);

        printf("BBGS parameters:\n");
        printf("q = %u\n", bq);
        printf("a = %u\n", ba);
        printf("b = %u\n", bb);
        printf("c = %u\n", c);
        printf("field size q^c = %llu\n",
               (unsigned long long)field_size);
        printf("curve exponent Q = q^(c-1) = %llu\n",
               (unsigned long long)expo);
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

    /* Automatic degree selection */

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

            rc = 2;
            goto cleanup;
        }
    }

    /* Build A, B, H */

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
            rc = 1;
            goto cleanup;
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
            rc = 2;
            goto cleanup;
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

    if (g_binrank) {
        t0 = now();

        int rb = binary_rank(&H, curve->m);

        if (rb < 0) {
            fprintf(stderr, "binary rank: allocation failed\n");
            rc = 1;
            goto cleanup;
        }

        fprintf(stderr, "[time] binary rank: %.2fs\n", now() - t0);

        int tmax = 0;

        while (tmax + 1 < nD &&
               log2_binom(nD, tmax + 1) <= (double)rb)
            ++tmax;

        printf("\nBinary subfield subcode:\n");
        printf("  GF(%d) parity-check rows        = %d\n", Q, H.count);
        printf("  binary parity-check rank        = %d (upper limit %d)\n",
               rb, H.count * curve->m);
        printf("  binary dimension k              >= %d\n", nD - rb);
        printf("  ECP: correctable errors (errors=%d given), A.count=%d\n",
               errors, A.count);
        printf("  estimate (log2 C(n,t) <= rank)  : t ~ %d\n", tmax);
        printf("  (estimate = how many random errors a syndrome of this\n"
               "   size can identify at best. Not a decoder.)\n");

        rc = 0;
        goto cleanup;
    }

    /* Allocate buffers */

    cw = malloc((size_t)nD);
    received = malloc((size_t)nD);
    decoded = malloc((size_t)nD);
    error_vec = calloc((size_t)nD, 1);
    injected = calloc((size_t)nD, 1);
    tmp = malloc((size_t)nD);
    S = calloc((size_t)A.count * B.count, 1);
    order = malloc((size_t)nD * sizeof(int));

    if (!cw || !received || !decoded ||
        !error_vec || !injected ||
        !tmp || !S || !order) {

        fprintf(stderr, "Allocation failed\n");
        rc = 1;
        goto cleanup;
    }

    g_injected = injected;

    /* Code generator (全0符号語なら不要) */

    if (!g_zero_cw) {
        t0 = now();

        if (!codegen_init(&cg, &H)) {
            fprintf(stderr,
                    "Code generator allocation failed\n");
            rc = 1;
            goto cleanup;
        }

        fprintf(stderr,
                "[time] codegen: %.2fs\n",
                now() - t0);
    }

    /* Trials */

    uint64_t rng =
        (uint64_t)(unsigned)seed +
        0x123456789abcdefULL;

    int success = 0;
    int fail = 0;
    int miscorrect = 0;

    double t_dec = 0;
    double t_syn = 0;

    for (int tr = 0; tr < trials; ++tr) {
        memset(injected, 0, (size_t)nD);

        if (g_zero_cw) {
            memset(cw, 0, (size_t)nD);
        }
        else {
            random_codeword(&cg, cw, &rng);

            /* 符号語の検査は最初の1回だけ */

            if (tr == 0 && !in_code(&H, cw)) {
                fprintf(stderr,
                        "Could not construct a codeword in ker(H)\n");
                rc = 1;
                goto cleanup;
            }
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

            GF value = g_binary
                ? (GF)1
                : (GF)(1 + rng_next(&rng) % (uint64_t)(Q - 1));

            received[order[e]] ^= value;
            injected[order[e]] ^= value;
        }

        double ts = now();

        compute_syndrome(&A, &B, received, S, tmp);

        t_syn += now() - ts;

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
                if (trials == 1 && mismatch < 20) {
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
            "[time] syndrome total: %.3fs\n",
            t_syn);

    fprintf(stderr,
            "[time] decode total: %.2fs\n",
            t_dec);

    rc = (success == trials) ? 0 : 1;

cleanup:
    syn_free();
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

    return rc;
}
