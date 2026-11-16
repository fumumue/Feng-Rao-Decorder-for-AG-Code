/*
 * BBGS / 一般化エルミート曲線ほか: 評価符号と ECP 型復号器 (GF(2^m), m<=8)
 *
 * 符号の作り方:
 *   A = mkbase の単項式 x^i y^j (i+j<=da, i<=4) の評価ベクトルの張る空間
 *   B = mkbase の単項式 x^i y^j (i+j<=db, i<=4) の評価ベクトルの張る空間
 *   H = span{ A_i * B_j }  (座標ごとの積)
 *   C = H^perp
 *
 * 復号: シンドローム S_ij = sum_P r(P) A_i(P) B_j(P) から
 *   S^T の右核 -> 共通零点 -> 誤り値を連立方程式で解く -> 検証
 *
 * ビルド:
 *   cc -O2 -std=c11 -Wall -Wextra bbgs.c -o bbgs
 *
 * 実行例:
 *   ./bbgs --curve cc --da 2 --db 2 --errors 3
 *   ./bbgs --curve gg --da 6 --db 4 --errors 20 --trials 20
 *   ./bbgs --curve he --m 6 --da 4 --db 4 --errors 5
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAX_MONOMIALS 8192

typedef uint8_t GF;

static int gQ = 128;            /* 体の位数 (実行時に決まる) */
static unsigned gpoly = 0x89;   /* 既約(原始)多項式 */
#define Q gQ

static int g_verbose = 0;
static int g_full = 0;      /* 1: mkbase ではなく x の指数に制限のない全次数基底を使う */

/* ============================================================
 * 曲線の定義
 * 各行: {x次数, y次数, z次数, 係数}。z は無視 (z=1 のアフィン部分)
 * ============================================================ */

/* GF(2^3) */
static const unsigned short sc[4][4] =   /* g=6 generalized Hermitian */
  { {3,2,0,1}, {2,4,0,1}, {0,1,0,1}, {4,0,0,1} };
static const unsigned short kl[3][4] =   /* g=3 Klein */
  { {3,1,0,1}, {0,3,0,1}, {1,0,0,1} };
static const unsigned short s3[4][4] =   /* Suzuki */
  { {0,8,0,1}, {0,1,0,1}, {10,0,0,1}, {3,0,0,1} };

/* GF(2^4) */
static const unsigned short gu[5][4] =   /* g=21 N=121 */
  { {7,4,0,1}, {6,8,0,1}, {4,1,0,1}, {0,2,0,1}, {8,0,0,1} };
static const unsigned short ku3[5][4] =  /* Kummer */
  { {0,5,0,1}, {12,0,0,1}, {9,0,0,1}, {6,0,0,1}, {3,0,0,1} };

/* GF(2^5) */
static const unsigned short ge[6][4] =   /* g=75 N=497 */
  { {15,8,0,1}, {14,16,0,1}, {12,1,0,1}, {8,2,0,1}, {0,4,0,1}, {16,0,0,1} };
static const unsigned short s2[4][4] =   /* Suzuki N=1024 */
  { {0,32,0,1}, {0,1,0,1}, {36,0,0,1}, {5,0,0,1} };
static const unsigned short ts[3][4] =   /* g=26 N=157 */
  { {2,2,5,1}, {7,0,2,1}, {0,9,0,1} };

/* GF(2^6) */
static const unsigned short gg[7][4] =   /* g=212 N=2017 */
  { {31,8,0,1}, {30,16,0,1}, {28,32,0,1}, {24,1,0,1}, {16,2,0,1},
    {0,4,0,1}, {32,0,0,1} };
static const unsigned short ku2[4][4] =  /* y^9=x^4+x^2+x */
  { {0,9,0,1}, {4,0,0,1}, {2,0,0,1}, {1,0,0,1} };
static const unsigned short ku4[5][4] =  /* Kummer g=56 */
  { {0,9,0,1}, {40,0,0,1}, {33,0,0,1}, {12,0,0,1}, {5,0,0,1} };
static const unsigned short ku5[3][4] =  /* y^9=x^2+x g=4 */
  { {0,9,0,1}, {2,0,0,1}, {1,0,0,1} };

/* GF(2^7) */
static const unsigned short cc[8][4] =   /* g=315 */
  { {63,8,0,1}, {62,16,0,1}, {60,32,0,1}, {56,64,0,1}, {48,1,0,1},
    {32,2,0,1}, {0,4,0,1}, {64,0,0,1} };
static const unsigned short tt[3][4] =   /* g=78 N=891 */
  { {3,1,0,1}, {13,0,0,1}, {0,14,0,1} };
static const unsigned short su[4][4] =   /* Suzuki N=16384 */
  { {0,128,0,1}, {0,1,0,1}, {136,0,0,1}, {9,0,0,1} };

/* GF(2^8) */
static const unsigned short gd[9][4] =   /* g=2413 */
  { {127,8,0,1}, {126,16,0,1}, {124,32,0,1}, {120,64,0,1}, {112,128,0,1},
    {96,1,0,1}, {64,2,0,1}, {0,4,0,1}, {128,0,0,1} };
static const unsigned short ku[5][4] =   /* y^17=x^8+x^4+x^2+x */
  { {0,17,0,1}, {8,0,0,1}, {4,0,0,1}, {2,0,0,1}, {1,0,0,1} };
static const unsigned short el[4][4] =   /* 楕円曲線 g=1 */
  { {0,2,1,1}, {1,1,1,1}, {3,0,0,1}, {0,0,3,1} };
static const unsigned short el2[5][4] =
  { {0,2,1,1}, {1,1,1,1}, {3,0,0,1}, {0,0,3,1}, {2,0,1,1} };

/* Hermitian x^(q+1) + y^q + y : --m で GF(2^m) (m 偶数) を指定、実行時に設定 */
static unsigned short he_buf[3][4];

/* 使えないもの:
 *   gt : GF(512)。GF が uint8_t なので不可
 *   lo, lk : 係数 3,6 があり GF(2^m) の曲線ではない */

typedef struct {
    const char *name;
    int m;                      /* GF(2^m) */
    unsigned poly;
    int nterms;
    const unsigned short (*t)[4];
} CurveDef;

#define NT(a) ((int)(sizeof(a) / sizeof((a)[0])))

static const CurveDef CURVES[] = {
    {"sc",  3, 0x0B,  NT(sc),  sc },
    {"kl",  3, 0x0B,  NT(kl),  kl },
    {"s3",  3, 0x0B,  NT(s3),  s3 },
    {"gu",  4, 0x13,  NT(gu),  gu },
    {"ku3", 4, 0x13,  NT(ku3), ku3},
    {"ge",  5, 0x25,  NT(ge),  ge },
    {"s2",  5, 0x25,  NT(s2),  s2 },
    {"ts",  5, 0x25,  NT(ts),  ts },
    {"gg",  6, 0x43,  NT(gg),  gg },
    {"ku2", 6, 0x43,  NT(ku2), ku2},
    {"ku4", 6, 0x43,  NT(ku4), ku4},
    {"ku5", 6, 0x43,  NT(ku5), ku5},
    {"cc",  7, 0x89,  NT(cc),  cc },
    {"su",  7, 0x89,  NT(su),  su },
    {"tt",  7, 0x89,  NT(tt),  tt },
    {"gd",  8, 0x11D, NT(gd),  gd },
    {"ku",  8, 0x11D, NT(ku),  ku },
    {"el",  8, 0x11D, NT(el),  el },
    {"el2", 8, 0x11D, NT(el2), el2},
    {"he",  0, 0,     3, (const unsigned short (*)[4])he_buf},
};
#define NCURVES ((int)(sizeof(CURVES) / sizeof(CURVES[0])))

static CurveDef cur_local;
static const CurveDef *curve = NULL;

static const CurveDef *find_curve(const char *name)
{
    for (int i = 0; i < NCURVES; ++i)
        if (!strcmp(CURVES[i].name, name))
            return &CURVES[i];
    return NULL;
}

/* 方程式 F(x,y) の全次数 */
static int curve_degree(void)
{
    int m = 0;
    for (int i = 0; i < curve->nterms; ++i) {
        int d = curve->t[i][0] + curve->t[i][1];
        if (d > m) m = d;
    }
    return m;
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
        if (x == 0 || logt[x] >= 0)
            return 0;               /* 2 が原始元でない */
        expt[i] = x;
        logt[x] = i;
        x = gf_mul_slow(x, 2);
    }
    if (x != 1)
        return 0;

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
    if (!a) return 0;
    return expt[(Q - 1) - logt[a]];
}

static GF gf_pow(GF a, unsigned n)
{
    if (n == 0) return 1;
    if (!a) return 0;
    return expt[((unsigned)logt[a] * (n % (unsigned)(Q - 1))) % (unsigned)(Q - 1)];
}

/* ============================================================
 * 曲線上のアフィン有理点
 * ============================================================ */

typedef struct { GF x, y; } Point;

static Point *D = NULL;
static int nD = 0;

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
            if (eval_curve((GF)x, (GF)y) == 0)
                D[nD++] = (Point){(GF)x, (GF)y};

    return nD;
}

/* ============================================================
 * GF 上の線形代数
 * ============================================================ */

/* 簡約階段形。ピボット列を piv に入れ、階数を返す */
static int rref(GF *m, int rows, int cols, int *piv)
{
    int rank = 0;

    for (int col = 0; col < cols && rank < rows; ++col) {
        int p = rank;

        while (p < rows && m[(size_t)p * cols + col] == 0)
            ++p;
        if (p == rows)
            continue;

        if (p != rank) {
            for (int j = 0; j < cols; ++j) {
                GF t = m[(size_t)rank * cols + j];
                m[(size_t)rank * cols + j] = m[(size_t)p * cols + j];
                m[(size_t)p * cols + j] = t;
            }
        }

        GF s = gf_inv(m[(size_t)rank * cols + col]);
        for (int j = 0; j < cols; ++j)
            m[(size_t)rank * cols + j] = gf_mul(m[(size_t)rank * cols + j], s);

        for (int i = 0; i < rows; ++i) {
            if (i == rank) continue;
            GF f = m[(size_t)i * cols + col];
            if (!f) continue;
            for (int j = 0; j < cols; ++j)
                m[(size_t)i * cols + j] ^= gf_mul(f, m[(size_t)rank * cols + j]);
        }

        piv[rank++] = col;
    }
    return rank;
}

/* 右零空間の基底 (rows x cols の行列) */
static GF *nullspace(const GF *in, int rows, int cols, int *dim)
{
    GF *m = malloc((size_t)rows * cols);
    int *piv = malloc((size_t)(rows + 1) * sizeof(int));
    uint8_t *is_pivot = calloc((size_t)cols, 1);

    if (!m || !piv || !is_pivot) {
        free(m); free(piv); free(is_pivot);
        return NULL;
    }

    memcpy(m, in, (size_t)rows * cols);

    int rank = rref(m, rows, cols, piv);

    for (int i = 0; i < rank; ++i)
        is_pivot[piv[i]] = 1;

    *dim = cols - rank;

    GF *basis = calloc((size_t)(*dim > 0 ? *dim : 1) * cols, 1);
    if (!basis) {
        free(m); free(piv); free(is_pivot);
        return NULL;
    }

    int d = 0;
    for (int fc = 0; fc < cols; ++fc) {
        if (is_pivot[fc]) continue;
        basis[(size_t)d * cols + fc] = 1;
        for (int r = 0; r < rank; ++r)
            basis[(size_t)d * cols + piv[r]] = m[(size_t)r * cols + fc];
        ++d;
    }

    free(m); free(piv); free(is_pivot);
    return basis;
}

/* ============================================================
 * 行空間 (独立性の判定用)
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
    s->echelon = calloc((size_t)cap * ncols, 1);
    s->piv = malloc((size_t)cap * sizeof(int));
    s->w = malloc((size_t)ncols);
    return s->echelon && s->piv && s->w;
}

/* 1: 独立で追加した, 0: 従属, -1: 容量不足 */
static int rs_add(RowSpace *s, const GF *v)
{
    GF *w = s->w;

    memcpy(w, v, (size_t)s->ncols);

    for (int r = 0; r < s->nrows; ++r) {
        GF f = w[s->piv[r]];
        if (!f) continue;
        const GF *e = s->echelon + (size_t)r * s->ncols;
        for (int j = 0; j < s->ncols; ++j)
            w[j] ^= gf_mul(f, e[j]);
    }

    int p = 0;
    while (p < s->ncols && !w[p]) ++p;
    if (p == s->ncols) return 0;
    if (s->nrows >= s->cap) return -1;

    GF inv = gf_inv(w[p]);
    GF *e = s->echelon + (size_t)s->nrows * s->ncols;
    for (int j = 0; j < s->ncols; ++j)
        e[j] = gf_mul(w[j], inv);

    s->piv[s->nrows++] = p;
    return 1;
}

static void rs_free(RowSpace *s)
{
    free(s->echelon);
    free(s->piv);
    free(s->w);
    memset(s, 0, sizeof(*s));
}

/* ============================================================
 * 評価基底
 * ============================================================ */

typedef struct {
    int count;
    GF *v;          /* count x nD */
    int *ex, *ey;
} EvalBasis;

static void free_basis(EvalBasis *b)
{
    free(b->v);
    free(b->ex);
    free(b->ey);
    memset(b, 0, sizeof(*b));
}

/*
 * 単項式の指数リスト lst[k] = {x指数, y指数} (n個) から評価基底を作る。
 *
 * 全次数が曲線の次数より小さく、点数が 次数*deg(F) より多いときは
 * Bezout の定理により評価ベクトルが必ず独立なので判定を省く。
 * それ以外は rs_add で従属なものを取り除く。
 */
static int build_basis_from_list(int (*lst)[2], int n, EvalBasis *out)
{
    memset(out, 0, sizeof(*out));
    if (n <= 0 || n > MAX_MONOMIALS)
        return 0;

    int xm = 0, ym = 0, maxdeg = 0;
    for (int k = 0; k < n; ++k) {
        if (lst[k][0] > xm) xm = lst[k][0];
        if (lst[k][1] > ym) ym = lst[k][1];
        if (lst[k][0] + lst[k][1] > maxdeg) maxdeg = lst[k][0] + lst[k][1];
    }

    int dF = curve_degree();
    int known = maxdeg < dF && (long)nD > (long)maxdeg * dF;

    RowSpace rs;
    int use_rs = !known;
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
                if (added < 0) { ok = 0; break; }
                if (added == 0) continue;     /* 従属 */
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

/*
 * x^i y^j (i+j<=degree, i<=xm) を全次数順に並べた基底 (H 用)。
 * 次数 d ごとに (d,0), (d-1,1), ... の順。
 */
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
 * mkbase: 単項式の並びの生成 (元の mkbase と同じ規則)
 *
 *   全次数 dg=0,1,2,... の順に、x の指数を大きい方から並べる:
 *     dg <= MK_XMAX : (dg,0), (dg-1,1), ..., (0,dg)
 *     dg >  MK_XMAX : (MK_XMAX,dg-MK_XMAX), ..., (0,dg)   (x <= MK_XMAX)
 *   dg <= MK_MAXDEG まで作る。MK_XMAX=4 のとき、元の mkbase と同じ並び。
 * bb[count][2] に入れ、個数を返す。
 * ============================================================ */

#define MK_XMAX 8       /* x の指数の上限 */
#define MK_MAXDEG 100   /* mkbase が作る全次数の上限 */
#define MK_BBCAP ((MK_XMAX + 1) * (MK_MAXDEG + 1))   /* 個数の上限 */

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

/* mkbase の並びのうち全次数 <= degree のものから評価基底を作る (A, B 用) */
static int build_mk_basis(int degree, EvalBasis *out)
{
    static int bb[MK_BBCAP][2];
    int cnt = mkbase(bb);

    int n = 0;
    while (n < cnt && bb[n][0] + bb[n][1] <= degree)
        ++n;

    return build_basis_from_list(bb, n, out);
}

/* mkbase の並びのうち全次数 <= degree の単項式の個数 (従属を無視した上限) */
static int mk_count(int degree)
{
    static int bb[MK_BBCAP][2];
    int cnt = mkbase(bb);
    int n = 0;

    while (n < cnt && bb[n][0] + bb[n][1] <= degree)
        ++n;
    return n;
}

/* A, B の基底: 既定は mkbase (x<=4)。--full なら全次数 <= d の全単項式 */
static int basis_count(int degree)
{
    return g_full ? (degree + 1) * (degree + 2) / 2 : mk_count(degree);
}

static int build_ab_basis(int degree, EvalBasis *out)
{
    return g_full ? build_monomial_basis(degree, degree, out)
                  : build_mk_basis(degree, out);
}

static int basis_xmax(int degree)
{
    return g_full ? degree : (MK_XMAX < degree ? MK_XMAX : degree);
}

/* ============================================================
 * 乱数
 * ============================================================ */

static uint64_t rng_next(uint64_t *s)
{
    uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);

    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* ============================================================
 * 符号語の生成 (H の rref は 1 回だけ)
 * ============================================================ */

typedef struct {
    GF *m;
    int *piv;
    uint8_t *isp;
    int rank;
} CodeGen;

static int codegen_init(CodeGen *g, const EvalBasis *H)
{
    memset(g, 0, sizeof(*g));

    g->m = malloc((size_t)H->count * nD);
    g->piv = malloc((size_t)(H->count + 1) * sizeof(int));
    g->isp = calloc((size_t)nD, 1);
    if (!g->m || !g->piv || !g->isp)
        return 0;

    memcpy(g->m, H->v, (size_t)H->count * nD);
    g->rank = rref(g->m, H->count, nD, g->piv);

    for (int r = 0; r < g->rank; ++r)
        g->isp[g->piv[r]] = 1;
    return 1;
}

static void codegen_free(CodeGen *g)
{
    free(g->m);
    free(g->piv);
    free(g->isp);
    memset(g, 0, sizeof(*g));
}

static void random_codeword(const CodeGen *g, GF *word, uint64_t *state)
{
    for (int p = 0; p < nD; ++p)
        word[p] = g->isp[p] ? 0 : (GF)(rng_next(state) & (uint64_t)(Q - 1));

    for (int r = 0; r < g->rank; ++r) {
        GF s = 0;
        const GF *row = g->m + (size_t)r * nD;
        for (int p = 0; p < nD; ++p)
            if (!g->isp[p])
                s ^= gf_mul(row[p], word[p]);
        word[g->piv[r]] = s;
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
 * シンドロームと復号
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

/*
 * シンドロームだけから誤りベクトルを求める。
 * maxnc: 候補点の数の上限 (H.count)。これを超える候補は解けない。
 * 戻り値 1: 一意な解が得られ検証も通った, 0: 失敗
 */
static int decode(const EvalBasis *A, const EvalBasis *B, const GF *S,
                  int maxnc, GF *error_vec, int *nerr)
{
    int k1 = A->count, k2 = B->count;

    memset(error_vec, 0, (size_t)nD);
    *nerr = 0;

    int allzero = 1;
    for (int i = 0; i < k1 * k2; ++i)
        if (S[i]) { allzero = 0; break; }
    if (allzero)
        return 1;

    /* S^T (k2 x k1) の右核 = シンドロームと直交する A の関数 */
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
    if (!cand) { free(ker); return 0; }

    int nc = 0;
    for (int p = 0; p < nD; ++p) {
        int common_zero = 1;

        for (int v = 0; v < dim && common_zero; ++v) {
            GF z = 0;
            for (int i = 0; i < k1; ++i)
                z ^= gf_mul(ker[(size_t)v * k1 + i], A->v[(size_t)i * nD + p]);
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

    /* S[i,j] = sum_c e_c A_i(P_c) B_j(P_c) を e_c について解く */
    int rows = k1 * k2;
    int cols = nc + 1;

    GF *aug = calloc((size_t)rows * cols, 1);
    int *piv = malloc((size_t)(rows + 1) * sizeof(int));
    if (!aug || !piv) {
        free(aug); free(piv); free(cand);
        return 0;
    }

    for (int i = 0; i < k1; ++i) {
        for (int j = 0; j < k2; ++j) {
            int r = i * k2 + j;
            for (int c = 0; c < nc; ++c) {
                int p = cand[c];
                aug[(size_t)r * cols + c] =
                    gf_mul(A->v[(size_t)i * nD + p], B->v[(size_t)j * nD + p]);
            }
            aug[(size_t)r * cols + nc] = S[(size_t)i * k2 + j];
        }
    }

    int rank = rref(aug, rows, cols, piv);

    /* 一意解: rank == nc かつ右辺の列がピボットでない */
    int good = (rank == nc);
    for (int r = 0; r < rank && good; ++r)
        if (piv[r] == nc)
            good = 0;

    if (good) {
        for (int c = 0; c < nc; ++c) {
            GF e = aug[(size_t)c * cols + nc];
            error_vec[cand[c]] = e;
            if (e) ++*nerr;
        }

        /* 検証: 誤りベクトルからシンドローム全体を再構成して比較 */
        for (int i = 0; i < k1 && good; ++i) {
            for (int j = 0; j < k2 && good; ++j) {
                GF check = 0;
                for (int c = 0; c < nc; ++c) {
                    int p = cand[c];
                    if (!error_vec[p]) continue;
                    check ^= gf_mul(error_vec[p],
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

    free(aug);
    free(piv);
    free(cand);
    return good;
}

/* ============================================================
 * コマンドライン
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

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

int main(int argc, char **argv)
{
    int da = 2, db = 2, errors = 1, trials = 1, seed = 1;
    int auto_mode = 0, margin = 0;
    int hm = 6;                     /* Hermitian: GF(2^hm), hm は偶数 */
    const char *cname = "cc";

    for (int i = 1; i < argc; ++i) {
        int *dst = NULL;

        if (!strcmp(argv[i], "--curve")) {
            if (++i >= argc) { fprintf(stderr, "missing curve name\n"); return 2; }
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
        } else if (!strcmp(argv[i], "--margin")) dst = &margin;
        else if (!strcmp(argv[i], "--m"))        dst = &hm;
        else if (!strcmp(argv[i], "--da"))       dst = &da;
        else if (!strcmp(argv[i], "--db"))       dst = &db;
        else if (!strcmp(argv[i], "--errors"))   dst = &errors;
        else if (!strcmp(argv[i], "--trials"))   dst = &trials;
        else if (!strcmp(argv[i], "--seed"))     dst = &seed;
        else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            printf("Usage: %s --curve NAME [--m N] [--da N] [--db N]\n"
                   "          [--errors N] [--trials N] [--seed N]\n          [--auto [--margin N]] [--full] [--verbose]\n",
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

    if (da > MK_MAXDEG || db > MK_MAXDEG || errors < 0 || trials < 1) {
        fprintf(stderr, "Invalid parameters (da, db <= %d).\n", MK_MAXDEG);
        return 2;
    }

    const CurveDef *c = find_curve(cname);
    if (!c) {
        fprintf(stderr, "Unknown curve: %s (use --help)\n", cname);
        return 2;
    }
    cur_local = *c;

    if (!strcmp(cname, "he")) {
        static const unsigned P[9] = {0, 0, 0x07, 0x0B, 0x13, 0x25, 0x43, 0x89, 0x11D};
        if (hm % 2 || hm < 2 || hm > 8) {
            fprintf(stderr, "--m must be even, 2..8\n");
            return 2;
        }
        unsigned q = 1u << (hm / 2);
        unsigned short h[3][4] = { {(unsigned short)(q + 1), 0, 0, 1},
                                   {0, (unsigned short)q, 0, 1},
                                   {0, 1, 0, 1} };
        memcpy(he_buf, h, sizeof h);
        cur_local.m = hm;
        cur_local.poly = P[hm];
    }
    curve = &cur_local;

    if (!gf_init(curve->m, curve->poly)) {
        fprintf(stderr, "GF(2^%d) init failed for polynomial 0x%X\n",
                curve->m, curve->poly);
        return 1;
    }

    double t0 = now();

    nD = enumerate_points();
    if (nD <= 0) {
        fprintf(stderr, "Point enumeration failed\n");
        return 1;
    }
    fprintf(stderr, "[time] points: %.2fs\n", now() - t0);

    if (errors > nD) {
        fprintf(stderr, "errors > n\n");
        return 2;
    }

    printf("Curve %s over GF(%d)\nF(x,y) =", cname, Q);
    for (int i = 0; i < curve->nterms; ++i)
        printf("%s%u*x^%u*y^%u", i ? " + " : " ",
               curve->t[i][3], curve->t[i][0], curve->t[i][1]);
    printf("\nAffine rational points: %d\n", nD);

    /* --auto: 誤り数 t から da, db を決める。
     *   A.count >= t + 2 + margin  (誤り位置関数が2次元以上の核を持つ)
     *   B.count >= t + margin      (誤り値が一意に決まる)
     * を満たす最小の da, db。 */
    int need_a = errors + 2 + margin;
    int need_b = errors + margin;

    if (auto_mode) {
        da = db = -1;
        for (int d = 0; d <= MK_MAXDEG; ++d) {
            if (da < 0 && basis_count(d) >= need_a) da = d;
            if (db < 0 && basis_count(d) >= need_b) db = d;
        }
        if (da < 0 || db < 0) {
            fprintf(stderr,
                    "errors=%d (margin %d) is too large: A.count is at most %d "
                    "for da <= %d (raise MK_MAXDEG)\n",
                    errors, margin, basis_count(MK_MAXDEG), MK_MAXDEG);
            return 2;
        }
    }

    EvalBasis A = {0}, B = {0}, H = {0};
    int xa, xb;

    t0 = now();
    for (;;) {
        free_basis(&A); free_basis(&B); free_basis(&H);

        xa = basis_xmax(da);
        xb = basis_xmax(db);

        if (!build_ab_basis(da, &A) ||
            !build_ab_basis(db, &B) ||
            !build_monomial_basis(da + db, xa + xb, &H)) {
            fprintf(stderr, "Basis construction failed.\n");
            free_basis(&A); free_basis(&B); free_basis(&H);
            free(D);
            return 1;
        }

        if (!auto_mode)
            break;

        /* 曲線の次数以上で従属な項が除かれて足りなくなった場合は次数を上げる */
        int short_a = A.count < need_a, short_b = B.count < need_b;
        if (!short_a && !short_b)
            break;
        if (short_a) ++da;
        if (short_b) ++db;
        if (da > MK_MAXDEG || db > MK_MAXDEG) {
            fprintf(stderr, "auto: da/db would exceed %d\n", MK_MAXDEG);
            free_basis(&A); free_basis(&B); free_basis(&H);
            free(D);
            return 2;
        }
    }
    fprintf(stderr, "[time] basis: %.2fs\n", now() - t0);

    if (auto_mode)
        printf("auto: errors=%d margin=%d -> da=%d db=%d\n",
               errors, margin, da, db);

    printf("A basis: %d independent monomials (total degree <= %d, x <= %d)\n",
           A.count, da, xa);
    printf("B basis: %d independent monomials (total degree <= %d, x <= %d)\n",
           B.count, db, xb);
    printf("H basis: %d independent products; C = H^perp\n", H.count);
    printf("Code length n=%d; parity-check rank=%d; dimension k=%d\n",
           nD, H.count, nD - H.count);

    CodeGen cg;
    GF *cw = malloc((size_t)nD);
    GF *received = malloc((size_t)nD);
    GF *decoded = malloc((size_t)nD);
    GF *error_vec = calloc((size_t)nD, 1);
    GF *injected = calloc((size_t)nD, 1);
    GF *tmp = malloc((size_t)nD);
    GF *S = calloc((size_t)A.count * B.count, 1);
    int *order = malloc((size_t)nD * sizeof(int));

    if (!cw || !received || !decoded || !error_vec || !injected ||
        !tmp || !S || !order) {
        fprintf(stderr, "Allocation failed\n");
        return 1;
    }

    t0 = now();
    if (!codegen_init(&cg, &H)) {
        fprintf(stderr, "Allocation failed\n");
        return 1;
    }
    fprintf(stderr, "[time] codegen: %.2fs\n", now() - t0);

    uint64_t rng = (uint64_t)(unsigned)seed + 0x123456789abcdefULL;

    int success = 0, fail = 0, miscorrect = 0;
    double t_dec = 0;

    for (int tr = 0; tr < trials; ++tr) {
        memset(injected, 0, (size_t)nD);

        random_codeword(&cg, cw, &rng);
        if (!in_code(&H, cw)) {
            fprintf(stderr, "Could not construct a codeword in ker(H)\n");
            return 1;
        }

        memcpy(received, cw, (size_t)nD);

        for (int p = 0; p < nD; ++p)
            order[p] = p;

        for (int e = 0; e < errors; ++e) {
            int j = e + (int)(rng_next(&rng) % (uint64_t)(nD - e));
            int t = order[e]; order[e] = order[j]; order[j] = t;

            GF value = (GF)(1 + rng_next(&rng) % (uint64_t)(Q - 1));
            received[order[e]] ^= value;
            injected[order[e]] ^= value;
        }

        compute_syndrome(&A, &B, received, S, tmp);

        double t1 = now();
        int recovered = 0;
        int ok = decode(&A, &B, S, H.count, error_vec, &recovered);
        t_dec += now() - t1;

        int mismatch = 0;
        for (int p = 0; p < nD; ++p) {
            if (injected[p] != error_vec[p]) {
                if (trials == 1)
                    printf("MISMATCH position=%d injected=0x%02X decoded=0x%02X\n",
                           p, injected[p], error_vec[p]);
                mismatch++;
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
                    printf("  position=%d value=0x%02X\n", p, injected[p]);

            printf("\nDecoded error locations and values:\n");
            for (int p = 0; p < nD; ++p)
                if (error_vec[p])
                    printf("  position=%d value=0x%02X\n", p, error_vec[p]);

            printf("Trial: %s; injected errors=%d; recovered nonzero corrections=%d\n",
                   same ? "PASS" : (ok ? "MISCORRECTION" : "FAIL"),
                   errors, recovered);
        }
    }

    if (trials > 1)
        printf("Trials=%d: success=%d, miscorrection=%d, failure=%d\n",
               trials, success, miscorrect, fail);

    fprintf(stderr, "[time] decode total: %.2fs\n", t_dec);

    codegen_free(&cg);
    free(injected); free(cw); free(received); free(decoded);
    free(order); free(error_vec); free(tmp); free(S);
    free_basis(&A); free_basis(&B); free_basis(&H);
    free(D);

    return (success == trials) ? 0 : 1;
}