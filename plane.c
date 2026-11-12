/*
 * plane_ag_decoder.c
 *
 * 非特異な射影平面曲線 F(x,y)=0 (GF(2^m) 上, m=2..8) から作る AG 符号の
 * 基本アルゴリズム (誤り訂正ペア / シンドローム行列の零空間) による復号デモ。
 *
 *   H  = 無限遠直線で切った因子 (deg H = d = 曲線の次数)
 *   A  = C_L(D, k1*H)   (評価した多項式 次数<=k1 の空間)
 *   B  = C_L(D, k2*H)
 *   符号 C = C_L(D, (k1+k2)*H) の双対 (検査行列 = 次数<=k1+k2 の単項式の評価)
 *   D  = 曲線のアフィン有理点すべて
 *
 * シンドローム行列  S[i][j] = sum_p r_p * a_i(P_p) * b_j(P_p)
 * 誤り位置関数の空間 = S^T の零空間, 誤り位置 = その共通零点,
 * 誤り値 = 連立一次方程式 sum_c e_c a_i(P_c) b_j(P_c) = S[i][j]
 *
 * 前提 (コードは検証しません):
 *   - 曲線は絶対既約かつ非特異 (無限遠点も含む)。
 *     有理点での特異性だけは簡易チェックします (証明にはなりません)。
 *   - (k1+k2)*d < n  (評価写像が単射になる条件)
 *
 * ビルド: gcc -O2 -Wall -o plane_ag_decoder plane_ag_decoder.c
 * 実行例: ./plane_ag_decoder --curve herm16 --errors 3
 *         ./plane_ag_decoder --m 3 --poly "x^3*y+y^3+x" --errors 2
 *         ./plane_ag_decoder --curve klein8 --errors 2 --trials 1000
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/* GF(2^m)                                                             */
/* ------------------------------------------------------------------ */
static int GQ; /* q = 2^m */
static uint8_t EXPT[512];
static int LOGT[256];

static int gf_init(int m)
{
    static const unsigned poly[9] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D};
    if (m < 2 || m > 8)
        return 0;
    GQ = 1 << m;
    unsigned x = 1;
    for (int i = 0; i < GQ - 1; ++i)
    {
        EXPT[i] = (uint8_t)x;
        LOGT[x] = i;
        x <<= 1;
        if (x & (unsigned)GQ)
            x ^= poly[m];
    }
    for (int i = GQ - 1; i < 2 * (GQ - 1); ++i)
        EXPT[i] = EXPT[i - (GQ - 1)];
    return 1;
}
static inline uint8_t gmul(uint8_t a, uint8_t b)
{
    return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0;
}
static inline uint8_t ginv(uint8_t a)
{
    return a ? EXPT[(GQ - 1) - LOGT[a]] : 0;
}
static uint8_t gpow(uint8_t a, int e)
{
    if (e == 0)
        return 1;
    if (!a)
        return 0;
    return EXPT[(int)(((long)LOGT[a] * e) % (GQ - 1))];
}

/* ------------------------------------------------------------------ */
/* 線形代数 (行列は行優先の1次元配列)                                   */
/* ------------------------------------------------------------------ */
static int rref(uint8_t *m, int rows, int cols, int *piv)
{
    int rank = 0;
    for (int col = 0; col < cols && rank < rows; ++col)
    {
        int p = rank;
        while (p < rows && m[(size_t)p * cols + col] == 0)
            ++p;
        if (p == rows)
            continue;
        if (p != rank)
            for (int j = 0; j < cols; ++j)
            {
                uint8_t t = m[(size_t)rank * cols + j];
                m[(size_t)rank * cols + j] = m[(size_t)p * cols + j];
                m[(size_t)p * cols + j] = t;
            }
        uint8_t s = ginv(m[(size_t)rank * cols + col]);
        for (int j = 0; j < cols; ++j)
            m[(size_t)rank * cols + j] = gmul(m[(size_t)rank * cols + j], s);
        for (int i = 0; i < rows; ++i)
        {
            if (i == rank)
                continue;
            uint8_t f = m[(size_t)i * cols + col];
            if (!f)
                continue;
            for (int j = 0; j < cols; ++j)
                m[(size_t)i * cols + j] ^= gmul(f, m[(size_t)rank * cols + j]);
        }
        piv[rank++] = col;
    }
    return rank;
}

/* in (rows x cols) の右零空間の基底 (dim x cols) を返す */
static uint8_t *nullspace(const uint8_t *in, int rows, int cols, int *dim)
{
    uint8_t *m = malloc((size_t)rows * cols + 1);
    int *piv = malloc(sizeof(int) * (rows + 1));
    int *isp = calloc(cols + 1, sizeof(int));
    memcpy(m, in, (size_t)rows * cols);
    int rank = rref(m, rows, cols, piv);
    for (int i = 0; i < rank; ++i)
        isp[piv[i]] = 1;
    *dim = cols - rank;
    uint8_t *basis = calloc((size_t)(*dim) * cols + 1, 1);
    int d = 0;
    for (int fc = 0; fc < cols; ++fc)
    {
        if (isp[fc])
            continue;
        basis[(size_t)d * cols + fc] = 1;
        for (int r = 0; r < rank; ++r)
            basis[(size_t)d * cols + piv[r]] = m[(size_t)r * cols + fc]; /* 標数2: -x = x */
        ++d;
    }
    free(m);
    free(piv);
    free(isp);
    return basis;
}

/* ------------------------------------------------------------------ */
/* 曲線の定義                                                          */
/* ------------------------------------------------------------------ */
typedef struct
{
    int i, j;
    uint8_t c;
} Term; /* c * x^i * y^j */
typedef struct
{
    const char *name, *desc;
    int m, deg, nt;
    Term t[32];
} Curve;

/* 標数2なので + と - は同じ。自分の曲線は "custom" を書き換えて使う */
static const Curve CURVES[] = {
    {"klein8", "Klein quartic x^3 y + y^3 + x = 0 over GF(8)", 3, 4, 3,
     {{3, 1, 1}, {0, 3, 1}, {1, 0, 1}}},
    {"herm4", "Hermitian y^2 + y = x^3 over GF(4)", 2, 3, 3,
     {{0, 2, 1}, {0, 1, 1}, {3, 0, 1}}},
    {"herm16", "Hermitian y^4 + y = x^5 over GF(16)", 4, 5, 3,
     {{0, 4, 1}, {0, 1, 1}, {5, 0, 1}}},
    {"fermat16", "Fermat x^5 + y^5 + 1 = 0 over GF(16)", 4, 5, 3,
     {{5, 0, 1}, {0, 5, 1}, {0, 0, 1}}},
    {"custom", "user-defined (edit the table in the source)", 3, 4, 3,
     {{3, 1, 1}, {0, 3, 1}, {1, 0, 1}}},
};
#define NCURVES ((int)(sizeof(CURVES) / sizeof(CURVES[0])))

typedef struct
{
    uint8_t x, y;
} Point;

static uint8_t eval_F(const Curve *cv, uint8_t x, uint8_t y)
{
    uint8_t z = 0;
    for (int t = 0; t < cv->nt; ++t)
        z ^= gmul(cv->t[t].c, gmul(gpow(x, cv->t[t].i), gpow(y, cv->t[t].j)));
    return z;
}

/* 有理点での特異点の簡易チェック。見つかった個数を返す */
static int rational_singularities(const Curve *cv)
{
    int cnt = 0;
    for (int x = 0; x < GQ; ++x)
        for (int y = 0; y < GQ; ++y)
        {
            if (eval_F(cv, (uint8_t)x, (uint8_t)y))
                continue;
            uint8_t fx = 0, fy = 0;
            for (int t = 0; t < cv->nt; ++t)
            {
                const Term *T = &cv->t[t];
                uint8_t base;
                if (T->i & 1)
                {
                    base = gmul(T->c, gmul(gpow((uint8_t)x, T->i - 1), gpow((uint8_t)y, T->j)));
                    fx ^= base;
                }
                if (T->j & 1)
                {
                    base = gmul(T->c, gmul(gpow((uint8_t)x, T->i), gpow((uint8_t)y, T->j - 1)));
                    fy ^= base;
                }
            }
            if (!fx && !fy)
                ++cnt;
        }
    /* 無限遠点 (1:y:0) と (0:1:0) */
    for (int k = 0; k <= GQ; ++k)
    {
        uint8_t x = (k == GQ) ? 0 : 1, y = (k == GQ) ? 1 : (uint8_t)k;
        uint8_t f = 0, fx = 0, fy = 0, fz = 0;
        for (int t = 0; t < cv->nt; ++t)
        {
            const Term *T = &cv->t[t];
            uint8_t mon = gmul(T->c, gmul(gpow(x, T->i), gpow(y, T->j)));
            if (T->i + T->j == cv->deg)
            {
                f ^= mon;
                if (T->i & 1)
                    fx ^= gmul(T->c, gmul(gpow(x, T->i - 1), gpow(y, T->j)));
                if (T->j & 1)
                    fy ^= gmul(T->c, gmul(gpow(x, T->i), gpow(y, T->j - 1)));
            }
            if (T->i + T->j == cv->deg - 1)
                fz ^= mon;
        }
        if (!f && !fx && !fy && !fz)
            ++cnt;
    }
    return cnt;
}


/* 式の文字列 "x^3*y + y^3 + x" を Curve に変換する。
 * 項は + (または -) で区切り、各項は 係数(0..q-1の整数) と x, x^N, y, y^N の積。
 * "*" や空白は省略可 (例: "x^3y", "2x^2"). 係数は GF(2^m) の元を整数で表したもの。 */
static int parse_poly(const char *s, Curve *cv, int m)
{
    static const char *nm = "command-line curve";
    cv->name = "cli";
    cv->desc = nm;
    cv->m = m;
    cv->nt = 0;
    cv->deg = 0;
    const char *p = s;
    while (*p)
    {
        int i = 0, j = 0, any = 0;
        uint8_t c = 1;
        while (*p && *p != '+' && *p != '-')
        {
            if (*p == ' ' || *p == '*')
            {
                ++p;
                continue;
            }
            if (*p >= '0' && *p <= '9')
            {
                int v = 0;
                while (*p >= '0' && *p <= '9')
                    v = v * 10 + (*p++ - '0');
                if (v >= GQ)
                    return 0;
                c = gmul(c, (uint8_t)v);
                any = 1;
            }
            else if (*p == 'x' || *p == 'y')
            {
                char ch = *p++;
                int e = 1;
                if (*p == '^')
                {
                    ++p;
                    if (!(*p >= '0' && *p <= '9'))
                        return 0;
                    e = 0;
                    while (*p >= '0' && *p <= '9')
                        e = e * 10 + (*p++ - '0');
                }
                if (ch == 'x')
                    i += e;
                else
                    j += e;
                any = 1;
            }
            else
                return 0;
        }
        if (any && c)
        {
            if (cv->nt >= 32)
                return 0;
            cv->t[cv->nt].i = i;
            cv->t[cv->nt].j = j;
            cv->t[cv->nt].c = c;
            ++cv->nt;
            if (i + j > cv->deg)
                cv->deg = i + j;
        }
        else if (!any && *p != '+' && *p != '-' && *p)
            return 0;
        if (*p == '+' || *p == '-')
            ++p;
    }
    return cv->nt > 0 && cv->deg >= 1;
}

/* 次数 <= k の多項式を F で割った空間の次元 */
static int dim_poly(int k, int d)
{
    int a = (k + 1) * (k + 2) / 2;
    int b = (k >= d) ? (k - d + 1) * (k - d + 2) / 2 : 0;
    return a - b;
}

/* ------------------------------------------------------------------ */
/* L(kH) の評価ベクトル基底: 次数 <= D の単項式から独立なものを残す       */
/* ------------------------------------------------------------------ */
typedef struct
{
    int cnt;
    uint8_t *v; /* cnt x n */
} Basis;

static Basis build_basis(int D, const Point *pts, int n)
{
    int maxc = (D + 1) * (D + 2) / 2;
    uint8_t *ech = calloc((size_t)maxc * n, 1);
    uint8_t *out = calloc((size_t)maxc * n, 1);
    uint8_t *v = malloc(n), *w = malloc(n);
    int *piv = calloc(maxc, sizeof(int));
    int rank = 0;
    for (int d = 0; d <= D; ++d)
        for (int j = 0; j <= d; ++j)
        {
            int i = d - j;
            for (int p = 0; p < n; ++p)
                w[p] = v[p] = gmul(gpow(pts[p].x, i), gpow(pts[p].y, j));
            for (int r = 0; r < rank; ++r)
            {
                uint8_t f = v[piv[r]];
                if (!f)
                    continue;
                for (int c = 0; c < n; ++c)
                    v[c] ^= gmul(f, ech[(size_t)r * n + c]);
            }
            int pv = 0;
            while (pv < n && v[pv] == 0)
                ++pv;
            if (pv == n)
                continue;
            uint8_t s = ginv(v[pv]);
            for (int c = 0; c < n; ++c)
                ech[(size_t)rank * n + c] = gmul(v[c], s);
            piv[rank] = pv;
            memcpy(out + (size_t)rank * n, w, n);
            ++rank;
        }
    free(ech);
    free(v);
    free(w);
    free(piv);
    Basis b = {rank, out};
    return b;
}

/* ------------------------------------------------------------------ */
/* 復号器                                                              */
/* ------------------------------------------------------------------ */
typedef struct
{
    int n;
    Basis A, B, H;
} Code;

static int in_code(const Code *c, const uint8_t *w)
{
    for (int r = 0; r < c->H.cnt; ++r)
    {
        uint8_t z = 0;
        for (int p = 0; p < c->n; ++p)
            z ^= gmul(c->H.v[(size_t)r * c->n + p], w[p]);
        if (z)
            return 0;
    }
    return 1;
}

/* 成功なら 1 を返し out に訂正語, *nerr に見つけた誤り個数 */
static int decode(const Code *c, const uint8_t *rcv, uint8_t *out, int *nerr)
{
    int n = c->n, K1 = c->A.cnt, K2 = c->B.cnt;
    int ok = 0;
    uint8_t *S = calloc((size_t)K1 * K2 + 1, 1);
    uint8_t *ST = calloc((size_t)K1 * K2 + 1, 1);
    uint8_t *AR = malloc((size_t)n);
    int allzero = 1;
    *nerr = 0;
    memcpy(out, rcv, n);

    for (int i = 0; i < K1; ++i)
    {
        for (int p = 0; p < n; ++p)
            AR[p] = gmul(rcv[p], c->A.v[(size_t)i * n + p]);
        for (int j = 0; j < K2; ++j)
        {
            uint8_t z = 0;
            for (int p = 0; p < n; ++p)
                z ^= gmul(AR[p], c->B.v[(size_t)j * n + p]);
            S[(size_t)i * K2 + j] = z;
            ST[(size_t)j * K1 + i] = z;
            if (z)
                allzero = 0;
        }
    }
    if (allzero)
    {
        ok = in_code(c, rcv);
        goto done;
    }

    int dimk;
    uint8_t *ker = nullspace(ST, K2, K1, &dimk);
    if (dimk == 0)
    {
        free(ker);
        goto done;
    }
    int *Z = malloc(sizeof(int) * n);
    int nz = 0;
    for (int p = 0; p < n; ++p)
    {
        int common = 1;
        for (int v = 0; v < dimk && common; ++v)
        {
            uint8_t z = 0;
            for (int i = 0; i < K1; ++i)
                z ^= gmul(ker[(size_t)v * K1 + i], c->A.v[(size_t)i * n + p]);
            if (z)
                common = 0;
        }
        if (common)
            Z[nz++] = p;
    }
    free(ker);
    if (nz == 0 || nz > K1 * K2)
    {
        free(Z);
        goto done;
    }
    {
        int rows = K1 * K2, cols = nz + 1;
        uint8_t *aug = calloc((size_t)rows * cols, 1);
        int *piv = malloc(sizeof(int) * (rows + 1));
        for (int i = 0; i < K1; ++i)
            for (int j = 0; j < K2; ++j)
            {
                int r = i * K2 + j;
                for (int k = 0; k < nz; ++k)
                    aug[(size_t)r * cols + k] =
                        gmul(c->A.v[(size_t)i * n + Z[k]], c->B.v[(size_t)j * n + Z[k]]);
                aug[(size_t)r * cols + nz] = S[(size_t)i * K2 + j];
            }
        int rank = rref(aug, rows, cols, piv);
        int good = (rank == nz);
        for (int r = 0; r < rank && good; ++r)
            if (piv[r] == nz)
                good = 0; /* 矛盾した連立方程式 */
        if (good)
        {
            for (int k = 0; k < nz; ++k)
                out[Z[k]] ^= aug[(size_t)k * cols + nz];
            if (in_code(c, out))
            {
                ok = 1;
                for (int k = 0; k < nz; ++k)
                    if (aug[(size_t)k * cols + nz])
                        ++*nerr;
            }
        }
        free(aug);
        free(piv);
    }
    free(Z);
done:
    free(S);
    free(ST);
    free(AR);
    return ok;
}

/* ------------------------------------------------------------------ */
/* 乱数 (splitmix64: 環境によらず再現可能)                              */
/* ------------------------------------------------------------------ */
static uint64_t rng_state;
static uint64_t rnd(void)
{
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static int parse_int(const char *s, int *v)
{
    char *e = NULL;
    long x = strtol(s, &e, 10);
    if (!s[0] || !e || *e || x < 0 || x > 1000000)
        return 0;
    *v = (int)x;
    return 1;
}

int main(int argc, char **argv)
{
    const char *cname = "herm16";
    const char *poly = NULL;
    int mm = 0;
    int k1 = 0, k2 = 0, errors = 2, seed = 1, trials = 1;
    for (int i = 1; i < argc; ++i)
    {
        int *dst = NULL;
        if (!strcmp(argv[i], "--curve") && i + 1 < argc)
        {
            cname = argv[++i];
            continue;
        }
        else if (!strcmp(argv[i], "--poly") && i + 1 < argc)
        {
            poly = argv[++i];
            continue;
        }
        else if (!strcmp(argv[i], "--m"))
            dst = &mm;
        else if (!strcmp(argv[i], "--k1"))
            dst = &k1;
        else if (!strcmp(argv[i], "--k2"))
            dst = &k2;
        else if (!strcmp(argv[i], "--errors"))
            dst = &errors;
        else if (!strcmp(argv[i], "--seed"))
            dst = &seed;
        else if (!strcmp(argv[i], "--trials"))
            dst = &trials;
        else if (!strcmp(argv[i], "--list"))
        {
            for (int c = 0; c < NCURVES; ++c)
                printf("%-9s GF(2^%d) deg %d : %s\n", CURVES[c].name, CURVES[c].m,
                       CURVES[c].deg, CURVES[c].desc);
            return 0;
        }
        else
        {
            printf("Usage: %s [--curve NAME | --m M --poly \"x^3*y+y^3+x\"] [--k1 K] [--k2 K] [--errors T] "
                   "[--seed S] [--trials N] [--list]\n",
                   argv[0]);
            return strcmp(argv[i], "--help") && strcmp(argv[i], "-h") ? 2 : 0;
        }
        if (i + 1 >= argc || !parse_int(argv[++i], dst))
        {
            fprintf(stderr, "Bad argument for %s\n", argv[i - 1]);
            return 2;
        }
    }
    static Curve cli;
    const Curve *cv = NULL;
    if (poly)
    {
        if (mm < 2 || mm > 8 || !gf_init(mm) || !parse_poly(poly, &cli, mm))
        {
            fprintf(stderr, "Bad --m (2..8) or --poly (example: --m 3 --poly \"x^3*y+y^3+x\")\n");
            return 2;
        }
        cv = &cli;
    }
    else
    {
        for (int c = 0; c < NCURVES; ++c)
            if (!strcmp(CURVES[c].name, cname))
                cv = &CURVES[c];
        if (!cv)
        {
            fprintf(stderr, "Unknown curve '%s' (see --list)\n", cname);
            return 2;
        }
        if (!gf_init(cv->m))
        {
            fprintf(stderr, "m must be in 2..8\n");
            return 2;
        }
    }

    /* 曲線の点 */
    int d = cv->deg, g = (d - 1) * (d - 2) / 2;
    Point *pts = malloc(sizeof(Point) * (size_t)GQ * GQ);
    int n = 0;
    for (int x = 0; x < GQ; ++x)
        for (int y = 0; y < GQ; ++y)
            if (eval_F(cv, (uint8_t)x, (uint8_t)y) == 0)
                pts[n++] = (Point){(uint8_t)x, (uint8_t)y};
    int sing = rational_singularities(cv);
    printf("Curve: %s\n", cv->desc);
    printf("GF(%d), degree d=%d, genus g=%d, affine rational points n=%d\n", GQ, d, g, n);
    if (sing)
        printf("WARNING: %d rational singular point(s) found; the curve is not smooth!\n", sing);
    else
        printf("(no rational singular point; non-rational singularities are NOT checked)\n");

    /* k1, k2 の自動選択: 保証される誤り数が最大になるもの */
    int best = -1;
    if (k1 == 0 || k2 == 0)
    {
        int b1 = 0, b2 = 0;
        for (int a = 1; a < 200; ++a)
            for (int b = 1; b < 200; ++b)
            {
                if ((a + b) * d >= n)
                    continue;
                int t = (b * d > 2 * g - 2) ? b * d - 2 * g + 1 : 0;
                int da = dim_poly(a, d) - 1;
                if (da < t)
                    t = da;
                if (t > best)
                {
                    best = t;
                    b1 = a;
                    b2 = b;
                }
            }
        if (!b1)
        {
            fprintf(stderr, "No admissible (k1,k2): too few points for this curve.\n");
            return 1;
        }
        if (!k1)
            k1 = b1;
        if (!k2)
            k2 = b2;
    }
    if (k1 < 1 || k2 < 1 || (k1 + k2) * d >= n)
    {
        fprintf(stderr, "Need k1,k2>=1 and (k1+k2)*d < n (here %d < %d).\n", (k1 + k2) * d, n);
        return 1;
    }

    Code code;
    code.n = n;
    code.A = build_basis(k1, pts, n);
    code.B = build_basis(k2, pts, n);
    code.H = build_basis(k1 + k2, pts, n);
    if (code.A.cnt != dim_poly(k1, d) || code.B.cnt != dim_poly(k2, d) ||
        code.H.cnt != dim_poly(k1 + k2, d))
    {
        fprintf(stderr, "Basis sizes disagree with the dimension formula "
                        "(curve not irreducible/smooth, or evaluation not injective).\n");
        return 1;
    }
    int tg = (k2 * d > 2 * g - 2) ? k2 * d - 2 * g + 1 : 0;
    if (code.A.cnt - 1 < tg)
        tg = code.A.cnt - 1;
    int cdim;
    uint8_t *ker = nullspace(code.H.v, code.H.cnt, n, &cdim);
    printf("k1=%d k2=%d : l(A)=%d, l(B)=%d, l(A+B)=%d\n", k1, k2, code.A.cnt, code.B.cnt, code.H.cnt);
    printf("Code C = dual of C_L(D,%dH): length %d, dimension %d, d_min >= %d\n",
           k1 + k2, n, cdim, (k1 + k2) * d - 2 * g + 2);
    printf("Guaranteed correctable errors (error-correcting pair): t <= %d\n", tg);
    if (cdim <= 0 || errors < 1 || errors > n)
    {
        fprintf(stderr, "Code dimension is 0 or --errors out of range.\n");
        return 1;
    }
    if (errors > tg)
        printf("NOTE: --errors=%d exceeds the guarantee; success is not guaranteed.\n", errors);

    rng_state = (uint64_t)seed * 0x2545F4914F6CDD1DULL + 12345;
    int succ = 0, fail = 0, miscor = 0;
    uint8_t *cw = malloc(n), *rcv = malloc(n), *err = malloc(n), *dec = malloc(n);
    int *idx = malloc(sizeof(int) * n);
    for (int tr = 0; tr < trials; ++tr)
    {
        memset(cw, 0, n);
        for (int t = 0; t < cdim; ++t)
        {
            uint8_t co = (uint8_t)(rnd() % GQ);
            for (int p = 0; p < n; ++p)
                cw[p] ^= gmul(co, ker[(size_t)t * n + p]);
        }
        memset(err, 0, n);
        for (int p = 0; p < n; ++p)
            idx[p] = p;
        for (int e = 0; e < errors; ++e)
        {
            int j = e + (int)(rnd() % (uint64_t)(n - e));
            int tmp = idx[e];
            idx[e] = idx[j];
            idx[j] = tmp;
            err[idx[e]] = (uint8_t)(1 + rnd() % (GQ - 1));
        }
        for (int p = 0; p < n; ++p)
            rcv[p] = cw[p] ^ err[p];
        int ne;
        int ok = decode(&code, rcv, dec, &ne);
        int same = ok && !memcmp(dec, cw, n);
        if (same)
            ++succ;
        else if (ok)
            ++miscor;
        else
            ++fail;
        if (trials == 1)
        {
            printf("\nInjected errors (index : (x,y) : value):\n");
            for (int e = 0; e < errors; ++e)
                printf("  %d : (%u,%u) : %u\n", idx[e], pts[idx[e]].x, pts[idx[e]].y, err[idx[e]]);
            if (ok)
            {
                printf("Decoded errors (index : (x,y) : value):\n");
                for (int p = 0; p < n; ++p)
                    if (dec[p] != rcv[p])
                        printf("  %d : (%u,%u) : %u\n", p, pts[p].x, pts[p].y, dec[p] ^ rcv[p]);
            }
            printf("Result: %s\n", same ? "PASS (original codeword recovered)"
                                        : ok ? "WRONG codeword (miscorrection)"
                                             : "FAIL (decoding failure detected)");
        }
    }
    if (trials > 1)
        printf("\n%d trials, %d errors each: success %d (%.1f%%), miscorrection %d, detected failure %d\n",
               trials, errors, succ, 100.0 * succ / trials, miscor, fail);
    return (trials == 1 && !succ) ? 1 : 0;
}
