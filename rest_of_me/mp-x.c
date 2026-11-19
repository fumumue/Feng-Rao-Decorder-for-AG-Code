/*
 * GF(3^2) 上の曲線 x^4 + y^3 + y = 0 (種数 g=3, 有理点 27 個, 無限遠点 Q 1 個)
 * の一点符号 C_Omega(P, W*Q) に対する Feng-Rao 基本アルゴリズムの復号器。
 *
 * 符号:  検査行列の行 = 重み 3a+4b <= WKNOWN の単項式 x^a y^b (b<=2)
 * 復号:  S_ij = S(phi_i phi_j) (重み w_i+w_j <= WKNOWN で既知) の行を重み順に
 *        見て、既知の列の範囲で前の行の一次結合になる最初の行 b_i を探す。
 *        b_i = phi_i + sum_{i'<i} alpha_i' phi_i' が誤り位置関数 (誤りの位置で 0)。
 *        その零点集合上で、既知シンドロームから誤り値を解く。
 * 保証:  誤り数 t <= (WKNOWN - 3g + 1) / 2   (WKNOWN=18 なら t <= 5)
 *
 * build: gcc -std=c11 -O3 -march=native -fopenmp hermitian_feng_rao.c -o hfr
 * usage: ./hfr [trials]    (trials: 誤り数ごとのランダム試行回数, 既定 20000)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

/* ---- パラメータ ---------------------------------------------------- */
#define CHAR_P 3
#define EXT_M 2
#define FIELD_N 9                /* CHAR_P^EXT_M (<=256) */
#define NPOS 27                  /* 有理点数 = 符号長 */
#define GENUS 3
#define XMAX 8
#define YMAX 2
#define NBASIS ((XMAX + 1) * (YMAX + 1))
#define WX 3                     /* x の重み (極の位数) */
#define WY 4                     /* y の重み */
#ifndef WKNOWN
#define WKNOWN 18                /* 既知シンドロームの最大重み (t<=5 なら 18) */
#endif
#define TBASIC ((WKNOWN - 3 * GENUS + 1) / 2)
#define SA (WKNOWN / WX + 1)
#define SB (WKNOWN / WY + 1)
#define TTEST (TBASIC + 2)

_Static_assert(FIELD_N == CHAR_P * CHAR_P && EXT_M == 2, "field size mismatch");
_Static_assert(WKNOWN >= 3 * GENUS - 1, "WKNOWN too small");

/* 原始多項式 x^2 + x + 2 */
static const int PRIM[EXT_M] = {2, 1};

/* 曲線 sum c x^a y^b = 0。decode の曲線関係式 y^3 = -y - x^4 はこの定義に依存 */
typedef struct { int a, b; uint8_t c; } Term;
static const Term CURVE[] = {{4, 0, 1}, {0, 3, 1}, {0, 1, 1}};
#define NTERMS ((int)(sizeof CURVE / sizeof CURVE[0]))

/* ---- 有限体 -------------------------------------------------------- */
static uint8_t EXP[2 * FIELD_N], LOG[FIELD_N];
static uint8_t ADD[FIELD_N][FIELD_N], MUL[FIELD_N][FIELD_N];
static uint8_t NEG[FIELD_N], INV[FIELD_N];
static uint8_t POWT[XMAX + 1][FIELD_N];
static uint8_t DIG[EXT_M][FIELD_N];

static void to_digits(int v, int d[EXT_M])
{
    for (int i = 0; i < EXT_M; i++) { d[i] = v % CHAR_P; v /= CHAR_P; }
}

static int from_digits(const int d[EXT_M])
{
    int v = 0;
    for (int i = EXT_M - 1; i >= 0; i--) v = v * CHAR_P + d[i];
    return v;
}

static int build_field(void)
{
    int d[EXT_M] = {1, 0};

    for (int k = 0; k < FIELD_N - 1; k++) {
        int v = from_digits(d);
        if (k > 0 && v == 1) return -1;
        EXP[k] = (uint8_t)v;
        LOG[v] = (uint8_t)k;
        int top = d[EXT_M - 1];
        for (int i = EXT_M - 1; i > 0; i--) d[i] = d[i - 1];
        d[0] = 0;
        for (int i = 0; i < EXT_M; i++)
            d[i] = ((d[i] - top * PRIM[i]) % CHAR_P + CHAR_P) % CHAR_P;
    }
    if (from_digits(d) != 1) return -1;
    for (int k = 0; k < FIELD_N - 1; k++) EXP[k + FIELD_N - 1] = EXP[k];

    for (int a = 0; a < FIELD_N; a++) {
        int da[EXT_M], n[EXT_M];
        to_digits(a, da);
        for (int i = 0; i < EXT_M; i++) {
            DIG[i][a] = (uint8_t)da[i];
            n[i] = (CHAR_P - da[i]) % CHAR_P;
        }
        NEG[a] = (uint8_t)from_digits(n);
        INV[a] = a ? EXP[(FIELD_N - 1 - LOG[a]) % (FIELD_N - 1)] : 0;
        for (int b = 0; b < FIELD_N; b++) {
            int db[EXT_M], s[EXT_M];
            to_digits(b, db);
            for (int i = 0; i < EXT_M; i++) s[i] = (da[i] + db[i]) % CHAR_P;
            ADD[a][b] = (uint8_t)from_digits(s);
            MUL[a][b] = (a && b) ? EXP[LOG[a] + LOG[b]] : 0;
        }
    }
    for (int v = 0; v < FIELD_N; v++) {
        POWT[0][v] = 1;
        for (int e = 1; e <= XMAX; e++) POWT[e][v] = MUL[POWT[e - 1][v]][v];
    }
    return 0;
}

/* ---- 点・基底・検査行列 -------------------------------------------- */
static uint8_t PX[NPOS], PY[NPOS];
static int BAS[NBASIS][2];
static uint8_t HH[NBASIS][NPOS];
static int NK;                         /* 重み <= WKNOWN の基底数 */

static inline int weight(int i) { return WX * BAS[i][0] + WY * BAS[i][1]; }

static int find_points(void)
{
    static uint8_t on[FIELD_N * FIELD_N];

    #pragma omp parallel for simd
    for (int k = 0; k < FIELD_N * FIELD_N; k++) {
        int x = k / FIELD_N, y = k % FIELD_N;
        uint8_t s = 0;
        for (int t = 0; t < NTERMS; t++) {
            uint8_t m = MUL[POWT[CURVE[t].a][x]][POWT[CURVE[t].b][y]];
            s = ADD[s][MUL[CURVE[t].c][m]];
        }
        on[k] = (s == 0);
    }
    int n = 0;
    for (int k = 0; k < FIELD_N * FIELD_N; k++) {
        if (!on[k]) continue;
        if (n >= NPOS) return -1;
        PX[n] = (uint8_t)(k / FIELD_N);
        PY[n] = (uint8_t)(k % FIELD_N);
        n++;
    }
    return n;
}

static int cmp_weight(const void *p, const void *q)
{
    const int *u = p, *v = q;
    return (WX * u[0] + WY * u[1]) - (WX * v[0] + WY * v[1]);
}

static void build_matrix(void)
{
    int n = 0;
    for (int b = 0; b <= YMAX; b++)
        for (int a = 0; a <= XMAX; a++) { BAS[n][0] = a; BAS[n][1] = b; n++; }
    qsort(BAS, NBASIS, sizeof BAS[0], cmp_weight);

    NK = 0;
    while (NK < NBASIS && weight(NK) <= WKNOWN) NK++;

    #pragma omp parallel for
    for (int i = 0; i < NBASIS; i++) {
        const uint8_t *pa = POWT[BAS[i][0]], *pb = POWT[BAS[i][1]];
        #pragma omp simd
        for (int j = 0; j < NPOS; j++)
            HH[i][j] = MUL[pa[PX[j]]][pb[PY[j]]];
    }
}

/* ---- シンドローム: syn[i] = sum_j err[j] * HH[i][j]  (i < n) ------- */
static void compute_syndromes(const uint8_t err[NPOS], uint8_t *syn, int n)
{
    for (int i = 0; i < n; i++) {
        int dg[EXT_M];
        for (int d = 0; d < EXT_M; d++) {
            int s = 0;
            #pragma omp simd reduction(+ : s)
            for (int j = 0; j < NPOS; j++)
                s += DIG[d][MUL[err[j]][HH[i][j]]];
            dg[d] = s % CHAR_P;
        }
        syn[i] = (uint8_t)from_digits(dg);
    }
}

/* ---- GF 上の連立一次方程式 ----------------------------------------- */
/* M: rows x (cols+1) の拡大係数行列 (破壊される)。
   解が存在すれば 0 (自由変数は 0)、矛盾なら -1 */
static int gf_solve(uint8_t *M, int rows, int cols, uint8_t *x)
{
    const int st = cols + 1;
    int piv[NPOS + 1], r = 0;

    for (int c = 0; c < cols && r < rows; c++) {
        int p = r;
        while (p < rows && M[p * st + c] == 0) p++;
        if (p == rows) continue;
        if (p != r)
            for (int k = 0; k < st; k++) {
                uint8_t t = M[p * st + k]; M[p * st + k] = M[r * st + k]; M[r * st + k] = t;
            }
        uint8_t iv = INV[M[r * st + c]];
        #pragma omp simd
        for (int k = 0; k < st; k++) M[r * st + k] = MUL[iv][M[r * st + k]];
        for (int q = 0; q < rows; q++) {
            uint8_t f = NEG[M[q * st + c]];
            if (q == r || f == 0) continue;
            #pragma omp simd
            for (int k = 0; k < st; k++)
                M[q * st + k] = ADD[M[q * st + k]][MUL[f][M[r * st + k]]];
        }
        piv[r++] = c;
    }
    for (int q = r; q < rows; q++)
        if (M[q * st + cols] != 0) return -1;
    memset(x, 0, (size_t)cols);
    for (int q = 0; q < r; q++) x[piv[q]] = M[q * st + cols];
    return 0;
}

/* ---- Feng-Rao 基本アルゴリズム ------------------------------------- */
/* syn: 既知シンドローム syn[0..NK-1] (BAS の重み順)。
   成功で 0 を返し out に誤りベクトルを書く。失敗 (訂正能力超過) は -1 */
static int decode(const uint8_t *syn, uint8_t out[NPOS])
{
    uint8_t Sf[SA][SB] = {{0}};
    uint8_t M[NBASIS * (NPOS + 1)], x[NPOS + 1], c[NBASIS], hv[NPOS];
    int found = -1;

    /* 既知シンドロームを単項式表に置き、y^3 = -y - x^4 で b>=3 へ拡張 */
    for (int i = 0; i < NK; i++) Sf[BAS[i][0]][BAS[i][1]] = syn[i];
    for (int b = YMAX + 1; b < SB; b++)
        for (int a = 0; a < SA; a++)
            if (WX * a + WY * b <= WKNOWN)
                Sf[a][b] = NEG[ADD[Sf[a][b - 2]][Sf[a + 4][b - 3]]];

    /* 重み順に行を見て、既知の列範囲で従属する最初の行を探す */
    for (int i = 0; i < NK && weight(i) <= TBASIC + GENUS; i++) {
        int nj = 0;
        while (nj < NK && weight(nj) <= WKNOWN - weight(i)) nj++;
        const int st = i + 1;
        for (int j = 0; j < nj; j++) {
            for (int k = 0; k < i; k++)
                M[j * st + k] = Sf[BAS[k][0] + BAS[j][0]][BAS[k][1] + BAS[j][1]];
            M[j * st + i] = NEG[Sf[BAS[i][0] + BAS[j][0]][BAS[i][1] + BAS[j][1]]];
        }
        if (gf_solve(M, nj, i, x) == 0) {
            for (int k = 0; k < i; k++) c[k] = x[k];
            c[i] = 1;
            found = i;
            break;
        }
    }
    if (found < 0) return -1;

    /* 誤り位置関数 h = sum c_k phi_k の零点集合 Z */
    memset(hv, 0, sizeof hv);
    for (int k = 0; k <= found; k++) {
        const uint8_t ck = c[k];
        #pragma omp simd
        for (int j = 0; j < NPOS; j++) hv[j] = ADD[hv[j]][MUL[ck][HH[k][j]]];
    }
    int z[NPOS], nz = 0;
    for (int j = 0; j < NPOS; j++)
        if (hv[j] == 0) z[nz++] = j;

    /* Z 上で sum_{j in Z} e_j HH[r][j] = syn[r] (r < NK) を解く */
    const int st = nz + 1;
    for (int r = 0; r < NK; r++) {
        for (int k = 0; k < nz; k++) M[r * st + k] = HH[r][z[k]];
        M[r * st + nz] = syn[r];
    }
    if (gf_solve(M, NK, nz, x) != 0) return -1;

    memset(out, 0, NPOS);
    for (int k = 0; k < nz; k++) out[z[k]] = x[k];
    return 0;
}

/* ---- 自己テスト ----------------------------------------------------- */
static inline uint64_t splitmix(uint64_t *s)
{
    uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static void self_test(int trials)
{
    printf("known weight W=%d, guaranteed t<=%d\n", WKNOWN, TBASIC);
    printf("t  correct  detected  miscorrect  (trials=%d)\n", trials);

    for (int t = 0; t <= TTEST; t++) {
        long ok = 0, fail = 0, wrong = 0;

        #pragma omp parallel for reduction(+ : ok, fail, wrong)
        for (int n = 0; n < trials; n++) {
            uint64_t rng = ((uint64_t)t << 40) ^ (uint64_t)n;
            uint8_t err[NPOS] = {0}, syn[NBASIS], dec[NPOS];

            for (int w = 0; w < t;) {
                int pos = (int)(splitmix(&rng) % NPOS);
                if (err[pos]) continue;
                err[pos] = (uint8_t)(1 + splitmix(&rng) % (FIELD_N - 1));
                w++;
            }
            compute_syndromes(err, syn, NK);
            if (decode(syn, dec) != 0)             fail++;
            else if (memcmp(err, dec, NPOS) == 0)  ok++;
            else                                   wrong++;
        }
        printf("%d  %7ld  %8ld  %10ld\n", t, ok, fail, wrong);
    }
}

/* ---- main ---------------------------------------------------------- */
int main(int argc, char **argv)
{
    int trials = argc > 1 ? atoi(argv[1]) : 20000;
    uint8_t err[NPOS] = {[0] = 1, [3] = 4, [10] = 7, [20] = 5, [25] = 2}, syn[NBASIS], dec[NPOS];

    if (build_field() != 0) {
        fprintf(stderr, "error: PRIM is not a primitive polynomial\n");
        return EXIT_FAILURE;
    }
    int npts = find_points();
    if (npts != NPOS) {
        fprintf(stderr, "error: found %d points, expected %d\n", npts, NPOS);
        return EXIT_FAILURE;
    }
    build_matrix();

    compute_syndromes(err, syn, NK);
    if (decode(syn, dec) != 0) {
        fprintf(stderr, "decoding failure\n");
        return EXIT_FAILURE;
    }
    printf("received syndromes (a,b):value\n");
    for (int i = 0; i < NK; i++) printf("(%d,%d):%d ", BAS[i][0], BAS[i][1], syn[i]);
    printf("\nerrors (position@(x,y) = value)\n");
    for (int j = 0; j < NPOS; j++)
        if (dec[j]) printf("  %d@(%d,%d) = %d\n", j, PX[j], PY[j], dec[j]);
    printf("example: %s\n\n", memcmp(err, dec, NPOS) == 0 ? "OK" : "MISMATCH");

    if (trials > 0) self_test(trials);
    return EXIT_SUCCESS;
}