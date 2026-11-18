/*
 * Suzuki curve over GF(2^12), q = 8, q0 = 2:  y^8 + y = x^2 (x^8 + x)
 * One-point code C = C_L(D, M P_inf)^perp  (g = 14, H = <8,10,12,13>).
 *
 * Three error-locator algorithms on the same syndromes, with timing:
 *
 *  FR    Feng-Rao basic algorithm (row reduction of the syndrome matrix
 *        S[i][j] = s(phi_i phi_j)), positions from the characteristic
 *        polynomial of S0^-1 SX.  Corrects t <= (M - 3g + 1)/2.
 *
 *  BMS   Sakata's algorithm: sweep the anti-diagonals n = rho_i + rho_j,
 *        keep only the minimal polynomials of the generators of the ideal E
 *        of leading orders, stored as VALUE VECTORS (no structure constants).
 *        Same pivots as FR, same radius, much faster.
 *
 *  VOTE  BMS + Feng-Rao majority voting.  The syndrome s is known on
 *        L(M P) only.  The g next values s(phi_u), u = M+1..M+g, are found
 *        one by one by voting: every pair (i,j), rho_i+rho_j = u, with row i
 *        not a known pivot row and column j not a known pivot column is a
 *        candidate; it predicts the value for which row i would have
 *        discrepancy 0.  Candidates that are in fact new pivots predict
 *        wrong values, but they are outnumbered as long as
 *            t <= (M - 2g + 1)/2   (half the designed distance),
 *        i.e. g/2 = 7 errors more than the basic algorithm.  With the
 *        syndromes extended to M+g the BMS sweep goes on to position M+g.
 *        To evaluate s on functions of order > M the coefficients on the top
 *        g basis functions are read off the values at NB selected points with
 *        a dual basis (computed once per code).
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki_vote suzuki_vote.c
 * Run:   ./suzuki_vote [-fr] [-bms] [-vote] [-v] [-p] [-a] [seed]
 *        -fr/-bms/-vote : run only the named algorithms (default: all)
 *        -v : print every vote,  -p : list all affine points,
 *        -a : print the complete error lists
 *        -DM_SYND=1028 -DNUM_ERRORS=500 etc. can be given at compile time.
 */

#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define FIELD_M 12
#define FIELD_SIZE (1u << FIELD_M)
#define FIELD_ORDER (FIELD_SIZE - 1u)
#define FIELD_POLY 0x1053u

#define SUZUKI_Q 8u
#define SUZUKI_Q0 2u
#define MAX_FIBER 8u
#define MAX_POINTS 5888u
#define GENUS 14                /* q0 (q - 1) */

/* ---- code / experiment parameters ---- */
#ifndef M_SYND
#define M_SYND 1024               /* syndromes known for h in L(M_SYND P_inf) */
#endif
#ifndef NUM_ERRORS
#define NUM_ERRORS 256            /* injected errors, must be <= TAU          */
#endif

#define TAU ((M_SYND - 3 * GENUS + 1) / 2)   /* basic algorithm             */
#define TAU_V ((M_SYND - 2 * GENUS + 1) / 2) /* with majority voting        */
#define M_EXT (M_SYND + GENUS)               /* syndromes after voting      */
#define L_DEG (TAU + GENUS)                  /* locators are in L(L_DEG P)  */
#define ROW_MAX (M_SYND - 8)                 /* FR: rows processed          */

#if TAU < 1
#error "M_SYND too small: need M_SYND >= 3*GENUS + 1 = 43"
#endif

#define MAX_BASIS (M_EXT + 1)   /* number of semigroup elements <= M_EXT    */
#define MAXT (TAU_V + 2)        /* maximal number of errors (staircase)     */
#define SG_MAX (M_EXT + 16)     /* semigroup bookkeeping range              */
#define MAXGEN 16               /* generators of E: at most q = 8           */
#define PRINT_LOCATORS 3        /* FR: how many locators are printed        */
#define PRINT_TERMS 12          /* FR: terms printed per locator            */

typedef struct {
    uint16_t x;
    uint16_t y;
} Point;

typedef struct {
    int a, b, c, d;             /* monomial x^a y^b z^c w^d */
    int rho;                    /* pole order               */
    uint16_t *val;              /* values at the n points   */
} Basis;

static Point pts[MAX_POINTS];
static uint32_t npts;
static int first_of_x[FIELD_SIZE];
static int count_of_x[FIELD_SIZE];

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ------------------------------------------------------------------ */
/* GF(2^12) arithmetic (log / antilog tables, X is primitive)         */
/* ------------------------------------------------------------------ */

static uint16_t gexp[2 * FIELD_ORDER + 2];
static uint16_t glog[FIELD_SIZE];

static int gf_init(void)
{
    uint32_t x = 1;

    for (uint32_t i = 0; i < FIELD_ORDER; ++i) {
        if (i > 0 && x == 1)
            return -1;                  /* X is not primitive */
        gexp[i] = (uint16_t)x;
        glog[x] = (uint16_t)i;
        x <<= 1;
        if (x & FIELD_SIZE)
            x ^= FIELD_POLY;
    }
    if (x != 1)
        return -1;
    for (uint32_t i = FIELD_ORDER; i < 2 * FIELD_ORDER + 2; ++i)
        gexp[i] = gexp[i - FIELD_ORDER];
    return 0;
}

static inline uint16_t gf_mul(uint16_t a, uint16_t b)
{
    if (a == 0 || b == 0)
        return 0;
    return gexp[glog[a] + glog[b]];
}

static uint16_t gf_pow(uint16_t a, unsigned int n)
{
    if (n == 0)
        return 1;
    if (a == 0)
        return 0;
    return gexp[((uint32_t)glog[a] * (n % FIELD_ORDER)) % FIELD_ORDER];
}

static inline uint16_t gf_inv(uint16_t a)
{
    return gexp[FIELD_ORDER - glog[a]];     /* a != 0 */
}

static uint16_t q_power(uint16_t a)
{
    return gf_pow(a, SUZUKI_Q);
}

/* ------------------------------------------------------------------ */
/* Point enumeration (only defines the code coordinates)              */
/* ------------------------------------------------------------------ */

static int enumerate_points(int print_points)
{
    static uint16_t fiber[FIELD_SIZE][MAX_FIBER];
    static uint8_t fiber_count[FIELD_SIZE];

    npts = 0;
    for (uint32_t y = 0; y < FIELD_SIZE; ++y) {
        uint16_t value = (uint16_t)(q_power((uint16_t)y) ^ y);
        uint8_t n = fiber_count[value];

        if (n >= MAX_FIBER) {
            fprintf(stderr, "Unexpected fiber size at value %u\n", value);
            return -1;
        }
        fiber[value][n] = (uint16_t)y;
        fiber_count[value] = (uint8_t)(n + 1);
    }

    if (print_points)
        puts("# Affine points (x,y):");

    for (uint32_t x = 0; x < FIELD_SIZE; ++x) {
        uint16_t xq = q_power((uint16_t)x);
        uint16_t xq0 = gf_pow((uint16_t)x, SUZUKI_Q0);
        uint16_t rhs = gf_mul(xq0, (uint16_t)(xq ^ x));

        first_of_x[x] = (int)npts;
        count_of_x[x] = fiber_count[rhs];
        for (uint8_t j = 0; j < fiber_count[rhs]; ++j) {
            if (npts >= MAX_POINTS) {
                fprintf(stderr, "Too many points\n");
                return -1;
            }
            pts[npts].x = (uint16_t)x;
            pts[npts].y = fiber[rhs][j];
            if (print_points)
                printf("%u,%u\n", x, fiber[rhs][j]);
            ++npts;
        }
    }

    if (npts != MAX_POINTS) {
        fprintf(stderr, "Point-count check failed (expected %u, got %u).\n",
                MAX_POINTS, npts);
        return -1;
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Basis of L(M P_inf): one monomial per semigroup element            */
/* ------------------------------------------------------------------ */

static Basis basis[MAX_BASIS];
static int nbasis;

static uint16_t monomial_value(const Basis *f, uint16_t x, uint16_t y)
{
    uint16_t y4 = gf_pow(y, 4);
    uint16_t z = (uint16_t)(gf_pow(x, 5) ^ y4);             /* x^5 + y^4   */
    uint16_t w = (uint16_t)(gf_mul(x, y4) ^ gf_pow(z, 4));  /* x y^4 + z^4 */
    uint16_t v = gf_pow(x, (unsigned)f->a);

    v = gf_mul(v, gf_pow(y, (unsigned)f->b));
    v = gf_mul(v, gf_pow(z, (unsigned)f->c));
    v = gf_mul(v, gf_pow(w, (unsigned)f->d));
    return v;
}

static int build_basis(int maxrho)
{
    nbasis = 0;
    for (int s = 0; s <= maxrho; ++s) {
        int found = 0, fa = 0, fb = 0, fc = 0, fd = 0;

        for (int d = 0; 13 * d <= s && !found; ++d)
            for (int c = 0; 13 * d + 12 * c <= s && !found; ++c)
                for (int b = 0; 13 * d + 12 * c + 10 * b <= s && !found; ++b) {
                    int r = s - 13 * d - 12 * c - 10 * b;
                    if (r % 8 == 0) {
                        found = 1;
                        fa = r / 8; fb = b; fc = c; fd = d;
                    }
                }
        if (!found)
            continue;                       /* s is a gap */
        if (nbasis >= MAX_BASIS) {
            fprintf(stderr, "Basis too large (increase MAX_BASIS)\n");
            return -1;
        }
        basis[nbasis].a = fa;
        basis[nbasis].b = fb;
        basis[nbasis].c = fc;
        basis[nbasis].d = fd;
        basis[nbasis].rho = s;
        basis[nbasis].val = malloc(sizeof(uint16_t) * npts);
        if (basis[nbasis].val == NULL)
            return -1;
        ++nbasis;
    }

    for (uint32_t k = 0; k < npts; ++k)
        for (int i = 0; i < nbasis; ++i)
            basis[i].val[k] = monomial_value(&basis[i], pts[k].x, pts[k].y);
    return 0;
}

static int count_basis_upto(int rho)
{
    int n = 0;
    for (int i = 0; i < nbasis; ++i)
        if (basis[i].rho <= rho)
            ++n;
    return n;
}

static void print_monomial(const Basis *f)
{
    int printed = 0;
    if (f->a) { printf("x^%d", f->a); printed = 1; }
    if (f->b) { printf("%sy^%d", printed ? "*" : "", f->b); printed = 1; }
    if (f->c) { printf("%sz^%d", printed ? "*" : "", f->c); printed = 1; }
    if (f->d) { printf("%sw^%d", printed ? "*" : "", f->d); printed = 1; }
    if (!printed)
        printf("1");
}

/* semigroup membership and "pole order -> index in basis[]" */
static int in_H[SG_MAX];
static int idx_of_ord[SG_MAX];

static void init_semigroup(void)
{
    for (int x = 0; x < SG_MAX; ++x) {
        in_H[x] = (x == 0) || (x >= 8 && in_H[x - 8]) ||
                  (x >= 10 && in_H[x - 10]) || (x >= 12 && in_H[x - 12]) ||
                  (x >= 13 && in_H[x - 13]);
        idx_of_ord[x] = -1;
    }
    for (int i = 0; i < nbasis; ++i)
        idx_of_ord[basis[i].rho] = i;
}

/* ------------------------------------------------------------------ */
/* Syndromes: s(h) = sum_k r_k h(P_k)  (only non-zero r_k contribute) */
/* ------------------------------------------------------------------ */

static const uint16_t *recv;
static uint32_t nz_idx[MAX_POINTS];
static uint32_t nz_cnt;

static uint16_t synd(int ia, int ib, const uint16_t *wt)
{
    uint16_t acc = 0;

    for (uint32_t n = 0; n < nz_cnt; ++n) {
        uint32_t k = nz_idx[n];
        uint16_t term = gf_mul(recv[k],
                               gf_mul(basis[ia].val[k], basis[ib].val[k]));
        if (wt != NULL)
            term = gf_mul(term, wt[k]);
        acc ^= term;
    }
    return acc;
}

/* ------------------------------------------------------------------ */
/* Result of one decoder run                                          */
/* ------------------------------------------------------------------ */

typedef struct {
    int T;                          /* staircase size = estimated t      */
    int nfound, resolved, overflow, failed;
    uint32_t pos[MAXT + 1];
    uint16_t val[MAXT + 1];
    uint8_t rowset[M_EXT + 1];      /* pole orders of the pivot rows     */
    uint8_t colset[M_EXT + 1];      /* pole orders of the pivot columns  */
    int vote_steps, vote_wrong, vote_tie, vote_min_margin;
    double t_main;                  /* locators (FR reduction / BMS)     */
    double t_extract;               /* error positions from the locators */
    double t_resolve;               /* error values                      */
} Result;

static Result res_fr, res_bms, res_vote;

/* ------------------------------------------------------------------ */
/* Candidate points beyond t (only possible near the limit t = tau):   */
/* solve  sum_k e_k phi_a(P_k) = s(phi_a)  for the candidates; the true */
/* error positions are the non-zero e_k.                              */
/* ------------------------------------------------------------------ */

static uint16_t aug[MAX_BASIS][MAXT + 2];
static uint16_t err_val[MAXT + 1];

static uint16_t synd1(int ia)
{
    uint16_t acc = 0;

    for (uint32_t n = 0; n < nz_cnt; ++n)
        acc ^= gf_mul(recv[nz_idx[n]], basis[ia].val[nz_idx[n]]);
    return acc;
}

static int resolve_by_values(uint32_t *found, int *nfound)
{
    int n = *nfound, m = count_basis_upto(M_SYND);   /* honest syndromes only */

    for (int a = 0; a < m; ++a) {
        for (int k = 0; k < n; ++k)
            aug[a][k] = basis[a].val[found[k]];
        aug[a][n] = synd1(a);
    }
    for (int c = 0; c < n; ++c) {
        int p = -1;
        for (int a = c; a < m; ++a)
            if (aug[a][c] != 0) { p = a; break; }
        if (p < 0)
            return 0;                       /* not determined */
        if (p != c)
            for (int k = 0; k <= n; ++k) {
                uint16_t t = aug[p][k]; aug[p][k] = aug[c][k]; aug[c][k] = t;
            }
        uint16_t inv = gf_inv(aug[c][c]);
        for (int k = c; k <= n; ++k)
            aug[c][k] = gf_mul(aug[c][k], inv);
        for (int a = 0; a < m; ++a) {
            uint16_t f = aug[a][c];
            if (a == c || f == 0)
                continue;
            for (int k = c; k <= n; ++k)
                aug[a][k] ^= gf_mul(f, aug[c][k]);
        }
    }
    for (int a = n; a < m; ++a)
        if (aug[a][n] != 0)
            return 0;                       /* inconsistent */
    int keep = 0;
    for (int k = 0; k < n; ++k)
        if (aug[k][n] != 0) {
            found[keep] = found[k];
            err_val[keep] = aug[k][n];
            ++keep;
        }
    *nfound = keep;
    return 1;
}

static void resolve_and_store(Result *R)
{
    double t0 = now();
    int resolved = 0;

    if (!R->overflow && R->nfound > 0) {
        if (R->nfound > R->T)
            printf("#   %d common zeros > t = %d: resolving by error values\n",
                   R->nfound, R->T);
        resolved = resolve_by_values(R->pos, &R->nfound);
        if (!resolved)
            puts("#   could not compute the error values.");
    }
    R->resolved = resolved;
    for (int m = 0; m < R->nfound; ++m)
        R->val[m] = resolved ? err_val[m] : 0;
    R->t_resolve = now() - t0;
}

/* ================================================================== */
/*  FR: Feng-Rao basic algorithm + characteristic polynomial          */
/* ================================================================== */

static uint16_t red[MAX_BASIS][MAX_BASIS];    /* reduced rows             */
static uint16_t coef[MAX_BASIS][MAX_BASIS];   /* f_i = sum coef[i][k] phi_k */
static int piv_of_row[MAX_BASIS];             /* pivot column or -1       */
static int row_of_col[MAX_BASIS];
static uint16_t pivinv[MAX_BASIS];

/* returns the number of rows processed */
static int feng_rao_reduce(void)
{
    int nrows = count_basis_upto(ROW_MAX);

    for (int j = 0; j < MAX_BASIS; ++j)
        row_of_col[j] = -1;

    for (int i = 0; i < nrows; ++i) {
        int ncol = count_basis_upto(M_SYND - basis[i].rho);

        for (int j = 0; j < ncol; ++j)
            red[i][j] = synd(i, j, NULL);
        memset(coef[i], 0, sizeof(coef[i]));
        coef[i][i] = 1;
        piv_of_row[i] = -1;

        for (int j = 0; j < ncol; ++j) {
            uint16_t v = red[i][j];
            int p;

            if (v == 0)
                continue;
            p = row_of_col[j];
            if (p >= 0) {
                uint16_t f = gf_mul(v, pivinv[p]);
                for (int jj = j; jj < ncol; ++jj)
                    red[i][jj] ^= gf_mul(f, red[p][jj]);
                for (int k = 0; k <= p; ++k)
                    coef[i][k] ^= gf_mul(f, coef[p][k]);
            } else {
                piv_of_row[i] = j;
                row_of_col[j] = i;
                pivinv[i] = gf_inv(v);
                break;
            }
        }
    }
    return nrows;
}

typedef uint16_t Mat[MAXT][MAXT];

static Mat S0, SX, S0inv, Q, WORK;
static uint16_t pol[MAXT + 1][MAXT + 1];     /* p_k(theta), k = 0..n */

/* Gauss-Jordan inverse of m (n x n) into out; returns 0 if singular */
static int mat_inverse(Mat m, Mat out, int n)
{
    memcpy(WORK, m, sizeof(Mat));
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j)
            out[i][j] = 0;
        out[i][i] = 1;
    }
    for (int c = 0; c < n; ++c) {
        int p = -1;
        for (int r = c; r < n; ++r)
            if (WORK[r][c] != 0) { p = r; break; }
        if (p < 0)
            return 0;
        if (p != c)
            for (int i = 0; i < n; ++i) {
                uint16_t t;
                t = WORK[p][i]; WORK[p][i] = WORK[c][i]; WORK[c][i] = t;
                t = out[p][i];  out[p][i]  = out[c][i];  out[c][i]  = t;
            }
        uint16_t inv = gf_inv(WORK[c][c]);
        for (int i = 0; i < n; ++i) {
            WORK[c][i] = gf_mul(WORK[c][i], inv);
            out[c][i] = gf_mul(out[c][i], inv);
        }
        for (int r = 0; r < n; ++r) {
            uint16_t f = WORK[r][c];
            if (r == c || f == 0)
                continue;
            for (int i = 0; i < n; ++i) {
                WORK[r][i] ^= gf_mul(f, WORK[c][i]);
                out[r][i] ^= gf_mul(f, out[c][i]);
            }
        }
    }
    return 1;
}

/*
 * Characteristic polynomial det(theta I + H) of an n x n matrix.
 * H is destroyed (reduced to upper Hessenberg form by similarity).
 * The result (monic, degree n) is written to g[0..n].
 */
static void charpoly(Mat H, int n, uint16_t *g)
{
    for (int k = 0; k + 2 < n; ++k) {
        int p = -1;
        for (int i = k + 1; i < n; ++i)
            if (H[i][k] != 0) { p = i; break; }
        if (p < 0)
            continue;
        if (p != k + 1) {                       /* swap rows and columns */
            for (int j = 0; j < n; ++j) {
                uint16_t t = H[p][j]; H[p][j] = H[k + 1][j]; H[k + 1][j] = t;
            }
            for (int i = 0; i < n; ++i) {
                uint16_t t = H[i][p]; H[i][p] = H[i][k + 1]; H[i][k + 1] = t;
            }
        }
        uint16_t inv = gf_inv(H[k + 1][k]);
        for (int i = k + 2; i < n; ++i) {
            if (H[i][k] == 0)
                continue;
            uint16_t f = gf_mul(H[i][k], inv);
            for (int j = 0; j < n; ++j)         /* row_i += f row_{k+1} */
                H[i][j] ^= gf_mul(f, H[k + 1][j]);
            for (int r = 0; r < n; ++r)         /* col_{k+1} += f col_i */
                H[r][k + 1] ^= gf_mul(f, H[r][i]);
        }
    }

    /* p_0 = 1,  p_k = (theta + h_kk) p_{k-1}
     *                 + sum_{i=1}^{k-1} h_{k-i,k} (prod_{j=k-i+1}^{k} h_{j,j-1}) p_{k-i-1}
     * (1-based indices in the formula, 0-based in the code)              */
    pol[0][0] = 1;
    for (int k = 1; k <= n; ++k) {
        uint16_t prod = 1;

        for (int d = 0; d <= k; ++d)
            pol[k][d] = 0;
        for (int d = 0; d < k; ++d) {                       /* theta * p_{k-1} */
            pol[k][d + 1] ^= pol[k - 1][d];
            pol[k][d] ^= gf_mul(H[k - 1][k - 1], pol[k - 1][d]);
        }
        for (int i = 1; i <= k - 1; ++i) {
            prod = gf_mul(prod, H[k - i][k - i - 1]);       /* h_{k-i+1,k-i} */
            if (prod == 0)
                break;
            uint16_t c = gf_mul(H[k - i - 1][k - 1], prod); /* h_{k-i,k}     */
            if (c == 0)
                continue;
            for (int d = 0; d <= k - i - 1; ++d)
                pol[k][d] ^= gf_mul(c, pol[k - i - 1][d]);
        }
    }
    for (int d = 0; d <= n; ++d)
        g[d] = pol[n][d];
}

static uint16_t poly_eval(const uint16_t *poly, int deg, uint16_t t)
{
    uint16_t acc = poly[deg];

    for (int i = deg - 1; i >= 0; --i)
        acc = (uint16_t)(gf_mul(acc, t) ^ poly[i]);
    return acc;
}

static void print_locator(int i)
{
    int first = 1, terms = 0;

    printf("  f_%d = ", basis[i].rho);
    for (int k = i; k >= 0; --k) {
        if (coef[i][k] == 0)
            continue;
        if (terms == PRINT_TERMS) {
            printf(" + ...");
            break;
        }
        printf("%s%u*", first ? "" : " + ", coef[i][k]);
        print_monomial(&basis[k]);
        first = 0;
        ++terms;
    }
    printf("\n");
}

static int decode_fr(Result *R)
{
    static int Rr[MAXT], Cc[MAXT];
    static uint16_t g[MAXT + 1];
    static uint16_t xv[MAX_POINTS];
    static uint16_t roots[FIELD_SIZE];
    int T = 0, nl, nloc = 0;
    double t0 = now();

    memset(R, 0, sizeof *R);
    int nrows = feng_rao_reduce();
    nl = count_basis_upto(L_DEG);
    for (int i = 0; i < nl; ++i)
        if (piv_of_row[i] < 0)
            ++nloc;
    for (int i = 0; i < nrows; ++i)
        if (piv_of_row[i] >= 0) {
            if (T >= MAXT) {
                fprintf(stderr, "FR: too many pivots\n");
                R->failed = 1;
                return -1;
            }
            Rr[T] = i;
            Cc[T] = piv_of_row[i];
            R->rowset[basis[i].rho] = 1;
            R->colset[basis[piv_of_row[i]].rho] = 1;
            ++T;
        }
    R->T = T;
    R->t_main = now() - t0;

    printf("# FR : %d error locators with rho <= %d (first %d shown):\n",
           nloc, L_DEG, PRINT_LOCATORS);
    for (int i = 0, shown = 0; i < nl && shown < PRINT_LOCATORS; ++i)
        if (piv_of_row[i] < 0) {
            print_locator(i);
            ++shown;
        }
    printf("# FR : staircase of %d elements -> estimated t = %d\n", T, T);
    if (T == 0)
        return 0;

    t0 = now();
    for (int a = 0; a < T; ++a)
        for (int b = 0; b < T; ++b)
            if (basis[Rr[a]].rho + basis[Cc[b]].rho + 8 > M_SYND) {
                puts("# FR : syndromes too short to form the shifted matrix.");
                R->failed = 1;
                return -1;
            }
    for (uint32_t k = 0; k < nz_cnt; ++k)
        xv[nz_idx[k]] = pts[nz_idx[k]].x;       /* needed only where r != 0 */
    for (int a = 0; a < T; ++a)
        for (int b = 0; b < T; ++b) {
            S0[a][b] = synd(Rr[a], Cc[b], NULL);
            SX[a][b] = synd(Rr[a], Cc[b], xv);
        }
    if (!mat_inverse(S0, S0inv, T)) {
        puts("# FR : S0 is singular (rank deficient).");
        R->failed = 1;
        return -1;
    }
    for (int a = 0; a < T; ++a)                 /* Q = S0^-1 SX */
        for (int b = 0; b < T; ++b) {
            uint16_t acc = 0;
            for (int k = 0; k < T; ++k)
                acc ^= gf_mul(S0inv[a][k], SX[k][b]);
            Q[a][b] = acc;
        }
    charpoly(Q, T, g);

    int nroots = 0;
    for (uint32_t th = 0; th < FIELD_SIZE; ++th)
        if (poly_eval(g, T, (uint16_t)th) == 0)
            roots[nroots++] = (uint16_t)th;
    printf("# FR : %d distinct roots (x-coordinates) in GF(2^12)\n", nroots);

    /* y from the fibre of each root: points where all locators vanish */
    int nfound = 0, overflow = 0;
    for (int m = 0; m < nroots; ++m) {
        uint16_t xr = roots[m];
        for (int j = 0; j < count_of_x[xr]; ++j) {
            uint32_t idx = (uint32_t)(first_of_x[xr] + j);
            int vanish = 1;

            for (int i = 0; i < nl && vanish; ++i) {
                uint16_t acc = 0;
                if (piv_of_row[i] >= 0)
                    continue;
                for (int k = 0; k <= i; ++k)
                    if (coef[i][k] != 0)
                        acc ^= gf_mul(coef[i][k], basis[k].val[idx]);
                if (acc != 0)
                    vanish = 0;
            }
            if (vanish) {
                if (nfound < MAXT)
                    R->pos[nfound++] = idx;
                else
                    overflow = 1;
            }
        }
    }
    R->nfound = nfound;
    R->overflow = overflow;
    R->t_extract = now() - t0;
    resolve_and_store(R);
    return 0;
}

/* ================================================================== */
/*  BMS: Sakata's algorithm on value vectors, with majority voting    */
/* ================================================================== */

typedef struct {
    int b;                  /* leading pole order (generator of E)      */
    int d;                  /* discrepancy at the current position      */
    uint16_t *f;            /* value vector f(P_1..P_n)                 */
} Gen;

static Gen gens[MAXGEN];
static int ngen;
static uint16_t *pivvec[SG_MAX];        /* pivot polynomial by pivot column */
static uint16_t pivd[SG_MAX];           /* its discrepancy                  */
static uint8_t colused[SG_MAX];
static uint8_t is_piv[SG_MAX];

static uint16_t *vec_new(void)
{
    uint16_t *v = malloc(sizeof(uint16_t) * npts);
    if (v == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(EXIT_FAILURE);
    }
    return v;
}

/* s(f * phi_m) = sum_k r_k f(P_k) phi_m(P_k)   (position rho(f)+m <= M) */
static uint16_t disc(const uint16_t *f, int m)
{
    const uint16_t *ph = basis[idx_of_ord[m]].val;
    uint16_t acc = 0;

    for (uint32_t n = 0; n < nz_cnt; ++n) {
        uint32_t k = nz_idx[n];
        acc ^= gf_mul(recv[k], gf_mul(f[k], ph[k]));
    }
    return acc;
}

static void vec_mul(uint16_t *out, const uint16_t *h, const uint16_t *f)
{
    for (uint32_t k = 0; k < npts; ++k)
        out[k] = gf_mul(h[k], f[k]);
}

static void vec_axpy(uint16_t *f, uint16_t c, const uint16_t *p)
{
    for (uint32_t k = 0; k < npts; ++k)
        f[k] ^= gf_mul(c, p[k]);
}

static const int gen_of_H[4] = { 8, 10, 12, 13 };

/* ------------------------------------------------------------------ */
/* Syndromes beyond M (majority voting)                                */
/*                                                                    */
/* The syndrome functional s is known on L(M P).  For the g positions  */
/* u = M+1 .. M+g it is an unknown number xhat[u] = s(phi_u) that is   */
/* found by voting.  To evaluate s(h) for h in L(u P) one needs the    */
/* coefficients a_v (v = M+1..u) of h on the top basis functions:      */
/*       h = h_low + sum_v a_v phi_v ,  h_low in L(M P),               */
/*       s(h) = s(h_low) + sum_v a_v xhat[v].                          */
/* The a_v are read off from the values of h at NB selected points     */
/* with a precomputed dual basis  a_v(h) = sum_p Bw[v][p] h(P_sel[p]). */
/* (one-time cost per code, like building the basis)                   */
/* ------------------------------------------------------------------ */

static uint16_t xhat[M_EXT + 2];
static uint16_t Bw[GENUS][MAX_BASIS];
static uint32_t selp[MAX_BASIS];
static int nsel_dual;
static uint16_t Aug[MAX_BASIS][MAX_BASIS + GENUS];
static int lgrow[MAX_BASIS + GENUS];

static int build_dual(void)
{
    static uint32_t perm[MAX_POINTS];
    static uint16_t bsol[MAX_BASIS];
    const int NB = nbasis, W = NB + GENUS;
    uint32_t seed = 12345u;

    if (NB != M_SYND + 1 || basis[NB - GENUS].rho != M_SYND + 1) {
        fprintf(stderr, "dual basis: unexpected basis layout\n");
        return -1;
    }
    for (int attempt = 0; attempt < 8; ++attempt) {
        int singular = 0;

        for (uint32_t i = 0; i < npts; ++i)
            perm[i] = i;
        for (uint32_t i = 0; i < (uint32_t)NB; ++i) {   /* random subset */
            seed = seed * 1664525u + 1013904223u;
            uint32_t j = i + (seed >> 8) % (npts - i);
            uint32_t t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            selp[i] = perm[i];
        }
        nsel_dual = NB;
        /* rows = basis functions, columns = selected points, RHS = unit
         * vectors of the g top basis functions                         */
        for (int j = 0; j < NB; ++j) {
            for (int p = 0; p < NB; ++p)
                Aug[j][p] = basis[j].val[selp[p]];
            for (int v = 0; v < GENUS; ++v)
                Aug[j][NB + v] = (j == NB - GENUS + v) ? 1 : 0;
        }
        for (int c = 0; c < NB && !singular; ++c) {
            int p = -1;
            for (int r = c; r < NB; ++r)
                if (Aug[r][c] != 0) { p = r; break; }
            if (p < 0) { singular = 1; break; }
            if (p != c)
                for (int k = 0; k < W; ++k) {
                    uint16_t t = Aug[p][k]; Aug[p][k] = Aug[c][k]; Aug[c][k] = t;
                }
            uint16_t inv = gf_inv(Aug[c][c]);
            for (int k = c; k < W; ++k)
                Aug[c][k] = gf_mul(Aug[c][k], inv);
            for (int k = c + 1; k < W; ++k)
                lgrow[k] = Aug[c][k] ? (int)glog[Aug[c][k]] : -1;
            for (int r = c + 1; r < NB; ++r) {
                uint16_t f = Aug[r][c];
                uint16_t *row = Aug[r];
                if (f == 0)
                    continue;
                int lf = glog[f];
                for (int k = c + 1; k < W; ++k)
                    if (lgrow[k] >= 0)
                        row[k] ^= gexp[lf + lgrow[k]];
                row[c] = 0;
            }
        }
        if (singular)
            continue;                       /* try another point subset */
        for (int v = 0; v < GENUS; ++v) {
            for (int i = NB - 1; i >= 0; --i) {
                uint16_t acc = Aug[i][NB + v];
                for (int k = i + 1; k < NB; ++k)
                    if (Aug[i][k] != 0 && bsol[k] != 0)
                        acc ^= gf_mul(Aug[i][k], bsol[k]);
                bsol[i] = acc;
            }
            for (int i = 0; i < NB; ++i)
                Bw[v][i] = bsol[i];
        }
        return 0;
    }
    fprintf(stderr, "dual basis: evaluation matrix singular\n");
    return -1;
}

/* check a_v(h) on a random function of L((M+g) P) */
static int dual_selftest(void)
{
    uint16_t coefv[MAX_BASIS];
    uint16_t hs[MAX_BASIS];

    for (int j = 0; j < nbasis; ++j)
        coefv[j] = (uint16_t)(1 + rand() % FIELD_ORDER);
    for (int p = 0; p < nsel_dual; ++p) {
        uint16_t acc = 0;
        for (int j = 0; j < nbasis; ++j)
            acc ^= gf_mul(coefv[j], basis[j].val[selp[p]]);
        hs[p] = acc;
    }
    for (int v = 0; v < GENUS; ++v) {
        uint16_t acc = 0;
        for (int p = 0; p < nsel_dual; ++p)
            acc ^= gf_mul(Bw[v][p], hs[p]);
        if (acc != coefv[nbasis - GENUS + v])
            return -1;
    }
    return 0;
}

/*
 * For f of pole order b and m = n - b > M - b ... position n = rho(f)+m,
 * n > M: returns the part of s(f phi_m) that does not involve xhat[n],
 * and the coefficient an of phi_n in f phi_m (so that
 *      s(f phi_m) = known + an * xhat[n] ).
 */
static uint16_t ext_known(const uint16_t *f, int m, int n, uint16_t *an_out)
{
    static uint16_t hsel[MAX_BASIS];
    uint16_t a[GENUS + 1];
    const uint16_t *ph = basis[idx_of_ord[m]].val;
    const uint16_t *top[GENUS + 1];
    const int nv = n - M_SYND;
    uint16_t s = 0;

    for (int p = 0; p < nsel_dual; ++p) {
        uint32_t k = selp[p];
        hsel[p] = gf_mul(f[k], ph[k]);
    }
    for (int v = 1; v <= nv; ++v) {
        uint16_t acc = 0;
        for (int p = 0; p < nsel_dual; ++p)
            if (hsel[p] != 0 && Bw[v - 1][p] != 0)
                acc ^= gf_mul(hsel[p], Bw[v - 1][p]);
        a[v] = acc;
        top[v] = basis[idx_of_ord[M_SYND + v]].val;
    }
    for (uint32_t i = 0; i < nz_cnt; ++i) {
        uint32_t k = nz_idx[i];
        uint16_t hv = gf_mul(f[k], ph[k]);
        for (int v = 1; v <= nv; ++v)
            if (a[v] != 0)
                hv ^= gf_mul(a[v], top[v][k]);      /* h_low(P_k) */
        s ^= gf_mul(recv[k], hv);
    }
    for (int v = 1; v < nv; ++v)
        if (a[v] != 0)
            s ^= gf_mul(a[v], xhat[M_SYND + v]);
    *an_out = a[nv];
    return s;
}

/* s(f phi_m) at position n (honest syndrome for n <= M, extended above) */
static uint16_t xdisc(const uint16_t *f, int m, int n)
{
    uint16_t an, known;

    if (n <= M_SYND)
        return disc(f, m);
    known = ext_known(f, m, n, &an);
    return (uint16_t)(known ^ gf_mul(an, xhat[n]));
}

/* simulation only: the true value s(phi_n) (valid because c = 0) */
static uint16_t true_syndrome(int n)
{
    const uint16_t *ph = basis[idx_of_ord[n]].val;
    uint16_t acc = 0;

    for (uint32_t i = 0; i < nz_cnt; ++i)
        acc ^= gf_mul(recv[nz_idx[i]], ph[nz_idx[i]]);
    return acc;
}

/*
 * Majority vote for xhat[n].
 * A pair (i, j), rho_i + rho_j = n, is a candidate when row i is not a
 * known pivot row and column j is not a known pivot column.  Every
 * candidate predicts the value of the unknown syndrome for which its
 * minimal polynomial would have discrepancy 0 (all rows i = g + h of a
 * generator g give the prediction of g).  Pivot candidates predict wrong
 * values; there are fewer of them than non-pivot candidates as long as
 * t <= (M - 2g + 1)/2.
 */
static int vote_position(int n, Result *R, int verbose)
{
    uint16_t pred[MAXGEN], dv[MAXGEN];
    int validg[MAXGEN], dc[MAXGEN], nd = 0, ncand = 0;

    for (int g = 0; g < ngen; ++g) {
        int m = n - gens[g].b;
        validg[g] = (m >= 0 && in_H[m]);
        if (validg[g]) {
            uint16_t an, known = ext_known(gens[g].f, m, n, &an);
            if (an == 0) {
                fprintf(stderr, "vote: zero leading coefficient (n=%d)\n", n);
                return -1;
            }
            pred[g] = gf_mul(known, gf_inv(an));
        }
    }
    for (int i = 0; i <= n; ++i) {
        int j = n - i, anc = -1, s;

        if (!in_H[i] || is_piv[i] || !in_H[j] || colused[j])
            continue;
        for (int g = 0; g < ngen; ++g)
            if (gens[g].b <= i && in_H[i - gens[g].b]) {
                anc = g;
                break;
            }
        if (anc < 0 || !validg[anc])
            continue;
        ++ncand;
        for (s = 0; s < nd; ++s)
            if (dv[s] == pred[anc])
                break;
        if (s == nd) {
            dv[nd] = pred[anc];
            dc[nd] = 0;
            ++nd;
        }
        ++dc[s];
    }
    if (nd == 0) {
        fprintf(stderr, "vote: no candidates at n=%d\n", n);
        return -1;
    }
    int best = 0, second = 0;
    for (int s = 1; s < nd; ++s)
        if (dc[s] > dc[best])
            best = s;
    for (int s = 0; s < nd; ++s)
        if (s != best && dc[s] > second)
            second = dc[s];
    xhat[n] = dv[best];

    int margin = dc[best] - second;
    ++R->vote_steps;
    if (margin < R->vote_min_margin)
        R->vote_min_margin = margin;
    if (margin <= 0)
        ++R->vote_tie;
    int right = true_syndrome(n) == xhat[n];
    if (!right)
        ++R->vote_wrong;
    if (verbose)
        printf("#   vote n=%d: %d candidates, %d distinct predictions, "
               "winner %d votes, runner-up %d%s\n", n, ncand, nd, dc[best],
               second, right ? "  (= true syndrome)" : "  (WRONG)");
    return 0;
}

static void bms_cleanup(void)
{
    for (int g = 0; g < ngen; ++g)
        free(gens[g].f);
    ngen = 0;
    for (int m = 0; m < SG_MAX; ++m) {
        free(pivvec[m]);
        pivvec[m] = NULL;
    }
}

/* positions n = 0 .. nmax; n > M uses voted syndromes */
static int bms_run(Result *R, int nmax, int verbose)
{
    int T = 0;

    memset(colused, 0, sizeof colused);
    memset(is_piv, 0, sizeof is_piv);
    memset(pivvec, 0, sizeof pivvec);
    ngen = 1;
    gens[0].b = 0;
    gens[0].d = 0;
    gens[0].f = vec_new();
    for (uint32_t k = 0; k < npts; ++k)
        gens[0].f[k] = 1;

    for (int n = 0; n <= nmax; ++n) {
        int anyfail = 0;

        if (n > M_SYND && vote_position(n, R, verbose) != 0)
            return -1;

        /* 1. discrepancy of every generator at position n */
        for (int g = 0; g < ngen; ++g) {
            int m = n - gens[g].b;
            gens[g].d = (m >= 0 && in_H[m]) ? xdisc(gens[g].f, m, n) : 0;
            if (gens[g].d != 0)
                anyfail = 1;
        }
        if (!anyfail)
            continue;

        /* 2. rows a = g + h (h in H) that fail at a free column become
         *    pivots: (a, n - a); their polynomial is h f_g              */
        for (int a = 0; a <= n; ++a) {
            int m = n - a, src = -1;

            if (!in_H[a] || is_piv[a] || !in_H[m] || colused[m])
                continue;
            for (int g = 0; g < ngen; ++g)
                if (gens[g].d != 0 && gens[g].b <= a &&
                    in_H[a - gens[g].b]) {
                    src = g;
                    break;
                }
            if (src < 0)
                continue;
            uint16_t *f = vec_new();
            vec_mul(f, basis[idx_of_ord[a - gens[src].b]].val, gens[src].f);
            uint16_t d = xdisc(f, m, n);
            if (d == 0) {
                fprintf(stderr, "BMS: internal error (zero pivot at n=%d)\n", n);
                free(f);
                return -1;
            }
            pivvec[m] = f;
            pivd[m] = d;
            colused[m] = 1;
            is_piv[a] = 1;
            R->rowset[a] = 1;
            R->colset[m] = 1;
            ++T;
        }

        /* 3. generators of the new E = H \ {pivot rows} */
        Gen ng[MAXGEN];
        uint8_t reused[MAXGEN];
        int nn = 0;

        memset(reused, 0, sizeof reused);
        for (int b = 0; b <= nmax; ++b) {
            int minimal = 1, og = -1;

            if (!in_H[b] || is_piv[b])
                continue;
            for (int s = 0; s < 4; ++s)
                if (b - gen_of_H[s] >= 0 && in_H[b - gen_of_H[s]] &&
                    !is_piv[b - gen_of_H[s]]) {
                    minimal = 0;
                    break;
                }
            if (!minimal)
                continue;
            if (nn >= MAXGEN) {
                fprintf(stderr, "BMS: too many generators\n");
                return -1;
            }
            for (int g = 0; g < ngen; ++g)
                if (gens[g].b == b)
                    og = g;
            if (og >= 0) {
                ng[nn] = gens[og];
                reused[og] = 1;
            } else {
                int src = -1, m = n - b;

                for (int g = 0; g < ngen; ++g)
                    if (gens[g].b <= b && in_H[b - gens[g].b]) {
                        src = g;
                        break;
                    }
                if (src < 0) {
                    fprintf(stderr, "BMS: no source for generator %d\n", b);
                    return -1;
                }
                ng[nn].b = b;
                ng[nn].f = vec_new();
                vec_mul(ng[nn].f, basis[idx_of_ord[b - gens[src].b]].val,
                        gens[src].f);
                ng[nn].d = (m >= 0 && in_H[m]) ? xdisc(ng[nn].f, m, n) : 0;
            }
            /* a generator that still fails sits on a used column: correct it
             * with the pivot polynomial of that column                    */
            {
                int m = n - ng[nn].b;
                if (m >= 0 && in_H[m] && ng[nn].d != 0) {
                    if (!colused[m] || pivvec[m] == NULL) {
                        fprintf(stderr, "BMS: inconsistent state (n=%d, b=%d)\n",
                                n, b);
                        return -1;
                    }
                    vec_axpy(ng[nn].f, gf_mul(ng[nn].d, gf_inv(pivd[m])),
                             pivvec[m]);
                    ng[nn].d = 0;
                }
            }
            ++nn;
        }
        for (int g = 0; g < ngen; ++g)
            if (!reused[g])
                free(gens[g].f);
        for (int g = 0; g < nn; ++g)
            gens[g] = ng[g];
        ngen = nn;
    }
    R->T = T;
    return 0;
}

/* use_vote = 0: positions 0..M (basic algorithm);
 * use_vote = 1: positions 0..M+g, the g extra syndromes found by voting   */
static int decode_bms(Result *R, int use_vote, int verbose)
{
    const char *name = use_vote ? "VOTE" : "BMS";
    const int Mtop = use_vote ? M_EXT : M_SYND;
    double t0 = now();

    memset(R, 0, sizeof *R);
    R->vote_min_margin = 1 << 30;
    memset(xhat, 0, sizeof xhat);
    if (bms_run(R, Mtop, verbose) != 0) {
        R->failed = 1;
        bms_cleanup();
        return -1;
    }
    R->t_main = now() - t0;

    /* locators: f with rho <= Mtop - 2g + 1 - t vanish on the error set;
     * the basic algorithm uses the fixed bound tau + g                    */
    int bmax = use_vote ? Mtop - 2 * GENUS + 1 - R->T : L_DEG;
    int nsel = 0, sel[MAXGEN];
    for (int g = 0; g < ngen; ++g)
        if (gens[g].b <= bmax)
            sel[nsel++] = g;
    printf("# %-4s: %d generators of E (rho =", name, ngen);
    for (int g = 0; g < ngen; ++g)
        printf(" %d", gens[g].b);
    printf("), %d with rho <= %d\n", nsel, bmax);
    printf("# %-4s: staircase of %d elements -> estimated t = %d\n", name,
           R->T, R->T);
    if (use_vote)
        printf("# %-4s: %d voted syndromes, smallest margin %d, "
               "%d wrong (vs. simulated truth), %d ties\n", name,
               R->vote_steps, R->vote_min_margin, R->vote_wrong, R->vote_tie);
    if (R->T == 0) {
        bms_cleanup();
        return 0;
    }

    t0 = now();
    int nfound = 0, overflow = 0;
    for (uint32_t k = 0; k < npts; ++k) {
        int vanish = nsel > 0;
        for (int s = 0; s < nsel && vanish; ++s)
            if (gens[sel[s]].f[k] != 0)
                vanish = 0;
        if (vanish) {
            if (nfound < MAXT)
                R->pos[nfound++] = k;
            else
                overflow = 1;
        }
    }
    R->nfound = nfound;
    R->overflow = overflow;
    R->t_extract = now() - t0;
    bms_cleanup();
    resolve_and_store(R);
    return 0;
}

/* ================================================================== */
/*  reporting                                                          */
/* ================================================================== */

typedef struct {
    uint32_t idx;
    uint16_t val;
} Entry;

static int cmp_entry(const void *a, const void *b)
{
    uint32_t x = ((const Entry *)a)->idx, y = ((const Entry *)b)->idx;
    return (x > y) - (x < y);
}

#define LIST_SHOWN 40           /* lines per list unless -a is given */

static void print_list(const char *title, Entry *e, int n, int with_val,
                       int print_all)
{
    qsort(e, (size_t)n, sizeof(Entry), cmp_entry);
    printf("# %s (%d):\n", title, n);
    printf("#   %5s  %7s  %s\n", "no.", "index", "(x,y)  value");
    for (int i = 0; i < n; ++i) {
        if (!print_all && i == LIST_SHOWN) {
            printf("#   ... (%d more, use -a to list all)\n", n - i);
            break;
        }
        printf("#   %5d  %7u  (%u,%u)", i + 1, e[i].idx, pts[e[i].idx].x,
               pts[e[i].idx].y);
        if (with_val)
            printf("  e=%u", e[i].val);
        printf("\n");
    }
}

static uint32_t true_pos[NUM_ERRORS];
static uint16_t true_val[NUM_ERRORS];

static int verify(const char *name, const Result *R)
{
    int same = 0;

    if (R->failed) {
        printf("# %-4s FAILED\n", name);
        return 0;
    }
    for (int m = 0; m < R->nfound; ++m)
        for (int e = 0; e < NUM_ERRORS; ++e)
            if (true_pos[e] == R->pos[m] && true_val[e] == R->val[m])
                ++same;
    int ok = !R->overflow && R->resolved && R->nfound == NUM_ERRORS &&
             same == NUM_ERRORS;
    printf("# %-4s %d of %d errors recovered with the correct value, "
           "%d reported -> %s\n", name, same, NUM_ERRORS, R->nfound,
           ok ? "OK" : "MISMATCH");
    return ok;
}

static void print_times(const char *name, const Result *R,
                        const char *main_label, const char *ext_label)
{
    printf("# %-4s time: %-24s %9.3f s\n", name, main_label, R->t_main);
    printf("#      time: %-24s %9.3f s\n", ext_label, R->t_extract);
    printf("#      time: %-24s %9.3f s\n", "error values", R->t_resolve);
    printf("#      time: %-24s %9.3f s\n", "total",
           R->t_main + R->t_extract + R->t_resolve);
}

static double total_time(const Result *R)
{
    return R->t_main + R->t_extract + R->t_resolve;
}

int main(int argc, char **argv)
{
    int print_points = 0, print_all = 0, verbose = 0;
    int run_fr = 1, run_bms = 1, run_vote = 1, only = 0;
    unsigned seed = 12345u;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-p") == 0)
            print_points = 1;
        else if (strcmp(argv[i], "-a") == 0)
            print_all = 1;
        else if (strcmp(argv[i], "-v") == 0)
            verbose = 1;
        else if (strcmp(argv[i], "-fr") == 0 || strcmp(argv[i], "-bms") == 0 ||
                 strcmp(argv[i], "-vote") == 0) {
            if (!only)
                run_fr = run_bms = run_vote = 0;
            only = 1;
            if (strcmp(argv[i], "-fr") == 0)
                run_fr = 1;
            else if (strcmp(argv[i], "-bms") == 0)
                run_bms = 1;
            else
                run_vote = 1;
        } else
            seed = (unsigned)strtoul(argv[i], NULL, 10);
    }

    if (NUM_ERRORS > TAU_V) {
        fprintf(stderr, "NUM_ERRORS=%d exceeds TAU_V=%d for M=%d\n",
                NUM_ERRORS, TAU_V, M_SYND);
        return EXIT_FAILURE;
    }
    if (gf_init() != 0) {
        fprintf(stderr, "field polynomial is not primitive\n");
        return EXIT_FAILURE;
    }

    puts("# Suzuki curve: y^8 + y = x^2 (x^8 + x)  over GF(2^12)");
    double ts = now();
    if (enumerate_points(print_points) != 0)
        return EXIT_FAILURE;
    printf("# Affine points: %u (+1 at infinity = %u)\n", npts, npts + 1u);
    printf("# genus g=%d, M=%d, designed distance d*=%d\n", GENUS, M_SYND,
           M_SYND - 2 * GENUS + 2);
    printf("# basic algorithm corrects t <= %d, with majority voting "
           "t <= %d\n", TAU, TAU_V);
    if (build_basis(M_EXT) != 0)
        return EXIT_FAILURE;
    init_semigroup();
    printf("# setup (points, basis values up to M+g): %.3f s\n", now() - ts);
    if (run_vote) {
        ts = now();
        if (build_dual() != 0 || dual_selftest() != 0) {
            fprintf(stderr, "dual basis construction failed\n");
            return EXIT_FAILURE;
        }
        printf("# setup (dual basis for the top g coefficients, once per "
               "code): %.3f s\n", now() - ts);
    }

    /* ---- simulate a channel: received word = error vector (c = 0) ---- */
    static uint16_t r[MAX_POINTS];

    srand(seed);
    for (int e = 0; e < NUM_ERRORS; ++e) {
        uint32_t p;
        int dup;
        do {
            p = (uint32_t)rand() % npts;
            dup = 0;
            for (int k = 0; k < e; ++k)
                if (true_pos[k] == p)
                    dup = 1;
        } while (dup);
        true_pos[e] = p;
        do {
            r[p] = (uint16_t)(rand() & (FIELD_SIZE - 1u));
        } while (r[p] == 0);
        true_val[e] = r[p];
    }
    printf("# %d errors injected (seed %u)%s\n", NUM_ERRORS, seed,
           NUM_ERRORS > TAU ? "  -- beyond the basic bound" : "");

    /* ---- decoder side: only r is used from here on ---- */
    recv = r;
    nz_cnt = 0;
    for (uint32_t k = 0; k < npts; ++k)
        if (r[k] != 0)
            nz_idx[nz_cnt++] = k;

    int ok_fr = 1, ok_bms = 1, ok_vote = 1;

    if (run_fr) {
        decode_fr(&res_fr);
        print_times("FR", &res_fr, "Feng-Rao reduction", "charpoly + roots");
        ok_fr = verify("FR", &res_fr);
    }
    if (run_bms) {
        decode_bms(&res_bms, 0, verbose);
        print_times("BMS", &res_bms, "Sakata (BMS) loop", "zero scan");
        ok_bms = verify("BMS", &res_bms);
    }
    if (run_vote) {
        decode_bms(&res_vote, 1, verbose);
        print_times("VOTE", &res_vote, "BMS + majority voting", "zero scan");
        ok_vote = verify("VOTE", &res_vote);
    }

    if (run_fr && run_bms && !res_fr.failed && !res_bms.failed &&
        NUM_ERRORS <= TAU) {
        printf("# pivot rows    FR == BMS : %s\n",
               memcmp(res_fr.rowset, res_bms.rowset, sizeof res_fr.rowset)
               == 0 ? "yes" : "NO");
        printf("# pivot columns FR == BMS : %s\n",
               memcmp(res_fr.colset, res_bms.colset, sizeof res_fr.colset)
               == 0 ? "yes" : "NO");
    }
    if (run_bms && run_vote && !res_bms.failed && !res_vote.failed &&
        NUM_ERRORS <= TAU)
        printf("# pivot rows    BMS == VOTE: %s\n",
               memcmp(res_bms.rowset, res_vote.rowset, sizeof res_bms.rowset)
               == 0 ? "yes" : "NO");
    if (run_fr && run_vote && !res_fr.failed && !res_vote.failed)
        printf("# whole decoder, FR / VOTE time ratio : %.1f x\n",
               total_time(&res_fr) / total_time(&res_vote));
    if (run_bms && run_vote && !res_bms.failed && !res_vote.failed)
        printf("# whole decoder, VOTE / BMS time ratio: %.1f x\n",
               total_time(&res_vote) / total_time(&res_bms));

    {
        static Entry orig[MAX_POINTS], dec[MAXT + 1];
        const Result *R = run_vote ? &res_vote : run_bms ? &res_bms : &res_fr;

        for (int e = 0; e < NUM_ERRORS; ++e) {
            orig[e].idx = true_pos[e];
            orig[e].val = true_val[e];
        }
        for (int m = 0; m < R->nfound; ++m) {
            dec[m].idx = R->pos[m];
            dec[m].val = R->val[m];
        }
        print_list("original errors", orig, NUM_ERRORS, 1, print_all);
        print_list("corrected errors", dec, R->nfound, R->resolved, print_all);
    }

    for (int i = 0; i < nbasis; ++i)
        free(basis[i].val);

    /* the basic decoders are only expected to work up to tau */
    int expect_basic = NUM_ERRORS <= TAU;
    int ok = (!run_fr || ok_fr || !expect_basic) &&
             (!run_bms || ok_bms || !expect_basic) &&
             (!run_vote || ok_vote);
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}