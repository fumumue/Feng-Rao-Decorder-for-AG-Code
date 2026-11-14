/*
 * Suzuki curve over GF(2^12), q = 8, q0 = 2:  y^8 + y = x^2 (x^8 + x)
 * Error locators for the one-point code C = C_L(D, M P_inf)^perp  (g = 14).
 *
 * (2) Semigroup version of the Feng-Rao basic algorithm
 *     --------------------------------------------------
 *     The syndrome matrix is indexed by the Weierstrass semigroup
 *     H = <8,10,12,13> :   S[i][j] = s(phi_i phi_j),  rho_i + rho_j <= M.
 *     Row i is known only on the columns rho_j <= M - rho_i.  Rows are
 *     reduced in order of increasing pole order against the earlier pivot
 *     rows (one pivot per column).  A row that becomes 0 on all its known
 *     columns gives a locator  f = phi_i + (lower terms);  a row with a
 *     non-zero entry becomes a new pivot row.  No structure constants of
 *     the function field are needed because s(f phi_j) = sum_k f_k S[k][j].
 *     Cost O(n^2 t).  (Feng-Rao basic algorithm, not Sakata's update.)
 *
 * (1) Univariate polynomial instead of scanning the points
 *     ----------------------------------------------------
 *     The t pivot rows / columns R, C are the standard monomials of A/I
 *     (I = locator ideal, dim A/I = t).  With
 *         S0[a][b] = s(phi_Ra phi_Cb),   SX[a][b] = s(x phi_Ra phi_Cb)
 *     one has S0^-1 SX = Phi_C^-1 diag(x_k) Phi_C, so the characteristic
 *     polynomial  g(theta) = det(theta I + S0^-1 SX)  (degree t) has the
 *     x-coordinates of the error points as roots.  g is computed by a
 *     Hessenberg reduction (O(t^3)); its roots are found by evaluating g
 *     on GF(2^12) (Horner).  For each root x the at most 8 points of the
 *     fibre are tested against the locators (rho <= L), which gives y.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki_feng_rao suzuki_feng_rao.c
 * Run:   ./suzuki_feng_rao [-p] [-a] [seed]
 *        -p : list all affine points,  -a : print the complete error lists
 *        -DM_SYND=1028 -DNUM_ERRORS=493 etc. can be given at compile time.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

#define TAU ((M_SYND - 3 * GENUS + 1) / 2)   /* guaranteed by this method   */
#define L_DEG (TAU + GENUS)                  /* locators are in L(L_DEG P)  */
#define ROW_MAX (M_SYND - 8)                 /* rows processed (rho <= ..)  */

#if TAU < 1
#error "M_SYND too small: need M_SYND >= 3*GENUS + 1 = 43"
#endif

#define MAX_BASIS (M_SYND + 1)  /* number of semigroup elements <= M_SYND   */
#define MAXT (TAU + 2)          /* maximal number of errors (staircase)     */
#define PRINT_LOCATORS 3        /* how many locators are printed            */
#define PRINT_TERMS 12          /* terms printed per locator                */

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
/* (2) Feng-Rao row reduction over the semigroup                      */
/* ------------------------------------------------------------------ */

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

/* ------------------------------------------------------------------ */
/* dense linear algebra over GF(2^12), n <= MAXT                      */
/* ------------------------------------------------------------------ */

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
    int n = *nfound, m = nbasis;

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

/* ------------------------------------------------------------------ */

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

int main(int argc, char **argv)
{
    int print_points = 0, print_all = 0;
    unsigned seed = 12345u;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-p") == 0)
            print_points = 1;
        else if (strcmp(argv[i], "-a") == 0)
            print_all = 1;
        else
            seed = (unsigned)strtoul(argv[i], NULL, 10);
    }

    if (NUM_ERRORS > TAU) {
        fprintf(stderr, "NUM_ERRORS=%d exceeds TAU=%d for M=%d\n",
                NUM_ERRORS, TAU, M_SYND);
        return EXIT_FAILURE;
    }
    if (gf_init() != 0) {
        fprintf(stderr, "field polynomial is not primitive\n");
        return EXIT_FAILURE;
    }

    puts("# Suzuki curve: y^8 + y = x^2 (x^8 + x)  over GF(2^12)");
    if (enumerate_points(print_points) != 0)
        return EXIT_FAILURE;
    printf("# Affine points: %u (+1 at infinity = %u)\n", npts, npts + 1u);
    printf("# genus g=%d, M=%d, tau=%d, locators in L(%d P_inf)\n",
           GENUS, M_SYND, TAU, L_DEG);

    if (build_basis(M_SYND) != 0)
        return EXIT_FAILURE;

    /* ---- simulate a channel: received word = error vector (c = 0) ---- */
    static uint16_t r[MAX_POINTS];
    static uint32_t true_pos[NUM_ERRORS];

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
    }
    printf("# %d errors injected\n", NUM_ERRORS);

    /* ---- decoder side: only r is used from here on ---- */
    recv = r;
    nz_cnt = 0;
    for (uint32_t k = 0; k < npts; ++k)
        if (r[k] != 0)
            nz_idx[nz_cnt++] = k;

    /* (2) Feng-Rao row reduction */
    int nrows = feng_rao_reduce();
    int nl = count_basis_upto(L_DEG);
    static int R[MAXT], C[MAXT];
    int T = 0;

    int nloc = 0;
    for (int i = 0; i < nl; ++i)
        if (piv_of_row[i] < 0)
            ++nloc;
    printf("# %d error locators with rho <= %d (first %d shown):\n", nloc,
           L_DEG, PRINT_LOCATORS);
    {
        int shown = 0;
        for (int i = 0; i < nl && shown < PRINT_LOCATORS; ++i)
            if (piv_of_row[i] < 0) {
                print_locator(i);
                ++shown;
            }
    }
    for (int i = 0; i < nrows; ++i)
        if (piv_of_row[i] >= 0) {
            if (T >= MAXT) {
                fprintf(stderr, "Too many pivots\n");
                return EXIT_FAILURE;
            }
            R[T] = i;
            C[T] = piv_of_row[i];
            ++T;
        }
    printf("# staircase (standard monomials of A/I): %d elements, "
           "rho = ", T);
    for (int a = 0; a < T && a < 12; ++a)
        printf("%d ", basis[R[a]].rho);
    printf("%s -> estimated number of errors t = %d\n", T > 12 ? "..." : "", T);

    if (T == 0) {
        puts("# no errors.");
        return EXIT_SUCCESS;
    }

    /* (1) univariate polynomial g(theta) and its roots */
    for (int a = 0; a < T; ++a)
        for (int b = 0; b < T; ++b)
            if (basis[R[a]].rho + basis[C[b]].rho + 8 > M_SYND) {
                puts("# syndromes too short to form the shifted matrix.");
                return EXIT_FAILURE;
            }

    static uint16_t xv[MAX_POINTS];
    for (uint32_t k = 0; k < nz_cnt; ++k)
        xv[nz_idx[k]] = pts[nz_idx[k]].x;       /* needed only where r != 0 */

    for (int a = 0; a < T; ++a)
        for (int b = 0; b < T; ++b) {
            S0[a][b] = synd(R[a], C[b], NULL);
            SX[a][b] = synd(R[a], C[b], xv);
        }
    if (!mat_inverse(S0, S0inv, T)) {
        puts("# S0 is singular (rank deficient): cannot form the polynomial.");
        return EXIT_FAILURE;
    }
    for (int a = 0; a < T; ++a)                 /* Q = S0^-1 SX */
        for (int b = 0; b < T; ++b) {
            uint16_t acc = 0;
            for (int k = 0; k < T; ++k)
                acc ^= gf_mul(S0inv[a][k], SX[k][b]);
            Q[a][b] = acc;
        }

    static uint16_t g[MAXT + 1];
    charpoly(Q, T, g);
    printf("# g(theta) (degree %d), top terms: ", T);
    for (int i = T, shown = 0; i >= 0 && shown < 4; --i)
        if (g[i] != 0) {
            printf("%s%u*theta^%d", shown ? " + " : "", g[i], i);
            ++shown;
        }
    printf(" ...\n");

    static uint16_t roots[FIELD_SIZE];
    int nroots = 0;
    for (uint32_t th = 0; th < FIELD_SIZE; ++th)
        if (poly_eval(g, T, (uint16_t)th) == 0)
            roots[nroots++] = (uint16_t)th;
    printf("# %d distinct roots (x-coordinates) in GF(2^12)\n", nroots);

    /* y from the fibre of each root: points where all locators vanish */
    static uint32_t found[MAXT + 1];
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
                    found[nfound++] = idx;
                else
                    overflow = 1;
            }
        }
    }

    int resolved = 0;
    if (!overflow && nfound > 0) {
        if (nfound > T)
            printf("# %d common zeros > t = %d: resolving by error values\n",
                   nfound, T);
        resolved = resolve_by_values(found, &nfound);
        if (!resolved)
            puts("# could not compute the error values.");
    }
    printf("# error points found: %d%s\n", nfound, overflow ? "+" : "");

    /* ---- lists: injected errors and corrected (decoded) errors ---- */
    {
        static Entry orig[MAX_POINTS], dec[MAXT + 1];

        for (int e = 0; e < NUM_ERRORS; ++e) {
            orig[e].idx = true_pos[e];
            orig[e].val = r[true_pos[e]];
        }
        for (int m = 0; m < nfound; ++m) {
            dec[m].idx = found[m];
            dec[m].val = resolved ? err_val[m] : 0;
        }
        print_list("original errors", orig, NUM_ERRORS, 1, print_all);
        print_list("corrected errors", dec, nfound, resolved, print_all);
        if (resolved) {
            int same = 0;
            for (int m = 0; m < nfound; ++m)
                for (int e = 0; e < NUM_ERRORS; ++e)
                    if (orig[e].idx == dec[m].idx && orig[e].val == dec[m].val)
                        ++same;
            printf("# %d of %d errors recovered with the correct value\n",
                   same, NUM_ERRORS);
        }
    }

    /* ---- verification against the simulated truth ---- */
    int ok = !overflow && nfound == NUM_ERRORS;
    for (int e = 0; e < NUM_ERRORS && ok; ++e) {
        int hit = 0;
        for (int m = 0; m < nfound; ++m)
            if (found[m] == true_pos[e])
                hit = 1;
        if (!hit)
            ok = 0;
    }
    if (ok && resolved)
        for (int m = 0; m < nfound; ++m)
            if (err_val[m] != r[found[m]])
                ok = 0;
    puts(ok ? "# OK: error positions coincide with the injected errors."
            : "# MISMATCH: result differs from the injected errors.");

    for (int i = 0; i < nbasis; ++i)
        free(basis[i].val);
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}