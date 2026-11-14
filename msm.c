/*
 * One-point AG-code decoder framework (single-file version).
 * Initial curve adapter: Suzuki curve y^8 + y = x^2 (x^8 + x), q=8, q0=2.
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
 * (1) Generic locator-point intersection
 *     -----------------------------------
 *     Evaluate the common Feng-Rao locators at every affine rational point.
 *     This avoids assuming that one coordinate (such as x) separates points.
 *     It is slower than the univariate characteristic-polynomial shortcut,
 *     but works for a curve adapter that supplies point enumeration and
 *     basis evaluation.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o ag_decoder ag_decoder.c
 * Run:   ./ag_decoder [--curve suzuki|plane] [--m degree] [--poly hex] [-p] [-a] [seed]
 * Plane mode: --equation "c:xpow:ypow;..." --wx N --wy N --dy N --genus G [--tau T]
 * Example: --curve plane --m 3 --poly 0xb --equation "1:0:2;1:0:1;1:3:0;1:1:0" --wx 2 --wy 3 --dy 2 --genus 1
 *        default field: GF(2^12), primitive polynomial 0x1053
 *        example: ./ag_decoder --m 6 --poly 0x43
 *        -p : list all affine points,  -a : print the complete error lists
 *        -DM_SYND=50 -DNUM_ERRORS=4 can be given at compile time.
 *
 * Curve adapter contract (CurveOps):
 *   enumerate       fills the affine evaluation set pts[0..npts).
 *   make_basis_term creates the curve-specific function for a pole order;
 *                   returns 1 for a nongap, 0 for a gap, -1 on failure.
 *   eval_basis      evaluates that function at a Point (including opaque
 *                   Point.curve_data when the model needs more coordinates).
 *   print_basis     prints a curve-specific basis function.
 *   decoding_radius and min_positive_nongap supply curve-dependent bounds.
 * The Feng-Rao reduction, syndrome evaluation, locator intersection and
 * error-value solver use only pole orders and evaluation vectors.
 * This file currently registers Suzuki; other curves are added by defining
 * another CurveOps adapter, without changing the common decoder.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_FIELD_M 16u
#define MAX_FIELD_SIZE (1u << MAX_FIELD_M)
static unsigned FIELD_M = 12u;
static uint32_t FIELD_SIZE = (1u << 12);
static uint32_t FIELD_ORDER = (1u << 12) - 1u;
static uint32_t FIELD_POLY = 0x1053u;

#define SUZUKI_Q 8u
#define SUZUKI_Q0 2u
#define MAX_FIBER 8u
#define MAX_POINTS (MAX_FIELD_SIZE * MAX_FIBER)

/* ---- code / experiment parameters ---- */
#ifndef M_SYND
#define M_SYND 2048               /* syndromes known for h in L(M_SYND P_inf) */
#endif
#ifndef NUM_ERRORS
#define NUM_ERRORS 512            /* injected errors, must be <= TAU          */
#endif

#define MAX_BASIS (M_SYND + 1)
#define MAXT (M_SYND / 2 + 2)  /* capacity; actual tau is curve-dependent */
static int TAU, L_DEG, ROW_MAX;
#define PRINT_LOCATORS 256        /* how many locators are printed            */
#define PRINT_TERMS 256          /* terms printed per locator                */

typedef struct {
    uint16_t x, y;          /* optional coordinates for simple plane curves */
    void *curve_data;       /* optional opaque point data for other models */
} Point;

typedef struct {
    int rho;                    /* pole order               */
    void *curve_data;           /* opaque curve-specific basis descriptor */
    uint16_t *val;              /* values at the n points   */
} Basis;

typedef struct CurveOps CurveOps;
struct CurveOps {
    const char *name;
    int genus;
    int min_positive_nongap;
    int (*decoding_radius)(int syndrome_order);
    int (*enumerate)(int print_points);
    int (*make_basis_term)(int rho, void **term_data); /* 1=nongap, 0=gap */
    uint16_t (*eval_basis)(const void *term_data, const Point *point);
    void (*print_basis)(const void *term_data);
    void (*print_point)(const Point *point);
};
static const CurveOps *active_curve;

static Point pts[MAX_POINTS];
static uint32_t npts;

/* ------------------------------------------------------------------ */
/* GF(2^m) arithmetic (runtime m, log / antilog tables)               */
/* ------------------------------------------------------------------ */

static uint16_t gexp[2 * ((1u << MAX_FIELD_M) - 1u) + 2u];
static uint16_t glog[MAX_FIELD_SIZE];

static int gf_init(void)
{
    uint32_t x = 1;
    FIELD_SIZE = 1u << FIELD_M;
    FIELD_ORDER = FIELD_SIZE - 1u;
    if (FIELD_M < 2u || FIELD_M > MAX_FIELD_M || FIELD_POLY >= (1u << (FIELD_M + 1u)) ||
        (FIELD_POLY & FIELD_SIZE) == 0u)
        return -1;
    memset(glog, 0, sizeof(glog));
    memset(gexp, 0, sizeof(gexp));

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
    static uint16_t fiber[MAX_FIELD_SIZE][MAX_FIBER];
    static uint8_t fiber_count[MAX_FIELD_SIZE];
    memset(fiber_count, 0, sizeof(fiber_count));

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

    if (npts == 0) {
        fprintf(stderr, "The selected field contains no affine points.\n");
        return -1;
    }
    if (FIELD_M == 12u && npts != 5888u) {
        fprintf(stderr, "Suzuki baseline point-count check failed (expected 5888, got %u).\n", npts);
        return -1;
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Curve adapter: Suzuki basis. The Feng-Rao engine sees only rho/value. */
/* ------------------------------------------------------------------ */

typedef struct { int a, b, c, d; } SuzukiBasisTerm;
static Basis basis[MAX_BASIS];
static int nbasis;

static uint16_t suzuki_eval_basis(const void *data, const Point *point)
{
    const SuzukiBasisTerm *f = (const SuzukiBasisTerm *)data;
    uint16_t x = point->x, y = point->y;
    uint16_t y4 = gf_pow(y, 4);
    uint16_t z = (uint16_t)(gf_pow(x, 5) ^ y4);
    uint16_t w = (uint16_t)(gf_mul(x, y4) ^ gf_pow(z, 4));
    uint16_t v = gf_pow(x, (unsigned)f->a);
    v = gf_mul(v, gf_pow(y, (unsigned)f->b));
    v = gf_mul(v, gf_pow(z, (unsigned)f->c));
    v = gf_mul(v, gf_pow(w, (unsigned)f->d));
    return v;
}

static int suzuki_make_basis_term(int s, void **term_data)
{
    int found = 0, fa = 0, fb = 0, fc = 0, fd = 0;
    for (int d = 0; 13 * d <= s && !found; ++d)
        for (int c = 0; 13 * d + 12 * c <= s && !found; ++c)
            for (int b = 0; 13 * d + 12 * c + 10 * b <= s && !found; ++b) {
                int r = s - 13 * d - 12 * c - 10 * b;
                if (r % 8 == 0) {
                    found = 1; fa = r / 8; fb = b; fc = c; fd = d;
                }
            }
    if (!found) return 0;
    SuzukiBasisTerm *t = (SuzukiBasisTerm *)malloc(sizeof(*t));
    if (!t) return -1;
    t->a = fa; t->b = fb; t->c = fc; t->d = fd;
    *term_data = t;
    return 1;
}

static void suzuki_print_basis(const void *data)
{
    const SuzukiBasisTerm *f = (const SuzukiBasisTerm *)data;
    int printed = 0;
    if (f->a) { printf("x^%d", f->a); printed = 1; }
    if (f->b) { printf("%sy^%d", printed ? "*" : "", f->b); printed = 1; }
    if (f->c) { printf("%sz^%d", printed ? "*" : "", f->c); printed = 1; }
    if (f->d) { printf("%sw^%d", printed ? "*" : "", f->d); printed = 1; }
    if (!printed) printf("1");
}

static int build_basis(int maxrho)
{
    nbasis = 0;
    for (int s = 0; s <= maxrho; ++s) {
        void *term = NULL;
        int has_term = active_curve->make_basis_term(s, &term);
        if (has_term < 0) return -1;
        if (!has_term) continue;
        if (nbasis >= MAX_BASIS) { free(term); return -1; }
        basis[nbasis].rho = s;
        basis[nbasis].curve_data = term;
        basis[nbasis].val = (uint16_t *)malloc(sizeof(uint16_t) * npts);
        if (!basis[nbasis].val) return -1;
        for (uint32_t k = 0; k < npts; ++k)
            basis[nbasis].val[k] = active_curve->eval_basis(term, &pts[k]);
        ++nbasis;
    }
    return 0;
}

static int suzuki_decoding_radius(int syndrome_order)
{
    return (syndrome_order - 3 * 14 + 1) / 2;
}

static void suzuki_print_point(const Point *p)
{
    printf("(%u,%u)", p->x, p->y);
}

static const CurveOps SUZUKI_CURVE = {
    "Suzuki", 14, 8, suzuki_decoding_radius, enumerate_points,
    suzuki_make_basis_term, suzuki_eval_basis, suzuki_print_basis,
    suzuki_print_point
};

/* ------------------------------------------------------------------ */
/* User-defined affine plane curve adapter                            */
/* Equation format: --equation "c:xpow:ypow;c:xpow:ypow;..."           */
/* Example y^2+y=x^3+x over GF(2): 1:0:2;1:0:1;1:3:0;1:1:0 */
/* Monomial basis x^a y^b, 0<=b<deg_y(F), with supplied pole weights. */
/* This adapter assumes a one-point model with the supplied weights.  */
/* It does NOT automatically prove smoothness or compute the genus.   */
/* ------------------------------------------------------------------ */
#define PLANE_MAX_TERMS 64

typedef struct { uint16_t c; unsigned ax, ay; } PlaneTerm;
typedef struct { unsigned a, b; } PlaneBasisTerm;
static PlaneTerm plane_terms[PLANE_MAX_TERMS];
static int plane_nterms = 0;
static unsigned plane_wx = 3, plane_wy = 2, plane_dy = 2;
static int plane_genus = 1;
static int plane_tau_override = -1;

static uint16_t plane_eval_poly(uint16_t x, uint16_t y)
{
    uint16_t v = 0;
    for (int i=0; i<plane_nterms; ++i) {
        const PlaneTerm *t=&plane_terms[i];
        uint16_t z=gf_mul(t->c, gf_pow(x,t->ax));
        z=gf_mul(z,gf_pow(y,t->ay));
        v ^= z;
    }
    return v;
}

static int plane_parse_equation(const char *src)
{
    size_t len=strlen(src)+1;
    char *copy=malloc(len), *tok;
    if (!copy) return -1;
    memcpy(copy,src,len);
    plane_nterms=0;
    for (tok=strtok(copy,";"); tok; tok=strtok(NULL,";")) {
        unsigned ax,ay; int c; char extra;
        if (plane_nterms>=PLANE_MAX_TERMS ||
            sscanf(tok,"%i:%u:%u%c",&c,&ax,&ay,&extra)!=3 || c<0) {
            free(copy); return -1;
        }
        if ((unsigned)c>=FIELD_SIZE) { free(copy); return -1; }
        plane_terms[plane_nterms++]=(PlaneTerm){(uint16_t)c,ax,ay};
    }
    free(copy);
    return plane_nterms ? 0 : -1;
}

static int plane_enumerate(int print_points)
{
    if (FIELD_M>10) {
        fprintf(stderr,"plane-polynomial enumeration is limited to m<=10 (quadratic point scan).\n");
        return -1;
    }
    npts=0;
    if (print_points) puts("# Affine points (x,y):");
    for (uint32_t x=0; x<FIELD_SIZE; ++x)
        for (uint32_t y=0; y<FIELD_SIZE; ++y)
            if (plane_eval_poly((uint16_t)x,(uint16_t)y)==0) {
                if (npts>=MAX_POINTS) { fprintf(stderr,"point capacity exceeded\n"); return -1; }
                pts[npts].x=(uint16_t)x; pts[npts].y=(uint16_t)y;
                if (print_points) printf("%u,%u\n",x,y);
                ++npts;
            }
    if (!npts) { fprintf(stderr,"the equation has no affine rational points\n"); return -1; }
    return 0;
}

static int plane_make_basis_term(int rho, void **term_data)
{
    for (unsigned b=0; b<plane_dy; ++b) {
        if (rho < (int)(b*plane_wy)) continue;
        unsigned rem=(unsigned)rho-b*plane_wy;
        if (rem%plane_wx==0) {
            PlaneBasisTerm *t=malloc(sizeof(*t));
            if (!t) return -1;
            t->a=rem/plane_wx; t->b=b; *term_data=t; return 1;
        }
    }
    return 0;
}
static uint16_t plane_eval_basis(const void *data,const Point *p)
{
    const PlaneBasisTerm *t=data;
    return gf_mul(gf_pow(p->x,t->a),gf_pow(p->y,t->b));
}
static void plane_print_basis(const void *data)
{
    const PlaneBasisTerm *t=data;
    if (!t->a && !t->b) { printf("1"); return; }
    if (t->a) printf("x^%u",t->a);
    if (t->a && t->b) printf("*");
    if (t->b) printf("y^%u",t->b);
}
static int plane_decoding_radius(int syndrome_order)
{
    if (plane_tau_override>=0) return plane_tau_override;
    return (syndrome_order-3*plane_genus+1)/2;
}
static void plane_print_point(const Point *p) { printf("(%u,%u)",p->x,p->y); }
static const CurveOps PLANE_CURVE={
    "plane-polynomial",0,1,plane_decoding_radius,plane_enumerate,
    plane_make_basis_term,plane_eval_basis,plane_print_basis,plane_print_point
};

static int count_basis_upto(int rho)
{
    int n = 0;
    for (int i = 0; i < nbasis; ++i)
        if (basis[i].rho <= rho)
            ++n;
    return n;
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
        active_curve->print_basis(basis[k].curve_data);
        first = 0;
        ++terms;
    }
    printf("\n");
}

int main(int argc, char **argv)
{
    int print_points = 0, print_all = 0;
    unsigned seed = 12345u;
    const char *curve_name = "suzuki";
    const char *equation = NULL;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--curve") == 0 && i + 1 < argc)
            curve_name = argv[++i];
        else
        if (strcmp(argv[i], "--m") == 0 && i + 1 < argc)
            FIELD_M = (unsigned)strtoul(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--poly") == 0 && i + 1 < argc)
            FIELD_POLY = (uint32_t)strtoul(argv[++i], NULL, 0);
        else if (strcmp(argv[i], "--equation") == 0 && i + 1 < argc)
            equation = argv[++i];
        else if (strcmp(argv[i], "--wx") == 0 && i + 1 < argc)
            plane_wx = (unsigned)strtoul(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--wy") == 0 && i + 1 < argc)
            plane_wy = (unsigned)strtoul(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--dy") == 0 && i + 1 < argc)
            plane_dy = (unsigned)strtoul(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--genus") == 0 && i + 1 < argc)
            plane_genus = atoi(argv[++i]);
        else if (strcmp(argv[i], "--tau") == 0 && i + 1 < argc)
            plane_tau_override = atoi(argv[++i]);
        else if (strcmp(argv[i], "-p") == 0)
            print_points = 1;
        else if (strcmp(argv[i], "-a") == 0)
            print_all = 1;
        else
            seed = (unsigned)strtoul(argv[i], NULL, 10);
    }

    if (strcmp(curve_name, "suzuki") == 0) {
        active_curve = &SUZUKI_CURVE;
    } else if (strcmp(curve_name, "plane") == 0 || strcmp(curve_name, "plane-polynomial") == 0) {
        active_curve = &PLANE_CURVE;
    } else {
        fprintf(stderr, "Unknown curve '%s'. Registered: suzuki, plane\n", curve_name);
        return EXIT_FAILURE;
    }
    TAU = active_curve->decoding_radius(M_SYND);
    L_DEG = TAU + active_curve->genus;
    ROW_MAX = M_SYND - (active_curve == &PLANE_CURVE ?
                        (int)(plane_wx < plane_wy ? plane_wx : plane_wy) :
                        active_curve->min_positive_nongap);
    if (TAU < 1 || NUM_ERRORS > TAU) {
        fprintf(stderr, "M_SYND=%d gives tau=%d for genus=%d; NUM_ERRORS=%d\n",
                M_SYND, TAU, active_curve->genus, NUM_ERRORS);
        return EXIT_FAILURE;
    }
    if (gf_init() != 0) {
        fprintf(stderr, "invalid field parameters or non-primitive polynomial (m=%u, poly=0x%x)\n", FIELD_M, FIELD_POLY);
        return EXIT_FAILURE;
    }

    if (active_curve == &PLANE_CURVE) {
        if (!equation || !plane_wx || !plane_wy || !plane_dy || plane_genus<0 ||
            plane_parse_equation(equation)!=0) {
            fprintf(stderr,"plane mode requires --equation and valid --wx/--wy/--dy/--genus parameters\n");
            return EXIT_FAILURE;
        }
        /* CurveOps is immutable; the plane adapter's genus is supplied at runtime. */
        if (plane_tau_override < -1) return EXIT_FAILURE;
    }
    printf("# %s curve over GF(2^%u), poly=0x%x\n", active_curve->name, FIELD_M, FIELD_POLY);
    if (active_curve->enumerate(print_points) != 0)
        return EXIT_FAILURE;
    printf("# Affine points: %u (+1 point at infinity = %u)\n", npts, npts + 1u);
    printf("# genus g=%d, M=%d, tau=%d, locators in L(%d P_inf)\n",
           active_curve == &PLANE_CURVE ? plane_genus : active_curve->genus,
           M_SYND, TAU, L_DEG);

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
            r[p] = (uint16_t)((unsigned)rand() % FIELD_SIZE);
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
    static int R[MAXT];
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

    /* Generic point recovery: common zero set of all locator functions.
       No assumption is made that x (or another single coordinate) separates
       the support. */
    static uint32_t found[MAXT + 1];
    int nfound = 0, overflow = 0;
    for (uint32_t idx = 0; idx < npts; ++idx) {
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
    printf("# common zeros of the locators on the affine point set: %d%s\n",
           nfound, overflow ? "+ (overflow)" : "");

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

    for (int i = 0; i < nbasis; ++i) {
        free(basis[i].val);
        free(basis[i].curve_data);
    }
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}