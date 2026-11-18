#define _POSIX_C_SOURCE 199309L
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

#ifndef RMAX
#define RMAX 608                /* highest pole order in the basis          */
#endif
#define MAXD 256                 /* points in a divisor                      */
#define MAXRES 12               /* reserved fibres                          */
#define CONMAX 768              /* vanishing conditions                     */

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
/* GF(2^12)                                                            */
/* ------------------------------------------------------------------ */

static uint16_t gexp[2 * FIELD_ORDER + 2];
static uint16_t glog[FIELD_SIZE];

static int gf_init(void)
{
    uint32_t x = 1;

    for (uint32_t i = 0; i < FIELD_ORDER; ++i) {
        if (i > 0 && x == 1)
            return -1;
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
    return gexp[FIELD_ORDER - glog[a]];
}

/* ------------------------------------------------------------------ */
/* Points and basis of L(RMAX P_inf)                                   */
/* ------------------------------------------------------------------ */

static int enumerate_points(void)
{
    static uint16_t fiber[FIELD_SIZE][MAX_FIBER];
    static uint8_t fiber_count[FIELD_SIZE];

    npts = 0;
    for (uint32_t y = 0; y < FIELD_SIZE; ++y) {
        uint16_t value = (uint16_t)(gf_pow((uint16_t)y, SUZUKI_Q) ^ y);
        uint8_t n = fiber_count[value];

        if (n >= MAX_FIBER)
            return -1;
        fiber[value][n] = (uint16_t)y;
        fiber_count[value] = (uint8_t)(n + 1);
    }
    for (uint32_t x = 0; x < FIELD_SIZE; ++x) {
        uint16_t xq = gf_pow((uint16_t)x, SUZUKI_Q);
        uint16_t xq0 = gf_pow((uint16_t)x, SUZUKI_Q0);
        uint16_t rhs = gf_mul(xq0, (uint16_t)(xq ^ x));

        first_of_x[x] = (int)npts;
        count_of_x[x] = fiber_count[rhs];
        for (uint8_t j = 0; j < fiber_count[rhs]; ++j) {
            if (npts >= MAX_POINTS)
                return -1;
            pts[npts].x = (uint16_t)x;
            pts[npts].y = fiber[rhs][j];
            ++npts;
        }
    }
    return npts == MAX_POINTS ? 0 : -1;
}

static Basis basis[RMAX + 1];
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

/* number of basis functions with pole order <= R */
static int nb_upto(int R)
{
    int n = 0;
    for (int i = 0; i < nbasis; ++i)
        if (basis[i].rho <= R)
            ++n;
    return n;
}

/* ------------------------------------------------------------------ */
/* Reserved fibres and the evaluation set D                            */
/*                                                                    */
/* Divisors are  G = a P_inf + sum(pos) - sum(neg)  where pos / neg are */
/* affine rational points taken from the RESERVED fibres x = x_s.  D is */
/* all affine points outside the reserved fibres, so every divisor of   */
/* this kind has supp(G) disjoint from D and all codes have length n.  */
/* ------------------------------------------------------------------ */

typedef struct {
    int a;                      /* coefficient of P_inf                  */
    int npos, pos[MAXD];        /* points with coefficient +1 (pts[] idx) */
    int nneg, neg[MAXD];        /* points with coefficient -1            */
} Div;

static int nres;
static int resx[MAXRES];        /* reserved x-values                     */
static int resq[MAXRES];        /* reserved points Q_i (first of fibre)  */
static uint8_t is_res_x[FIELD_SIZE];
static uint32_t dlist[MAX_POINTS];
static uint32_t nD;

static int setup_reserved(int s)
{
    nres = 0;
    memset(is_res_x, 0, sizeof is_res_x);
    for (uint32_t x = 1; x < FIELD_SIZE && nres < s; ++x)
        if (count_of_x[x] == (int)MAX_FIBER) {
            resx[nres] = (int)x;
            resq[nres] = first_of_x[x];
            is_res_x[x] = 1;
            ++nres;
        }
    if (nres != s)
        return -1;
    nD = 0;
    for (uint32_t k = 0; k < npts; ++k)
        if (!is_res_x[pts[k].x])
            dlist[nD++] = k;
    return 0;
}

/* ------------------------------------------------------------------ */
/* Riemann-Roch space L(G)                                             */
/*                                                                    */
/* Let x_s be the x-values of the fibres that contain a pole of G and W  */
/* = prod (x - x_s) (simple zeros at all 8 points of each such fibre,   */
/* 8 poles at P_inf).  h is in L(G)  <=>  f = h W is in L((a+8 nf)P_inf) */
/* and vanishes at the fibre points that are not poles of G and at the  */
/* zeros of G.  All conditions are of first order (x - x_s is a local   */
/* parameter at every affine point because F_y = 1).                   */
/* Returns dim L(G), or -1 if G is not supported by this routine        */
/* (zero in a fibre that also contains a pole, or order > 1).           */
/* If rows != NULL, rows[t] receives h_t evaluated on D (length nD).    */
/* ------------------------------------------------------------------ */

static uint16_t Acon[CONMAX][RMAX + 1];
static uint16_t Nul[RMAX + 1][RMAX + 1];

static int nullspace(int ncon, int nc)
{
    static char ispiv[RMAX + 1];
    int pivcol[CONMAX], row = 0, dim = 0;

    memset(ispiv, 0, sizeof ispiv);
    for (int c = 0; c < nc && row < ncon; ++c) {
        int p = -1;
        for (int r = row; r < ncon; ++r)
            if (Acon[r][c] != 0) { p = r; break; }
        if (p < 0)
            continue;
        if (p != row)
            for (int k = 0; k < nc; ++k) {
                uint16_t t = Acon[p][k]; Acon[p][k] = Acon[row][k];
                Acon[row][k] = t;
            }
        uint16_t inv = gf_inv(Acon[row][c]);
        for (int k = c; k < nc; ++k)
            Acon[row][k] = gf_mul(Acon[row][k], inv);
        for (int r = 0; r < ncon; ++r) {
            uint16_t f = Acon[r][c];
            if (r == row || f == 0)
                continue;
            for (int k = c; k < nc; ++k)
                Acon[r][k] ^= gf_mul(f, Acon[row][k]);
        }
        pivcol[row] = c;
        ispiv[c] = 1;
        ++row;
    }
    for (int f = 0; f < nc; ++f)
        if (!ispiv[f]) {
            memset(Nul[dim], 0, sizeof(uint16_t) * (size_t)nc);
            Nul[dim][f] = 1;
            for (int r = 0; r < row; ++r)
                Nul[dim][pivcol[r]] = Acon[r][f];
            ++dim;
        }
    return dim;
}

static int has_point(const int *list, int n, int p)
{
    for (int i = 0; i < n; ++i)
        if (list[i] == p)
            return 1;
    return 0;
}

static int rr_space(const Div *G, uint16_t **rows)
{
    int fibx[MAXD], nf = 0, ncon = 0;

    for (int i = 0; i < G->npos; ++i) {
        int x = pts[G->pos[i]].x, j;
        for (j = 0; j < nf; ++j)
            if (fibx[j] == x)
                break;
        if (j == nf)
            fibx[nf++] = x;
    }
    for (int i = 0; i < G->nneg; ++i)
        for (int j = 0; j < nf; ++j)
            if (pts[G->neg[i]].x == fibx[j])
                return -1;                  /* zero in a pole fibre */
    long R = (long)G->a + 8L * nf;
    if (R < 0)
        return 0;
    if (R > RMAX)
        return -1;
    int nr = nb_upto((int)R);
    if (nr == 0)
        return 0;

    for (int j = 0; j < nf; ++j)
        for (int t = 0; t < count_of_x[fibx[j]]; ++t) {
            int P = first_of_x[fibx[j]] + t;
            if (has_point(G->pos, G->npos, P))
                continue;
            if (ncon >= CONMAX)
                return -1;
            for (int k = 0; k < nr; ++k)
                Acon[ncon][k] = basis[k].val[P];
            ++ncon;
        }
    for (int i = 0; i < G->nneg; ++i) {
        if (ncon >= CONMAX)
            return -1;
        for (int k = 0; k < nr; ++k)
            Acon[ncon][k] = basis[k].val[G->neg[i]];
        ++ncon;
    }
    int dim = nullspace(ncon, nr);
    if (rows != NULL)
        for (int t = 0; t < dim; ++t) {
            rows[t] = malloc(sizeof(uint16_t) * nD);
            for (uint32_t i = 0; i < nD; ++i) {
                uint32_t P = dlist[i];
                uint16_t f = 0, W = 1;
                for (int k = 0; k < nr; ++k)
                    if (Nul[t][k] != 0)
                        f ^= gf_mul(Nul[t][k], basis[k].val[P]);
                for (int j = 0; j < nf; ++j)
                    W = gf_mul(W, (uint16_t)(pts[P].x ^ fibx[j]));
                rows[t][i] = gf_mul(f, gf_inv(W));      /* W != 0 on D */
            }
        }
    return dim;
}

static int divisor_degree(const Div *G)
{
    return G->a + G->npos - G->nneg;
}

/* E = A - B (cancelling common points); -1 if a coefficient is not in
 * {-1, 0, 1} */
static int div_diff(const Div *A, const Div *B, Div *E)
{
    int all[4 * MAXD], na = 0;

    memset(E, 0, sizeof *E);
    E->a = A->a - B->a;
    for (int i = 0; i < A->npos; ++i) all[na++] = A->pos[i];
    for (int i = 0; i < A->nneg; ++i) all[na++] = A->neg[i];
    for (int i = 0; i < B->npos; ++i) all[na++] = B->pos[i];
    for (int i = 0; i < B->nneg; ++i) all[na++] = B->neg[i];
    for (int i = 0; i < na; ++i) {
        int p = all[i], seen = 0, cnt;
        for (int j = 0; j < i; ++j)
            if (all[j] == p)
                seen = 1;
        if (seen)
            continue;
        cnt = has_point(A->pos, A->npos, p) - has_point(A->neg, A->nneg, p) -
              has_point(B->pos, B->npos, p) + has_point(B->neg, B->nneg, p);
        if (cnt == 1 && E->npos < MAXD)
            E->pos[E->npos++] = p;
        else if (cnt == -1 && E->nneg < MAXD)
            E->neg[E->nneg++] = p;
        else if (cnt != 0)
            return -1;
    }
    return 0;
}

/* 1 if E is principal (degree 0 assumed), 0 if not, -1 if unsupported */
static int is_principal(const Div *E)
{
    int d = rr_space(E, NULL);
    return d < 0 ? -1 : d >= 1;
}

/* ------------------------------------------------------------------ */
/* Linear algebra on codes                                             */
/* ------------------------------------------------------------------ */

typedef struct {
    int ncols, rank, cap;
    uint16_t **v;
    int *piv;
} Ech;

static void ech_init(Ech *e, int ncols, int cap)
{
    e->ncols = ncols;
    e->rank = 0;
    e->cap = cap;
    e->v = calloc((size_t)cap, sizeof *e->v);
    e->piv = calloc((size_t)cap, sizeof(int));
}

static void ech_free(Ech *e)
{
    for (int i = 0; i < e->rank; ++i)
        free(e->v[i]);
    free(e->v);
    free(e->piv);
    e->v = NULL;
    e->piv = NULL;
    e->rank = 0;
}

static void ech_copy(Ech *dst, const Ech *src, int extra)
{
    ech_init(dst, src->ncols, src->cap + extra);
    for (int i = 0; i < src->rank; ++i) {
        dst->v[i] = malloc(sizeof(uint16_t) * (size_t)src->ncols);
        memcpy(dst->v[i], src->v[i], sizeof(uint16_t) * (size_t)src->ncols);
        dst->piv[i] = src->piv[i];
    }
    dst->rank = src->rank;
}

/* reduce w by the basis; returns the first non-zero column or -1 */
static int ech_reduce(const Ech *e, uint16_t *w)
{
    for (int i = 0; i < e->rank; ++i) {
        uint16_t c = w[e->piv[i]];
        const uint16_t *b = e->v[i];
        if (c == 0)
            continue;
        for (int k = e->piv[i]; k < e->ncols; ++k)
            if (b[k] != 0)
                w[k] ^= gf_mul(c, b[k]);
    }
    for (int k = 0; k < e->ncols; ++k)
        if (w[k] != 0)
            return k;
    return -1;
}

static int ech_insert(Ech *e, const uint16_t *vec)
{
    uint16_t *w;
    int p;

    if (e->rank >= e->cap)
        return 0;
    w = malloc(sizeof(uint16_t) * (size_t)e->ncols);
    memcpy(w, vec, sizeof(uint16_t) * (size_t)e->ncols);
    p = ech_reduce(e, w);
    if (p < 0) {
        free(w);
        return 0;
    }
    uint16_t inv = gf_inv(w[p]);
    for (int k = p; k < e->ncols; ++k)
        w[k] = gf_mul(w[k], inv);
    e->v[e->rank] = w;
    e->piv[e->rank] = p;
    ++e->rank;
    return 1;
}

static int ech_contains(const Ech *e, const uint16_t *vec)
{
    static uint16_t tmp[MAX_POINTS];

    memcpy(tmp, vec, sizeof(uint16_t) * (size_t)e->ncols);
    return ech_reduce(e, tmp) < 0;
}

typedef struct {
    int k;
    uint16_t **rows;
    Ech ech;
    int sqdim;                  /* dim of the Schur square C * C (or -1) */
} Code;

/* code C_L(D, G); returns k = dim L(G), or -1 */
static int code_from_div(const Div *G, Code *C)
{
    int k = rr_space(G, NULL);

    if (k < 0)
        return -1;
    C->k = k;
    C->rows = calloc((size_t)(k > 0 ? k : 1), sizeof *C->rows);
    if (C->rows == NULL)
        return -1;
    C->sqdim = -1;
    if (rr_space(G, C->rows) != k)
        return -1;
    ech_init(&C->ech, (int)nD, k > 0 ? k : 1);
    if (C->ech.v == NULL || C->ech.piv == NULL)
        return -1;
    for (int i = 0; i < k; ++i)
        ech_insert(&C->ech, C->rows[i]);
    /* The evaluation map must be injective on L(G) for dim C_L(D,G)=l(G). */
    if (C->ech.rank != k) {
        fprintf(stderr, "error: evaluation rows have rank %d, expected %d\n",
                C->ech.rank, k);
        return -1;
    }
    return k;
}

static void code_free(Code *C)
{
    for (int i = 0; i < C->k; ++i)
        free(C->rows[i]);
    free(C->rows);
    ech_free(&C->ech);
}

/* dimension of the Schur square C * C (invariant under monomial equivalence) */
static int schur_dim(Code *C)
{
    Ech e;
    static uint16_t prod[MAX_POINTS];
    int cap = C->k * (C->k + 1) / 2;

    if (C->sqdim >= 0)
        return C->sqdim;
    if (cap > (int)nD)
        cap = (int)nD;
    ech_init(&e, (int)nD, cap > 0 ? cap : 1);
    for (int i = 0; i < C->k && e.rank < cap; ++i)
        for (int j = i; j < C->k && e.rank < cap; ++j) {
            for (uint32_t t = 0; t < nD; ++t)
                prod[t] = gf_mul(C->rows[i][t], C->rows[j][t]);
            ech_insert(&e, prod);
        }
    C->sqdim = e.rank;
    ech_free(&e);
    return C->sqdim;
}

/* dim (A ∩ B) = kA + kB - dim (A + B) */
static int dim_intersection(const Code *A, const Code *B)
{
    Ech e;
    int rank;

    ech_copy(&e, &A->ech, B->k);
    for (int i = 0; i < B->k; ++i)
        ech_insert(&e, B->rows[i]);
    rank = e.rank;
    ech_free(&e);
    return A->k + B->k - rank;
}

static int codes_equal(const Code *A, const Code *B)
{
    if (A->k != B->k)
        return 0;
    for (int i = 0; i < B->k; ++i)
        if (!ech_contains(&A->ech, B->rows[i]))
            return 0;
    return 1;
}

/* is every codeword of A in B ? */
static int code_subset(const Code *A, const Code *B)
{
    for (int i = 0; i < A->k; ++i)
        if (!ech_contains(&B->ech, A->rows[i]))
            return 0;
    return 1;
}

static int common_setup(int nres_wanted)
{
    if (gf_init() != 0 || enumerate_points() != 0) {
        fprintf(stderr, "curve setup failed\n");
        return -1;
    }
    if (build_basis(RMAX) != 0) {
        fprintf(stderr, "basis setup failed\n");
        return -1;
    }
    if (setup_reserved(nres_wanted) != 0) {
        fprintf(stderr, "not enough fibres\n");
        return -1;
    }
    return 0;
}

static void print_point(const char *name, int idx)
{
    printf("#   %s = (%u,%u)\n", name, pts[idx].x, pts[idx].y);
}
/* ------------------------------------------------------------------ */
/* Two equal-parameter, different divisors and an ECP decoder            */
/*                                                                      */
/* We construct G_i = m P_inf + P_i - Q, with P_1,P_2,Q in three       */
/* different reserved fibres.  A = a P_inf - Q and B = b P_inf,        */
/* where a+b <= m.  Thus A+B <= G_i for both i, and consequently        */
/* C_L(D,A) * C_L(D,B) is contained in C_L(D,G_i).                      */
/* The decoded code is C_i = C_L(D,G_i)^perp.                           */
/*                                                                      */
/* The decoder uses the ECP syndrome map                                     */
/*   T_r : L(A) -> L(B)^*,  a |-> (b |-> sum_P r_P a(P)b(P)).           */
/* Its kernel gives functions vanishing at the error positions.         */
/* ------------------------------------------------------------------ */

#define DEFAULT_M 600
#define DEFAULT_A 300
#define DEFAULT_B 300
#define DEFAULT_T 256

static uint32_t rng_state = 0x6d2b79f5u;
static uint32_t rnd32(void)
{
    uint32_t x = rng_state;
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    rng_state = x;
    return x;
}
static uint16_t rnd_gf_nonzero(void)
{
    uint16_t x;
    do { x = (uint16_t)(rnd32() & FIELD_ORDER); } while (!x);
    return x;
}

static int div_one_point(int a, int pos, int neg, Div *G)
{
    memset(G, 0, sizeof *G);
    G->a = a;
    if (pos >= 0) G->pos[G->npos++] = pos;
    if (neg >= 0) G->neg[G->nneg++] = neg;
    return 0;
}

static int schur_contained(const Code *A, const Code *B, const Code *C)
{
    static uint16_t product[MAX_POINTS];
    for (int i = 0; i < A->k; ++i)
        for (int j = 0; j < B->k; ++j) {
            for (uint32_t p = 0; p < nD; ++p)
                product[p] = gf_mul(A->rows[i][p], B->rows[j][p]);
            if (!ech_contains(&C->ech, product)) return 0;
        }
    return 1;
}

/* RREF of a small matrix.  Returns rank; pivot columns are written to piv. */
static int small_rref(uint16_t a[CONMAX][MAXD + 1], int nr, int nc,
                      int *piv)
{
    int row = 0;
    for (int c = 0; c < nc && row < nr; ++c) {
        int p = row;
        while (p < nr && a[p][c] == 0) ++p;
        if (p == nr) continue;
        if (p != row)
            for (int j = c; j <= nc; ++j) {
                uint16_t z = a[p][j]; a[p][j] = a[row][j]; a[row][j] = z;
            }
        uint16_t iv = gf_inv(a[row][c]);
        for (int j = c; j <= nc; ++j) a[row][j] = gf_mul(a[row][j], iv);
        for (int i = 0; i < nr; ++i) if (i != row && a[i][c]) {
            uint16_t f = a[i][c];
            for (int j = c; j <= nc; ++j)
                a[i][j] ^= gf_mul(f, a[row][j]);
        }
        piv[row++] = c;
    }
    return row;
}

/* Solve H e = syndrome for a known list of at most MAXD positions. */
static int solve_error_values(const Code *G, const uint32_t *where,
                              int nw, const uint16_t *received,
                              uint16_t *value)
{
    uint16_t mat[CONMAX][MAXD + 1];
    int piv[MAXD], nr = G->k;
    if (nw > MAXD || nr > CONMAX) return -1;
    for (int i = 0; i < nr; ++i) {
        uint16_t s = 0;
        for (uint32_t p = 0; p < nD; ++p)
            s ^= gf_mul(G->rows[i][p], received[p]);
        for (int j = 0; j < nw; ++j) {
            mat[i][j] = G->rows[i][where[j]];
        }
        mat[i][nw] = s;
    }
    int rank = small_rref(mat, nr, nw, piv);
    if (rank != nw) return -1;
    for (int i = rank; i < nr; ++i)
        if (mat[i][nw] != 0) return -1;
    for (int j = 0; j < nw; ++j) value[piv[j]] = mat[j][nw];
    return 0;
}

/* Make a random word in the dual of the row space generated by G. */
static int random_dual_word(const Code *G, uint16_t *word)
{
    uint16_t **h = calloc((size_t)G->k, sizeof *h);
    int *piv = calloc((size_t)G->k, sizeof *piv);
    uint8_t *ispiv = calloc((size_t)nD, 1);
    if (!h || !piv || !ispiv) { free(h); free(piv); free(ispiv); return -1; }
    for (int i = 0; i < G->k; ++i) {
        h[i] = malloc(sizeof(uint16_t) * nD);
        if (!h[i]) { for (int j=0;j<i;++j) free(h[j]); free(h); free(piv); free(ispiv); return -1; }
        memcpy(h[i], G->rows[i], sizeof(uint16_t) * nD);
    }
    int row = 0;
    for (uint32_t c = 0; c < nD && row < G->k; ++c) {
        int p = row;
        while (p < G->k && h[p][c] == 0) ++p;
        if (p == G->k) continue;
        if (p != row) { uint16_t *z=h[p]; h[p]=h[row]; h[row]=z; }
        uint16_t iv = gf_inv(h[row][c]);
        for (uint32_t j = c; j < nD; ++j) h[row][j] = gf_mul(h[row][j], iv);
        for (int i = 0; i < G->k; ++i) if (i != row && h[i][c]) {
            uint16_t f = h[i][c];
            for (uint32_t j = c; j < nD; ++j) h[i][j] ^= gf_mul(f, h[row][j]);
        }
        piv[row] = (int)c; ispiv[c] = 1; ++row;
    }
    if (row != G->k) { for(int i=0;i<G->k;++i)free(h[i]); free(h);free(piv);free(ispiv);return -1; }
    memset(word, 0, sizeof(uint16_t) * nD);
    for (uint32_t c = 0; c < nD; ++c) if (!ispiv[c]) word[c] = (uint16_t)(rnd32() & FIELD_ORDER);
    for (int i = 0; i < G->k; ++i) {
        uint16_t z = 0;
        for (uint32_t c = 0; c < nD; ++c) if (!ispiv[c])
            z ^= gf_mul(h[i][c], word[c]);
        word[piv[i]] = z;
    }
    for (int i=0;i<G->k;++i) free(h[i]);
    free(h); free(piv); free(ispiv);
    return 0;
}

/* Decode r in C_L(D,G)^perp.  where[] is returned as indices in D. */
static int ecp_decode(const Code *A, const Code *B, const Code *G,
                      const uint16_t *received, int t,
                      uint16_t *decoded, int *nerrors)
{
    uint16_t mat[CONMAX][RMAX + 1];
    uint32_t where[MAXD];
    uint16_t errval[MAXD];
    int piv[RMAX + 1], nr = B->k, nc = A->k;
    if (t > MAXD || nr > CONMAX || nc > RMAX + 1) return -1;

    /* Equations for the kernel of T_r: one equation per basis element of B. */
    for (int j = 0; j < B->k; ++j) {
        for (int i = 0; i < A->k; ++i) {
            uint16_t z = 0;
            for (uint32_t p = 0; p < nD; ++p)
                z ^= gf_mul(received[p], gf_mul(A->rows[i][p], B->rows[j][p]));
            mat[j][i] = z;
        }
    }
    int rank = 0;
    /* RREF on nr x nc, with a zero RHS column. */
    for (int c = 0; c < nc && rank < nr; ++c) {
        int p = rank; while (p < nr && mat[p][c] == 0) ++p;
        if (p == nr) continue;
        if (p != rank) for (int j=0;j<nc;++j) { uint16_t z=mat[p][j];mat[p][j]=mat[rank][j];mat[rank][j]=z; }
        uint16_t iv=gf_inv(mat[rank][c]);
        for(int j=c;j<nc;++j) mat[rank][j]=gf_mul(mat[rank][j],iv);
        for(int i=0;i<nr;++i) if(i!=rank && mat[i][c]) { uint16_t f=mat[i][c]; for(int j=c;j<nc;++j) mat[i][j]^=gf_mul(f,mat[rank][j]); }
        piv[rank++]=c;
    }
    uint8_t ispiv[RMAX + 1] = {0};
    for (int i=0;i<rank;++i) ispiv[piv[i]]=1;
    int nul_dim=0;
    uint16_t kernel[RMAX + 1][RMAX + 1];
    memset(kernel,0,sizeof kernel);
    for(int f=0;f<nc;++f) if(!ispiv[f]) {
        kernel[nul_dim][f]=1;
        for(int i=0;i<rank;++i) kernel[nul_dim][piv[i]]=mat[i][f];
        ++nul_dim;
    }
    if (nul_dim == 0) return -1;

    /* Common zero set of the kernel functions. */
    int nwhere=0;
    for(uint32_t p=0;p<nD;++p) {
        int allzero=1;
        for(int u=0;u<nul_dim && allzero;++u) {
            uint16_t z=0;
            for(int i=0;i<A->k;++i) if(kernel[u][i]) z ^= gf_mul(kernel[u][i],A->rows[i][p]);
            if(z) allzero=0;
        }
        if(allzero) {
            if(nwhere>=t || nwhere>=MAXD) return -1;
            where[nwhere++]=p;
        }
    }
    if (nwhere == 0) {
        memcpy(decoded, received, sizeof(uint16_t) * nD);
        *nerrors=0;
        return 0;
    }
    memset(errval,0,sizeof errval);
    if (solve_error_values(G,where,nwhere,received,errval)!=0) return -1;
    memcpy(decoded,received,sizeof(uint16_t)*nD);
    for(int j=0;j<nwhere;++j) decoded[where[j]] ^= errval[j];

    /* Final membership test: every row of L(G) must be orthogonal. */
    for(int i=0;i<G->k;++i) {
        uint16_t z=0;
        for(uint32_t p=0;p<nD;++p) z ^= gf_mul(G->rows[i][p],decoded[p]);
        if(z) return -1;
    }
    *nerrors=nwhere;
    return 0;
}

static int make_received(const Code *G, int t, uint16_t *word,
                         uint16_t *received, uint32_t *actual)
{
    uint8_t *used = calloc((size_t)nD,1);
    if (!used) return -1;
    if (random_dual_word(G,word)!=0) { free(used); return -1; }
    memcpy(received,word,sizeof(uint16_t)*nD);
    for(int i=0;i<t;++i) {
        uint32_t p;
        do { p=rnd32()%nD; } while(used[p]);
        used[p]=1; actual[i]=p;
        received[p] ^= rnd_gf_nonzero();
    }
    free(used);
    return 0;
}

/* Check A+B <= G as divisors.  This proves L(A)L(B) subset L(G)
 * without testing every pair of evaluated basis vectors. */
static int ecp_divisor_condition(const Div *G, const Div *A, const Div *B)
{
    Div tmp, rem;
    if (div_diff(G, A, &tmp) != 0) return 0;
    if (div_diff(&tmp, B, &rem) != 0) return 0;
    /* The remainder must be effective: nonnegative infinity coefficient
       and no negative finite-point coefficients. */
    return rem.a >= 0 && rem.nneg == 0;
}

static int check_pair(const Div *G1, const Div *G2,
                      const Div *Adiv, const Div *Bdiv,
                      Code *C1, Code *C2, Code *A, Code *B)
{
    if (!ecp_divisor_condition(G1,Adiv,Bdiv) ||
        !ecp_divisor_condition(G2,Adiv,Bdiv)) return 0;
    if (code_from_div(G1,C1)<0 || code_from_div(G2,C2)<0 ||
        code_from_div(Adiv,A)<0 || code_from_div(Bdiv,B)<0) return -1;
    if (C1->k != C2->k) return 0;
    return 1;
}


/* Compare the injected error vector with the correction made by the decoder.
 * injected[p] = received[p] - codeword[p]
 * corrected[p] = received[p] - decoded[p]
 * In characteristic two, subtraction is XOR. */
static int compare_error_vector(const uint16_t *codeword,
                                const uint16_t *received,
                                const uint16_t *decoded)
{
    int equal = 1;
    int nin = 0, nout = 0;

    printf("\nError-vector comparison (nonzero positions):\n");
    printf(" position   injected    decoder\n");
    for (uint32_t p = 0; p < nD; ++p) {
        uint16_t injected = received[p] ^ codeword[p];
        uint16_t corrected = received[p] ^ decoded[p];
        if (injected) ++nin;
        if (corrected) ++nout;
        if (injected || corrected) {
            printf(" %8u   0x%03X      0x%03X%s\n",
                   p, injected, corrected,
                   injected == corrected ? "" : "  MISMATCH");
        }
        if (injected != corrected) equal = 0;
    }
    printf("injected nonzero symbols = %d\n", nin);
    printf("decoder correction symbols = %d\n", nout);
    printf("error vectors: %s\n", equal ? "IDENTICAL" : "DIFFERENT");
    return equal;
}

int main(int argc, char **argv)
{
    int m=DEFAULT_M, aa=DEFAULT_A, bb=DEFAULT_B, t=DEFAULT_T;
    int seed=1;
    if (argc>1) m=atoi(argv[1]);
    if (argc>2) t=atoi(argv[2]);
    if (argc>3) seed=atoi(argv[3]);
    /* G_i has a positive affine point, so rr_space needs basis up to m+8. */
    if (m<DEFAULT_A+DEFAULT_B || m>RMAX-8 || t<0 || t>DEFAULT_B-2*GENUS+1) {
        fprintf(stderr,"usage: %s [G-degree %d..%d] [errors 0..%d] [seed=1]\n",
                argv[0],DEFAULT_A+DEFAULT_B,RMAX-8,DEFAULT_B-2*GENUS+1);
        return 2;
    }
    rng_state=(uint32_t)seed;
    if (common_setup(3)!=0) return 1;
    if (nres<3) return 1;

    /* Pick Q, P1, P2 in distinct reserved fibres. */
    int Q=resq[0], P1=resq[1], P2=resq[2];
    Div G1,G2,Ad,Bd;
    div_one_point(m,P1,Q,&G1);
    div_one_point(m,P2,Q,&G2);
    div_one_point(aa,-1,Q,&Ad);
    div_one_point(bb,-1,-1,&Bd);

    Code C1={0},C2={0},A={0},B={0};
    int ok=check_pair(&G1,&G2,&Ad,&Bd,&C1,&C2,&A,&B);
    if(ok<=0) {
        fprintf(stderr,"failed to construct codes/ECP pair (status=%d)\n",ok);
        if (C1.rows) code_free(&C1);
        if (C2.rows) code_free(&C2);
        if (A.rows) code_free(&A);
        if (B.rows) code_free(&B);
        return 1;
    }

    /* For deg(G)>2g-2, Riemann--Roch gives l(G)=deg(G)-g+1.
       Since deg(G)<|D|, evaluation is injective and this is dim C_L(D,G). */
    int degG1 = divisor_degree(&G1);
    int degG2 = divisor_degree(&G2);
    int expected_l = degG1 - GENUS + 1;
    if (degG1 != degG2 || degG1 <= 2 * GENUS - 2 ||
        degG1 >= (int)nD || C1.k != expected_l || C2.k != expected_l) {
        fprintf(stderr,
                "Riemann-Roch/degree consistency check failed: deg=(%d,%d), "
                "computed l=(%d,%d), expected=%d, n=%u\n",
                degG1, degG2, C1.k, C2.k, expected_l, nD);
        code_free(&C1); code_free(&C2); code_free(&A); code_free(&B);
        return 1;
    }

    Div diff;
    if(div_diff(&G1,&G2,&diff)!=0) { fprintf(stderr,"divisor difference unsupported\n"); return 1; }
    int principal=is_principal(&diff);
    int same=codes_equal(&C1,&C2);
    int k=C1.k;
    int designed_dual_distance=m-2*GENUS+2;

    printf("Suzuki curve over GF(2^%d), polynomial 0x%x\n",FIELD_M,FIELD_POLY);
    printf("affine rational points = %u, reserved fibres = %d, evaluation length n = %u\n",npts,nres,nD);
    printf("G1 = %d P_inf + P1 - Q, G2 = %d P_inf + P2 - Q\n",m,m);
    print_point("Q",Q); print_point("P1",P1); print_point("P2",P2);
    printf("deg(G1) = deg(G2) = %d\n",degG1);
    printf("dim L(G1) = dim L(G2) = %d (Riemann-Roch: deg(G)-g+1)\n",C1.k);
    printf("evaluation codes C_L(D,G_i): [n=%u, k=%d, d >= %u]\n",
           nD,k,nD-(uint32_t)degG1);
    printf("dual target codes C_i = C_L(D,G_i)^perp: [n=%u, k=%u, d >= %d]\n",
           nD,nD-(uint32_t)k,designed_dual_distance);
    printf("A: dim=%d, B: dim=%d, t=%d\n",A.k,B.k,t);
    printf("A*B subset L(G1): yes; A*B subset L(G2): yes\n");
    printf("G1-G2 principal: %s\n",principal==0?"no":principal==1?"yes":"unsupported");
    printf("evaluation row spaces L(G1), L(G2) equal: %s\n",same?"yes":"no");
    printf("Note: both distance values are designed lower bounds, not exact minimum-distance computations.\n");
    if(principal!=0 || same) printf("WARNING: this pair has not passed the intended distinctness test.\n");

    uint16_t *cw=calloc(nD,sizeof(uint16_t)), *r=calloc(nD,sizeof(uint16_t));
    uint16_t *dec=calloc(nD,sizeof(uint16_t));
    uint32_t actual[MAXD];
    if(!cw||!r||!dec) return 1;
    for(int which=0;which<2;++which) {
        const Code *G=which?&C2:&C1;
        if(make_received(G,t,cw,r,actual)!=0) { fprintf(stderr,"test-word generation failed\n"); return 1; }
        int got=-1;
        int rc=ecp_decode(&A,&B,G,r,t,dec,&got);
        int equal = 0;
        if (rc == 0) {
            int error_equal = compare_error_vector(cw, r, dec);
            equal = (error_equal &&
                     memcmp(cw, dec, sizeof(uint16_t) * nD) == 0);
        }
        printf("decode C%d: rc=%d, corrected errors=%d, exact recovery=%s\n",
               which+1, rc, got, equal ? "yes" : "no");
        if (rc != 0)
            printf("  decoder failed; no correction vector to compare\n");
        else if (!equal)
            printf("  decoder did not recover the original codeword\n");
    }
    free(cw);free(r);free(dec);
    code_free(&C1);code_free(&C2);code_free(&A);code_free(&B);
    for(int i=0;i<nbasis;++i) free(basis[i].val);
    return 0;
}
