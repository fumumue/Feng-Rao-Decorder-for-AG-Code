/*
 * Method 1: codes with the same parameters from different divisor CLASSES,
 *           plus a Feng-Rao decoder with majority voting for their duals.
 *
 * Curve: Suzuki curve  y^8 + y = x^2 (x^8 + x)  over GF(2^12), genus 14,
 *        5888 affine points + P_inf.
 * Codes: C_L(D, G_ij),  G_ij = m P_inf + Q_i - Q_j  (deg G_ij = m),
 *        Q_i, Q_j rational points from s reserved fibres.  D = all affine
 *        points outside the reserved fibres, so every code has the same
 *        length n = 5888 - 8 s, dimension k = m + 1 - g (m >= 2g-1) and the
 *        same Goppa bound d >= n - m.
 *
 * G_ij and G_kl give equivalent codes if G_ij ~ G_kl (linearly equivalent),
 * and codes of effective divisors of the same degree are equal only if the
 * divisors are equal.  Here G_ij - G_kl = (Q_i - Q_j) - (Q_k - Q_l); it is
 * principal iff there is a function with exactly this divisor, which the
 * program decides with the Riemann-Roch routine (is_principal).
 *
 * L(G) is computed with first-order conditions only:
 *   h in L(a P_inf + Q - Z)  <=>  f = h (x - x_Q) lies in L((a+8) P_inf),
 *   vanishes at the 7 other points of the fibre of Q and at the points Z.
 * (F_y = 1, so x - x_Q is a local parameter at every affine point.)
 *
 * Invariant used to tell codes apart: dim(C * C), the Schur square, is
 * unchanged by monomial equivalence.  For deg G >= 2g+1 it is the same for
 * all classes; the interesting range is m close to 2g-1 .. 2g+1.
 *
 * ---------------------------------------------------------------------
 * DECODING (new, second half of this file)
 *
 * C_L(D, G) itself has tiny dimension k = m+1-g, so the code that one
 * wants to decode is its DUAL  C_L(D, G)^perp  (= C_Omega type code, length
 * n, redundancy k, designed distance d* = Feng-Rao order bound).  Its parity
 * checks are exactly the generator rows of C_L(D, G).
 *
 *  * G = m P_inf: parity checks  f_0 .. f_k  (pole order <= m).  Plain
 *    one-point code; Feng-Rao majority voting finds the unknown syndromes
 *    s(f_l), rho_l > m, and then the error locations / values.
 *
 *  * G = m P_inf + Q_i - Q_j (any divisor class): with W = x - x_i,
 *       h in L(G)  <=>  f = h W in L((m+8) P_inf), f = 0 at the 7 other
 *       points of the fibre of Q_i and at Q_j.
 *    Put c' = c / W (componentwise on D).  Then c in C_L(D,G)^perp  <=>
 *       sum c'_P f(P) = 0 for all f vanishing on S8 = {7 points, Q_j}
 *    <=>  the syndrome of (c', 0) w.r.t. L((m+8) P_inf) is a combination
 *         sum_Q mu_Q f(Q) over S8, i.e. (c', mu) is a word of the one-point
 *         code C_Omega(D u S8, (m+8) P_inf).
 *    So the 8 points of S8 behave as 8 additional ERRORS at known
 *    positions.  The class code is therefore decoded by the same one-point
 *    decoder with m' = m + 8, evaluation set D u S8, and t + 8 <= tmax.
 *    (The 8 "erasures" are treated as errors; handling them as true
 *    erasures would gain 8 in the radius but needs a modified voting.)
 *
 * Feng-Rao majority voting (Feng-Rao 1993, Duursma 1993):
 *   S_ij = s(f_i f_j) is a Hankel-like matrix of rank t = #errors.  For
 *   rho_l > m' the syndrome s_l = s(f_l) is unknown, but every pair
 *   (i,j) with rho_i + rho_j = rho_l that is a "candidate"
 *      rank S[0..i-1][0..j-1] = rank S[0..i-1][0..j] = rank S[0..i][0..j-1]
 *   votes for the unique value of S_ij that keeps the rank.  The number of
 *   wrong votes is <= t, correct votes >= N_l - 2t + wrong, with
 *   N_l = #{(i,j): rho_i + rho_j = rho_l}, so the majority is correct for
 *   t < d* / 2, with d* = min over rho_l > m' of N_l.  Once the syndromes reach order
 *   R ~ 2t + 4g, the kernel of the known part of S gives functions that
 *   vanish on the error positions (locator), the error values follow from
 *   a linear system, and the result is checked against ALL syndromes.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki_divclass suzuki_divclass.c
 * Run:   ./suzuki_divclass [-m degree] [-s number_of_reserved_fibres]
 *            experiment of the original program (divisor classes)
 *        ./suzuki_divclass -t T [-m degree] [-s fibres] [-i I -j J]
 *                          [-N trials] [-p pattern] [-R min_order] [-S seed]
 *            decode the dual of C_L(D, mP_inf) (or of C_L(D, G_IJ) when
 *            -i/-j are given) with T random errors, N trials;
 *            -p 0 random errors, -p 1..4 errors on level sets of x,y,z,w
 *            -R forces majority voting up to syndrome order min_order
 */

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
#define RMAX 200                /* highest pole order in the basis          */
#endif
#define MAXD 24                 /* points in a divisor                      */
#define MAXRES 12               /* reserved fibres                          */
#define CONMAX 256              /* vanishing conditions                     */

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
    C->sqdim = -1;
    rr_space(G, C->rows);
    ech_init(&C->ech, (int)nD, k > 0 ? k : 1);
    for (int i = 0; i < k; ++i)
        ech_insert(&C->ech, C->rows[i]);
    if (C->ech.rank != k)
        fprintf(stderr, "warning: generator rows dependent (rank %d < k %d)\n",
                C->ech.rank, k);
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
static __attribute__((unused)) int code_subset(const Code *A, const Code *B)
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

static Div div_inf(int a)
{
    Div d;

    memset(&d, 0, sizeof d);
    d.a = a;
    return d;
}

/* ------------------------------------------------------------------ */
/* Method 1: change the CLASS of the divisor                           */
/*   G_ij = m P_inf + Q_i - Q_j   (degree m, same parameters for all i,j) */
/* ------------------------------------------------------------------ */

static int experiment_classes(int m, int s)
{
    printf("# Suzuki curve y^8 + y = x^2 (x^8 + x) over GF(2^12): %u affine "
           "points, genus %d\n", npts, GENUS);
    printf("# %d reserved fibres (8 points each) are removed from D: "
           "length n = %u\n", s, nD);
    for (int i = 0; i < s; ++i) {
        char name[16];
        snprintf(name, sizeof name, "Q_%d", i);
        print_point(name, resq[i]);
    }

    Div G0 = div_inf(m);
    Code C0;
    int k0 = code_from_div(&G0, &C0);
    printf("# reference code C0 = C_L(D, %d P_inf): [%u, %d, >=%u]  "
           "(k = m+1-g = %d)\n", m, nD, k0, nD - (unsigned)m, m + 1 - GENUS);
    printf("#   dim C0*C0 = %d  (2m+1-g = %d)\n", schur_dim(&C0),
           2 * m + 1 - GENUS);

    /* self-check: a principal shift gives a monomially equivalent code:
     * G_s = G0 + div(x - x_0) = (m-8) P_inf + (8 points of the fibre x_0)  */
    {
        static uint16_t tmp[MAX_POINTS];
        Div Gs = div_inf(m - 8), E;
        Code Cs;
        int ok;

        for (int t = 0; t < 8; ++t)
            Gs.pos[Gs.npos++] = first_of_x[resx[0]] + t;
        div_diff(&Gs, &G0, &E);
        ok = is_principal(&E) == 1;
        int ks = code_from_div(&Gs, &Cs);
        ok = ok && ks == k0;
        for (int i = 0; i < ks && ok; ++i) {
            for (uint32_t t = 0; t < nD; ++t)
                tmp[t] = gf_mul(Cs.rows[i][t],
                                (uint16_t)(pts[dlist[t]].x ^ resx[0]));
            if (!ech_contains(&C0.ech, tmp))
                ok = 0;
        }
        printf("# self-check: G0 + div(x - x_0) is principal and gives the "
               "code diag(1/(x-x_0)) * C0 : %s\n", ok ? "OK" : "FAILED");
        code_free(&Cs);
    }

    int np = s * (s - 1);
    Div *G = malloc((size_t)np * sizeof *G);
    Code *C = malloc((size_t)np * sizeof *C);
    int *gi = malloc((size_t)np * sizeof(int));
    int *gj = malloc((size_t)np * sizeof(int));
    int nc = 0, bad = 0;

    printf("# codes C_L(D, G_ij), G_ij = %d P_inf + Q_i - Q_j:\n", m);
    printf("#   (i,j)    k   dim C*C   dim C∩C0   G_ij - %dP_inf principal?\n",
           m);
    for (int i = 0; i < s; ++i)
        for (int j = 0; j < s; ++j) {
            Div E;
            int pr;

            if (i == j)
                continue;
            G[nc] = div_inf(m);
            G[nc].pos[G[nc].npos++] = resq[i];
            G[nc].neg[G[nc].nneg++] = resq[j];
            gi[nc] = i;
            gj[nc] = j;
            int k = code_from_div(&G[nc], &C[nc]);
            if (k != m + 1 - GENUS)
                ++bad;
            div_diff(&G[nc], &G0, &E);
            pr = is_principal(&E);
            printf("#   (%d,%d)  %3d   %6d   %8d   %s\n", i, j, k,
                   schur_dim(&C[nc]), dim_intersection(&C[nc], &C0),
                   pr == 0 ? "no (class differs from m P_inf)" :
                   pr == 1 ? "YES" : "?");
            ++nc;
        }
    printf("# all codes have k = m+1-g: %s\n", bad ? "NO" : "yes");

    int tested = 0, equiv = 0, unsup = 0, equal = 0;
    for (int a = 0; a < nc; ++a)
        for (int b = a + 1; b < nc; ++b) {
            Div E;
            int pr;

            ++tested;
            if (codes_equal(&C[a], &C[b]))
                ++equal;
            if (div_diff(&G[a], &G[b], &E) != 0) {
                ++unsup;
                continue;
            }
            pr = is_principal(&E);
            if (pr < 0)
                ++unsup;
            else if (pr == 1) {
                ++equiv;
                printf("#   G_%d%d ~ G_%d%d (linearly equivalent)\n", gi[a],
                       gj[a], gi[b], gj[b]);
            }
        }
    printf("# %d pairs of divisors: %d linearly equivalent, %d with equal "
           "codes, %d not testable (a point with coefficient 2)\n", tested,
           equiv, equal, unsup);

    int distinct = 0, vals[256];
    for (int a = 0; a < nc; ++a) {
        int d = schur_dim(&C[a]), seen = 0;
        for (int t = 0; t < distinct; ++t)
            if (vals[t] == d)
                seen = 1;
        if (!seen && distinct < 256)
            vals[distinct++] = d;
    }
    printf("# dim(C*C) takes %d distinct value(s):", distinct);
    for (int t = 0; t < distinct; ++t)
        printf(" %d", vals[t]);
    printf("\n");

    for (int a = 0; a < nc; ++a)
        code_free(&C[a]);
    code_free(&C0);
    free(G); free(C); free(gi); free(gj);
    return EXIT_SUCCESS;
}

/* ================================================================== */
/* Feng-Rao decoder with majority voting (one-point codes at P_inf)    */
/*                                                                    */
/* Code decoded:  C = { c in F^N : sum_p c_p f_t(pos_p) = 0, rho_t <= m' } */
/* Basis f_0 .. f_{nbasis-1} of L(RMAX P_inf) ordered by pole order     */
/* rho_t (semigroup <8,10,12,13>).                                      */
/* ================================================================== */

static int idx_of_rho[RMAX + 1];        /* semigroup element -> index or -1 */
static int Bpts[RMAX + 1];              /* points for the product decomposition */
static uint16_t invV[RMAX + 1][RMAX + 1];
static uint16_t *cfc[RMAX + 1][RMAX + 1];   /* cache: f_i f_j = sum_t c_t f_t */
static int fr_ready;
static int fr_rmin;                     /* do not try to locate before this order (tests voting) */

static uint16_t synd[RMAX + 1];         /* s_t = s(f_t), known or voted      */
static uint16_t Sm[RMAX + 1][RMAX + 1]; /* S_ij = s(f_i f_j) (0 = unknown)   */

typedef struct {
    int nerr;                           /* number of non-zero error values   */
    int p[RMAX + 2];                    /* positions (index into pos[])      */
    uint16_t v[RMAX + 2];               /* error values                      */
    int R;                              /* syndromes known up to this order  */
    int nvotes;                         /* syndromes obtained by voting      */
    int minmargin;                      /* smallest (winner - runner-up)     */
    int a, b, ra, cb;                   /* ECP pair A = L(aP), B = L(bP), dims */
} FRRes;

/* Gauss-Jordan on an nrows x ncols matrix (row-major); the first nvars
 * columns are eliminated in order, the last column is the right-hand side.
 * Returns nvars on success, -1 if a pivot is missing, -2 if inconsistent. */
static int gj_solve(uint16_t *A, int nrows, int ncols, int nvars)
{
    for (int c = 0; c < nvars; ++c) {
        int p = -1;
        for (int r = c; r < nrows; ++r)
            if (A[(size_t)r * ncols + c] != 0) { p = r; break; }
        if (p < 0)
            return -1;
        if (p != c)
            for (int k = 0; k < ncols; ++k) {
                uint16_t t = A[(size_t)p * ncols + k];
                A[(size_t)p * ncols + k] = A[(size_t)c * ncols + k];
                A[(size_t)c * ncols + k] = t;
            }
        uint16_t inv = gf_inv(A[(size_t)c * ncols + c]);
        for (int k = c; k < ncols; ++k)
            A[(size_t)c * ncols + k] = gf_mul(A[(size_t)c * ncols + k], inv);
        for (int r = 0; r < nrows; ++r) {
            uint16_t f = A[(size_t)r * ncols + c];
            if (r == c || f == 0)
                continue;
            for (int k = c; k < ncols; ++k)
                A[(size_t)r * ncols + k] ^= gf_mul(f, A[(size_t)c * ncols + k]);
        }
    }
    for (int r = nvars; r < nrows; ++r)
        if (A[(size_t)r * ncols + ncols - 1] != 0)
            return -2;
    return nvars;
}

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd(void)
{
    rng_state ^= rng_state >> 12;
    rng_state ^= rng_state << 25;
    rng_state ^= rng_state >> 27;
    return rng_state * 2685821657736338717ULL;
}

/* Choose nbasis points B_k with an invertible matrix [f_t(B_k)] and store its
 * inverse.  Then f_i f_j = sum_t c_t f_t with c = invV * (f_i f_j)(B). */
static int fr_setup(void)
{
    static uint16_t Aug[RMAX + 1][2 * (RMAX + 1)];
    int nB = 0, n = nbasis;
    Ech e;
    uint16_t *vec;

    if (fr_ready)
        return 0;
    for (int r = 0; r <= RMAX; ++r)
        idx_of_rho[r] = -1;
    for (int i = 0; i < nbasis; ++i)
        idx_of_rho[basis[i].rho] = i;

    ech_init(&e, n, n);
    vec = malloc(sizeof(uint16_t) * (size_t)n);
    for (uint32_t P = 0; P < npts && nB < n; ++P) {
        for (int t = 0; t < n; ++t)
            vec[t] = basis[t].val[P];
        if (ech_insert(&e, vec))
            Bpts[nB++] = (int)P;
    }
    free(vec);
    ech_free(&e);
    if (nB != n) {
        fprintf(stderr, "could not find %d independent points\n", n);
        return -1;
    }
    memset(Aug, 0, sizeof Aug);
    for (int k = 0; k < n; ++k) {
        for (int t = 0; t < n; ++t)
            Aug[k][t] = basis[t].val[Bpts[k]];
        Aug[k][n + k] = 1;
    }
    for (int c = 0; c < n; ++c) {
        int p = -1;
        for (int r = c; r < n; ++r)
            if (Aug[r][c] != 0) { p = r; break; }
        if (p < 0)
            return -1;
        if (p != c)
            for (int k = 0; k < 2 * n; ++k) {
                uint16_t t = Aug[p][k]; Aug[p][k] = Aug[c][k]; Aug[c][k] = t;
            }
        uint16_t inv = gf_inv(Aug[c][c]);
        for (int k = 0; k < 2 * n; ++k)
            Aug[c][k] = gf_mul(Aug[c][k], inv);
        for (int r = 0; r < n; ++r) {
            uint16_t f = Aug[r][c];
            if (r == c || f == 0)
                continue;
            for (int k = 0; k < 2 * n; ++k)
                Aug[r][k] ^= gf_mul(f, Aug[c][k]);
        }
    }
    for (int t = 0; t < n; ++t)
        for (int k = 0; k < n; ++k)
            invV[t][k] = Aug[t][n + k];
    fr_ready = 1;
    return 0;
}

/* coefficients c_0 .. c_l of f_i f_j (l = index of rho_i + rho_j) */
static const uint16_t *decomp(int i, int j)
{
    uint16_t g[RMAX + 1], *c;
    int sum, l;

    if (i > j) { int t = i; i = j; j = t; }
    if (cfc[i][j] != NULL)
        return cfc[i][j];
    sum = basis[i].rho + basis[j].rho;
    if (sum > RMAX || (l = idx_of_rho[sum]) < 0)
        return NULL;
    for (int k = 0; k < nbasis; ++k)
        g[k] = gf_mul(basis[i].val[Bpts[k]], basis[j].val[Bpts[k]]);
    c = malloc(sizeof(uint16_t) * (size_t)(l + 1));
    for (int t = 0; t <= l; ++t) {
        uint16_t acc = 0;
        for (int k = 0; k < nbasis; ++k)
            acc ^= gf_mul(invV[t][k], g[k]);
        c[t] = acc;
    }
    cfc[i][j] = c;
    return c;
}

static int fr_selfcheck(void)
{
    int bad = 0;

    for (int trial = 0; trial < 40; ++trial) {
        int i = (int)(rnd() % (uint64_t)nbasis), j = (int)(rnd() % (uint64_t)nbasis);
        const uint16_t *c;
        int l;

        if (basis[i].rho + basis[j].rho > RMAX)
            continue;
        l = idx_of_rho[basis[i].rho + basis[j].rho];
        c = decomp(i, j);
        if (c == NULL || c[l] == 0) {
            ++bad;
            continue;
        }
        for (int q = 0; q < 4; ++q) {
            uint32_t P = (uint32_t)(rnd() % npts);
            uint16_t lhs = gf_mul(basis[i].val[P], basis[j].val[P]), rhs = 0;
            for (int t = 0; t <= l; ++t)
                rhs ^= gf_mul(c[t], basis[t].val[P]);
            if (lhs != rhs)
                ++bad;
        }
    }
    return bad;
}

/* N_l = #{(i,j) : rho_i + rho_j = rho_l}  (ordered pairs) */
static int fr_nu(int l)
{
    int n = 0;
    for (int i = 0; i <= l; ++i)
        if (idx_of_rho[basis[l].rho - basis[i].rho] >= 0)
            ++n;
    return n;
}

/* Feng-Rao bound d* = min { N_l : rho_l > mp } */
static int fr_dstar(int mp)
{
    int d = -1;
    for (int l = 0; l < nbasis; ++l)
        if (basis[l].rho > mp) {
            int v = fr_nu(l);
            if (d < 0 || v < d)
                d = v;
        }
    return d;
}

/* S_ij for all pairs with rho_i + rho_j = rho_l, once s_0 .. s_l are known */
static void fr_fill_sums(int l)
{
    for (int i = 0; i <= l; ++i) {
        int j = idx_of_rho[basis[l].rho - basis[i].rho];
        const uint16_t *c;
        uint16_t acc = 0;

        if (j < 0)
            continue;
        c = decomp(i, j);
        for (int t = 0; t <= l; ++t)
            acc ^= gf_mul(c[t], synd[t]);
        Sm[i][j] = acc;
    }
}

/* Majority vote for the unknown syndrome s_l.  Rows are inserted one by one
 * into an echelon basis (leftmost pivots); then, for the row i and the
 * column j with rho_i + rho_j = rho_l,
 *   rank S[0..i-1][0..j] = rank S[0..i-1][0..j-1]   <=>  no pivot in column j
 *   rank S[0..i][0..j-1] = rank S[0..i-1][0..j-1]   <=>  row i (columns < j)
 *                                                       reduces to zero
 * and the value of S_ij keeping the rank is the residual in column j.
 * Returns 0 and the winning value, or -1 if there is no strict majority. */
static int fr_vote(int l, uint16_t *val, int *margin)
{
    static uint16_t Ev[RMAX + 1][RMAX + 1];
    static int Elead[RMAX + 1];
    uint16_t w[RMAX + 1], cand[RMAX + 2];
    int ne = 0, nc = 0, W = l + 1, rl = basis[l].rho;

    for (int i = 0; i <= l; ++i) {
        int j = idx_of_rho[rl - basis[i].rho];

        if (j >= 0) {
            int ok = 1;
            for (int e = 0; e < ne; ++e)
                if (Elead[e] == j) { ok = 0; break; }
            if (ok) {
                memcpy(w, Sm[i], sizeof(uint16_t) * (size_t)W);
                for (int e = 0; e < ne; ++e) {
                    int p = Elead[e];
                    uint16_t c;
                    if (p >= j)
                        continue;
                    c = w[p];
                    if (c == 0)
                        continue;
                    for (int k = p; k <= j; ++k)
                        w[k] ^= gf_mul(c, Ev[e][k]);
                }
                for (int k = 0; k < j; ++k)
                    if (w[k] != 0) { ok = 0; break; }
                if (ok) {
                    const uint16_t *cf = decomp(i, j);
                    uint16_t acc = w[j];
                    if (cf != NULL && cf[l] != 0) {
                        for (int t = 0; t < l; ++t)
                            acc ^= gf_mul(cf[t], synd[t]);
                        cand[nc++] = gf_mul(acc, gf_inv(cf[l]));
                    }
                }
            }
        }
        /* insert row i (known entries only; unknown ones are 0) */
        memcpy(w, Sm[i], sizeof(uint16_t) * (size_t)W);
        for (int e = 0; e < ne; ++e) {
            int p = Elead[e];
            uint16_t c = w[p];
            if (c == 0)
                continue;
            for (int k = p; k < W; ++k)
                w[k] ^= gf_mul(c, Ev[e][k]);
        }
        {
            int p = -1;
            for (int k = 0; k < W; ++k)
                if (w[k] != 0) { p = k; break; }
            if (p >= 0) {
                uint16_t inv = gf_inv(w[p]);
                memset(Ev[ne], 0, sizeof(uint16_t) * (size_t)W);
                for (int k = p; k < W; ++k)
                    Ev[ne][k] = gf_mul(w[k], inv);
                Elead[ne++] = p;
            }
        }
    }

    if (nc == 0)
        return -1;
    {
        int best = -1, bestc = 0, second = 0;
        for (int a = 0; a < nc; ++a) {
            int cnt = 0, seen = 0;
            for (int b = 0; b < nc; ++b)
                if (cand[b] == cand[a]) {
                    ++cnt;
                    if (b < a)
                        seen = 1;
                }
            if (seen)
                continue;
            if (cnt > bestc) {
                second = bestc;
                bestc = cnt;
                best = a;
            } else if (cnt > second)
                second = cnt;
        }
        *margin = bestc - second;
        if (*margin <= 0)
            return -1;
        *val = cand[best];
    }
    return 0;
}

/* With the syndromes s_0 .. s_{nk-1} (order R) known: take the kernel of the
 * known block  S[rho_i <= R/2][rho_j <= R - R/2]  (functions h = sum kappa_i f_i
 * with sum_P e_P h(P) f_j(P) = 0), intersect their zero sets on the positions,
 * solve for the error values, and accept only a solution that matches all nk
 * syndromes and has weight <= tmax. */
static int fr_try(int nk, const int *pos, int N, int tmax, FRRes *res)
{
    int Rk = basis[nk - 1].rho, a = Rk / 2, b = Rk - a;
    int ra = nb_upto(a), cb = nb_upto(b), dim, nz = 0, zl[RMAX + 2];
    uint16_t *A;
    int ncols, rc, cnt = 0;

    if (ra < 1 || cb < 1)
        return 0;
    for (int c = 0; c < cb; ++c)
        for (int i = 0; i < ra; ++i)
            Acon[c][i] = Sm[i][c];
    dim = nullspace(cb, ra);
    if (dim == 0)
        return 0;
    for (int p = 0; p < N; ++p) {
        uint32_t P = (uint32_t)pos[p];
        uint16_t f = 0;
        for (int k = 0; k < ra; ++k)
            if (Nul[0][k] != 0)
                f ^= gf_mul(Nul[0][k], basis[k].val[P]);
        if (f == 0) {
            if (nz >= RMAX)
                return 0;
            zl[nz++] = p;
        }
    }
    for (int d = 1; d < dim && nz > 0; ++d) {
        int keep = 0;
        for (int q = 0; q < nz; ++q) {
            uint32_t P = (uint32_t)pos[zl[q]];
            uint16_t f = 0;
            for (int k = 0; k < ra; ++k)
                if (Nul[d][k] != 0)
                    f ^= gf_mul(Nul[d][k], basis[k].val[P]);
            if (f == 0)
                zl[keep++] = zl[q];
        }
        nz = keep;
    }
    if (nz == 0 || nz > nk)
        return 0;

    ncols = nz + 1;
    A = malloc(sizeof(uint16_t) * (size_t)nk * (size_t)ncols);
    for (int k = 0; k < nk; ++k) {
        for (int z = 0; z < nz; ++z)
            A[(size_t)k * ncols + z] = basis[k].val[pos[zl[z]]];
        A[(size_t)k * ncols + nz] = synd[k];
    }
    rc = gj_solve(A, nk, ncols, nz);
    if (rc == nz) {
        for (int z = 0; z < nz; ++z)
            if (A[(size_t)z * ncols + nz] != 0)
                ++cnt;
        if (cnt <= tmax) {
            res->a = a; res->b = b; res->ra = ra; res->cb = cb;
            res->nerr = 0;
            for (int z = 0; z < nz; ++z)
                if (A[(size_t)z * ncols + nz] != 0) {
                    res->p[res->nerr] = zl[z];
                    res->v[res->nerr] = A[(size_t)z * ncols + nz];
                    ++res->nerr;
                }
        } else
            rc = -3;
    }
    free(A);
    return rc == nz;
}

/* Decode r (length N, evaluation points pos[]) in the code with parity checks
 * f_t, rho_t <= mp.  tmax = (d* - 1) / 2.  Returns 0 on success (res holds the
 * error vector), -1 if the syndromes ran out of range, -2 if a vote failed. */
static int fr_decode(const int *pos, int N, const uint16_t *r, int mp,
                     int tmax, FRRes *res)
{
    int nm = nb_upto(mp), nk, allzero = 1;

    memset(res, 0, sizeof *res);
    res->minmargin = 1 << 30;
    memset(Sm, 0, sizeof Sm);
    memset(synd, 0, sizeof synd);
    for (int t = 0; t < nm; ++t) {
        uint16_t acc = 0;
        for (int p = 0; p < N; ++p)
            if (r[p] != 0)
                acc ^= gf_mul(r[p], basis[t].val[pos[p]]);
        synd[t] = acc;
        if (acc != 0)
            allzero = 0;
    }
    res->R = basis[nm - 1].rho;
    if (allzero)
        return 0;                           /* a code word: no errors */
    for (int l = 0; l < nm; ++l)
        fr_fill_sums(l);
    nk = nm;
    for (;;) {
        uint16_t val;
        int margin;

        if (basis[nk - 1].rho >= fr_rmin && fr_try(nk, pos, N, tmax, res)) {
            res->R = basis[nk - 1].rho;
            return 0;
        }
        if (nk >= nbasis)
            return -1;
        if (fr_vote(nk, &val, &margin) < 0)
            return -2;
        if (margin < res->minmargin)
            res->minmargin = margin;
        synd[nk] = val;
        fr_fill_sums(nk);
        ++nk;
        ++res->nvotes;
    }
}

/* ------------------------------------------------------------------ */
/* Decoding experiment                                                 */
/* ------------------------------------------------------------------ */

/* error patterns: -p 0 random; -p 1..4 put the errors on level sets of the
 * functions x, y, z = x^5+y^4, w = x y^4 + z^4 (pole orders 8, 10, 12, 13),
 * largest level sets first, i.e. on the zero sets of low-order functions
 * (x = c: up to 8 points, y = c: up to 10, ...).  Such positions are the
 * ones for which "independent evaluations" can fail without the pole-order
 * conditions of the ECP. */
typedef struct {
    int size, start;
    uint64_t key;
} Grp;

static uint16_t level_value(int pat, uint32_t P)
{
    uint16_t x = pts[P].x, y = pts[P].y, y4 = gf_pow(y, 4);
    uint16_t z = (uint16_t)(gf_pow(x, 5) ^ y4);
    uint16_t w = (uint16_t)(gf_mul(x, y4) ^ gf_pow(z, 4));

    return pat == 1 ? x : pat == 2 ? y : pat == 3 ? z : w;
}

static uint16_t *lv_cur;
static uint16_t *lv_val;

static int cmp_idx(const void *a, const void *b)
{
    int i = *(const int *)a, j = *(const int *)b;

    if (lv_val[i] != lv_val[j])
        return lv_val[i] < lv_val[j] ? -1 : 1;
    return i < j ? -1 : i > j;
}

static int cmp_grp(const void *a, const void *b)
{
    const Grp *g = a, *h = b;

    if (g->size != h->size)
        return g->size > h->size ? -1 : 1;
    return g->key < h->key ? -1 : g->key > h->key;
}

/* choose t distinct indices of D on the largest level sets; returns the
 * number of level sets used */
static int pattern_positions(int pat, int t, int *et)
{
    static int idx[MAX_POINTS];
    static Grp grp[MAX_POINTS];
    int ng = 0, n = 0, used = 0;

    lv_val = malloc(sizeof(uint16_t) * nD);
    for (uint32_t d = 0; d < nD; ++d) {
        lv_val[d] = level_value(pat, dlist[d]);
        idx[d] = (int)d;
    }
    qsort(idx, nD, sizeof(int), cmp_idx);
    for (uint32_t a = 0; a < nD; ++a) {
        if (a == 0 || lv_val[idx[a]] != lv_val[idx[a - 1]]) {
            grp[ng].start = (int)a;
            grp[ng].size = 0;
            grp[ng].key = rnd();
            ++ng;
        }
        ++grp[ng - 1].size;
    }
    qsort(grp, (size_t)ng, sizeof(Grp), cmp_grp);
    for (int g = 0; g < ng && n < t; ++g, ++used)
        for (int q = 0; q < grp[g].size && n < t; ++q)
            et[n++] = idx[grp[g].start + q];
    free(lv_val);
    (void)lv_cur;
    return used;
}

static int experiment_decode(int m, int t, int ntr, int ci, int cj, int pat)
{
    int cls = ci >= 0, extra = cls ? 8 : 0, mp = m + extra;
    int N = (int)nD + extra, k, dstar, tmaxtot, success = 0, sumR = 0,
        sumv = 0, gaps = 0, minm = 1 << 30, found8 = 0;
    int *pos = malloc(sizeof(int) * (size_t)N);
    uint16_t *r = malloc(sizeof(uint16_t) * (size_t)N);
    uint16_t *cw = malloc(sizeof(uint16_t) * nD);
    uint16_t *ev = malloc(sizeof(uint16_t) * nD);
    int *et = malloc(sizeof(int) * (size_t)(t > 0 ? t : 1));
    Div G = div_inf(m);
    Code C;
    FRRes *res = malloc(sizeof *res);

    if (cls) {
        G.pos[G.npos++] = resq[ci];
        G.neg[G.nneg++] = resq[cj];
    }
    if (nb_upto(mp) >= nbasis - 1) {
        fprintf(stderr, "m too large for RMAX = %d\n", RMAX);
        return EXIT_FAILURE;
    }
    if (fr_setup() != 0)
        return EXIT_FAILURE;
    for (int s = 0; s <= 2 * GENUS; ++s)
        if (idx_of_rho[s] < 0)
            ++gaps;
    k = code_from_div(&G, &C);
    if (k != m + 1 - GENUS) {
        fprintf(stderr, "unexpected dimension %d\n", k);
        return EXIT_FAILURE;
    }
    dstar = fr_dstar(mp);
    tmaxtot = (dstar - 1) / 2;

    printf("# Feng-Rao majority voting; semigroup gaps = %d (genus %d), "
           "decomposition self-check: %s\n", gaps, GENUS,
           fr_selfcheck() == 0 ? "OK" : "FAILED");
    if (cls)
        printf("# decoding the dual of C_L(D, G_%d%d), G = %d P_inf + Q_%d - "
               "Q_%d: [%u, %u]; parity checks = rows of C_L(D,G) (k = %d)\n",
               ci, cj, m, ci, cj, nD, nD - (unsigned)k, k);
    else
        printf("# decoding the dual of C_L(D, %d P_inf): [%u, %u]; parity "
               "checks f_0..f_%d (k = %d)\n", m, nD, nD - (unsigned)k, k - 1, k);
    printf("# one-point code with m' = %d%s: Feng-Rao bound d* = %d, "
           "radius tmax = %d%s\n", mp,
           cls ? " (= m + 8, the 8 points of S8 count as errors)" : "", dstar,
           tmaxtot, cls ? " (errors in D + 8)" : "");
    printf("# error pattern: %s\n", pat == 0 ? "random positions" :
           pat == 1 ? "level sets of x (fibres)" :
           pat == 2 ? "level sets of y" : pat == 3 ? "level sets of z" :
           "level sets of w");
    if (t + extra > tmaxtot)
        printf("# warning: t = %d (+%d) exceeds the guaranteed radius; the "
               "decoder may fail\n", t, extra);

    for (uint32_t d = 0; d < nD; ++d)
        pos[d] = (int)dlist[d];
    if (cls) {
        for (int q = 1; q < 8; ++q)
            pos[nD + q - 1] = first_of_x[resx[ci]] + q;
        pos[nD + 7] = resq[cj];
    }

    for (int tr = 0; tr < ntr; ++tr) {
        int rc, ok = 1, nfd = 0, hit8 = 0;
        uint16_t *A = malloc(sizeof(uint16_t) * (size_t)k * (size_t)(k + 1));

        /* random code word c of C_L(D,G)^perp: random vector, then fix k
         * coordinates (the pivot columns of C_L(D,G)) to make all parity
         * checks vanish */
        for (uint32_t d = 0; d < nD; ++d)
            cw[d] = (uint16_t)(rnd() & (FIELD_SIZE - 1));
        for (int a = 0; a < k; ++a) {
            uint16_t sg = 0;
            for (uint32_t d = 0; d < nD; ++d)
                sg ^= gf_mul(cw[d], C.rows[a][d]);
            for (int b = 0; b < k; ++b)
                A[(size_t)a * (k + 1) + b] = C.rows[a][C.ech.piv[b]];
            A[(size_t)a * (k + 1) + k] = sg;
        }
        if (gj_solve(A, k, k + 1, k) != k) {
            fprintf(stderr, "code word construction failed\n");
            return EXIT_FAILURE;
        }
        for (int b = 0; b < k; ++b)
            cw[C.ech.piv[b]] ^= A[(size_t)b * (k + 1) + k];
        free(A);
        for (int a = 0; a < k; ++a) {
            uint16_t sg = 0;
            for (uint32_t d = 0; d < nD; ++d)
                sg ^= gf_mul(cw[d], C.rows[a][d]);
            if (sg != 0)
                ok = 0;
        }
        if (!ok) {
            fprintf(stderr, "internal error: not a code word\n");
            return EXIT_FAILURE;
        }

        /* t random errors */
        memset(ev, 0, sizeof(uint16_t) * nD);
        if (pat == 0) {
            for (int q = 0; q < t; ++q) {
                uint32_t d;
                int dup;
                do {
                    d = (uint32_t)(rnd() % nD);
                    dup = ev[d] != 0;
                } while (dup);
                ev[d] = (uint16_t)(1 + rnd() % FIELD_ORDER);
                et[q] = (int)d;
            }
        } else {
            pattern_positions(pat, t, et);
            for (int q = 0; q < t; ++q)
                ev[et[q]] = (uint16_t)(1 + rnd() % FIELD_ORDER);
        }
        for (uint32_t d = 0; d < nD; ++d) {
            uint16_t v = (uint16_t)(cw[d] ^ ev[d]);
            if (cls)
                v = gf_mul(v, gf_inv((uint16_t)(pts[dlist[d]].x ^ resx[ci])));
            r[d] = v;
        }
        for (int q = 0; q < extra; ++q)
            r[nD + q] = 0;

        rc = fr_decode(pos, N, r, mp, tmaxtot, res);
        ok = rc == 0;
        if (ok) {
            /* compare with the true error vector (positions in D) */
            int nD_found = 0;
            for (int q = 0; q < res->nerr; ++q) {
                int p = res->p[q];
                if (p >= (int)nD) {
                    ++hit8;
                    continue;
                }
                uint16_t v = res->v[q];
                if (cls)
                    v = gf_mul(v, (uint16_t)(pts[dlist[p]].x ^ resx[ci]));
                if (ev[p] != v)
                    ok = 0;
                ++nD_found;
            }
            nfd = nD_found;
            if (nD_found != t)
                ok = 0;
        }
        printf("trial %2d: t=%d  %s  errors found in D: %d  S8 errors: %d  "
               "syndrome order R=%d  votes=%d  min margin=%d  "
               "A=L(%dP) dim %d, B=L(%dP) dim %d\n", tr, t,
               rc == 0 ? (ok ? "CORRECT " : "WRONG   ")
                       : (rc == -1 ? "FAIL(R) " : "FAIL(vote)"),
               nfd, hit8, res->R, res->nvotes,
               res->nvotes ? res->minmargin : 0, res->a, res->ra, res->b, res->cb);
        if (ok) {
            ++success;
            sumR += res->R;
            sumv += res->nvotes;
            found8 += hit8;
            if (res->nvotes && res->minmargin < minm)
                minm = res->minmargin;
        }
    }
    printf("# %d / %d decoded correctly", success, ntr);
    if (success)
        printf("; mean R = %.1f, mean voted syndromes = %.1f, smallest "
               "majority margin = %d%s", (double)sumR / success,
               (double)sumv / success, minm == (1 << 30) ? 0 : minm,
               cls ? "" : "");
    printf("\n");
    (void)found8;

    code_free(&C);
    free(pos); free(r); free(cw); free(ev); free(et); free(res);
    return success == ntr ? EXIT_SUCCESS : EXIT_FAILURE;
}

int main(int argc, char **argv)
{
    int m = 28, s = 5, m_set = 0, t = -1, ntr = 5, ci = -1, cj = -1, pat = 0, rc;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-m") == 0 && i + 1 < argc) {
            m = atoi(argv[++i]);
            m_set = 1;
        } else if (strcmp(argv[i], "-s") == 0 && i + 1 < argc)
            s = atoi(argv[++i]);
        else if (strcmp(argv[i], "-t") == 0 && i + 1 < argc)
            t = atoi(argv[++i]);
        else if (strcmp(argv[i], "-N") == 0 && i + 1 < argc)
            ntr = atoi(argv[++i]);
        else if (strcmp(argv[i], "-i") == 0 && i + 1 < argc)
            ci = atoi(argv[++i]);
        else if (strcmp(argv[i], "-j") == 0 && i + 1 < argc)
            cj = atoi(argv[++i]);
        else if (strcmp(argv[i], "-p") == 0 && i + 1 < argc)
            pat = atoi(argv[++i]);
        else if (strcmp(argv[i], "-R") == 0 && i + 1 < argc)
            fr_rmin = atoi(argv[++i]);
        else if (strcmp(argv[i], "-S") == 0 && i + 1 < argc)
            rng_state ^= (uint64_t)strtoull(argv[++i], NULL, 10) *
                         0x9E3779B97F4A7C15ULL;
        else {
            fprintf(stderr, "usage: %s [-m degree] [-s reserved fibres] "
                    "[-t errors [-N trials] [-i I -j J] [-p pattern] [-R min_order] [-S seed]]\n", argv[0]);
            return EXIT_FAILURE;
        }
    }
    if (t >= 0 && !m_set)
        m = 60;
    if (s < 2 || s > MAXRES || m < 2 * GENUS - 1 || m + 8 > RMAX) {
        fprintf(stderr, "need 2 <= s <= %d and %d <= m <= %d\n", MAXRES,
                2 * GENUS - 1, RMAX - 8);
        return EXIT_FAILURE;
    }
    if (pat < 0 || pat > 4) {
        fprintf(stderr, "-p must be 0..4\n");
        return EXIT_FAILURE;
    }
    if ((ci >= 0) != (cj >= 0) || (ci >= 0 && (ci >= s || cj >= s || ci == cj))) {
        fprintf(stderr, "-i and -j must be two different fibre numbers < s\n");
        return EXIT_FAILURE;
    }
    if (common_setup(s) != 0)
        return EXIT_FAILURE;

    if (t >= 0)
        rc = experiment_decode(m, t, ntr, ci, cj, pat);
    else
        rc = experiment_classes(m, s);

    for (int i = 0; i < nbasis; ++i)
        free(basis[i].val);
    return rc;
}