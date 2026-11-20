/*
 * Skorobogatov-Vladut (error-correcting pair) decoder for the duals of
 * multipoint codes on the Suzuki curve  y^8 + y = x^2 (x^8 + x)  over GF(2^12).
 *
 * Code:   C = C_L(D, G)^perp,   G = (M - r) P_inf + sum_{Q in T} Q   (deg G = M),
 *         D = all affine points outside s reserved fibres (n = 5888 - 8 s).
 *         [n, n - (M+1-g), >= M - 2g + 2],  g = 14.
 * Syndromes: s(h) = <r, h(D)> for h in L(G).
 *
 * Basic SV algorithm.  Split G = F + (G - F) and let A = L(F), B = L(G - F)
 * with deg F = tau + g, tau = floor((M - 3g + 1)/2); then A * B is inside
 * L(G) and for every t <= tau errors
 *   - the left kernel K of S[i][j] = s(a_i b_j) is  { a in A : a vanishes on
 *     the error positions }  (a * e is orthogonal to B, and d(B^perp) > t
 *     forces a * e = 0),
 *   - dim K >= dim A - t >= 1.
 * The error positions are among the common zeros of K in D.  If there are
 * more candidates than errors (only possible near t = tau) the error values
 * are obtained from the linear system  sum_k e_k h(P_k) = s(h), h in L(G).
 * F may carry some of the poles of G (option -F), which changes A and B
 * but not the radius.
 *
 * Cost: the syndrome matrix S has (tau+1) x (M - tau - 2g + 1) entries, each
 * a sum over the non-zero positions of r (simulation: received word = error
 * vector, c = 0, as in the other programs).
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o suzuki_sv suzuki_sv.c
 * Run:   ./suzuki_sv [-m M] [-R maxrho] [-s fibres] [-T mask] [-F mask] [-e errors] [seed]
 *   -m M      degree of G (default 200)
 *   -R maxrho  highest pole order used to build the basis (default RMAX)
 *   -s fibres reserved fibres (default 4); the points Q_0..Q_{s-1} may be
 *             used as simple poles of G
 *   -T mask   bit mask of the reserved points that are poles of G
 *             (default 0 = one-point code G = M P_inf)
 *   -F mask   poles of G that go to F instead of G - F (default 0)
 *   -e t      number of random errors (default tau)
 *   -DRMAX=n  highest pole order in the basis (default 1100)
 */

#ifndef RMAX
#define RMAX 1100
#endif

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

static int rr_space_at(const Div *G, uint16_t **rows, const uint32_t *pl,
                       uint32_t np)
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
            rows[t] = malloc(sizeof(uint16_t) * np);
            for (uint32_t i = 0; i < np; ++i) {
                uint32_t P = pl[i];
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

static int rr_space(const Div *G, uint16_t **rows)
{
    return rr_space_at(G, rows, dlist, nD);
}

/* E = A - B (cancelling common points); -1 if a coefficient is not in
 * {-1, 0, 1} */
static __attribute__((unused)) int div_diff(const Div *A, const Div *B, Div *E)
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
static __attribute__((unused)) int is_principal(const Div *E)
{
    int d = rr_space(E, NULL);
    return d < 0 ? -1 : d >= 1;
}


/* ------------------------------------------------------------------ */
/* helpers for the SV decoder                                          */
/* ------------------------------------------------------------------ */

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static Div div_inf(int a)
{
    Div d;

    memset(&d, 0, sizeof d);
    d.a = a;
    return d;
}

static void free_rows(uint16_t **rows, int k)
{
    for (int i = 0; i < k; ++i)
        free(rows[i]);
    free(rows);
}

/* left kernel {lam : lam^T S = 0} of the na x nb matrix S (rows i, cols j).
 * Returns the dimension; *ker receives dim vectors of length na.        */
static int left_kernel(uint16_t **S, int na, int nb, uint16_t ***ker)
{
    uint16_t **Mt = malloc((size_t)nb * sizeof *Mt);
    int *pivcol = malloc((size_t)nb * sizeof(int));
    int *lg = malloc((size_t)na * sizeof(int));
    char *ispiv = calloc((size_t)na, 1);
    int row = 0, dim = 0;

    for (int j = 0; j < nb; ++j) {
        Mt[j] = malloc(sizeof(uint16_t) * (size_t)na);
        for (int i = 0; i < na; ++i)
            Mt[j][i] = S[i][j];
    }
    for (int c = 0; c < na && row < nb; ++c) {
        int p = -1;
        for (int r = row; r < nb; ++r)
            if (Mt[r][c] != 0) { p = r; break; }
        if (p < 0)
            continue;
        uint16_t *tmp = Mt[p]; Mt[p] = Mt[row]; Mt[row] = tmp;
        uint16_t inv = gf_inv(Mt[row][c]);
        for (int k = c; k < na; ++k)
            Mt[row][k] = gf_mul(Mt[row][k], inv);
        for (int k = c; k < na; ++k)
            lg[k] = Mt[row][k] ? (int)glog[Mt[row][k]] : -1;
        for (int r = 0; r < nb; ++r) {
            uint16_t f = Mt[r][c];
            if (r == row || f == 0)
                continue;
            int lf = glog[f];
            uint16_t *dst = Mt[r];
            for (int k = c; k < na; ++k)
                if (lg[k] >= 0)
                    dst[k] ^= gexp[lf + lg[k]];
        }
        pivcol[row] = c;
        ispiv[c] = 1;
        ++row;
    }
    *ker = malloc((size_t)(na - row + 1) * sizeof **ker);
    for (int f = 0; f < na; ++f)
        if (!ispiv[f]) {
            uint16_t *v = calloc((size_t)na, sizeof(uint16_t));
            v[f] = 1;
            for (int r = 0; r < row; ++r)
                v[pivcol[r]] = Mt[r][f];
            (*ker)[dim++] = v;
        }
    for (int j = 0; j < nb; ++j)
        free(Mt[j]);
    free(Mt); free(pivcol); free(lg); free(ispiv);
    return dim;
}

int main(int argc, char **argv)
{
    int M = 200, maxrho = RMAX, s = 4, Tmask = 0, Fmask = 0, t = -1;
    unsigned seed = 12345u;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-m") == 0 && i + 1 < argc)
            M = atoi(argv[++i]);
        else if (strcmp(argv[i], "-R") == 0 && i + 1 < argc)
            maxrho = atoi(argv[++i]);
        else if (strcmp(argv[i], "-s") == 0 && i + 1 < argc)
            s = atoi(argv[++i]);
        else if (strcmp(argv[i], "-T") == 0 && i + 1 < argc)
            Tmask = atoi(argv[++i]);
        else if (strcmp(argv[i], "-F") == 0 && i + 1 < argc)
            Fmask = atoi(argv[++i]);
        else if (strcmp(argv[i], "-e") == 0 && i + 1 < argc)
            t = atoi(argv[++i]);
        else if (argv[i][0] != '-')
            seed = (unsigned)strtoul(argv[i], NULL, 10);
        else {
            fprintf(stderr, "usage: %s [-m M] [-R maxrho] [-s fibres] [-T mask] [-F mask] "
                    "[-e errors] [seed]\n", argv[0]);
            return EXIT_FAILURE;
        }
    }
    int r = __builtin_popcount((unsigned)Tmask);
    int nF = __builtin_popcount((unsigned)(Tmask & Fmask));
    int tau = (M - 3 * GENUS + 1) / 2;

    if (s < 1 || s > MAXRES || (Tmask >> s) != 0 || tau < 1 ||
        maxrho < 1 || maxrho > RMAX || M + 7 * r > maxrho - 8) {
        fprintf(stderr, "need 1 <= s <= %d, T inside the reserved points, "
                "M >= %d and M + 7r <= maxrho - 8 (maxrho <= %d)\n", MAXRES, 3 * GENUS + 1, RMAX);
        return EXIT_FAILURE;
    }
    if (t < 0)
        t = tau;

    if (gf_init() != 0 || enumerate_points() != 0 || build_basis(maxrho) != 0 ||
        setup_reserved(s) != 0) {
        fprintf(stderr, "setup failed\n");
        return EXIT_FAILURE;
    }
    if (t < 0 || t > (int)nD) {
        fprintf(stderr, "errors must be between 0 and n = %u\n", nD);
        return EXIT_FAILURE;
    }
    if (t > tau)
        printf("# note: %d errors is beyond the radius tau = %d; decoding may fail\n", t, tau);

    /* divisors: G = F + (G - F) */
    Div G = div_inf(M - r), FD, BD;
    int f = tau + GENUS - nF;
    FD = div_inf(f);
    BD = div_inf(M - r - f);
    for (int i = 0; i < s; ++i)
        if (Tmask >> i & 1) {
            G.pos[G.npos++] = resq[i];
            if (Fmask >> i & 1)
                FD.pos[FD.npos++] = resq[i];
            else
                BD.pos[BD.npos++] = resq[i];
        }
    if (f < 0 || BD.a < 0) {
        fprintf(stderr, "cannot split G with these masks\n");
        return EXIT_FAILURE;
    }

    printf("# Suzuki curve y^8 + y = x^2 (x^8 + x) over GF(2^12), genus %d, "
           "n = %u\n", GENUS, nD);
    printf("# code C = C_L(D,G)^perp,  G = %d P_inf", M - r);
    for (int i = 0; i < s; ++i)
        if (Tmask >> i & 1)
            printf(" + Q_%d", i);
    printf("   (deg G = %d)\n", M);
    printf("# C: [%u, %d, >=%d];  SV radius tau = %d\n", nD,
           (int)nD - (M + 1 - GENUS), M - 2 * GENUS + 2, tau);
    printf("# F = %d P_inf", f);
    for (int i = 0; i < s; ++i)
        if ((Tmask & Fmask) >> i & 1)
            printf(" + Q_%d", i);
    printf(" (deg %d),  G - F = %d P_inf", f + nF, BD.a);
    for (int i = 0; i < s; ++i)
        if ((Tmask & ~Fmask) >> i & 1)
            printf(" + Q_%d", i);
    printf(" (deg %d)\n", M - f - nF);

    double t0 = now();
    uint16_t **rowsA = malloc(sizeof(uint16_t *) * (size_t)(RMAX + 1));
    uint16_t **rowsB = malloc(sizeof(uint16_t *) * (size_t)(RMAX + 1));
    int la = rr_space(&FD, rowsA), lb = rr_space(&BD, rowsB);
    if (la < 0 || lb < 0) {
        fprintf(stderr, "Riemann-Roch routine failed\n");
        return EXIT_FAILURE;
    }
    printf("# dim A = l(F) = %d (> t),  dim B = l(G-F) = %d,  S is %d x %d\n",
           la, lb, la, lb);
    printf("# setup of A and B: %.3f s\n", now() - t0);

    /* ---- inject errors: received word = error vector ---- */
    static uint16_t rec[MAX_POINTS];
    static uint32_t tpos[MAX_POINTS];
    static uint16_t tval[MAX_POINTS];

    srand(seed);
    for (int e = 0; e < t; ++e) {
        uint32_t p;
        int dup;
        do {
            p = (uint32_t)rand() % nD;
            dup = 0;
            for (int k = 0; k < e; ++k)
                if (tpos[k] == p)
                    dup = 1;
        } while (dup);
        tpos[e] = p;
        do {
            rec[p] = (uint16_t)(rand() & (FIELD_SIZE - 1u));
        } while (rec[p] == 0);
        tval[e] = rec[p];
    }
    printf("# %d errors injected (seed %u)\n", t, seed);

    /* ---- decoder side: only rec is used from here ---- */
    uint32_t *nzi = malloc(sizeof(uint32_t) * nD);
    int nz = 0;
    for (uint32_t k = 0; k < nD; ++k)
        if (rec[k] != 0)
            nzi[nz++] = k;
    if (nz == 0) {
        puts("# no errors.");
        return EXIT_SUCCESS;
    }

    /* 1. syndrome matrix S[i][j] = s(a_i b_j) */
    t0 = now();
    uint16_t **S = malloc(sizeof(uint16_t *) * (size_t)la);
    uint16_t *Bt = malloc(sizeof(uint16_t) * (size_t)nz * (size_t)lb);
    for (int q = 0; q < nz; ++q)
        for (int j = 0; j < lb; ++j)
            Bt[(size_t)q * (size_t)lb + (size_t)j] = rowsB[j][nzi[q]];
    for (int i = 0; i < la; ++i) {
        S[i] = calloc((size_t)lb, sizeof(uint16_t));
        for (int q = 0; q < nz; ++q) {
            uint16_t u = gf_mul(rec[nzi[q]], rowsA[i][nzi[q]]);
            const uint16_t *brow = Bt + (size_t)q * (size_t)lb;
            if (u == 0)
                continue;
            int lu = glog[u];
            for (int j = 0; j < lb; ++j)
                if (brow[j] != 0)
                    S[i][j] ^= gexp[lu + glog[brow[j]]];
        }
    }
    double t_synd = now() - t0;

    /* 2. kernel K = left kernel of S  = { a in A vanishing on the errors } */
    t0 = now();
    uint16_t **ker;
    int dk = left_kernel(S, la, lb, &ker);
    double t_ker = now() - t0;
    printf("# kernel of S: dimension %d (>= dim A - t = %d)\n", dk, la - t);

    /* 3. common zeros of the kernel in D */
    t0 = now();
    uint32_t *Z = malloc(sizeof(uint32_t) * nD);
    int nZ = 0;
    if (dk > 0) {
        for (uint32_t k = 0; k < nD; ++k) {
            uint16_t acc = 0;
            for (int i = 0; i < la; ++i)
                if (ker[0][i] != 0)
                    acc ^= gf_mul(ker[0][i], rowsA[i][k]);
            if (acc == 0)
                Z[nZ++] = k;
        }
        for (int v = 1; v < dk && nZ > 0; ++v) {
            int keep = 0;
            for (int z = 0; z < nZ; ++z) {
                uint16_t acc = 0;
                for (int i = 0; i < la; ++i)
                    if (ker[v][i] != 0)
                        acc ^= gf_mul(ker[v][i], rowsA[i][Z[z]]);
                if (acc == 0)
                    Z[keep++] = Z[z];
            }
            nZ = keep;
        }
    }
    double t_zero = now() - t0;
    printf("# common zeros of the kernel in D: %d candidates\n", nZ);

    /* 4. error values on the candidates:  sum_z e_z h(P_z) = s(h),  h in L(G) */
    t0 = now();
    int nfound = 0, solved = 0;
    static uint32_t fpos[MAX_POINTS];
    static uint16_t fval[MAX_POINTS];
    if (nZ > 0) {
        uint32_t *plz = malloc(sizeof(uint32_t) * (size_t)nZ);
        uint32_t *pln = malloc(sizeof(uint32_t) * (size_t)nz);
        for (int z = 0; z < nZ; ++z)
            plz[z] = dlist[Z[z]];
        for (int q = 0; q < nz; ++q)
            pln[q] = dlist[nzi[q]];
        uint16_t **hz = malloc(sizeof(uint16_t *) * (size_t)(RMAX + 1));
        uint16_t **hn = malloc(sizeof(uint16_t *) * (size_t)(RMAX + 1));
        int kg = rr_space_at(&G, hz, plz, (uint32_t)nZ);
        rr_space_at(&G, hn, pln, (uint32_t)nz);
        int nc = nZ + 1;
        uint16_t **aug = malloc(sizeof(uint16_t *) * (size_t)kg);
        for (int a = 0; a < kg; ++a) {
            aug[a] = malloc(sizeof(uint16_t) * (size_t)nc);
            memcpy(aug[a], hz[a], sizeof(uint16_t) * (size_t)nZ);
            uint16_t sy = 0;                       /* s(h_a) */
            for (int q = 0; q < nz; ++q)
                sy ^= gf_mul(rec[nzi[q]], hn[a][q]);
            aug[a][nZ] = sy;
        }
        int ok = 1;
        for (int c = 0; c < nZ && ok; ++c) {
            int p = -1;
            for (int a = c; a < kg; ++a)
                if (aug[a][c] != 0) { p = a; break; }
            if (p < 0) { ok = 0; break; }          /* not determined */
            uint16_t *tmp = aug[p]; aug[p] = aug[c]; aug[c] = tmp;
            uint16_t inv = gf_inv(aug[c][c]);
            for (int k = c; k < nc; ++k)
                aug[c][k] = gf_mul(aug[c][k], inv);
            for (int a = 0; a < kg; ++a) {
                uint16_t ff = aug[a][c];
                if (a == c || ff == 0)
                    continue;
                for (int k = c; k < nc; ++k)
                    aug[a][k] ^= gf_mul(ff, aug[c][k]);
            }
        }
        for (int a = nZ; a < kg && ok; ++a)
            if (aug[a][nZ] != 0)
                ok = 0;                             /* inconsistent */
        if (ok) {
            solved = 1;
            for (int z = 0; z < nZ; ++z)
                if (aug[z][nZ] != 0) {
                    fpos[nfound] = Z[z];
                    fval[nfound] = aug[z][nZ];
                    ++nfound;
                }
        } else
            puts("# could not determine the error values.");
        for (int a = 0; a < kg; ++a)
            free(aug[a]);
        free(aug);
        free_rows(hz, kg);
        free_rows(hn, kg);
        free(plz); free(pln);
    }
    double t_val = now() - t0;

    /* 5. verification against the simulated truth */
    int same = 0;
    for (int a = 0; a < nfound; ++a)
        for (int e = 0; e < t; ++e)
            if (tpos[e] == fpos[a] && tval[e] == fval[a])
                ++same;
    int okall = solved && nfound == t && same == t;
    printf("# %d of %d errors recovered with the correct value, %d reported "
           "-> %s\n", same, t, nfound, okall ? "OK" : "MISMATCH");
    printf("# time: syndrome matrix %.3f s, kernel %.3f s, zero search %.3f s, "
           "error values %.3f s, total %.3f s\n", t_synd, t_ker, t_zero, t_val,
           t_synd + t_ker + t_zero + t_val);

    free_rows(rowsA, la);
    free_rows(rowsB, lb);
    for (int i = 0; i < la; ++i)
        free(S[i]);
    free(S); free(Bt); free(nzi); free(Z);
    for (int v = 0; v < dk; ++v)
        free(ker[v]);
    free(ker);
    for (int i = 0; i < nbasis; ++i)
        free(basis[i].val);
    return okall ? EXIT_SUCCESS : EXIT_FAILURE;
}