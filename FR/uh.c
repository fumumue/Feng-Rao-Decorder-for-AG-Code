/*
 * bbgs_decode.c -- BBGS-type plane curves F(X,Y)=0 over GF(2^m), m <= 11
 *
 *   * one-point codes at ANY rational place at infinity (non-monomial basis, found by
 *     exact Laurent expansions; no monomial basis needed), automatic choice of the best place
 *   * multi-point codes  D = sum m_Q Q  (Galois orbits of places, no field extension needed)
 *   * decoders on the same syndromes:  FR (basic, charpoly), BMS (Sakata),
 *     VOTE (BMS + Feng-Rao majority voting, t <= (M-2g+1)/2)   [one-point],
 *     BASIC (kernel of S(h_a f_b), t <= (deg G - 3g + 1)/2)    [multi-point]
 *
 * Build: cc -O2 -fopenmp -std=gnu11 -o bbgs_decode bbgs_decode.c    (-fopenmp optional)
 * Run:   ./bbgs_decode --help
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint16_t fe;

#define MAXB 1400            /* max number of basis functions (M+1)          */
#define MAXT 420             /* max number of errors                         */
#define MAXGEN 100           /* max generators of the ideal E                */
#define MAXGENUS 6800         /* max genus handled by the voting part         */
#define SGMAX (MAXB + MAXGENUS + 64)
#define MAXTERM 64
#define MAXEDGE 32
#define MAXORB 128

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ================= GF(2^m), m <= 11, tables ================= */
static int FM, FS, FO;
static unsigned FPOLY;
static fe *gexp, *glog;

static int gf_init(int m, unsigned poly)
{
    FM = m; FS = 1 << m; FO = FS - 1; FPOLY = poly;
    free(gexp); free(glog);
    gexp = malloc(sizeof(fe) * (2 * FO + 4));
    glog = malloc(sizeof(fe) * FS);
    unsigned x = 1;
    for (int i = 0; i < FO; ++i) {
        if (i > 0 && x == 1) return -1;
        gexp[i] = (fe)x; glog[x] = (fe)i;
        x <<= 1;
        if (x & (unsigned)FS) x ^= poly;
    }
    if (x != 1) return -1;
    for (int i = FO; i < 2 * FO + 4; ++i) gexp[i] = gexp[i - FO];
    glog[0] = 0;
    return 0;
}
static inline fe mul(fe a, fe b) { return (a && b) ? gexp[glog[a] + glog[b]] : 0; }
static inline fe inv(fe a) { return gexp[FO - glog[a]]; }
static fe gpow(fe a, long long n)
{
    if (n == 0) return 1;
    if (!a) return 0;
    long long e = n % FO; if (e < 0) e += FO;
    return gexp[(int)(((long long)glog[a] * e) % FO)];
}

/* ================= curve ================= */
static int T, TX[MAXTERM], TY[MAXTERM];
static fe TC[MAXTERM];
static int dx_deg;
static fe coef_at(int px, int py)
{
    for (int t = 0; t < T; ++t) if (TX[t] == px && TY[t] == py) return TC[t];
    return 0;
}
static int gcdi(int a, int b) { a = abs(a); b = abs(b); while (b) { int t = a % b; a = b; b = t; } return a; }
static void egcd(int a, int b, int *x, int *y)
{
    if (b == 0) { *x = (a >= 0) ? 1 : -1; *y = 0; return; }
    int x1, y1; egcd(b, a % b, &x1, &y1);
    *x = y1; *y = x1 - (a / b) * y1;
}
static long long cross(int ax, int ay, int bx, int by, int cx, int cy)
{
    return (long long)(bx - ax) * (cy - ay) - (long long)(by - ay) * (cx - ax);
}
static int hull(int *hx, int *hy)
{
    int idx[MAXTERM], n = T;
    for (int i = 0; i < n; i++) idx[i] = i;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
        if (TX[idx[j]] < TX[idx[i]] || (TX[idx[j]] == TX[idx[i]] && TY[idx[j]] < TY[idx[i]])) { int t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
    int h[2 * MAXTERM], k = 0;
    for (int i = 0; i < n; i++) {
        while (k >= 2 && cross(TX[h[k-2]], TY[h[k-2]], TX[h[k-1]], TY[h[k-1]], TX[idx[i]], TY[idx[i]]) <= 0) k--;
        h[k++] = idx[i];
    }
    for (int i = n - 2, t = k + 1; i >= 0; i--) {
        while (k >= t && cross(TX[h[k-2]], TY[h[k-2]], TX[h[k-1]], TY[h[k-1]], TX[idx[i]], TY[idx[i]]) <= 0) k--;
        h[k++] = idx[i];
    }
    k--;
    for (int i = 0; i < k; i++) { hx[i] = TX[h[i]]; hy[i] = TY[h[i]]; }
    return k;
}

typedef struct { int vx, vy, ex, ey, len, wx, wy, a, b, w0, inf; } Edge;
static Edge ed[MAXEDGE];
static int ne;

static int build_edges(void)       /* returns interior lattice points = genus (nondegenerate) */
{
    int hx[2 * MAXTERM], hy[2 * MAXTERM];
    int h = hull(hx, hy);
    if (h < 3) { fprintf(stderr, "Newton polygon is degenerate\n"); exit(1); }
    ne = h;
    long long A2 = 0; int B = 0;
    for (int k = 0; k < h; k++) {
        int k2 = (k + 1) % h;
        int dx = hx[k2] - hx[k], dy = hy[k2] - hy[k];
        int g = gcdi(dx, dy);
        Edge *e = &ed[k];
        e->vx = hx[k]; e->vy = hy[k]; e->len = g;
        e->ex = dx / g; e->ey = dy / g;
        e->wx = -e->ey; e->wy = e->ex;
        e->inf = (e->wx < 0 || e->wy < 0);
        int x, y; egcd(e->wx, e->wy, &x, &y);
        e->a = x; e->b = y;
        if (e->wx * e->a + e->wy * e->b != 1) { e->a = -e->a; e->b = -e->b; }
        e->w0 = e->wx * e->vx + e->wy * e->vy;
        A2 += (long long)hx[k] * hy[k2] - (long long)hx[k2] * hy[k];
        B += g;
    }
    if (A2 < 0) A2 = -A2;
    return (int)((A2 - B + 2) / 2);
}

/* ================= polynomials over GF(2^m) (small degree) ================= */
typedef struct { int deg; fe c[16]; } Poly;
static void ptrim(Poly *p) { while (p->deg > 0 && p->c[p->deg] == 0) p->deg--; }
static fe peval(const Poly *p, fe x) { fe acc = 0; for (int i = p->deg; i >= 0; --i) acc = (fe)(mul(acc, x) ^ p->c[i]); return acc; }
static void pmod(Poly *a, const Poly *b)         /* a mod b, b monic or not */
{
    fe ib = inv(b->c[b->deg]);
    while (a->deg >= b->deg && !(a->deg == 0 && a->c[0] == 0)) {
        fe f = mul(a->c[a->deg], ib);
        int sh = a->deg - b->deg;
        for (int i = 0; i <= b->deg; ++i) a->c[i + sh] ^= mul(f, b->c[i]);
        a->c[a->deg] = 0;
        if (a->deg == 0) break;
        a->deg--;
        ptrim(a);
        if (a->deg < b->deg) break;
    }
}
static Poly pdiv_exact(const Poly *a, const Poly *b)   /* assumes b | a */
{
    Poly r = *a, q; memset(&q, 0, sizeof q);
    q.deg = a->deg - b->deg;
    fe ib = inv(b->c[b->deg]);
    for (int i = q.deg; i >= 0; --i) {
        fe f = mul(r.c[i + b->deg], ib);
        q.c[i] = f;
        for (int j = 0; j <= b->deg; ++j) r.c[i + j] ^= mul(f, b->c[j]);
    }
    return q;
}
static int pdivides(const Poly *b, const Poly *a)
{
    Poly r = *a;
    if (a->deg < b->deg) return 0;
    pmod(&r, b);
    for (int i = 0; i <= r.deg; ++i) if (r.c[i]) return 0;
    return 1;
}
static Poly pmonic(Poly p) { fe i = inv(p.c[p.deg]); for (int k = 0; k <= p.deg; ++k) p.c[k] = mul(p.c[k], i); return p; }

/* ================= places = Galois orbits of places at infinity ================= */
typedef struct {
    int edge, wx, wy, a, b, w0;
    int d;                 /* degree of the orbit (size of the Galois orbit) */
    fe p[8];               /* monic irreducible factor, p[0..d-1] (p[d] = 1) */
    int mult;
    int sigval;            /* index of root among the orbit list (for printing) */
} Place;
static Place pl[MAXORB];
static int np;

/* split the edge polynomial of edge k into irreducible factors over GF(2^m) */
static int split_edge(int k, Poly *facs)
{
    Edge *e = &ed[k];
    Poly Q; memset(&Q, 0, sizeof Q);
    Q.deg = e->len;
    for (int t = 0; t <= e->len; ++t)
        Q.c[e->len - t] = coef_at(e->vx + t * e->ex, e->vy + t * e->ey);
    ptrim(&Q);
    if (Q.deg != e->len || Q.c[0] == 0) { fprintf(stderr, "edge polynomial has a zero end coefficient\n"); exit(1); }
    Q = pmonic(Q);
    /* squarefree check: Q' = sum_{j odd} c_j x^{j-1};  gcd(Q,Q') = 1 */
    {
        Poly D; memset(&D, 0, sizeof D);
        for (int j = 1; j <= Q.deg; j += 2) D.c[j - 1] = Q.c[j];
        D.deg = Q.deg - 1; ptrim(&D);
        int allzero = 1; for (int i = 0; i <= D.deg; ++i) if (D.c[i]) allzero = 0;
        if (allzero) { fprintf(stderr, "edge %d: polynomial is a p-th power (degenerate)\n", k); exit(1); }
        Poly A = Q, B2 = D;
        while (!(B2.deg == 0 && B2.c[0] == 0)) {
            Poly Rr = A; pmod(&Rr, &B2);
            A = B2; B2 = Rr;
            int z = 1; for (int i = 0; i <= B2.deg; ++i) if (B2.c[i]) z = 0;
            if (z) break;
        }
        if (A.deg > 0) { fprintf(stderr, "edge %d: repeated factor (curve is degenerate)\n", k); exit(1); }
    }
    int nf = 0;
    /* linear factors */
    for (int x = 0; x < FS; ++x) if (peval(&Q, (fe)x) == 0) {
        Poly L; memset(&L, 0, sizeof L); L.deg = 1; L.c[1] = 1; L.c[0] = (fe)x;
        facs[nf++] = L;
        Poly q = pdiv_exact(&Q, &L); Q = q;
    }
    /* quadratic factors */
    if (Q.deg >= 4) {
        for (int a = 0; a < FS && Q.deg >= 4; ++a)
            for (int b = 1; b < FS && Q.deg >= 4; ++b) {
                Poly Qd; memset(&Qd, 0, sizeof Qd); Qd.deg = 2; Qd.c[2] = 1; Qd.c[1] = (fe)a; Qd.c[0] = (fe)b;
                if (pdivides(&Qd, &Q)) { facs[nf++] = Qd; Poly q = pdiv_exact(&Q, &Qd); Q = q; }
            }
    }
    if (Q.deg > 5) { fprintf(stderr, "edge %d: irreducible factor of degree > 5 not supported\n", k); exit(1); }
    if (Q.deg >= 1) facs[nf++] = Q;
    return nf;
}

static int ne_inf_orbits(void)
{
    np = 0;
    for (int k = 0; k < ne; ++k) {
        if (!ed[k].inf) continue;
        Poly facs[16];
        int nf = split_edge(k, facs);
        for (int f = 0; f < nf; ++f) {
            if (np >= MAXORB) { fprintf(stderr, "too many places\n"); exit(1); }
            Place *P = &pl[np++];
            P->edge = k; P->wx = ed[k].wx; P->wy = ed[k].wy; P->a = ed[k].a; P->b = ed[k].b; P->w0 = ed[k].w0;
            P->d = facs[f].deg; P->mult = 0;
            for (int i = 0; i < 8; ++i) P->p[i] = (i <= facs[f].deg) ? facs[f].c[i] : 0;
        }
    }
    return np;
}

/* ================= ring K_d = GF(2^m)[theta]/(p) and Laurent series over it ================= */
static int KD;
static fe KP[8];
static uint64_t KQD;     /* q^d */

static void k_setup(const Place *P)
{
    KD = P->d;
    for (int i = 0; i < 8; ++i) KP[i] = P->p[i];
    KQD = 1; for (int i = 0; i < KD; ++i) KQD *= (uint64_t)FS;
}
static inline void k_mul_acc(fe *dst, const fe *a, const fe *b)
{
    if (KD == 1) { dst[0] ^= mul(a[0], b[0]); return; }
    fe t[16] = {0};
    for (int i = 0; i < KD; ++i) if (a[i]) for (int j = 0; j < KD; ++j) if (b[j]) t[i + j] ^= mul(a[i], b[j]);
    for (int k = 2 * KD - 2; k >= KD; --k) {
        fe c = t[k]; if (!c) continue;
        for (int l = 0; l < KD; ++l) t[k - KD + l] ^= mul(c, KP[l]);
        t[k] = 0;
    }
    for (int i = 0; i < KD; ++i) dst[i] ^= t[i];
}
static void k_mul(fe *dst, const fe *a, const fe *b) { for (int i = 0; i < KD; ++i) dst[i] = 0; k_mul_acc(dst, a, b); }
static int k_zero(const fe *a) { for (int i = 0; i < KD; ++i) if (a[i]) return 0; return 1; }
static void k_pow_u64(fe *out, const fe *a, uint64_t n)
{
    fe res[8] = {0}, base[8], tmp[8];
    res[0] = 1; for (int i = 0; i < KD; ++i) base[i] = a[i];
    while (n) {
        if (n & 1) { k_mul(tmp, res, base); for (int i = 0; i < KD; ++i) res[i] = tmp[i]; }
        n >>= 1;
        if (n) { k_mul(tmp, base, base); for (int i = 0; i < KD; ++i) base[i] = tmp[i]; }
    }
    for (int i = 0; i < KD; ++i) out[i] = res[i];
}
static void k_inv(fe *out, const fe *a)
{
    if (KD == 1) { out[0] = inv(a[0]); return; }
    k_pow_u64(out, a, KQD - 2);
}

#define SC(arr, t) ((arr) + (size_t)(t) * KD)

static void s_mul(const fe *a, const fe *b, fe *r, int n)
{
    memset(r, 0, (size_t)n * KD * sizeof(fe));
    if (KD == 1) {
        for (int i = 0; i < n; i++) {
            if (!a[i]) continue;
            int la = glog[a[i]];
            for (int j = 0; i + j < n; j++) if (b[j]) r[i + j] ^= gexp[la + glog[b[j]]];
        }
        return;
    }
    for (int i = 0; i < n; i++) {
        const fe *ai = SC(a, i);
        if (k_zero(ai)) continue;
        for (int j = 0; i + j < n; j++) {
            const fe *bj = SC(b, j);
            if (k_zero(bj)) continue;
            k_mul_acc(SC(r, i + j), ai, bj);
        }
    }
}
static void s_inv(const fe *a, fe *r, int n)
{
    fe i0[8];
    k_inv(i0, a);
    for (int i = 0; i < KD; ++i) SC(r, 0)[i] = i0[i];
    for (int k = 1; k < n; k++) {
        fe s[8] = {0};
        for (int j = 1; j <= k; j++) {
            const fe *aj = SC(a, j), *rk = SC(r, k - j);
            if (k_zero(aj) || k_zero(rk)) continue;
            k_mul_acc(s, aj, rk);
        }
        k_mul(SC(r, k), s, i0);
    }
}
static void s_pow(const fe *a, long long r, int n, fe *out)
{
    size_t sz = (size_t)n * KD;
    fe *base = malloc(sz * sizeof(fe)), *res = calloc(sz, sizeof(fe)), *tmp = malloc(sz * sizeof(fe));
    if (r < 0) { s_inv(a, base, n); r = -r; } else memcpy(base, a, sz * sizeof(fe));
    res[0] = 1;
    while (r) {
        if (r & 1) { s_mul(res, base, tmp, n); memcpy(res, tmp, sz * sizeof(fe)); }
        r >>= 1;
        if (r) { s_mul(base, base, tmp, n); memcpy(base, tmp, sz * sizeof(fe)); }
    }
    memcpy(out, res, sz * sizeof(fe));
    free(base); free(res); free(tmp);
}

static fe *compute_sigma(const Place *P, int N)
{
    size_t sz = (size_t)N * KD;
    fe *sg = calloc(sz, sizeof(fe)), *G = malloc(sz * sizeof(fe)), *Gs = malloc(sz * sizeof(fe));
    fe *pr = malloc(sz * sizeof(fe)), *iv = malloc(sz * sizeof(fe)), *dl = malloc(sz * sizeof(fe));
    if (KD == 1) sg[0] = P->p[0]; else sg[1] = 1;       /* root of the factor: theta (or -p0 = p0) */
    int iters = 1; while ((1 << iters) < N) iters++;
    iters += 2;
    for (int it = 0; it <= iters; it++) {
        memset(G, 0, sz * sizeof(fe)); memset(Gs, 0, sz * sizeof(fe));
        for (int t = 0; t < T; t++) {
            int sh = P->wx * TX[t] + P->wy * TY[t] - P->w0;
            int r = -P->b * TX[t] + P->a * TY[t];
            if (sh >= N) continue;
            s_pow(sg, r, N, pr);
            for (int k = 0; k + sh < N; k++) for (int c = 0; c < KD; c++) SC(G, k + sh)[c] ^= mul(TC[t], SC(pr, k)[c]);
            if (r & 1) {
                s_pow(sg, r - 1, N, pr);
                for (int k = 0; k + sh < N; k++) for (int c = 0; c < KD; c++) SC(Gs, k + sh)[c] ^= mul(TC[t], SC(pr, k)[c]);
            }
        }
        if (it == iters) {
            for (size_t k = 0; k < sz; k++) if (G[k]) { fprintf(stderr, "Newton iteration did not converge\n"); exit(1); }
            break;
        }
        if (k_zero(Gs)) { fprintf(stderr, "multiple root of the edge polynomial\n"); exit(1); }
        s_inv(Gs, iv, N); s_mul(G, iv, dl, N);
        for (size_t k = 0; k < sz; k++) sg[k] ^= dl[k];
    }
    free(G); free(Gs); free(pr); free(iv); free(dl);
    return sg;
}

typedef struct { int vmin, N, rmin, rmax; fe *pw; } PSer;

static void place_series(const Place *P, int ehi, int J, PSer *S)
{
    k_setup(P);
    int c[4] = { 0, P->wx * (dx_deg - 1), P->wy * J, P->wx * (dx_deg - 1) + P->wy * J };
    int vmin = c[0]; for (int i = 1; i < 4; i++) if (c[i] < vmin) vmin = c[i];
    int rc[4] = { 0, -P->b * (dx_deg - 1), P->a * J, -P->b * (dx_deg - 1) + P->a * J };
    int rmin = rc[0], rmax = rc[0];
    for (int i = 1; i < 4; i++) { if (rc[i] < rmin) rmin = rc[i]; if (rc[i] > rmax) rmax = rc[i]; }
    S->vmin = vmin; S->rmin = rmin; S->rmax = rmax;
    int N = ehi - vmin + 1;
    S->N = N > 0 ? N : 0; S->pw = NULL;
    if (N <= 0) return;
    size_t sz = (size_t)N * KD;
    fe *sg = compute_sigma(P, N), *si = malloc(sz * sizeof(fe));
    s_inv(sg, si, N);
    int R = rmax - rmin + 1;
    S->pw = calloc((size_t)R * sz, sizeof(fe));
    fe *z = S->pw + (size_t)(0 - rmin) * sz; z[0] = 1;
    for (int r = 1; r <= rmax; r++) s_mul(S->pw + (size_t)(r - 1 - rmin) * sz, sg, S->pw + (size_t)(r - rmin) * sz, N);
    for (int r = -1; r >= rmin; r--) s_mul(S->pw + (size_t)(r + 1 - rmin) * sz, si, S->pw + (size_t)(r - rmin) * sz, N);
    free(sg); free(si);
}

/* ================= L(D): D supported on places at infinity ================= */
typedef struct { int dim, K, J; fe *B; } LSp;

static int genus_g;

static int solve_L(const int *mult, int Jfix, int Jstep, int Jmax, int verbose, LSp *out)
{
    int degD = 0, maxm = 0;
    for (int q = 0; q < np; q++) { degD += mult[q] * pl[q].d; if (mult[q] > maxm) maxm = mult[q]; }
    int certifiable = degD >= 2 * genus_g - 1, expected = degD - genus_g + 1;
    int J = (Jfix >= 0) ? Jfix : (maxm / 4 + 16);
    if (J < 8) J = 8;
    fe *Bv = NULL; int dim = 0, K = 0, lastdim = -1, stable = 0;
    for (;;) {
        K = dx_deg * (J + 1);
        int ehi_q[MAXORB]; PSer S[MAXORB]; size_t E = 0;
        for (int q = 0; q < np; q++) {
            ehi_q[q] = -mult[q] - 1;
            place_series(&pl[q], ehi_q[q], J, &S[q]);
            E += (size_t)S[q].N * pl[q].d;
        }
        if ((double)E * K > 9e8) { fprintf(stderr, "matrix too large (E=%zu, K=%d)\n", E, K); exit(1); }
        fe *Mx = calloc(E * K ? E * K : 1, sizeof(fe));
        size_t off = 0;
        for (int q = 0; q < np; q++) {
            int d = pl[q].d;
            if (S[q].N > 0) {
                size_t sz = (size_t)S[q].N * d;
                for (int j = 0; j <= J; j++) for (int i = 0; i < dx_deg; i++) {
                    int col = j * dx_deg + i;
                    int v = pl[q].wx * i + pl[q].wy * j, r = -pl[q].b * i + pl[q].a * j;
                    const fe *pw = S[q].pw + (size_t)(r - S[q].rmin) * sz;
                    for (int t = 0; v + t <= ehi_q[q]; t++)
                        for (int k = 0; k < d; k++) {
                            size_t row = off + (size_t)(v + t - S[q].vmin) * d + k;
                            Mx[row * K + col] = pw[(size_t)t * d + k];
                        }
                }
            }
            off += (size_t)S[q].N * d;
            free(S[q].pw);
        }
        int *pc = malloc(sizeof(int) * (K + 1)); size_t rk = 0;
        int *lr = malloc(sizeof(int) * K);
        fe *tmprow = malloc(sizeof(fe) * K);
        for (int c = 0; c < K && rk < E; c++) {
            size_t p = rk; while (p < E && !Mx[p * K + c]) p++;
            if (p == E) continue;
            if (p != rk) { memcpy(tmprow, Mx + p * K, K * sizeof(fe)); memcpy(Mx + p * K, Mx + rk * K, K * sizeof(fe)); memcpy(Mx + rk * K, tmprow, K * sizeof(fe)); }
            fe *R = Mx + rk * K; fe iv = inv(R[c]);
            for (int col = c; col < K; col++) R[col] = mul(R[col], iv);
            for (int col = c; col < K; col++) lr[col] = R[col] ? glog[R[col]] : -1;
#pragma omp parallel for schedule(static)
            for (long long ii = (long long)rk + 1; ii < (long long)E; ii++) {
                fe *Dr = Mx + (size_t)ii * K; fe f = Dr[c];
                if (!f) continue;
                int lf = glog[f];
                for (int col = c; col < K; col++) { int x = lr[col]; if (x >= 0) Dr[col] ^= gexp[lf + x]; }
            }
            pc[rk++] = c;
        }
        char *isp = calloc(K, 1);
        for (size_t i = 0; i < rk; i++) isp[pc[i]] = 1;
        dim = K - (int)rk;
        free(Bv); Bv = calloc((size_t)(dim ? dim : 1) * K, sizeof(fe));
        int bi = 0;
        for (int f = 0; f < K; f++) {
            if (isp[f]) continue;
            fe *x = Bv + (size_t)bi * K;
            x[f] = 1;
            for (long long i = (long long)rk - 1; i >= 0; i--) {
                int c = pc[i]; const fe *R = Mx + (size_t)i * K; fe s = 0;
                for (int col = c + 1; col < K; col++) if (R[col] && x[col]) s ^= mul(R[col], x[col]);
                x[c] = s;
            }
            bi++;
        }
        free(Mx); free(pc); free(lr); free(tmprow); free(isp);
        if (verbose) { printf("#   J=%d: unknowns %d, equations %zu, dim L(D) = %d", J, K, E, dim);
            if (certifiable) printf("  (Riemann-Roch: %d)", expected);
            printf("\n"); fflush(stdout); }
        if (Jfix >= 0) break;
        if (certifiable) {
            if (dim == expected) break;
            if (dim > expected) { fprintf(stderr, "dimension exceeds Riemann-Roch: curve assumptions violated\n"); break; }
        } else {
            if (dim == lastdim) { stable++; if (stable >= 2) break; } else stable = 0;
            lastdim = dim;
        }
        if (J >= Jmax) { fprintf(stderr, "warning: Jmax reached, basis may be incomplete\n"); break; }
        int deficit = certifiable ? expected - dim : 0;
        int st = Jstep; if (certifiable && deficit / 6 + 1 > st) st = deficit / 6 + 1;
        J += st; if (J > Jmax) J = Jmax;
    }
    out->dim = dim; out->K = K; out->J = J; out->B = Bv;
    if (certifiable && dim != expected) return -1;
    return 0;
}

/* ================= points ================= */
static int npts;
static fe *PXv, *PYv;

static void enumerate_points(void)
{
    int cap = 1024; npts = 0;
    PXv = malloc(sizeof(fe) * cap); PYv = malloc(sizeof(fe) * cap);
    fe *ypw = malloc(sizeof(fe) * (size_t)T * FS);
    for (int t = 0; t < T; ++t) for (int y = 0; y < FS; ++y) ypw[(size_t)t * FS + y] = gpow((fe)y, TY[t]);
    for (int x = 0; x < FS; ++x) {
        fe xp[MAXTERM];
        for (int t = 0; t < T; ++t) xp[t] = mul(TC[t], gpow((fe)x, TX[t]));
        for (int y = 0; y < FS; ++y) {
            fe acc = 0;
            for (int t = 0; t < T; ++t) acc ^= mul(xp[t], ypw[(size_t)t * FS + y]);
            if (!acc) {
                if (npts == cap) { cap *= 2; PXv = realloc(PXv, sizeof(fe) * cap); PYv = realloc(PYv, sizeof(fe) * cap); }
                PXv[npts] = (fe)x; PYv[npts] = (fe)y; npts++;
            }
        }
    }
    free(ypw);
}

/* evaluation matrix: out[d*npts + p] = (d-th basis vector of L)(P_p) */
static fe *eval_space(const LSp *L)
{
    int dim = L->dim, K = L->K, J = L->J;
    fe *out = malloc(sizeof(fe) * (size_t)(dim ? dim : 1) * npts);
    uint16_t *LB = malloc(sizeof(uint16_t) * (size_t)(dim ? dim : 1) * K);
    for (size_t i = 0; i < (size_t)dim * K; ++i) LB[i] = L->B[i] ? glog[L->B[i]] : 0xFFFF;
#pragma omp parallel
    {
        fe *xp = malloc(sizeof(fe) * dx_deg), *yp = malloc(sizeof(fe) * (J + 1));
        int *ml = malloc(sizeof(int) * K);
#pragma omp for schedule(static)
        for (int p = 0; p < npts; ++p) {
            xp[0] = 1; for (int i = 1; i < dx_deg; ++i) xp[i] = mul(xp[i - 1], PXv[p]);
            yp[0] = 1; for (int j = 1; j <= J; ++j) yp[j] = mul(yp[j - 1], PYv[p]);
            for (int c = 0; c < K; ++c) { fe v = mul(xp[c % dx_deg], yp[c / dx_deg]); ml[c] = v ? glog[v] : -1; }
            for (int d = 0; d < dim; ++d) {
                const uint16_t *lb = LB + (size_t)d * K; fe acc = 0;
                for (int c = 0; c < K; ++c) if (lb[c] != 0xFFFF && ml[c] >= 0) acc ^= gexp[lb[c] + ml[c]];
                out[(size_t)d * npts + p] = acc;
            }
        }
        free(xp); free(yp); free(ml);
    }
    free(LB);
    return out;
}

static fe dotv(const fe *a, const fe *b, int n)
{
    fe s = 0;
    for (int k = 0; k < n; ++k) if (a[k] && b[k]) s ^= gexp[glog[a[k]] + glog[b[k]]];
    return s;
}

/* nullspace of A (E x K) (A is destroyed); out: dim x K, identity on free columns */
static int nullspace_gf(fe *A, int E, int K, fe **out)
{
    int *pc = malloc(sizeof(int) * (K + 1)); int rk = 0;
    int *lr = malloc(sizeof(int) * K); fe *tmp = malloc(sizeof(fe) * K);
    for (int c = 0; c < K && rk < E; ++c) {
        int p = rk; while (p < E && !A[(size_t)p * K + c]) p++;
        if (p == E) continue;
        if (p != rk) { memcpy(tmp, A + (size_t)p * K, K * sizeof(fe)); memcpy(A + (size_t)p * K, A + (size_t)rk * K, K * sizeof(fe)); memcpy(A + (size_t)rk * K, tmp, K * sizeof(fe)); }
        fe *R = A + (size_t)rk * K; fe iv = inv(R[c]);
        for (int col = c; col < K; ++col) R[col] = mul(R[col], iv);
        for (int col = c; col < K; ++col) lr[col] = R[col] ? glog[R[col]] : -1;
#pragma omp parallel for schedule(static)
        for (int ii = rk + 1; ii < E; ++ii) {
            fe *Dr = A + (size_t)ii * K; fe f = Dr[c];
            if (!f) continue;
            int lf = glog[f];
            for (int col = c; col < K; ++col) { int x = lr[col]; if (x >= 0) Dr[col] ^= gexp[lf + x]; }
        }
        pc[rk++] = c;
    }
    char *isp = calloc(K, 1);
    for (int i = 0; i < rk; ++i) isp[pc[i]] = 1;
    int dim = K - rk;
    fe *B = calloc((size_t)(dim ? dim : 1) * K, sizeof(fe));
    int bi = 0;
    for (int f = 0; f < K; ++f) {
        if (isp[f]) continue;
        fe *x = B + (size_t)bi * K; x[f] = 1;
        for (int i = rk - 1; i >= 0; --i) {
            int c = pc[i]; const fe *R = A + (size_t)i * K; fe s = 0;
            for (int col = c + 1; col < K; ++col) if (R[col] && x[col]) s ^= mul(R[col], x[col]);
            x[c] = s;
        }
        bi++;
    }
    free(pc); free(lr); free(tmp); free(isp);
    *out = B;
    return dim;
}

/* right inverse: R (n x r) with U R = I_r, U is r x n of full row rank */
static int right_inverse(const fe *U, int r, int n, fe *R)
{
    int W = n + r;
    fe *Aug = calloc((size_t)r * W, sizeof(fe));
    for (int i = 0; i < r; ++i) { memcpy(Aug + (size_t)i * W, U + (size_t)i * n, n * sizeof(fe)); Aug[(size_t)i * W + n + i] = 1; }
    int *P = malloc(sizeof(int) * r); int rk = 0;
    int *lr = malloc(sizeof(int) * W);
    for (int c = 0; c < n && rk < r; ++c) {
        int p = rk; while (p < r && !Aug[(size_t)p * W + c]) p++;
        if (p == r) continue;
        if (p != rk) for (int k = 0; k < W; ++k) { fe t = Aug[(size_t)p * W + k]; Aug[(size_t)p * W + k] = Aug[(size_t)rk * W + k]; Aug[(size_t)rk * W + k] = t; }
        fe *Rw = Aug + (size_t)rk * W; fe iv = inv(Rw[c]);
        for (int k = c; k < W; ++k) Rw[k] = mul(Rw[k], iv);
        for (int k = c; k < W; ++k) lr[k] = Rw[k] ? glog[Rw[k]] : -1;
#pragma omp parallel for schedule(static)
        for (int ii = 0; ii < r; ++ii) {
            if (ii == rk) continue;
            fe *Dr = Aug + (size_t)ii * W; fe f = Dr[c];
            if (!f) continue;
            int lf = glog[f];
            for (int k = c; k < W; ++k) { int x = lr[k]; if (x >= 0) Dr[k] ^= gexp[lf + x]; }
        }
        P[rk++] = c;
    }
    if (rk < r) { free(Aug); free(P); free(lr); return -1; }
    memset(R, 0, sizeof(fe) * (size_t)n * r);
    for (int a = 0; a < r; ++a) for (int b = 0; b < r; ++b) R[(size_t)P[a] * r + b] = Aug[(size_t)a * W + n + b];
    free(Aug); free(P); free(lr);
    return 0;
}

/* ================= one-point echelon basis at a rational place ================= */
/* Turns the nullspace basis of L(mP) into functions f_s with pole order exactly s and
 * Laurent coefficient 1 at u^-s ("monic").  polev[d] = pole order of basis vector d
 * (0 for the constant).  Returns the number of constants (should be 1).              */
static int semigroup_echelon(LSp *L, const Place *P, int m, int *polev)
{
    int dim = L->dim, K = L->K, J = L->J;
    PSer S; place_series(P, -1, J, &S);
    fe *phi = calloc((size_t)dim * m, sizeof(fe));
#pragma omp parallel for schedule(static)
    for (int d = 0; d < dim; ++d) {
        const fe *b = L->B + (size_t)d * K;
        for (int col = 0; col < K; ++col) {
            fe x = b[col]; if (!x) continue;
            int j = col / dx_deg, i = col % dx_deg;
            int v = P->wx * i + P->wy * j, r = -P->b * i + P->a * j;
            const fe *pw = S.pw + (size_t)(r - S.rmin) * S.N;
            for (int s = 1; s <= m; ++s) {
                int t = -s - v;
                if (t < 0) continue;
                if (t >= S.N) break;
                fe cf = pw[t]; if (cf) phi[(size_t)d * m + s - 1] ^= mul(cf, x);
            }
        }
    }
    free(S.pw);
    char *used = calloc(dim, 1);
    for (int s = m; s >= 1; --s) {
        int p = -1;
        for (int d = 0; d < dim; ++d) if (!used[d] && phi[(size_t)d * m + s - 1]) { p = d; break; }
        if (p < 0) continue;
        fe iv = inv(phi[(size_t)p * m + s - 1]);
        for (int t = 0; t < m; ++t) phi[(size_t)p * m + t] = mul(phi[(size_t)p * m + t], iv);
        for (int c = 0; c < K; ++c) L->B[(size_t)p * K + c] = mul(L->B[(size_t)p * K + c], iv);
#pragma omp parallel for schedule(static)
        for (int d = 0; d < dim; ++d) {
            if (d == p || used[d]) continue;
            fe f = phi[(size_t)d * m + s - 1]; if (!f) continue;
            for (int t = 0; t < m; ++t) phi[(size_t)d * m + t] ^= mul(f, phi[(size_t)p * m + t]);
            for (int c = 0; c < K; ++c) L->B[(size_t)d * K + c] ^= mul(f, L->B[(size_t)p * K + c]);
        }
        used[p] = 1; polev[p] = s;
    }
    int nconst = 0;
    for (int d = 0; d < dim; ++d) if (!used[d]) { polev[d] = 0; nconst++; }
    free(phi); free(used);
    return nconst;
}

/* d_FR(M) = min { nu(s) : s > M, s in H },  nu(s) = #{(a,b) in H^2, a+b = s} */
static int dfr_of(const int *inH_arr, int M, int span)
{
    int best = 1 << 30;
    for (int s = M + 1; s <= M + span; ++s) {
        int c = 0;
        for (int a = 0; a <= s; ++a) if (inH_arr[a] && inH_arr[s - a]) c++;
        if (c < best) best = c;
    }
    return best;
}

/* ================================================================== */
/*  One-point decoders (generalised from the Suzuki version)           */
/* ================================================================== */
static int GENUS, M_SYND, M_EXT, TAU, TAU_V, L_DEG, ROW_MAX, ASHIFT, NUM_ERRORS;

typedef struct { int rho; fe *val; } Basis;
static Basis basis[MAXB];
static int nbasis;
static int in_H[SGMAX], idx_of_ord[SGMAX];
static int genH[MAXB], ngenH;

static int count_basis_upto(int rho)
{
    int n = 0;
    for (int i = 0; i < nbasis; ++i) if (basis[i].rho <= rho) ++n;
    return n;
}

static void init_semigroup(void)
{
    for (int x = 0; x < SGMAX; ++x) { in_H[x] = (x > M_EXT); idx_of_ord[x] = -1; }
    for (int i = 0; i < nbasis; ++i) { in_H[basis[i].rho] = 1; idx_of_ord[basis[i].rho] = i; }
    ngenH = 0;
    for (int s = 1; s <= M_EXT; ++s) {
        if (!in_H[s]) continue;
        int gen = 1;
        for (int a = 1; a <= s / 2 && gen; ++a) if (in_H[a] && in_H[s - a]) gen = 0;
        if (gen) genH[ngenH++] = s;
    }
}

/* ---- syndromes ---- */
static const fe *recv;
static int *nz_idx;
static int nz_cnt;

static fe synd(int ia, int ib, const fe *wt)
{
    fe acc = 0;
    for (int n = 0; n < nz_cnt; ++n) {
        int k = nz_idx[n];
        fe term = mul(recv[k], mul(basis[ia].val[k], basis[ib].val[k]));
        if (wt) term = mul(term, wt[k]);
        acc ^= term;
    }
    return acc;
}
static fe synd1(int ia)
{
    fe acc = 0;
    for (int n = 0; n < nz_cnt; ++n) acc ^= mul(recv[nz_idx[n]], basis[ia].val[nz_idx[n]]);
    return acc;
}

typedef struct {
    int T, nfound, resolved, overflow, failed;
    int pos[MAXT + 1];
    fe val[MAXT + 1];
    uint8_t rowset[SGMAX], colset[SGMAX];
    int vote_steps, vote_wrong, vote_tie, vote_min_margin;
    double t_main, t_extract, t_resolve;
} Result;
static Result res_fr, res_bms, res_vote;

static fe aug[MAXB][MAXT + 2];
static fe err_val[MAXT + 1];

static int resolve_by_values(int *found, int *nfound)
{
    int n = *nfound, m = count_basis_upto(M_SYND);
    if (n > MAXT) return 0;
    for (int a = 0; a < m; ++a) {
        for (int k = 0; k < n; ++k) aug[a][k] = basis[a].val[found[k]];
        aug[a][n] = synd1(a);
    }
    for (int c = 0; c < n; ++c) {
        int p = -1;
        for (int a = c; a < m; ++a) if (aug[a][c]) { p = a; break; }
        if (p < 0) return 0;
        if (p != c) for (int k = 0; k <= n; ++k) { fe t = aug[p][k]; aug[p][k] = aug[c][k]; aug[c][k] = t; }
        fe iv = inv(aug[c][c]);
        for (int k = c; k <= n; ++k) aug[c][k] = mul(aug[c][k], iv);
        for (int a = 0; a < m; ++a) {
            fe f = aug[a][c];
            if (a == c || !f) continue;
            for (int k = c; k <= n; ++k) aug[a][k] ^= mul(f, aug[c][k]);
        }
    }
    for (int a = n; a < m; ++a) if (aug[a][n]) return 0;
    int keep = 0;
    for (int k = 0; k < n; ++k) if (aug[k][n]) { found[keep] = found[k]; err_val[keep] = aug[k][n]; ++keep; }
    *nfound = keep;
    return 1;
}

static void resolve_and_store(Result *R)
{
    double t0 = now();
    int resolved = 0;
    if (!R->overflow && R->nfound > 0) {
        if (R->nfound > R->T) printf("#   %d common zeros > t = %d: resolving by error values\n", R->nfound, R->T);
        resolved = resolve_by_values(R->pos, &R->nfound);
        if (!resolved) puts("#   could not compute the error values.");
    }
    R->resolved = resolved;
    for (int m = 0; m < R->nfound; ++m) R->val[m] = resolved ? err_val[m] : 0;
    R->t_resolve = now() - t0;
}

/* ================= FR: basic algorithm + characteristic polynomial ================= */
static fe red[MAXB][MAXB];
static fe coefm[MAXB][MAXB];
static int piv_of_row[MAXB], row_of_col[MAXB];
static fe pivinv[MAXB];

static int feng_rao_reduce(void)
{
    int nrows = count_basis_upto(ROW_MAX);
    for (int j = 0; j < MAXB; ++j) row_of_col[j] = -1;
    for (int i = 0; i < nrows; ++i) {
        int ncol = count_basis_upto(M_SYND - basis[i].rho);
        for (int j = 0; j < ncol; ++j) red[i][j] = synd(i, j, NULL);
        memset(coefm[i], 0, sizeof(coefm[i]));
        coefm[i][i] = 1;
        piv_of_row[i] = -1;
        for (int j = 0; j < ncol; ++j) {
            fe v = red[i][j];
            if (!v) continue;
            int p = row_of_col[j];
            if (p >= 0) {
                fe f = mul(v, pivinv[p]);
                for (int jj = j; jj < ncol; ++jj) red[i][jj] ^= mul(f, red[p][jj]);
                for (int k = 0; k <= p; ++k) coefm[i][k] ^= mul(f, coefm[p][k]);
            } else {
                piv_of_row[i] = j; row_of_col[j] = i; pivinv[i] = inv(v);
                break;
            }
        }
    }
    return nrows;
}

typedef fe Mat[MAXT][MAXT];
static Mat S0, SX, S0inv, Qm, WORK;
static fe pol[MAXT + 1][MAXT + 1];

static int mat_inverse(Mat m, Mat out, int n)
{
    memcpy(WORK, m, sizeof(Mat));
    for (int i = 0; i < n; ++i) { for (int j = 0; j < n; ++j) out[i][j] = 0; out[i][i] = 1; }
    for (int c = 0; c < n; ++c) {
        int p = -1;
        for (int r = c; r < n; ++r) if (WORK[r][c]) { p = r; break; }
        if (p < 0) return 0;
        if (p != c) for (int i = 0; i < n; ++i) {
            fe t;
            t = WORK[p][i]; WORK[p][i] = WORK[c][i]; WORK[c][i] = t;
            t = out[p][i]; out[p][i] = out[c][i]; out[c][i] = t;
        }
        fe iv = inv(WORK[c][c]);
        for (int i = 0; i < n; ++i) { WORK[c][i] = mul(WORK[c][i], iv); out[c][i] = mul(out[c][i], iv); }
        for (int r = 0; r < n; ++r) {
            fe f = WORK[r][c];
            if (r == c || !f) continue;
            for (int i = 0; i < n; ++i) { WORK[r][i] ^= mul(f, WORK[c][i]); out[r][i] ^= mul(f, out[c][i]); }
        }
    }
    return 1;
}

static void charpoly(Mat H, int n, fe *g)
{
    for (int k = 0; k + 2 < n; ++k) {
        int p = -1;
        for (int i = k + 1; i < n; ++i) if (H[i][k]) { p = i; break; }
        if (p < 0) continue;
        if (p != k + 1) {
            for (int j = 0; j < n; ++j) { fe t = H[p][j]; H[p][j] = H[k + 1][j]; H[k + 1][j] = t; }
            for (int i = 0; i < n; ++i) { fe t = H[i][p]; H[i][p] = H[i][k + 1]; H[i][k + 1] = t; }
        }
        fe iv = inv(H[k + 1][k]);
        for (int i = k + 2; i < n; ++i) {
            if (!H[i][k]) continue;
            fe f = mul(H[i][k], iv);
            for (int j = 0; j < n; ++j) H[i][j] ^= mul(f, H[k + 1][j]);
            for (int r = 0; r < n; ++r) H[r][k + 1] ^= mul(f, H[r][i]);
        }
    }
    pol[0][0] = 1;
    for (int k = 1; k <= n; ++k) {
        fe prod = 1;
        for (int d = 0; d <= k; ++d) pol[k][d] = 0;
        for (int d = 0; d < k; ++d) { pol[k][d + 1] ^= pol[k - 1][d]; pol[k][d] ^= mul(H[k - 1][k - 1], pol[k - 1][d]); }
        for (int i = 1; i <= k - 1; ++i) {
            prod = mul(prod, H[k - i][k - i - 1]);
            if (!prod) break;
            fe c = mul(H[k - i - 1][k - 1], prod);
            if (!c) continue;
            for (int d = 0; d <= k - i - 1; ++d) pol[k][d] ^= mul(c, pol[k - i - 1][d]);
        }
    }
    for (int d = 0; d <= n; ++d) g[d] = pol[n][d];
}

static fe poly_eval(const fe *poly, int deg, fe t)
{
    fe acc = poly[deg];
    for (int i = deg - 1; i >= 0; --i) acc = (fe)(mul(acc, t) ^ poly[i]);
    return acc;
}

/* points grouped by the value of omega = basis[1] (the smallest non-constant function) */
static int *wstart, *wlist;
static void build_omega_buckets(void)
{
    free(wstart); free(wlist);
    wstart = calloc(FS + 2, sizeof(int)); wlist = malloc(sizeof(int) * npts);
    for (int k = 0; k < npts; ++k) wstart[basis[1].val[k] + 1]++;
    for (int v = 0; v < FS; ++v) wstart[v + 1] += wstart[v];
    int *fill = malloc(sizeof(int) * (FS + 1)); memcpy(fill, wstart, sizeof(int) * (FS + 1));
    for (int k = 0; k < npts; ++k) wlist[fill[basis[1].val[k]]++] = k;
    free(fill);
}

static int decode_fr(Result *R, int quiet)
{
    static int Rr[MAXT], Cc[MAXT];
    static fe g[MAXT + 1];
    fe *xv = calloc(npts, sizeof(fe));
    int T_ = 0, nl, nloc = 0;
    double t0 = now();

    memset(R, 0, sizeof *R);
    int nrows = feng_rao_reduce();
    nl = count_basis_upto(L_DEG);
    for (int i = 0; i < nl; ++i) if (piv_of_row[i] < 0) ++nloc;
    for (int i = 0; i < nrows; ++i) if (piv_of_row[i] >= 0) {
        if (T_ >= MAXT - 1) { fprintf(stderr, "FR: too many pivots\n"); R->failed = 1; free(xv); return -1; }
        Rr[T_] = i; Cc[T_] = piv_of_row[i];
        R->rowset[basis[i].rho] = 1; R->colset[basis[piv_of_row[i]].rho] = 1;
        ++T_;
    }
    R->T = T_;
    R->t_main = now() - t0;
    if (!quiet) {
        printf("# FR : %d error locators with rho <= %d\n", nloc, L_DEG);
        printf("# FR : staircase of %d elements -> estimated t = %d\n", T_, T_);
    }
    if (T_ == 0) { free(xv); return 0; }

    t0 = now();
    for (int a = 0; a < T_; ++a) for (int b = 0; b < T_; ++b)
        if (basis[Rr[a]].rho + basis[Cc[b]].rho + ASHIFT > M_SYND) {
            if (!quiet) puts("# FR : syndromes too short to form the shifted matrix.");
            R->failed = 1; free(xv); return -1;
        }
    for (int k = 0; k < nz_cnt; ++k) xv[nz_idx[k]] = basis[1].val[nz_idx[k]];
    for (int a = 0; a < T_; ++a) for (int b = 0; b < T_; ++b) {
        S0[a][b] = synd(Rr[a], Cc[b], NULL);
        SX[a][b] = synd(Rr[a], Cc[b], xv);
    }
    if (!mat_inverse(S0, S0inv, T_)) {
        if (!quiet) puts("# FR : S0 is singular (rank deficient).");
        R->failed = 1; free(xv); return -1;
    }
    for (int a = 0; a < T_; ++a) for (int b = 0; b < T_; ++b) {
        fe acc = 0;
        for (int k = 0; k < T_; ++k) acc ^= mul(S0inv[a][k], SX[k][b]);
        Qm[a][b] = acc;
    }
    charpoly(Qm, T_, g);
    int nfound = 0, overflow = 0, nroots = 0;
    for (int th = 0; th < FS; ++th) {
        if (poly_eval(g, T_, (fe)th) != 0) continue;
        nroots++;
        for (int q = wstart[th]; q < wstart[th + 1]; ++q) {
            int idx = wlist[q], vanish = 1;
            for (int i = 0; i < nl && vanish; ++i) {
                fe acc = 0;
                if (piv_of_row[i] >= 0) continue;
                for (int k = 0; k <= i; ++k) if (coefm[i][k]) acc ^= mul(coefm[i][k], basis[k].val[idx]);
                if (acc) vanish = 0;
            }
            if (vanish) { if (nfound < MAXT) R->pos[nfound++] = idx; else overflow = 1; }
        }
    }
    if (!quiet) printf("# FR : %d distinct roots (omega-values) in GF(2^%d)\n", nroots, FM);
    R->nfound = nfound; R->overflow = overflow;
    R->t_extract = now() - t0;
    resolve_and_store(R);
    free(xv);
    return 0;
}

/* ================= BMS (Sakata) with value vectors and majority voting ================= */
typedef struct { int b, d; fe *f; } Gen;
static Gen gens[MAXGEN];
static int ngen;
static fe *pivvec[SGMAX];
static fe pivd[SGMAX];
static uint8_t colused[SGMAX], is_piv[SGMAX];

static fe *vec_new(void)
{
    fe *v = malloc(sizeof(fe) * npts);
    if (!v) { fprintf(stderr, "out of memory\n"); exit(1); }
    return v;
}
static fe disc(const fe *f, int m)
{
    const fe *ph = basis[idx_of_ord[m]].val;
    fe acc = 0;
    for (int n = 0; n < nz_cnt; ++n) { int k = nz_idx[n]; acc ^= mul(recv[k], mul(f[k], ph[k])); }
    return acc;
}
static void vec_mul(fe *out, const fe *h, const fe *f) { for (int k = 0; k < npts; ++k) out[k] = mul(h[k], f[k]); }
static void vec_axpy(fe *f, fe c, const fe *p) { for (int k = 0; k < npts; ++k) f[k] ^= mul(c, p[k]); }

/* ---- majority voting machinery ---- */
static fe xhat[SGMAX];
static fe Bw[MAXGENUS][MAXB];
static int selp[MAXB];
static int nsel_dual;
static fe Aug[MAXB][MAXB + MAXGENUS];
static int lgrow[MAXB + MAXGENUS];

static int build_dual(void)
{
    int *perm = malloc(sizeof(int) * npts);
    static fe bsol[MAXB];
    const int NB = nbasis, W = NB + GENUS;
    unsigned seed = 12345u;
    if (NB != M_SYND + 1 || basis[NB - GENUS].rho != M_SYND + 1) { fprintf(stderr, "dual basis: unexpected basis layout (need M >= conductor)\n"); free(perm); return -1; }
    if (NB > npts) { fprintf(stderr, "dual basis: fewer points than basis functions\n"); free(perm); return -1; }
    for (int attempt = 0; attempt < 8; ++attempt) {
        int singular = 0;
        for (int i = 0; i < npts; ++i) perm[i] = i;
        for (int i = 0; i < NB; ++i) {
            seed = seed * 1664525u + 1013904223u;
            int j = i + (int)((seed >> 8) % (unsigned)(npts - i));
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            selp[i] = perm[i];
        }
        nsel_dual = NB;
        for (int j = 0; j < NB; ++j) {
            for (int p = 0; p < NB; ++p) Aug[j][p] = basis[j].val[selp[p]];
            for (int v = 0; v < GENUS; ++v) Aug[j][NB + v] = (j == NB - GENUS + v) ? 1 : 0;
        }
        for (int c = 0; c < NB && !singular; ++c) {
            int p = -1;
            for (int r = c; r < NB; ++r) if (Aug[r][c]) { p = r; break; }
            if (p < 0) { singular = 1; break; }
            if (p != c) for (int k = 0; k < W; ++k) { fe t = Aug[p][k]; Aug[p][k] = Aug[c][k]; Aug[c][k] = t; }
            fe iv = inv(Aug[c][c]);
            for (int k = c; k < W; ++k) Aug[c][k] = mul(Aug[c][k], iv);
            for (int k = c + 1; k < W; ++k) lgrow[k] = Aug[c][k] ? (int)glog[Aug[c][k]] : -1;
#pragma omp parallel for schedule(static)
            for (int r = c + 1; r < NB; ++r) {
                fe f = Aug[r][c]; fe *row = Aug[r];
                if (!f) continue;
                int lf = glog[f];
                for (int k = c + 1; k < W; ++k) if (lgrow[k] >= 0) row[k] ^= gexp[lf + lgrow[k]];
                row[c] = 0;
            }
        }
        if (singular) continue;
        for (int v = 0; v < GENUS; ++v) {
            for (int i = NB - 1; i >= 0; --i) {
                fe acc = Aug[i][NB + v];
                for (int k = i + 1; k < NB; ++k) if (Aug[i][k] && bsol[k]) acc ^= mul(Aug[i][k], bsol[k]);
                bsol[i] = acc;
            }
            for (int i = 0; i < NB; ++i) Bw[v][i] = bsol[i];
        }
        free(perm);
        return 0;
    }
    fprintf(stderr, "dual basis: evaluation matrix singular\n");
    free(perm);
    return -1;
}

static int dual_selftest(void)
{
    fe *coefv = malloc(sizeof(fe) * nbasis), *hs = malloc(sizeof(fe) * nbasis);
    for (int j = 0; j < nbasis; ++j) coefv[j] = (fe)(1 + rand() % FO);
    for (int p = 0; p < nsel_dual; ++p) {
        fe acc = 0;
        for (int j = 0; j < nbasis; ++j) acc ^= mul(coefv[j], basis[j].val[selp[p]]);
        hs[p] = acc;
    }
    int bad = 0;
    for (int v = 0; v < GENUS; ++v) {
        fe acc = 0;
        for (int p = 0; p < nsel_dual; ++p) acc ^= mul(Bw[v][p], hs[p]);
        if (acc != coefv[nbasis - GENUS + v]) bad = 1;
    }
    free(coefv); free(hs);
    return bad ? -1 : 0;
}

static fe ext_known(const fe *f, int m, int n, fe *an_out)
{
    static fe hsel[MAXB];
    fe a[MAXGENUS + 1];
    const fe *ph = basis[idx_of_ord[m]].val;
    const fe *top[MAXGENUS + 1];
    const int nv = n - M_SYND;
    fe s = 0;
    for (int p = 0; p < nsel_dual; ++p) { int k = selp[p]; hsel[p] = mul(f[k], ph[k]); }
    for (int v = 1; v <= nv; ++v) {
        fe acc = 0;
        for (int p = 0; p < nsel_dual; ++p) if (hsel[p] && Bw[v - 1][p]) acc ^= mul(hsel[p], Bw[v - 1][p]);
        a[v] = acc;
        top[v] = basis[idx_of_ord[M_SYND + v]].val;
    }
    for (int i = 0; i < nz_cnt; ++i) {
        int k = nz_idx[i];
        fe hv = mul(f[k], ph[k]);
        for (int v = 1; v <= nv; ++v) if (a[v]) hv ^= mul(a[v], top[v][k]);
        s ^= mul(recv[k], hv);
    }
    for (int v = 1; v < nv; ++v) if (a[v]) s ^= mul(a[v], xhat[M_SYND + v]);
    *an_out = a[nv];
    return s;
}
static fe xdisc(const fe *f, int m, int n)
{
    fe an, known;
    if (n <= M_SYND) return disc(f, m);
    known = ext_known(f, m, n, &an);
    return (fe)(known ^ mul(an, xhat[n]));
}
static fe true_syndrome(int n)
{
    const fe *ph = basis[idx_of_ord[n]].val;
    fe acc = 0;
    for (int i = 0; i < nz_cnt; ++i) acc ^= mul(recv[nz_idx[i]], ph[nz_idx[i]]);
    return acc;
}

static int vote_position(int n, Result *R, int verbose)
{
    fe pred[MAXGEN], dv[MAXGEN];
    int validg[MAXGEN], dc[MAXGEN], nd = 0, ncand = 0;
    for (int g = 0; g < ngen; ++g) {
        int m = n - gens[g].b;
        validg[g] = (m >= 0 && in_H[m]);
        if (validg[g]) {
            fe an, known = ext_known(gens[g].f, m, n, &an);
            if (!an) { fprintf(stderr, "vote: zero leading coefficient (n=%d)\n", n); return -1; }
            pred[g] = mul(known, inv(an));
        }
    }
    for (int i = 0; i <= n; ++i) {
        int j = n - i, anc = -1, s;
        if (!in_H[i] || is_piv[i] || !in_H[j] || colused[j]) continue;
        for (int g = 0; g < ngen; ++g) if (gens[g].b <= i && in_H[i - gens[g].b]) { anc = g; break; }
        if (anc < 0 || !validg[anc]) continue;
        ++ncand;
        for (s = 0; s < nd; ++s) if (dv[s] == pred[anc]) break;
        if (s == nd) { dv[nd] = pred[anc]; dc[nd] = 0; ++nd; }
        ++dc[s];
    }
    if (nd == 0) { fprintf(stderr, "vote: no candidates at n=%d\n", n); return -1; }
    int best = 0, second = 0;
    for (int s = 1; s < nd; ++s) if (dc[s] > dc[best]) best = s;
    for (int s = 0; s < nd; ++s) if (s != best && dc[s] > second) second = dc[s];
    xhat[n] = dv[best];
    int margin = dc[best] - second;
    ++R->vote_steps;
    if (margin < R->vote_min_margin) R->vote_min_margin = margin;
    if (margin <= 0) ++R->vote_tie;
    int right = true_syndrome(n) == xhat[n];
    if (!right) ++R->vote_wrong;
    if (verbose) printf("#   vote n=%d: %d candidates, %d predictions, winner %d votes, runner-up %d%s\n", n, ncand, nd, dc[best], second, right ? "  (= true syndrome)" : "  (WRONG)");
    return 0;
}

static void bms_cleanup(void)
{
    for (int g = 0; g < ngen; ++g) free(gens[g].f);
    ngen = 0;
    for (int m = 0; m < SGMAX; ++m) { free(pivvec[m]); pivvec[m] = NULL; }
}

static int bms_run(Result *R, int nmax, int verbose)
{
    int T_ = 0;
    memset(colused, 0, sizeof colused);
    memset(is_piv, 0, sizeof is_piv);
    memset(pivvec, 0, sizeof pivvec);
    ngen = 1; gens[0].b = 0; gens[0].d = 0; gens[0].f = vec_new();
    for (int k = 0; k < npts; ++k) gens[0].f[k] = 1;

    for (int n = 0; n <= nmax; ++n) {
        int anyfail = 0;
        if (n > M_SYND && vote_position(n, R, verbose) != 0) return -1;
        for (int g = 0; g < ngen; ++g) {
            int m = n - gens[g].b;
            gens[g].d = (m >= 0 && in_H[m]) ? xdisc(gens[g].f, m, n) : 0;
            if (gens[g].d) anyfail = 1;
        }
        if (!anyfail) continue;
        for (int a = 0; a <= n; ++a) {
            int m = n - a, src = -1;
            if (!in_H[a] || is_piv[a] || !in_H[m] || colused[m]) continue;
            for (int g = 0; g < ngen; ++g)
                if (gens[g].d && gens[g].b <= a && in_H[a - gens[g].b]) { src = g; break; }
            if (src < 0) continue;
            fe *f = vec_new();
            vec_mul(f, basis[idx_of_ord[a - gens[src].b]].val, gens[src].f);
            fe d = xdisc(f, m, n);
            if (!d) { fprintf(stderr, "BMS: internal error (zero pivot at n=%d)\n", n); free(f); return -1; }
            pivvec[m] = f; pivd[m] = d; colused[m] = 1; is_piv[a] = 1;
            R->rowset[a] = 1; R->colset[m] = 1; ++T_;
        }
        Gen ng[MAXGEN];
        uint8_t reused[MAXGEN];
        int nn = 0;
        memset(reused, 0, sizeof reused);
        for (int b = 0; b <= nmax; ++b) {
            int minimal = 1, og = -1;
            if (!in_H[b] || is_piv[b]) continue;
            for (int s = 0; s < ngenH; ++s)
                if (b - genH[s] >= 0 && in_H[b - genH[s]] && !is_piv[b - genH[s]]) { minimal = 0; break; }
            if (!minimal) continue;
            if (nn >= MAXGEN) { fprintf(stderr, "BMS: too many generators\n"); return -1; }
            for (int g = 0; g < ngen; ++g) if (gens[g].b == b) og = g;
            if (og >= 0) { ng[nn] = gens[og]; reused[og] = 1; }
            else {
                int src = -1, m = n - b;
                for (int g = 0; g < ngen; ++g) if (gens[g].b <= b && in_H[b - gens[g].b]) { src = g; break; }
                if (src < 0) { fprintf(stderr, "BMS: no source for generator %d\n", b); return -1; }
                ng[nn].b = b; ng[nn].f = vec_new();
                vec_mul(ng[nn].f, basis[idx_of_ord[b - gens[src].b]].val, gens[src].f);
                ng[nn].d = (m >= 0 && in_H[m]) ? xdisc(ng[nn].f, m, n) : 0;
            }
            {
                int m = n - ng[nn].b;
                if (m >= 0 && in_H[m] && ng[nn].d) {
                    if (!colused[m] || !pivvec[m]) { fprintf(stderr, "BMS: inconsistent state (n=%d, b=%d)\n", n, b); return -1; }
                    vec_axpy(ng[nn].f, mul(ng[nn].d, inv(pivd[m])), pivvec[m]);
                    ng[nn].d = 0;
                }
            }
            ++nn;
        }
        for (int g = 0; g < ngen; ++g) if (!reused[g]) free(gens[g].f);
        for (int g = 0; g < nn; ++g) gens[g] = ng[g];
        ngen = nn;
    }
    R->T = T_;
    return 0;
}

static int decode_bms(Result *R, int use_vote, int verbose, int quiet)
{
    const char *name = use_vote ? "VOTE" : "BMS";
    const int Mtop = use_vote ? M_EXT : M_SYND;
    double t0 = now();
    memset(R, 0, sizeof *R);
    R->vote_min_margin = 1 << 30;
    memset(xhat, 0, sizeof xhat);
    if (bms_run(R, Mtop, verbose) != 0) { R->failed = 1; bms_cleanup(); return -1; }
    R->t_main = now() - t0;
    int bmax = use_vote ? Mtop - 2 * GENUS + 1 - R->T : L_DEG;
    int nsel = 0, sel[MAXGEN];
    for (int g = 0; g < ngen; ++g) if (gens[g].b <= bmax) sel[nsel++] = g;
    if (!quiet) {
        printf("# %-4s: %d generators of E, %d with rho <= %d\n", name, ngen, nsel, bmax);
        printf("# %-4s: staircase of %d elements -> estimated t = %d\n", name, R->T, R->T);
        if (use_vote) printf("# %-4s: %d voted syndromes, smallest margin %d, %d wrong (vs. simulated truth), %d ties\n", name, R->vote_steps, R->vote_min_margin, R->vote_wrong, R->vote_tie);
    }
    if (R->T == 0) { bms_cleanup(); return 0; }
    t0 = now();
    int nfound = 0, overflow = 0;
    for (int k = 0; k < npts; ++k) {
        int vanish = nsel > 0;
        for (int s = 0; s < nsel && vanish; ++s) if (gens[sel[s]].f[k]) vanish = 0;
        if (vanish) { if (nfound < MAXT) R->pos[nfound++] = k; else overflow = 1; }
    }
    R->nfound = nfound; R->overflow = overflow;
    R->t_extract = now() - t0;
    bms_cleanup();
    resolve_and_store(R);
    return 0;
}

/* ---- error simulation / verification ---- */
static int true_pos[MAXT];
static fe true_val[MAXT];

static int verify(const char *name, const Result *R, int quiet)
{
    int same = 0;
    if (R->failed) { if (!quiet) printf("# %-5s FAILED\n", name); return 0; }
    for (int m = 0; m < R->nfound; ++m)
        for (int e = 0; e < NUM_ERRORS; ++e)
            if (true_pos[e] == R->pos[m] && true_val[e] == R->val[m]) ++same;
    int ok = !R->overflow && R->resolved && R->nfound == NUM_ERRORS && same == NUM_ERRORS;
    if (!quiet) printf("# %-5s %d of %d errors recovered with the correct value, %d reported -> %s\n", name, same, NUM_ERRORS, R->nfound, ok ? "OK" : "MISMATCH");
    return ok;
}
static double total_time(const Result *R) { return R->t_main + R->t_extract + R->t_resolve; }

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

/* draw NUM_ERRORS random errors; fills r (length npts), true_pos/true_val */
static void make_errors(fe *r)
{
    memset(r, 0, sizeof(fe) * npts);
    for (int e = 0; e < NUM_ERRORS; ++e) {
        int p, dup;
        do {
            p = (int)(rnd() % (uint64_t)npts); dup = 0;
            for (int k = 0; k < e; ++k) if (true_pos[k] == p) dup = 1;
        } while (dup);
        true_pos[e] = p;
        do { r[p] = (fe)(rnd() % (uint64_t)FS); } while (!r[p]);
        true_val[e] = r[p];
    }
}
static void set_received(fe *r)
{
    recv = r; nz_cnt = 0;
    for (int k = 0; k < npts; ++k) if (r[k]) nz_idx[nz_cnt++] = k;
}

/* ================================================================== */
/*  multi-point codes: basic algorithm  S(h_a f_b) = sum_k e_k h_a f_b */
/* ================================================================== */
static int solve_values(const fe *VG, int rG, const fe *sigma, const int *Z, int nz, fe *val)
{
    int W = nz + 1;
    fe *A = malloc(sizeof(fe) * (size_t)rG * W);
    for (int s = 0; s < rG; ++s) { for (int c = 0; c < nz; ++c) A[(size_t)s * W + c] = VG[(size_t)s * npts + Z[c]]; A[(size_t)s * W + nz] = sigma[s]; }
    for (int c = 0; c < nz; ++c) {
        int p = -1;
        for (int a = c; a < rG; ++a) if (A[(size_t)a * W + c]) { p = a; break; }
        if (p < 0) { free(A); return 0; }
        if (p != c) for (int k = 0; k < W; ++k) { fe t = A[(size_t)p * W + k]; A[(size_t)p * W + k] = A[(size_t)c * W + k]; A[(size_t)c * W + k] = t; }
        fe iv = inv(A[(size_t)c * W + c]);
        for (int k = c; k < W; ++k) A[(size_t)c * W + k] = mul(A[(size_t)c * W + k], iv);
#pragma omp parallel for schedule(static)
        for (int a = 0; a < rG; ++a) {
            fe f = A[(size_t)a * W + c];
            if (a == c || !f) continue;
            for (int k = c; k < W; ++k) A[(size_t)a * W + k] ^= mul(f, A[(size_t)c * W + k]);
        }
    }
    for (int a = nz; a < rG; ++a) if (A[(size_t)a * W + nz]) { free(A); return 0; }
    for (int c = 0; c < nz; ++c) val[c] = A[(size_t)c * W + nz];
    free(A);
    return 1;
}

static void usage(void)
{
    puts("bbgs_decode [options] [seed]\n"
         "  --m m            base field GF(2^m), m <= 11            (default 6)\n"
         "  --poly 0x43      primitive polynomial of GF(2^m)       (default: standard)\n"
         "  --q auto|2|4|8   BBGS family X^(q^2)+Y+X^(q^2-1)Y^q+X^(q^2-q)Y^(q^2); auto: q^3 = 2^m if m%3==0, else q=4\n"
         "  --terms \"16,0;0,1;15,4;12,16\"   any curve instead (monomials X^i Y^j, optionally \"i,j,coef\"); X-monic\n"
         "  --errors t       number of injected errors              (default 256)\n"
         "  --M M            syndrome bound / pole order (default 2t+2g)\n"
         "  --len L | -half  puncture: use only the first L points (or half of them) as positions\n"
         "  --place k        pole place (index from the list); default: automatic choice\n"
         "  --pole \"E2:140,E1:85\" or \"#3:100\"   multi-point divisor (E<k>: edge, #k: orbit)\n"
         "  -fr -bms -vote   one-point decoders to run (default: all)\n"
         "  -force           also run FR/BMS beyond the basic bound tau (they will usually fail)\n"
         "  -basic           (multi-point) basic algorithm\n"
         "  --place k        also avoids probing every candidate place (saves setup time)\n"
         "  -n N             N random trials (summary only)       -v  votes     -list  only list places");
}

int main(int argc, char **argv)
{
    const char *terms = "16,0;0,1;15,4;12,16", *polespec = NULL;
    int len_req = -1, half = 0, q_req = -1, terms_set = 0, m_bits = 6, Mreq = -1, place_req = -1, trials = 1, verbose = 0, only_list = 0, Jstep = 16, Jmax = 700;
    unsigned poly = 0, seed = 1;
    int run_fr = 1, run_bms = 1, run_vote = 1, only = 0, nerr = 256, force = 0;
    for (int i = 1; i < argc; ++i) {
        {   /* accept --force / --fr / --bms / --vote / --basic / --list as well as -force ... */
            static const char *flags[] = { "half", "force", "fr", "bms", "vote", "basic", "list", "v", NULL };
            if (argv[i][0] == '-' && argv[i][1] == '-')
                for (int f = 0; flags[f]; ++f) if (!strcmp(argv[i] + 2, flags[f])) { argv[i]++; break; }
        }
        if (!strcmp(argv[i], "--m") && i + 1 < argc) m_bits = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--poly") && i + 1 < argc) poly = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--terms") && i + 1 < argc) { terms = argv[++i]; terms_set = 1; }
        else if (!strcmp(argv[i], "--len") && i + 1 < argc) len_req = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--q") && i + 1 < argc) { ++i; q_req = strcmp(argv[i], "auto") ? atoi(argv[i]) : -1; }
        else if (!strcmp(argv[i], "--errors") && i + 1 < argc) nerr = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--M") && i + 1 < argc) Mreq = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--place") && i + 1 < argc) place_req = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--pole") && i + 1 < argc) polespec = argv[++i];
        else if (!strcmp(argv[i], "--Jstep") && i + 1 < argc) Jstep = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--Jmax") && i + 1 < argc) Jmax = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-n") && i + 1 < argc) trials = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-list")) only_list = 1;
        else if (!strcmp(argv[i], "-force")) force = 1;
        else if (!strcmp(argv[i], "-half")) half = 1;
        else if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) { usage(); return 0; }
        else if (!strcmp(argv[i], "-fr") || !strcmp(argv[i], "-bms") || !strcmp(argv[i], "-vote") || !strcmp(argv[i], "-basic")) {
            if (!only) run_fr = run_bms = run_vote = 0;
            only = 1;
            if (!strcmp(argv[i], "-fr")) run_fr = 1; else if (!strcmp(argv[i], "-bms")) run_bms = 1; else if (!strcmp(argv[i], "-vote")) run_vote = 1;
        } else if (argv[i][0] == '-') { fprintf(stderr, "unknown option: %s  (see --help)\n", argv[i]); return 1; }
        else seed = (unsigned)strtoul(argv[i], NULL, 10);
    }
    if (m_bits < 1 || m_bits > 11) { fprintf(stderr, "--m must be in 1..11\n"); return 1; }
    if (!poly) { static const unsigned dp[12] = { 0, 3, 7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D, 0x211, 0x409, 0x805 }; poly = dp[m_bits]; }
    if (gf_init(m_bits, poly) != 0) { fprintf(stderr, "polynomial 0x%X is not primitive of degree %d\n", poly, m_bits); return 1; }
    rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 8; ++i) rnd();
    srand(seed);

    /* ---- curve ---- */
    static char tbuf[128];
    int qfam = 0;
    if (!terms_set) {
        int q = q_req;
        if (q < 0) q = (m_bits % 3 == 0) ? (1 << (m_bits / 3)) : 4;
        if (q < 2 || (q & (q - 1))) { fprintf(stderr, "--q must be a power of 2 (>= 2)\n"); return 1; }
        snprintf(tbuf, sizeof tbuf, "%d,0;0,1;%d,%d;%d,%d", q * q, q * q - 1, q, q * q - q, q * q);
        terms = tbuf; qfam = q;
        if (q_req < 0 && m_bits % 3 == 0) printf("# q^3 = 2^%d  ->  q = %d: using the BBGS curve  X^%d + Y + X^%d Y^%d + X^%d Y^%d\n", m_bits, q, q * q, q * q - 1, q, q * q - q, q * q);
        else if (q_req < 0) printf("# 2^%d is not a cube: using the q = %d curve (give --q or --terms to change)\n", m_bits, q);
        else printf("# q = %d: curve  X^%d + Y + X^%d Y^%d + X^%d Y^%d\n", q, q * q, q * q - 1, q, q * q - q, q * q);
    }
    {
        char *s = strdup(terms), *tok = strtok(s, ";");
        while (tok) {
            int a, b, c = 1;
            int k = sscanf(tok, "%d,%d,%d", &a, &b, &c);
            if (k < 2) { fprintf(stderr, "--terms: \"i,j[,coef];...\"\n"); return 1; }
            if (c <= 0 || c >= FS) { fprintf(stderr, "coefficient out of range\n"); return 1; }
            TX[T] = a; TY[T] = b; TC[T] = (fe)c; T++;
            tok = strtok(NULL, ";");
        }
    }
    dx_deg = 0; for (int t = 0; t < T; ++t) if (TX[t] > dx_deg) dx_deg = TX[t];
    { int top = 0, pure = 0;
      for (int t = 0; t < T; ++t) if (TX[t] == dx_deg) { top++; if (TY[t] == 0) pure = 1; }
      if (top != 1 || !pure) { fprintf(stderr, "only curves that are monic in X are supported (swap X and Y in --terms)\n"); return 1; } }
    genus_g = build_edges();
    int ng_orb = ne_inf_orbits();
    GENUS = genus_g;
    double ts = now();
    enumerate_points();
    int nfull = npts;
    if (half) len_req = npts / 2;
    if (len_req > 0 && len_req < npts) npts = len_req;      /* puncturing: keep the first points only */
    printf("# curve over GF(2^%d) [poly 0x%X]: X-degree %d, genus g = %d, n = %d affine rational points\n", FM, FM ? poly : 0, dx_deg, genus_g, nfull);
    if (npts != nfull) printf("# punctured: only the first %d of %d points are used as code positions\n", npts, nfull);
    for (int k = 0; k < ne; ++k)
        printf("#   edge E%d: from (%d,%d) dir (%d,%d) length %d  w=(%d,%d) %s\n", k, ed[k].vx, ed[k].vy, ed[k].ex, ed[k].ey, ed[k].len, ed[k].wx, ed[k].wy, ed[k].inf ? "[infinity]" : "[affine side]");
    int nrat = 0, ratidx[MAXORB];
    for (int q = 0; q < ng_orb; ++q) {
        printf("#   place #%d: edge E%d, degree %d (%s)\n", q, pl[q].edge, pl[q].d, pl[q].d == 1 ? "rational" : "Galois orbit");
        if (pl[q].d == 1) ratidx[nrat++] = q;
    }
    if (qfam) {
        long long nopt = 1 + ((long long)qfam * qfam * qfam - 1) * qfam * qfam;
        if ((long long)qfam * qfam * qfam == (long long)FS)
            printf("# GF(2^%d) = GF(q^3): maximal-structure point count 1 + (q^3-1) q^2 = %lld, found n = %d%s\n", FM, nopt, nfull, nopt == nfull ? "  (matches)" : "  (differs)");
        else printf("# note: 2^%d != q^3, so the q = %d curve has no special point structure here\n", FM, qfam);
    }
    if (only_list) return 0;
    /*
    if (GENUS > MAXGENUS - 1 || 2 * GENUS + 2 > MAXB - GENUS) {
        fprintf(stderr, "# genus g = %d: decoding needs M >= 2g = %d syndromes (> this build's limit: g <= %d).\n"
                        "# The dense linear algebra of this program is not feasible at this size; -list works, decoding does not.\n", GENUS, 2 * GENUS, MAXGENUS - 1);
        return 1;
    }
    */
    
    NUM_ERRORS = nerr;
    if (nerr < 1 || nerr > MAXT - 2) { fprintf(stderr, "--errors out of range (1..%d)\n", MAXT - 2); return 1; }
    int mult[MAXORB]; memset(mult, 0, sizeof mult);

    /* ===================== choose the code ===================== */
    int multi = (polespec != NULL);
    if (!multi && nrat == 0) {
        multi = 1;
        printf("# no rational place at infinity: no one-point code with a pole at a rational point on this model.\n"
               "# fallback: multi-point divisor supported on the lowest-degree Galois orbit, decoded by the basic algorithm.\n");
    }
    if (multi) {
        /* ---------- multi-point: basic algorithm ---------- */
        int degG = 0;
        if (polespec) {
            char *s = strdup(polespec), *tok = strtok(s, ",");
            while (tok) {
                int id, mm;
                if (sscanf(tok, "E%d:%d", &id, &mm) == 2) {
                    if (id < 0 || id >= ne || !ed[id].inf) { fprintf(stderr, "E%d is not an edge at infinity\n", id); return 1; }
                    for (int q = 0; q < ng_orb; ++q) if (pl[q].edge == id) mult[q] = mm;
                } else if (sscanf(tok, "#%d:%d", &id, &mm) == 2) {
                    if (id < 0 || id >= ng_orb) { fprintf(stderr, "no place #%d\n", id); return 1; }
                    mult[id] = mm;
                } else { fprintf(stderr, "--pole: \"E1:10,#3:5\"\n"); return 1; }
                tok = strtok(NULL, ",");
            }
        } else {
            int best = 0;
            for (int q = 1; q < ng_orb; ++q) if (pl[q].d < pl[best].d) best = q;
            int need = 2 * nerr + 3 * GENUS + 4;
            mult[best] = (need + pl[best].d - 1) / pl[best].d;
        }
        for (int q = 0; q < ng_orb; ++q) degG += mult[q] * pl[q].d;
        int need = 2 * nerr + 3 * GENUS - 1;
        printf("# multi-point divisor G: deg G = %d, designed distance >= %d; basic algorithm needs deg G >= %d for t = %d\n", degG, degG - 2 * GENUS + 2, need, nerr);
        if (degG < need) { fprintf(stderr, "deg G too small for %d errors with the basic algorithm (tau = %d)\n", nerr, (degG - 3 * GENUS + 1) / 2); return 1; }
        /* split G = F + H with deg F >= t+g and deg H >= t+2g-1 */
        int lo = nerr + GENUS, hi = degG - nerr - 2 * GENUS + 1, target = (lo + hi) / 2;
        int fm[MAXORB], hm[MAXORB], degF = 0;
        for (int q = 0; q < ng_orb; ++q) { fm[q] = (int)(((long long)mult[q] * target + degG / 2) / degG); if (fm[q] > mult[q]) fm[q] = mult[q]; degF += fm[q] * pl[q].d; }
        for (int tries = 0; tries < 400 && (degF < lo || degF > hi); ++tries) {
            int q = tries % ng_orb;
            if (degF < lo && fm[q] < mult[q]) { fm[q]++; degF += pl[q].d; }
            else if (degF > hi && fm[q] > 0) { fm[q]--; degF -= pl[q].d; }
        }
        for (int q = 0; q < ng_orb; ++q) hm[q] = mult[q] - fm[q];
        if (degF < lo || degF > hi) { fprintf(stderr, "could not split G into F + H (deg F = %d, need %d..%d)\n", degF, lo, hi); return 1; }
        printf("# splitting G = F + H: deg F = %d (>= t+g = %d), deg H = %d (>= t+2g-1 = %d)\n", degF, lo, degG - degF, nerr + 2 * GENUS - 1);
        LSp LG, LF, LH;
        double t0 = now();
        if (solve_L(mult, -1, Jstep, Jmax, 0, &LG) != 0) fprintf(stderr, "warning: L(G) not certified\n");
        solve_L(fm, -1, Jstep, Jmax, 0, &LF);
        solve_L(hm, -1, Jstep, Jmax, 0, &LH);
        printf("# dim L(G) = %d, dim L(F) = %d, dim L(H) = %d  (%.2f s)\n", LG.dim, LF.dim, LH.dim, now() - t0);
        fe *VG = eval_space(&LG), *VF = eval_space(&LF), *VH = eval_space(&LH);
        int rG = LG.dim, dF = LF.dim, dH = LH.dim;
        fe *R0 = malloc(sizeof(fe) * (size_t)npts * rG);
        if (right_inverse(VG, rG, npts, R0) != 0) { fprintf(stderr, "evaluation of L(G) is not injective: deg G >= n?\n"); return 1; }
        printf("# code: n = %d, check rows = %d, k = %d, designed distance >= %d, setup %.2f s\n", npts, rG, npts - rG, degG - 2 * GENUS + 2, now() - ts);
        fe *r = malloc(sizeof(fe) * npts), *sigma = malloc(sizeof(fe) * rG), *estar = malloc(sizeof(fe) * npts);
        fe *Mt = malloc(sizeof(fe) * (size_t)dH * dF), *ae = malloc(sizeof(fe) * npts);
        int okc = 0;
        for (int tr = 0; tr < trials; ++tr) {
            make_errors(r);
            double t1 = now();
            for (int s = 0; s < rG; ++s) { fe acc = 0; for (int e = 0; e < NUM_ERRORS; ++e) acc ^= mul(true_val[e], VG[(size_t)s * npts + true_pos[e]]); sigma[s] = acc; }
            for (int k = 0; k < npts; ++k) { fe acc = 0; for (int s = 0; s < rG; ++s) if (sigma[s] && R0[(size_t)k * rG + s]) acc ^= mul(R0[(size_t)k * rG + s], sigma[s]); estar[k] = acc; }
            for (int a = 0; a < dF; ++a) {
                for (int k = 0; k < npts; ++k) ae[k] = mul(estar[k], VF[(size_t)a * npts + k]);
                for (int b = 0; b < dH; ++b) Mt[(size_t)b * dF + a] = dotv(ae, VH + (size_t)b * npts, npts);
            }
            fe *ker; int kd = nullspace_gf(Mt, dH, dF, &ker);
            int *Z = malloc(sizeof(int) * npts), nz = 0;
            for (int k = 0; k < npts; ++k) Z[nz++] = k;
            for (int v = 0; v < kd && nz > 0; ++v) {
                int nn = 0;
                for (int zi = 0; zi < nz; ++zi) {
                    int k = Z[zi]; fe acc = 0;
                    for (int a = 0; a < dF; ++a) if (ker[(size_t)v * dF + a]) acc ^= mul(ker[(size_t)v * dF + a], VF[(size_t)a * npts + k]);
                    if (!acc) Z[nn++] = k;
                }
                nz = nn;
            }
            free(ker);
            fe *val = malloc(sizeof(fe) * (nz + 1));
            int ok = 0, nfound = 0;
            if (nz > 0 && nz <= MAXT && solve_values(VG, rG, sigma, Z, nz, val)) {
                int same = 0;
                for (int c = 0; c < nz; ++c) if (val[c]) { nfound++; for (int e = 0; e < NUM_ERRORS; ++e) if (true_pos[e] == Z[c] && true_val[e] == val[c]) same++; }
                ok = (same == NUM_ERRORS && nfound == NUM_ERRORS);
            }
            okc += ok;
            if (trials == 1 || verbose)
                printf("# BASIC trial %d: %d kernel vectors of dim L(F) = %d, %d common zeros, %d errors reported -> %s (%.2f s)\n", tr + 1, kd, dF, nz, nfound, ok ? "OK" : "FAILED", now() - t1);
            free(Z); free(val);
        }
        printf("# BASIC: %d of %d trials decoded %d errors correctly\n", okc, trials, NUM_ERRORS);
        return okc == trials ? 0 : 1;
    }

    /* ---------- one-point codes ---------- */
    int M = (Mreq > 0) ? Mreq : 2 * nerr + 2 * GENUS;
    if (M < 2 * GENUS) M = 2 * GENUS;
    M_SYND = M; M_EXT = M + GENUS;
    TAU = (M - 3 * GENUS + 1) / 2; TAU_V = (M - 2 * GENUS + 1) / 2; L_DEG = TAU + GENUS;
    if (M_EXT + 1 > MAXB - 1) { fprintf(stderr, "M too large for this build\n"); return 1; }
    if (nerr > TAU_V) { fprintf(stderr, "%d errors exceed tau_vote = %d for M = %d (need M >= %d)\n", nerr, TAU_V, M, 2 * nerr + 2 * GENUS); return 1; }
    printf("# one-point code: M = %d, g = %d, basic algorithm t <= %d, with majority voting t <= %d\n", M, GENUS, TAU, TAU_V);
    if (npts <= M_EXT) {
        fprintf(stderr, "# the curve has only n = %d rational points, but M + g = %d >= n: the evaluation map is not injective.\n"
                        "# Use a larger field (--m) or a smaller M/number of errors (need n > M + g).\n", npts, M_EXT);
        return 1;
    }

    /* candidates = rational places; pick the best (largest d_FR, then smallest first pole) */
    LSp Lc[MAXORB]; int *pv[MAXORB];
    int best = -1, bestdfr = -1, besta = 1 << 30;
    int cand[MAXORB], ncand = 0;
    if (place_req >= 0) {
        if (place_req < ng_orb && pl[place_req].d == 1) cand[ncand++] = place_req;
        else printf("# requested place #%d is not a rational place at infinity -> searching for a substitute\n", place_req);
    }
    if (ncand == 0) for (int i = 0; i < nrat; ++i) cand[ncand++] = ratidx[i];
    printf("# candidate poles (rational places at infinity): %d\n", ncand);
    for (int ci = 0; ci < ncand; ++ci) {
        int q = cand[ci];
        int mm[MAXORB]; memset(mm, 0, sizeof mm); mm[q] = M_EXT;
        double t0 = now();
        if (solve_L(mm, -1, Jstep, Jmax, 0, &Lc[q]) != 0) { printf("#   place #%d: L(%dP) not certified, skipped\n", q, M_EXT); Lc[q].B = NULL; continue; }
        pv[q] = malloc(sizeof(int) * Lc[q].dim);
        int nconst = semigroup_echelon(&Lc[q], &pl[q], M_EXT, pv[q]);
        static int inHt[SGMAX]; memset(inHt, 0, sizeof inHt);
        for (int x = M_EXT + 1; x < SGMAX; ++x) inHt[x] = 1;
        for (int d = 0; d < Lc[q].dim; ++d) inHt[pv[q][d]] = 1;
        int ngaps = 0; for (int x = 1; x <= M_EXT; ++x) if (!inHt[x]) ngaps++;
        int a1 = 1 << 30; for (int x = 1; x <= M_EXT; ++x) if (inHt[x]) { a1 = x; break; }
        int span = SGMAX - M - 2; if (span > 400) span = 400;
        int dfr = dfr_of(inHt, M, span);
        printf("#   place #%d: first non-zero pole order %d, %d gaps (g = %d)%s, d_FR(M) = %d -> t = %d  (%.1f s)\n", q, a1, ngaps, GENUS, ngaps == GENUS && nconst == 1 ? "" : "  [semigroup check FAILED]", dfr, (dfr - 1) / 2, now() - t0);
        if (ngaps == GENUS && nconst == 1 && (dfr > bestdfr || (dfr == bestdfr && a1 < besta))) { best = q; bestdfr = dfr; besta = a1; }
    }
    if (best < 0) { fprintf(stderr, "no usable rational place for a one-point code\n"); return 1; }
    printf("# chosen pole: place #%d  (d_FR = %d, designed t = %d)\n", best, bestdfr, (bestdfr - 1) / 2);
    LSp *L = &Lc[best];
    fe *V = eval_space(L);
    {   /* basis sorted by pole order */
        int dim = L->dim; int *ord = malloc(sizeof(int) * dim);
        for (int i = 0; i < dim; ++i) ord[i] = i;
        for (int i = 1; i < dim; ++i) { int x = ord[i], j = i - 1; while (j >= 0 && pv[best][ord[j]] > pv[best][x]) { ord[j + 1] = ord[j]; j--; } ord[j + 1] = x; }
        nbasis = dim;
        for (int i = 0; i < dim; ++i) {
            basis[i].rho = pv[best][ord[i]];
            basis[i].val = malloc(sizeof(fe) * npts);
            if (i == 0) for (int k = 0; k < npts; ++k) basis[0].val[k] = 1;
            else memcpy(basis[i].val, V + (size_t)ord[i] * npts, sizeof(fe) * npts);
        }
        free(ord);
    }
    init_semigroup();
    ASHIFT = basis[1].rho; ROW_MAX = M_SYND - ASHIFT;
    build_omega_buckets();
    nz_idx = malloc(sizeof(int) * npts);
    printf("# setup (curve, places, basis up to M+g, evaluation): %.2f s;  semigroup has %d generators, smallest pole %d\n", now() - ts, ngenH, ASHIFT);
    if (run_vote) {
        double t0 = now();
        if (build_dual() != 0 || dual_selftest() != 0) { fprintf(stderr, "dual basis construction failed\n"); return 1; }
        printf("# setup (dual basis for the top g coefficients, once per code): %.2f s\n", now() - t0);
    }
    fe *r = malloc(sizeof(fe) * npts);
    int cnt_fr = 0, cnt_bms = 0, cnt_vote = 0;
    int quiet = trials > 1;
    for (int tr = 0; tr < trials; ++tr) {
        make_errors(r);
        set_received(r);
        if (!quiet) printf("# %d errors injected (seed %u)%s\n", NUM_ERRORS, seed, NUM_ERRORS > TAU ? "  -- beyond the basic bound" : "");
        if (force && NUM_ERRORS > TAU && !quiet) puts("# -force: running FR/BMS beyond their proven bound (expected to fail)");
        int okf = 1, okb = 1, okv = 1;
        if (run_fr) {
            if (NUM_ERRORS > TAU && !force) { okf = 0; if (!quiet) puts("# FR   skipped: beyond the basic bound"); }
            else { decode_fr(&res_fr, quiet); okf = verify("FR", &res_fr, quiet); cnt_fr += okf; }
        }
        if (run_bms) {
            if (NUM_ERRORS > TAU && !force) { okb = 0; if (!quiet) puts("# BMS  skipped: beyond the basic bound"); }
            else { decode_bms(&res_bms, 0, verbose, quiet); okb = verify("BMS", &res_bms, quiet); cnt_bms += okb; }
        }
        if (run_vote) { decode_bms(&res_vote, 1, verbose, quiet); okv = verify("VOTE", &res_vote, quiet); cnt_vote += okv; }
        if (!quiet) {
            if (run_fr && (NUM_ERRORS <= TAU || force)) printf("# time FR   : reduction %.3f s, charpoly+roots %.3f s, values %.3f s\n", res_fr.t_main, res_fr.t_extract, res_fr.t_resolve);
            if (run_bms && (NUM_ERRORS <= TAU || force)) printf("# time BMS  : loop %.3f s, scan %.3f s, values %.3f s\n", res_bms.t_main, res_bms.t_extract, res_bms.t_resolve);
            if (run_vote) printf("# time VOTE : BMS+voting %.3f s, scan %.3f s, values %.3f s\n", res_vote.t_main, res_vote.t_extract, res_vote.t_resolve);
            if (run_fr && run_vote && (NUM_ERRORS <= TAU || force) && !res_fr.failed) printf("# FR / VOTE time ratio: %.1f x\n", total_time(&res_fr) / total_time(&res_vote));
        } else {
            int bo = NUM_ERRORS <= TAU || force;
            printf("# trial %d: FR %s  BMS %s  VOTE %s\n", tr + 1, (run_fr && bo) ? (okf ? "ok" : "FAIL") : "n/a", (run_bms && bo) ? (okb ? "ok" : "FAIL") : "n/a", run_vote ? (okv ? "ok" : "FAIL") : "n/a");
        }
    }
    if (trials > 1) {
        char sf[32], sb[32], sv[32];
        int basic_ok = NUM_ERRORS <= TAU || force;
        if (run_fr && basic_ok) snprintf(sf, sizeof sf, "%d/%d", cnt_fr, trials); else snprintf(sf, sizeof sf, "n/a");
        if (run_bms && basic_ok) snprintf(sb, sizeof sb, "%d/%d", cnt_bms, trials); else snprintf(sb, sizeof sb, "n/a");
        if (run_vote) snprintf(sv, sizeof sv, "%d/%d", cnt_vote, trials); else snprintf(sv, sizeof sv, "n/a");
        printf("# summary of %d trials with %d errors: FR %s, BMS %s, VOTE %s  (n/a: not run or beyond its bound)\n", trials, NUM_ERRORS, sf, sb, sv);
    }
    return 0;
}