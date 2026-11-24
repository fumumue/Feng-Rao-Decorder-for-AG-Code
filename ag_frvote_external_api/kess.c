/*
 * ag_frvote.c -- one-point AG-code FR-VOTE for supported plane curves over GF(2^m)
 *
 *   * one-point codes at a rational place at infinity: the basis of L(MP) is
 * built from the NEWTON POLYGON (monomials x^i y^j = lattice points; no local
 * expansions, no linear algebra), certified by Riemann-Roch at run time; if
 * that does not apply (edge of lattice length > 1, ...) it falls back to exact
 * Laurent expansions (-nonewton forces the old path); automatic choice of the
 * best place
 *   * multi-point codes  D = sum m_Q Q  (Galois orbits of places, no field
 * extension needed)
 *   * decoders on the same syndromes:  FR (basic, charpoly), BMS (Sakata),
 *     VOTE (BMS + Feng-Rao majority voting, t <= (M-2g+1)/2)   [one-point],
 *     BASIC (kernel of S(h_a f_b), t <= (deg G - 3g + 1)/2)    [multi-point]
 *
 * Build: cc -O2 -fopenmp -std=gnu11 -o bbgs_decode bbgs_decode.c    (-fopenmp
 * optional) Run:   ./bbgs_decode --help
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint16_t fe;

#define MAXB 20000     /* max number of basis functions (M+1)          */
#define MAXT 3000      /* max number of errors                         */
#define MAXGEN 100    /* max generators of the ideal E                */
#define MAXGENUS 9000 /* max genus handled by the voting part         */
#define SGMAX (MAXB + MAXGENUS + 64)
#define MAXTERM 64
#define MAXEDGE 32
#define MAXORB 128

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ================= GF(2^m), m <= 11, tables ================= */
static int FM, FS, FO;
static unsigned FPOLY;
static fe *gexp, *glog;

static int gf_init(int m, unsigned poly) {
  FM = m;
  FS = 1 << m;
  FO = FS - 1;
  FPOLY = poly;
  free(gexp);
  free(glog);
  gexp = malloc(sizeof(fe) * (2 * FO + 4));
  glog = malloc(sizeof(fe) * FS);
  unsigned x = 1;
  for (int i = 0; i < FO; ++i) {
    if (i > 0 && x == 1)
      return -1;
    gexp[i] = (fe)x;
    glog[x] = (fe)i;
    x <<= 1;
    if (x & (unsigned)FS)
      x ^= poly;
  }
  if (x != 1)
    return -1;
  for (int i = FO; i < 2 * FO + 4; ++i)
    gexp[i] = gexp[i - FO];
  glog[0] = 0;
  return 0;
}
static inline fe mul(fe a, fe b) {
  return (a && b) ? gexp[glog[a] + glog[b]] : 0;
}
static inline fe inv(fe a) { return gexp[FO - glog[a]]; }
static fe gpow(fe a, long long n) {
  if (n == 0)
    return 1;
  if (!a)
    return 0;
  long long e = n % FO;
  if (e < 0)
    e += FO;
  return gexp[(int)(((long long)glog[a] * e) % FO)];
}

/* ================= curve ================= */
static int T, TX[MAXTERM], TY[MAXTERM];
static fe TC[MAXTERM];
static int dx_deg;
/* Nonzero only for the built-in Hermitian family. */
static int hermitian_q = 0;
static fe coef_at(int px, int py) {
  for (int t = 0; t < T; ++t)
    if (TX[t] == px && TY[t] == py)
      return TC[t];
  return 0;
}
static int gcdi(int a, int b) {
  a = abs(a);
  b = abs(b);
  while (b) {
    int t = a % b;
    a = b;
    b = t;
  }
  return a;
}
static void egcd(int a, int b, int *x, int *y) {
  if (b == 0) {
    *x = (a >= 0) ? 1 : -1;
    *y = 0;
    return;
  }
  int x1, y1;
  egcd(b, a % b, &x1, &y1);
  *x = y1;
  *y = x1 - (a / b) * y1;
}
static long long cross(int ax, int ay, int bx, int by, int cx, int cy) {
  return (long long)(bx - ax) * (cy - ay) - (long long)(by - ay) * (cx - ax);
}
static int hull(int *hx, int *hy) {
  int idx[MAXTERM], n = T;
  for (int i = 0; i < n; i++)
    idx[i] = i;
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      if (TX[idx[j]] < TX[idx[i]] ||
          (TX[idx[j]] == TX[idx[i]] && TY[idx[j]] < TY[idx[i]])) {
        int t = idx[i];
        idx[i] = idx[j];
        idx[j] = t;
      }
  int h[2 * MAXTERM], k = 0;
  for (int i = 0; i < n; i++) {
    while (k >= 2 && cross(TX[h[k - 2]], TY[h[k - 2]], TX[h[k - 1]],
                           TY[h[k - 1]], TX[idx[i]], TY[idx[i]]) <= 0)
      k--;
    h[k++] = idx[i];
  }
  for (int i = n - 2, t = k + 1; i >= 0; i--) {
    while (k >= t && cross(TX[h[k - 2]], TY[h[k - 2]], TX[h[k - 1]],
                           TY[h[k - 1]], TX[idx[i]], TY[idx[i]]) <= 0)
      k--;
    h[k++] = idx[i];
  }
  k--;
  for (int i = 0; i < k; i++) {
    hx[i] = TX[h[i]];
    hy[i] = TY[h[i]];
  }
  return k;
}

typedef struct {
  int vx, vy, ex, ey, len, wx, wy, a, b, w0, inf;
} Edge;
static Edge ed[MAXEDGE];
static int ne;

static int
build_edges(void) /* returns interior lattice points = genus (nondegenerate) */
{
  int hx[2 * MAXTERM], hy[2 * MAXTERM];
  int h = hull(hx, hy);
  if (h < 3) {
    fprintf(stderr, "Newton polygon is degenerate\n");
    exit(1);
  }
  ne = h;
  long long A2 = 0;
  int B = 0;
  for (int k = 0; k < h; k++) {
    int k2 = (k + 1) % h;
    int dx = hx[k2] - hx[k], dy = hy[k2] - hy[k];
    int g = gcdi(dx, dy);
    Edge *e = &ed[k];
    e->vx = hx[k];
    e->vy = hy[k];
    e->len = g;
    e->ex = dx / g;
    e->ey = dy / g;
    e->wx = -e->ey;
    e->wy = e->ex;
    e->inf = (e->wx < 0 || e->wy < 0);
    int x, y;
    egcd(e->wx, e->wy, &x, &y);
    e->a = x;
    e->b = y;
    if (e->wx * e->a + e->wy * e->b != 1) {
      e->a = -e->a;
      e->b = -e->b;
    }
    e->w0 = e->wx * e->vx + e->wy * e->vy;
    A2 += (long long)hx[k] * hy[k2] - (long long)hx[k2] * hy[k];
    B += g;
  }
  if (A2 < 0)
    A2 = -A2;
  return (int)((A2 - B + 2) / 2);
}

/* ================= polynomials over GF(2^m) (small degree) =================
 */
typedef struct {
  int deg;
  fe c[16];
} Poly;
static void ptrim(Poly *p) {
  while (p->deg > 0 && p->c[p->deg] == 0)
    p->deg--;
}
static fe peval(const Poly *p, fe x) {
  fe acc = 0;
  for (int i = p->deg; i >= 0; --i)
    acc = (fe)(mul(acc, x) ^ p->c[i]);
  return acc;
}
static void pmod(Poly *a, const Poly *b) /* a mod b, b monic or not */
{
  fe ib = inv(b->c[b->deg]);
  while (a->deg >= b->deg && !(a->deg == 0 && a->c[0] == 0)) {
    fe f = mul(a->c[a->deg], ib);
    int sh = a->deg - b->deg;
    for (int i = 0; i <= b->deg; ++i)
      a->c[i + sh] ^= mul(f, b->c[i]);
    a->c[a->deg] = 0;
    if (a->deg == 0)
      break;
    a->deg--;
    ptrim(a);
    if (a->deg < b->deg)
      break;
  }
}
static Poly pdiv_exact(const Poly *a, const Poly *b) /* assumes b | a */
{
  Poly r = *a, q;
  memset(&q, 0, sizeof q);
  q.deg = a->deg - b->deg;
  fe ib = inv(b->c[b->deg]);
  for (int i = q.deg; i >= 0; --i) {
    fe f = mul(r.c[i + b->deg], ib);
    q.c[i] = f;
    for (int j = 0; j <= b->deg; ++j)
      r.c[i + j] ^= mul(f, b->c[j]);
  }
  return q;
}
static int pdivides(const Poly *b, const Poly *a) {
  Poly r = *a;
  if (a->deg < b->deg)
    return 0;
  pmod(&r, b);
  for (int i = 0; i <= r.deg; ++i)
    if (r.c[i])
      return 0;
  return 1;
}
static Poly pmonic(Poly p) {
  fe i = inv(p.c[p.deg]);
  for (int k = 0; k <= p.deg; ++k)
    p.c[k] = mul(p.c[k], i);
  return p;
}

/* ================= places = Galois orbits of places at infinity
 * ================= */
typedef struct {
  int edge, wx, wy, a, b, w0;
  int d;   /* degree of the orbit (size of the Galois orbit) */
  fe p[8]; /* monic irreducible factor, p[0..d-1] (p[d] = 1) */
  int mult;
  int sigval; /* index of root among the orbit list (for printing) */
} Place;
static Place pl[MAXORB];
static int np;

/* split the edge polynomial of edge k into irreducible factors over GF(2^m) */
static int split_edge(int k, Poly *facs) {
  Edge *e = &ed[k];
  Poly Q;
  memset(&Q, 0, sizeof Q);
  Q.deg = e->len;
  for (int t = 0; t <= e->len; ++t)
    Q.c[e->len - t] = coef_at(e->vx + t * e->ex, e->vy + t * e->ey);
  ptrim(&Q);
  if (Q.deg != e->len || Q.c[0] == 0) {
    fprintf(stderr, "edge polynomial has a zero end coefficient\n");
    exit(1);
  }
  Q = pmonic(Q);
  /* squarefree check: Q' = sum_{j odd} c_j x^{j-1};  gcd(Q,Q') = 1 */
  {
    Poly D;
    memset(&D, 0, sizeof D);
    for (int j = 1; j <= Q.deg; j += 2)
      D.c[j - 1] = Q.c[j];
    D.deg = Q.deg - 1;
    ptrim(&D);
    int allzero = 1;
    for (int i = 0; i <= D.deg; ++i)
      if (D.c[i])
        allzero = 0;
    if (allzero) {
      fprintf(stderr, "edge %d: polynomial is a p-th power (degenerate)\n", k);
      exit(1);
    }
    Poly A = Q, B2 = D;
    while (!(B2.deg == 0 && B2.c[0] == 0)) {
      Poly Rr = A;
      pmod(&Rr, &B2);
      A = B2;
      B2 = Rr;
      int z = 1;
      for (int i = 0; i <= B2.deg; ++i)
        if (B2.c[i])
          z = 0;
      if (z)
        break;
    }
    if (A.deg > 0) {
      fprintf(stderr, "edge %d: repeated factor (curve is degenerate)\n", k);
      exit(1);
    }
  }
  int nf = 0;
  /* linear factors */
  for (int x = 0; x < FS; ++x)
    if (peval(&Q, (fe)x) == 0) {
      Poly L;
      memset(&L, 0, sizeof L);
      L.deg = 1;
      L.c[1] = 1;
      L.c[0] = (fe)x;
      facs[nf++] = L;
      Poly q = pdiv_exact(&Q, &L);
      Q = q;
    }
  /* quadratic factors */
  if (Q.deg >= 4) {
    for (int a = 0; a < FS && Q.deg >= 4; ++a)
      for (int b = 1; b < FS && Q.deg >= 4; ++b) {
        Poly Qd;
        memset(&Qd, 0, sizeof Qd);
        Qd.deg = 2;
        Qd.c[2] = 1;
        Qd.c[1] = (fe)a;
        Qd.c[0] = (fe)b;
        if (pdivides(&Qd, &Q)) {
          facs[nf++] = Qd;
          Poly q = pdiv_exact(&Q, &Qd);
          Q = q;
        }
      }
  }
  if (Q.deg > 5) {
    fprintf(stderr, "edge %d: irreducible factor of degree > 5 not supported\n",
            k);
    exit(1);
  }
  if (Q.deg >= 1)
    facs[nf++] = Q;
  return nf;
}

static int ne_inf_orbits(void) {
  np = 0;
  for (int k = 0; k < ne; ++k) {
    if (!ed[k].inf)
      continue;
    Poly facs[16];
    int nf = split_edge(k, facs);
    for (int f = 0; f < nf; ++f) {
      if (np >= MAXORB) {
        fprintf(stderr, "too many places\n");
        exit(1);
      }
      Place *P = &pl[np++];
      P->edge = k;
      P->wx = ed[k].wx;
      P->wy = ed[k].wy;
      P->a = ed[k].a;
      P->b = ed[k].b;
      P->w0 = ed[k].w0;
      P->d = facs[f].deg;
      P->mult = 0;
      for (int i = 0; i < 8; ++i)
        P->p[i] = (i <= facs[f].deg) ? facs[f].c[i] : 0;
    }
  }
  return np;
}

/* ================= ring K_d = GF(2^m)[theta]/(p) and Laurent series over it
 * ================= */
static int KD;
static fe KP[8];
static uint64_t KQD; /* q^d */

static void k_setup(const Place *P) {
  KD = P->d;
  for (int i = 0; i < 8; ++i)
    KP[i] = P->p[i];
  KQD = 1;
  for (int i = 0; i < KD; ++i)
    KQD *= (uint64_t)FS;
}
static inline void k_mul_acc(fe *dst, const fe *a, const fe *b) {
  if (KD == 1) {
    dst[0] ^= mul(a[0], b[0]);
    return;
  }
  fe t[16] = {0};
  for (int i = 0; i < KD; ++i)
    if (a[i])
      for (int j = 0; j < KD; ++j)
        if (b[j])
          t[i + j] ^= mul(a[i], b[j]);
  for (int k = 2 * KD - 2; k >= KD; --k) {
    fe c = t[k];
    if (!c)
      continue;
    for (int l = 0; l < KD; ++l)
      t[k - KD + l] ^= mul(c, KP[l]);
    t[k] = 0;
  }
  for (int i = 0; i < KD; ++i)
    dst[i] ^= t[i];
}
static void k_mul(fe *dst, const fe *a, const fe *b) {
  for (int i = 0; i < KD; ++i)
    dst[i] = 0;
  k_mul_acc(dst, a, b);
}
static int k_zero(const fe *a) {
  for (int i = 0; i < KD; ++i)
    if (a[i])
      return 0;
  return 1;
}
static void k_pow_u64(fe *out, const fe *a, uint64_t n) {
  fe res[8] = {0}, base[8], tmp[8];
  res[0] = 1;
  for (int i = 0; i < KD; ++i)
    base[i] = a[i];
  while (n) {
    if (n & 1) {
      k_mul(tmp, res, base);
      for (int i = 0; i < KD; ++i)
        res[i] = tmp[i];
    }
    n >>= 1;
    if (n) {
      k_mul(tmp, base, base);
      for (int i = 0; i < KD; ++i)
        base[i] = tmp[i];
    }
  }
  for (int i = 0; i < KD; ++i)
    out[i] = res[i];
}
static void k_inv(fe *out, const fe *a) {
  if (KD == 1) {
    out[0] = inv(a[0]);
    return;
  }
  k_pow_u64(out, a, KQD - 2);
}

#define SC(arr, t) ((arr) + (size_t)(t) * KD)

static void s_mul(const fe *a, const fe *b, fe *r, int n) {
  memset(r, 0, (size_t)n * KD * sizeof(fe));
  if (KD == 1) {
    for (int i = 0; i < n; i++) {
      if (!a[i])
        continue;
      int la = glog[a[i]];
      for (int j = 0; i + j < n; j++)
        if (b[j])
          r[i + j] ^= gexp[la + glog[b[j]]];
    }
    return;
  }
  for (int i = 0; i < n; i++) {
    const fe *ai = SC(a, i);
    if (k_zero(ai))
      continue;
    for (int j = 0; i + j < n; j++) {
      const fe *bj = SC(b, j);
      if (k_zero(bj))
        continue;
      k_mul_acc(SC(r, i + j), ai, bj);
    }
  }
}
static void s_inv(const fe *a, fe *r, int n) {
  fe i0[8];
  k_inv(i0, a);
  for (int i = 0; i < KD; ++i)
    SC(r, 0)[i] = i0[i];
  for (int k = 1; k < n; k++) {
    fe s[8] = {0};
    for (int j = 1; j <= k; j++) {
      const fe *aj = SC(a, j), *rk = SC(r, k - j);
      if (k_zero(aj) || k_zero(rk))
        continue;
      k_mul_acc(s, aj, rk);
    }
    k_mul(SC(r, k), s, i0);
  }
}
static void s_pow(const fe *a, long long r, int n, fe *out) {
  size_t sz = (size_t)n * KD;
  fe *base = malloc(sz * sizeof(fe)), *res = calloc(sz, sizeof(fe)),
     *tmp = malloc(sz * sizeof(fe));
  if (r < 0) {
    s_inv(a, base, n);
    r = -r;
  } else
    memcpy(base, a, sz * sizeof(fe));
  res[0] = 1;
  while (r) {
    if (r & 1) {
      s_mul(res, base, tmp, n);
      memcpy(res, tmp, sz * sizeof(fe));
    }
    r >>= 1;
    if (r) {
      s_mul(base, base, tmp, n);
      memcpy(base, tmp, sz * sizeof(fe));
    }
  }
  memcpy(out, res, sz * sizeof(fe));
  free(base);
  free(res);
  free(tmp);
}

static fe *compute_sigma(const Place *P, int N) {
  size_t sz = (size_t)N * KD;
  fe *sg = calloc(sz, sizeof(fe)), *G = malloc(sz * sizeof(fe)),
     *Gs = malloc(sz * sizeof(fe));
  fe *pr = malloc(sz * sizeof(fe)), *iv = malloc(sz * sizeof(fe)),
     *dl = malloc(sz * sizeof(fe));
  if (KD == 1)
    sg[0] = P->p[0];
  else
    sg[1] = 1; /* root of the factor: theta (or -p0 = p0) */
  int iters = 1;
  while ((1 << iters) < N)
    iters++;
  iters += 2;
  for (int it = 0; it <= iters; it++) {
    memset(G, 0, sz * sizeof(fe));
    memset(Gs, 0, sz * sizeof(fe));
    for (int t = 0; t < T; t++) {
      int sh = P->wx * TX[t] + P->wy * TY[t] - P->w0;
      int r = -P->b * TX[t] + P->a * TY[t];
      if (sh >= N)
        continue;
      s_pow(sg, r, N, pr);
      for (int k = 0; k + sh < N; k++)
        for (int c = 0; c < KD; c++)
          SC(G, k + sh)[c] ^= mul(TC[t], SC(pr, k)[c]);
      if (r & 1) {
        s_pow(sg, r - 1, N, pr);
        for (int k = 0; k + sh < N; k++)
          for (int c = 0; c < KD; c++)
            SC(Gs, k + sh)[c] ^= mul(TC[t], SC(pr, k)[c]);
      }
    }
    if (it == iters) {
      for (size_t k = 0; k < sz; k++)
        if (G[k]) {
          fprintf(stderr, "Newton iteration did not converge\n");
          exit(1);
        }
      break;
    }
    if (k_zero(Gs)) {
      fprintf(stderr, "multiple root of the edge polynomial\n");
      exit(1);
    }
    s_inv(Gs, iv, N);
    s_mul(G, iv, dl, N);
    for (size_t k = 0; k < sz; k++)
      sg[k] ^= dl[k];
  }
  free(G);
  free(Gs);
  free(pr);
  free(iv);
  free(dl);
  return sg;
}

typedef struct {
  int vmin, N, rmin, rmax;
  fe *pw;
} PSer;

static void place_series(const Place *P, int ehi, int J, PSer *S) {
  k_setup(P);
  int c[4] = {0, P->wx * (dx_deg - 1), P->wy * J,
              P->wx * (dx_deg - 1) + P->wy * J};
  int vmin = c[0];
  for (int i = 1; i < 4; i++)
    if (c[i] < vmin)
      vmin = c[i];
  int rc[4] = {0, -P->b * (dx_deg - 1), P->a * J,
               -P->b * (dx_deg - 1) + P->a * J};
  int rmin = rc[0], rmax = rc[0];
  for (int i = 1; i < 4; i++) {
    if (rc[i] < rmin)
      rmin = rc[i];
    if (rc[i] > rmax)
      rmax = rc[i];
  }
  S->vmin = vmin;
  S->rmin = rmin;
  S->rmax = rmax;
  int N = ehi - vmin + 1;
  S->N = N > 0 ? N : 0;
  S->pw = NULL;
  if (N <= 0)
    return;
  size_t sz = (size_t)N * KD;
  fe *sg = compute_sigma(P, N), *si = malloc(sz * sizeof(fe));
  s_inv(sg, si, N);
  int R = rmax - rmin + 1;
  S->pw = calloc((size_t)R * sz, sizeof(fe));
  fe *z = S->pw + (size_t)(0 - rmin) * sz;
  z[0] = 1;
  for (int r = 1; r <= rmax; r++)
    s_mul(S->pw + (size_t)(r - 1 - rmin) * sz, sg,
          S->pw + (size_t)(r - rmin) * sz, N);
  for (int r = -1; r >= rmin; r--)
    s_mul(S->pw + (size_t)(r + 1 - rmin) * sz, si,
          S->pw + (size_t)(r - rmin) * sz, N);
  free(sg);
  free(si);
}

/* ================= L(D): D supported on places at infinity =================
 */
typedef struct {
  int dim, K, J;
  fe *B;
} LSp;

static int genus_g;

static int solve_L(const int *mult, int Jfix, int Jstep, int Jmax, int verbose,
                   LSp *out) {
  int degD = 0, maxm = 0;
  for (int q = 0; q < np; q++) {
    degD += mult[q] * pl[q].d;
    if (mult[q] > maxm)
      maxm = mult[q];
  }
  int certifiable = degD >= 2 * genus_g - 1, expected = degD - genus_g + 1;
  int J = (Jfix >= 0) ? Jfix : (maxm / 4 + 16);
  if (J < 8)
    J = 8;
  fe *Bv = NULL;
  int dim = 0, K = 0, lastdim = -1, stable = 0;
  for (;;) {
    K = dx_deg * (J + 1);
    int ehi_q[MAXORB];
    PSer S[MAXORB];
    size_t E = 0;
    for (int q = 0; q < np; q++) {
      ehi_q[q] = -mult[q] - 1;
      place_series(&pl[q], ehi_q[q], J, &S[q]);
      E += (size_t)S[q].N * pl[q].d;
    }
    if ((double)E * K > 9e8) {
      fprintf(stderr, "matrix too large (E=%zu, K=%d)\n", E, K);
      exit(1);
    }
    fe *Mx = calloc(E * K ? E * K : 1, sizeof(fe));
    size_t off = 0;
    for (int q = 0; q < np; q++) {
      int d = pl[q].d;
      if (S[q].N > 0) {
        size_t sz = (size_t)S[q].N * d;
        for (int j = 0; j <= J; j++)
          for (int i = 0; i < dx_deg; i++) {
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
    int *pc = malloc(sizeof(int) * (K + 1));
    size_t rk = 0;
    int *lr = malloc(sizeof(int) * K);
    fe *tmprow = malloc(sizeof(fe) * K);
    for (int c = 0; c < K && rk < E; c++) {
      size_t p = rk;
      while (p < E && !Mx[p * K + c])
        p++;
      if (p == E)
        continue;
      if (p != rk) {
        memcpy(tmprow, Mx + p * K, K * sizeof(fe));
        memcpy(Mx + p * K, Mx + rk * K, K * sizeof(fe));
        memcpy(Mx + rk * K, tmprow, K * sizeof(fe));
      }
      fe *R = Mx + rk * K;
      fe iv = inv(R[c]);
      for (int col = c; col < K; col++)
        R[col] = mul(R[col], iv);
      for (int col = c; col < K; col++)
        lr[col] = R[col] ? glog[R[col]] : -1;
#pragma omp parallel for schedule(static)
      for (long long ii = (long long)rk + 1; ii < (long long)E; ii++) {
        fe *Dr = Mx + (size_t)ii * K;
        fe f = Dr[c];
        if (!f)
          continue;
        int lf = glog[f];
        for (int col = c; col < K; col++) {
          int x = lr[col];
          if (x >= 0)
            Dr[col] ^= gexp[lf + x];
        }
      }
      pc[rk++] = c;
    }
    char *isp = calloc(K, 1);
    for (size_t i = 0; i < rk; i++)
      isp[pc[i]] = 1;
    dim = K - (int)rk;
    free(Bv);
    Bv = calloc((size_t)(dim ? dim : 1) * K, sizeof(fe));
    int bi = 0;
    for (int f = 0; f < K; f++) {
      if (isp[f])
        continue;
      fe *x = Bv + (size_t)bi * K;
      x[f] = 1;
      for (long long i = (long long)rk - 1; i >= 0; i--) {
        int c = pc[i];
        const fe *R = Mx + (size_t)i * K;
        fe s = 0;
        for (int col = c + 1; col < K; col++)
          if (R[col] && x[col])
            s ^= mul(R[col], x[col]);
        x[c] = s;
      }
      bi++;
    }
    free(Mx);
    free(pc);
    free(lr);
    free(tmprow);
    free(isp);
    if (verbose) {
      printf("#   J=%d: unknowns %d, equations %zu, dim L(D) = %d", J, K, E,
             dim);
      if (certifiable)
        printf("  (Riemann-Roch: %d)", expected);
      printf("\n");
      fflush(stdout);
    }
    if (Jfix >= 0)
      break;
    if (certifiable) {
      if (dim == expected)
        break;
      if (dim > expected) {
        fprintf(stderr,
                "dimension exceeds Riemann-Roch: curve assumptions violated\n");
        break;
      }
    } else {
      if (dim == lastdim) {
        stable++;
        if (stable >= 2)
          break;
      } else
        stable = 0;
      lastdim = dim;
    }
    if (J >= Jmax) {
      fprintf(stderr, "warning: Jmax reached, basis may be incomplete\n");
      break;
    }
    int deficit = certifiable ? expected - dim : 0;
    int st = Jstep;
    if (certifiable && deficit / 6 + 1 > st)
      st = deficit / 6 + 1;
    J += st;
    if (J > Jmax)
      J = Jmax;
  }
  out->dim = dim;
  out->K = K;
  out->J = J;
  out->B = Bv;
  if (certifiable && dim != expected)
    return -1;
  return 0;
}

/* ================= points ================= */
static int npts;
static fe *PXv, *PYv;

static void enumerate_points(void) {
  int cap = 1024;
  npts = 0;
  PXv = malloc(sizeof(fe) * cap);
  PYv = malloc(sizeof(fe) * cap);
  fe *ypw = malloc(sizeof(fe) * (size_t)T * FS);
  for (int t = 0; t < T; ++t)
    for (int y = 0; y < FS; ++y)
      ypw[(size_t)t * FS + y] = gpow((fe)y, TY[t]);
  for (int x = 0; x < FS; ++x) {
    fe xp[MAXTERM];
    for (int t = 0; t < T; ++t)
      xp[t] = mul(TC[t], gpow((fe)x, TX[t]));
    for (int y = 0; y < FS; ++y) {
      fe acc = 0;
      for (int t = 0; t < T; ++t)
        acc ^= mul(xp[t], ypw[(size_t)t * FS + y]);
      if (!acc) {
        if (npts == cap) {
          cap *= 2;
          PXv = realloc(PXv, sizeof(fe) * cap);
          PYv = realloc(PYv, sizeof(fe) * cap);
        }
        PXv[npts] = (fe)x;
        PYv[npts] = (fe)y;
        npts++;
      }
    }
  }
  free(ypw);
}

/* evaluation matrix: out[d*npts + p] = (d-th basis vector of L)(P_p) */
static fe *eval_space(const LSp *L) {
  int dim = L->dim, K = L->K, J = L->J;
  fe *out = malloc(sizeof(fe) * (size_t)(dim ? dim : 1) * npts);
  uint16_t *LB = malloc(sizeof(uint16_t) * (size_t)(dim ? dim : 1) * K);
  for (size_t i = 0; i < (size_t)dim * K; ++i)
    LB[i] = L->B[i] ? glog[L->B[i]] : 0xFFFF;
#pragma omp parallel
  {
    fe *xp = malloc(sizeof(fe) * dx_deg), *yp = malloc(sizeof(fe) * (J + 1));
    int *ml = malloc(sizeof(int) * K);
#pragma omp for schedule(static)
    for (int p = 0; p < npts; ++p) {
      xp[0] = 1;
      for (int i = 1; i < dx_deg; ++i)
        xp[i] = mul(xp[i - 1], PXv[p]);
      yp[0] = 1;
      for (int j = 1; j <= J; ++j)
        yp[j] = mul(yp[j - 1], PYv[p]);
      for (int c = 0; c < K; ++c) {
        fe v = mul(xp[c % dx_deg], yp[c / dx_deg]);
        ml[c] = v ? glog[v] : -1;
      }
      for (int d = 0; d < dim; ++d) {
        const uint16_t *lb = LB + (size_t)d * K;
        fe acc = 0;
        for (int c = 0; c < K; ++c)
          if (lb[c] != 0xFFFF && ml[c] >= 0)
            acc ^= gexp[lb[c] + ml[c]];
        out[(size_t)d * npts + p] = acc;
      }
    }
    free(xp);
    free(yp);
    free(ml);
  }
  free(LB);
  return out;
}

static fe dotv(const fe *a, const fe *b, int n) {
  fe s = 0;
  for (int k = 0; k < n; ++k)
    if (a[k] && b[k])
      s ^= gexp[glog[a[k]] + glog[b[k]]];
  return s;
}

/* nullspace of A (E x K) (A is destroyed); out: dim x K, identity on free
 * columns */
static int nullspace_gf(fe *A, int E, int K, fe **out) {
  int *pc = malloc(sizeof(int) * (K + 1));
  int rk = 0;
  int *lr = malloc(sizeof(int) * K);
  fe *tmp = malloc(sizeof(fe) * K);
  for (int c = 0; c < K && rk < E; ++c) {
    int p = rk;
    while (p < E && !A[(size_t)p * K + c])
      p++;
    if (p == E)
      continue;
    if (p != rk) {
      memcpy(tmp, A + (size_t)p * K, K * sizeof(fe));
      memcpy(A + (size_t)p * K, A + (size_t)rk * K, K * sizeof(fe));
      memcpy(A + (size_t)rk * K, tmp, K * sizeof(fe));
    }
    fe *R = A + (size_t)rk * K;
    fe iv = inv(R[c]);
    for (int col = c; col < K; ++col)
      R[col] = mul(R[col], iv);
    for (int col = c; col < K; ++col)
      lr[col] = R[col] ? glog[R[col]] : -1;
#pragma omp parallel for schedule(static)
    for (int ii = rk + 1; ii < E; ++ii) {
      fe *Dr = A + (size_t)ii * K;
      fe f = Dr[c];
      if (!f)
        continue;
      int lf = glog[f];
      for (int col = c; col < K; ++col) {
        int x = lr[col];
        if (x >= 0)
          Dr[col] ^= gexp[lf + x];
      }
    }
    pc[rk++] = c;
  }
  char *isp = calloc(K, 1);
  for (int i = 0; i < rk; ++i)
    isp[pc[i]] = 1;
  int dim = K - rk;
  fe *B = calloc((size_t)(dim ? dim : 1) * K, sizeof(fe));
  int bi = 0;
  for (int f = 0; f < K; ++f) {
    if (isp[f])
      continue;
    fe *x = B + (size_t)bi * K;
    x[f] = 1;
    for (int i = rk - 1; i >= 0; --i) {
      int c = pc[i];
      const fe *R = A + (size_t)i * K;
      fe s = 0;
      for (int col = c + 1; col < K; ++col)
        if (R[col] && x[col])
          s ^= mul(R[col], x[col]);
      x[c] = s;
    }
    bi++;
  }
  free(pc);
  free(lr);
  free(tmp);
  free(isp);
  *out = B;
  return dim;
}

/* right inverse: R (n x r) with U R = I_r, U is r x n of full row rank */
static int right_inverse(const fe *U, int r, int n, fe *R) {
  int W = n + r;
  fe *Aug = calloc((size_t)r * W, sizeof(fe));
  for (int i = 0; i < r; ++i) {
    memcpy(Aug + (size_t)i * W, U + (size_t)i * n, n * sizeof(fe));
    Aug[(size_t)i * W + n + i] = 1;
  }
  int *P = malloc(sizeof(int) * r);
  int rk = 0;
  int *lr = malloc(sizeof(int) * W);
  for (int c = 0; c < n && rk < r; ++c) {
    int p = rk;
    while (p < r && !Aug[(size_t)p * W + c])
      p++;
    if (p == r)
      continue;
    if (p != rk)
      for (int k = 0; k < W; ++k) {
        fe t = Aug[(size_t)p * W + k];
        Aug[(size_t)p * W + k] = Aug[(size_t)rk * W + k];
        Aug[(size_t)rk * W + k] = t;
      }
    fe *Rw = Aug + (size_t)rk * W;
    fe iv = inv(Rw[c]);
    for (int k = c; k < W; ++k)
      Rw[k] = mul(Rw[k], iv);
    for (int k = c; k < W; ++k)
      lr[k] = Rw[k] ? glog[Rw[k]] : -1;
#pragma omp parallel for schedule(static)
    for (int ii = 0; ii < r; ++ii) {
      if (ii == rk)
        continue;
      fe *Dr = Aug + (size_t)ii * W;
      fe f = Dr[c];
      if (!f)
        continue;
      int lf = glog[f];
      for (int k = c; k < W; ++k) {
        int x = lr[k];
        if (x >= 0)
          Dr[k] ^= gexp[lf + x];
      }
    }
    P[rk++] = c;
  }
  if (rk < r) {
    free(Aug);
    free(P);
    free(lr);
    return -1;
  }
  memset(R, 0, sizeof(fe) * (size_t)n * r);
  for (int a = 0; a < r; ++a)
    for (int b = 0; b < r; ++b)
      R[(size_t)P[a] * r + b] = Aug[(size_t)a * W + n + b];
  free(Aug);
  free(P);
  free(lr);
  return 0;
}

/* ================= one-point echelon basis at a rational place
 * ================= */
/* Turns the nullspace basis of L(mP) into functions f_s with pole order exactly
 * s and Laurent coefficient 1 at u^-s ("monic").  polev[d] = pole order of
 * basis vector d (0 for the constant).  Returns the number of constants (should
 * be 1).              */
static int semigroup_echelon(LSp *L, const Place *P, int m, int *polev) {
  int dim = L->dim, K = L->K, J = L->J;
  PSer S;
  place_series(P, -1, J, &S);
  fe *phi = calloc((size_t)dim * m, sizeof(fe));
#pragma omp parallel for schedule(static)
  for (int d = 0; d < dim; ++d) {
    const fe *b = L->B + (size_t)d * K;
    for (int col = 0; col < K; ++col) {
      fe x = b[col];
      if (!x)
        continue;
      int j = col / dx_deg, i = col % dx_deg;
      int v = P->wx * i + P->wy * j, r = -P->b * i + P->a * j;
      const fe *pw = S.pw + (size_t)(r - S.rmin) * S.N;
      for (int s = 1; s <= m; ++s) {
        int t = -s - v;
        if (t < 0)
          continue;
        if (t >= S.N)
          break;
        fe cf = pw[t];
        if (cf)
          phi[(size_t)d * m + s - 1] ^= mul(cf, x);
      }
    }
  }
  free(S.pw);
  char *used = calloc(dim, 1);
  for (int s = m; s >= 1; --s) {
    int p = -1;
    for (int d = 0; d < dim; ++d)
      if (!used[d] && phi[(size_t)d * m + s - 1]) {
        p = d;
        break;
      }
    if (p < 0)
      continue;
    fe iv = inv(phi[(size_t)p * m + s - 1]);
    for (int t = 0; t < m; ++t)
      phi[(size_t)p * m + t] = mul(phi[(size_t)p * m + t], iv);
    for (int c = 0; c < K; ++c)
      L->B[(size_t)p * K + c] = mul(L->B[(size_t)p * K + c], iv);
#pragma omp parallel for schedule(static)
    for (int d = 0; d < dim; ++d) {
      if (d == p || used[d])
        continue;
      fe f = phi[(size_t)d * m + s - 1];
      if (!f)
        continue;
      for (int t = 0; t < m; ++t)
        phi[(size_t)d * m + t] ^= mul(f, phi[(size_t)p * m + t]);
      for (int c = 0; c < K; ++c)
        L->B[(size_t)d * K + c] ^= mul(f, L->B[(size_t)p * K + c]);
    }
    used[p] = 1;
    polev[p] = s;
  }
  int nconst = 0;
  for (int d = 0; d < dim; ++d)
    if (!used[d]) {
      polev[d] = 0;
      nconst++;
    }
  free(phi);
  free(used);
  return nconst;
}

/* ================================================================== */
/*  One-point basis from the NEWTON POLYGON  (replaces solve_L +        */
/*  semigroup_echelon whenever it applies)                              */
/* ================================================================== */
/* Let P be the place of an edge e of Newton(F) of lattice length 1, with
 * primitive inward normal w_e.  A Laurent monomial x^i y^j has valuation
 * w_k . (i,j) at the places of edge k, so
 *      x^i y^j in L(M P)   <=>   w_k.(i,j) >= 0 (all k != e),  -w_e.(i,j) <= M,
 * its pole order at P being -w_e.(i,j).  Monomials of equal weight differ only
 * by lower pole orders (modulo F), so one representative per weight suffices.
 * If the weights found are exactly the M+1-g many pole orders that
 * Riemann-Roch demands (M >= 2g-1), they form a complete basis of L(M P):
 * the result is certified at run time, otherwise the caller falls back to
 * the Laurent-expansion method.                                              */
typedef struct {
  int n, laurent;
  int *rho, *ei, *ej; /* sorted by pole order rho */
} NBas;
static int use_newton = 1, allplaces = 0;
#define NCAND_MAX (MAXORB + MAXEDGE)

static long nb_fdiv(long a, long b) { /* floor(a/b), b > 0 */
  long q = a / b;
  if ((a % b) && (a < 0))
    --q;
  return q;
}

static int newton_basis(int e, int Mx, NBas *out) {
  if (ed[e].len != 1)
    return -1; /* a single place exists only on a primitive edge */
  long ca[MAXEDGE + 1], cb[MAXEDGE + 1], ck[MAXEDGE + 1];
  int nc = 0;
  for (int k = 0; k < ne; ++k)
    if (k != e) {
      ca[nc] = ed[k].wx;
      cb[nc] = ed[k].wy;
      ck[nc] = 0;
      nc++;
    }
  ca[nc] = ed[e].wx; /* pole order -w_e.(i,j) <= M  <=>  w_e.(i,j) + M >= 0 */
  cb[nc] = ed[e].wy;
  ck[nc] = Mx;
  nc++;
  int *ri = malloc(sizeof(int) * (Mx + 1)), *rj = malloc(sizeof(int) * (Mx + 1));
  char *have = calloc(Mx + 1, 1);
  int bad = 0;
  for (int dir = 0; dir < 2 && !bad; ++dir)
    for (int i = dir ? -1 : 0;; i += dir ? -1 : 1) {
      if (i > (1 << 20) || i < -(1 << 20)) {
        bad = 1;
        break;
      }
      long jl = -(1L << 40), jh = (1L << 40);
      double rl = -1e18, rh = 1e18;
      int empty = 0;
      for (int c = 0; c < nc && !empty; ++c) {
        long v = ca[c] * i + ck[c];
        if (cb[c] == 0) {
          if (v < 0)
            empty = 1;
        } else if (cb[c] > 0) {
          long l = -nb_fdiv(v, cb[c]);
          if (l > jl)
            jl = l;
          double r = -(double)v / (double)cb[c];
          if (r > rl)
            rl = r;
        } else {
          long h = nb_fdiv(v, -cb[c]);
          if (h < jh)
            jh = h;
          double r = (double)v / (double)(-cb[c]);
          if (r < rh)
            rh = r;
        }
      }
      if (empty || rl > rh + 1e-9)
        break; /* convex region: slices are contiguous in i */
      for (long j = jl; j <= jh; ++j) {
        int w = -(int)(ed[e].wx * (long)i + ed[e].wy * j);
        if (w < 0 || w > Mx) {
          bad = 1;
          break;
        }
        int neg = (i < 0 || j < 0);
        if (!have[w]) {
          have[w] = 1;
          ri[w] = i;
          rj[w] = (int)j;
        } else if (neg == 0 && (ri[w] < 0 || rj[w] < 0)) {
          ri[w] = i; /* prefer a representative without negative exponents */
          rj[w] = (int)j;
        }
      }
      if (bad)
        break;
    }
  int cnt = 0;
  for (int w = 0; w <= Mx; ++w)
    cnt += have[w];
  int ok = !bad && have[0] && ri[0] == 0 && rj[0] == 0 &&
           cnt == Mx + 1 - genus_g;
  int laurent = 0;
  if (ok)
    for (int w = 0; w <= Mx; ++w)
      if (have[w] && (ri[w] < 0 || rj[w] < 0))
        laurent = 1;
  if (ok && laurent) {
    /* negative exponents need: the only point of the model on x=0 or y=0 is
     * the origin, i.e. F(0,y) and F(x,0) are single monomials */
    int tx0 = 0, ty0 = 0;
    for (int t = 0; t < T; ++t) {
      tx0 += (TX[t] == 0);
      ty0 += (TY[t] == 0);
    }
    if (tx0 > 1 || ty0 > 1)
      ok = 0;
  }
  if (ok) {
    out->n = cnt;
    out->laurent = laurent;
    out->rho = malloc(sizeof(int) * cnt);
    out->ei = malloc(sizeof(int) * cnt);
    out->ej = malloc(sizeof(int) * cnt);
    int k = 0;
    for (int w = 0; w <= Mx; ++w)
      if (have[w]) {
        out->rho[k] = w;
        out->ei[k] = ri[w];
        out->ej[k] = rj[w];
        k++;
      }
  }
  free(ri);
  free(rj);
  free(have);
  return ok ? 0 : -1;
}

/* value of x^i y^j at a point (i, j may be negative; then x, y != 0) */
static fe mono_eval(fe x, fe y, int i, int j) {
  if (i == 0 && j == 0)
    return 1;
  if ((i != 0 && !x) || (j != 0 && !y))
    return 0;
  long long ex = ((long long)i * (x ? glog[x] : 0) +
                  (long long)j * (y ? glog[y] : 0)) % FO;
  if (ex < 0)
    ex += FO;
  return gexp[ex];
}


/* Fast row evaluation: out[k] = x_k^i y_k^j for k < n, using precomputed
 * log arrays (lx[k], ly[k] = -1 for a zero coordinate).  Same result as
 * mono_eval, but without per-element 64-bit division (Barrett reduction). */
static void mono_eval_row(fe *out, int n, const int *lx, const int *ly, int i,
                          int j) {
  if (i == 0 && j == 0) {
    for (int k = 0; k < n; ++k)
      out[k] = 1;
    return;
  }
  int ie = i % FO, je = j % FO;
  if (ie < 0)
    ie += FO;
  if (je < 0)
    je += FO;
  const uint64_t magic = ((uint64_t)1 << 40) / (uint64_t)FO + 1;
  for (int k = 0; k < n; ++k) {
    int a = lx[k], b = ly[k];
    if ((i != 0 && a < 0) || (j != 0 && b < 0)) {
      out[k] = 0;
      continue;
    }
    uint32_t ex = (uint32_t)(ie * (a < 0 ? 0 : a) + je * (b < 0 ? 0 : b));
    uint32_t q = (uint32_t)(((uint64_t)ex * magic) >> 40);
    out[k] = gexp[ex - q * (uint32_t)FO];
  }
}

/* d_FR(M) = min { nu(s) : s > M, s in H },  nu(s) = #{(a,b) in H^2, a+b = s} */
static int dfr_of(const int *inH_arr, int M, int span) {
  int best = 1 << 30;
  for (int s = M + 1; s <= M + span; ++s) {
    int c = 0;
    for (int a = 0; a <= s; ++a)
      if (inH_arr[a] && inH_arr[s - a])
        c++;
    if (c < best)
      best = c;
  }
  return best;
}

/* ================================================================== */
/*  One-point decoders (generalised from the Suzuki version)           */
/* ================================================================== */
static int GENUS, M_SYND, M_EXT, TAU, TAU_V, L_DEG, ROW_MAX, ASHIFT, NUM_ERRORS;

typedef struct {
  int rho;
  fe *val;
} Basis;
static Basis basis[MAXB];
static int nbasis;
static int in_H[SGMAX], idx_of_ord[SGMAX];
static int genH[MAXB], ngenH;

static int count_basis_upto(int rho) {
  int n = 0;
  for (int i = 0; i < nbasis; ++i)
    if (basis[i].rho <= rho)
      ++n;
  return n;
}

static void init_semigroup(void) {
  for (int x = 0; x < SGMAX; ++x) {
    in_H[x] = (x > M_EXT);
    idx_of_ord[x] = -1;
  }
  for (int i = 0; i < nbasis; ++i) {
    in_H[basis[i].rho] = 1;
    idx_of_ord[basis[i].rho] = i;
  }
  ngenH = 0;
  for (int s = 1; s <= M_EXT; ++s) {
    if (!in_H[s])
      continue;
    int gen = 1;
    for (int a = 1; a <= s / 2 && gen; ++a)
      if (in_H[a] && in_H[s - a])
        gen = 0;
    if (gen)
      genH[ngenH++] = s;
  }
}

/* ---- syndromes ---- */
static const fe *recv;
static int *nz_idx;
static int nz_cnt;

static fe synd(int ia, int ib, const fe *wt) {
  fe acc = 0;
  for (int n = 0; n < nz_cnt; ++n) {
    int k = nz_idx[n];
    fe term = mul(recv[k], mul(basis[ia].val[k], basis[ib].val[k]));
    if (wt)
      term = mul(term, wt[k]);
    acc ^= term;
  }
  return acc;
}
static fe synd1(int ia) {
  fe acc = 0;
  for (int n = 0; n < nz_cnt; ++n)
    acc ^= mul(recv[nz_idx[n]], basis[ia].val[nz_idx[n]]);
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
static Result res_fr, res_bms, res_vote, res_frvote;

/* Public API bridge: caller-owned received word and output buffers. */
static const fe *api_received = NULL;
static size_t api_received_len = 0;
static size_t *api_error_positions = NULL;
static fe *api_error_values = NULL;
static size_t api_output_capacity = 0;
static size_t *api_error_count = NULL;
static int api_mode = 0;
static int api_completed = 0;
static fe *api_owned_received = NULL;
static size_t *api_position_map = NULL;

static fe aug[MAXB][MAXT + 2];
static fe err_val[MAXT + 1];

/* Error values: solve  sum_k e_k h_a(P_k) = S_a  (a = 0 .. m-1).
 * Only ~n rows are needed to determine the n unknowns, so forward elimination
 * is done on the first R = n + slack rows only (O(n^3/3) instead of
 * O(m n^2/2)); the remaining rows are merely verified afterwards, O(m n).
 * The inner loop is branch-free: the pivot row is kept in log form and the
 * zero element is mapped to a sentinel log whose exp-table entry is 0. */
static int resolve_by_values(int *found, int *nfound) {
  int n = *nfound, m = count_basis_upto(M_SYND);
  if (n > MAXT)
    return 0;
  const int SENT = 2 * FO;
  fe *E = malloc(sizeof(fe) * (size_t)(3 * FO + 8));
  uint16_t *lg = malloc(sizeof(uint16_t) * (size_t)(n + 2));
  fe *x = malloc(sizeof(fe) * (size_t)(n + 1));
  int ok = 0;
  if (!E || !lg || !x)
    goto done;
  for (int i = 0; i < 3 * FO + 8; ++i)
    E[i] = i < 2 * FO ? gexp[i % FO] : 0;
  int R = n + 32 < m ? n + 32 : m;
  for (;;) {
    for (int a = 0; a < R; ++a) {
      for (int k = 0; k < n; ++k)
        aug[a][k] = basis[a].val[found[k]];
      aug[a][n] = synd1(a);
    }
    int retry = 0;
    for (int c = 0; c < n; ++c) {
      int p = -1;
      for (int a = c; a < R; ++a)
        if (aug[a][c]) {
          p = a;
          break;
        }
      if (p < 0) {
        if (R < m) {
          retry = 1; /* rare: enlarge the row window and start over */
          break;
        }
        goto done;
      }
      if (p != c)
        for (int k = c; k <= n; ++k) {
          fe t = aug[p][k];
          aug[p][k] = aug[c][k];
          aug[c][k] = t;
        }
      fe iv = inv(aug[c][c]);
      aug[c][c] = 1;
      lg[c] = 0;
      for (int k = c + 1; k <= n; ++k) {
        aug[c][k] = mul(aug[c][k], iv);
        lg[k] = aug[c][k] ? glog[aug[c][k]] : (uint16_t)SENT;
      }
      for (int a = c + 1; a < R; ++a) {
        fe f = aug[a][c];
        if (!f)
          continue;
        const int lf = glog[f];
        fe *row = aug[a];
        for (int k = c + 1; k <= n; ++k)
          row[k] ^= E[lf + lg[k]];
        row[c] = 0;
      }
    }
    if (retry) {
      R = m;
      continue;
    }
    break;
  }
  for (int a = n; a < R; ++a)
    if (aug[a][n])
      goto done; /* inconsistent */
  /* back substitution */
  for (int c = n - 1; c >= 0; --c) {
    fe acc = aug[c][n];
    for (int k = c + 1; k < n; ++k)
      acc ^= mul(aug[c][k], x[k]);
    x[c] = acc;
  }
  /* verify the rows that were not used for elimination */
  for (int a = R; a < m; ++a) {
    fe acc = synd1(a);
    for (int k = 0; k < n; ++k)
      acc ^= mul(x[k], basis[a].val[found[k]]);
    if (acc)
      goto done;
  }
  {
    int keep = 0;
    for (int k = 0; k < n; ++k)
      if (x[k]) {
        found[keep] = found[k];
        err_val[keep] = x[k];
        ++keep;
      }
    *nfound = keep;
  }
  ok = 1;
done:
  free(E);
  free(lg);
  free(x);
  return ok;
}

static void resolve_and_store(Result *R) {
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

/* ================= FR: basic algorithm + characteristic polynomial
 * ================= */
static uint16_t (*plr)[MAXB], (*plc)[MAXB];   /* ピボット行の log(スロット MAXT 個) */
static int slot_of_row[MAXB];
static fe *E0f;

/* ---- 後ろで定義されるものの前方宣言 ---- */
static int use_poly;                       /* 後ろの "static int use_poly = 0, ..." と両立する(仮定義) */
static fe *pp_S;
static inline int pp_at(int i, int j);
static int *bas_ei, *bas_ej;               /* main で設定 */


static inline fe synd_fast(int a, int b, int shi, int shj) {
  if (!bas_ei || !bas_ej) { fprintf(stderr, "bas_ei/bas_ej not set\n"); abort(); }
  int t = pp_at(bas_ei[a] + bas_ei[b] + shi, bas_ej[a] + bas_ej[b] + shj);
  if (t < 0) {
    fprintf(stderr, "synd_fast: lattice point not in table (a=%d b=%d)\n", a, b);
    abort();
  }
  return pp_S[t];
}

/* ---- 消えていた元の宣言 ---- */
static fe red[MAXB][MAXB];
static fe coefm[MAXB][MAXB];
static int piv_of_row[MAXB], row_of_col[MAXB];
static fe pivinv[MAXB];

static uint16_t (*plr)[MAXB], (*plc)[MAXB];
static int slot_of_row[MAXB];
static fe *E0f;


static inline fe synd_fast2(int a, int b, int shi, int shj) {
  int t = pp_at(bas_ei[a] + bas_ei[b] + shi, bas_ej[a] + bas_ej[b] + shj);
  return pp_S[t];
}

/* ---- 消えていた元の宣言 ---- */
static fe red[MAXB][MAXB];
static fe coefm[MAXB][MAXB];
static int piv_of_row[MAXB], row_of_col[MAXB];
static fe pivinv[MAXB];

/* ---- 私が書いた追加分 ---- */
static uint16_t (*plr)[MAXB], (*plc)[MAXB];
static int slot_of_row[MAXB];
static fe *E0f;


#define FR_BLK 64
static int fr_pos[MAXB], fr_ncol[MAXB];

/* 行 i を列 j0 から簡約する。ピボット列を持たない非零の列で止まり、その列を返す。
 * 最後まで消えたら ncol を返す。row_of_col / plr / plc は読むだけ。 */
static int fr_run(int i, int ncol, int needc, int j0) {
  fe *Ri = red[i];
  for (int j = j0; j < ncol; ++j) {
    fe v = Ri[j];
    if (!v) continue;
    int p = row_of_col[j];
    if (p < 0) return j;
    int s  = slot_of_row[p];
    int lf = glog[mul(v, pivinv[p])];
    const uint16_t *lr = plr[s];
    for (int jj = j; jj < ncol; ++jj) Ri[jj] ^= E0f[lf + lr[jj]];
    if (needc) {
      const uint16_t *lc = plc[s];
      fe *Ci = coefm[i];
      for (int k = 0; k <= p; ++k) Ci[k] ^= E0f[lf + lc[k]];
    }
  }
  return ncol;
}

static int feng_rao_reduce(void) {
  int nrows = count_basis_upto(ROW_MAX);
  int nl    = count_basis_upto(L_DEG);
  int nslot = 0;
  if (!E0f) {
    E0f = calloc((size_t)4 * FO + 8, sizeof(fe));
    for (int k = 0; k < 2 * FO; ++k) E0f[k] = gexp[k];
    plr = calloc(MAXT, sizeof *plr);
    plc = calloc(MAXT, sizeof *plc);
  }
  for (int j = 0; j < MAXB; ++j) row_of_col[j] = -1;

  for (int b0 = 0; b0 < nrows; b0 += FR_BLK) {
    int b1 = b0 + FR_BLK < nrows ? b0 + FR_BLK : nrows;

    /* フェーズA: 成分作り + 確定済みピボットでの簡約(並列) */
#pragma omp parallel for schedule(dynamic, 1)
    for (int i = b0; i < b1; ++i) {
      int ncol  = count_basis_upto(M_SYND - basis[i].rho);
      int needc = (i < nl);
      fr_ncol[i] = ncol;
      piv_of_row[i] = -1;
      for (int j = 0; j < ncol; ++j)
        red[i][j] = use_poly ? synd_fast(i, j, 0, 0) : synd(i, j, NULL);
      if (needc) { memset(coefm[i], 0, (size_t)(i + 1) * sizeof(fe)); coefm[i][i] = 1; }
      fr_pos[i] = fr_run(i, ncol, needc, 0);
    }

    /* フェーズB: ブロック内の新ピボットを使って続行(逐次) */
    for (int i = b0; i < b1; ++i) {
      int ncol  = fr_ncol[i];
      int needc = (i < nl);
      int j = fr_run(i, ncol, needc, fr_pos[i]);
      if (j >= ncol) continue;                 /* 依存行: 0 になった */
      if (nslot >= MAXT - 1) return -1;        /* ピボット過多 */
      int s = nslot++;
      slot_of_row[i] = s;
      for (int jj = 0; jj < ncol; ++jj)
        plr[s][jj] = red[i][jj] ? glog[red[i][jj]] : (uint16_t)(2 * FO);
      if (needc)
        for (int k = 0; k <= i; ++k)
          plc[s][k] = coefm[i][k] ? glog[coefm[i][k]] : (uint16_t)(2 * FO);
      piv_of_row[i] = j;
      row_of_col[j] = i;
      pivinv[i] = inv(red[i][j]);
    }
  }
  return nrows;
}


static int feng_rao_reduce2(void) {
  int nrows = count_basis_upto(ROW_MAX);
  int nl    = count_basis_upto(L_DEG);
  int nslot = 0;
  if (!E0f) {
    E0f = calloc((size_t)4 * FO + 8, sizeof(fe));
    for (int k = 0; k < 2 * FO; ++k) E0f[k] = gexp[k];
    plr = calloc(MAXT, sizeof *plr);
    plc = calloc(MAXT, sizeof *plc);
  }
  for (int j = 0; j < MAXB; ++j) row_of_col[j] = -1;

  for (int i = 0; i < nrows; ++i) {
    int ncol  = count_basis_upto(M_SYND - basis[i].rho);
    int needc = (i < nl);
    for (int j = 0; j < ncol; ++j)
      red[i][j] = use_poly ? synd_fast(i, j, 0, 0) : synd(i, j, NULL);
    if (needc) { memset(coefm[i], 0, (size_t)(i + 1) * sizeof(fe)); coefm[i][i] = 1; }
    piv_of_row[i] = -1;

    for (int j = 0; j < ncol; ++j) {
      fe v = red[i][j];
      if (!v) continue;
      int p = row_of_col[j];
      if (p >= 0) {
        int s  = slot_of_row[p];
        int lf = glog[mul(v, pivinv[p])];
        const uint16_t *lr = plr[s];
        fe *Ri = red[i];
        for (int jj = j; jj < ncol; ++jj) Ri[jj] ^= E0f[lf + lr[jj]];
        if (needc) {
          const uint16_t *lc = plc[s];
          fe *Ci = coefm[i];
          for (int k = 0; k <= p; ++k) Ci[k] ^= E0f[lf + lc[k]];
        }
      } else {
        if (nslot >= MAXT - 1) return -1;       /* ピボット過多 */
        int s = nslot++;
        slot_of_row[i] = s;
        for (int jj = 0; jj < ncol; ++jj)
          plr[s][jj] = red[i][jj] ? glog[red[i][jj]] : (uint16_t)(2 * FO);
        if (needc)
          for (int k = 0; k <= i; ++k)
            plc[s][k] = coefm[i][k] ? glog[coefm[i][k]] : (uint16_t)(2 * FO);
        piv_of_row[i] = j;
        row_of_col[j] = i;
        pivinv[i] = inv(v);
        break;
      }
    }
  }
  return nrows;
}





typedef fe Mat[MAXT][MAXT];
static Mat S0, SX, S0inv, Qm, WORK;
static fe pol[MAXT + 1][MAXT + 1];

static int mat_inverse(Mat m, Mat out, int n) {
  memcpy(WORK, m, sizeof(Mat));
  for (int i = 0; i < n; ++i) {
    for (int j = 0; j < n; ++j)
      out[i][j] = 0;
    out[i][i] = 1;
  }
  for (int c = 0; c < n; ++c) {
    int p = -1;
    for (int r = c; r < n; ++r)
      if (WORK[r][c]) {
        p = r;
        break;
      }
    if (p < 0)
      return 0;
    if (p != c)
      for (int i = 0; i < n; ++i) {
        fe t;
        t = WORK[p][i];
        WORK[p][i] = WORK[c][i];
        WORK[c][i] = t;
        t = out[p][i];
        out[p][i] = out[c][i];
        out[c][i] = t;
      }
    fe iv = inv(WORK[c][c]);
    for (int i = 0; i < n; ++i) {
      WORK[c][i] = mul(WORK[c][i], iv);
      out[c][i] = mul(out[c][i], iv);
    }
    for (int r = 0; r < n; ++r) {
      fe f = WORK[r][c];
      if (r == c || !f)
        continue;
      for (int i = 0; i < n; ++i) {
        WORK[r][i] ^= mul(f, WORK[c][i]);
        out[r][i] ^= mul(f, out[c][i]);
      }
    }
  }
  return 1;
}

static void charpoly(Mat H, int n, fe *g) {
  for (int k = 0; k + 2 < n; ++k) {
    int p = -1;
    for (int i = k + 1; i < n; ++i)
      if (H[i][k]) {
        p = i;
        break;
      }
    if (p < 0)
      continue;
    if (p != k + 1) {
      for (int j = 0; j < n; ++j) {
        fe t = H[p][j];
        H[p][j] = H[k + 1][j];
        H[k + 1][j] = t;
      }
      for (int i = 0; i < n; ++i) {
        fe t = H[i][p];
        H[i][p] = H[i][k + 1];
        H[i][k + 1] = t;
      }
    }
    fe iv = inv(H[k + 1][k]);
    for (int i = k + 2; i < n; ++i) {
      if (!H[i][k])
        continue;
      fe f = mul(H[i][k], iv);
      for (int j = 0; j < n; ++j)
        H[i][j] ^= mul(f, H[k + 1][j]);
      for (int r = 0; r < n; ++r)
        H[r][k + 1] ^= mul(f, H[r][i]);
    }
  }
  pol[0][0] = 1;
  for (int k = 1; k <= n; ++k) {
    fe prod = 1;
    for (int d = 0; d <= k; ++d)
      pol[k][d] = 0;
    for (int d = 0; d < k; ++d) {
      pol[k][d + 1] ^= pol[k - 1][d];
      pol[k][d] ^= mul(H[k - 1][k - 1], pol[k - 1][d]);
    }
    for (int i = 1; i <= k - 1; ++i) {
      prod = mul(prod, H[k - i][k - i - 1]);
      if (!prod)
        break;
      fe c = mul(H[k - i - 1][k - 1], prod);
      if (!c)
        continue;
      for (int d = 0; d <= k - i - 1; ++d)
        pol[k][d] ^= mul(c, pol[k - i - 1][d]);
    }
  }
  for (int d = 0; d <= n; ++d)
    g[d] = pol[n][d];
}

static fe poly_eval(const fe *poly, int deg, fe t) {
  fe acc = poly[deg];
  for (int i = deg - 1; i >= 0; --i)
    acc = (fe)(mul(acc, t) ^ poly[i]);
  return acc;
}

/* points grouped by the value of omega = basis[1] (the smallest non-constant
 * function) */
static int *wstart, *wlist;
static void build_omega_buckets(void) {
  free(wstart);
  free(wlist);
  wstart = calloc(FS + 2, sizeof(int));
  wlist = malloc(sizeof(int) * npts);
  for (int k = 0; k < npts; ++k)
    wstart[basis[1].val[k] + 1]++;
  for (int v = 0; v < FS; ++v)
    wstart[v + 1] += wstart[v];
  int *fill = malloc(sizeof(int) * (FS + 1));
  memcpy(fill, wstart, sizeof(int) * (FS + 1));
  for (int k = 0; k < npts; ++k)
    wlist[fill[basis[1].val[k]]++] = k;
  free(fill);
}

static int decode_fr(Result *R, int quiet) {
  static int Rr[MAXT], Cc[MAXT];
  static fe g[MAXT + 1];
  fe *xv = calloc(npts, sizeof(fe));
  int T_ = 0, nl, nloc = 0;
  double t0 = now();

  memset(R, 0, sizeof *R);
  int nrows = feng_rao_reduce();
  nl = count_basis_upto(L_DEG);
  for (int i = 0; i < nl; ++i)
    if (piv_of_row[i] < 0)
      ++nloc;
  for (int i = 0; i < nrows; ++i)
    if (piv_of_row[i] >= 0) {
      if (T_ >= MAXT - 1) {
        fprintf(stderr, "FR: too many pivots\n");
        R->failed = 1;
        free(xv);
        return -1;
      }
      Rr[T_] = i;
      Cc[T_] = piv_of_row[i];
      R->rowset[basis[i].rho] = 1;
      R->colset[basis[piv_of_row[i]].rho] = 1;
      ++T_;
    }
  R->T = T_;
  R->t_main = now() - t0;
  if (!quiet) {
    printf("# FR : %d error locators with rho <= %d\n", nloc, L_DEG);
    printf("# FR : staircase of %d elements -> estimated t = %d\n", T_, T_);
  }
  if (T_ == 0) {
    free(xv);
    return 0;
  }

  t0 = now();
  for (int a = 0; a < T_; ++a)
    for (int b = 0; b < T_; ++b)
      if (basis[Rr[a]].rho + basis[Cc[b]].rho + ASHIFT > M_SYND) {
        if (!quiet)
          puts("# FR : syndromes too short to form the shifted matrix.");
        R->failed = 1;
        free(xv);
        return -1;
      }
  for (int k = 0; k < nz_cnt; ++k)
    xv[nz_idx[k]] = basis[1].val[nz_idx[k]];
  for (int a = 0; a < T_; ++a)
    for (int b = 0; b < T_; ++b) {
      S0[a][b] = synd(Rr[a], Cc[b], NULL);
      SX[a][b] = synd(Rr[a], Cc[b], xv);
    }
  if (!mat_inverse(S0, S0inv, T_)) {
    if (!quiet)
      puts("# FR : S0 is singular (rank deficient).");
    R->failed = 1;
    free(xv);
    return -1;
  }
  for (int a = 0; a < T_; ++a)
    for (int b = 0; b < T_; ++b) {
      fe acc = 0;
      for (int k = 0; k < T_; ++k)
        acc ^= mul(S0inv[a][k], SX[k][b]);
      Qm[a][b] = acc;
    }
  charpoly(Qm, T_, g);
  int nfound = 0, overflow = 0, nroots = 0;
  for (int th = 0; th < FS; ++th) {
    if (poly_eval(g, T_, (fe)th) != 0)
      continue;
    nroots++;
    for (int q = wstart[th]; q < wstart[th + 1]; ++q) {
      int idx = wlist[q], vanish = 1;
      for (int i = 0; i < nl && vanish; ++i) {
        fe acc = 0;
        if (piv_of_row[i] >= 0)
          continue;
        for (int k = 0; k <= i; ++k)
          if (coefm[i][k])
            acc ^= mul(coefm[i][k], basis[k].val[idx]);
        if (acc)
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
  if (!quiet)
    printf("# FR : %d distinct roots (omega-values) in GF(2^%d)\n", nroots, FM);
  R->nfound = nfound;
  R->overflow = overflow;
  R->t_extract = now() - t0;
  resolve_and_store(R);
  free(xv);
  return 0;
}

/* ================= BMS (Sakata) with value vectors and majority voting
 * ================= */
typedef struct {
  int b, d;
  fe *f;
} Gen;
static Gen gens[MAXGEN];
static int ngen;
static fe *pivvec[SGMAX];
static fe pivd[SGMAX];
static uint8_t colused[SGMAX], is_piv[SGMAX];

static fe *vec_new(void) {
  fe *v = malloc(sizeof(fe) * npts);
  if (!v) {
    fprintf(stderr, "out of memory\n");
    exit(1);
  }
  return v;
}
static fe disc(const fe *f, int m) {
  const fe *ph = basis[idx_of_ord[m]].val;
  fe acc = 0;
  for (int n = 0; n < nz_cnt; ++n) {
    int k = nz_idx[n];
    acc ^= mul(recv[k], mul(f[k], ph[k]));
  }
  return acc;
}
static void vec_mul(fe *out, const fe *h, const fe *f) {
  for (int k = 0; k < npts; ++k)
    out[k] = mul(h[k], f[k]);
}
static void vec_axpy(fe *f, fe c, const fe *p) {
  for (int k = 0; k < npts; ++k)
    f[k] ^= mul(c, p[k]);
}

/* ---- majority voting machinery ---- */
static fe xhat[SGMAX];
static fe Bw[MAXGENUS][MAXB];
static int selp[MAXB];
static int nsel_dual;
static fe Aug[MAXB][MAXB + MAXGENUS];
static int lgrow[MAXB + MAXGENUS];

static int build_dual(void) {
  int *perm = malloc(sizeof(int) * npts);
  static fe bsol[MAXB];
  const int NB = nbasis, W = NB + GENUS;
  unsigned seed = 12345u;
  if (NB != M_SYND + 1 || basis[NB - GENUS].rho != M_SYND + 1) {
    fprintf(stderr,
            "dual basis: unexpected basis layout (need M >= conductor)\n");
    free(perm);
    return -1;
  }
  if (NB > npts) {
    fprintf(stderr, "dual basis: fewer points than basis functions\n");
    free(perm);
    return -1;
  }
  for (int attempt = 0; attempt < 8; ++attempt) {
    int singular = 0;
    for (int i = 0; i < npts; ++i)
      perm[i] = i;
    for (int i = 0; i < NB; ++i) {
      seed = seed * 1664525u + 1013904223u;
      int j = i + (int)((seed >> 8) % (unsigned)(npts - i));
      int t = perm[i];
      perm[i] = perm[j];
      perm[j] = t;
      selp[i] = perm[i];
    }
    nsel_dual = NB;
    for (int j = 0; j < NB; ++j) {
      for (int p = 0; p < NB; ++p)
        Aug[j][p] = basis[j].val[selp[p]];
      for (int v = 0; v < GENUS; ++v)
        Aug[j][NB + v] = (j == NB - GENUS + v) ? 1 : 0;
    }
    for (int c = 0; c < NB && !singular; ++c) {
      int p = -1;
      for (int r = c; r < NB; ++r)
        if (Aug[r][c]) {
          p = r;
          break;
        }
      if (p < 0) {
        singular = 1;
        break;
      }
      if (p != c)
        for (int k = 0; k < W; ++k) {
          fe t = Aug[p][k];
          Aug[p][k] = Aug[c][k];
          Aug[c][k] = t;
        }
      fe iv = inv(Aug[c][c]);
      for (int k = c; k < W; ++k)
        Aug[c][k] = mul(Aug[c][k], iv);
      for (int k = c + 1; k < W; ++k)
        lgrow[k] = Aug[c][k] ? (int)glog[Aug[c][k]] : -1;
#pragma omp parallel for schedule(static)
      for (int r = c + 1; r < NB; ++r) {
        fe f = Aug[r][c];
        fe *row = Aug[r];
        if (!f)
          continue;
        int lf = glog[f];
        for (int k = c + 1; k < W; ++k)
          if (lgrow[k] >= 0)
            row[k] ^= gexp[lf + lgrow[k]];
        row[c] = 0;
      }
    }
    if (singular)
      continue;
    for (int v = 0; v < GENUS; ++v) {
      for (int i = NB - 1; i >= 0; --i) {
        fe acc = Aug[i][NB + v];
        for (int k = i + 1; k < NB; ++k)
          if (Aug[i][k] && bsol[k])
            acc ^= mul(Aug[i][k], bsol[k]);
        bsol[i] = acc;
      }
      for (int i = 0; i < NB; ++i)
        Bw[v][i] = bsol[i];
    }
    free(perm);
    return 0;
  }
  fprintf(stderr, "dual basis: evaluation matrix singular\n");
  free(perm);
  return -1;
}

static int dual_selftest(void) {
  fe *coefv = malloc(sizeof(fe) * nbasis), *hs = malloc(sizeof(fe) * nbasis);
  for (int j = 0; j < nbasis; ++j)
    coefv[j] = (fe)(1 + rand() % FO);
  for (int p = 0; p < nsel_dual; ++p) {
    fe acc = 0;
    for (int j = 0; j < nbasis; ++j)
      acc ^= mul(coefv[j], basis[j].val[selp[p]]);
    hs[p] = acc;
  }
  int bad = 0;
  for (int v = 0; v < GENUS; ++v) {
    fe acc = 0;
    for (int p = 0; p < nsel_dual; ++p)
      acc ^= mul(Bw[v][p], hs[p]);
    if (acc != coefv[nbasis - GENUS + v])
      bad = 1;
  }
  free(coefv);
  free(hs);
  return bad ? -1 : 0;
}

/* branch-free GF multiply-accumulate in the log domain: zero is the log code
 * 2*FO, and the table E0 is 0 beyond 2*FO, so  E0[la + lb] = a*b  (0 if either
 * is zero).  LBw holds the logs of the dual rows Bw.                          */
static fe *E0;
static uint16_t (*LBw)[MAXB];
static void init_dual_logs(void) {
  E0 = calloc((size_t)4 * FO + 8, sizeof(fe));
  for (int k = 0; k < 2 * FO; ++k)
    E0[k] = gexp[k];
  LBw = calloc((size_t)MAXGENUS, sizeof *LBw);
  for (int v = 0; v < GENUS; ++v)
    for (int p = 0; p < nsel_dual; ++p)
      LBw[v][p] = Bw[v][p] ? glog[Bw[v][p]] : (uint16_t)(2 * FO);
}

/* ext_known results are cached per BMS step n (same function vector, same m):
 * the voting step and the discrepancy step ask for the same value. */
typedef struct {
  const fe *f;
  int m, n;
  fe known, an;
} ExtCache;
static ExtCache ecache[MAXGEN + 8];
static int necache, ecache_n = -1;

static fe ext_known(const fe *f, int m, int n, fe *an_out) {
  static fe hsel[MAXB];
  static uint16_t hl[MAXB];
  fe a[MAXGENUS + 1];
  const fe *ph = basis[idx_of_ord[m]].val;
  const fe *top[MAXGENUS + 1];
  const int nv = n - M_SYND;
  fe s = 0;
  if (ecache_n != n) {
    ecache_n = n;
    necache = 0;
  }
  for (int c = 0; c < necache; ++c)
    if (ecache[c].f == f && ecache[c].m == m) {
      *an_out = ecache[c].an;
      return ecache[c].known;
    }
  for (int p = 0; p < nsel_dual; ++p) {
    int k = selp[p];
    hsel[p] = mul(f[k], ph[k]);
    hl[p] = hsel[p] ? glog[hsel[p]] : (uint16_t)(2 * FO);
  }
  for (int v = 1; v <= nv; ++v) {
    const uint16_t *lb = LBw[v - 1];
    fe acc = 0;
    for (int p = 0; p < nsel_dual; ++p)
      acc ^= E0[hl[p] + lb[p]];
    a[v] = acc;
    top[v] = basis[idx_of_ord[M_SYND + v]].val;
  }
  for (int i = 0; i < nz_cnt; ++i) {
    int k = nz_idx[i];
    fe hv = mul(f[k], ph[k]);
    for (int v = 1; v <= nv; ++v)
      if (a[v])
        hv ^= mul(a[v], top[v][k]);
    s ^= mul(recv[k], hv);
  }
  for (int v = 1; v < nv; ++v)
    if (a[v])
      s ^= mul(a[v], xhat[M_SYND + v]);
  *an_out = a[nv];
  if (necache < MAXGEN + 8) {
    ecache[necache].f = f;
    ecache[necache].m = m;
    ecache[necache].n = n;
    ecache[necache].known = s;
    ecache[necache].an = a[nv];
    ++necache;
  }
  return s;
}
static fe xdisc(const fe *f, int m, int n) {
  fe an, known;
  if (n <= M_SYND)
    return disc(f, m);
  known = ext_known(f, m, n, &an);
  return (fe)(known ^ mul(an, xhat[n]));
}
static fe true_syndrome(int n) {
  const fe *ph = basis[idx_of_ord[n]].val;
  fe acc = 0;
  for (int i = 0; i < nz_cnt; ++i)
    acc ^= mul(recv[nz_idx[i]], ph[nz_idx[i]]);
  return acc;
}

/* ================================================================== */
/*  MONOMIAL SYNDROME TABLES (Newton polygon, NO dual basis)            */
/* ================================================================== */
/* All lattice points p=(i,j) of the cone {w_k.p>=0 (k!=e), pole order <= M+g}
 * are kept as monomials x^i y^j (there are only a few more than dim L((M+g)P)).
 * S(p) = sum_k e_k x_k^i y_k^j.  Pole orders <= M: S(p) is a parity check,
 * computed directly.  Above M: only the independent points ("reps", one per
 * pole order) are unknown (voted); a dependent point p = h + vA reduces via
 *      x^h * F = 0  :  S(h+vA) = S(h+vB) + sum_{other terms t} S(h+vt)
 * where vA, vB are the two terms of F on the pole edge (same pole order; the
 * other terms have strictly lower pole order).  So f is kept as a coefficient
 * vector over the lattice points: no evaluation, no dual basis, no elimination. */
static int use_poly = 0, use_poly_opt = 1;
static int NPT;
static int *pp_i, *pp_j, *pp_w, *pp_q, *pp_low, *pp_dep;
static int pp_nlow;
static int *pp_rep, *pp_ws, *pp_we, *pp_upto; /* by pole order 0..Mx */
static int pp_Mx;
static int pp_bi0, pp_bj0, pp_bw, pp_bh, *pp_box;
static fe *pp_S, *pp_lam, *pp_K;
static int *pivb;

static inline int pp_at(int i, int j) {
  i -= pp_bi0;
  j -= pp_bj0;
  if (i < 0 || i >= pp_bw || j < 0 || j >= pp_bh)
    return -1;
  return pp_box[(size_t)i * pp_bh + j];
}
typedef struct {
  int i, j, w, depth;
} PPt;
static int pp_cmp(const void *a, const void *b) {
  const PPt *x = a, *y = b;
  if (x->w != y->w)
    return x->w - y->w;
  if (x->depth != y->depth)
    return x->depth - y->depth;
  return x->i - y->i;
}

static int poly_setup(int e, int Mx, NBas *B) {
  /* 1. all lattice points of the cone */
  long ca[MAXEDGE + 1], cb[MAXEDGE + 1], ck[MAXEDGE + 1];
  int nc = 0;
  for (int k = 0; k < ne; ++k)
    if (k != e) {
      ca[nc] = ed[k].wx;
      cb[nc] = ed[k].wy;
      ck[nc] = 0;
      nc++;
    }
  ca[nc] = ed[e].wx;
  cb[nc] = ed[e].wy;
  ck[nc] = Mx;
  nc++;
  size_t cap = 1 << 14, n0 = 0;
  PPt *P = malloc(cap * sizeof *P);
  int bad = 0;
  if (hermitian_q > 0) {
    /*
     * Hermitian affine coordinate ring:
     *   y^q + y + x^(q+1) = 0.
     * Its regular one-point monomials are x^i y^j (i >= 0, j >= 0),
     * and y^q is reduced by y^q = y + x^(q+1).  The generic toric cone
     * also contains Laurent monomials (for example x^i/y), which are not
     * regular on the affine curve.  Enumerate the actual polynomial
     * semigroup instead of that larger toric cone.
     */
    const int q = hermitian_q;
    const int wx = q, wy = q + 1;
    for (int i = 0; i <= Mx / wx; ++i) {
      int jmax = (Mx - wx * i) / wy;
      for (int j = 0; j <= jmax; ++j) {
        if (n0 == cap) {
          cap *= 2;
          PPt *tmp = realloc(P, cap * sizeof *P);
          if (!tmp) { free(P); return -1; }
          P = tmp;
        }
        P[n0].i = i;
        P[n0].j = j;
        P[n0].w = wx * i + wy * j;
        P[n0].depth = 0;
        ++n0;
      }
    }
  } else {
    for (int dir = 0; dir < 2 && !bad; ++dir)
      for (int i = dir ? -1 : 0;; i += dir ? -1 : 1) {
        if (i > (1 << 20) || i < -(1 << 20)) {
          bad = 1;
          break;
        }
        long jl = -(1L << 40), jh = (1L << 40);
        double rl = -1e18, rh = 1e18;
        int empty = 0;
        for (int c = 0; c < nc && !empty; ++c) {
          long v = ca[c] * i + ck[c];
          if (cb[c] == 0) {
            if (v < 0)
              empty = 1;
          } else if (cb[c] > 0) {
            long l = -nb_fdiv(v, cb[c]);
            if (l > jl)
              jl = l;
            double r = -(double)v / (double)cb[c];
            if (r > rl)
              rl = r;
          } else {
            long h = nb_fdiv(v, -cb[c]);
            if (h < jh)
              jh = h;
            double r = (double)v / (double)(-cb[c]);
            if (r < rh)
              rh = r;
          }
        }
        if (empty || rl > rh + 1e-9)
          break;
        for (long j = jl; j <= jh; ++j) {
          int w = -(int)(ed[e].wx * (long)i + ed[e].wy * j);
          if (w < 0 || w > Mx) {
            bad = 1;
            break;
          }
          if (n0 == cap) {
            cap *= 2;
            PPt *tmp = realloc(P, cap * sizeof *P);
            if (!tmp) { free(P); return -1; }
            P = tmp;
          }
          P[n0].i = i;
          P[n0].j = (int)j;
          P[n0].w = w;
          P[n0].depth = 0;
          n0++;
        }
        if (bad)
          break;
      }
  }
  if (bad || n0 == 0) {
    free(P);
    return -1;
  }
  /* 2. the two terms of F on the pole edge */
  long vmin = 1L << 40;
  for (int s = 0; s < T; ++s) {
    long v = ed[e].wx * (long)TX[s] + ed[e].wy * (long)TY[s];
    if (v < vmin)
      vmin = v;
  }
  int tA = -1, tB = -1;
  for (int s = 0; s < T; ++s)
    if (ed[e].wx * (long)TX[s] + ed[e].wy * (long)TY[s] == vmin) {
      if (tA < 0)
        tA = s;
      else if (tB < 0)
        tB = s;
      else
        tA = -2;
    }
  if (tA < 0 || tB < 0 || T > MAXTERM) {
    free(P);
    return -1;
  }
  const int dx = TX[tB] - TX[tA], dy = TY[tB] - TY[tA];
  /* 3. box index (unsorted) */
  int imin = 1 << 30, imax = -(1 << 30), jmin = 1 << 30, jmax = -(1 << 30);
  for (size_t p = 0; p < n0; ++p) {
    if (P[p].i < imin) imin = P[p].i;
    if (P[p].i > imax) imax = P[p].i;
    if (P[p].j < jmin) jmin = P[p].j;
    if (P[p].j > jmax) jmax = P[p].j;
  }
  pp_bi0 = imin;
  pp_bj0 = jmin;
  pp_bw = imax - imin + 1;
  pp_bh = jmax - jmin + 1;
  if ((double)pp_bw * pp_bh > 2e8) {
    free(P);
    return -1;
  }
  pp_box = malloc(sizeof(int) * (size_t)pp_bw * pp_bh);
  for (size_t x = 0; x < (size_t)pp_bw * pp_bh; ++x)
    pp_box[x] = -1;
  for (size_t p = 0; p < n0; ++p)
    pp_box[(size_t)(P[p].i - imin) * pp_bh + (P[p].j - jmin)] = (int)p;
  /* 4. dependent points and chain depth */
  char *dep = calloc(n0, 1);
  int *nb = malloc(sizeof(int) * n0);
  for (size_t p = 0; p < n0; ++p) {
    int hi = P[p].i - TX[tA], hj = P[p].j - TY[tA], ok = 1;
    for (int s = 0; s < T && ok; ++s)
      if (pp_at(hi + TX[s], hj + TY[s]) < 0)
        ok = 0;
    dep[p] = ok;
    nb[p] = ok ? pp_at(P[p].i + dx, P[p].j + dy) : -1;
    P[p].depth = ok ? -1 : 0;
  }
  for (int changed = 1; changed;) {
    changed = 0;
    for (size_t p = 0; p < n0; ++p)
      if (dep[p] && P[p].depth < 0 && nb[p] >= 0 && P[nb[p]].depth >= 0) {
        P[p].depth = P[nb[p]].depth + 1;
        changed = 1;
      }
  }
  int ok = 1;
  for (size_t p = 0; p < n0; ++p)
    if (P[p].depth < 0)
      ok = 0;
  /* 5. exactly one independent point per pole order, M+1-g in total */
  int *cnt = calloc(Mx + 1, sizeof(int)), nrep = 0;
  for (size_t p = 0; p < n0 && ok; ++p)
    if (!dep[p]) {
      if (++cnt[P[p].w] > 1)
        ok = 0;
      nrep++;
    }
  if (nrep != Mx + 1 - genus_g)
    ok = 0;
  free(cnt);
  if (ok) { /* axis points: negative exponents need x,y != 0 positions */
    int laurent = 0;
    for (size_t p = 0; p < n0; ++p)
      if (P[p].i < 0 || P[p].j < 0)
        laurent = 1;
    if (laurent) {
      int tx0 = 0, ty0 = 0;
      for (int s = 0; s < T; ++s) {
        tx0 += (TX[s] == 0);
        ty0 += (TY[s] == 0);
      }
      if (tx0 > 1 || ty0 > 1)
        ok = 0;
    }
    B->laurent = laurent;
  }
  free(dep);
  free(nb);
  free(pp_box);
  if (!ok) {
    free(P);
    return -1;
  }
  /* 6. sort by (pole order, chain depth) and rebuild everything */
  qsort(P, n0, sizeof *P, pp_cmp);
  NPT = (int)n0;
  pp_i = malloc(sizeof(int) * n0);
  pp_j = malloc(sizeof(int) * n0);
  pp_w = malloc(sizeof(int) * n0);
  pp_q = malloc(sizeof(int) * n0);
  pp_dep = malloc(sizeof(int) * n0);
  pp_nlow = T - 2;
  pp_low = malloc(sizeof(int) * n0 * (pp_nlow > 0 ? pp_nlow : 1));
  pp_box = malloc(sizeof(int) * (size_t)pp_bw * pp_bh);
  for (size_t x = 0; x < (size_t)pp_bw * pp_bh; ++x)
    pp_box[x] = -1;
  for (size_t p = 0; p < n0; ++p) {
    pp_i[p] = P[p].i;
    pp_j[p] = P[p].j;
    pp_w[p] = P[p].w;
    pp_box[(size_t)(P[p].i - imin) * pp_bh + (P[p].j - jmin)] = (int)p;
  }
  pp_Mx = Mx;
  pp_rep = malloc(sizeof(int) * (Mx + 1));
  pp_ws = malloc(sizeof(int) * (Mx + 2));
  pp_we = malloc(sizeof(int) * (Mx + 2));
  pp_upto = malloc(sizeof(int) * (Mx + 2));
  for (int w = 0; w <= Mx; ++w) {
    pp_rep[w] = -1;
    pp_ws[w] = pp_we[w] = 0;
  }
  for (size_t p = 0; p < n0; ++p) {
    int hi = pp_i[p] - TX[tA], hj = pp_j[p] - TY[tA], isdep = 1;
    for (int s = 0; s < T; ++s)
      if (pp_at(hi + TX[s], hj + TY[s]) < 0)
        isdep = 0;
    pp_dep[p] = isdep;
    if (!isdep)
      pp_rep[pp_w[p]] = (int)p;
    else {
      pp_q[p] = pp_at(pp_i[p] + dx, pp_j[p] + dy);
      int c = 0;
      for (int s = 0; s < T; ++s)
        if (s != tA && s != tB)
          pp_low[p * pp_nlow + c++] = pp_at(hi + TX[s], hj + TY[s]);
    }
    if (pp_ws[pp_w[p]] == 0 && pp_we[pp_w[p]] == 0)
      pp_ws[pp_w[p]] = (int)p;
    pp_we[pp_w[p]] = (int)p + 1;
  }
  { int cum = 0;
    for (int w = 0; w <= Mx; ++w) {
      if (pp_we[w] > 0)
        cum = pp_we[w];
      pp_upto[w] = cum;
    } }
  /* 7. the basis = the independent points; B in pole-order order */
  for (int k = 0; k < B->n; ++k) {
    int r = pp_rep[B->rho[k]];
    if (r < 0) {
      free(P);
      return -1; /* cannot happen: same pole-order set */
    }
    B->ei[k] = pp_i[r];
    B->ej[k] = pp_j[r];
  }
  pp_S = calloc(n0, sizeof(fe));
  pp_lam = calloc(n0, sizeof(fe));
  pp_K = calloc(n0, sizeof(fe));
  pivb = calloc(SGMAX, sizeof(int));
  free(P);
  return 0;
}

/* syndromes of the received word: direct for pole order <= M, 0 above */
static void poly_syndromes(void) {
  for (int p = 0; p < NPT; ++p) {
    if (pp_w[p] > M_SYND) {
      pp_S[p] = 0;
      continue;
    }
    fe acc = 0;
    for (int z = 0; z < nz_cnt; ++z) {
      int k = nz_idx[z];
      acc ^= mul(recv[k], mono_eval(PXv[k], PYv[k], pp_i[p], pp_j[p]));
    }
    pp_S[p] = acc;
  }
}
/* relation check on the known range (dependent points <= M) */
static int poly_selfcheck(void) {
  int bad = 0, tested = 0;
  for (int p = 0; p < NPT; ++p)
    if (pp_dep[p] && pp_w[p] <= M_SYND) {
      fe v = pp_S[pp_q[p]];
      for (int c = 0; c < pp_nlow; ++c)
        v ^= pp_S[pp_low[p * pp_nlow + c]];
      tested++;
      if (v != pp_S[p])
        bad++;
    }
  (void)tested;
  return bad;
}
/* weight-n points: S(p) = lam*X_n + K, X_n the (unknown) syndrome of the rep */
static void poly_prepare(int n) {
  for (int p = pp_ws[n]; p < pp_we[n]; ++p) {
    if (!pp_dep[p]) {
      pp_lam[p] = 1;
      pp_K[p] = 0;
    } else {
      int q = pp_q[p];
      fe k = pp_K[q];
      for (int c = 0; c < pp_nlow; ++c)
        k ^= pp_S[pp_low[p * pp_nlow + c]];
      pp_lam[p] = pp_lam[q];
      pp_K[p] = k;
    }
  }
}
static void poly_finalize(int n, fe x) {
  for (int p = pp_ws[n]; p < pp_we[n]; ++p)
    pp_S[p] = (fe)(mul(pp_lam[p], x) ^ pp_K[p]);
}
static fe *vnew(void) {
  size_t n = (size_t)(npts > NPT ? npts : NPT);
  fe *v = calloc(n, sizeof(fe));
  if (!v) {
    fprintf(stderr, "out of memory\n");
    exit(1);
  }
  return v;
}
static inline int pp_shift(int p, int ri, int rj) {
  int t = pp_at(pp_i[p] + ri, pp_j[p] + rj);
  if (t < 0) {
    fprintf(stderr, "internal error: product leaves the lattice cone\n");
    exit(1);
  }
  return t;
}
/* out = x^(rep c) * f ,  f of pole order bsrc */
static void vmul_b(fe *out, int c, const fe *f, int bsrc) {
  if (!use_poly) {
    vec_mul(out, basis[idx_of_ord[c]].val, f);
    return;
  }
  int r = pp_rep[c], ri = pp_i[r], rj = pp_j[r];
  for (int p = 0; p < pp_upto[bsrc]; ++p)
    if (f[p])
      out[pp_shift(p, ri, rj)] = f[p];
}
static void vaxpy_b(fe *f, fe c, const fe *piv, int bpiv) {
  if (!use_poly) {
    vec_axpy(f, c, piv);
    return;
  }
  for (int p = 0; p < pp_upto[bpiv]; ++p)
    if (piv[p])
      f[p] ^= mul(c, piv[p]);
}
static fe poly_xdisc(const fe *f, int b, int m) {
  int r = pp_rep[m], ri = pp_i[r], rj = pp_j[r];
  fe acc = 0;
  for (int p = 0; p < pp_upto[b]; ++p)
    if (f[p])
      acc ^= mul(f[p], pp_S[pp_shift(p, ri, rj)]);
  return acc;
}
static fe poly_ext_known(const fe *f, int b, int m, int n, fe *an) {
  int r = pp_rep[m], ri = pp_i[r], rj = pp_j[r];
  fe known = 0, a = 0;
  for (int p = 0; p < pp_upto[b]; ++p)
    if (f[p]) {
      int t = pp_shift(p, ri, rj);
      if (pp_w[t] < n)
        known ^= mul(f[p], pp_S[t]);
      else {
        a ^= mul(f[p], pp_lam[t]);
        known ^= mul(f[p], pp_K[t]);
      }
    }
  *an = a;
  return known;
}
static fe ext_known_b(const fe *f, int b, int m, int n, fe *an) {
  return use_poly ? poly_ext_known(f, b, m, n, an) : ext_known(f, m, n, an);
}
static fe xdisc_b(const fe *f, int b, int m, int n) {
  if (use_poly)
    return poly_xdisc(f, b, m);
  return xdisc(f, m, n);
}
/* does the polynomial f (pole order b) not vanish at position k */
static int poly_nonzero(const fe *f, int b, int k) {
  fe acc = 0;
  for (int p = 0; p < pp_upto[b]; ++p)
    if (f[p])
      acc ^= mul(f[p], mono_eval(PXv[k], PYv[k], pp_i[p], pp_j[p]));
  return acc != 0;
}

static int vote_position(int n, Result *R, int verbose) {
  fe pred[MAXGEN], dv[MAXGEN];
  int validg[MAXGEN], dc[MAXGEN], nd = 0, ncand = 0;
  if (use_poly)
    poly_prepare(n);
  for (int g = 0; g < ngen; ++g) {
    int m = n - gens[g].b;
    validg[g] = (m >= 0 && in_H[m]);
    if (validg[g]) {
      fe an, known = ext_known_b(gens[g].f, gens[g].b, m, n, &an);
      if (!an) {
        fprintf(stderr, "vote: zero leading coefficient (n=%d)\n", n);
        return -1;
      }
      pred[g] = mul(known, inv(an));
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
  if (use_poly)
    poly_finalize(n, xhat[n]);
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
    printf("#   vote n=%d: %d candidates, %d predictions, winner %d votes, "
           "runner-up %d%s\n",
           n, ncand, nd, dc[best], second,
           right ? "  (= true syndrome)" : "  (WRONG)");
  return 0;
}

static void bms_cleanup(void);

/* ================= 純粋なFeng-Rao多数決復号 ==========================
 * 誤り位置消去イデアルは、Sakata/BMSの逐次更新ではなく、
 * Feng-Raoシンドローム行列の核（feng_rao_reduce）から構成する。
 * その最小半群生成元を使ってFeng-Rao多数決を行う。
 * Newton多項式シンドローム表現を必須とし、従来VOTEの補間双対基底は使わない。
 */
static int decode_fr_vote(Result *R, int verbose, int quiet) {
  double t0 = now();
  int nrows, nl, nsel = 0, nfound = 0, overflow = 0;
  int sel[MAXGEN];

  memset(R, 0, sizeof *R);
  R->vote_min_margin = 1 << 30;
  if (!use_poly) {
    fprintf(stderr,
            "FR-VOTE requires the Newton monomial syndrome path; "
            "enable it with the default Newton setup (do not use -nopoly/-nonewton).\n");
    R->failed = 1;
    return -1;
  }

  memset(xhat, 0, sizeof xhat);
  memset(is_piv, 0, sizeof is_piv);
  memset(colused, 0, sizeof colused);
  bms_cleanup();

  nrows = feng_rao_reduce();
  if (nrows < 0) {
    fprintf(stderr, "FR-VOTE: Feng-Rao reduction failed.\n");
    R->failed = 1;
    return -1;
  }
  nl = count_basis_upto(L_DEG);

  /* Feng-Rao簡約のピボット階段を半群次数の集合へ移す。 */
  for (int i = 0; i < nrows; ++i) {
    if (piv_of_row[i] >= 0) {
      int b = basis[i].rho;
      int c = basis[piv_of_row[i]].rho;
      if (b < SGMAX) {
        is_piv[b] = 1;
        R->rowset[b] = 1;
      }
      if (c < SGMAX) {
        colused[c] = 1;
        R->colset[c] = 1;
      }
      ++R->T;
    }
  }
  if (R->T == 0) {
    R->resolved = 1;
    R->t_main = now() - t0;
    return 0;
  }

  /* 非ピボット行は誤り位置消去関数になる。
   * Weierstrass半群で割り切れない最小生成元だけを残す。 */
  for (int b = 0; b <= L_DEG; ++b) {
    int i, minimal = 1;
    if (!in_H[b] || is_piv[b])
      continue;
    i = idx_of_ord[b];
    if (i < 0 || i >= nl || piv_of_row[i] >= 0)
      continue;
    for (int q = 0; q < ngenH; ++q) {
      int a = b - genH[q];
      if (a >= 0 && in_H[a] && !is_piv[a]) {
        minimal = 0;
        break;
      }
    }
    if (!minimal)
      continue;
    if (ngen >= MAXGEN) {
      fprintf(stderr, "FR-VOTE: too many locator generators.\n");
      R->failed = 1;
      bms_cleanup();
      return -1;
    }
    gens[ngen].b = b;
    gens[ngen].d = 0;
    gens[ngen].f = vnew();
    for (int k = 0; k <= i; ++k) {
      fe c = coefm[i][k];
      if (!c)
        continue;
      int z = pp_at(bas_ei[k], bas_ej[k]);
      if (z < 0 || z >= pp_upto[b]) {
        fprintf(stderr,
                "FR-VOTE: locator coefficient is outside Newton table "
                "(b=%d, basis=%d, index=%d).\n", b, k, z);
        R->failed = 1;
        bms_cleanup();
        return -1;
      }
      gens[ngen].f[z] ^= c;
    }
    ++ngen;
  }

  if (ngen == 0) {
    fprintf(stderr, "FR-VOTE: no locator generators were obtained from the FR kernel.\n");
    R->failed = 1;
    return -1;
  }

  /* 未知のg層のシンドロームをFeng-Rao多数決で順に復元する。 */
  for (int n = M_SYND + 1; n <= M_EXT; ++n) {
    if (vote_position(n, R, verbose) != 0) {
      R->failed = 1;
      bms_cleanup();
      return -1;
    }
  }
  R->t_main = now() - t0;

  /* Feng-Rao限界に従って必要な消去関数を選び、その共通零点を誤り位置とする。 */
  {
    int bmax = M_EXT - 2 * GENUS + 1 - R->T;
    for (int g = 0; g < ngen; ++g)
      if (gens[g].b <= bmax)
        sel[nsel++] = g;
  }
  if (!quiet) {
    printf("# FR-VOTE: %d FR-kernel locator generators, %d used (rho <= %d)\n",
           ngen, nsel, M_EXT - 2 * GENUS + 1 - R->T);
    printf("# FR-VOTE: staircase of %d elements; %d voted syndromes, "
           "smallest margin %d, %d wrong, %d ties\n",
           R->T, R->vote_steps, R->vote_min_margin,
           R->vote_wrong, R->vote_tie);
  }

  t0 = now();
  if (nsel == 0) {
    fprintf(stderr, "FR-VOTE: no locator generators satisfy the Feng-Rao bound.\n");
    R->failed = 1;
    bms_cleanup();
    return -1;
  }
  for (int k = 0; k < npts; ++k) {
    int vanish = 1;
    for (int q = 0; q < nsel && vanish; ++q)
      if (poly_nonzero(gens[sel[q]].f, gens[sel[q]].b, k))
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

static void bms_cleanup(void) {
  for (int g = 0; g < ngen; ++g)
    free(gens[g].f);
  ngen = 0;
  for (int m = 0; m < SGMAX; ++m) {
    free(pivvec[m]);
    pivvec[m] = NULL;
  }
}

static int bms_run(Result *R, int nmax, int verbose) {
  int T_ = 0;
  memset(colused, 0, sizeof colused);
  memset(is_piv, 0, sizeof is_piv);
  memset(pivvec, 0, sizeof pivvec);
  ngen = 1;
  gens[0].b = 0;
  gens[0].d = 0;
  gens[0].f = vnew();
  if (use_poly)
    gens[0].f[pp_at(0, 0)] = 1;
  else
    for (int k = 0; k < npts; ++k)
      gens[0].f[k] = 1;

  for (int n = 0; n <= nmax; ++n) {
    int anyfail = 0;
    if (n > M_SYND && vote_position(n, R, verbose) != 0)
      return -1;
    for (int g = 0; g < ngen; ++g) {
      int m = n - gens[g].b;
      gens[g].d = (m >= 0 && in_H[m]) ? xdisc_b(gens[g].f, gens[g].b, m, n) : 0;
      if (gens[g].d)
        anyfail = 1;
    }
    if (!anyfail)
      continue;
    for (int a = 0; a <= n; ++a) {
      int m = n - a, src = -1;
      if (!in_H[a] || is_piv[a] || !in_H[m] || colused[m])
        continue;
      for (int g = 0; g < ngen; ++g)
        if (gens[g].d && gens[g].b <= a && in_H[a - gens[g].b]) {
          src = g;
          break;
        }
      if (src < 0)
        continue;
      fe *f = vnew();
      vmul_b(f, a - gens[src].b, gens[src].f, gens[src].b);
      fe d = xdisc_b(f, a, m, n);
      if (!d) {
        fprintf(stderr, "BMS: internal error (zero pivot at n=%d)\n", n);
        free(f);
        return -1;
      }
      pivvec[m] = f;
      if (use_poly)
        pivb[m] = a;
      pivd[m] = d;
      colused[m] = 1;
      is_piv[a] = 1;
      R->rowset[a] = 1;
      R->colset[m] = 1;
      ++T_;
    }
    Gen ng[MAXGEN];
    uint8_t reused[MAXGEN];
    int nn = 0;
    memset(reused, 0, sizeof reused);
    for (int b = 0; b <= nmax; ++b) {
      int minimal = 1, og = -1;
      if (!in_H[b] || is_piv[b])
        continue;
      for (int s = 0; s < ngenH; ++s)
        if (b - genH[s] >= 0 && in_H[b - genH[s]] && !is_piv[b - genH[s]]) {
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
        ng[nn].f = vnew();
        vmul_b(ng[nn].f, b - gens[src].b, gens[src].f, gens[src].b);
        ng[nn].d = (m >= 0 && in_H[m]) ? xdisc_b(ng[nn].f, b, m, n) : 0;
      }
      {
        int m = n - ng[nn].b;
        if (m >= 0 && in_H[m] && ng[nn].d) {
          if (!colused[m] || !pivvec[m]) {
            fprintf(stderr, "BMS: inconsistent state (n=%d, b=%d)\n", n, b);
            return -1;
          }
          vaxpy_b(ng[nn].f, mul(ng[nn].d, inv(pivd[m])), pivvec[m], use_poly ? pivb[m] : 0);
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
  R->T = T_;
  return 0;
}

static int decode_bms(Result *R, int use_vote, int verbose, int quiet) {
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
  int bmax = use_vote ? Mtop - 2 * GENUS + 1 - R->T : L_DEG;
  int nsel = 0, sel[MAXGEN];
  for (int g = 0; g < ngen; ++g)
    if (gens[g].b <= bmax)
      sel[nsel++] = g;
  if (!quiet) {
    printf("# %-4s: %d generators of E, %d with rho <= %d\n", name, ngen, nsel,
           bmax);
    printf("# %-4s: staircase of %d elements -> estimated t = %d\n", name, R->T,
           R->T);
    if (use_vote)
      printf("# %-4s: %d voted syndromes, smallest margin %d, %d wrong (vs. "
             "simulated truth), %d ties\n",
             name, R->vote_steps, R->vote_min_margin, R->vote_wrong,
             R->vote_tie);
  }
  if (R->T == 0) {
    bms_cleanup();
    return 0;
  }
  t0 = now();
  int nfound = 0, overflow = 0;
  for (int k = 0; k < npts; ++k) {
    int vanish = nsel > 0;
    for (int s = 0; s < nsel && vanish; ++s)
      if (use_poly ? poly_nonzero(gens[sel[s]].f, gens[sel[s]].b, k)
                   : gens[sel[s]].f[k])
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

/* ---- error simulation / verification ---- */
static int true_pos[MAXT];
static fe true_val[MAXT];

static int verify(const char *name, const Result *R, int quiet) {
  int same = 0;
  if (R->failed) {
    if (!quiet)
      printf("# %-5s FAILED\n", name);
    return 0;
  }
  for (int m = 0; m < R->nfound; ++m)
    for (int e = 0; e < NUM_ERRORS; ++e)
      if (true_pos[e] == R->pos[m] && true_val[e] == R->val[m])
        ++same;
  int ok = !R->overflow && R->resolved && R->nfound == NUM_ERRORS &&
           same == NUM_ERRORS;
  if (!quiet)
    printf("# %-5s %d of %d errors recovered with the correct value, %d "
           "reported -> %s\n",
           name, same, NUM_ERRORS, R->nfound, ok ? "OK" : "MISMATCH");
  return ok;
}
static double total_time(const Result *R) {
  return R->t_main + R->t_extract + R->t_resolve;
}

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) {
  rng_s ^= rng_s << 13;
  rng_s ^= rng_s >> 7;
  rng_s ^= rng_s << 17;
  return rng_s;
}

/* draw NUM_ERRORS random errors; fills r (length npts), true_pos/true_val */
static void make_errors(fe *r) {
  memset(r, 0, sizeof(fe) * npts);
  for (int e = 0; e < NUM_ERRORS; ++e) {
    int p, dup;
    do {
      p = (int)(rnd() % (uint64_t)npts);
      dup = 0;
      for (int k = 0; k < e; ++k)
        if (true_pos[k] == p)
          dup = 1;
    } while (dup);
    true_pos[e] = p;
    do {
      r[p] = (fe)(rnd() % (uint64_t)FS);
    } while (!r[p]);
    true_val[e] = r[p];
  }
}
static void set_received(fe *r) {
  recv = r;
  nz_cnt = 0;
  for (int k = 0; k < npts; ++k)
    if (r[k])
      nz_idx[nz_cnt++] = k;
  if (use_poly) {
    static int checked = 0;
    poly_syndromes();
    if (!checked) {
      checked = 1;
      int bad = poly_selfcheck();
      if (bad)
        fprintf(stderr, "# WARNING: monomial relation self-check failed at %d "
                        "points\n", bad);
    }
  }
}

/* ================================================================== */
/*  multi-point codes: basic algorithm  S(h_a f_b) = sum_k e_k h_a f_b */
/* ================================================================== */
static int solve_values(const fe *VG, int rG, const fe *sigma, const int *Z,
                        int nz, fe *val) {
  int W = nz + 1;
  fe *A = malloc(sizeof(fe) * (size_t)rG * W);
  for (int s = 0; s < rG; ++s) {
    for (int c = 0; c < nz; ++c)
      A[(size_t)s * W + c] = VG[(size_t)s * npts + Z[c]];
    A[(size_t)s * W + nz] = sigma[s];
  }
  for (int c = 0; c < nz; ++c) {
    int p = -1;
    for (int a = c; a < rG; ++a)
      if (A[(size_t)a * W + c]) {
        p = a;
        break;
      }
    if (p < 0) {
      free(A);
      return 0;
    }
    if (p != c)
      for (int k = 0; k < W; ++k) {
        fe t = A[(size_t)p * W + k];
        A[(size_t)p * W + k] = A[(size_t)c * W + k];
        A[(size_t)c * W + k] = t;
      }
    fe iv = inv(A[(size_t)c * W + c]);
    for (int k = c; k < W; ++k)
      A[(size_t)c * W + k] = mul(A[(size_t)c * W + k], iv);
#pragma omp parallel for schedule(static)
    for (int a = 0; a < rG; ++a) {
      fe f = A[(size_t)a * W + c];
      if (a == c || !f)
        continue;
      for (int k = c; k < W; ++k)
        A[(size_t)a * W + k] ^= mul(f, A[(size_t)c * W + k]);
    }
  }
  for (int a = nz; a < rG; ++a)
    if (A[(size_t)a * W + nz]) {
      free(A);
      return 0;
    }
  for (int c = 0; c < nz; ++c)
    val[c] = A[(size_t)c * W + nz];
  free(A);
  return 1;
}

/* ---- what parameters does this build / this curve handle? ---- */
static int limit_Mmax(int g, int n) {
  int mm = n - g - 2; /* M+g <= n-2: injective evaluation, one point may be dropped */
  if (mm > MAXB - 2)
    mm = MAXB - 2; /* basis array holds M+1 functions */
  return mm;
}
static void print_limits(int g, int n, int t) {
  int Mmax = limit_Mmax(g, n), cap = MAXT - 2;
  puts("# ---- parameter limits (this build, this curve) ----");
  printf("#   field GF(2^m): m <= 11;  here g = %d, n = %d positions, build "
         "caps: MAXB = %d, MAXT = %d\n",
         g, n, MAXB, MAXT);
  if (Mmax < 2 * g) {
    printf("#   NOT decodable here: needs M >= 2g = %d but M <= %d  (n must be "
           "> 3g+1 = %d and MAXB >= 3g+3)\n",
           2 * g, Mmax, 3 * g + 1);
    return;
  }
  int tb = (Mmax - 3 * g + 1) / 2, tv = (Mmax - 2 * g + 1) / 2;
  if (tb > cap)
    tb = cap;
  if (tv > cap)
    tv = cap;
  printf("#   syndrome bound M: %d .. %d\n", 2 * g, Mmax);
  printf("#   max errors at M = %d:  basic FR/BMS %d,  majority voting %d  "
         "(designed bounds)\n",
         Mmax, tb < 0 ? 0 : tb, tv);
  int Mb = 2 * t + 3 * g - 1, Mv = 2 * t + 2 * g;
  printf("#   for t = %d errors: needs M >= %d (FR/BMS) %s, M >= %d (voting) "
         "%s%s\n",
         t, Mb, Mb <= Mmax ? "[OK]" : "[too large]", Mv,
         Mv <= Mmax ? "[OK]" : "[too large]",
         t > cap ? "  [t exceeds MAXT-2]" : "");
}

static void usage(void) {
  puts(
      "ag_frvote [options] [seed]\n"
      "  --m m            base field GF(2^m), m <= 11            (default 6)\n"
      "  --poly 0x43      primitive polynomial of GF(2^m)       (default: "
      "standard)\n"
      "  --curve bbgs|hermitian  select a built-in curve family (default bbgs)\n"
      "  --q auto|2|4|8   family parameter q (power of 2)\n"
      "auto: q^3 = 2^m if m%3==0, else q=4\n"
      "  --terms \"16,0;0,1;15,4;12,16\"   custom X-monic curve instead (X^i "
      "Y^j, optionally \"i,j,coef\"); X-monic\n"
      "  --errors t       number of injected errors              (default "
      "256)\n"
      "  --M M            syndrome bound / pole order (default 2t+2g)\n"
      "  --len L | -half  puncture: use only the first L points (or half of "
      "them) as positions\n"
      "  --place k        pole place (index from the list); default: automatic "
      "choice\n"
      "  --pole \"E2:140,E1:85\" or \"#3:100\"   multi-point divisor (E<k>: "
      "edge, #k: orbit)\n"
      "  -fr -bms -vote   one-point decoders to run (default: all)\n"
      "  -frvote          pure Feng-Rao majority voting (Newton path; no BMS, no dual basis)\n"
      "  -strict          skip FR/BMS when t exceeds the basic bound tau (default: run them anyway)\n"
      "  -limits          print the parameter limits of this build/curve and exit\n"
      "  -basic           (multi-point) basic algorithm\n"
      "  -allplaces       one-point: also evaluate the slow (Laurent-expansion) places and keep the best d_FR\n"
      "  -nonewton        one-point: build the basis by Laurent expansions (old, slow) instead of the Newton polygon\n"
      "  --place k        also avoids probing every candidate place (saves "
      "setup time)\n"
      "  -n N             N random trials (summary only)       -v  votes     "
      "-list  only list places");
}

int ag_frvote_run(int argc, char **argv) {
  const char *terms = "16,0;0,1;15,4;12,16", *polespec = NULL;
  const char *curve_name = "bbgs";
  int len_req = -1, half = 0, q_req = -1, terms_set = 0, m_bits = 6, Mreq = -1,
      place_req = -1, trials = 1, verbose = 0, only_list = 0, Jstep = 16,
      Jmax = 700;
  unsigned poly = 0, seed = 1;
  int run_fr = 1, run_bms = 1, run_vote = 1, run_frvote = 0, only = 0, nerr = 256, force = 1;
  for (int i = 1; i < argc; ++i) {
    { /* accept --force / --fr / --bms / --vote / --basic / --list as well as
         -force ... */
      static const char *flags[] = {"half",  "force", "fr", "bms", "vote", "frvote",
                                    "basic", "list",  "v",  "nonewton", "allplaces", "strict", "limits", "nopoly", NULL};
      if (argv[i][0] == '-' && argv[i][1] == '-')
        for (int f = 0; flags[f]; ++f)
          if (!strcmp(argv[i] + 2, flags[f])) {
            argv[i]++;
            break;
          }
    }
    if (!strcmp(argv[i], "--curve") && i + 1 < argc)
      curve_name = argv[++i];
    else if (!strcmp(argv[i], "--m") && i + 1 < argc)
      m_bits = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--poly") && i + 1 < argc)
      poly = (unsigned)strtoul(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "--terms") && i + 1 < argc) {
      terms = argv[++i];
      terms_set = 1;
    } else if (!strcmp(argv[i], "--len") && i + 1 < argc)
      len_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--q") && i + 1 < argc) {
      ++i;
      q_req = strcmp(argv[i], "auto") ? atoi(argv[i]) : -1;
    } else if (!strcmp(argv[i], "--errors") && i + 1 < argc)
      nerr = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--M") && i + 1 < argc)
      Mreq = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--place") && i + 1 < argc)
      place_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--pole") && i + 1 < argc)
      polespec = argv[++i];
    else if (!strcmp(argv[i], "--Jstep") && i + 1 < argc)
      Jstep = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--Jmax") && i + 1 < argc)
      Jmax = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-n") && i + 1 < argc)
      trials = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-v"))
      verbose = 1;
    else if (!strcmp(argv[i], "-list"))
      only_list = 1;
    else if (!strcmp(argv[i], "-force"))
      force = 1;
    else if (!strcmp(argv[i], "-strict"))
      force = 0;
    else if (!strcmp(argv[i], "-nopoly"))
      use_poly_opt = 0;
    else if (!strcmp(argv[i], "-limits"))
      only_list = 1;
    else if (!strcmp(argv[i], "-nonewton"))
      use_newton = 0;
    else if (!strcmp(argv[i], "-allplaces"))
      allplaces = 1;
    else if (!strcmp(argv[i], "-half"))
      half = 1;
    else if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage();
      return 0;
    } else if (!strcmp(argv[i], "-fr") || !strcmp(argv[i], "-bms") ||
               !strcmp(argv[i], "-vote") || !strcmp(argv[i], "-frvote") ||
               !strcmp(argv[i], "-basic")) {
      if (!only)
        run_fr = run_bms = run_vote = run_frvote = 0;
      only = 1;
      if (!strcmp(argv[i], "-fr"))
        run_fr = 1;
      else if (!strcmp(argv[i], "-bms"))
        run_bms = 1;
      else if (!strcmp(argv[i], "-vote"))
        run_vote = 1;
      else if (!strcmp(argv[i], "-frvote"))
        run_frvote = 1;
    } else if (argv[i][0] == '-') {
      fprintf(stderr, "unknown option: %s  (see --help)\n", argv[i]);
      return 1;
    } else
      seed = (unsigned)strtoul(argv[i], NULL, 10);
  }
  if (api_mode && (polespec != NULL || !run_frvote || run_fr || run_bms || run_vote)) {
    fprintf(stderr, "API mode supports only one-point Newton FR-VOTE; use -frvote alone and do not set --pole.\n");
    return 1;
  }
  if (m_bits < 1 || m_bits > 11) {
    fprintf(stderr, "--m must be in 1..11\n");
    return 1;
  }
  if (!poly) {
    static const unsigned dp[12] = {0,    3,    7,     0xB,   0x13,  0x25,
                                    0x43, 0x89, 0x11D, 0x211, 0x409, 0x805};
    poly = dp[m_bits];
  }
  if (gf_init(m_bits, poly) != 0) {
    fprintf(stderr, "polynomial 0x%X is not primitive of degree %d\n", poly,
            m_bits);
    return 1;
  }
  rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
  for (int i = 0; i < 8; ++i)
    rnd();
  srand(seed);

  /* ---- curve family ----
   * F(X,Y)=0 is stored as a sparse polynomial.  Both built-in families are
   * handled by the same point enumerator, Newton-polygon code and FR-VOTE.
   */
  static char tbuf[160];
  int qfam = 0;
  if (!terms_set) {
    int q = q_req;
    if (q < 0)
      q = (m_bits % 3 == 0) ? (1 << (m_bits / 3)) : 4;
    if (q < 2 || (q & (q - 1))) {
      fprintf(stderr, "--q must be a power of 2 (>= 2)\n");
      return 1;
    }
    if (!strcmp(curve_name, "hermitian")) {
      /* Hermitian: Y^q + Y + X^(q+1) = 0. */
      snprintf(tbuf, sizeof tbuf, "0,%d;%d,0;0,1", q, q + 1);
      terms = tbuf;
      hermitian_q = q;
      printf("# Hermitian curve: Y^%d + Y + X^%d = 0 (q=%d)\n", q, q + 1, q);
    } else if (!strcmp(curve_name, "bbgs")) {
      /* BBGS family used by the original implementation. */
      snprintf(tbuf, sizeof tbuf, "%d,0;0,1;%d,%d;%d,%d", q * q, q * q - 1, q,
               q * q - q, q * q);
      terms = tbuf;
      qfam = q;
      printf("# BBGS curve: X^%d + Y + X^%d Y^%d + X^%d Y^%d = 0 (q=%d)\n",
             q*q, q*q-1, q, q*q-q, q*q, q);
    } else {
      fprintf(stderr, "--curve must be bbgs or hermitian (or use --terms)\n");
      return 1;
    }
  }
  {
    char *s = strdup(terms), *tok = strtok(s, ";");
    while (tok) {
      int a, b, c = 1;
      int k = sscanf(tok, "%d,%d,%d", &a, &b, &c);
      if (k < 2) {
        fprintf(stderr, "--terms: \"i,j[,coef];...\"\n");
        return 1;
      }
      if (c <= 0 || c >= FS) {
        fprintf(stderr, "coefficient out of range\n");
        return 1;
      }
      TX[T] = a;
      TY[T] = b;
      TC[T] = (fe)c;
      T++;
      tok = strtok(NULL, ";");
    }
  }
  dx_deg = 0;
  for (int t = 0; t < T; ++t)
    if (TX[t] > dx_deg)
      dx_deg = TX[t];
  {
    int top = 0, pure = 0;
    for (int t = 0; t < T; ++t)
      if (TX[t] == dx_deg) {
        top++;
        if (TY[t] == 0)
          pure = 1;
      }
    if (top != 1 || !pure) {
      fprintf(stderr, "only curves that are monic in X are supported (swap X "
                      "and Y in --terms)\n");
      return 1;
    }
  }
  genus_g = build_edges();
  int ng_orb = ne_inf_orbits();
  GENUS = genus_g;
  double ts = now();
  enumerate_points();
  int nfull = npts;
  if (half)
    len_req = npts / 2;
  else if (len_req < 0 && npts > 8192) {
    len_req = 8192; /* default code length cap (override with --len) */
    printf("# code length capped at 8192 (use --len L to change)\n");
  }
  if (len_req > 0 && len_req < npts)
    npts = len_req; /* puncturing: keep the first points only */
  printf("# curve over GF(2^%d) [poly 0x%X]: X-degree %d, genus g = %d, n = %d "
         "affine rational points\n",
         FM, FM ? poly : 0, dx_deg, genus_g, nfull);
  if (npts != nfull)
    printf("# punctured: only the first %d of %d points are used as code "
           "positions\n",
           npts, nfull);
  for (int k = 0; k < ne; ++k)
    printf("#   edge E%d: from (%d,%d) dir (%d,%d) length %d  w=(%d,%d) %s\n",
           k, ed[k].vx, ed[k].vy, ed[k].ex, ed[k].ey, ed[k].len, ed[k].wx,
           ed[k].wy, ed[k].inf ? "[infinity]" : "[affine side]");
  int nrat = 0, ratidx[MAXORB];
  for (int q = 0; q < ng_orb; ++q) {
    printf("#   place #%d: edge E%d, degree %d (%s)\n", q, pl[q].edge, pl[q].d,
           pl[q].d == 1 ? "rational" : "Galois orbit");
    if (pl[q].d == 1)
      ratidx[nrat++] = q;
  }
  if (qfam) {
    long long nopt = 1 + ((long long)qfam * qfam * qfam - 1) * qfam * qfam;
    if ((long long)qfam * qfam * qfam == (long long)FS)
      printf("# GF(2^%d) = GF(q^3): maximal-structure point count 1 + (q^3-1) "
             "q^2 = %lld, found n = %d%s\n",
             FM, nopt, nfull, nopt == nfull ? "  (matches)" : "  (differs)");
    else
      printf("# note: 2^%d != q^3, so the q = %d curve has no special point "
             "structure here\n",
             FM, qfam);
  }
  print_limits(GENUS, npts, nerr);
  if (only_list)
    return 0;
  /*
  if (GENUS > MAXGENUS - 1 || 2 * GENUS + 2 > MAXB - GENUS) {
      fprintf(stderr, "# genus g = %d: decoding needs M >= 2g = %d syndromes (>
  this build's limit: g <= %d).\n"
                      "# The dense linear algebra of this program is not
  feasible at this size; -list works, decoding does not.\n", GENUS, 2 * GENUS,
  MAXGENUS - 1); return 1;
  }
  */

  NUM_ERRORS = nerr;
  if (nerr < 1 || nerr > MAXT - 2) {
    fprintf(stderr, "--errors out of range (1..%d)\n", MAXT - 2);
    return 1;
  }
  int mult[MAXORB];
  memset(mult, 0, sizeof mult);

  /* ===================== choose the code ===================== */
  int multi = (polespec != NULL);
  int nvirt = 0;
  if (use_newton)
    for (int k = 0; k < ne; ++k)
      if (!ed[k].inf && ed[k].len == 1)
        nvirt++;
  if (!multi && nrat == 0 && nvirt == 0) {
    multi = 1;
    printf("# no rational place at infinity: no one-point code with a pole at "
           "a rational point on this model.\n"
           "# fallback: multi-point divisor supported on the lowest-degree "
           "Galois orbit, decoded by the basic algorithm.\n");
  }
  if (multi) {
    /* ---------- multi-point: basic algorithm ---------- */
    int degG = 0;
    if (polespec) {
      char *s = strdup(polespec), *tok = strtok(s, ",");
      while (tok) {
        int id, mm;
        if (sscanf(tok, "E%d:%d", &id, &mm) == 2) {
          if (id < 0 || id >= ne || !ed[id].inf) {
            fprintf(stderr, "E%d is not an edge at infinity\n", id);
            return 1;
          }
          for (int q = 0; q < ng_orb; ++q)
            if (pl[q].edge == id)
              mult[q] = mm;
        } else if (sscanf(tok, "#%d:%d", &id, &mm) == 2) {
          if (id < 0 || id >= ng_orb) {
            fprintf(stderr, "no place #%d\n", id);
            return 1;
          }
          mult[id] = mm;
        } else {
          fprintf(stderr, "--pole: \"E1:10,#3:5\"\n");
          return 1;
        }
        tok = strtok(NULL, ",");
      }
    } else {
      int best = 0;
      for (int q = 1; q < ng_orb; ++q)
        if (pl[q].d < pl[best].d)
          best = q;
      int need = 2 * nerr + 3 * GENUS + 4;
      mult[best] = (need + pl[best].d - 1) / pl[best].d;
    }
    for (int q = 0; q < ng_orb; ++q)
      degG += mult[q] * pl[q].d;
    int need = 2 * nerr + 3 * GENUS - 1;
    printf("# multi-point divisor G: deg G = %d, designed distance >= %d; "
           "basic algorithm needs deg G >= %d for t = %d\n",
           degG, degG - 2 * GENUS + 2, need, nerr);
    if (degG < need) {
      fprintf(
          stderr,
          "deg G too small for %d errors with the basic algorithm (tau = %d)\n",
          nerr, (degG - 3 * GENUS + 1) / 2);
      return 1;
    }
    /* split G = F + H with deg F >= t+g and deg H >= t+2g-1 */
    int lo = nerr + GENUS, hi = degG - nerr - 2 * GENUS + 1,
        target = (lo + hi) / 2;
    int fm[MAXORB], hm[MAXORB], degF = 0;
    for (int q = 0; q < ng_orb; ++q) {
      fm[q] = (int)(((long long)mult[q] * target + degG / 2) / degG);
      if (fm[q] > mult[q])
        fm[q] = mult[q];
      degF += fm[q] * pl[q].d;
    }
    for (int tries = 0; tries < 400 && (degF < lo || degF > hi); ++tries) {
      int q = tries % ng_orb;
      if (degF < lo && fm[q] < mult[q]) {
        fm[q]++;
        degF += pl[q].d;
      } else if (degF > hi && fm[q] > 0) {
        fm[q]--;
        degF -= pl[q].d;
      }
    }
    for (int q = 0; q < ng_orb; ++q)
      hm[q] = mult[q] - fm[q];
    if (degF < lo || degF > hi) {
      fprintf(stderr,
              "could not split G into F + H (deg F = %d, need %d..%d)\n", degF,
              lo, hi);
      return 1;
    }
    printf("# splitting G = F + H: deg F = %d (>= t+g = %d), deg H = %d (>= "
           "t+2g-1 = %d)\n",
           degF, lo, degG - degF, nerr + 2 * GENUS - 1);
    LSp LG, LF, LH;
    double t0 = now();
    if (solve_L(mult, -1, Jstep, Jmax, 0, &LG) != 0)
      fprintf(stderr, "warning: L(G) not certified\n");
    solve_L(fm, -1, Jstep, Jmax, 0, &LF);
    solve_L(hm, -1, Jstep, Jmax, 0, &LH);
    printf("# dim L(G) = %d, dim L(F) = %d, dim L(H) = %d  (%.2f s)\n", LG.dim,
           LF.dim, LH.dim, now() - t0);
    fe *VG = eval_space(&LG), *VF = eval_space(&LF), *VH = eval_space(&LH);
    int rG = LG.dim, dF = LF.dim, dH = LH.dim;
    fe *R0 = malloc(sizeof(fe) * (size_t)npts * rG);
    if (right_inverse(VG, rG, npts, R0) != 0) {
      fprintf(stderr, "evaluation of L(G) is not injective: deg G >= n?\n");
      return 1;
    }
    printf("# code: n = %d, check rows = %d, k = %d, designed distance >= %d, "
           "setup %.2f s\n",
           npts, rG, npts - rG, degG - 2 * GENUS + 2, now() - ts);
    fe *r = malloc(sizeof(fe) * npts), *sigma = malloc(sizeof(fe) * rG),
       *estar = malloc(sizeof(fe) * npts);
    fe *Mt = malloc(sizeof(fe) * (size_t)dH * dF),
       *ae = malloc(sizeof(fe) * npts);
    int okc = 0;
    for (int tr = 0; tr < trials; ++tr) {
      make_errors(r);
      double t1 = now();
      for (int s = 0; s < rG; ++s) {
        fe acc = 0;
        for (int e = 0; e < NUM_ERRORS; ++e)
          acc ^= mul(true_val[e], VG[(size_t)s * npts + true_pos[e]]);
        sigma[s] = acc;
      }
      for (int k = 0; k < npts; ++k) {
        fe acc = 0;
        for (int s = 0; s < rG; ++s)
          if (sigma[s] && R0[(size_t)k * rG + s])
            acc ^= mul(R0[(size_t)k * rG + s], sigma[s]);
        estar[k] = acc;
      }
      for (int a = 0; a < dF; ++a) {
        for (int k = 0; k < npts; ++k)
          ae[k] = mul(estar[k], VF[(size_t)a * npts + k]);
        for (int b = 0; b < dH; ++b)
          Mt[(size_t)b * dF + a] = dotv(ae, VH + (size_t)b * npts, npts);
      }
      fe *ker;
      int kd = nullspace_gf(Mt, dH, dF, &ker);
      int *Z = malloc(sizeof(int) * npts), nz = 0;
      for (int k = 0; k < npts; ++k)
        Z[nz++] = k;
      for (int v = 0; v < kd && nz > 0; ++v) {
        int nn = 0;
        for (int zi = 0; zi < nz; ++zi) {
          int k = Z[zi];
          fe acc = 0;
          for (int a = 0; a < dF; ++a)
            if (ker[(size_t)v * dF + a])
              acc ^= mul(ker[(size_t)v * dF + a], VF[(size_t)a * npts + k]);
          if (!acc)
            Z[nn++] = k;
        }
        nz = nn;
      }
      free(ker);
      fe *val = malloc(sizeof(fe) * (nz + 1));
      int ok = 0, nfound = 0;
      if (nz > 0 && nz <= MAXT && solve_values(VG, rG, sigma, Z, nz, val)) {
        int same = 0;
        for (int c = 0; c < nz; ++c)
          if (val[c]) {
            nfound++;
            for (int e = 0; e < NUM_ERRORS; ++e)
              if (true_pos[e] == Z[c] && true_val[e] == val[c])
                same++;
          }
        ok = (same == NUM_ERRORS && nfound == NUM_ERRORS);
      }
      okc += ok;
      if (trials == 1 || verbose)
        printf("# BASIC trial %d: %d kernel vectors of dim L(F) = %d, %d "
               "common zeros, %d errors reported -> %s (%.2f s)\n",
               tr + 1, kd, dF, nz, nfound, ok ? "OK" : "FAILED", now() - t1);
      free(Z);
      free(val);
    }
    printf("# BASIC: %d of %d trials decoded %d errors correctly\n", okc,
           trials, NUM_ERRORS);
    return okc == trials ? 0 : 1;
  }

  /* ---------- one-point codes ---------- */
  int M = Mreq;
  if (M <= 0) {
    /* default: the smallest M for which FR/BMS (basic bound) AND voting all
     * correct nerr errors; if that does not fit, the voting minimum */
    int Mb = 2 * nerr + 3 * GENUS - 1;
    if (Mb <= limit_Mmax(GENUS, npts))
      M = Mb;
    else {
      M = 2 * nerr + 2 * GENUS;
      printf("# M = %d (voting minimum): the basic bound would need M = %d, "
             "which does not fit; FR/BMS will be run beyond their proven "
             "bound\n",
             M, Mb);
    }
  }
  if (M < 2 * GENUS)
    M = 2 * GENUS;
  M_SYND = M;
  M_EXT = M + GENUS;
  TAU = (M - 3 * GENUS + 1) / 2;
  TAU_V = (M - 2 * GENUS + 1) / 2;
  /* FR-VOTE needs locator functions through the voting radius, not the
   * smaller basic-decoding radius used by FR/BMS. */
  L_DEG = (run_frvote ? TAU_V : TAU) + GENUS;
  if (M + 1 > MAXB - 1) {
    fprintf(stderr, "M too large for this build\n");
    print_limits(GENUS, npts, nerr);
    return 1;
  }
  if (nerr > TAU_V) {
    fprintf(stderr,
            "%d errors exceed tau_vote = %d for M = %d (need M >= %d)\n", nerr,
            TAU_V, M, 2 * nerr + 2 * GENUS);
    print_limits(GENUS, npts, nerr);
    return 1;
  }
  printf("# one-point code: M = %d, g = %d, basic algorithm t <= %d, with "
         "majority voting t <= %d\n",
         M, GENUS, TAU, TAU_V);
  if (npts <= M_EXT) {
    fprintf(stderr,
            "# the curve has only n = %d rational points, but M + g = %d >= n: "
            "the evaluation map is not injective.\n"
            "# Use a larger field (--m) or a smaller M/number of errors (need "
            "n > M + g).\n",
            npts, M_EXT);
    print_limits(GENUS, npts, nerr);
    return 1;
  }

  /* Candidate poles.  Pass 0: places whose L(MP) the NEWTON POLYGON gives
   * directly (any edge of lattice length 1 = a single rational place; this
   * includes the affine-side edge, e.g. the origin).  Pass 1 (only if pass 0
   * found nothing, or -allplaces / --place asks for it): rational places at
   * infinity whose basis needs exact Laurent expansions (slow). */
  LSp Lc[NCAND_MAX];
  int *pv[NCAND_MAX];
  NBas NB[NCAND_MAX];
  int via_newton[NCAND_MAX];
  memset(via_newton, 0, sizeof via_newton);
  memset(NB, 0, sizeof NB);
  int best = -1, bestdfr = -1, besta = 1 << 30;
  int cand[NCAND_MAX], ncand = 0;
  if (place_req >= 0) {
    if (place_req < ng_orb && pl[place_req].d == 1)
      cand[ncand++] = place_req;
    else
      printf("# requested place #%d is not a rational place at infinity -> "
             "searching for a substitute\n",
             place_req);
  }
  if (ncand == 0) {
    for (int i = 0; i < nrat; ++i)
      cand[ncand++] = ratidx[i];
    if (use_newton)
      for (int k = 0; k < ne; ++k)
        if (!ed[k].inf && ed[k].len == 1)
          cand[ncand++] = MAXORB + k;
  }
  printf("# candidate poles: %d\n", ncand);
  for (int pass = 0; pass < 2; ++pass) {
    if (pass == 1 && !(best < 0 || allplaces))
      break;
    for (int ci = 0; ci < ncand; ++ci) {
      int id = cand[ci], virt = id >= MAXORB;
      double t0 = now();
      int dimq = 0, nconst = 1;
      const int *rhos = NULL;
      if (pass == 0) {
        int e = virt ? id - MAXORB : pl[id].edge;
        if (!use_newton || newton_basis(e, M_EXT, &NB[id]) != 0)
          continue;
        via_newton[id] = 1;
        dimq = NB[id].n;
        rhos = NB[id].rho;
      } else {
        if (virt || via_newton[id])
          continue;
        int mm[MAXORB];
        memset(mm, 0, sizeof mm);
        mm[id] = M_EXT;
        Lc[id].B = NULL;
        if (solve_L(mm, -1, Jstep, Jmax, 0, &Lc[id]) != 0) {
          printf("#   place #%d: L(%dP) not certified, skipped\n", id, M_EXT);
          Lc[id].B = NULL;
          continue;
        }
        pv[id] = malloc(sizeof(int) * Lc[id].dim);
        nconst = semigroup_echelon(&Lc[id], &pl[id], M_EXT, pv[id]);
        dimq = Lc[id].dim;
        rhos = pv[id];
      }
      static int inHt[SGMAX];
      memset(inHt, 0, sizeof inHt);
      for (int x = M_EXT + 1; x < SGMAX; ++x)
        inHt[x] = 1;
      for (int d = 0; d < dimq; ++d)
        inHt[rhos[d]] = 1;
      int ngaps = 0;
      for (int x = 1; x <= M_EXT; ++x)
        if (!inHt[x])
          ngaps++;
      int a1 = 1 << 30;
      for (int x = 1; x <= M_EXT; ++x)
        if (inHt[x]) {
          a1 = x;
          break;
        }
      int span = SGMAX - M - 2;
      if (span > 400)
        span = 400;
      int dfr = dfr_of(inHt, M, span);
      char lab[64];
      if (virt)
        snprintf(lab, sizeof lab, "place of edge E%d (%s)", id - MAXORB,
                 "affine side");
      else
        snprintf(lab, sizeof lab, "place #%d", id);
      printf("#   %s: first non-zero pole order %d, %d gaps (g = %d)%s, "
             "d_FR(M) = %d -> t = %d  [basis via %s]  (%.3f s)\n",
             lab, a1, ngaps, GENUS,
             ngaps == GENUS && nconst == 1 ? "" : "  [semigroup check FAILED]",
             dfr, (dfr - 1) / 2,
             via_newton[id] ? "Newton polygon" : "Laurent expansions",
             now() - t0);
      if (ngaps == GENUS && nconst == 1 &&
          (dfr > bestdfr || (dfr == bestdfr && a1 < besta))) {
        best = id;
        bestdfr = dfr;
        besta = a1;
      }
    }
  }
  if (best < 0) {
    fprintf(stderr, "no usable rational place for a one-point code\n");
    return 1;
  }
  if (best >= MAXORB)
    printf("# chosen pole: place of edge E%d  (d_FR = %d, designed t = %d)\n",
           best - MAXORB, bestdfr, (bestdfr - 1) / 2);
  else
    printf("# chosen pole: place #%d  (d_FR = %d, designed t = %d)\n", best,
           bestdfr, (bestdfr - 1) / 2);
if (via_newton[best] && use_poly_opt) {
  int e = best >= MAXORB ? best - MAXORB : pl[best].edge;
  if (poly_setup(e, M_EXT, &NB[best]) == 0) {
    use_poly = 1;
    bas_ei = NB[best].ei;   /* poly_setup の後 */
    bas_ej = NB[best].ej;
      if (hermitian_q > 0)
        printf("# Hermitian monomial syndrome tables on %d polynomial "
               "semigroup points (no dual basis)\n", NPT);
      else
        printf("# monomial syndrome tables on %d lattice points of the Newton "
               "cone (no dual basis, f kept as monomial coefficients)\n",
               NPT);
  }
}


  if (via_newton[best]) {
    /* ---- basis straight from the lattice points: monomials x^i y^j ---- */
    NBas *B = &NB[best];
    if (B->laurent) {
      /* Laurent monomials: x = 0 or y = 0 are not allowed as positions.
       * The only axis point of the model is the origin (checked), which is a
       * point where the chosen functions are regular but whose x^-1 / y^-1
       * values are undefined, so it is dropped from the positions. */
      int original_npts = npts;
      int k = 0;
      if (api_mode && api_received_len == (size_t)original_npts) {
        api_owned_received = malloc(sizeof(fe) * (size_t)original_npts);
        api_position_map = malloc(sizeof(size_t) * (size_t)original_npts);
        if (!api_owned_received || !api_position_map) {
          fprintf(stderr, "API allocation failed while puncturing Laurent positions\n");
          return 1;
        }
      }
      for (int p = 0; p < original_npts; ++p)
        if (PXv[p] && PYv[p]) {
          PXv[k] = PXv[p];
          PYv[k] = PYv[p];
          if (api_mode && api_received_len == (size_t)original_npts) {
            api_owned_received[k] = api_received[p];
            api_position_map[k] = (size_t)p;
          }
          k++;
        }
      if (api_mode && api_received_len == (size_t)original_npts) {
        api_received = api_owned_received;
        api_received_len = (size_t)k;
      }
      printf("# Laurent monomials used: %d axis points dropped, n = %d\n",
             npts - k, k);
      npts = k;
      if (npts <= M_EXT) {
        fprintf(stderr,
                "# only n = %d positions left, but M + g = %d >= n.\n", npts,
                M_EXT);
        return 1;
      }
    }
    nbasis = B->n;
    {
      int *lxs = malloc(sizeof(int) * (size_t)npts);
      int *lys = malloc(sizeof(int) * (size_t)npts);
      for (int k = 0; k < npts; ++k) {
        lxs[k] = PXv[k] ? (int)glog[PXv[k]] : -1;
        lys[k] = PYv[k] ? (int)glog[PYv[k]] : -1;
      }
      for (int i = 0; i < B->n; ++i) {
        basis[i].rho = B->rho[i];
        basis[i].val = malloc(sizeof(fe) * npts);
        mono_eval_row(basis[i].val, npts, lxs, lys, B->ei[i], B->ej[i]);
      }
      free(lxs);
      free(lys);
    }
  } else {
    LSp *L = &Lc[best];
    fe *V = eval_space(L);
    { /* basis sorted by pole order */
      int dim = L->dim;
      int *ord = malloc(sizeof(int) * dim);
      for (int i = 0; i < dim; ++i)
        ord[i] = i;
      for (int i = 1; i < dim; ++i) {
        int x = ord[i], j = i - 1;
        while (j >= 0 && pv[best][ord[j]] > pv[best][x]) {
          ord[j + 1] = ord[j];
          j--;
        }
        ord[j + 1] = x;
      }
      nbasis = dim;
      for (int i = 0; i < dim; ++i) {
        basis[i].rho = pv[best][ord[i]];
        basis[i].val = malloc(sizeof(fe) * npts);
        if (i == 0)
          for (int k = 0; k < npts; ++k)
            basis[0].val[k] = 1;
        else
          memcpy(basis[i].val, V + (size_t)ord[i] * npts, sizeof(fe) * npts);
      }
      free(ord);
    }
  }
  init_semigroup();
  ASHIFT = basis[1].rho;
  ROW_MAX = M_SYND - ASHIFT;
  build_omega_buckets();
  nz_idx = malloc(sizeof(int) * npts);
  printf("# setup (curve, places, basis up to M+g, evaluation): %.2f s;  "
         "semigroup has %d generators, smallest pole %d\n",
         now() - ts, ngenH, ASHIFT);
  if (run_vote && !use_poly) {
    double t0 = now();
    if (build_dual() != 0 || dual_selftest() != 0) {
      fprintf(stderr, "dual basis construction failed\n");
      return 1;
    }
    init_dual_logs();
    printf("# setup (dual basis for the top g coefficients, once per code): "
           "%.2f s\n",
           now() - t0);
  }
  fe *r = malloc(sizeof(fe) * npts);
  int cnt_fr = 0, cnt_bms = 0, cnt_vote = 0, cnt_frvote = 0;
  int quiet = trials > 1;
  for (int tr = 0; tr < trials; ++tr) {
    if (api_mode) {
      if (!run_frvote || run_fr || run_bms || run_vote) {
        fprintf(stderr, "API mode requires -frvote alone (do not enable -fr/-bms/-vote).\n");
        return 1;
      }
      if (api_received_len != (size_t)npts) {
        fprintf(stderr, "API received length mismatch: got %zu, expected %d\n",
                api_received_len, npts);
        return 1;
      }
      for (int k = 0; k < npts; ++k) {
        if (api_received[k] >= FS) {
          fprintf(stderr, "API received[%d]=%u is outside GF(2^%d)\n",
                  k, (unsigned)api_received[k], FM);
          return 1;
        }
      }
      memcpy(r, api_received, sizeof(fe) * (size_t)npts);
      set_received(r);
      if (decode_fr_vote(&res_frvote, verbose, 0) != 0 ||
          res_frvote.failed || !res_frvote.resolved) {
        fprintf(stderr, "API FR-VOTE decoding failed or error values unresolved.\n");
        return 2;
      }
      if ((size_t)res_frvote.nfound > api_output_capacity) {
        fprintf(stderr, "API output buffer too small: need %d, capacity %zu\n",
                res_frvote.nfound, api_output_capacity);
        return 3;
      }
      for (int k = 0; k < res_frvote.nfound; ++k) {
        api_error_positions[k] = api_position_map
            ? api_position_map[res_frvote.pos[k]]
            : (size_t)res_frvote.pos[k];
        api_error_values[k] = res_frvote.val[k];
      }
      *api_error_count = (size_t)res_frvote.nfound;
      api_completed = 1;
      break;
    }
    make_errors(r);
    set_received(r);
    if (!quiet)
      printf("# %d errors injected (seed %u)%s\n", NUM_ERRORS, seed,
             NUM_ERRORS > TAU ? "  -- beyond the basic bound" : "");
    if (force && NUM_ERRORS > TAU && !quiet && (run_fr || run_bms))
      puts("# FR/BMS: t exceeds the proven basic bound; running anyway (expected to "
           "fail)");
    int okf = 1, okb = 1, okv = 1, okfv = 1;
    if (run_frvote) {
      decode_fr_vote(&res_frvote, verbose, quiet);
      okfv = verify("FR-VOTE", &res_frvote, quiet);
      cnt_frvote += okfv;
    }
    if (run_fr) {
      if (NUM_ERRORS > TAU && !force) {
        okf = 0;
        if (!quiet)
          puts("# FR   skipped: beyond the basic bound");
      } else {
        decode_fr(&res_fr, quiet);
        okf = verify("FR", &res_fr, quiet);
        cnt_fr += okf;
      }
    }
    if (run_bms) {
      if (NUM_ERRORS > TAU && !force) {
        okb = 0;
        if (!quiet)
          puts("# BMS  skipped: beyond the basic bound");
      } else {
        decode_bms(&res_bms, 0, verbose, quiet);
        okb = verify("BMS", &res_bms, quiet);
        cnt_bms += okb;
      }
    }
    if (run_vote) {
      decode_bms(&res_vote, 1, verbose, quiet);
      okv = verify("VOTE", &res_vote, quiet);
      cnt_vote += okv;
    }
    if (!quiet) {
      if (run_fr && (NUM_ERRORS <= TAU || force))
        printf("# time FR   : reduction %.3f s, charpoly+roots %.3f s, values "
               "%.3f s\n",
               res_fr.t_main, res_fr.t_extract, res_fr.t_resolve);
      if (run_bms && (NUM_ERRORS <= TAU || force))
        printf("# time BMS  : loop %.3f s, scan %.3f s, values %.3f s\n",
               res_bms.t_main, res_bms.t_extract, res_bms.t_resolve);
      if (run_vote)
        printf("# time VOTE : BMS+voting %.3f s, scan %.3f s, values %.3f s\n",
               res_vote.t_main, res_vote.t_extract, res_vote.t_resolve);
      if (run_frvote)
        printf("# time FR-VOTE: FR-kernel+voting %.3f s, scan %.3f s, values %.3f s\n",
               res_frvote.t_main, res_frvote.t_extract, res_frvote.t_resolve);
      if (run_fr && run_vote && (NUM_ERRORS <= TAU || force) && !res_fr.failed)
        printf("# FR / VOTE time ratio: %.1f x\n",
               total_time(&res_fr) / total_time(&res_vote));
    } else {
      int bo = NUM_ERRORS <= TAU || force;
      printf("# trial %d: FR %s  BMS %s  VOTE %s\n", tr + 1,
             (run_fr && bo) ? (okf ? "ok" : "FAIL") : "n/a",
             (run_bms && bo) ? (okb ? "ok" : "FAIL") : "n/a",
             run_vote ? (okv ? "ok" : "FAIL") : "n/a");
      if (run_frvote)
        printf("# trial %d: FR-VOTE %s\n", tr + 1,
               okfv ? "ok" : "FAIL");
    }
  }
  if (trials > 1) {
    char sf[32], sb[32], sv[32];
    int basic_ok = NUM_ERRORS <= TAU || force;
    if (run_fr && basic_ok)
      snprintf(sf, sizeof sf, "%d/%d", cnt_fr, trials);
    else
      snprintf(sf, sizeof sf, "n/a");
    if (run_bms && basic_ok)
      snprintf(sb, sizeof sb, "%d/%d", cnt_bms, trials);
    else
      snprintf(sb, sizeof sb, "n/a");
    if (run_vote)
      snprintf(sv, sizeof sv, "%d/%d", cnt_vote, trials);
    else
      snprintf(sv, sizeof sv, "n/a");
    printf("# summary of %d trials with %d errors: FR %s, BMS %s, VOTE %s\n",
           trials, NUM_ERRORS, sf, sb, sv);
    if (run_frvote)
      printf("# FR-VOTE: %d/%d\n", cnt_frvote, trials);
  }
  return 0;
}
int ag_frvote_decode(int argc, char **argv, const uint16_t *received,
                     size_t received_len, size_t *error_positions,
                     uint16_t *error_values, size_t output_capacity,
                     size_t *error_count) {
  if (!argv || argc < 1 || !received || !error_count ||
      (output_capacity && (!error_positions || !error_values)))
    return -1;
  *error_count = 0;
  api_received = (const fe *)received;
  api_received_len = received_len;
  api_error_positions = error_positions;
  api_error_values = (fe *)error_values;
  api_output_capacity = output_capacity;
  api_error_count = error_count;
  api_mode = 1;
  api_completed = 0;
  api_owned_received = NULL;
  api_position_map = NULL;
  int rc = ag_frvote_run(argc, argv);
  free(api_owned_received);
  free(api_position_map);
  api_owned_received = NULL;
  api_position_map = NULL;
  api_mode = 0;
  api_received = NULL;
  api_error_positions = NULL;
  api_error_values = NULL;
  api_error_count = NULL;
  if (rc != 0)
    return rc;
  return api_completed ? 0 : -10;
}

#ifndef AG_FRVOTE_NO_MAIN
int main(int argc, char **argv) {
  return ag_frvote_run(argc, argv);
}
#endif