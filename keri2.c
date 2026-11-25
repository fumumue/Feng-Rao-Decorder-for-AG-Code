/*
 * ag_frvote.c -- one-point AG-code FR-VOTE for supported plane curves over
 * GF(2^m)
 *
 *   * one-point codes at a rational place at infinity: the basis of L(MP) is
 * built from the NEWTON POLYGON (monomials x^i y^j = lattice points; no local
 * expansions, no linear algebra), certified by Riemann-Roch at run time; if
 * that does not apply (edge of lattice length > 1, ...) it falls back to exact
 * Laurent-series fallback disabled; automatic choice of the
 * best place
 *   * multi-point codes  D = sum m_Q Q  (Galois orbits of places, no field
 * extension needed)
 *   * decoders on the same syndromes:  FR (basic, adaptive locator extraction),
 * BMS (Sakata), VOTE (BMS + Feng-Rao majority voting, t <= (M-2g+1)/2)
 * [one-point], BASIC (kernel of S(h_a f_b), t <= (deg G - 3g + 1)/2)
 * [multi-point]
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

/* EXTENSION_POINT: algorithmic/memory capacities. Raising m alone is not
 * sufficient; audit these limits against genus, point count and M first. */
#define MAXB 400000      /* max number of basis functions (M+1)          */
#define MAXT 3000        /* max number of errors                         */
#define MAXGEN 100       /* max generators of the ideal E                */
#define MAXGENUS 1310006 /* max genus handled by the voting part         */
#define SGMAX (MAXB + MAXGENUS + 64)
#define MAXTERM 64 /* EXTENSION_POINT: sparse curve term capacity   */
#define MAXEDGE 32 /* EXTENSION_POINT: Newton polygon edge capacity */
#define MAXORB 128 /* EXTENSION_POINT: place/orbit capacity          */

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ================= GF(2^m), supported m <= 12 =================
 * EXTENSION_POINT: increase this bound only after auditing field tables,
 * point enumeration, integer widths, and memory limits. */
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
#define PMAXD 320 /* maximum supported Newton-edge polynomial degree */
typedef struct {
  int deg;
  fe c[PMAXD + 1];
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
  if (e->len > PMAXD) {
    fprintf(stderr, "edge %d: lattice length %d exceeds PMAXD = %d\n", k,
            e->len, PMAXD);
    exit(1);
  }
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
  /* EXTENSION_POINT: higher-degree edge factorization is not implemented. */
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
    Poly *facs = malloc(sizeof(*facs) * (PMAXD + 1));
    if (!facs) {
      fprintf(stderr, "out of memory while factoring edge polynomial\n");
      exit(1);
    }
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
    free(facs);
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

/* 旧 solve_L() の名前を変更 */
static int solve_L_laurent(
    const int *mult, int Jfix, int Jstep, int Jmax,
    int verbose, LSp *out){
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
    fe *Mx = calloc((size_t)((E > 0 && K > 0) ? E * K : 1), sizeof(fe));
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
static int use_newton = 1;
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
  int *ri = malloc(sizeof(int) * (Mx + 1)),
      *rj = malloc(sizeof(int) * (Mx + 1));
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
  int ok =
      !bad && have[0] && ri[0] == 0 && rj[0] == 0 && cnt == Mx + 1 - genus_g;
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



/*
 * Newton-first L(D) solver.
 *
 * Supported:
 *   D = m P, where P is a rational place on a primitive Newton edge.
 *   The Newton basis must be non-Laurent and fit the existing
 *   rectangular monomial representation used by LSp/eval_space.
 *
 * Unsupported divisors are delegated to solve_L_laurent().
 */
static int solve_L(const int *mult, int Jfix, int Jstep, int Jmax,
                   int verbose, LSp *out)
{
    if (!mult || !out)
        return -1;

    memset(out, 0, sizeof(*out));

    int qsel = -1;
    int degD = 0;

    for (int q = 0; q < np; ++q) {
        if (mult[q] < 0)
            return -1;

        degD += mult[q] * pl[q].d;

        if (mult[q] != 0) {
            if (qsel >= 0) {
                qsel = -2;  /* multiple places */
                break;
            }
            qsel = q;
        }
    }

    /*
     * D = 0: L(0) = <1>.
     */
    if (qsel == -1) {
        out->dim = 1;
        out->J = 0;
        out->K = dx_deg;
        out->B = calloc((size_t)dx_deg, sizeof(fe));

        if (!out->B)
            return -1;

        out->B[0] = 1;
        return 0;
    }

    /*
     * Newton one-point basis does not directly handle
     * multiple places or non-rational places.
     */
    if (qsel < 0 || pl[qsel].d != 1 ||
        pl[qsel].edge < 0 || pl[qsel].edge >= ne ||
        ed[pl[qsel].edge].len != 1) {
        return solve_L_laurent(
            mult, Jfix, Jstep, Jmax, verbose, out);
    }

    /*
     * Riemann-Roch certification is required here.
     */
    if (degD < 2 * genus_g - 1) {
        return solve_L_laurent(
            mult, Jfix, Jstep, Jmax, verbose, out);
    }

    NBas NB = {0};

    if (newton_basis(pl[qsel].edge, mult[qsel], &NB) != 0) {
        free(NB.rho);
        free(NB.ei);
        free(NB.ej);

        return solve_L_laurent(
            mult, Jfix, Jstep, Jmax, verbose, out);
    }

    int expected = degD - genus_g + 1;

    /*
     * Require the Riemann-Roch dimension and a basis that
     * can be represented by the existing LSp coefficient array.
     */
    int supported = (NB.n == expected && !NB.laurent);
    int maxj = 0;

    for (int k = 0; k < NB.n && supported; ++k) {
        if (NB.ei[k] < 0 ||
            NB.ei[k] >= dx_deg ||
            NB.ej[k] < 0) {
            supported = 0;
            break;
        }

        if (NB.ej[k] > maxj)
            maxj = NB.ej[k];
    }

    if (!supported) {
        free(NB.rho);
        free(NB.ei);
        free(NB.ej);

        return solve_L_laurent(
            mult, Jfix, Jstep, Jmax, verbose, out);
    }

    int J = maxj;
    int K = dx_deg * (J + 1);

    if (K <= 0 ||
        (size_t)NB.n > SIZE_MAX / (size_t)K / sizeof(fe)) {
        free(NB.rho);
        free(NB.ei);
        free(NB.ej);
        return -1;
    }

    fe *B = calloc((size_t)NB.n * K, sizeof(fe));

    if (!B) {
        free(NB.rho);
        free(NB.ei);
        free(NB.ej);
        return -1;
    }

    /*
     * Convert each Newton monomial x^i y^j into
     * the existing LSp coefficient layout:
     *
     *   column = j * dx_deg + i
     */
    for (int k = 0; k < NB.n; ++k) {
        int col = NB.ej[k] * dx_deg + NB.ei[k];
        B[(size_t)k * K + col] = 1;
    }

    out->dim = NB.n;
    out->K = K;
    out->J = J;
    out->B = B;

    if (verbose) {
        printf("# Newton L(D): dim = %d "
               "(Riemann-Roch: %d), J = %d\n",
               NB.n, expected, J);
    }

    free(NB.rho);
    free(NB.ei);
    free(NB.ej);

    return 0;
}

/* value of x^i y^j at a point (i, j may be negative; then x, y != 0) */
static fe mono_eval(fe x, fe y, int i, int j) {
  if (i == 0 && j == 0)
    return 1;
  if ((i != 0 && !x) || (j != 0 && !y))
    return 0;
  long long ex =
      ((long long)i * (x ? glog[x] : 0) + (long long)j * (y ? glog[y] : 0)) %
      FO;
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
static int show_locator_equations = 0;

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
static int use_poly;
static int compact_fr_mode;
static fe basis_value_at(int basis_index, int point_index);
static fe basis_syndrome(int basis_index);
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
  if (use_poly)
    return basis_syndrome(ia);
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

static fe *aug =
    NULL; /* resolve_by_values: allocated to the active row window */
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
  int aug_cap = R;
  aug = calloc((size_t)aug_cap * (size_t)(n + 1), sizeof(fe));
  if (!aug)
    goto done;
  for (;;) {
    for (int a = 0; a < R; ++a) {
      for (int k = 0; k < n; ++k)
        aug[(size_t)a * (size_t)(n + 1) + (size_t)k] =
            basis_value_at(a, found[k]);
      aug[(size_t)a * (size_t)(n + 1) + (size_t)n] = synd1(a);
    }
    int retry = 0;
    for (int c = 0; c < n; ++c) {
      int p = -1;
      for (int a = c; a < R; ++a)
        if (aug[(size_t)a * (size_t)(n + 1) + (size_t)c]) {
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
          fe t = aug[(size_t)p * (size_t)(n + 1) + (size_t)k];
          aug[(size_t)p * (size_t)(n + 1) + (size_t)k] =
              aug[(size_t)c * (size_t)(n + 1) + (size_t)k];
          aug[(size_t)c * (size_t)(n + 1) + (size_t)k] = t;
        }
      fe iv = inv(aug[(size_t)c * (size_t)(n + 1) + (size_t)c]);
      aug[(size_t)c * (size_t)(n + 1) + (size_t)c] = 1;
      lg[c] = 0;
      for (int k = c + 1; k <= n; ++k) {
        aug[(size_t)c * (size_t)(n + 1) + (size_t)k] =
            mul(aug[(size_t)c * (size_t)(n + 1) + (size_t)k], iv);
        lg[k] = aug[(size_t)c * (size_t)(n + 1) + (size_t)k]
                    ? glog[aug[(size_t)c * (size_t)(n + 1) + (size_t)k]]
                    : (uint16_t)SENT;
      }
      for (int a = c + 1; a < R; ++a) {
        fe f = aug[(size_t)a * (size_t)(n + 1) + (size_t)c];
        if (!f)
          continue;
        const int lf = glog[f];
        fe *row = aug + (size_t)a * (size_t)(n + 1);
        for (int k = c + 1; k <= n; ++k)
          row[k] ^= E[lf + lg[k]];
        row[c] = 0;
      }
    }
    if (retry) {
      R = m;
      if (R > aug_cap) {
        fe *tmp = realloc(aug, (size_t)R * (size_t)(n + 1) * sizeof(fe));
        if (!tmp)
          goto done;
        aug = tmp;
        aug_cap = R;
      }
      continue;
    }
    break;
  }
  for (int a = n; a < R; ++a)
    if (aug[(size_t)a * (size_t)(n + 1) + (size_t)n])
      goto done; /* inconsistent */
  /* back substitution */
  for (int c = n - 1; c >= 0; --c) {
    fe acc = aug[(size_t)c * (size_t)(n + 1) + (size_t)n];
    for (int k = c + 1; k < n; ++k)
      acc ^= mul(aug[(size_t)c * (size_t)(n + 1) + (size_t)k], x[k]);
    x[c] = acc;
  }
  /* verify the rows that were not used for elimination */
  for (int a = R; a < m; ++a) {
    fe acc = synd1(a);
    for (int k = 0; k < n; ++k)
      acc ^= mul(x[k], basis_value_at(a, found[k]));
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
  free(aug);
  aug = NULL;
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

/* Experimental multivariate Forney-function evaluation.
 *
 * Construct functions f_i in the available check-function space such that
 *       f_i(P_j) = delta_ij.
 * Since S(f) = sum_j e_j f(P_j), this gives e_i = S(f_i).
 *
 * This is the interpolation/Forney-function identity, not the optimized
 * Kötter-update algorithm.  It is kept separate from resolve_by_values so
 * the two implementations can be compared on identical FR locations.
 */
static int resolve_by_forney_functions(int *found, int *nfound) {
  int n = *nfound, m = count_basis_upto(M_SYND);
  if (n <= 0 || n > MAXT || m < n)
    return 0;

  int R = n + 32 < m ? n + 32 : m;
  int cap = R;
  int *row_id = malloc((size_t)cap * sizeof(*row_id));
  fe *work = calloc((size_t)cap * (size_t)n, sizeof(*work));
  fe *aug2 = NULL;
  fe *sy = malloc((size_t)n * sizeof(*sy));
  fe *vals = malloc((size_t)n * sizeof(*vals));
  int ok = 0;
  if (!row_id || !work || !sy || !vals)
    goto done;

  for (;;) {
    for (int a = 0; a < R; ++a) {
      row_id[a] = a;
      for (int k = 0; k < n; ++k)
        work[(size_t)a * n + k] = basis_value_at(a, found[k]);
    }
    int rank = 0;
    for (int c = 0; c < n; ++c) {
      int pivot = -1;
      for (int a = rank; a < R; ++a)
        if (work[(size_t)a * n + c]) {
          pivot = a;
          break;
        }
      if (pivot < 0)
        continue;
      if (pivot != rank) {
        for (int k = 0; k < n; ++k) {
          fe t = work[(size_t)pivot * n + k];
          work[(size_t)pivot * n + k] = work[(size_t)rank * n + k];
          work[(size_t)rank * n + k] = t;
        }
        int ti = row_id[pivot];
        row_id[pivot] = row_id[rank];
        row_id[rank] = ti;
      }
      fe iv = inv(work[(size_t)rank * n + c]);
      for (int k = c; k < n; ++k)
        work[(size_t)rank * n + k] = mul(work[(size_t)rank * n + k], iv);
      for (int a = rank + 1; a < R; ++a) {
        fe f = work[(size_t)a * n + c];
        if (!f)
          continue;
        for (int k = c; k < n; ++k)
          work[(size_t)a * n + k] ^= mul(f, work[(size_t)rank * n + k]);
      }
      ++rank;
      if (rank == n)
        break;
    }
    if (rank == n)
      break;
    if (R == m)
      goto done;
    int next = m;
    fe *tmp = realloc(work, (size_t)next * (size_t)n * sizeof(*work));
    int *tmpid = realloc(row_id, (size_t)next * sizeof(*row_id));
    if (!tmp || !tmpid) {
      if (tmp)
        work = tmp;
      if (tmpid)
        row_id = tmpid;
      goto done;
    }
    work = tmp;
    row_id = tmpid;
    cap = next;
    R = next;
    (void)cap;
  }

  /* V[k,c] = h_{row_id[c]}(P_k).  Invert V^T to obtain the
   * coefficients of the interpolating functions f_i. */
  aug2 = calloc((size_t)n * (size_t)(2 * n), sizeof(*aug2));
  if (!aug2)
    goto done;
  for (int k = 0; k < n; ++k) {
    for (int c = 0; c < n; ++c)
      aug2[(size_t)k * (2 * n) + c] = basis_value_at(row_id[c], found[k]);
    aug2[(size_t)k * (2 * n) + n + k] = 1;
  }
  for (int c = 0; c < n; ++c) {
    int pivot = c;
    while (pivot < n && !aug2[(size_t)pivot * (2 * n) + c])
      ++pivot;
    if (pivot == n)
      goto done;
    if (pivot != c)
      for (int k = 0; k < 2 * n; ++k) {
        fe t = aug2[(size_t)pivot * (2 * n) + k];
        aug2[(size_t)pivot * (2 * n) + k] = aug2[(size_t)c * (2 * n) + k];
        aug2[(size_t)c * (2 * n) + k] = t;
      }
    fe iv = inv(aug2[(size_t)c * (2 * n) + c]);
    for (int k = 0; k < 2 * n; ++k)
      aug2[(size_t)c * (2 * n) + k] = mul(aug2[(size_t)c * (2 * n) + k], iv);
    for (int a = 0; a < n; ++a)
      if (a != c) {
        fe f = aug2[(size_t)a * (2 * n) + c];
        if (!f)
          continue;
        for (int k = 0; k < 2 * n; ++k)
          aug2[(size_t)a * (2 * n) + k] ^=
              mul(f, aug2[(size_t)c * (2 * n) + k]);
      }
  }
  for (int c = 0; c < n; ++c)
    sy[c] = synd1(row_id[c]);
  for (int i = 0; i < n; ++i) {
    fe e = 0;
    for (int c = 0; c < n; ++c)
      e ^= mul(aug2[(size_t)c * (2 * n) + n + i], sy[c]);
    vals[i] = e;
  }

  /* Verify the recovered values against the complete available syndrome
   * sequence before accepting them.  This prevents an underdetermined
   * interpolation from being mistaken for a successful Forney evaluation. */
  for (int a = 0; a < m; ++a) {
    fe check = 0;
    for (int i = 0; i < n; ++i)
      if (vals[i])
        check ^= mul(vals[i], basis_value_at(a, found[i]));
    if (check != synd1(a))
      goto done;
  }
  {
    int keep = 0;
    for (int i = 0; i < n; ++i)
      if (vals[i]) {
        found[keep] = found[i];
        err_val[keep] = vals[i];
        ++keep;
      }
    *nfound = keep;
  }
  ok = 1;
done:
  free(row_id);
  free(work);
  free(aug2);
  free(sy);
  free(vals);
  return ok;
}

static int use_forney_values = 0;
static int use_kotter_values = 0;
static int kotter_ready = 0;
static int resolve_by_kotter(int *found, int *nfound);
static void resolve_and_store_fr_forney(Result *R) {
  if (use_kotter_values) {
    double t0 = now();
    int resolved = 0;
    if (kotter_ready && !R->overflow && R->nfound > 0)
      resolved = resolve_by_kotter(R->pos, &R->nfound);
    if (resolved)
      puts("# FR: error values via Kötter generalized Forney update");
    else if (!R->overflow && R->nfound > 0)
      puts("# FR: Kötter update failed verification; no fallback was used.");
    R->resolved = resolved;
    for (int i = 0; i < R->nfound; ++i)
      R->val[i] = resolved ? err_val[i] : 0;
    R->t_resolve = now() - t0;
  } else if (use_forney_values) {
    double t0 = now();
    int resolved = 0;
    if (!R->overflow && R->nfound > 0)
      resolved = resolve_by_forney_functions(R->pos, &R->nfound);
    if (resolved)
      puts("# FR: error values via verified multivariate Forney functions");
    else if (!R->overflow && R->nfound > 0)
      puts("# FR: Forney-function evaluation failed verification; no fallback "
           "was used.");
    R->resolved = resolved;
    for (int i = 0; i < R->nfound; ++i)
      R->val[i] = resolved ? err_val[i] : 0;
    R->t_resolve = now() - t0;
  } else {
    /* Default: one augmented elimination.  The interpolation-based Forney
     * path needs a separate row-rank pass and a second inverse, and showed
     * no speed advantage in the current tests. */
    resolve_and_store(R);
  }
}

/* ================= FR: basic algorithm + characteristic polynomial
 * ================= */
static int slot_of_row[MAXB];
static fe *E0f;
static fe *pp_S;
static inline int pp_at(int i, int j);
static int *bas_ei, *bas_ej;
static int piv_of_row[MAXB], row_of_col[MAXB];
static fe pivinv[MAXB];
static fe **coefm; /* triangular locator coefficient rows, allocated to nl */
static int coefm_rows;
static fe *fr_coef_blk;
static size_t fr_coef_stride;
static fe *red_blk;
static size_t fr_stride;
static uint8_t **plr, **plc;
static void free_pivot_rows(void) {
  if (plr) {
    for (int i = 0; i < MAXT; ++i)
      free(plr[i]);
    free(plr);
    plr = NULL;
  }
  if (plc) {
    for (int i = 0; i < MAXT; ++i)
      free(plc[i]);
    free(plc);
    plc = NULL;
  }
}

static inline fe synd_fast(int a, int b, int shi, int shj) {
  if (!bas_ei || !bas_ej) {
    fprintf(stderr, "bas_ei/bas_ej not set\n");
    abort();
  }
  int t = pp_at(bas_ei[a] + bas_ei[b] + shi, bas_ej[a] + bas_ej[b] + shj);
  if (t < 0) {
    fprintf(stderr, "synd_fast: lattice point not in table (a=%d b=%d)\n", a,
            b);
    abort();
  }
  return pp_S[t];
}

static inline fe synd_fast2(int a, int b, int shi, int shj) {
  int t = pp_at(bas_ei[a] + bas_ei[b] + shi, bas_ej[a] + bas_ej[b] + shj);
  return pp_S[t];
}

#define FR_BLK 64
/* Log values are in [0, 2*FO].  FM+1 bits are sufficient, so store
 * pivot rows packed instead of spending 16 bits per log value. */
/* plain uint16 log rows (the bit-packed variant was ~1.7x slower in the hot
 * loop and saved only ~38% of a small table) */
static inline size_t packed_log_bytes(size_t n) { return n * sizeof(uint16_t); }
static inline void packed_log_set(uint8_t *p, size_t i, uint16_t v) {
  ((uint16_t *)p)[i] = v;
}
static inline uint16_t packed_log_get(const uint8_t *p, size_t i) {
  return ((const uint16_t *)p)[i];
}
static int fr_pos[MAXB], fr_ncol[MAXB];

/* 行 i を列 j0
 * から簡約する。ピボット列を持たない非零の列で止まり、その列を返す。
 * 最後まで消えたら ncol を返す。row_of_col / plr / plc は読むだけ。 */
static int fr_run(fe *Ri, fe *Ci, int ncol, int needc, int j0) {
  for (int j = j0; j < ncol; ++j) {
    fe v = Ri[j];
    if (!v)
      continue;
    int p = row_of_col[j];
    if (p < 0)
      return j;
    int s = slot_of_row[p];
    int lf = glog[mul(v, pivinv[p])];
    const uint8_t *lr = plr[s];
    for (int jj = j; jj < ncol; ++jj)
      Ri[jj] ^= E0f[lf + packed_log_get(lr, (size_t)jj)];
    if (needc) {
      const uint8_t *lc = plc[s];
      for (int k = 0; k <= p; ++k)
        Ci[k] ^= E0f[lf + packed_log_get(lc, (size_t)k)];
    }
  }
  return ncol;
}

static int alloc_coefm(int nl) {
  if (coefm) {
    for (int i = 0; i < coefm_rows; ++i)
      free(coefm[i]);
    free(coefm);
    coefm = NULL;
  }
  coefm = calloc((size_t)nl, sizeof(*coefm));
  if (!coefm)
    return -1;
  coefm_rows = nl;
  for (int i = 0; i < nl; ++i) {
    coefm[i] = calloc((size_t)i + 1, sizeof(**coefm));
    if (!coefm[i]) {
      for (int j = 0; j < i; ++j)
        free(coefm[j]);
      free(coefm);
      coefm = NULL;
      coefm_rows = 0;
      return -1;
    }
  }
  return 0;
}

static void free_coefm(void) {
  if (coefm) {
    for (int i = 0; i < coefm_rows; ++i)
      free(coefm[i]);
    free(coefm);
    coefm = NULL;
  }
  coefm_rows = 0;
}

static int fr_locator_is_minimal(int basis_row) {
  int b = basis[basis_row].rho;
  for (int q = 0; q < ngenH; ++q) {
    int a = b - genH[q];
    if (a >= 0 && a < SGMAX && in_H[a]) {
      int ia = idx_of_ord[a];
      if (ia >= 0 && ia < basis_row && piv_of_row[ia] < 0)
        return 0;
    }
  }
  return 1;
}

static int feng_rao_reduce(int row_limit) {
  int nrows = count_basis_upto(ROW_MAX);
  if (row_limit > 0 && row_limit < nrows)
    nrows = row_limit;
  int nl = count_basis_upto(L_DEG);
  int nslot = 0;
  free_coefm();
  if (compact_fr_mode) {
    coefm = calloc((size_t)nl, sizeof(*coefm));
    if (!coefm)
      return -1;
    coefm_rows = nl;
    fr_coef_stride = (size_t)(nl > 0 ? nl : 1);
    free(fr_coef_blk);
    fr_coef_blk = calloc((size_t)FR_BLK * fr_coef_stride, sizeof(fe));
    if (!fr_coef_blk)
      return -1;
  } else if (alloc_coefm(nl) != 0)
    return -1;
  int maxcol = count_basis_upto(M_SYND - basis[0].rho);
  if (maxcol < 1)
    maxcol = 1;
  fr_stride = (size_t)maxcol;
  free(red_blk);
  red_blk = calloc((size_t)FR_BLK * fr_stride, sizeof(fe));
  if (!red_blk)
    return -1;
  if (!E0f) {
    E0f = calloc((size_t)4 * FO + 8, sizeof(fe));
    for (int k = 0; k < 2 * FO; ++k)
      E0f[k] = gexp[k];
    if (!E0f)
      return -1;
  }
  free_pivot_rows();
  plr = calloc((size_t)MAXT, sizeof(*plr));
  plc = calloc((size_t)MAXT, sizeof(*plc));
  if (!plr || !plc) {
    free_pivot_rows();
    return -1;
  }
  for (int j = 0; j < MAXB; ++j)
    row_of_col[j] = -1;

  for (int b0 = 0; b0 < nrows; b0 += FR_BLK) {
    int b1 = b0 + FR_BLK < nrows ? b0 + FR_BLK : nrows;

    /* フェーズA: 成分作り + 確定済みピボットでの簡約(並列) */
#pragma omp parallel for schedule(dynamic, 1)
    for (int i = b0; i < b1; ++i) {
      int ncol = count_basis_upto(M_SYND - basis[i].rho);
      int needc = (i < nl);
      fr_ncol[i] = ncol;
      piv_of_row[i] = -1;
      fe *Ri = red_blk + (size_t)(i - b0) * fr_stride;
      fe *Ci = compact_fr_mode ? fr_coef_blk + (size_t)(i - b0) * fr_coef_stride
                               : (needc ? coefm[i] : NULL);
      for (int j = 0; j < ncol; ++j)
        Ri[j] = use_poly ? synd_fast(i, j, 0, 0) : synd(i, j, NULL);
      if (needc) {
        memset(Ci, 0, (size_t)(i + 1) * sizeof(fe));
        Ci[i] = 1;
      }
      fr_pos[i] = fr_run(Ri, Ci, ncol, needc, 0);
    }

    /* フェーズB: ブロック内の新ピボットを使って続行(逐次) */
    for (int i = b0; i < b1; ++i) {
      int ncol = fr_ncol[i];
      int needc = (i < nl);
      fe *Ri = red_blk + (size_t)(i - b0) * fr_stride;
      fe *Ci = compact_fr_mode ? fr_coef_blk + (size_t)(i - b0) * fr_coef_stride
                               : (needc ? coefm[i] : NULL);
      int j = fr_run(Ri, Ci, ncol, needc, fr_pos[i]);
      if (j >= ncol) {
        /* Dependent row: FR-VOTE only retains coefficient vectors for the
         * minimal non-pivot generators that will actually become locators. */
        if (compact_fr_mode && needc && fr_locator_is_minimal(i)) {
          coefm[i] = malloc((size_t)(i + 1) * sizeof(fe));
          if (!coefm[i])
            return -1;
          memcpy(coefm[i], Ci, (size_t)(i + 1) * sizeof(fe));
        }
        continue;
      }
      if (nslot >= MAXT - 1)
        return -1; /* ピボット過多 */
      int s = nslot++;
      slot_of_row[i] = s;
      plr[s] = calloc(1, packed_log_bytes((size_t)(ncol ? ncol : 1)));
      if (!plr[s])
        return -1;
      for (int jj = 0; jj < ncol; ++jj)
        packed_log_set(plr[s], (size_t)jj,
                       Ri[jj] ? glog[Ri[jj]] : (uint16_t)(2 * FO));
      if (needc) {
        plc[s] = calloc(1, packed_log_bytes((size_t)(i + 1)));
        if (!plc[s])
          return -1;
        for (int k = 0; k <= i; ++k)
          packed_log_set(plc[s], (size_t)k,
                         Ci[k] ? glog[Ci[k]] : (uint16_t)(2 * FO));
      }
      piv_of_row[i] = j;
      row_of_col[j] = i;
      pivinv[i] = inv(Ri[j]);
    }
  }
  if (compact_fr_mode) {
    free(fr_coef_blk);
    fr_coef_blk = NULL;
    fr_coef_stride = 0;
  }
  return nrows;
}

static int feng_rao_reduce2(void) {
  int nrows = count_basis_upto(ROW_MAX);
  int maxcol = count_basis_upto(M_SYND - basis[0].rho);
  if (maxcol < 1)
    maxcol = 1;
  fe *red2 = calloc((size_t)nrows * (size_t)maxcol, sizeof(fe));
  if (!red2)
    return -1;
  int nl = count_basis_upto(L_DEG);
  int nslot = 0;
  if (alloc_coefm(nl) != 0) {
    free(red2);
    return -1;
  }
  if (!E0f) {
    E0f = calloc((size_t)4 * FO + 8, sizeof(fe));
    for (int k = 0; k < 2 * FO; ++k)
      E0f[k] = gexp[k];
    if (!E0f) {
      free(red2);
      return -1;
    }
  }
  free_pivot_rows();
  plr = calloc((size_t)MAXT, sizeof(*plr));
  plc = calloc((size_t)MAXT, sizeof(*plc));
  if (!plr || !plc) {
    free(red2);
    free_pivot_rows();
    return -1;
  }
  for (int j = 0; j < MAXB; ++j)
    row_of_col[j] = -1;

  for (int i = 0; i < nrows; ++i) {
    int ncol = count_basis_upto(M_SYND - basis[i].rho);
    int needc = (i < nl);
    for (int j = 0; j < ncol; ++j)
      red2[(size_t)i * (size_t)maxcol + (size_t)j] =
          use_poly ? synd_fast(i, j, 0, 0) : synd(i, j, NULL);
    if (needc) {
      memset(coefm[i], 0, (size_t)(i + 1) * sizeof(fe));
      coefm[i][i] = 1;
    }
    piv_of_row[i] = -1;

    for (int j = 0; j < ncol; ++j) {
      fe v = red2[(size_t)i * (size_t)maxcol + (size_t)j];
      if (!v)
        continue;
      int p = row_of_col[j];
      if (p >= 0) {
        int s = slot_of_row[p];
        int lf = glog[mul(v, pivinv[p])];
        const uint8_t *lr = plr[s];
        fe *Ri = red2 + (size_t)i * (size_t)maxcol;
        for (int jj = j; jj < ncol; ++jj)
          Ri[jj] ^= E0f[lf + packed_log_get(lr, (size_t)jj)];
        if (needc) {
          const uint8_t *lc = plc[s];
          fe *Ci = coefm[i];
          for (int k = 0; k <= p; ++k)
            Ci[k] ^= E0f[lf + packed_log_get(lc, (size_t)k)];
        }
      } else {
        if (nslot >= MAXT - 1)
          return -1; /* ピボット過多 */
        int s = nslot++;
        slot_of_row[i] = s;
        plr[s] = calloc(1, packed_log_bytes((size_t)(ncol ? ncol : 1)));
        if (!plr[s]) {
          free(red2);
          return -1;
        }
        for (int jj = 0; jj < ncol; ++jj)
          packed_log_set(
              plr[s], (size_t)jj,
              red2[(size_t)i * (size_t)maxcol + (size_t)jj]
                  ? glog[red2[(size_t)i * (size_t)maxcol + (size_t)jj]]
                  : (uint16_t)(2 * FO));
        if (needc) {
          plc[s] = calloc(1, packed_log_bytes((size_t)(i + 1)));
          if (!plc[s]) {
            free(red2);
            return -1;
          }
          for (int k = 0; k <= i; ++k)
            packed_log_set(plc[s], (size_t)k,
                           coefm[i][k] ? glog[coefm[i][k]]
                                       : (uint16_t)(2 * FO));
        }
        piv_of_row[i] = j;
        row_of_col[j] = i;
        pivinv[i] = inv(v);
        break;
      }
    }
  }
  free(red2);
  return nrows;
}

/* ================= FR: direct locator evaluation (no charpoly) ======= */
static int true_pos[MAXT];
static void report_fr_locator_zero_counts(int nl, const Result *R) {
  int locno = 0;
  puts("# FR locator zero counts on the evaluation-point set:");
  for (int i = 0; i < nl; ++i) {
    if (piv_of_row[i] >= 0)
      continue;
    int zeros = 0, true_hits = 0;
    for (int p = 0; p < npts; ++p) {
      fe acc = 0;
      for (int k = 0; k <= i; ++k)
        if (coefm[i][k])
          acc ^= mul(coefm[i][k], basis[k].val[p]);
      if (!acc) {
        ++zeros;
        for (int e = 0; e < NUM_ERRORS; ++e)
          if (true_pos[e] == p) {
            ++true_hits;
            break;
          }
      }
    }
    printf("#   L_%d: zeros=%d, injected-error points among them=%d\n", locno++,
           zeros, true_hits);
  }
  int common_true = 0;
  for (int e = 0; e < NUM_ERRORS; ++e)
    for (int k = 0; k < R->nfound; ++k)
      if (true_pos[e] == R->pos[k]) {
        ++common_true;
        break;
      }
  printf("# FR common zero set: %d points; injected-error points in it=%d/%d\n",
         R->nfound, common_true, NUM_ERRORS);
}

static void print_fr_locator_equations(int nl, int quiet) {
  if (!show_locator_equations || quiet)
    return;
  puts("# FR error-position equations (common-zero system):");
  int count = 0;
  for (int i = 0; i < nl; ++i) {
    if (piv_of_row[i] >= 0)
      continue;
    printf("#   L_%d(P) = ", count++);
    int first = 1;
    for (int k = 0; k <= i; ++k) {
      fe c = coefm[i][k];
      if (!c)
        continue;
      printf("%s0x%03X*h_%d(P)", first ? "" : " + ", (unsigned)c, k);
      first = 0;
    }
    if (first)
      printf("0");
    puts(" = 0");
  }
  puts("# Error positions are the common zeros of these locator equations.");
}

static int decode_fr(Result *R, int quiet) {
  int nl, nloc = 0;
  double t0 = now();
  memset(R, 0, sizeof *R);
  int nrows = feng_rao_reduce(0);
  if (nrows < 0) {
    R->failed = 1;
    return -1;
  }
  nl = count_basis_upto(L_DEG);
  for (int i = 0; i < nl; ++i)
    if (piv_of_row[i] < 0)
      ++nloc;
  for (int i = 0; i < nrows; ++i)
    if (piv_of_row[i] >= 0) {
      R->rowset[basis[i].rho] = 1;
      R->colset[basis[piv_of_row[i]].rho] = 1;
      ++R->T;
    }
  R->t_main = now() - t0;
  if (!quiet) {
    printf("# FR : %d error locators with rho <= %d\n", nloc, L_DEG);
    printf("# FR : staircase of %d elements -> estimated t = %d\n", R->T, R->T);
  }
  if (R->T == 0)
    return 0;
  if (nloc > 0)
    print_fr_locator_equations(nl, quiet);
  if (nloc == 0) {
    if (!quiet)
      puts("# FR : no error locator below the degree bound -> failed");
    R->failed = 1;
    return -1;
  }
  t0 = now();
  int nfound = 0, overflow = 0;
  for (int idx = 0; idx < npts; ++idx) {
    int vanish = 1;
    for (int i = 0; i < nl && vanish; ++i) {
      if (piv_of_row[i] >= 0)
        continue;
      fe acc = 0;
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
  R->nfound = nfound;
  R->overflow = overflow;
  R->t_extract = now() - t0;
  if (quiet) {
    printf("# FR : %d positions found by direct locator evaluation "
           "(characteristic polynomial disabled)\n",
           nfound);
    report_fr_locator_zero_counts(nl, R);
  }
  resolve_and_store_fr_forney(R);
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
/* FR-VOTE-only sparse locator supports.  The dense coefficient vectors remain
 * available for the common algebra, but the voting hot path visits only their
 * nonzero terms instead of scanning every lattice point. */
static int *frv_support_idx[MAXGEN];
static fe *frv_support_val[MAXGEN];
static int frv_support_n[MAXGEN];
static int frv_ancestor[SGMAX];
static int frv_support_ready;
static uint32_t *frv_vote_counts; /* ngen x (M_EXT-M_SYND), exact pair counts */
static int frv_vote_count_len;
static int frv_vote_conv_ready;
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
static fe **Bw;
static int selp[MAXB];
static int nsel_dual;
static fe *Aug;
static int lgrow[MAXB + MAXGENUS];

static int build_dual(void) {
  int *perm = malloc(sizeof(int) * npts);
  const int NB = nbasis;
  if (Bw) {
    for (int v = 0; v < GENUS; ++v)
      free(Bw[v]);
    free(Bw);
    Bw = NULL;
  }
  Bw = calloc((size_t)GENUS, sizeof(*Bw));
  /* Keep the GENUS right-hand sides in Bw instead of appending them to Aug.
   * This changes Aug from NB x (NB+GENUS) to NB x NB and avoids a second
   * copy of the transformed right-hand sides. */
  Aug = calloc((size_t)NB * (size_t)NB, sizeof(fe));
  if (!Bw || !Aug) {
    free(perm);
    free(Aug);
    Aug = NULL;
    if (Bw) {
      free(Bw);
      Bw = NULL;
    }
    return -1;
  }
  for (int v = 0; v < GENUS; ++v) {
    Bw[v] = calloc((size_t)NB, sizeof(fe));
    if (!Bw[v]) {
      for (int z = 0; z < v; ++z)
        free(Bw[z]);
      free(Bw);
      Bw = NULL;
      free(perm);
      free(Aug);
      Aug = NULL;
      return -1;
    }
  }
  unsigned seed = 12345u;
  if (NB != M_SYND + 1 || basis[NB - GENUS].rho != M_SYND + 1) {
    fprintf(stderr,
            "dual basis: unexpected basis layout (need M >= conductor)\n");
    free(perm);
    free(Aug);
    Aug = NULL;
    for (int v = 0; v < GENUS; ++v)
      free(Bw[v]);
    free(Bw);
    Bw = NULL;
    return -1;
  }
  if (NB > npts) {
    fprintf(stderr, "dual basis: fewer points than basis functions\n");
    free(perm);
    free(Aug);
    Aug = NULL;
    for (int v = 0; v < GENUS; ++v)
      free(Bw[v]);
    free(Bw);
    Bw = NULL;
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
        Aug[(size_t)j * (size_t)NB + (size_t)p] = basis[j].val[selp[p]];
      for (int v = 0; v < GENUS; ++v)
        Bw[v][j] = (j == NB - GENUS + v) ? 1 : 0;
    }
    for (int c = 0; c < NB && !singular; ++c) {
      int p = -1;
      for (int r = c; r < NB; ++r)
        if (Aug[(size_t)r * (size_t)NB + (size_t)c]) {
          p = r;
          break;
        }
      if (p < 0) {
        singular = 1;
        break;
      }
      if (p != c) {
        for (int k = 0; k < NB; ++k) {
          fe t = Aug[(size_t)p * (size_t)NB + (size_t)k];
          Aug[(size_t)p * (size_t)NB + (size_t)k] =
              Aug[(size_t)c * (size_t)NB + (size_t)k];
          Aug[(size_t)c * (size_t)NB + (size_t)k] = t;
        }
        for (int v = 0; v < GENUS; ++v) {
          fe t = Bw[v][p];
          Bw[v][p] = Bw[v][c];
          Bw[v][c] = t;
        }
      }
      fe iv = inv(Aug[(size_t)c * (size_t)NB + (size_t)c]);
      for (int k = c; k < NB; ++k)
        Aug[(size_t)c * (size_t)NB + (size_t)k] =
            mul(Aug[(size_t)c * (size_t)NB + (size_t)k], iv);
      for (int v = 0; v < GENUS; ++v)
        Bw[v][c] = mul(Bw[v][c], iv);
      for (int k = c + 1; k < NB; ++k)
        lgrow[k] = Aug[(size_t)c * (size_t)NB + (size_t)k]
                       ? (int)glog[Aug[(size_t)c * (size_t)NB + (size_t)k]]
                       : -1;
#pragma omp parallel for schedule(static)
      for (int r = c + 1; r < NB; ++r) {
        fe f = Aug[(size_t)r * (size_t)NB + (size_t)c];
        if (!f)
          continue;
        int lf = glog[f];
        fe *row = Aug + (size_t)r * (size_t)NB;
        for (int k = c + 1; k < NB; ++k)
          if (lgrow[k] >= 0)
            row[k] ^= gexp[lf + lgrow[k]];
        row[c] = 0;
        /* Each worker owns row r, so updating all RHS rows here is race-free
         * only if v is included in the same row operation. */
        for (int v = 0; v < GENUS; ++v)
          Bw[v][r] ^= mul(f, Bw[v][c]);
      }
    }
    if (singular)
      continue;
    for (int v = 0; v < GENUS; ++v) {
      /* Back substitution in place: Bw[v] already contains the transformed
       * right-hand side, and solved entries are overwritten from bottom up. */
      for (int i = NB - 1; i >= 0; --i) {
        fe acc = Bw[v][i];
        for (int k = i + 1; k < NB; ++k)
          if (Aug[(size_t)i * (size_t)NB + (size_t)k] && Bw[v][k])
            acc ^= mul(Aug[(size_t)i * (size_t)NB + (size_t)k], Bw[v][k]);
        Bw[v][i] = acc;
      }
    }
    free(perm);
    free(Aug);
    Aug = NULL;
    return 0;
  }
  fprintf(stderr, "dual basis: evaluation matrix singular\n");
  free(perm);
  free(Aug);
  Aug = NULL;
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
 * is zero).  LBw holds the logs of the dual rows Bw. */
static fe *E0;
static uint16_t **LBw;
static void init_dual_logs(void) {
  E0 = calloc((size_t)4 * FO + 8, sizeof(fe));
  for (int k = 0; k < 2 * FO; ++k)
    E0[k] = gexp[k];
  LBw = calloc((size_t)GENUS, sizeof *LBw);
  if (!LBw)
    return;
  for (int v = 0; v < GENUS; ++v) {
    LBw[v] = calloc((size_t)nsel_dual, sizeof(**LBw));
    if (!LBw[v])
      return;
    for (int p = 0; p < nsel_dual; ++p)
      LBw[v][p] = Bw[v][p] ? glog[Bw[v][p]] : (uint16_t)(2 * FO);
  }
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
static fe true_syndrome(int n) { return basis_syndrome(idx_of_ord[n]); }

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
 * vector over the lattice points: no evaluation, no dual basis, no elimination.
 */
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

/* The Newton path can evaluate a basis monomial directly at one point.  This
 * avoids retaining the full basis-by-position evaluation matrix when only
 * FR-VOTE is selected. */
static fe basis_value_at(int basis_index, int point_index) {
  if (use_poly && bas_ei && bas_ej)
    return mono_eval(PXv[point_index], PYv[point_index], bas_ei[basis_index],
                     bas_ej[basis_index]);
  return basis[basis_index].val[point_index];
}

static fe basis_syndrome(int basis_index) {
  if (use_poly && bas_ei && bas_ej) {
    int z = pp_at(bas_ei[basis_index], bas_ej[basis_index]);
    if (z >= 0)
      return pp_S[z];
  }
  fe acc = 0;
  for (int i = 0; i < nz_cnt; ++i) {
    int k = nz_idx[i];
    acc ^= mul(recv[k], basis_value_at(basis_index, k));
  }
  return acc;
}

/* Experimental decoder for a known common error value.
 * It solves the syndrome equations over GF(2), with one binary unknown per
 * evaluation position.  This is deliberately separate from FR/FR-VOTE.
 * The small-instance limits are intentional: minimum-weight binary syndrome
 * decoding is combinatorial, and this prototype enumerates the affine
 * solution space only when its dimension is at most 20. */
static int decode_common_value_positions(int common_value, int expected_weight,
                                         int verbose) {
  if (common_value <= 0 || common_value >= FS) {
    fprintf(stderr, "# COMMON-BINARY: requires a known nonzero common value\n");
    return -1;
  }
  const int n = npts;
  const int nb = count_basis_upto(M_SYND);
  const int nr = nb * FM;
  if (n > 4096 || nr > 8192) {
    printf("# COMMON-BINARY: prototype limit exceeded (n=%d, binary rows=%d; "
           "limits 4096/8192)\n",
           n, nr);
    return -1;
  }
  const int words = (n + 1 + 63) / 64;
  uint64_t *mat = calloc((size_t)nr * words, sizeof(uint64_t));
  int *pivot_col = malloc((size_t)(nr < n ? nr : n) * sizeof(int));
  if (!mat || !pivot_col) {
    free(mat);
    free(pivot_col);
    fprintf(stderr, "# COMMON-BINARY: allocation failed\n");
    return -1;
  }
  const fe ic = inv((fe)common_value);
  int row = 0;
  for (int bi = 0; bi < nb; ++bi) {
    if (basis[bi].rho > M_SYND)
      continue;
    fe rhs = mul(basis_syndrome(bi), ic);
    for (int bit = 0; bit < FM; ++bit, ++row) {
      uint64_t *r = mat + (size_t)row * words;
      for (int p = 0; p < n; ++p)
        if ((basis_value_at(bi, p) >> bit) & 1u)
          r[p >> 6] |= UINT64_C(1) << (p & 63);
      if ((rhs >> bit) & 1u)
        r[n >> 6] |= UINT64_C(1) << (n & 63);
    }
  }
  /* Reduced row-echelon form over GF(2). */
  int rank = 0;
  for (int col = 0; col < n && rank < row; ++col) {
    int sel = rank;
    while (sel < row &&
           !((mat[(size_t)sel * words + (col >> 6)] >> (col & 63)) & 1u))
      ++sel;
    if (sel == row)
      continue;
    if (sel != rank)
      for (int w = 0; w < words; ++w) {
        uint64_t t = mat[(size_t)rank * words + w];
        mat[(size_t)rank * words + w] = mat[(size_t)sel * words + w];
        mat[(size_t)sel * words + w] = t;
      }
    for (int rr = 0; rr < row; ++rr)
      if (rr != rank &&
          ((mat[(size_t)rr * words + (col >> 6)] >> (col & 63)) & 1u))
        for (int w = 0; w < words; ++w)
          mat[(size_t)rr * words + w] ^= mat[(size_t)rank * words + w];
    pivot_col[rank++] = col;
  }
  for (int rr = rank; rr < row; ++rr) {
    int any = 0;
    for (int w = 0; w < (n + 63) / 64; ++w)
      any |= mat[(size_t)rr * words + w] != 0;
    if (!any && ((mat[(size_t)rr * words + (n >> 6)] >> (n & 63)) & 1u)) {
      printf("# COMMON-BINARY: inconsistent equations for common value %d\n",
             common_value);
      free(mat);
      free(pivot_col);
      return 0;
    }
  }
  uint8_t *is_pivot = calloc((size_t)n, 1);
  int *free_col = malloc((size_t)(n - rank + 1) * sizeof(int));
  if (!is_pivot || !free_col) {
    free(mat);
    free(pivot_col);
    free(is_pivot);
    free(free_col);
    return -1;
  }
  for (int i = 0; i < rank; ++i)
    is_pivot[pivot_col[i]] = 1;
  int nf = 0;
  for (int c = 0; c < n; ++c)
    if (!is_pivot[c])
      free_col[nf++] = c;
  printf("# COMMON-BINARY: GF(2) system %d x %d, rank=%d, nullity=%d\n", row, n,
         rank, nf);
  if (nf > 20) {
    printf("# COMMON-BINARY: nullity %d exceeds exact-search cap 20; no "
           "position claim\n",
           nf);
    free(mat);
    free(pivot_col);
    free(is_pivot);
    free(free_col);
    return 0;
  }
  /* Diagnostic: exact minimum distance of the binary kernel. */
  int kernel_dmin = n + 1;
  uint8_t *kx = calloc((size_t)n, 1);
  if (!kx) {
    free(mat);
    free(pivot_col);
    free(is_pivot);
    free(free_col);
    return -1;
  }
  for (uint64_t km = 1; km < (UINT64_C(1) << nf); ++km) {
    memset(kx, 0, (size_t)n);
    for (int j = 0; j < nf; ++j)
      kx[free_col[j]] = (uint8_t)((km >> j) & 1u);
    for (int i = 0; i < rank; ++i) {
      const uint64_t *r = mat + (size_t)i * words;
      int v = 0;
      for (int j = 0; j < nf; ++j)
        if (kx[free_col[j]] &&
            ((r[free_col[j] >> 6] >> (free_col[j] & 63)) & 1u))
          v ^= 1;
      kx[pivot_col[i]] = (uint8_t)v;
    }
    int kw = 0;
    for (int p = 0; p < n; ++p)
      kw += kx[p];
    if (kw < kernel_dmin)
      kernel_dmin = kw;
  }
  printf("# COMMON-BINARY kernel minimum distance: %d; guaranteed unique "
         "radius: %d\n",
         kernel_dmin, (kernel_dmin - 1) / 2);
  free(kx);
  uint8_t *x = calloc((size_t)n, 1);
  uint8_t *bestx = calloc((size_t)n, 1);
  int bestwt = n + 1, best_count = 0;
  uint64_t total = UINT64_C(1) << nf;
  for (uint64_t mask = 0; mask < total; ++mask) {
    memset(x, 0, (size_t)n);
    for (int j = 0; j < nf; ++j)
      x[free_col[j]] = (uint8_t)((mask >> j) & 1u);
    for (int i = 0; i < rank; ++i) {
      const uint64_t *r = mat + (size_t)i * words;
      int v = (int)((r[n >> 6] >> (n & 63)) & 1u);
      for (int j = 0; j < nf; ++j)
        if (x[free_col[j]] &&
            ((r[free_col[j] >> 6] >> (free_col[j] & 63)) & 1u))
          v ^= 1;
      x[pivot_col[i]] = (uint8_t)v;
    }
    int wt = 0;
    for (int p = 0; p < n; ++p)
      wt += x[p];
    /* Certify the reconstructed support against every used field syndrome.
     * This remains valid when recv also contains an unknown codeword. */
    int ok = 1;
    for (int bi = 0; bi < nb && ok; ++bi)
      if (basis[bi].rho <= M_SYND) {
        fe acc = 0;
        for (int p = 0; p < n; ++p)
          if (x[p])
            acc ^= basis_value_at(bi, p);
        if (acc != mul(basis_syndrome(bi), ic))
          ok = 0;
      }
    if (ok) {
      if (wt < bestwt) {
        bestwt = wt;
        best_count = 1;
        memcpy(bestx, x, (size_t)n);
      } else if (wt == bestwt) {
        ++best_count;
      }
    }
  }
  if (best_count == 1) {
    if (verbose) {
      printf("# COMMON-BINARY positions (zero-based):");
      for (int p = 0; p < n; ++p)
        if (bestx[p])
          printf(" %d", p);
      putchar('\n');
    }
    int same = 0;
    for (int e = 0; e < expected_weight; ++e)
      if (bestx[true_pos[e]])
        ++same;
    printf("# COMMON-BINARY minimum-weight support: %d; injected-position "
           "comparison: %d/%d\n",
           bestwt, same, expected_weight);
  }
  printf("# COMMON-BINARY: %s (searched %llu affine solutions)\n",
         best_count == 1  ? "unique minimum-weight position set certified"
         : best_count > 1 ? "ambiguous minimum-weight position sets"
                          : "no certified solution found",
         (unsigned long long)total);
  free(mat);
  free(pivot_col);
  free(is_pivot);
  free(free_col);
  free(x);
  free(bestx);
  return best_count == 1 ? 1 : 0;
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

static int poly_force_regular = 0;
static int poly_setup_impl(int e, int Mx, NBas *B);
/* weights of the single place at infinity (both x and y have poles there) */
static int single_inf_weights(int e, int *wx, int *wy) {
  int ninf = 0;
  for (int k = 0; k < ne; ++k)
    if (ed[k].inf)
      ninf++;
  if (ninf != 1 || !ed[e].inf || ed[e].len != 1 || ed[e].wx >= 0 ||
      ed[e].wy >= 0)
    return 0;
  *wx = -ed[e].wx;
  *wy = -ed[e].wy;
  return 1;
}
static int poly_setup(int e, int Mx, NBas *B) {
  int rc = poly_setup_impl(e, Mx, B);
  int wx, wy;
  if (rc != 0 && hermitian_q == 0 && single_inf_weights(e, &wx, &wy)) {
    poly_force_regular = 1;
    rc = poly_setup_impl(e, Mx, B);
    poly_force_regular = 0;
  }
  return rc;
}
static int poly_setup_impl(int e, int Mx, NBas *B) {
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
  if (hermitian_q > 0 || poly_force_regular) {
    /*
     * Hermitian affine coordinate ring:
     *   y^q + y + x^(q+1) = 0.
     * Its regular one-point monomials are x^i y^j (i >= 0, j >= 0),
     * and y^q is reduced by y^q = y + x^(q+1).  The generic toric cone
     * also contains Laurent monomials (for example x^i/y), which are not
     * regular on the affine curve.  Enumerate the actual polynomial
     * semigroup instead of that larger toric cone.
     */
    int wx = hermitian_q, wy = hermitian_q + 1;
    if (poly_force_regular)
      single_inf_weights(e, &wx, &wy);
    for (int i = 0; i <= Mx / wx; ++i) {
      int jmax = (Mx - wx * i) / wy;
      for (int j = 0; j <= jmax; ++j) {
        if (n0 == cap) {
          cap *= 2;
          PPt *tmp = realloc(P, cap * sizeof *P);
          if (!tmp) {
            free(P);
            return -1;
          }
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
            if (!tmp) {
              free(P);
              return -1;
            }
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
    if (P[p].i < imin)
      imin = P[p].i;
    if (P[p].i > imax)
      imax = P[p].i;
    if (P[p].j < jmin)
      jmin = P[p].j;
    if (P[p].j > jmax)
      jmax = P[p].j;
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
  {
    int cum = 0;
    for (int w = 0; w <= Mx; ++w) {
      if (pp_we[w] > 0)
        cum = pp_we[w];
      pp_upto[w] = cum;
    }
  }
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

/* -------------------------------------------------------------------------
 * Kötter / O'Sullivan one-point error-value update (generic rational edge).
 * Functions are represented in the Apéry module basis x^a z_b.  The
 * multiplication table is derived from the same Newton-cone reductions used
 * by the syndrome engine; no interpolation matrix or per-error solve occurs.
 * ------------------------------------------------------------------------- */
typedef struct {
  int a, b;
  fe v;
} KTerm;
typedef struct {
  KTerm *t;
  int n;
} KPoly;
static int kotter_xmul_ready = 0;
static int kotter_kappa = 0, kotter_amax = 0, kotter_maxw = 0;
static int kotter_axis = 0; /* 0:Y^-1, 1:X, 2:X^-1, 3:Y */
static int kotter_lam[128], kotter_zi[128], kotter_zj[128];
static KPoly kotter_E[12000];
static KPoly kotter_C[128][128];
static fe *kotter_f = NULL, *kotter_g = NULL;
static int kotter_stride_a, kotter_stride_b;

static size_t kidx(int i, int a, int b) {
  return ((size_t)i * (size_t)kotter_stride_a + (size_t)a) *
             (size_t)kotter_stride_b +
         (size_t)b;
}
static int kpoly_from_dense(KPoly *p, const fe *d, int na, int k) {
  int n = 0;
  for (int a = 0; a < na; ++a)
    for (int b = 0; b < k; ++b)
      n += d[(size_t)a * k + b] != 0;
  p->t = n ? malloc((size_t)n * sizeof(*p->t)) : NULL;
  if (n && !p->t)
    return 0;
  p->n = n;
  int z = 0;
  for (int a = 0; a < na; ++a)
    for (int b = 0; b < k; ++b) {
      fe v = d[(size_t)a * k + b];
      if (v)
        p->t[z++] = (KTerm){a, b, v};
    }
  return 1;
}
static int kotter_nf(int p, uint8_t *mark, int *list, int *nout) {
  if (p < 0 || p >= NPT)
    return 0;
  memset(mark, 0, (size_t)NPT);
  mark[p] = 1;
  for (int r = p; r >= 0; --r)
    if (mark[r] && pp_dep[r]) {
      mark[r] = 0;
      int q = pp_q[r];
      if (q < 0 || q >= r)
        return 0;
      mark[q] ^= 1;
      for (int c = 0; c < pp_nlow; ++c) {
        int v = pp_low[(size_t)r * pp_nlow + c];
        if (v < 0 || v >= r)
          return 0;
        mark[v] ^= 1;
      }
    }
  int n = 0;
  for (int r = 0; r < NPT; ++r)
    if (mark[r]) {
      if (pp_dep[r])
        return 0;
      list[n++] = r;
    }
  *nout = n;
  return 1;
}
static void kotter_toggle_poly(fe *dense, const KPoly *p) {
  for (int i = 0; i < p->n; ++i) {
    const KTerm *t = &p->t[i];
    dense[(size_t)t->a * kotter_kappa + t->b] ^= t->v;
  }
}
static int kotter_prepare_module(int edge, NBas *B) {
  if (!use_poly || !B || edge < 0 || edge >= ne)
    return 0;
  /* Generic one-point Apéry module. Choose the inverse coordinate with
   * larger pole order as x; this keeps the module rank kappa manageable.
   * The curve polynomial is read from TX/TY/TC, not matched to fixed terms. */
  if (ed[edge].len != 1 || (ed[edge].wx == 0 && ed[edge].wy == 0))
    return 0;
  if (abs(ed[edge].wx) > abs(ed[edge].wy))
    kotter_axis = ed[edge].wx < 0 ? 1 : 2;
  else
    kotter_axis = ed[edge].wy > 0 ? 0 : 3;
  kotter_kappa = (kotter_axis == 1 || kotter_axis == 2) ? abs(ed[edge].wx)
                                                        : abs(ed[edge].wy);
  if (kotter_kappa < 1 || kotter_kappa > 128 ||
      B->n <= kotter_kappa) /* EXTENSION_POINT: module-rank cap */
    return 0;
  for (int b = 0; b < kotter_kappa; ++b) {
    int h = 0;
    while (h < B->n && B->rho[h] % kotter_kappa != b)
      ++h;
    if (h == B->n)
      return 0;
    kotter_lam[b] = B->rho[h];
    kotter_zi[b] = B->ei[h];
    kotter_zj[b] = B->ej[h];
  }
  int lmax = 0;
  for (int b = 0; b < kotter_kappa; ++b)
    if (kotter_lam[b] > lmax)
      lmax = kotter_lam[b];
  kotter_maxw = 2 * lmax;
  if (kotter_maxw >= (int)(sizeof(kotter_E) / sizeof(kotter_E[0])) ||
      kotter_maxw > pp_Mx)
    return 0;
  kotter_amax = M_SYND / kotter_kappa + 8;
  if (kotter_amax < kotter_maxw / kotter_kappa + 4)
    kotter_amax = kotter_maxw / kotter_kappa + 4;
  size_t dn = (size_t)(kotter_amax + 1) * kotter_kappa;
  fe *dense = calloc(dn, sizeof(fe));
  uint8_t *mark = malloc((size_t)NPT);
  int *list = malloc((size_t)NPT * sizeof(int));
  if (!dense || !mark || !list) {
    free(dense);
    free(mark);
    free(list);
    return 0;
  }

  /* E[w] converts the canonical Newton monomial of pole order w into the
   * Apéry module basis x^a z_b.  The recursion is triangular in pole order. */
  for (int w = 0; w <= kotter_maxw; ++w) {
    int pcan = pp_rep[w];
    if (pcan < 0)
      continue;
    int b = w % kotter_kappa;
    int a = (w - kotter_lam[b]) / kotter_kappa;
    if (a < 0) {
      free(dense);
      free(mark);
      free(list);
      return 0;
    }
    int I = kotter_zi[b], J = kotter_zj[b];
    if (kotter_axis == 0)
      J -= a;
    else if (kotter_axis == 1)
      I += a;
    else if (kotter_axis == 2)
      I -= a;
    else
      J += a;
    int p = pp_at(I, J), nn = 0;
    if (!kotter_nf(p, mark, list, &nn)) {
      free(dense);
      free(mark);
      free(list);
      return 0;
    }
    memset(dense, 0, dn * sizeof(fe));
    dense[(size_t)a * kotter_kappa + b] = 1;
    int saw_top = 0;
    for (int q = 0; q < nn; ++q) {
      int r = list[q], wr = pp_w[r];
      if (wr == w) {
        if (r != pcan) {
          free(dense);
          free(mark);
          free(list);
          return 0;
        }
        saw_top = 1;
      } else if (wr < w)
        kotter_toggle_poly(dense, &kotter_E[wr]);
      else {
        free(dense);
        free(mark);
        free(list);
        return 0;
      }
    }
    if (!saw_top ||
        !kpoly_from_dense(&kotter_E[w], dense, kotter_amax + 1, kotter_kappa)) {
      free(dense);
      free(mark);
      free(list);
      return 0;
    }
  }

  /* Multiplication table z_j*z_c in the Apéry basis. */
  for (int j = 0; j < kotter_kappa; ++j)
    for (int c = 0; c < kotter_kappa; ++c) {
      int p = pp_at(kotter_zi[j] + kotter_zi[c], kotter_zj[j] + kotter_zj[c]);
      int nn = 0;
      if (!kotter_nf(p, mark, list, &nn)) {
        free(dense);
        free(mark);
        free(list);
        return 0;
      }
      memset(dense, 0, dn * sizeof(fe));
      for (int q = 0; q < nn; ++q)
        kotter_toggle_poly(dense, &kotter_E[pp_w[list[q]]]);
      if (!kpoly_from_dense(&kotter_C[j][c], dense, kotter_amax + 1,
                            kotter_kappa)) {
        free(dense);
        free(mark);
        free(list);
        return 0;
      }
    }
  free(dense);
  free(mark);
  free(list);
  kotter_stride_a = kotter_amax + 1;
  kotter_stride_b = kotter_kappa;
  size_t fn = (size_t)kotter_kappa * kotter_stride_a * kotter_stride_b;
  kotter_f = calloc(fn, sizeof(fe));
  kotter_g = calloc(fn, sizeof(fe));
  if (!kotter_f || !kotter_g)
    return 0;
  for (int i = 0; i < kotter_kappa; ++i)
    kotter_f[kidx(i, 0, i)] = 1;
  kotter_xmul_ready = 1;
  return 1;
}
static int kotter_rho(const fe *f, int i) {
  int d = -1;
  for (int a = 0; a <= kotter_amax; ++a)
    for (int b = 0; b < kotter_kappa; ++b)
      if (f[kidx(i, a, b)]) {
        int w = a * kotter_kappa + kotter_lam[b];
        if (w > d)
          d = w;
      }
  return d;
}
static fe kotter_syndrome(int a, int b) {
  if (a < 0)
    return 0;
  int I = kotter_zi[b], J = kotter_zj[b];
  if (kotter_axis == 0)
    J -= a;
  else if (kotter_axis == 1)
    I += a;
  else if (kotter_axis == 2)
    I -= a;
  else
    J += a;
  int p = pp_at(I, J);
  if (p < 0 || pp_w[p] > M_SYND)
    return 0;
  return pp_S[p];
}
static fe kotter_mu(const fe *f, int i, int j, int r) {
  fe mu = 0;
  for (int a = 0; a <= kotter_amax; ++a)
    for (int c = 0; c < kotter_kappa; ++c) {
      fe fc = f[kidx(i, a, c)];
      if (!fc)
        continue;
      const KPoly *p = &kotter_C[j][c];
      for (int z = 0; z < p->n; ++z) {
        const KTerm *t = &p->t[z];
        fe s = kotter_syndrome(a + t->a + r, t->b);
        if (s)
          mu ^= mul(fc, mul(t->v, s));
      }
    }
  return mu;
}
static fe kotter_partial_curve(fe X, fe Y, int dx) {
  fe acc = 0;
  for (int t = 0; t < T; ++t) {
    int e = dx ? TX[t] : TY[t];
    if (e & 1) {
      int I = TX[t] - (dx ? 1 : 0);
      int J = TY[t] - (dx ? 0 : 1);
      acc ^= mul(TC[t], mono_eval(X, Y, I, J));
    }
  }
  return acc;
}

/* Differentiate a function on F(X,Y)=0 with respect to the selected
 * pole coordinate x (one of X, X^-1, Y, Y^-1). */
static int kotter_eval_derivative(const fe *f, int i, fe X, fe Y, fe *out) {
  if (!X || !Y)
    return 0;
  fe FX = kotter_partial_curve(X, Y, 1);
  fe FY = kotter_partial_curve(X, Y, 0);
  fe X2 = mul(X, X), Y2 = mul(Y, Y);
  fe dXdx = 0, dYdx = 0;
  switch (kotter_axis) {
  case 0: /* x=Y^-1 */
    if (!FX)
      return 0;
    dXdx = mul(mul(FY, Y2), inv(FX));
    dYdx = Y2;
    break;
  case 1: /* x=X */
    if (!FY)
      return 0;
    dXdx = 1;
    dYdx = mul(FX, inv(FY));
    break;
  case 2: /* x=X^-1 */
    if (!FY)
      return 0;
    dXdx = X2;
    dYdx = mul(mul(FX, X2), inv(FY));
    break;
  default: /* x=Y */
    if (!FX)
      return 0;
    dXdx = mul(FY, inv(FX));
    dYdx = 1;
    break;
  }
  fe acc = 0;
  for (int a = 0; a <= kotter_amax; ++a)
    for (int b = 0; b < kotter_kappa; ++b) {
      fe c = f[kidx(i, a, b)];
      if (!c)
        continue;
      int I = kotter_zi[b], J = kotter_zj[b];
      if (kotter_axis == 0)
        J -= a;
      else if (kotter_axis == 1)
        I += a;
      else if (kotter_axis == 2)
        I -= a;
      else
        J += a;
      if (I & 1)
        acc ^= mul(c, mul(mono_eval(X, Y, I - 1, J), dXdx));
      if (J & 1)
        acc ^= mul(c, mul(mono_eval(X, Y, I, J - 1), dYdx));
    }
  *out = acc;
  return 1;
}

static int resolve_by_kotter(int *found, int *nfound) {
  if (!kotter_xmul_ready || !found || !nfound || *nfound <= 0 || *nfound > MAXT)
    return 0;
  const int k = kotter_kappa, A = kotter_amax,
            stride = kotter_stride_a * kotter_stride_b;
  memset(kotter_f, 0, (size_t)k * stride * sizeof(fe));
  memset(kotter_g, 0, (size_t)k * stride * sizeof(fe));
  for (int i = 0; i < k; ++i)
    kotter_f[kidx(i, 0, i)] = 1;
  fe *oldf = malloc((size_t)stride * sizeof(fe));
  if (!oldf)
    return 0;
  fe *oldf2 = malloc((size_t)stride * sizeof(fe));
  if (!oldf2) {
    free(oldf);
    return 0;
  }
  for (int m = 0; m <= M_SYND; ++m) {
    for (int i = 0; i < k; ++i) {
      int j = (m - i) % k;
      if (j < 0)
        j += k;
      /* The paper's "pair i,j" is unordered.  Process {i,j} once,
       * applying the symmetric update to (f_i,g_j) and (f_j,g_i). */
      if (i > j)
        continue;
      int di = kotter_rho(kotter_f, i), dj = kotter_rho(kotter_f, j);
      if (di < 0 || dj < 0 || (m - di - kotter_lam[j]) % k ||
          (m - dj - kotter_lam[i]) % k) {
        free(oldf);
        free(oldf2);
        return 0;
      }
      int ri = (m - di - kotter_lam[j]) / k;
      int rj = (m - dj - kotter_lam[i]) / k;
      fe mui = kotter_mu(kotter_f, i, j, ri);
      fe muj = (i == j) ? mui : kotter_mu(kotter_f, j, i, rj);
      if (mui != muj) {
        free(oldf);
        free(oldf2);
        return 0;
      }
      int p = (di + dj - m) / k - 1;
      fe *fi = kotter_f + (size_t)i * stride;
      fe *gj = kotter_g + (size_t)j * stride;
      fe *fj = kotter_f + (size_t)j * stride;
      fe *gi = kotter_g + (size_t)i * stride;
      if (!mui || p >= 0) {
        if (mui) {
          for (int a = 0; a <= A; ++a) {
            int src = a - p;
            if (src < 0)
              continue;
            for (int b = 0; b < k; ++b) {
              fe v = gj[(size_t)src * k + b];
              if (v)
                fi[(size_t)a * k + b] ^= mul(mui, v);
              if (i != j) {
                v = gi[(size_t)src * k + b];
                if (v)
                  fj[(size_t)a * k + b] ^= mul(mui, v);
              }
            }
          }
        }
      } else {
        int sh = -p;
        memcpy(oldf, fi, (size_t)stride * sizeof(fe));
        if (i != j)
          memcpy(oldf2, fj, (size_t)stride * sizeof(fe));
        fe im = inv(mui);
        for (int a = 0; a <= A; ++a)
          for (int b = 0; b < k; ++b) {
            size_t z = (size_t)a * k + b;
            fe v = (a >= sh) ? oldf[(size_t)(a - sh) * k + b] : 0;
            if (gj[z])
              v ^= mul(mui, gj[z]);
            fi[z] = v;
            if (i != j) {
              v = (a >= sh) ? oldf2[(size_t)(a - sh) * k + b] : 0;
              if (gi[z])
                v ^= mul(mui, gi[z]);
              fj[z] = v;
            }
          }
        for (int a = 0; a <= A; ++a)
          for (int b = 0; b < k; ++b) {
            size_t z = (size_t)a * k + b;
            gj[z] = mul(im, oldf[z]);
            if (i != j)
              gi[z] = mul(im, oldf2[z]);
          }
      }
    }
  }
  free(oldf2);
  free(oldf);
  int n = *nfound;
  fe *vals = malloc((size_t)n * sizeof(fe));
  if (!vals)
    return 0;
  for (int u = 0; u < n; ++u) {
    fe X = PXv[found[u]], Y = PYv[found[u]], sum = 0;
    for (int i = 0; i < k; ++i) {
      fe fp = 0;
      if (!kotter_eval_derivative(kotter_f, i, X, Y, &fp)) {
        free(vals);
        return 0;
      }
      fe gp = 0;
      for (int a = 0; a <= kotter_amax; ++a)
        for (int b = 0; b < k; ++b) {
          fe c = kotter_g[kidx(i, a, b)];
          if (c) {
            int I = kotter_zi[b], J = kotter_zj[b];
            if (kotter_axis == 0)
              J -= a;
            else if (kotter_axis == 1)
              I += a;
            else if (kotter_axis == 2)
              I -= a;
            else
              J += a;
            gp ^= mul(c, mono_eval(X, Y, I, J));
          }
        }
      sum ^= mul(fp, gp);
    }
    if (!sum) {
      free(vals);
      return 0;
    }
    vals[u] = inv(sum);
  } 
  /* Independent full syndrome verification. */
  int nb = count_basis_upto(M_SYND);
  for (int a = 0; a < nb; ++a) {
    fe check = 0;
    for (int u = 0; u < n; ++u)
      check ^= mul(vals[u], basis_value_at(a, found[u]));
    if (check != synd1(a)) {
      free(vals);
      return 0;
    }
  }
  for (int u = 0; u < n; ++u)
    err_val[u] = vals[u];
  free(vals);
  return 1;
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
/* Explicit BMS doubled-syndrome matrix diagnostic.
 * For basis functions f_i with rho(f_i) <= floor(M/2), form
 *     S2[i,j] = S(f_i f_j) = sum_k e_k f_i(P_k) f_j(P_k).
 * This is the finite square submatrix of the product-syndrome array
 * (the 2Sigma construction).  The normal BMS path accesses the same entries
 * implicitly through pp_shift()/poly_xdisc(); this routine materializes them
 * only for a small diagnostic run and checks them against pp_S.
 */
static int bms2_check_enabled = 0;
static int bms2_syndrome_check(void) {
  int ids[MAXB], r = 0, mismatch = 0, entries = 0;
  if (!use_poly || !pp_S || !bas_ei || !bas_ej) {
    puts("# BMS2: unavailable (Newton monomial syndrome table is not active)");
    return -1;
  }
  for (int bi = 0; bi < nbasis; ++bi)
    if (basis[bi].rho <= M_SYND / 2)
      ids[r++] = bi;
  if (r <= 0) {
    puts("# BMS2: empty product-syndrome matrix");
    return -1;
  }
  /* This explicit O(r^3) diagnostic is intentionally limited to small
   * instances; the production BMS path does not materialize this matrix. */
  if (r > 256) {
    printf("# BMS2: extraction skipped (matrix dimension %d exceeds diagnostic "
           "cap 256)\n",
           r);
    return -1;
  }
  fe *mat = calloc((size_t)r * (size_t)r, sizeof(fe));
  if (!mat) {
    puts("# BMS2: allocation failed");
    return -1;
  }
  for (int i = 0; i < r; ++i) {
    int bi = ids[i];
    for (int j = 0; j < r; ++j) {
      int bj = ids[j];
      fe v = 0;
      for (int z = 0; z < nz_cnt; ++z) {
        int k = nz_idx[z];
        fe vi = basis_value_at(bi, k);
        fe vj = basis_value_at(bj, k);
        v ^= mul(recv[k], mul(vi, vj));
      }
      mat[(size_t)i * r + j] = v;
      int t = pp_at(bas_ei[bi] + bas_ei[bj], bas_ej[bi] + bas_ej[bj]);
      if (t < 0 || pp_w[t] > M_SYND || pp_S[t] != v)
        ++mismatch;
      else
        ++entries;
    }
  }
  /* Reduced row-echelon form over GF(2^m).  We retain pivot columns so
   * that the full nullspace, not just the rank, is available below. */
  int *pivot_col = malloc((size_t)r * sizeof(*pivot_col));
  if (!pivot_col) {
    free(mat);
    puts("# BMS2: pivot allocation failed");
    return -1;
  }
  int rank = 0;
  for (int col = 0; col < r; ++col) {
    int piv = rank;
    while (piv < r && mat[(size_t)piv * r + col] == 0)
      ++piv;
    if (piv == r)
      continue;
    if (piv != rank)
      for (int j = 0; j < r; ++j) {
        fe tmp = mat[(size_t)rank * r + j];
        mat[(size_t)rank * r + j] = mat[(size_t)piv * r + j];
        mat[(size_t)piv * r + j] = tmp;
      }
    fe ip = inv(mat[(size_t)rank * r + col]);
    for (int j = 0; j < r; ++j)
      mat[(size_t)rank * r + j] = mul(mat[(size_t)rank * r + j], ip);
    for (int i = 0; i < r; ++i) {
      if (i == rank)
        continue;
      fe c = mat[(size_t)i * r + col];
      if (!c)
        continue;
      for (int j = 0; j < r; ++j)
        mat[(size_t)i * r + j] ^= mul(c, mat[(size_t)rank * r + j]);
    }
    pivot_col[rank++] = col;
  }
  int nullity = r - rank;
  printf("# BMS2: explicit product-syndrome matrix %d x %d, ", r, r);
  printf("rank=%d, nullity=%d, injected errors=%d\n", rank, nullity, nz_cnt);
  printf("# BMS2: checked entries=%d, mismatches=%d; entries are ", entries,
         mismatch);
  puts("S_ij = sum_e e_k f_i(P_k) f_j(P_k) = S(f_i f_j)");
  if (mismatch || nullity <= 0) {
    if (!nullity)
      puts("# BMS2: nullspace is trivial; cannot extract common zeros");
    free(pivot_col);
    free(mat);
    return mismatch ? -1 : rank;
  }
  if (nullity > 512 || r > 2048) {
    printf("# BMS2: extraction skipped (r=%d, nullity=%d; diagnostic cap "
           "r<=2048, nullity<=512)\n",
           r, nullity);
    free(pivot_col);
    free(mat);
    return rank;
  }
  uint8_t *is_pivot = calloc((size_t)r, 1);
  fe *ker = calloc((size_t)nullity * (size_t)r, sizeof(fe));
  if (!is_pivot || !ker) {
    free(is_pivot);
    free(ker);
    free(pivot_col);
    free(mat);
    puts("# BMS2: nullspace allocation failed");
    return -1;
  }
  for (int i = 0; i < rank; ++i)
    is_pivot[pivot_col[i]] = 1;
  int q = 0;
  for (int free_col = 0; free_col < r; ++free_col)
    if (!is_pivot[free_col]) {
      fe *v = ker + (size_t)q * r;
      v[free_col] = 1;
      for (int i = 0; i < rank; ++i)
        v[pivot_col[i]] = mat[(size_t)i * r + free_col];
      ++q;
    }
  /* A point is a common zero precisely when every nullspace function
   * evaluates to zero there.  For a full-row-rank error evaluation matrix,
   * these common zeros are the error support. */
  int found[MAXT + 1], nfound = 0, too_many = 0;
  for (int p = 0; p < npts; ++p) {
    int common_zero = 1;
    for (int h = 0; h < nullity && common_zero; ++h) {
      const fe *v = ker + (size_t)h * r;
      fe value = 0;
      for (int j = 0; j < r; ++j)
        if (v[j])
          value ^= mul(v[j], basis_value_at(ids[j], p));
      if (value)
        common_zero = 0;
    }
    if (common_zero) {
      if (nfound < MAXT)
        found[nfound++] = p;
      else
        too_many = 1;
    }
  }
  printf("# BMS2: nullspace common-zero candidates=%s%d\n",
         too_many ? ">=" : "", nfound);
  if (!too_many && nfound > 0 && resolve_by_values(found, &nfound)) {
    int same = 0;
    for (int i = 0; i < nfound; ++i)
      for (int j = 0; j < NUM_ERRORS; ++j)
        if (found[i] == true_pos[j] && err_val[i] == recv[true_pos[j]]) {
          ++same;
          break;
        }
    printf("# BMS2: value solve recovered=%d, exact position/value "
           "matches=%d/%d -> %s\n",
           nfound, same, NUM_ERRORS,
           (nfound == NUM_ERRORS && same == NUM_ERRORS) ? "SUCCESS"
                                                        : "MISMATCH");
  } else {
    puts("# BMS2: value solve failed (candidate set is not the exact error "
         "support)");
  }
  free(is_pivot);
  free(ker);
  free(pivot_col);
  free(mat);
  return mismatch ? -1 : rank;
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
/* Exact NTT convolution for the majority-vote candidate counts.
 * MOD is larger than M_EXT, so every coefficient is an exact integer count,
 * not merely a residue. */
#define FRV_NTT_MOD 998244353u
#define FRV_NTT_ROOT 3u
static uint32_t frv_mod_pow(uint32_t a, uint32_t e) {
  uint64_t r = 1, x = a;
  while (e) {
    if (e & 1u)
      r = (r * x) % FRV_NTT_MOD;
    x = (x * x) % FRV_NTT_MOD;
    e >>= 1;
  }
  return (uint32_t)r;
}
static void frv_ntt(uint32_t *a, int n, int invert) {
  for (int i = 1, j = 0; i < n; ++i) {
    int bit = n >> 1;
    for (; j & bit; bit >>= 1)
      j ^= bit;
    j ^= bit;
    if (i < j) {
      uint32_t t = a[i];
      a[i] = a[j];
      a[j] = t;
    }
  }
  for (int len = 2; len <= n; len <<= 1) {
    uint32_t wlen =
        frv_mod_pow(FRV_NTT_ROOT, (FRV_NTT_MOD - 1u) / (uint32_t)len);
    if (invert)
      wlen = frv_mod_pow(wlen, FRV_NTT_MOD - 2u);
    for (int i = 0; i < n; i += len) {
      uint64_t w = 1;
      int half = len >> 1;
      for (int j = 0; j < half; ++j) {
        uint32_t u = a[i + j];
        uint32_t v = (uint32_t)((uint64_t)a[i + j + half] * w % FRV_NTT_MOD);
        uint32_t x = u + v;
        if (x >= FRV_NTT_MOD)
          x -= FRV_NTT_MOD;
        uint32_t y = u >= v ? u - v : u + FRV_NTT_MOD - v;
        a[i + j] = x;
        a[i + j + half] = y;
        w = w * wlen % FRV_NTT_MOD;
      }
    }
  }
  if (invert) {
    uint32_t invn = frv_mod_pow((uint32_t)n, FRV_NTT_MOD - 2u);
    for (int i = 0; i < n; ++i)
      a[i] = (uint32_t)((uint64_t)a[i] * invn % FRV_NTT_MOD);
  }
}
static int frv_build_vote_convolutions(void) {
  const int L = M_EXT + 1;
  const int need = 2 * L - 1;
  int ntt_n = 1;
  while (ntt_n < need && ntt_n < (1 << 23))
    ntt_n <<= 1;
  if (ntt_n < need || (uint64_t)(M_EXT + 1) >= FRV_NTT_MOD)
    return -1;
  uint32_t *fb = calloc((size_t)ntt_n, sizeof(uint32_t));
  uint32_t *fa = calloc((size_t)ntt_n, sizeof(uint32_t));
  size_t count_len = (size_t)(M_EXT - M_SYND);
  uint32_t *counts = calloc((size_t)ngen * count_len, sizeof(uint32_t));
  if (!fb || !fa || !counts) {
    free(fb);
    free(fa);
    free(counts);
    return -1;
  }
  for (int j = 0; j <= M_EXT; ++j)
    if (in_H[j] && !colused[j])
      fb[j] = 1;
  frv_ntt(fb, ntt_n, 0);
  for (int g = 0; g < ngen; ++g) {
    memset(fa, 0, (size_t)ntt_n * sizeof(uint32_t));
    for (int i = 0; i <= M_EXT; ++i)
      if (frv_ancestor[i] == g)
        fa[i] = 1;
    frv_ntt(fa, ntt_n, 0);
    for (int k = 0; k < ntt_n; ++k)
      fa[k] = (uint32_t)((uint64_t)fa[k] * fb[k] % FRV_NTT_MOD);
    frv_ntt(fa, ntt_n, 1);
    uint32_t *dst = counts + (size_t)g * count_len;
    for (int n = M_SYND + 1; n <= M_EXT; ++n)
      dst[n - (M_SYND + 1)] = fa[n];
  }
  free(fb);
  free(fa);
  free(frv_vote_counts);
  frv_vote_counts = counts;
  frv_vote_count_len = (int)count_len;
  frv_vote_conv_ready = 1;
  return 0;
}

/* Build sparse supports once after the FR kernel has produced its locators.
 * The ancestor of a pole order i depends only on i and the locator ideal, not
 * on the syndrome order n; precomputing it removes the inner generator scan
 * from every majority-vote step. */
static int frv_build_sparse(void) {
  for (int g = 0; g < ngen; ++g) {
    int lim = pp_upto[gens[g].b], nnz = 0;
    for (int p = 0; p < lim; ++p)
      nnz += gens[g].f[p] != 0;
    frv_support_idx[g] = nnz ? malloc((size_t)nnz * sizeof(int)) : NULL;
    frv_support_val[g] = nnz ? malloc((size_t)nnz * sizeof(fe)) : NULL;
    if (nnz && (!frv_support_idx[g] || !frv_support_val[g]))
      return -1;
    frv_support_n[g] = nnz;
    int z = 0;
    for (int p = 0; p < lim; ++p)
      if (gens[g].f[p]) {
        frv_support_idx[g][z] = p;
        frv_support_val[g][z] = gens[g].f[p];
        ++z;
      }
  }
  for (int i = 0; i <= M_EXT; ++i) {
    frv_ancestor[i] = -1;
    if (!in_H[i] || is_piv[i])
      continue;
    for (int g = 0; g < ngen; ++g) {
      int a = i - gens[g].b;
      if (a >= 0 && in_H[a]) {
        frv_ancestor[i] = g;
        break;
      }
    }
  }
  frv_support_ready = 1;
  /* The convolution path replaces O(M_EXT^2) candidate scans by a small
   * number of O(N log N) exact convolutions.  If it cannot be allocated, the
   * original exact scan remains available. */
  (void)frv_build_vote_convolutions();
  return 0;
}
static fe poly_ext_known_sparse(int g, int m, int n, fe *an) {
  int r = pp_rep[m], ri = pp_i[r], rj = pp_j[r];
  fe known = 0, a = 0;
  for (int z = 0; z < frv_support_n[g]; ++z) {
    int p = frv_support_idx[g][z];
    fe c = frv_support_val[g][z];
    int t = pp_shift(p, ri, rj);
    if (pp_w[t] < n)
      known ^= mul(c, pp_S[t]);
    else {
      a ^= mul(c, pp_lam[t]);
      known ^= mul(c, pp_K[t]);
    }
  }
  *an = a;
  return known;
}
static int poly_nonzero_sparse(int g, int k) {
  fe acc = 0;
  for (int z = 0; z < frv_support_n[g]; ++z) {
    int p = frv_support_idx[g][z];
    acc ^=
        mul(frv_support_val[g][z], mono_eval(PXv[k], PYv[k], pp_i[p], pp_j[p]));
  }
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
      fe an, known = (use_poly && frv_support_ready)
                         ? poly_ext_known_sparse(g, m, n, &an)
                         : ext_known_b(gens[g].f, gens[g].b, m, n, &an);
      if (!an) {
        fprintf(stderr, "vote: zero leading coefficient (n=%d)\n", n);
        return -1;
      }
      pred[g] = mul(known, inv(an));
    }
  }
  if (frv_vote_conv_ready && frv_support_ready) {
    /* Count all (i,j) pairs with i+j=n by locator ancestor using exact
     * integer convolutions.  Group equal predicted field values afterwards. */
    for (int g = 0; g < ngen; ++g) {
      uint32_t cnt = frv_vote_counts[(size_t)g * frv_vote_count_len +
                                     (size_t)(n - M_SYND - 1)];
      if (!validg[g] || !cnt)
        continue;
      ncand += (int)cnt;
      int s = 0;
      while (s < nd && dv[s] != pred[g])
        ++s;
      if (s == nd) {
        dv[nd] = pred[g];
        dc[nd] = 0;
        ++nd;
      }
      dc[s] += (int)cnt;
    }
  } else {
    /* Exact reference path, retained as a fallback. */
    for (int i = 0; i <= n; ++i) {
      int j = n - i, anc = -1, s;
      if (!in_H[i] || is_piv[i] || !in_H[j] || colused[j])
        continue;
      anc = frv_support_ready ? frv_ancestor[i] : -1;
      if (!frv_support_ready) {
        for (int g = 0; g < ngen; ++g)
          if (gens[g].b <= i && in_H[i - gens[g].b]) {
            anc = g;
            break;
          }
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
  if (frv_vote_conv_ready && frv_support_ready && margin <= 0) {
    /* The convolution gives exact vote counts, but not the order in which
     * equal-count predictions first appeared.  Re-run only tied steps with
     * the original i-ascending scan to preserve the previous tie-break. */
    nd = ncand = 0;
    for (int i = 0; i <= n; ++i) {
      int j = n - i, anc = frv_ancestor[i], ss;
      if (anc < 0 || !in_H[j] || colused[j] || !validg[anc])
        continue;
      ++ncand;
      for (ss = 0; ss < nd; ++ss)
        if (dv[ss] == pred[anc])
          break;
      if (ss == nd) {
        dv[nd] = pred[anc];
        dc[nd] = 0;
        ++nd;
      }
      ++dc[ss];
    }
    best = 0;
    second = 0;
    for (int ss = 1; ss < nd; ++ss)
      if (dc[ss] > dc[best])
        best = ss;
    for (int ss = 0; ss < nd; ++ss)
      if (ss != best && dc[ss] > second)
        second = dc[ss];
    margin = dc[best] - second;
  }
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
static int decode_fr_vote_pass(Result *R, int verbose, int quiet,
                               int row_limit) {
  double t0 = now();
  int nrows, nl, nsel = 0, nfound = 0, overflow = 0;
  int sel[MAXGEN];

  memset(R, 0, sizeof *R);
  R->vote_min_margin = 1 << 30;
  if (!use_poly) {
    fprintf(stderr, "FR-VOTE requires the Newton monomial syndrome path; "
                    "enable it with the default Newton setup (do not use "
                    "-nopoly/-nonewton).\n");
    R->failed = 1;
    return -1;
  }

  memset(xhat, 0, sizeof xhat);
  memset(is_piv, 0, sizeof is_piv);
  memset(colused, 0, sizeof colused);
  bms_cleanup();

  nrows = feng_rao_reduce(row_limit);
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
    if (i < 0 || i >= nl || i >= nrows || piv_of_row[i] >= 0)
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
                "(b=%d, basis=%d, index=%d).\n",
                b, k, z);
        R->failed = 1;
        bms_cleanup();
        return -1;
      }
      gens[ngen].f[z] ^= c;
    }
    ++ngen;
  }

  if (ngen == 0) {
    fprintf(
        stderr,
        "FR-VOTE: no locator generators were obtained from the FR kernel.\n");
    R->failed = 1;
    return -1;
  }
  if (frv_build_sparse() != 0) {
    fprintf(stderr, "FR-VOTE: cannot allocate sparse locator supports.\n");
    R->failed = 1;
    bms_cleanup();
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
           R->T, R->vote_steps, R->vote_min_margin, R->vote_wrong, R->vote_tie);
  }

  t0 = now();
  if (nsel == 0) {
    fprintf(stderr,
            "FR-VOTE: no locator generators satisfy the Feng-Rao bound.\n");
    R->failed = 1;
    bms_cleanup();
    return -1;
  }
  for (int k = 0; k < npts; ++k) {
    int vanish = 1;
    for (int q = 0; q < nsel && vanish; ++q)
      if (frv_support_ready ? poly_nonzero_sparse(sel[q], k)
                            : poly_nonzero(gens[sel[q]].f, gens[sel[q]].b, k))
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
  if (!quiet) {
    puts("# FR-VOTE locator zero counts on the evaluation-point set:");
    for (int q = 0; q < nsel; ++q) {
      int zeros = 0, true_hits = 0;
      for (int p = 0; p < npts; ++p) {
        int iszero = frv_support_ready
                         ? !poly_nonzero_sparse(sel[q], p)
                         : !poly_nonzero(gens[sel[q]].f, gens[sel[q]].b, p);
        if (iszero) {
          ++zeros;
          for (int e = 0; e < NUM_ERRORS; ++e)
            if (true_pos[e] == p) {
              ++true_hits;
              break;
            }
        }
      }
      printf(
          "#   G_%d (rho=%d): zeros=%d, injected-error points among them=%d\n",
          q, gens[sel[q]].b, zeros, true_hits);
    }
    int common_true = 0;
    for (int e = 0; e < NUM_ERRORS; ++e)
      for (int k = 0; k < R->nfound; ++k)
        if (true_pos[e] == R->pos[k]) {
          ++common_true;
          break;
        }
    printf("# FR-VOTE common zero set: %d points; injected-error points in "
           "it=%d/%d\n",
           R->nfound, common_true, NUM_ERRORS);
  }
  bms_cleanup();
  resolve_and_store(R);
  return 0;
}

static void bms_cleanup(void) {
  for (int g = 0; g < MAXGEN; ++g) {
    free(frv_support_idx[g]);
    free(frv_support_val[g]);
    frv_support_idx[g] = NULL;
    frv_support_val[g] = NULL;
    frv_support_n[g] = 0;
  }
  frv_support_ready = 0;
  free(frv_vote_counts);
  frv_vote_counts = NULL;
  frv_vote_count_len = 0;
  frv_vote_conv_ready = 0;
  for (int g = 0; g < ngen; ++g)
    free(gens[g].f);
  ngen = 0;
  for (int m = 0; m < SGMAX; ++m) {
    free(pivvec[m]);
    pivvec[m] = NULL;
  }
}

/* Fast FR-VOTE first reduces only the rows that can produce locator
 * coefficient vectors.  This is a candidate solution, not an unchecked
 * truncation: the existing error-value solver verifies the recovered values
 * against the complete available syndrome sequence.  If it cannot certify
 * the result, retry with the original full row range. */
static int frv_known_syndromes_nonzero(void) {
  for (int p = 0; p < NPT; ++p)
    if (pp_w[p] <= M_SYND && pp_S[p])
      return 1;
  return 0;
}
static int decode_fr_vote(Result *R, int verbose, int quiet) {
  /* Small prefixes are tried first.  A result is accepted only when the
   * existing full-syndrome error-value check certifies it; otherwise enlarge
   * the prefix and ultimately fall back to the original full reduction. */
  int limits[] = {4096, 8192, 16384, count_basis_upto(L_DEG), 0};
  const int nlimits = (int)(sizeof(limits) / sizeof(limits[0]));
  int rc = -1, previous_limit = -1;
  for (int pass = 0; pass < nlimits; ++pass) {
    int lim = limits[pass];
    if (lim > 0 && lim <= previous_limit)
      continue;
    previous_limit = lim;
    rc = decode_fr_vote_pass(R, verbose, quiet, lim);
    if (rc == 0 && R->resolved && (R->T != 0 || !frv_known_syndromes_nonzero()))
      return 0;
    if (pass + 1 < nlimits) {
      fprintf(stderr,
              "# FR-VOTE: prefix %d was not certified; expanding reduction.\n",
              lim ? lim : count_basis_upto(ROW_MAX));
      bms_cleanup();
      poly_syndromes(); /* discard tentative unknown syndromes */
    }
  }
  if (rc == 0 && R->T == 0 && frv_known_syndromes_nonzero()) {
    R->resolved = 0;
    R->failed = 1;
    return -1;
  }
  return rc;
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
          vaxpy_b(ng[nn].f, mul(ng[nn].d, inv(pivd[m])), pivvec[m],
                  use_poly ? pivb[m] : 0);
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
static fe true_val[MAXT];

/* Print the injected values next to the values recovered by one decoder. */
static void show_error_values(const char *name, const Result *R) {
  printf("# %s error details (%d injected, %d recovered)\n", name, NUM_ERRORS,
         R->nfound);
  puts("# pos       (X,Y)          error     before    after     corrected  "
       "match");
  for (int e = 0; e < NUM_ERRORS; ++e) {
    fe got = 0;
    int found = 0;
    int p = true_pos[e];
    for (int k = 0; k < R->nfound; ++k) {
      if (R->pos[k] == p) {
        got = R->val[k];
        found = 1;
        break;
      }
    }
    /* This simulator transmits the all-zero codeword.  Thus before=0,
       after=the injected symbol, and corrected=after XOR decoded error. */
    fe before = 0;
    fe after = recv ? recv[p] : true_val[e];
    fe corrected = found ? (fe)(after ^ got) : after;
    printf("# %-9d (%03X,%03X)   0x%03X    0x%03X    0x%03X    0x%03X    %s\n",
           p, (unsigned)PXv[p], (unsigned)PYv[p], (unsigned)true_val[e],
           (unsigned)before, (unsigned)after, (unsigned)corrected,
           found && got == true_val[e] && corrected == before
               ? "OK"
               : (found ? "MISMATCH" : "MISSING"));
  }
  puts("# Position condition: (X,Y) is a common zero of the displayed "
       "L_i(X,Y).");
}

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

static int fixed_error_value = 0; /* 0=random nonzero; otherwise force every
                                     injected error to this field element */
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
    if (fixed_error_value > 0) {
      r[p] = (fe)fixed_error_value;
    } else {
      do {
        r[p] = (fe)(rnd() % (uint64_t)FS);
      } while (!r[p]);
    }
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
        fprintf(stderr,
                "# WARNING: monomial relation self-check failed at %d "
                "points\n",
                bad);
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
  int mm = n - g -
           2; /* M+g <= n-2: injective evaluation, one point may be dropped */
  if (mm > MAXB - 2)
    mm = MAXB - 2; /* basis array holds M+1 functions */
  return mm;
}
static void print_limits(int g, int n, int t) {
  int Mmax = limit_Mmax(g, n), cap = MAXT - 2;
  puts("# ---- parameter limits (this build, this curve) ----");
  printf("#   field GF(2^m): m <= 12;  here g = %d, n = %d positions, build "
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
      "  --m m            base field GF(2^m), m <= 12             (default 6)\n"
      "  --poly 0x43      primitive polynomial of GF(2^m)       (default: "
      "standard)\n"
      "  --curve bbgs|hermitian|suzuki  select a built-in curve family (default "
      "bbgs)\n"
      "  --q auto|power-of-2   BBGS parameter q (power of 2); Suzuki: "
      "q=2^(2n+1), default 8 (own engine; uses --M --errors -n)\n"
      "  --a A --b B      BBGS coprime positive parameters (default 1,2); "
      "c=a+b\n"
      "  BBGS field is GF(q^c), c=a+b; curve has c+1 terms\n"
      "  --terms \"16,0;0,1;15,4;12,16\"   custom X-monic curve instead (X^i "
      "Y^j, optionally \"i,j,coef\"); X-monic\n"
      "  --errors t       number of injected errors              (default "
      "256)\n"
      "  --fixed-error-value v  use the same nonzero field value at every "
      "error\n"
      "  -common-binary    experimental GF(2) position-only decoder (small "
      "cases)\n"
      "  -bms2-check       build S(f_i f_j), compute its GF(2^m) nullspace,\n"
      "                    scan common zeros and solve error values (small "
      "cases)\n"
      "  --M M            syndrome bound / pole order (default 2t+2g)\n"
      "  --len L | -half  puncture: use only the first L points (or half of "
      "them) as positions\n"
      "  --place k        pole place (index from the list); default: automatic "
      "choice\n"
      "  --pole \"E2:140,E1:85\" or \"#3:100\"   multi-point divisor (E<k>: "
      "edge, #k: orbit)\n"
      "  -fr -bms -vote   one-point decoders to run (default: all)\n"
      "  -frvote          pure Feng-Rao majority voting (Newton path; no BMS, "
      "no dual basis)\n"
      "  -forney          use multivariate AG Forney-function evaluation for "
      "FR\n"
      "  -kotter          use Kötter one-point update + generalized Forney "
      "formula\n"
      "  -show-values     print injected and decoded error values\n"
      "  -strict          skip FR/BMS when t exceeds the basic bound tau "
      "(default: run them anyway)\n"
      "  -limits          print the parameter limits of this build/curve and "
      "exit\n"
      "  -basic           (multi-point) basic algorithm\n"
      "  -nonewton        disabled: this build requires Newton-polygon bases\n"
      "  --place k        also avoids probing every candidate place (saves "
      "setup time)\n"
      "  -n N             N random trials (summary only)       -v  votes     "
      "-list  only list places");
}

/* ================= Suzuki curve: dedicated one-point engine =================
 *   y^q + y = x^q0 (x^q + x),   q = 2^(2n+1),  q0 = 2^n,   genus g = q0 (q-1)
 * The Weierstrass semigroup at the single place at infinity is
 * <q, q+q0, q+2q0, q+2q0+1>; the plane monomials x^i y^j do not realise it, so
 * L(M P_inf) is spanned by the monomials x^a y^b z^c w^d with
 *   z = x^(2q0+1) + y^(2q0),   w = x y^(2q0) + z^(2q0)
 * of pole orders q, q+q0, q+2q0, q+2q0+1 (one monomial per semigroup element).
 * Decoding is the Feng-Rao basic algorithm on the semigroup syndrome matrix
 * S[i][j] = s(phi_i phi_j) (only function values at the points are needed),
 * followed by the univariate polynomial g(theta) = det(theta I + S0^-1 SX) whose
 * roots are the x-coordinates of the errors, and a linear solve for the values.
 * Guaranteed: t <= (M - 3g + 1) / 2.  Independent of the plane-curve machinery
 * of the rest of this file (own working arrays; uses only the field above). */
static int sz_q, sz_q0, sz_g, sz_M, sz_tau, sz_ldeg, sz_rowmax;
static int sz_np;
static fe *sz_px, *sz_py;
static int *sz_first, *sz_count;
static int sz_nb;
static int *sz_rho, *sz_cnt;
static fe **sz_val;

static void sz_free_all(void) {
  free(sz_px);
  free(sz_py);
  free(sz_first);
  free(sz_count);
  free(sz_rho);
  free(sz_cnt);
  if (sz_val)
    for (int i = 0; i < sz_nb; ++i)
      free(sz_val[i]);
  free(sz_val);
  sz_px = sz_py = NULL;
  sz_first = sz_count = sz_rho = sz_cnt = NULL;
  sz_val = NULL;
  sz_nb = 0;
}
static int sz_count_upto(int rho) {
  if (rho < 0)
    return 0;
  if (rho > sz_M)
    rho = sz_M;
  return sz_cnt[rho];
}
static int sz_enumerate(void) {
  const int q = sz_q, q0 = sz_q0;
  fe *fib = malloc((size_t)FS * (size_t)q * sizeof(fe));
  int *fc = calloc((size_t)FS, sizeof(int));
  sz_first = malloc((size_t)FS * sizeof(int));
  sz_count = malloc((size_t)FS * sizeof(int));
  if (!fib || !fc || !sz_first || !sz_count) {
    free(fib);
    free(fc);
    return -1;
  }
  for (int y = 0; y < FS; ++y) {
    int v = gpow((fe)y, q) ^ y;
    if (fc[v] >= q) {
      free(fib);
      free(fc);
      return -1;
    }
    fib[(size_t)v * q + fc[v]++] = (fe)y;
  }
  size_t total = 0;
  for (int x = 0; x < FS; ++x) {
    int rhs = mul(gpow((fe)x, q0), (fe)(gpow((fe)x, q) ^ x));
    total += (size_t)fc[rhs];
  }
  sz_px = malloc((total + 1) * sizeof(fe));
  sz_py = malloc((total + 1) * sizeof(fe));
  if (!sz_px || !sz_py) {
    free(fib);
    free(fc);
    return -1;
  }
  size_t np = 0;
  for (int x = 0; x < FS; ++x) {
    int rhs = mul(gpow((fe)x, q0), (fe)(gpow((fe)x, q) ^ x));
    sz_first[x] = (int)np;
    sz_count[x] = fc[rhs];
    for (int j = 0; j < fc[rhs]; ++j) {
      sz_px[np] = (fe)x;
      sz_py[np] = fib[(size_t)rhs * q + j];
      ++np;
    }
  }
  sz_np = (int)np;
  free(fib);
  free(fc);
  return 0;
}
static int sz_build_basis(void) {
  const int q = sz_q, q0 = sz_q0, M = sz_M;
  const int wy = q + q0, wz = q + 2 * q0, ww = q + 2 * q0 + 1;
  sz_rho = malloc((size_t)(M + 1) * sizeof(int));
  sz_cnt = malloc((size_t)(M + 1) * sizeof(int));
  int *ea = malloc((size_t)(M + 1) * sizeof(int)), *eb = malloc((size_t)(M + 1) * sizeof(int)),
      *ec = malloc((size_t)(M + 1) * sizeof(int)), *ed = malloc((size_t)(M + 1) * sizeof(int));
  if (!sz_rho || !sz_cnt || !ea || !eb || !ec || !ed) {
    free(ea);
    free(eb);
    free(ec);
    free(ed);
    return -1;
  }
  int nb = 0;
  for (int s = 0; s <= M; ++s) {
    int found = 0, fa = 0, fb = 0, fc2 = 0, fd = 0;
    for (int d = 0; ww * d <= s && !found; ++d)
      for (int c = 0; ww * d + wz * c <= s && !found; ++c)
        for (int b = 0; ww * d + wz * c + wy * b <= s && !found; ++b) {
          int r = s - ww * d - wz * c - wy * b;
          if (r % q == 0) {
            found = 1;
            fa = r / q;
            fb = b;
            fc2 = c;
            fd = d;
          }
        }
    if (found) {
      sz_rho[nb] = s;
      ea[nb] = fa;
      eb[nb] = fb;
      ec[nb] = fc2;
      ed[nb] = fd;
      ++nb;
    }
    sz_cnt[s] = nb;
  }
  sz_nb = 0;
  sz_val = calloc((size_t)nb + 1, sizeof(fe *));
  if (!sz_val) {
    free(ea);
    free(eb);
    free(ec);
    free(ed);
    return -1;
  }
  sz_nb = nb;
  for (int i = 0; i < nb; ++i) {
    sz_val[i] = malloc((size_t)sz_np * sizeof(fe));
    if (!sz_val[i]) {
      free(ea);
      free(eb);
      free(ec);
      free(ed);
      return -1;
    }
  }
  for (int k = 0; k < sz_np; ++k) {
    fe x = sz_px[k], y = sz_py[k];
    fe y2 = gpow(y, 2 * q0);
    fe z = (fe)(gpow(x, 2 * q0 + 1) ^ y2);
    fe w = (fe)(mul(x, y2) ^ gpow(z, 2 * q0));
    for (int i = 0; i < nb; ++i)
      sz_val[i][k] = mul(mul(gpow(x, ea[i]), gpow(y, eb[i])),
                         mul(gpow(z, ec[i]), gpow(w, ed[i])));
  }
  free(ea);
  free(eb);
  free(ec);
  free(ed);
  return 0;
}
/* flat n x n matrices, stride n */
static int sz_mat_inverse(const fe *m, fe *out, int n) {
  fe *wk = malloc((size_t)n * n * sizeof(fe));
  if (!wk)
    return 0;
  memcpy(wk, m, (size_t)n * n * sizeof(fe));
  for (int i = 0; i < n; ++i) {
    for (int j = 0; j < n; ++j)
      out[(size_t)i * n + j] = 0;
    out[(size_t)i * n + i] = 1;
  }
  for (int c = 0; c < n; ++c) {
    int p = -1;
    for (int r = c; r < n; ++r)
      if (wk[(size_t)r * n + c]) {
        p = r;
        break;
      }
    if (p < 0) {
      free(wk);
      return 0;
    }
    if (p != c)
      for (int i = 0; i < n; ++i) {
        fe t = wk[(size_t)p * n + i];
        wk[(size_t)p * n + i] = wk[(size_t)c * n + i];
        wk[(size_t)c * n + i] = t;
        t = out[(size_t)p * n + i];
        out[(size_t)p * n + i] = out[(size_t)c * n + i];
        out[(size_t)c * n + i] = t;
      }
    fe iv = inv(wk[(size_t)c * n + c]);
    for (int i = 0; i < n; ++i) {
      wk[(size_t)c * n + i] = mul(wk[(size_t)c * n + i], iv);
      out[(size_t)c * n + i] = mul(out[(size_t)c * n + i], iv);
    }
    for (int r = 0; r < n; ++r) {
      fe f = wk[(size_t)r * n + c];
      if (r == c || !f)
        continue;
      for (int i = 0; i < n; ++i) {
        wk[(size_t)r * n + i] ^= mul(f, wk[(size_t)c * n + i]);
        out[(size_t)r * n + i] ^= mul(f, out[(size_t)c * n + i]);
      }
    }
  }
  free(wk);
  return 1;
}
/* characteristic polynomial det(theta I + H); H (n x n) is destroyed */
static int sz_charpoly(fe *H, int n, fe *g) {
  for (int k = 0; k + 2 < n; ++k) {
    int p = -1;
    for (int i = k + 1; i < n; ++i)
      if (H[(size_t)i * n + k]) {
        p = i;
        break;
      }
    if (p < 0)
      continue;
    if (p != k + 1) {
      for (int j = 0; j < n; ++j) {
        fe t = H[(size_t)p * n + j];
        H[(size_t)p * n + j] = H[(size_t)(k + 1) * n + j];
        H[(size_t)(k + 1) * n + j] = t;
      }
      for (int i = 0; i < n; ++i) {
        fe t = H[(size_t)i * n + p];
        H[(size_t)i * n + p] = H[(size_t)i * n + k + 1];
        H[(size_t)i * n + k + 1] = t;
      }
    }
    fe iv = inv(H[(size_t)(k + 1) * n + k]);
    for (int i = k + 2; i < n; ++i) {
      if (!H[(size_t)i * n + k])
        continue;
      fe f = mul(H[(size_t)i * n + k], iv);
      for (int j = 0; j < n; ++j)
        H[(size_t)i * n + j] ^= mul(f, H[(size_t)(k + 1) * n + j]);
      for (int r = 0; r < n; ++r)
        H[(size_t)r * n + k + 1] ^= mul(f, H[(size_t)r * n + i]);
    }
  }
  fe **pol = calloc((size_t)n + 1, sizeof(fe *));
  if (!pol)
    return 0;
  for (int k = 0; k <= n; ++k) {
    pol[k] = calloc((size_t)k + 1, sizeof(fe));
    if (!pol[k]) {
      for (int j = 0; j < k; ++j)
        free(pol[j]);
      free(pol);
      return 0;
    }
  }
  pol[0][0] = 1;
  for (int k = 1; k <= n; ++k) {
    fe prod = 1;
    for (int d = 0; d < k; ++d) {
      pol[k][d + 1] ^= pol[k - 1][d];
      pol[k][d] ^= mul(H[(size_t)(k - 1) * n + k - 1], pol[k - 1][d]);
    }
    for (int i = 1; i <= k - 1; ++i) {
      prod = mul(prod, H[(size_t)(k - i) * n + k - i - 1]);
      if (!prod)
        break;
      fe c = mul(H[(size_t)(k - i - 1) * n + k - 1], prod);
      if (!c)
        continue;
      for (int d = 0; d <= k - i - 1; ++d)
        pol[k][d] ^= mul(c, pol[k - i - 1][d]);
    }
  }
  for (int d = 0; d <= n; ++d)
    g[d] = pol[n][d];
  for (int k = 0; k <= n; ++k)
    free(pol[k]);
  free(pol);
  return 1;
}
/* decode one received word r (length sz_np); returns 1 when every injected
 * error was recovered with its value (true_pos / r are the simulated truth) */
static int sz_decode(const fe *r, const int *true_pos, int nerr, int verbose,
                     int list_values, int *nfound_out) {
  const int np = sz_np, nb = sz_nb, M = sz_M, q = sz_q;
  int ok = 0;
  int *nz = malloc((size_t)np * sizeof(int));
  int nzc = 0;
  for (int k = 0; k < np; ++k)
    if (r[k])
      nz[nzc++] = k;
  int nrows = sz_count_upto(sz_rowmax);
  int nl = sz_count_upto(sz_ldeg);
  if (nl > nrows)
    nl = nrows;
  fe **red = calloc((size_t)nrows + 1, sizeof(fe *));
  fe **coef = calloc((size_t)nrows + 1, sizeof(fe *));
  int *piv = malloc(((size_t)nrows + 1) * sizeof(int));
  int *rowc = malloc(((size_t)nb + 1) * sizeof(int));
  fe *pivinv = malloc(((size_t)nrows + 1) * sizeof(fe));
  fe *u = malloc(((size_t)nzc + 1) * sizeof(fe));
  const int maxt = sz_tau + 2;
  int *R = malloc((size_t)(maxt + 1) * sizeof(int)),
      *C = malloc((size_t)(maxt + 1) * sizeof(int));
  fe *xv = calloc((size_t)np, sizeof(fe));
  int *found = malloc((size_t)(maxt + 1) * sizeof(int));
  fe *errv = malloc((size_t)(maxt + 1) * sizeof(fe));
  fe *S0 = NULL, *SX = NULL, *S0i = NULL, *Q = NULL, *gp = NULL, *aug = NULL;
  int *roots = NULL;
  int nfound = 0, overflow = 0, resolved = 0, tt = 0;
  if (!nz || !red || !coef || !piv || !rowc || !pivinv || !u || !R || !C ||
      !xv || !found || !errv)
    goto done;
  for (int j = 0; j < nb; ++j)
    rowc[j] = -1;
  for (int i = 0; i < nrows; ++i) {
    int ncol = sz_count_upto(M - sz_rho[i]);
    red[i] = malloc((size_t)(ncol + 1) * sizeof(fe));
    coef[i] = calloc((size_t)i + 1, sizeof(fe));
    if (!red[i] || !coef[i])
      goto done;
    for (int n = 0; n < nzc; ++n)
      u[n] = mul(r[nz[n]], sz_val[i][nz[n]]);
    for (int j = 0; j < ncol; ++j) {
      fe acc = 0;
      for (int n = 0; n < nzc; ++n)
        acc ^= mul(u[n], sz_val[j][nz[n]]);
      red[i][j] = acc;
    }
    coef[i][i] = 1;
    piv[i] = -1;
    for (int j = 0; j < ncol; ++j) {
      fe v = red[i][j];
      if (!v)
        continue;
      int p = rowc[j];
      if (p >= 0) {
        fe f = mul(v, pivinv[p]);
        for (int jj = j; jj < ncol; ++jj)
          red[i][jj] ^= mul(f, red[p][jj]);
        for (int k = 0; k <= p; ++k)
          coef[i][k] ^= mul(f, coef[p][k]);
      } else {
        piv[i] = j;
        rowc[j] = i;
        pivinv[i] = inv(v);
        break;
      }
    }
  }
  int nloc = 0;
  for (int i = 0; i < nl; ++i)
    if (piv[i] < 0)
      ++nloc;
  for (int i = 0; i < nrows; ++i)
    if (piv[i] >= 0) {
      if (tt >= maxt) {
        if (verbose)
          puts("# SUZUKI: too many pivots (more errors than the designed "
               "bound)");
        goto done;
      }
      R[tt] = i;
      C[tt] = piv[i];
      ++tt;
    }
  if (verbose) {
    printf("# SUZUKI: %d error locators with rho <= %d\n", nloc, sz_ldeg);
    printf("# SUZUKI: staircase of %d elements -> estimated number of errors "
           "t = %d\n",
           tt, tt);
  }
  if (tt == 0) {
    if (verbose)
      puts("# SUZUKI: no errors.");
    ok = (nerr == 0);
    goto done;
  }
  for (int a = 0; a < tt; ++a)
    for (int b = 0; b < tt; ++b)
      if (sz_rho[R[a]] + sz_rho[C[b]] + q > M) {
        if (verbose)
          puts("# SUZUKI: syndromes too short to form the shifted matrix.");
        goto done;
      }
  for (int n = 0; n < nzc; ++n)
    xv[nz[n]] = sz_px[nz[n]];
  S0 = malloc((size_t)tt * tt * sizeof(fe));
  SX = malloc((size_t)tt * tt * sizeof(fe));
  S0i = malloc((size_t)tt * tt * sizeof(fe));
  Q = malloc((size_t)tt * tt * sizeof(fe));
  gp = malloc(((size_t)tt + 1) * sizeof(fe));
  if (!S0 || !SX || !S0i || !Q || !gp)
    goto done;
  for (int a = 0; a < tt; ++a) {
    for (int n = 0; n < nzc; ++n)
      u[n] = mul(r[nz[n]], sz_val[R[a]][nz[n]]);
    for (int b = 0; b < tt; ++b) {
      fe a0 = 0, ax = 0;
      for (int n = 0; n < nzc; ++n) {
        fe t = mul(u[n], sz_val[C[b]][nz[n]]);
        a0 ^= t;
        ax ^= mul(t, xv[nz[n]]);
      }
      S0[(size_t)a * tt + b] = a0;
      SX[(size_t)a * tt + b] = ax;
    }
  }
  if (!sz_mat_inverse(S0, S0i, tt)) {
    if (verbose)
      puts("# SUZUKI: S0 is singular (rank deficient).");
    goto done;
  }
  for (int a = 0; a < tt; ++a)
    for (int b = 0; b < tt; ++b) {
      fe acc = 0;
      for (int k = 0; k < tt; ++k)
        acc ^= mul(S0i[(size_t)a * tt + k], SX[(size_t)k * tt + b]);
      Q[(size_t)a * tt + b] = acc;
    }
  if (!sz_charpoly(Q, tt, gp))
    goto done;
  roots = malloc((size_t)FS * sizeof(int));
  if (!roots)
    goto done;
  int nroots = 0;
  for (int th = 0; th < FS; ++th) {
    fe acc = gp[tt];
    for (int i = tt - 1; i >= 0; --i)
      acc = (fe)(mul(acc, (fe)th) ^ gp[i]);
    if (!acc)
      roots[nroots++] = th;
  }
  if (verbose)
    printf("# SUZUKI: g(theta) of degree %d has %d distinct roots in GF(2^%d)\n",
           tt, nroots, FM);
  for (int m = 0; m < nroots; ++m) {
    int xr = roots[m];
    for (int j = 0; j < sz_count[xr]; ++j) {
      int idx = sz_first[xr] + j, vanish = 1;
      for (int i = 0; i < nl && vanish; ++i) {
        if (piv[i] >= 0)
          continue;
        fe acc = 0;
        for (int k = 0; k <= i; ++k)
          if (coef[i][k])
            acc ^= mul(coef[i][k], sz_val[k][idx]);
        if (acc)
          vanish = 0;
      }
      if (vanish) {
        if (nfound < maxt)
          found[nfound++] = idx;
        else
          overflow = 1;
      }
    }
  }
  if (!overflow && nfound > 0) {
    if (nfound > tt && verbose)
      printf("# SUZUKI: %d common zeros > t = %d: resolving by error values\n",
             nfound, tt);
    int n = nfound, mrows = nb;
    aug = malloc((size_t)mrows * ((size_t)n + 1) * sizeof(fe));
    if (aug) {
      const size_t st = (size_t)n + 1;
      for (int a = 0; a < mrows; ++a) {
        for (int k = 0; k < n; ++k)
          aug[(size_t)a * st + k] = sz_val[a][found[k]];
        fe s = 0;
        for (int i2 = 0; i2 < nzc; ++i2)
          s ^= mul(r[nz[i2]], sz_val[a][nz[i2]]);
        aug[(size_t)a * st + n] = s;
      }
      int good = 1;
      for (int c = 0; c < n && good; ++c) {
        int p = -1;
        for (int a = c; a < mrows; ++a)
          if (aug[(size_t)a * st + c]) {
            p = a;
            break;
          }
        if (p < 0) {
          good = 0;
          break;
        }
        if (p != c)
          for (int k = 0; k <= n; ++k) {
            fe t = aug[(size_t)p * st + k];
            aug[(size_t)p * st + k] = aug[(size_t)c * st + k];
            aug[(size_t)c * st + k] = t;
          }
        fe iv = inv(aug[(size_t)c * st + c]);
        for (int k = c; k <= n; ++k)
          aug[(size_t)c * st + k] = mul(aug[(size_t)c * st + k], iv);
        for (int a = 0; a < mrows; ++a) {
          fe f = aug[(size_t)a * st + c];
          if (a == c || !f)
            continue;
          for (int k = c; k <= n; ++k)
            aug[(size_t)a * st + k] ^= mul(f, aug[(size_t)c * st + k]);
        }
      }
      if (good)
        for (int a = n; a < mrows; ++a)
          if (aug[(size_t)a * st + n]) {
            good = 0;
            break;
          }
      if (good) {
        int keep = 0;
        for (int k = 0; k < n; ++k)
          if (aug[(size_t)k * st + n]) {
            found[keep] = found[k];
            errv[keep] = aug[(size_t)k * st + n];
            ++keep;
          }
        nfound = keep;
        resolved = 1;
      }
    }
    if (!resolved && verbose)
      puts("# SUZUKI: could not compute the error values.");
  }
  if (nfound_out)
    *nfound_out = nfound;
  {
    int same = 0;
    for (int m = 0; m < nfound && resolved; ++m)
      if (r[found[m]] && errv[m] == r[found[m]])
        ++same;
    ok = resolved && !overflow && nfound == nerr && same == nerr;
    if (verbose) {
      if (list_values)
        for (int m = 0; m < nfound; ++m)
          printf("#   decoded error %d: position %d (x=%u,y=%u)  value=%u\n",
                 m + 1, found[m], sz_px[found[m]], sz_py[found[m]],
                 resolved ? errv[m] : 0);
      printf("# SUZUKI %d of %d errors recovered with the correct value, %d "
             "reported -> %s\n",
             same, nerr, nfound, ok ? "OK" : "MISMATCH");
    }
  }
done:
  if (red)
    for (int i = 0; i < nrows; ++i)
      free(red[i]);
  if (coef)
    for (int i = 0; i < nrows; ++i)
      free(coef[i]);
  free(red);
  free(coef);
  free(piv);
  free(rowc);
  free(pivinv);
  free(u);
  free(R);
  free(C);
  free(xv);
  free(found);
  free(errv);
  free(S0);
  free(SX);
  free(S0i);
  free(Q);
  free(gp);
  free(aug);
  free(roots);
  free(nz);
  (void)true_pos;
  return ok;
}
static int suzuki_run(int q_req, int nerr, int Mreq, int trials, int verbose,
                      int fixed_val, int list_values, int only_list) {
  int q = q_req > 0 ? q_req : 8, ex = 0;
  while ((1 << ex) < q)
    ++ex;
  if ((1 << ex) != q || (ex % 2) == 0 || ex > 9) {
    fprintf(stderr,
            "--curve suzuki needs --q = 2^(2n+1) (2, 8, 32, 128, 512); got %d\n",
            q);
    return 1;
  }
  sz_q = q;
  sz_q0 = 1 << ((ex - 1) / 2);
  sz_g = sz_q0 * (q - 1);
  if (nerr < 0 || trials < 1) {
    fprintf(stderr, "invalid --errors or -n\n");
    return 1;
  }
  sz_M = Mreq > 0 ? Mreq : 2 * nerr + 3 * sz_g - 1;
  if (sz_M < 3 * sz_g + 1)
    sz_M = 3 * sz_g + 1;
  sz_tau = (sz_M - 3 * sz_g + 1) / 2;
  sz_ldeg = sz_tau + sz_g;
  sz_rowmax = sz_M - q;
  printf("# Suzuki curve: y^%d + y = x^%d (x^%d + x)  over GF(2^%d)  "
         "(q=%d, q0=%d, genus g=%d)\n",
         q, sz_q0, q, FM, q, sz_q0, sz_g);
  if (sz_enumerate() != 0) {
    fprintf(stderr, "Suzuki point enumeration failed\n");
    sz_free_all();
    return 1;
  }
  printf("# %d affine rational points (+1 at infinity); semigroup <%d,%d,%d,%d>\n",
         sz_np, q, q + sz_q0, q + 2 * sz_q0, q + 2 * sz_q0 + 1);
  printf("# one-point code: M = %d, g = %d, designed t <= %d, locators in "
         "L(%d P_inf)\n",
         sz_M, sz_g, sz_tau, sz_ldeg);
  if (only_list) {
    sz_free_all();
    return 0;
  }
  if (nerr > sz_tau) {
    fprintf(stderr,
            "# %d errors exceed the designed bound t <= %d for M = %d; raise "
            "--M (need M >= %d) or lower --errors\n",
            nerr, sz_tau, sz_M, 2 * nerr + 3 * sz_g - 1);
    sz_free_all();
    return 1;
  }
  if (sz_np <= sz_M + sz_g) {
    fprintf(stderr,
            "# the curve has only n = %d rational points, but M + g = %d >= "
            "n: use a larger field (--m) or smaller M/errors\n",
            sz_np, sz_M + sz_g);
    sz_free_all();
    return 1;
  }
  if (nerr > sz_np || sz_build_basis() != 0) {
    fprintf(stderr, "Suzuki basis setup failed\n");
    sz_free_all();
    return 1;
  }
  printf("# basis: %d monomials x^a y^b z^c w^d, one per semigroup element "
         "<= M\n",
         sz_nb);
  fe *r = malloc((size_t)sz_np * sizeof(fe));
  int *tp = malloc(((size_t)nerr + 1) * sizeof(int));
  unsigned char *used = malloc((size_t)sz_np);
  int good = 0;
  for (int tr = 1; tr <= trials; ++tr) {
    memset(r, 0, (size_t)sz_np * sizeof(fe));
    memset(used, 0, (size_t)sz_np);
    for (int e = 0; e < nerr; ++e) {
      int p;
      do
        p = (int)(rnd() % (uint64_t)sz_np);
      while (used[p]);
      used[p] = 1;
      tp[e] = p;
      r[p] = fixed_val > 0 ? (fe)fixed_val : (fe)(1 + rnd() % (uint64_t)(FS - 1));
    }
    int vb = (trials == 1) || verbose;
    if (vb && trials > 1)
      printf("# trial %d\n", tr);
    if (vb)
      printf("# %d errors injected\n", nerr);
    int ok = sz_decode(r, tp, nerr, vb, list_values, NULL);
    if (ok)
      ++good;
    if (!vb)
      printf("# trial %d: SUZUKI %s\n", tr, ok ? "ok" : "FAIL");
  }
  if (trials > 1)
    printf("# summary of %d trials with %d errors: SUZUKI %d/%d\n", trials,
           nerr, good, trials);
  free(r);
  free(tp);
  free(used);
  sz_free_all();
  return good == trials ? 0 : 3;
}

int ag_frvote_run(int argc, char **argv) {
  const char *terms = "16,0;0,1;15,4;12,16", *polespec = NULL;
  const char *curve_name = "bbgs";
  int len_req = -1, half = 0, q_req = -1, terms_set = 0, m_bits = 6, Mreq = -1,
      bbgs_a = 1, bbgs_b = 2, place_req = -1, trials = 1, verbose = 0,
      show_values = 0, only_list = 0, Jstep = 16, Jmax = 700;
  unsigned poly = 0, seed = 1;
  int run_fr = 1, run_bms = 1, run_vote = 1, run_frvote = 0, only = 0,
      nerr = 256, force = 1, fixed_value_req = 0, run_common_binary = 0;
  for (int i = 1; i < argc; ++i) {
    { /* accept --force / --fr / --bms / --vote / --basic / --list as well as
         -force ... */
      static const char *flags[] = {"half",   "force",    "fr",     "bms",
                                    "vote",   "frvote",   "basic",  "list",
                                    "v",      "nonewton", "strict", "limits",
                                    "nopoly", "forney",   "kotter", NULL};
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
    } else if (!strcmp(argv[i], "--a") && i + 1 < argc)
      bbgs_a = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--b") && i + 1 < argc)
      bbgs_b = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--errors") && i + 1 < argc)
      nerr = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--fixed-error-value") && i + 1 < argc)
      fixed_value_req = (int)strtol(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "-common-binary"))
      run_common_binary = 1;
    else if (!strcmp(argv[i], "-bms2-check"))
      bms2_check_enabled = 1;
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
    else if (!strcmp(argv[i], "-show-values")) {
      show_values = 1;
      show_locator_equations = 1;
    } else if (!strcmp(argv[i], "-list"))
      only_list = 1;
    else if (!strcmp(argv[i], "-force"))
      force = 1;
    else if (!strcmp(argv[i], "-strict"))
      force = 0;
    else if (!strcmp(argv[i], "-nopoly"))
      use_poly_opt = 0;
    else if (!strcmp(argv[i], "-forney"))
      use_forney_values = 1;
    else if (!strcmp(argv[i], "-kotter"))
      use_kotter_values = 1;
    else if (!strcmp(argv[i], "-limits"))
      only_list = 1;
    else if (!strcmp(argv[i], "-nonewton")) {
      fprintf(stderr, "-nonewton is disabled: this build uses Newton-polygon "
                      "bases only.\n");
      return 2;
    } else if (!strcmp(argv[i], "-half"))
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
  if (run_frvote && run_fr) {
    fprintf(stderr, "-frvote cannot be combined with -fr: FR-VOTE keeps no "
                    "basis-value table and only the minimal locator rows.\n");
    return 1;
  }
  compact_fr_mode = run_frvote;
  if (api_mode &&
      (polespec != NULL || !run_frvote || run_fr || run_bms || run_vote)) {
    fprintf(stderr, "API mode supports only one-point Newton FR-VOTE; use "
                    "-frvote alone and do not set --pole.\n");
    return 1;
  }
  if (m_bits < 1 || m_bits > 12) {
    fprintf(stderr, "--m must be in 1..12 in this build\n");
    return 1;
  }
  if (!poly) {
    static const unsigned dp[13] = {0,     3,     7,     0xB,   0x13,
                                    0x25,  0x43,  0x89,  0x11D, 0x211,
                                    0x409, 0x805, 0x1053};
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
  if (!terms_set && !strcmp(curve_name, "suzuki")) {
    if (api_mode) {
      fprintf(stderr, "--curve suzuki is not available in API mode\n");
      return 1;
    }
    return suzuki_run(q_req, nerr, Mreq, trials, verbose, fixed_value_req,
                      show_values, only_list);
  }

  /* ---- curve family ----
   * F(X,Y)=0 is stored as a sparse polynomial.  Both built-in families are
   * handled by the same point enumerator, Newton-polygon code and FR-VOTE.
   */
  static char tbuf[4096];
  int qfam = 0;
  if (!terms_set) {
    int q = q_req;
    if (!strcmp(curve_name, "bbgs")) {
      int a = bbgs_a, b = bbgs_b, c = a + b;
      if (a < 1 || b < 1 || gcdi(a, b) != 1 || c > 10) {
        /* EXTENSION_POINT: c<=10 is a structural guard; revisit together
         * with qpow[] sizing and curve/point-count complexity. */
        fprintf(stderr,
                "BBGS requires positive coprime --a and --b, with a+b <= 10\n");
        return 1;
      }
      if (q < 0) {
        if (m_bits % c != 0) {
          fprintf(stderr, "For --a %d --b %d, --m must be divisible by c=%d\n",
                  a, b, c);
          return 1;
        }
        int r = m_bits / c;
        if (r < 1 || r > 10)
          return 1;
        q = 1 << r;
      }
      if (q < 2 || (q & (q - 1))) {
        fprintf(stderr, "--q must be a power of 2 (>= 2)\n");
        return 1;
      }
      /* EXTENSION_POINT: fixed exponent table; current m<=12 makes every
       * accepted q^c <= 512, but retain a checked bound for future growth. */
      int qpow[16];
      qpow[0] = 1;
      for (int k = 1; k <= c; ++k) {
        if (qpow[k - 1] > 8192 / q) { /* EXTENSION_POINT: exponent ceiling */
          fprintf(stderr, "BBGS exponents exceed this build's limits\n");
          return 1;
        }
        qpow[k] = qpow[k - 1] * q;
      }
      if (qpow[c] != FS) {
        int r = 0, qq = q;
        while (qq > 1) {
          ++r;
          qq >>= 1;
        }
        fprintf(stderr,
                "BBGS field mismatch: need --m %d for GF(q^c)=GF(2^%d), got "
                "--m %d\n",
                r * c, r * c, m_bits);
        return 1;
      }
      int used = snprintf(tbuf, sizeof tbuf, "%d,0", qpow[c - 1]);
      for (int k = 0; k < b; ++k)
        used += snprintf(tbuf + used, sizeof tbuf - (size_t)used, ";%d,%d",
                         qpow[c - 1] - qpow[k], qpow[a + k]);
      for (int k = 0; k < a; ++k)
        used += snprintf(tbuf + used, sizeof tbuf - (size_t)used, ";%d,%d",
                         qpow[c - 1] - qpow[b + k], qpow[k]);
      if (used < 0 || (size_t)used >= sizeof tbuf) {
        fprintf(stderr, "BBGS term list exceeds buffer\n");
        return 1;
      }
      terms = tbuf;
      if (a == 1 && b == 2)
        qfam = q;
      printf("# BBGS curve (a=%d,b=%d,c=%d,q=%d), %d terms:\n#   X^%d", a, b, c,
             q, c + 1, qpow[c - 1]);
      for (int k = 0; k < b; ++k)
        printf(" + X^%d Y^%d", qpow[c - 1] - qpow[k], qpow[a + k]);
      for (int k = 0; k < a; ++k)
        printf(" + X^%d Y^%d", qpow[c - 1] - qpow[b + k], qpow[k]);
      puts(" = 0");
    } else if (!strcmp(curve_name, "hermitian")) {
      if (q < 0)
        q = (m_bits % 3 == 0) ? (1 << (m_bits / 3)) : 4;
      if (q < 2 || (q & (q - 1))) {
        fprintf(stderr, "--q must be a power of 2 (>= 2)\n");
        return 1;
      }
      snprintf(tbuf, sizeof tbuf, "0,%d;%d,0;0,1", q, q + 1);
      terms = tbuf;
      hermitian_q = q;
      printf("# Hermitian curve: Y^%d + Y + X^%d = 0 (q=%d)\n", q, q + 1, q);
    } else {
      fprintf(stderr, "--curve must be bbgs, hermitian or suzuki (or use --terms)\n");
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
  /* --terms that spell the Hermitian curve X^(q+1) + Y^q + Y (all coefficients
   * 1) get the same dedicated polynomial-semigroup path as --curve hermitian */
  if (hermitian_q == 0 && T == 3) {
    int q = 0, hx = 0, hy = 0, h1 = 0, ok = 1;
    for (int t = 0; t < T; ++t)
      if (TC[t] != 1)
        ok = 0;
    for (int t = 0; t < T && ok; ++t) {
      if (TY[t] == 0 && TX[t] > 1) {
        hx++;
        q = TX[t] - 1;
      } else if (TX[t] == 0 && TY[t] == 1)
        h1++;
      else if (TX[t] == 0 && TY[t] > 1)
        hy++;
    }
    if (ok && hx == 1 && h1 == 1 && hy == 1 && q >= 2 && !(q & (q - 1))) {
      int ycnt = 0;
      for (int t = 0; t < T; ++t)
        if (TX[t] == 0 && TY[t] == q)
          ycnt++;
      if (ycnt == 1) {
        hermitian_q = q;
        printf("# --terms recognised as the Hermitian curve (q=%d)\n", q);
      }
    }
  }
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
  if (fixed_value_req < 0 || fixed_value_req >= FS) {
    fprintf(stderr, "--fixed-error-value must be in 1..%d (or omit it)\n",
            FS - 1);
    return 1;
  }
  fixed_error_value = fixed_value_req;
  if (run_common_binary) {
    run_fr = run_bms = run_vote = run_frvote = 0;
  }
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
  if (nerr > TAU_V && !run_common_binary) {
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

  /* Candidate poles are accepted only when the Newton polygon certifies the
   * complete one-point basis.  No Laurent-series fallback is performed. */
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
  for (int pass = 0; pass < 1; ++pass) {
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
        /* Laurent-series basis construction is intentionally disabled. */
        continue;
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
             dfr, (dfr - 1) / 2, "Newton polygon", now() - t0);
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
  /* free the Newton bases of the candidates that were not chosen */
  for (int ci = 0; ci < ncand; ++ci) {
    int id = cand[ci];
    if (id != best && via_newton[id]) {
      free(NB[id].rho);
      free(NB[id].ei);
      free(NB[id].ej);
      memset(&NB[id], 0, sizeof NB[id]);
      via_newton[id] = 0;
    }
  }
  if (best >= MAXORB)
    printf("# chosen pole: place of edge E%d  (d_FR = %d, designed t = %d)\n",
           best - MAXORB, bestdfr, (bestdfr - 1) / 2);
  else
    printf("# chosen pole: place #%d  (d_FR = %d, designed t = %d)\n", best,
           bestdfr, (bestdfr - 1) / 2);
  if (via_newton[best] && use_poly_opt) {
    int e = best >= MAXORB ? best - MAXORB : pl[best].edge;
    if (poly_setup(e, M_EXT + (use_kotter_values ? 128 : 0), &NB[best]) == 0) {
      use_poly = 1;
      if (use_kotter_values) {
        kotter_ready = kotter_prepare_module(e, &NB[best]);
        if (!kotter_ready) {
          fprintf(stderr, "Kötter path unsupported for this curve/place or "
                          "module setup failed.\n");
          return 2;
        }
      }
      bas_ei = NB[best].ei; /* poly_setup の後 */
      bas_ej = NB[best].ej;
      if (hermitian_q > 0)
        printf("# Hermitian monomial syndrome tables on %d polynomial "
               "semigroup points (no dual basis)\n",
               NPT);
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
          fprintf(stderr,
                  "API allocation failed while puncturing Laurent positions\n");
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
        fprintf(stderr, "# only n = %d positions left, but M + g = %d >= n.\n",
                npts, M_EXT);
        return 1;
      }
    }
    nbasis = B->n;
    if (run_frvote) {
      /* FR-VOTE's Newton syndrome path only needs monomial exponents and
       * point coordinates.  Do not allocate nbasis*npts field elements;
       * selected error positions are evaluated on demand. */
      for (int i = 0; i < B->n; ++i) {
        basis[i].rho = B->rho[i];
        basis[i].val = NULL;
      }
    } else {
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
        /* V is already a contiguous dim x npts evaluation matrix.  Point
         * directly into its rows instead of allocating/copying every row.
         * This also fixes the former leak of V and halves this phase's peak
         * evaluation-storage requirement. */
        basis[i].val = V + (size_t)ord[i] * (size_t)npts;
      }
      free(ord);
    }
  }
  init_semigroup();
  ASHIFT = basis[1].rho;
  ROW_MAX = M_SYND - ASHIFT;
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
        fprintf(stderr, "API mode requires -frvote alone (do not enable "
                        "-fr/-bms/-vote).\n");
        return 1;
      }
      if (api_received_len != (size_t)npts) {
        fprintf(stderr, "API received length mismatch: got %zu, expected %d\n",
                api_received_len, npts);
        return 1;
      }
      for (int k = 0; k < npts; ++k) {
        if (api_received[k] >= FS) {
          fprintf(stderr, "API received[%d]=%u is outside GF(2^%d)\n", k,
                  (unsigned)api_received[k], FM);
          return 1;
        }
      }
      memcpy(r, api_received, sizeof(fe) * (size_t)npts);
      set_received(r);
      if (decode_fr_vote(&res_frvote, verbose, 0) != 0 || res_frvote.failed ||
          !res_frvote.resolved) {
        fprintf(stderr,
                "API FR-VOTE decoding failed or error values unresolved.\n");
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
    if (bms2_check_enabled)
      (void)bms2_syndrome_check();
    if (run_common_binary) {
      if (!fixed_error_value) {
        fprintf(stderr, "# COMMON-BINARY requires --fixed-error-value v (known "
                        "common value)\n");
        return 1;
      }
      decode_common_value_positions(fixed_error_value, NUM_ERRORS, verbose);
    }
    if (!quiet) {
      printf("# %d errors injected (seed %u)%s\n", NUM_ERRORS, seed,
             NUM_ERRORS > TAU ? "  -- beyond the basic bound" : "");
      if (fixed_error_value)
        printf("# injected error values: all fixed to %u\n",
               (unsigned)fixed_error_value);
      else
        puts("# injected error values: random nonzero field elements");
    }
    if (force && NUM_ERRORS > TAU && !quiet && (run_fr || run_bms))
      puts("# FR/BMS: t exceeds the proven basic bound; running anyway "
           "(expected to "
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
    if (show_values && !quiet) {
      if (run_fr && (NUM_ERRORS <= TAU || force))
        show_error_values(
            use_kotter_values
                ? "FR/Kotter"
                : (use_forney_values ? "FR/Forney" : "FR/solve_L"),
            &res_fr);
      if (run_bms && (NUM_ERRORS <= TAU || force))
        show_error_values("BMS", &res_bms);
      if (run_vote)
        show_error_values("VOTE", &res_vote);
      if (run_frvote)
        show_error_values("FR-VOTE", &res_frvote);
    }
    if (!quiet) {
      if (run_fr && (NUM_ERRORS <= TAU || force))
        printf("# time FR   : reduction %.3f s, position extraction %.3f s, "
               "values "
               "%.3f s\n",
               res_fr.t_main, res_fr.t_extract, res_fr.t_resolve);
      if (run_bms && (NUM_ERRORS <= TAU || force))
        printf("# time BMS  : loop %.3f s, scan %.3f s, values %.3f s\n",
               res_bms.t_main, res_bms.t_extract, res_bms.t_resolve);
      if (run_vote)
        printf("# time VOTE : BMS+voting %.3f s, scan %.3f s, values %.3f s\n",
               res_vote.t_main, res_vote.t_extract, res_vote.t_resolve);
      if (run_frvote)
        printf("# time FR-VOTE: FR-kernel+voting %.3f s, scan %.3f s, values "
               "%.3f s\n",
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
        printf("# trial %d: FR-VOTE %s\n", tr + 1, okfv ? "ok" : "FAIL");
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
  if (via_newton[best])
    free(NB[best].rho); /* ei/ej stay referenced by bas_ei/bas_ej */
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
int main(int argc, char **argv) { return ag_frvote_run(argc, argv); }
#endif