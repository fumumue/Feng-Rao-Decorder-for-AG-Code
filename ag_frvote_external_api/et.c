/*
 * codes.c -- encoders and decoders for classical algebraic code families
 *            (same conventions as noizy2.c: GF(2^m) with m <= 12, xorshift
 *            RNG with a seed, "# ..." report lines, --errors / -n / -v)
 *
 *   bch      narrow-sense / any-b binary BCH code (primitive, cyclic n | 2^m-1,
 *            or shortened), decoded by Berlekamp-Massey + Chien search
 *   golay    binary Golay [23,12,7] and extended [24,12,8], syndrome table
 *            (perfect code: every error pattern of weight <= 3 is corrected)
 *   goppa    binary classical Goppa code Gamma(L,g), g irreducible, corrects
 *            t = deg g errors: extended Euclid on the key equation modulo g^2
 *            (Patterson-equivalent, no square roots needed)
 *   alt      random binary alternant code (alpha_i, y_i random), t = r/2
 *   rm       binary Reed-Muller code RM(r,m) = [2^m, sum_{i<=r} C(m,i),
 *            2^(m-r)], Reed majority-logic decoding (corrects 2^(m-r-1)-1)
 *   hadamard Hadamard code [2^m, m, 2^(m-1)]; with -fht also RM(1,m): maximum-
 *            likelihood decoding by the fast Walsh-Hadamard transform,
 *            O(n log n), beyond the bounded-distance radius
 *   grs      generalized Reed-Solomon code over GF(2^m); errors AND erasures
 *            (2e + s <= n-k), Berlekamp-Massey + Forney
 *   rank     Gabidulin code (rank metric, linearized polynomials), n <= m,
 *            corrects t = (n-k)/2 rank errors, linearized key equation
 *   product  product code C1 x C2 of two binary codes (bch/golay/goppa/alt
 *            specs), iterative row/column hard-decision decoding
 *   concat   concatenated code: outer GRS over GF(2^m), inner binary code
 *            (any spec with k_in >= m, shortened if k_in > m); inner decoding
 *            failures become erasures for the outer decoder
 *
 * Binary alternant-type codes (bch, alt, goppa) are encoded through the exact
 * binary kernel of the GF(2) parity-check matrix (systematic on the free
 * columns), so k is always the true dimension, not just the lower bound.
 *
 * Build: cc -O2 -std=gnu11 -o codes codes.c
 * Run:   ./codes --help
 */
#define _POSIX_C_SOURCE 200809L
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint16_t fe;

#define MAXM 12   /* GF(2^m), m <= 12 (fe is 16 bit)                      */
#define PMAXD 1100 /* maximum polynomial degree (EXTENSION_POINT)           */

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static void die(const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  fprintf(stderr, "error: ");
  vfprintf(stderr, f, ap);
  fputc('\n', stderr);
  va_end(ap);
  exit(1);
}

/* ================= random numbers (same generator as noizy2.c) ============ */
static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) {
  rng_s ^= rng_s << 13;
  rng_s ^= rng_s >> 7;
  rng_s ^= rng_s << 17;
  return rng_s;
}
/* choose cnt distinct positions in [0,n) that are not flagged in excl */
static void pick(int n, int cnt, int *dst, const uint8_t *excl) {
  int avail = n;
  if (excl)
    for (int i = 0; i < n; ++i)
      avail -= excl[i] != 0;
  if (cnt > avail)
    die("cannot place %d distinct positions among %d available", cnt, avail);
  for (int e = 0; e < cnt; ++e) {
    int p, dup;
    do {
      p = (int)(rnd() % (uint64_t)n);
      dup = excl && excl[p];
      for (int k = 0; k < e; ++k)
        if (dst[k] == p)
          dup = 1;
    } while (dup);
    dst[e] = p;
  }
}

/* ================= GF(2^m), supported m <= 12 ================= */
typedef struct {
  int m, size, ord;
  unsigned poly;
  fe *exp, *log;
} GF;

static const unsigned DEFPOLY[13] = {0,    0,     0x7,   0xB,   0x13,
                                     0x25, 0x43,  0x89,  0x11D, 0x211,
                                     0x409, 0x805, 0x1053};

static GF *gf_new(int m, unsigned poly) {
  if (m < 2 || m > MAXM)
    die("--m must be in 2..%d", MAXM);
  if (!poly)
    poly = DEFPOLY[m];
  GF *F = calloc(1, sizeof *F);
  F->m = m;
  F->size = 1 << m;
  F->ord = F->size - 1;
  F->poly = poly;
  F->exp = malloc(sizeof(fe) * (2 * F->ord + 4));
  F->log = malloc(sizeof(fe) * F->size);
  unsigned x = 1;
  for (int i = 0; i < F->ord; ++i) {
    if (i > 0 && x == 1)
      die("polynomial 0x%X is not primitive of degree %d", poly, m);
    F->exp[i] = (fe)x;
    F->log[x] = (fe)i;
    x <<= 1;
    if (x & (unsigned)F->size)
      x ^= poly;
  }
  if (x != 1)
    die("polynomial 0x%X is not primitive of degree %d", poly, m);
  for (int i = F->ord; i < 2 * F->ord + 4; ++i)
    F->exp[i] = F->exp[i - F->ord];
  F->log[0] = 0;
  return F;
}
static inline fe gmul(const GF *F, fe a, fe b) {
  return (a && b) ? F->exp[F->log[a] + F->log[b]] : 0;
}
static inline fe ginv(const GF *F, fe a) { return F->exp[F->ord - F->log[a]]; }
static inline fe gdiv(const GF *F, fe a, fe b) { return gmul(F, a, ginv(F, b)); }
static fe gpow(const GF *F, fe a, long long n) {
  if (n == 0)
    return 1;
  if (!a)
    return 0;
  long long e = n % F->ord;
  if (e < 0)
    e += F->ord;
  return F->exp[(int)(((long long)F->log[a] * e) % F->ord)];
}
static fe gfrob(const GF *F, fe a, int i) { /* a^(2^i) = a^[i] */
  for (; i > 0; --i)
    a = gmul(F, a, a);
  return a;
}
static fe grand_nz(const GF *F) { return (fe)(1 + rnd() % (uint64_t)F->ord); }

/* ================= polynomials over GF(2^m); deg = -1 is the zero poly ===== */
typedef struct {
  int deg;
  fe c[PMAXD + 1];
} Poly;
static void ptrim(Poly *p) {
  while (p->deg >= 0 && p->c[p->deg] == 0)
    p->deg--;
}
static fe peval(const GF *F, const Poly *p, fe x) {
  fe acc = 0;
  for (int i = p->deg; i >= 0; --i)
    acc = (fe)(gmul(F, acc, x) ^ p->c[i]);
  return acc;
}
static void pcopy(Poly *d, const Poly *s) {
  d->deg = s->deg;
  if (s->deg >= 0)
    memcpy(d->c, s->c, sizeof(fe) * (size_t)(s->deg + 1));
}
static void pmul(const GF *F, const Poly *a, const Poly *b, Poly *r) {
  if (a->deg < 0 || b->deg < 0) {
    r->deg = -1;
    return;
  }
  if (a->deg + b->deg > PMAXD)
    die("polynomial degree exceeds PMAXD=%d", PMAXD);
  r->deg = a->deg + b->deg;
  memset(r->c, 0, sizeof(fe) * (size_t)(r->deg + 1));
  for (int i = 0; i <= a->deg; ++i)
    if (a->c[i])
      for (int j = 0; j <= b->deg; ++j)
        r->c[i + j] ^= gmul(F, a->c[i], b->c[j]);
  ptrim(r);
}
static void padd(const Poly *a, const Poly *b, Poly *r) {
  int d = a->deg > b->deg ? a->deg : b->deg;
  fe tmp[PMAXD + 1];
  for (int i = 0; i <= d; ++i)
    tmp[i] = (fe)((i <= a->deg ? a->c[i] : 0) ^ (i <= b->deg ? b->c[i] : 0));
  r->deg = d;
  if (d >= 0)
    memcpy(r->c, tmp, sizeof(fe) * (size_t)(d + 1));
  ptrim(r);
}
/* r = a mod b, q = a div b (q may be NULL); b != 0; r may alias a */
static void pdivmod(const GF *F, const Poly *a, const Poly *b, Poly *q,
                    Poly *r) {
  if (r != a)
    pcopy(r, a);
  if (q) {
    q->deg = a->deg >= b->deg ? a->deg - b->deg : -1;
    if (q->deg >= 0)
      memset(q->c, 0, sizeof(fe) * (size_t)(q->deg + 1));
  }
  fe ib = ginv(F, b->c[b->deg]);
  while (r->deg >= b->deg) {
    fe f = gmul(F, r->c[r->deg], ib);
    int sh = r->deg - b->deg;
    if (q)
      q->c[sh] = f;
    for (int i = 0; i <= b->deg; ++i)
      r->c[i + sh] ^= gmul(F, f, b->c[i]);
    ptrim(r);
  }
}
static void pderiv(const Poly *a, Poly *r) { /* characteristic 2 */
  r->deg = a->deg - 1;
  for (int i = 0; i <= r->deg; ++i)
    r->c[i] = (i % 2 == 0) ? a->c[i + 1] : 0;
  ptrim(r);
}
static void pgcd(const GF *F, const Poly *a, const Poly *b, Poly *g) {
  Poly x, y, r;
  pcopy(&x, a);
  pcopy(&y, b);
  while (y.deg >= 0) {
    pdivmod(F, &x, &y, NULL, &r);
    pcopy(&x, &y);
    pcopy(&y, &r);
  }
  pcopy(g, &x);
}
static void psqr_mod(const GF *F, const Poly *p, const Poly *g, Poly *out) {
  Poly t;
  if (p->deg < 0) {
    out->deg = -1;
    return;
  }
  t.deg = 2 * p->deg;
  memset(t.c, 0, sizeof(fe) * (size_t)(t.deg + 1));
  for (int i = 0; i <= p->deg; ++i)
    t.c[2 * i] = gmul(F, p->c[i], p->c[i]);
  pdivmod(F, &t, g, NULL, out);
}
/* g (monic, deg >= 1) is irreducible over GF(2^m) iff it has no irreducible
 * factor of degree <= deg/2, i.e. gcd(x^(Q^i) - x, g) = 1 for i <= deg/2 */
static int pirreducible(const GF *F, const Poly *g) {
  Poly P, x, d, t;
  x.deg = 1;
  x.c[0] = 0;
  x.c[1] = 1;
  if (g->deg == 1)
    return 1;
  pdivmod(F, &x, g, NULL, &P);
  for (int i = 1; i <= g->deg / 2; ++i) {
    for (int s = 0; s < F->m; ++s) { /* P <- P^(2^m) = P^Q */
      psqr_mod(F, &P, g, &t);
      pcopy(&P, &t);
    }
    padd(&P, &x, &d);
    if (d.deg < 0)
      return 0;
    pgcd(F, g, &d, &t);
    if (t.deg > 0)
      return 0;
  }
  return 1;
}

/* ================= linear algebra helpers ================= */
/* solve A x = b over GF(2^m), A is N x N row-major, destroyed; x -> b */
static int gf_solve(const GF *F, fe *A, fe *b, int N) {
  for (int c = 0; c < N; ++c) {
    int p = -1;
    for (int r = c; r < N; ++r)
      if (A[r * N + c]) {
        p = r;
        break;
      }
    if (p < 0)
      return -1;
    if (p != c) {
      for (int j = 0; j < N; ++j) {
        fe t = A[p * N + j];
        A[p * N + j] = A[c * N + j];
        A[c * N + j] = t;
      }
      fe t = b[p];
      b[p] = b[c];
      b[c] = t;
    }
    fe iv = ginv(F, A[c * N + c]);
    for (int j = 0; j < N; ++j)
      A[c * N + j] = gmul(F, A[c * N + j], iv);
    b[c] = gmul(F, b[c], iv);
    for (int r = 0; r < N; ++r)
      if (r != c && A[r * N + c]) {
        fe f = A[r * N + c];
        for (int j = 0; j < N; ++j)
          A[r * N + j] ^= gmul(F, f, A[c * N + j]);
        b[r] ^= gmul(F, f, b[c]);
      }
  }
  return 0;
}
/* GF(2) basis with combination tracking (vectors < 2^16, combos < 2^16) */
typedef struct {
  int has[16];
  unsigned vec[16], comb[16];
} B2;
static int hibit(unsigned v) { return 31 - __builtin_clz(v); }
/* insert v (tagged comb). returns 1 if independent; else 0 and *dep = the
 * combination of tags that adds up to zero */
static int b2_insert(B2 *b, unsigned v, unsigned comb, unsigned *dep) {
  while (v) {
    int hb = hibit(v);
    if (!b->has[hb]) {
      b->has[hb] = 1;
      b->vec[hb] = v;
      b->comb[hb] = comb;
      return 1;
    }
    v ^= b->vec[hb];
    comb ^= b->comb[hb];
  }
  if (dep)
    *dep = comb;
  return 0;
}
/* reduce v; returns the remainder (0 iff v in span), *mask = tags used */
static unsigned b2_reduce(const B2 *b, unsigned v, unsigned *mask) {
  *mask = 0;
  while (v) {
    int hb = hibit(v);
    if (!b->has[hb])
      return v;
    v ^= b->vec[hb];
    *mask ^= b->comb[hb];
  }
  return 0;
}

/* ================= Berlekamp-Massey ================= */
/* shortest LFSR for u[0..N-1]; C[0..N] = connection poly (C[0]=1); returns L */
static int bm(const GF *F, const fe *u, int N, fe *C) {
  fe *B = calloc((size_t)N + 2, sizeof(fe)), *Tt = calloc((size_t)N + 2, sizeof(fe));
  memset(C, 0, sizeof(fe) * (size_t)(N + 1));
  C[0] = 1;
  B[0] = 1;
  int L = 0, m = 1;
  fe b = 1;
  for (int k = 0; k < N; ++k) {
    fe d = u[k];
    for (int i = 1; i <= L; ++i)
      d ^= gmul(F, C[i], u[k - i]);
    if (!d) {
      ++m;
      continue;
    }
    fe coef = gdiv(F, d, b);
    if (2 * L <= k) {
      memcpy(Tt, C, sizeof(fe) * (size_t)(N + 1));
      for (int i = 0; i + m <= N; ++i)
        C[i + m] ^= gmul(F, coef, B[i]);
      L = k + 1 - L;
      memcpy(B, Tt, sizeof(fe) * (size_t)(N + 1));
      b = d;
      m = 1;
    } else {
      for (int i = 0; i + m <= N; ++i)
        C[i + m] ^= gmul(F, coef, B[i]);
      ++m;
    }
  }
  free(B);
  free(Tt);
  return L;
}

/* ================= generic alternant / GRS decoder =================
 * Parity checks   s_j = sum_i y_i c_i alpha_i^j   (j = 0..r-1, alpha_i != 0
 * distinct).  Corrects e errors + s erasures whenever 2e + s <= r:
 *   erasure locator Gamma, modified syndromes T = Gamma*S mod x^r, BM on
 *   T[s..r-1] -> Lambda, Psi = Gamma*Lambda, Omega = Psi*S mod x^r, Chien
 *   search, Forney  f_i = alpha_i Omega(1/alpha_i) / Psi'(1/alpha_i),
 *   error value e_i = f_i / y_i.
 * rcv[i] must be 0 at erased positions.  Returns the number of (nonzero)
 * error values, positions in epos[], values in eval[] (c_i = rcv_i + e_i);
 * -1 on decoding failure.  The result is re-verified against the syndromes. */
static int alt_decode(const GF *F, int n, const fe *al, const fe *y, int r,
                      const fe *rcv, const uint8_t *era, int *epos, fe *eval) {
  int res = -1;
  fe *S = calloc((size_t)r + 1, sizeof(fe)), *T = calloc((size_t)r + 1, sizeof(fe)),
     *C = calloc((size_t)r + 2, sizeof(fe));
  Poly *Gam = malloc(sizeof(Poly)), *Lam = malloc(sizeof(Poly)),
       *Psi = malloc(sizeof(Poly)), *Om = malloc(sizeof(Poly)),
       *dPsi = malloc(sizeof(Poly));
  if (r > PMAXD / 2)
    die("too many parity checks (r=%d) for PMAXD", r);
  for (int i = 0; i < n; ++i)
    if (rcv[i]) {
      fe t = gmul(F, y[i], rcv[i]);
      for (int j = 0; j < r; ++j) {
        S[j] ^= t;
        t = gmul(F, t, al[i]);
      }
    }
  int nz = 0;
  for (int j = 0; j < r; ++j)
    nz |= S[j];
  if (!nz) {
    res = 0;
    goto done;
  }
  int nu = 0;
  Gam->deg = 0;
  Gam->c[0] = 1;
  if (era)
    for (int i = 0; i < n; ++i)
      if (era[i]) {
        if (++nu > r)
          goto done;
        Gam->c[Gam->deg + 1] = 0;
        for (int j = Gam->deg + 1; j >= 1; --j)
          Gam->c[j] ^= gmul(F, al[i], Gam->c[j - 1]);
        Gam->deg++;
      }
  for (int j = 0; j < r; ++j) {
    fe acc = 0;
    for (int l = 0; l <= Gam->deg && l <= j; ++l)
      acc ^= gmul(F, Gam->c[l], S[j - l]);
    T[j] = acc;
  }
  int N = r - nu;
  int L = bm(F, T + nu, N, C);
  if (2 * L > N)
    goto done;
  Lam->deg = L;
  memcpy(Lam->c, C, sizeof(fe) * (size_t)(L + 1));
  ptrim(Lam);
  pmul(F, Gam, Lam, Psi);
  Om->deg = r - 1;
  for (int j = 0; j < r; ++j) {
    fe acc = 0;
    for (int l = 0; l <= Psi->deg && l <= j; ++l)
      acc ^= gmul(F, Psi->c[l], S[j - l]);
    Om->c[j] = acc;
  }
  ptrim(Om);
  pderiv(Psi, dPsi);
  int cnt = 0, nroots = 0;
  for (int i = 0; i < n; ++i) {
    fe x = ginv(F, al[i]);
    if (peval(F, Psi, x))
      continue;
    ++nroots;
    fe den = peval(F, dPsi, x);
    if (!den)
      goto done;
    fe f = gmul(F, al[i], gdiv(F, peval(F, Om, x), den));
    fe e = gdiv(F, f, y[i]);
    if (e) {
      epos[cnt] = i;
      eval[cnt++] = e;
    }
  }
  if (nroots != Psi->deg)
    goto done;
  for (int q = 0; q < cnt; ++q) { /* verify: corrected word has zero syndrome */
    fe t = gmul(F, y[epos[q]], eval[q]);
    for (int j = 0; j < r; ++j) {
      S[j] ^= t;
      t = gmul(F, t, al[epos[q]]);
    }
  }
  for (int j = 0; j < r; ++j)
    if (S[j])
      goto done;
  res = cnt;
done:
  free(S);
  free(T);
  free(C);
  free(Gam);
  free(Lam);
  free(Psi);
  free(Om);
  free(dPsi);
  return res;
}

/* ================= binary alternant-type code (bch / alt / goppa) =========
 * parity check  H = (y_i alpha_i^j), j < r, expanded over GF(2); the code is
 * the exact binary kernel.  goppa=1: y_i = 1/g(alpha_i), r = deg g, decoded
 * by the Euclidean algorithm modulo g^2. */
typedef struct {
  GF *F;
  int n, r, goppa;
  fe *al, *y, *invG2, *rb, *val;
  int *pos;
  Poly g, G2;
  int k, W, *info;
  uint64_t *gen; /* k rows of W words */
} AltCode;

static AltCode *altc_alloc(GF *F, int n, int r) {
  AltCode *A = calloc(1, sizeof *A);
  A->F = F;
  A->n = n;
  A->r = r;
  A->al = calloc((size_t)n, sizeof(fe));
  A->y = calloc((size_t)n, sizeof(fe));
  A->rb = calloc((size_t)n, sizeof(fe));
  A->val = calloc((size_t)n, sizeof(fe));
  A->pos = calloc((size_t)n, sizeof(int));
  return A;
}
static void altc_build(AltCode *A) {
  GF *F = A->F;
  int n = A->n, r = A->r, m = F->m, W = (n + 63) / 64, R = m * r;
  A->W = W;
  uint64_t *H = calloc((size_t)R * (size_t)W, sizeof(uint64_t));
  for (int i = 0; i < n; ++i) {
    fe t = A->y[i];
    for (int j = 0; j < r; ++j) {
      for (int b = 0; b < m; ++b)
        if ((t >> b) & 1)
          H[(size_t)(j * m + b) * W + i / 64] |= 1ULL << (i % 64);
      t = gmul(F, t, A->al[i]);
    }
  }
  int *piv = malloc(sizeof(int) * (size_t)(n + 1)), rank = 0;
  for (int c = 0; c < n && rank < R; ++c) {
    int p = -1;
    for (int q = rank; q < R; ++q)
      if ((H[(size_t)q * W + c / 64] >> (c % 64)) & 1) {
        p = q;
        break;
      }
    if (p < 0)
      continue;
    if (p != rank)
      for (int w = 0; w < W; ++w) {
        uint64_t t = H[(size_t)p * W + w];
        H[(size_t)p * W + w] = H[(size_t)rank * W + w];
        H[(size_t)rank * W + w] = t;
      }
    for (int q = 0; q < R; ++q)
      if (q != rank && ((H[(size_t)q * W + c / 64] >> (c % 64)) & 1))
        for (int w = c / 64; w < W; ++w)
          H[(size_t)q * W + w] ^= H[(size_t)rank * W + w];
    piv[rank++] = c;
  }
  uint8_t *isp = calloc((size_t)n, 1);
  for (int q = 0; q < rank; ++q)
    isp[piv[q]] = 1;
  A->k = n - rank;
  if (A->k <= 0)
    die("the code has dimension 0 (parameters too strong for n=%d)", n);
  A->info = malloc(sizeof(int) * (size_t)A->k);
  A->gen = calloc((size_t)A->k * (size_t)W, sizeof(uint64_t));
  int u = 0;
  for (int f = 0; f < n; ++f)
    if (!isp[f]) {
      A->info[u] = f;
      uint64_t *row = A->gen + (size_t)u * W;
      row[f / 64] |= 1ULL << (f % 64);
      for (int q = 0; q < rank; ++q)
        if ((H[(size_t)q * W + f / 64] >> (f % 64)) & 1)
          row[piv[q] / 64] |= 1ULL << (piv[q] % 64);
      ++u;
    }
  free(H);
  free(piv);
  free(isp);
}
static void altc_encode(const AltCode *A, const uint8_t *msg, uint8_t *cw) {
  int W = A->W;
  uint64_t *acc = calloc((size_t)W, sizeof(uint64_t));
  for (int u = 0; u < A->k; ++u)
    if (msg[u])
      for (int w = 0; w < W; ++w)
        acc[w] ^= A->gen[(size_t)u * W + w];
  for (int i = 0; i < A->n; ++i)
    cw[i] = (uint8_t)((acc[i / 64] >> (i % 64)) & 1);
  free(acc);
}
static int altc_decode_bm(const AltCode *A, const uint8_t *rcv,
                          const uint8_t *era, uint8_t *out) {
  int n = A->n;
  for (int i = 0; i < n; ++i) {
    int er = era && era[i];
    A->rb[i] = er ? 0 : rcv[i];
    out[i] = A->rb[i];
  }
  int c = alt_decode(A->F, n, A->al, A->y, A->r, A->rb, era, A->pos, A->val);
  if (c < 0)
    return -1;
  for (int q = 0; q < c; ++q) {
    if (A->val[q] != 1)
      return -1; /* not a binary error pattern */
    out[A->pos[q]] ^= 1;
  }
  return c;
}
/* S(z) = sum_{w_i=1} (z - alpha_i)^(-1) mod g^2 */
static void goppa_syndrome(const AltCode *A, const uint8_t *w, Poly *S) {
  const GF *F = A->F;
  int d = A->G2.deg;
  fe q[PMAXD + 1];
  S->deg = d - 1;
  memset(S->c, 0, sizeof(fe) * (size_t)d);
  for (int i = 0; i < A->n; ++i)
    if (w[i]) {
      q[d - 1] = A->G2.c[d];
      for (int j = d - 1; j >= 1; --j)
        q[j - 1] = (fe)(A->G2.c[j] ^ gmul(F, A->al[i], q[j]));
      for (int j = 0; j < d; ++j)
        S->c[j] ^= gmul(F, A->invG2[i], q[j]);
    }
  ptrim(S);
}
static int altc_decode_goppa(const AltCode *A, const uint8_t *rcv,
                             uint8_t *out) {
  const GF *F = A->F;
  int t = A->g.deg;
  memcpy(out, rcv, (size_t)A->n);
  Poly *S = malloc(sizeof(Poly)), *r0 = malloc(sizeof(Poly)),
       *r1 = malloc(sizeof(Poly)), *t0 = malloc(sizeof(Poly)),
       *t1 = malloc(sizeof(Poly)), *q = malloc(sizeof(Poly)),
       *rem = malloc(sizeof(Poly)), *qt = malloc(sizeof(Poly)),
       *t2 = malloc(sizeof(Poly));
  int res = -1;
  goppa_syndrome(A, rcv, S);
  if (S->deg < 0) {
    res = 0;
    goto done;
  }
  pcopy(r0, &A->G2);
  pcopy(r1, S);
  t0->deg = -1;
  t1->deg = 0;
  t1->c[0] = 1;
  while (r1->deg >= t) { /* Euclid until deg r < t: sigma = t1, omega = r1 */
    pdivmod(F, r0, r1, q, rem);
    pmul(F, q, t1, qt);
    padd(t0, qt, t2);
    pcopy(r0, r1);
    pcopy(r1, rem);
    pcopy(t0, t1);
    pcopy(t1, t2);
  }
  if (t1->deg < 1 || t1->deg > t)
    goto done;
  int cnt = 0;
  for (int i = 0; i < A->n; ++i)
    if (!peval(F, t1, A->al[i])) {
      out[i] ^= 1;
      ++cnt;
    }
  if (cnt != t1->deg)
    goto done;
  goppa_syndrome(A, out, S);
  if (S->deg >= 0)
    goto done;
  res = cnt;
done:
  free(S);
  free(r0);
  free(r1);
  free(t0);
  free(t1);
  free(q);
  free(rem);
  free(qt);
  free(t2);
  return res;
}

/* ---- constructors ---- */
static AltCode *make_bch(int m, unsigned poly, int t, int n, int b) {
  GF *F = gf_new(m, poly);
  if (n <= 0)
    n = F->ord;
  if (n > F->ord)
    die("BCH length n=%d exceeds 2^m-1=%d (use a larger --m)", n, F->ord);
  if (t < 1 || 2 * t >= n)
    die("BCH needs 1 <= t and 2t < n");
  /* n | 2^m-1, n < 2^m-1: cyclic code of length n (beta of order n);
   * otherwise primitive or shortened primitive BCH code */
  fe beta = (n < F->ord && F->ord % n == 0) ? F->exp[F->ord / n] : F->exp[1];
  AltCode *A = altc_alloc(F, n, 2 * t);
  for (int i = 0; i < n; ++i) {
    A->al[i] = gpow(F, beta, i);
    A->y[i] = gpow(F, A->al[i], b);
  }
  altc_build(A);
  return A;
}
static AltCode *make_alt(int m, unsigned poly, int t, int n) {
  GF *F = gf_new(m, poly);
  if (n <= 0)
    n = F->ord;
  if (n > F->ord)
    die("alternant length n=%d exceeds 2^m-1=%d (alpha_i must be nonzero)", n,
        F->ord);
  if (t < 1 || 2 * t >= n)
    die("alternant needs 1 <= t and 2t < n");
  AltCode *A = altc_alloc(F, n, 2 * t);
  fe *perm = malloc(sizeof(fe) * (size_t)F->ord);
  for (int i = 0; i < F->ord; ++i)
    perm[i] = F->exp[i];
  for (int i = F->ord - 1; i > 0; --i) { /* Fisher-Yates */
    int j = (int)(rnd() % (uint64_t)(i + 1));
    fe tmp = perm[i];
    perm[i] = perm[j];
    perm[j] = tmp;
  }
  for (int i = 0; i < n; ++i) {
    A->al[i] = perm[i];
    A->y[i] = grand_nz(F);
  }
  free(perm);
  altc_build(A);
  return A;
}
static AltCode *make_goppa(int m, unsigned poly, int t, int n) {
  GF *F = gf_new(m, poly);
  if (t < 1 || t > PMAXD / 4)
    die("Goppa degree t must be in 1..%d", PMAXD / 4);
  Poly g;
  int tries = 0;
  do { /* random monic irreducible g of degree t */
    g.deg = t;
    for (int i = 0; i < t; ++i)
      g.c[i] = (fe)(rnd() % (uint64_t)F->size);
    g.c[t] = 1;
    if (++tries > 200000)
      die("could not find an irreducible polynomial of degree %d", t);
  } while (!pirreducible(F, &g));
  fe *L = malloc(sizeof(fe) * (size_t)F->size);
  int nl = 0;
  for (int x = 0; x < F->size; ++x)
    if (peval(F, &g, (fe)x))
      L[nl++] = (fe)x;
  if (n <= 0)
    n = nl;
  if (n > nl)
    die("Goppa length n=%d exceeds |L|=%d", n, nl);
  if (n <= 2 * t)
    die("Goppa needs n > 2t");
  AltCode *A = altc_alloc(F, n, t);
  A->goppa = 1;
  pcopy(&A->g, &g);
  pmul(F, &g, &g, &A->G2);
  A->invG2 = malloc(sizeof(fe) * (size_t)n);
  for (int i = 0; i < n; ++i) {
    A->al[i] = L[i];
    fe gv = peval(F, &g, L[i]);
    A->y[i] = ginv(F, gv);
    A->invG2[i] = ginv(F, gmul(F, gv, gv));
  }
  free(L);
  altc_build(A);
  return A;
}

/* ================= Golay codes ================= */
#define GOLAY_G 0xC75u /* x^11+x^10+x^6+x^5+x^4+x^2+1 divides x^23 + 1 */
static uint32_t gol_rem(uint32_t v) {
  for (int i = 22; i >= 11; --i)
    if ((v >> i) & 1)
      v ^= GOLAY_G << (i - 11);
  return v;
}
static uint32_t *golay_table(void) {
  uint32_t *tab = malloc(2048 * sizeof(uint32_t));
  for (int i = 0; i < 2048; ++i)
    tab[i] = 0xFFFFFFFFu;
  tab[0] = 0;
  for (int a = 0; a < 23; ++a) {
    tab[gol_rem(1u << a)] = 1u << a;
    for (int b = a + 1; b < 23; ++b) {
      tab[gol_rem((1u << a) | (1u << b))] = (1u << a) | (1u << b);
      for (int c = b + 1; c < 23; ++c) {
        uint32_t e = (1u << a) | (1u << b) | (1u << c);
        tab[gol_rem(e)] = e;
      }
    }
  }
  for (int i = 0; i < 2048; ++i)
    if (tab[i] == 0xFFFFFFFFu)
      die("Golay generator polynomial check failed (not a perfect code)");
  return tab;
}

/* ================= unified binary code object ================= */
static int g_fht = 0; /* -fht: RM(1,m) is decoded by the Walsh-Hadamard transform */
typedef enum { BC_ALT = 0, BC_GOPPA = 1, BC_GOLAY = 2, BC_RM = 3, BC_HAD = 4 } BcKind;
typedef struct {
  char name[128];
  BcKind kind;
  int n, k, t, dmin, ext;
  int *info; /* message bit j sits at codeword position info[j] */
  AltCode *alt;
  uint32_t *gtab;
  int rm_r, rm_m;
  unsigned *mon;   /* RM: monomial x_S (bit mask S), degree <= r */
  uint8_t *gsys;   /* RM: systematic generator, k rows of n bytes */
} BinCode;

static BinCode *bc_from_alt(AltCode *A, const char *name, int t) {
  BinCode *B = calloc(1, sizeof *B);
  snprintf(B->name, sizeof B->name, "%s", name);
  B->kind = A->goppa ? BC_GOPPA : BC_ALT;
  B->n = A->n;
  B->k = A->k;
  B->t = t;
  B->dmin = 2 * t + 1;
  B->info = A->info;
  B->alt = A;
  return B;
}
static BinCode *bc_golay(int ext) {
  BinCode *B = calloc(1, sizeof *B);
  B->kind = BC_GOLAY;
  B->ext = ext;
  B->n = ext ? 24 : 23;
  B->k = 12;
  B->t = 3;
  B->dmin = ext ? 8 : 7;
  snprintf(B->name, sizeof B->name, "Golay[%d,12,%d]", B->n, B->dmin);
  B->info = malloc(sizeof(int) * 12);
  for (int j = 0; j < 12; ++j)
    B->info[j] = 11 + j;
  B->gtab = golay_table();
  return B;
}
/* Reed-Muller RM(r,m): point p in [0,2^m) has coordinates = bits of p,
 * monomial x_S takes the value 1 at p iff (p & S) == S. */
static BinCode *bc_rm(int r, int m) {
  if (m < 1 || m > MAXM || r < 0 || r > m)
    die("Reed-Muller needs 0 <= r <= m <= %d", MAXM);
  int n = 1 << m, k = 0;
  BinCode *B = calloc(1, sizeof *B);
  B->kind = BC_RM;
  B->rm_r = r;
  B->rm_m = m;
  B->n = n;
  for (int S = 0; S < n; ++S)
    if (__builtin_popcount(S) <= r)
      ++k;
  B->k = k;
  B->dmin = 1 << (m - r);
  B->t = (B->dmin - 1) / 2;
  snprintf(B->name, sizeof B->name, "RM(%d,%d)[%d,%d,%d]", r, m, n, k, B->dmin);
  B->mon = malloc(sizeof(unsigned) * (size_t)k);
  int u = 0;
  for (int d = r; d >= 0; --d) /* highest degree first */
    for (int S = 0; S < n; ++S)
      if (__builtin_popcount(S) == d)
        B->mon[u++] = (unsigned)S;
  uint8_t *G = malloc((size_t)k * (size_t)n);
  for (int i = 0; i < k; ++i)
    for (int pt = 0; pt < n; ++pt)
      G[(size_t)i * n + pt] = ((unsigned)pt & B->mon[i]) == B->mon[i];
  B->info = malloc(sizeof(int) * (size_t)k);
  int rank = 0;
  for (int c = 0; c < n && rank < k; ++c) { /* Gauss-Jordan -> systematic */
    int pv = -1;
    for (int q = rank; q < k; ++q)
      if (G[(size_t)q * n + c]) {
        pv = q;
        break;
      }
    if (pv < 0)
      continue;
    if (pv != rank)
      for (int j = 0; j < n; ++j) {
        uint8_t t = G[(size_t)pv * n + j];
        G[(size_t)pv * n + j] = G[(size_t)rank * n + j];
        G[(size_t)rank * n + j] = t;
      }
    for (int q = 0; q < k; ++q)
      if (q != rank && G[(size_t)q * n + c])
        for (int j = 0; j < n; ++j)
          G[(size_t)q * n + j] ^= G[(size_t)rank * n + j];
    B->info[rank++] = c;
  }
  if (rank != k)
    die("Reed-Muller generator has rank %d != %d", rank, k);
  B->gsys = G;
  return B;
}
/* Reed majority-logic decoding: for d = r..0 every coefficient a_S, |S| = d,
 * is the majority of the 2^(m-d) disjoint check sums  sum_{x_S free} w(x)
 * (the other coordinates fixed); decoded degree-d terms are then removed. */
static int rm_decode(const BinCode *B, const uint8_t *rcv, uint8_t *out) {
  int n = B->n, m = B->rm_m, k = B->k;
  uint8_t *w = malloc((size_t)n), *a = calloc((size_t)k, 1);
  memcpy(w, rcv, (size_t)n);
  int res = -1, i = 0;
  for (int d = B->rm_r; d >= 0; --d) {
    int i0 = i;
    for (; i < k && __builtin_popcount(B->mon[i]) == d; ++i) {
      unsigned S = B->mon[i], C = ~S & (unsigned)(n - 1);
      long ones = 0, checks = 1L << (m - d);
      for (unsigned t = C;; t = (t - 1) & C) {
        int par = 0;
        for (unsigned s = S;; s = (s - 1) & S) {
          par ^= w[t | s];
          if (!s)
            break;
        }
        ones += par;
        if (!t)
          break;
      }
      if (2 * ones == checks)
        goto done; /* tie: failure */
      a[i] = 2 * ones > checks;
    }
    for (int q = i0; q < i; ++q)
      if (a[q])
        for (int pt = 0; pt < n; ++pt)
          if (((unsigned)pt & B->mon[q]) == B->mon[q])
            w[pt] ^= 1;
  }
  memset(out, 0, (size_t)n);
  for (int q = 0; q < k; ++q)
    if (a[q])
      for (int pt = 0; pt < n; ++pt)
        if (((unsigned)pt & B->mon[q]) == B->mon[q])
          out[pt] ^= 1;
  int cnt = 0;
  for (int pt = 0; pt < n; ++pt)
    cnt += out[pt] != rcv[pt];
  if (cnt <= B->t)
    res = cnt;
done:
  free(w);
  free(a);
  return res;
}
/* in-place fast Walsh-Hadamard transform (n = 2^m), n log n additions */
static void fwht(int *a, int n) {
  for (int h = 1; h < n; h <<= 1)
    for (int i = 0; i < n; i += h << 1)
      for (int j = i; j < i + h; ++j) {
        int x = a[j], y = a[j + h];
        a[j] = x + y;
        a[j + h] = x - y;
      }
}
/* ML decoding of first-order words  c(x) = a0 + a.x  via
 *   F[a] = sum_x (-1)^(r(x)+a.x) = n - 2 d(r, a.x):
 * the largest |F| (RM(1,m)) or largest F (Hadamard code, a0 = 0 forced) gives
 * the nearest codeword; ties = detected failure.  Returns distance or -1. */
static int fht_decode(const BinCode *B, const uint8_t *rcv, uint8_t *out,
                      int allow_complement) {
  int n = B->n;
  int *F = malloc(sizeof(int) * (size_t)n);
  for (int x = 0; x < n; ++x)
    F[x] = rcv[x] ? -1 : 1;
  fwht(F, n);
  int best = -1, bv = -1, ties = 0;
  for (int a = 0; a < n; ++a) {
    int v = allow_complement ? abs(F[a]) : F[a];
    if (v > bv) {
      bv = v;
      best = a;
      ties = 1;
    } else if (v == bv)
      ++ties;
  }
  int a0 = allow_complement && F[best] < 0;
  int cnt = 0;
  for (int x = 0; x < n; ++x) {
    out[x] = (uint8_t)((__builtin_popcount((unsigned)(best & x)) & 1) ^ a0);
    cnt += out[x] != rcv[x];
  }
  free(F);
  return ties > 1 ? -1 : cnt;
}
static BinCode *bc_had(int m) {
  if (m < 2 || m > MAXM)
    die("Hadamard code needs 2 <= m <= %d", MAXM);
  BinCode *B = calloc(1, sizeof *B);
  B->kind = BC_HAD;
  B->n = 1 << m;
  B->k = m;
  B->rm_m = m;
  B->dmin = 1 << (m - 1);
  B->t = (B->dmin - 1) / 2;
  snprintf(B->name, sizeof B->name, "Hadamard[%d,%d,%d]", B->n, m, B->dmin);
  B->info = malloc(sizeof(int) * (size_t)m);
  for (int j = 0; j < m; ++j)
    B->info[j] = 1 << j; /* c(e_j) = a_j: systematic */
  return B;
}
static void bc_encode(const BinCode *B, const uint8_t *msg, uint8_t *cw) {
  if (B->kind == BC_GOLAY) {
    uint32_t m = 0;
    for (int j = 0; j < 12; ++j)
      m |= (uint32_t)(msg[j] & 1) << j;
    uint32_t v = m << 11;
    v |= gol_rem(v);
    for (int i = 0; i < 23; ++i)
      cw[i] = (uint8_t)((v >> i) & 1);
    if (B->ext)
      cw[23] = (uint8_t)(__builtin_popcount(v) & 1);
  } else if (B->kind == BC_HAD) {
    unsigned a = 0;
    for (int j = 0; j < B->k; ++j)
      a |= (unsigned)(msg[j] & 1) << j;
    for (int x = 0; x < B->n; ++x)
      cw[x] = (uint8_t)(__builtin_popcount(a & (unsigned)x) & 1);
  } else if (B->kind == BC_RM) {
    memset(cw, 0, (size_t)B->n);
    for (int u = 0; u < B->k; ++u)
      if (msg[u])
        for (int j = 0; j < B->n; ++j)
          cw[j] ^= B->gsys[(size_t)u * B->n + j];
  } else
    altc_encode(B->alt, msg, cw);
}
/* corrected-error count, or -1 (detected failure).  era may be NULL;
 * erasures are supported by BCH/alternant codes only. */
static int bc_decode(const BinCode *B, const uint8_t *rcv, const uint8_t *era,
                     uint8_t *out) {
  if (B->kind == BC_GOLAY) {
    uint32_t v = 0;
    for (int i = 0; i < 23; ++i)
      v |= (uint32_t)(rcv[i] & 1) << i;
    uint32_t e = B->gtab[gol_rem(v)], c = v ^ e;
    int cnt = __builtin_popcount(e);
    for (int i = 0; i < 23; ++i)
      out[i] = (uint8_t)((c >> i) & 1);
    if (B->ext) {
      int par = __builtin_popcount(c) & 1;
      out[23] = (uint8_t)par;
      cnt += (rcv[23] & 1) != par;
      if (cnt > 3)
        return -1; /* 4 errors: detected */
    }
    return cnt;
  }
  if (B->kind == BC_HAD)
    return fht_decode(B, rcv, out, 0);
  if (B->kind == BC_RM)
    return (g_fht && B->rm_r == 1) ? fht_decode(B, rcv, out, 1)
                                   : rm_decode(B, rcv, out);
  if (B->kind == BC_GOPPA)
    return altc_decode_goppa(B->alt, rcv, out);
  return altc_decode_bm(B->alt, rcv, era, out);
}

/* parse "bch:m:t[:n[:b]]", "golay", "golay24", "goppa:m:t[:n]", "alt:m:n:t" */
static BinCode *bc_parse(const char *spec, unsigned poly) {
  char buf[128], *tok[8];
  int nt = 0;
  snprintf(buf, sizeof buf, "%s", spec);
  for (char *p = strtok(buf, ":"); p && nt < 8; p = strtok(NULL, ":"))
    tok[nt++] = p;
  if (!nt)
    die("empty code spec");
  int v[8] = {0};
  for (int i = 1; i < nt; ++i)
    v[i] = atoi(tok[i]);
  char name[128];
  if (!strcmp(tok[0], "golay"))
    return bc_golay(0);
  if (!strcmp(tok[0], "golay24"))
    return bc_golay(1);
  if (!strcmp(tok[0], "had") && nt >= 2)
    return bc_had(v[1]);
  if (!strcmp(tok[0], "rm") && nt >= 3)
    return bc_rm(v[1], v[2]);
  if (!strcmp(tok[0], "bch") && nt >= 3) {
    int n = nt > 3 ? v[3] : 0, b = nt > 4 ? v[4] : 1;
    AltCode *A = make_bch(v[1], poly, v[2], n, b);
    snprintf(name, sizeof name, "BCH[%d,%d,>=%d] GF(2^%d) b=%d", A->n, A->k,
             2 * v[2] + 1, v[1], b);
    return bc_from_alt(A, name, v[2]);
  }
  if (!strcmp(tok[0], "goppa") && nt >= 3) {
    AltCode *A = make_goppa(v[1], poly, v[2], nt > 3 ? v[3] : 0);
    snprintf(name, sizeof name, "Goppa[%d,%d,>=%d] GF(2^%d) deg g=%d", A->n,
             A->k, 2 * v[2] + 1, v[1], v[2]);
    return bc_from_alt(A, name, v[2]);
  }
  if (!strcmp(tok[0], "alt") && nt >= 4) {
    AltCode *A = make_alt(v[1], poly, v[3], v[2]);
    snprintf(name, sizeof name, "alternant[%d,>=%d,>=%d] GF(2^%d)", A->n, A->k,
             2 * v[3] + 1, v[1]);
    return bc_from_alt(A, name, v[3]);
  }
  die("bad code spec '%s' (bch:m:t[:n[:b]] | golay | golay24 | goppa:m:t[:n] | "
      "alt:m:n:t | rm:r:m | had:m)",
      spec);
  return NULL;
}

/* ================= GRS ================= */
typedef struct {
  GF *F;
  int n, k;
  fe *al, *v, *y, *rb, *val;
  int *pos;
  int found; /* number of error values of the last decode */
} GRS;

static GRS *grs_new(GF *F, int n, int k, int shuffle, int randv) {
  if (n > F->ord)
    die("GRS length n=%d exceeds 2^m-1=%d", n, F->ord);
  if (k < 1 || k >= n)
    die("GRS needs 1 <= k < n");
  GRS *G = calloc(1, sizeof *G);
  G->F = F;
  G->n = n;
  G->k = k;
  G->al = malloc(sizeof(fe) * (size_t)n);
  G->v = malloc(sizeof(fe) * (size_t)n);
  G->y = malloc(sizeof(fe) * (size_t)n);
  G->rb = malloc(sizeof(fe) * (size_t)n);
  G->val = malloc(sizeof(fe) * (size_t)n);
  G->pos = malloc(sizeof(int) * (size_t)n);
  fe *perm = malloc(sizeof(fe) * (size_t)F->ord);
  for (int i = 0; i < F->ord; ++i)
    perm[i] = F->exp[i];
  if (shuffle)
    for (int i = F->ord - 1; i > 0; --i) {
      int j = (int)(rnd() % (uint64_t)(i + 1));
      fe t = perm[i];
      perm[i] = perm[j];
      perm[j] = t;
    }
  for (int i = 0; i < n; ++i) {
    G->al[i] = perm[i];
    G->v[i] = randv ? grand_nz(F) : 1;
  }
  free(perm);
  for (int i = 0; i < n; ++i) { /* dual multipliers  1/(v_i prod (a_i-a_l)) */
    fe p = G->v[i];
    for (int l = 0; l < n; ++l)
      if (l != i)
        p = gmul(F, p, G->al[i] ^ G->al[l]);
    G->y[i] = ginv(F, p);
  }
  return G;
}
static void grs_encode(const GRS *G, const fe *msg, fe *cw) {
  for (int i = 0; i < G->n; ++i) {
    fe acc = 0;
    for (int j = G->k - 1; j >= 0; --j)
      acc = (fe)(gmul(G->F, acc, G->al[i]) ^ msg[j]);
    cw[i] = gmul(G->F, G->v[i], acc);
  }
}
static int grs_decode(GRS *G, const fe *rcv, const uint8_t *era, fe *out) {
  for (int i = 0; i < G->n; ++i) {
    int er = era && era[i];
    G->rb[i] = er ? 0 : rcv[i];
    out[i] = G->rb[i];
  }
  int c = alt_decode(G->F, G->n, G->al, G->y, G->n - G->k, G->rb, era, G->pos,
                     G->val);
  G->found = c;
  if (c < 0)
    return -1;
  for (int q = 0; q < c; ++q)
    out[G->pos[q]] ^= G->val[q];
  return c;
}
/* Lagrange interpolation on the first k points: cw_i / v_i = f(alpha_i) */
static void grs_message(const GRS *G, const fe *cw, fe *msg) {
  const GF *F = G->F;
  int k = G->k;
  fe *M = calloc((size_t)k + 1, sizeof(fe)), *Q = calloc((size_t)k + 1, sizeof(fe));
  M[0] = 1;
  for (int i = 0; i < k; ++i) { /* M <- M * (x + al_i) */
    for (int j = i + 1; j >= 1; --j)
      M[j] = (fe)(M[j - 1] ^ gmul(F, G->al[i], M[j]));
    M[0] = gmul(F, G->al[i], M[0]);
  }
  memset(msg, 0, sizeof(fe) * (size_t)k);
  for (int i = 0; i < k; ++i) {
    Q[k - 1] = M[k];
    for (int j = k - 1; j >= 1; --j)
      Q[j - 1] = (fe)(M[j] ^ gmul(F, G->al[i], Q[j]));
    fe den = 0;
    for (int j = k - 1; j >= 0; --j)
      den = (fe)(gmul(F, den, G->al[i]) ^ Q[j]);
    fe sc = gdiv(F, gdiv(F, cw[i], G->v[i]), den);
    for (int j = 0; j < k; ++j)
      msg[j] ^= gmul(F, sc, Q[j]);
  }
  free(M);
  free(Q);
}

/* ================= Gabidulin (rank metric) ================= */
typedef struct {
  GF *F;
  int n, k;
  fe *g, *h;
  fe *gp; /* gp[i*n+j] = g_j^[i], i < k      */
  fe *hp; /* hp[i*n+j] = h_j^[i], i < n-k    */
} Gab;

static Gab *gab_new(GF *F, int n, int k) {
  if (n > F->m)
    die("Gabidulin needs n <= m (n=%d, m=%d)", n, F->m);
  if (n < 2 || k < 1 || k >= n)
    die("Gabidulin needs 1 <= k < n");
  Gab *G = calloc(1, sizeof *G);
  G->F = F;
  G->n = n;
  G->k = k;
  G->g = malloc(sizeof(fe) * (size_t)n);
  G->h = malloc(sizeof(fe) * (size_t)n);
  for (int j = 0; j < n; ++j)
    G->g[j] = F->exp[j]; /* 1, a, a^2, ...: independent over GF(2) */
  int N = n - 1;
  fe *A = malloc(sizeof(fe) * (size_t)N * (size_t)N), *b = malloc(sizeof(fe) * (size_t)N);
  for (int i = 0; i < N; ++i) { /* sum_j h_j g_j^[i] = 0, i = 0..n-2, h_{n-1}=1 */
    for (int j = 0; j < N; ++j)
      A[i * N + j] = gfrob(F, G->g[j], i);
    b[i] = gfrob(F, G->g[n - 1], i);
  }
  if (gf_solve(F, A, b, N))
    die("Gabidulin: Moore matrix is singular");
  for (int j = 0; j < N; ++j)
    G->h[j] = b[j];
  G->h[n - 1] = 1;
  /* H rows must be h_j^[i-(n-k-1)], i = 0..n-k-1 (then H G^T = 0 follows from
   * sum_j h_j g_j^[e] = 0 for e = 0..n-2); absorb the shift into h */
  for (int j = 0; j < n; ++j)
    G->h[j] = gfrob(F, G->h[j], F->m - (n - k - 1));
  free(A);
  free(b);
  G->gp = malloc(sizeof(fe) * (size_t)k * (size_t)n);
  for (int i = 0; i < k; ++i)
    for (int j = 0; j < n; ++j)
      G->gp[i * n + j] = gfrob(F, G->g[j], i);
  G->hp = malloc(sizeof(fe) * (size_t)(n - k) * (size_t)n);
  for (int i = 0; i < n - k; ++i)
    for (int j = 0; j < n; ++j)
      G->hp[i * n + j] = gfrob(F, G->h[j], i);
  return G;
}
static void gab_encode(const Gab *G, const fe *msg, fe *cw) {
  for (int j = 0; j < G->n; ++j) {
    fe acc = 0;
    for (int i = 0; i < G->k; ++i)
      acc ^= gmul(G->F, msg[i], G->gp[i * G->n + j]);
    cw[j] = acc;
  }
}
static int gab_message(const Gab *G, const fe *cw, fe *msg) {
  int k = G->k;
  fe *A = malloc(sizeof(fe) * (size_t)k * (size_t)k);
  for (int j = 0; j < k; ++j) {
    for (int i = 0; i < k; ++i)
      A[j * k + i] = G->gp[i * G->n + j];
    msg[j] = cw[j];
  }
  int rc = gf_solve(G->F, A, msg, k);
  free(A);
  return rc;
}
static int rank_weight(const GF *F, const fe *e, int n) {
  B2 b;
  memset(&b, 0, sizeof b);
  int rk = 0;
  for (int j = 0; j < n; ++j)
    if (e[j])
      rk += b2_insert(&b, e[j], 0, NULL);
  (void)F;
  return rk;
}
/* returns the rank of the corrected error (>= 0), or -1 on failure */
static int gab_decode(const Gab *G, const fe *y, fe *out) {
  const GF *F = G->F;
  int n = G->n, r = n - G->k, m = F->m;
  fe s[16], A[64], rhs[8];
  memcpy(out, y, sizeof(fe) * (size_t)n);
  int nz = 0;
  for (int i = 0; i < r; ++i) {
    fe a = 0;
    for (int j = 0; j < n; ++j)
      a ^= gmul(F, y[j], G->hp[i * n + j]);
    s[i] = a;
    nz |= a;
  }
  if (!nz)
    return 0;
  int tau, found = 0;
  fe lam[8];
  for (tau = r / 2; tau >= 1; --tau) {
    /* sum_{l=0}^{tau} Lambda_l s_{i-l}^[l] = 0, i = tau..2tau-1, Lambda_tau=1 */
    for (int row = 0; row < tau; ++row) {
      for (int l = 0; l < tau; ++l)
        A[row * tau + l] = gfrob(F, s[row + tau - l], l);
      rhs[row] = gfrob(F, s[row], tau);
    }
    if (gf_solve(F, A, rhs, tau) == 0) {
      for (int l = 0; l < tau; ++l)
        lam[l] = rhs[l];
      found = 1;
      break;
    }
  }
  if (!found)
    return -1;
  /* root space of Lambda(x) = sum_{l<tau} lam_l x^[l] + x^[tau]  (dim tau) */
  fe a[8];
  int na = 0;
  B2 kb;
  memset(&kb, 0, sizeof kb);
  for (int u = 0; u < m; ++u) {
    fe x = (fe)(1u << u), img = gfrob(F, x, tau);
    for (int l = 0; l < tau; ++l)
      img ^= gmul(F, lam[l], gfrob(F, x, l));
    unsigned dep;
    if (!b2_insert(&kb, img, 1u << u, &dep)) {
      if (na >= 8)
        return -1;
      a[na++] = (fe)dep;
    }
  }
  if (na != tau)
    return -1;
  /* z_u = sum_j B_uj h_j from  s_i^[m-i] = sum_u a_u^[m-i] z_u, i < tau */
  fe M[64], zr[8];
  for (int i = 0; i < tau; ++i) {
    for (int u = 0; u < tau; ++u)
      M[i * tau + u] = gfrob(F, a[u], m - i);
    zr[i] = gfrob(F, s[i], m - i);
  }
  if (gf_solve(F, M, zr, tau))
    return -1;
  B2 hb;
  memset(&hb, 0, sizeof hb);
  for (int j = 0; j < n; ++j)
    if (!b2_insert(&hb, G->h[j], 1u << j, NULL))
      return -1;
  for (int j = 0; j < n; ++j)
    out[j] = y[j];
  for (int u = 0; u < tau; ++u) {
    unsigned mask;
    if (b2_reduce(&hb, zr[u], &mask))
      return -1;
    for (int j = 0; j < n; ++j)
      if ((mask >> j) & 1)
        out[j] ^= a[u];
  }
  for (int i = 0; i < r; ++i) { /* verify */
    fe acc = 0;
    for (int j = 0; j < n; ++j)
      acc ^= gmul(F, out[j], G->hp[i * n + j]);
    if (acc)
      return -1;
  }
  return tau;
}
/* random error vector of rank exactly tau */
static void rank_error(const GF *F, int n, int tau, fe *e) {
  fe a[MAXM];
  unsigned bm[MAXM];
  B2 ba, bb;
  memset(&ba, 0, sizeof ba);
  memset(&bb, 0, sizeof bb);
  for (int u = 0; u < tau;) {
    fe x = (fe)(1 + rnd() % (uint64_t)F->ord);
    if (b2_insert(&ba, x, 0, NULL))
      a[u++] = x;
  }
  for (int u = 0; u < tau;) {
    unsigned x = (unsigned)(rnd() % (1ull << n));
    if (b2_insert(&bb, x, 0, NULL))
      bm[u++] = x;
  }
  for (int j = 0; j < n; ++j) {
    e[j] = 0;
    for (int u = 0; u < tau; ++u)
      if ((bm[u] >> j) & 1)
        e[j] ^= a[u];
  }
}

/* ================= experiment drivers ================= */
typedef struct {
  int trials, ok, fail, wrong;
  double t_enc, t_dec;
} Stat;
static void stat_add(Stat *s, int cls) {
  s->trials++;
  if (cls == 0)
    s->ok++;
  else if (cls == 1)
    s->fail++;
  else
    s->wrong++;
}
static const char *cls_name(int c) {
  return c == 0 ? "OK" : (c == 1 ? "FAILED (detected)" : "MISCORRECTED");
}
static void stat_print(const Stat *s, const char *what) {
  printf("# summary of %d trials with %s: ok %d, detected failure %d, "
         "miscorrection %d\n",
         s->trials, what, s->ok, s->fail, s->wrong);
  printf("# time: encode %.4f s, decode %.4f s (total over %d trials)\n",
         s->t_enc, s->t_dec, s->trials);
}
static void print_bits(const char *tag, const uint8_t *b, int n) {
  printf("# %s ", tag);
  for (int i = 0; i < n; ++i)
    putchar('0' + b[i]);
  putchar('\n');
}
static void print_ilist(const char *tag, const int *p, int c) {
  printf("# %s (%d):", tag, c);
  for (int i = 0; i < c; ++i)
    printf(" %d", p[i]);
  putchar('\n');
}
static void sort_ints(int *a, int n) {
  for (int i = 1; i < n; ++i) {
    int x = a[i], j = i - 1;
    while (j >= 0 && a[j] > x) {
      a[j + 1] = a[j];
      --j;
    }
    a[j + 1] = x;
  }
}

/* ---- binary codes: bch / alt / goppa / golay ---- */
static void run_bincode(const BinCode *B, int trials, int nerr, int nera,
                        int verbose, int showv) {
  int n = B->n, k = B->k;
  if (nera && B->kind != BC_ALT)
    die("--erasures is supported for bch / alt codes (and grs, concat)");
  if (nerr + nera > n)
    die("too many errors/erasures for n=%d", n);
  uint8_t *msg = malloc((size_t)k), *cw = malloc((size_t)n),
          *rv = malloc((size_t)n), *out = malloc((size_t)n),
          *era = calloc((size_t)n, 1);
  int *ep = malloc(sizeof(int) * (size_t)(nerr + nera + 1));
  Stat st = {0};
  int quiet = trials > 1 && !verbose;
  for (int tr = 0; tr < trials; ++tr) {
    for (int j = 0; j < k; ++j)
      msg[j] = (uint8_t)(rnd() & 1);
    double t0 = now();
    bc_encode(B, msg, cw);
    st.t_enc += now() - t0;
    for (int j = 0; j < k; ++j)
      if (cw[B->info[j]] != msg[j])
        die("internal error: encoder is not systematic on info positions");
    memcpy(rv, cw, (size_t)n);
    memset(era, 0, (size_t)n);
    pick(n, nerr, ep, NULL);
    for (int e = 0; e < nerr; ++e)
      rv[ep[e]] ^= 1;
    int *xp = malloc(sizeof(int) * (size_t)(nera + 1));
    uint8_t *used = calloc((size_t)n, 1);
    for (int e = 0; e < nerr; ++e)
      used[ep[e]] = 1;
    pick(n, nera, xp, used);
    for (int e = 0; e < nera; ++e) {
      era[xp[e]] = 1;
      rv[xp[e]] = 0;
    }
    free(used);
    t0 = now();
    int res = bc_decode(B, rv, nera ? era : NULL, out);
    st.t_dec += now() - t0;
    int cls = res < 0 ? 1 : (memcmp(out, cw, (size_t)n) ? 2 : 0);
    if (cls == 0)
      for (int j = 0; j < k; ++j)
        if (out[B->info[j]] != msg[j])
          cls = 2;
    stat_add(&st, cls);
    if (!quiet) {
      sort_ints(ep, nerr);
      printf("# trial %d: %d errors + %d erasures -> %s", tr + 1, nerr, nera,
             cls_name(cls));
      if (res >= 0)
        printf(", %d bit flips applied", res);
      putchar('\n');
      if (nerr <= 64 && (verbose || trials == 1))
        print_ilist("error positions", ep, nerr);
      if (showv && n <= 512) {
        print_bits("message  ", msg, k);
        print_bits("codeword ", cw, n);
        print_bits("received ", rv, n);
        print_bits("decoded  ", out, n);
      }
    }
    free(xp);
  }
  char what[64];
  snprintf(what, sizeof what, "%d errors%s", nerr, nera ? " + erasures" : "");
  stat_print(&st, what);
}

/* ---- GRS ---- */
static void run_grs(GRS *G, int trials, int nerr, int nera, int verbose,
                    int showv) {
  int n = G->n, k = G->k;
  const GF *F = G->F;
  fe *msg = malloc(sizeof(fe) * (size_t)k), *dm = malloc(sizeof(fe) * (size_t)k),
     *cw = malloc(sizeof(fe) * (size_t)n), *rv = malloc(sizeof(fe) * (size_t)n),
     *out = malloc(sizeof(fe) * (size_t)n);
  uint8_t *era = calloc((size_t)n, 1), *used = calloc((size_t)n, 1);
  int *ep = malloc(sizeof(int) * (size_t)(nerr + 1)),
      *xp = malloc(sizeof(int) * (size_t)(nera + 1));
  fe *ev = malloc(sizeof(fe) * (size_t)(nerr + 1));
  Stat st = {0};
  int quiet = trials > 1 && !verbose;
  if (nerr + nera > n)
    die("too many errors/erasures for n=%d", n);
  for (int tr = 0; tr < trials; ++tr) {
    for (int j = 0; j < k; ++j)
      msg[j] = (fe)(rnd() % (uint64_t)F->size);
    double t0 = now();
    grs_encode(G, msg, cw);
    st.t_enc += now() - t0;
    memcpy(rv, cw, sizeof(fe) * (size_t)n);
    memset(era, 0, (size_t)n);
    memset(used, 0, (size_t)n);
    pick(n, nerr, ep, NULL);
    for (int e = 0; e < nerr; ++e) {
      ev[e] = grand_nz(F);
      rv[ep[e]] ^= ev[e];
      used[ep[e]] = 1;
    }
    pick(n, nera, xp, used);
    for (int e = 0; e < nera; ++e) {
      era[xp[e]] = 1;
      rv[xp[e]] = (fe)(rnd() % (uint64_t)F->size); /* garbage, ignored */
    }
    t0 = now();
    int res = grs_decode(G, rv, nera ? era : NULL, out);
    st.t_dec += now() - t0;
    int cls = res < 0 ? 1 : (memcmp(out, cw, sizeof(fe) * (size_t)n) ? 2 : 0);
    if (cls == 0) {
      grs_message(G, out, dm);
      if (memcmp(dm, msg, sizeof(fe) * (size_t)k))
        cls = 2;
    }
    stat_add(&st, cls);
    if (!quiet) {
      printf("# trial %d: %d errors + %d erasures -> %s", tr + 1, nerr, nera,
             cls_name(cls));
      if (res >= 0)
        printf(", %d error values found", res);
      putchar('\n');
      if (showv) {
        printf("# injected (position:value):");
        for (int e = 0; e < nerr; ++e)
          printf(" %d:%u", ep[e], (unsigned)ev[e]);
        printf("\n# decoded  (position:value):");
        if (res > 0)
          for (int q = 0; q < G->found; ++q)
            printf(" %d:%u", G->pos[q], (unsigned)G->val[q]);
        putchar('\n');
      }
    }
  }
  char what[64];
  snprintf(what, sizeof what, "%d errors + %d erasures", nerr, nera);
  stat_print(&st, what);
}

/* ---- Gabidulin ---- */
static void run_rank(Gab *G, int trials, int nerr, int verbose, int showv) {
  int n = G->n, k = G->k;
  const GF *F = G->F;
  if (nerr > n)
    die("rank weight cannot exceed n");
  fe *msg = malloc(sizeof(fe) * (size_t)k), *dm = malloc(sizeof(fe) * (size_t)k),
     *cw = malloc(sizeof(fe) * (size_t)n), *rv = malloc(sizeof(fe) * (size_t)n),
     *out = malloc(sizeof(fe) * (size_t)n), *e = malloc(sizeof(fe) * (size_t)n);
  Stat st = {0};
  int quiet = trials > 1 && !verbose;
  for (int tr = 0; tr < trials; ++tr) {
    for (int j = 0; j < k; ++j)
      msg[j] = (fe)(rnd() % (uint64_t)F->size);
    double t0 = now();
    gab_encode(G, msg, cw);
    st.t_enc += now() - t0;
    rank_error(F, n, nerr, e);
    for (int j = 0; j < n; ++j)
      rv[j] = cw[j] ^ e[j];
    t0 = now();
    int res = gab_decode(G, rv, out);
    st.t_dec += now() - t0;
    int cls = res < 0 ? 1 : (memcmp(out, cw, sizeof(fe) * (size_t)n) ? 2 : 0);
    if (cls == 0) {
      if (gab_message(G, out, dm) || memcmp(dm, msg, sizeof(fe) * (size_t)k))
        cls = 2;
    }
    stat_add(&st, cls);
    if (!quiet) {
      printf("# trial %d: rank-%d error (rank_weight=%d) -> %s", tr + 1, nerr,
             rank_weight(F, e, n), cls_name(cls));
      if (res >= 0)
        printf(", decoded error has rank %d", res);
      putchar('\n');
      if (showv) {
        printf("# error vector   :");
        for (int j = 0; j < n; ++j)
          printf(" %u", (unsigned)e[j]);
        printf("\n# found (r-e)    :");
        if (res >= 0)
          for (int j = 0; j < n; ++j)
            printf(" %u", (unsigned)(rv[j] ^ out[j]));
        putchar('\n');
      }
    }
  }
  char what[64];
  snprintf(what, sizeof what, "rank-%d errors", nerr);
  stat_print(&st, what);
}

/* ---- product code C1 x C2 : rows are C1 words (length n1), columns C2 ---- */
static void run_product(const BinCode *C1, const BinCode *C2, int trials,
                        int nerr, int iters, int verbose, int showv) {
  int n1 = C1->n, k1 = C1->k, n2 = C2->n, k2 = C2->k, N = n1 * n2;
  if (nerr > N)
    die("too many errors for the %d x %d array", n2, n1);
  uint8_t *msg = malloc((size_t)k1 * k2), *A = malloc((size_t)N),
          *R = malloc((size_t)N), *tmp = malloc((size_t)(n1 > n2 ? n1 : n2)),
          *col = malloc((size_t)n2), *col2 = malloc((size_t)n2),
          *cm = malloc((size_t)k2);
  int *ep = malloc(sizeof(int) * (size_t)(nerr + 1));
  Stat st = {0};
  int quiet = trials > 1 && !verbose;
  for (int tr = 0; tr < trials; ++tr) {
    for (int i = 0; i < k1 * k2; ++i)
      msg[i] = (uint8_t)(rnd() & 1);
    double t0 = now();
    memset(A, 0, (size_t)N);
    for (int a = 0; a < k2; ++a) /* encode the info rows with C1 */
      bc_encode(C1, msg + a * k1, A + C2->info[a] * n1);
    for (int j = 0; j < n1; ++j) { /* encode every column with C2 */
      for (int a = 0; a < k2; ++a)
        cm[a] = A[C2->info[a] * n1 + j];
      bc_encode(C2, cm, col);
      for (int i = 0; i < n2; ++i)
        A[i * n1 + j] = col[i];
    }
    st.t_enc += now() - t0;
    memcpy(R, A, (size_t)N);
    pick(N, nerr, ep, NULL);
    for (int e = 0; e < nerr; ++e)
      R[ep[e]] ^= 1;
    t0 = now();
    int it, bad = 0;
    for (it = 1; it <= iters; ++it) {
      int changed = 0;
      bad = 0;
      for (int i = 0; i < n2; ++i) { /* rows */
        int c = bc_decode(C1, R + i * n1, NULL, tmp);
        if (c < 0)
          ++bad;
        else if (c > 0) {
          memcpy(R + i * n1, tmp, (size_t)n1);
          ++changed;
        }
      }
      for (int j = 0; j < n1; ++j) { /* columns */
        for (int i = 0; i < n2; ++i)
          col[i] = R[i * n1 + j];
        int c = bc_decode(C2, col, NULL, col2);
        if (c < 0)
          ++bad;
        else if (c > 0) {
          for (int i = 0; i < n2; ++i)
            R[i * n1 + j] = col2[i];
          ++changed;
        }
      }
      if (!changed)
        break;
    }
    st.t_dec += now() - t0;
    int cls = bad ? 1 : (memcmp(R, A, (size_t)N) ? 2 : 0);
    if (cls == 0)
      for (int a = 0; a < k2; ++a)
        for (int b = 0; b < k1; ++b)
          if (R[C2->info[a] * n1 + C1->info[b]] != msg[a * k1 + b])
            cls = 2;
    if (bad && !memcmp(R, A, (size_t)N))
      cls = 0; /* all words are fine; "bad" came from an earlier sweep */
    stat_add(&st, cls);
    if (!quiet) {
      printf("# trial %d: %d errors in a %d x %d array -> %s (%d sweep%s)\n",
             tr + 1, nerr, n2, n1, cls_name(cls), it > iters ? iters : it,
             (it > iters ? iters : it) == 1 ? "" : "s");
      if (showv && N <= 1024) {
        int diff = 0;
        for (int i = 0; i < N; ++i)
          diff += R[i] != A[i];
        printf("# residual differing bits: %d\n", diff);
      }
    }
  }
  char what[64];
  snprintf(what, sizeof what, "%d random errors", nerr);
  stat_print(&st, what);
}

/* ---- concatenated code: outer GRS over GF(2^m), inner binary code ---- */
static void run_concat(GRS *G, const BinCode *In, int trials, int nerr,
                       int verbose, int showv) {
  int no = G->n, ko = G->k, m = G->F->m, ni = In->n;
  long N = (long)no * ni;
  if (In->k < m)
    die("inner code has k=%d < m=%d: choose an inner code with k >= m", In->k,
        m);
  if (nerr > N)
    die("too many errors for %ld bits", N);
  fe *msg = malloc(sizeof(fe) * (size_t)ko), *dm = malloc(sizeof(fe) * (size_t)ko),
     *cw = malloc(sizeof(fe) * (size_t)no), *rs = malloc(sizeof(fe) * (size_t)no),
     *os = malloc(sizeof(fe) * (size_t)no);
  uint8_t *bits = malloc((size_t)N), *ib = malloc((size_t)In->k),
          *era = calloc((size_t)no, 1), *dec = malloc((size_t)ni);
  int *ep = malloc(sizeof(int) * (size_t)(nerr + 1));
  Stat st = {0};
  int quiet = trials > 1 && !verbose;
  for (int tr = 0; tr < trials; ++tr) {
    for (int j = 0; j < ko; ++j)
      msg[j] = (fe)(rnd() % (uint64_t)G->F->size);
    double t0 = now();
    grs_encode(G, msg, cw);
    for (int i = 0; i < no; ++i) {
      memset(ib, 0, (size_t)In->k);
      for (int b = 0; b < m; ++b)
        ib[b] = (uint8_t)((cw[i] >> b) & 1);
      bc_encode(In, ib, bits + (long)i * ni);
    }
    st.t_enc += now() - t0;
    pick((int)N, nerr, ep, NULL);
    for (int e = 0; e < nerr; ++e)
      bits[ep[e]] ^= 1;
    t0 = now();
    int nera = 0;
    for (int i = 0; i < no; ++i) {
      int c = bc_decode(In, bits + (long)i * ni, NULL, dec), ok = c >= 0;
      fe sym = 0;
      if (ok) {
        for (int j = 0; j < In->k; ++j) {
          uint8_t v = dec[In->info[j]];
          if (j < m)
            sym |= (fe)(v << j);
          else if (v)
            ok = 0; /* shortened-bit violated: unreliable block */
        }
      }
      era[i] = !ok;
      nera += !ok;
      rs[i] = ok ? sym : 0;
    }
    int res = grs_decode(G, rs, nera ? era : NULL, os);
    st.t_dec += now() - t0;
    int cls = res < 0 ? 1 : (memcmp(os, cw, sizeof(fe) * (size_t)no) ? 2 : 0);
    if (cls == 0) {
      grs_message(G, os, dm);
      if (memcmp(dm, msg, sizeof(fe) * (size_t)ko))
        cls = 2;
    }
    stat_add(&st, cls);
    if (!quiet) {
      printf("# trial %d: %d bit errors -> inner erasures %d of %d blocks -> "
             "%s\n",
             tr + 1, nerr, nera, no, cls_name(cls));
      if (showv && res >= 0)
        printf("# outer decoder located %d symbol positions\n", res);
    }
  }
  char what[64];
  snprintf(what, sizeof what, "%d random bit errors", nerr);
  stat_print(&st, what);
}

/* ================= command line ================= */
static void usage(void) {
  puts(
      "codes [options] [seed]\n"
      "  --code bch|golay|goppa|alt|rm|hadamard|grs|rank|product|concat   (default bch)\n"
      "  --m m           field GF(2^m), m <= 12              (default per code)\n"
      "  --poly 0x43     primitive polynomial of GF(2^m)     (default: "
      "standard)\n"
      "  --len n         code length (bch: also divisors of 2^m-1 => cyclic; "
      "goppa/alt/grs/rank)\n"
      "  --k k           dimension (grs, rank, concat outer code)\n"
      "  --t t           correction capability (bch, goppa = deg g, alt)\n"
      "  --r r           Reed-Muller order: RM(r,m), length 2^m     (default 2)\n"
      "  --b b           first zero beta^b of the BCH code   (default 1)\n"
      "  --ext           golay: extended [24,12,8] code\n"
      "  --errors e      injected errors (bits / symbols / rank / total bits)\n"
      "                  default: the guaranteed capability of the code\n"
      "  --erasures s    injected erasures (bch, alt, grs)\n"
      "  --c1 spec --c2 spec   product code components (default bch:5:2 and "
      "c1)\n"
      "  --inner spec    concat: inner binary code             (default "
      "golay)\n"
      "        specs:  bch:m:t[:n[:b]]  golay  golay24  goppa:m:t[:n]  "
      "alt:m:n:t  rm:r:m  had:m\n"
      "  --iters N       product: maximal row/column sweeps  (default 8)\n"
      "  -fht            RM(1,m): ML decoding by the fast Walsh-Hadamard "
      "transform\n"
      "  -shuffle        grs: random order of the evaluation points\n"
      "  -random-v       grs: random column multipliers (true GRS, not RS)\n"
      "  -n N            N random trials (summary only)       -v  every trial\n"
      "  -show-values    print vectors / error values\n"
      "  -list           only list the code parameters and exit\n"
      "examples:\n"
      "  codes --code bch --m 6 --t 3 --errors 3\n"
      "  codes --code rm --r 2 --m 6 --errors 7 -n 200\n"
      "  codes --code golay --ext --errors 3 -n 1000\n"
      "  codes --code goppa --m 8 --t 10 --errors 10 -n 20\n"
      "  codes --code grs --m 8 --len 255 --k 223 --errors 10 --erasures 12\n"
      "  codes --code rank --m 8 --len 8 --k 4 --errors 2\n"
      "  codes --code product --c1 bch:5:2 --c2 golay --errors 8\n"
      "  codes --code concat --m 12 --len 100 --k 60 --inner golay --errors "
      "100");
}
static int flag(const char *a, const char *name) {
  return a[0] == '-' && (!strcmp(a + 1, name) || (a[1] == '-' && !strcmp(a + 2, name)));
}

int codes_run(int argc, char **argv) {
  const char *code = "bch", *c1 = "bch:5:2", *c2 = NULL, *inner = "golay";
  int m = 0, len = -1, k = -1, t = -1, b = 1, nerr = -1, nera = 0, trials = 1,
      verbose = 0, showv = 0, only_list = 0, iters = 8, ext = 0, shuffle = 0,
      randv = 0, rmr = 2;
  unsigned poly = 0, seed = 1;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--code") && i + 1 < argc)
      code = argv[++i];
    else if (!strcmp(argv[i], "--m") && i + 1 < argc)
      m = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--poly") && i + 1 < argc)
      poly = (unsigned)strtoul(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "--len") && i + 1 < argc)
      len = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--k") && i + 1 < argc)
      k = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--t") && i + 1 < argc)
      t = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--r") && i + 1 < argc)
      rmr = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--b") && i + 1 < argc)
      b = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--errors") && i + 1 < argc)
      nerr = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--erasures") && i + 1 < argc)
      nera = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--c1") && i + 1 < argc)
      c1 = argv[++i];
    else if (!strcmp(argv[i], "--c2") && i + 1 < argc)
      c2 = argv[++i];
    else if (!strcmp(argv[i], "--inner") && i + 1 < argc)
      inner = argv[++i];
    else if (!strcmp(argv[i], "--iters") && i + 1 < argc)
      iters = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-n") && i + 1 < argc)
      trials = atoi(argv[++i]);
    else if (flag(argv[i], "fht"))
      g_fht = 1;
    else if (flag(argv[i], "ext"))
      ext = 1;
    else if (flag(argv[i], "shuffle"))
      shuffle = 1;
    else if (flag(argv[i], "random-v"))
      randv = 1;
    else if (flag(argv[i], "v"))
      verbose = 1;
    else if (flag(argv[i], "show-values"))
      showv = 1;
    else if (flag(argv[i], "list"))
      only_list = 1;
    else if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage();
      return 0;
    } else if (argv[i][0] == '-') {
      fprintf(stderr, "unknown option: %s  (see --help)\n", argv[i]);
      return 1;
    } else
      seed = (unsigned)strtoul(argv[i], NULL, 10);
  }
  if (trials < 1)
    trials = 1;
  rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
  for (int i = 0; i < 8; ++i)
    (void)rnd();

  if (!strcmp(code, "bch") || !strcmp(code, "alt") || !strcmp(code, "goppa") ||
      !strcmp(code, "golay") ||
      !strcmp(code, "rm") || !strcmp(code, "hadamard")) {
    BinCode *B;
    char spec[64];
    if (!strcmp(code, "golay"))
      B = bc_golay(ext);
    else if (!strcmp(code, "hadamard"))
      B = bc_had(m ? m : 6);
    else if (!strcmp(code, "rm"))
      B = bc_rm(rmr, m ? m : 5);
    else {
      int mm = m ? m : (!strcmp(code, "goppa") ? 8 : 6);
      int tt = t > 0 ? t : (!strcmp(code, "goppa") ? 10 : 3);
      if (!strcmp(code, "bch"))
        snprintf(spec, sizeof spec, "bch:%d:%d:%d:%d", mm, tt, len > 0 ? len : 0, b);
      else if (!strcmp(code, "goppa"))
        snprintf(spec, sizeof spec, "goppa:%d:%d:%d", mm, tt, len > 0 ? len : 0);
      else
        snprintf(spec, sizeof spec, "alt:%d:%d:%d", mm, len > 0 ? len : (1 << mm) - 1, tt);
      B = bc_parse(spec, poly);
    }
    if (nerr < 0)
      nerr = B->t;
    printf("# code: %s, dimension k=%d, corrects t=%d errors%s\n", B->name,
           B->k, B->t, B->kind == BC_ALT ? " (+ erasures: 2e+s <= 2t)" : "");
    if (only_list)
      return 0;
    run_bincode(B, trials, nerr, nera, verbose, showv);
    return 0;
  }
  if (!strcmp(code, "grs")) {
    int mm = m ? m : 8;
    GF *F = gf_new(mm, poly);
    int n = len > 0 ? len : F->ord, kk = k > 0 ? k : n - 32 > 0 ? n - 32 : n / 2;
    GRS *G = grs_new(F, n, kk, shuffle, randv);
    if (nerr < 0)
      nerr = (n - kk) / 2;
    printf("# code: %s [%d,%d,%d] over GF(2^%d), corrects e errors + s "
           "erasures with 2e+s <= %d\n",
           randv ? "GRS" : "RS", n, kk, n - kk + 1, mm, n - kk);
    if (only_list)
      return 0;
    run_grs(G, trials, nerr, nera, verbose, showv);
    return 0;
  }
  if (!strcmp(code, "rank")) {
    int mm = m ? m : 8;
    GF *F = gf_new(mm, poly);
    int n = len > 0 ? len : mm, kk = k > 0 ? k : n / 2;
    Gab *G = gab_new(F, n, kk);
    if (nerr < 0)
      nerr = (n - kk) / 2;
    printf("# code: Gabidulin [%d,%d,%d] rank-metric over GF(2^%d), corrects "
           "t=%d rank errors\n",
           n, kk, n - kk + 1, mm, (n - kk) / 2);
    if (only_list)
      return 0;
    run_rank(G, trials, nerr, verbose, showv);
    return 0;
  }
  if (!strcmp(code, "product")) {
    BinCode *A = bc_parse(c1, poly), *B2c = bc_parse(c2 ? c2 : c1, poly);
    if (nerr < 0)
      nerr = (A->dmin * B2c->dmin - 1) / 2 < 8 ? (A->dmin * B2c->dmin - 1) / 2 : 8;
    printf("# product code: C1 = %s (rows)  x  C2 = %s (columns)\n", A->name,
           B2c->name);
    printf("# length %d x %d = %d, dimension %d x %d = %d, d >= %d, "
           "guaranteed ML radius %d\n",
           B2c->n, A->n, A->n * B2c->n, B2c->k, A->k, A->k * B2c->k,
           A->dmin * B2c->dmin, (A->dmin * B2c->dmin - 1) / 2);
    if (only_list)
      return 0;
    run_product(A, B2c, trials, nerr, iters, verbose, showv);
    return 0;
  }
  if (!strcmp(code, "concat")) {
    int mm = m ? m : 12;
    GF *F = gf_new(mm, poly);
    BinCode *In = bc_parse(inner, poly);
    int no = len > 0 ? len : 100, ko = k > 0 ? k : no * 3 / 5;
    GRS *G = grs_new(F, no, ko, shuffle, randv);
    if (nerr < 0)
      nerr = In->t * ((no - ko) / 2 + 1);
    printf("# concatenated code: outer %s[%d,%d,%d] over GF(2^%d)  o  inner "
           "%s (k_in=%d, %d message bits per symbol)\n",
           randv ? "GRS" : "RS", no, ko, no - ko + 1, mm, In->name, In->k, mm);
    printf("# binary length %d, binary dimension %d, d >= %d\n", no * In->n,
           ko * mm, (no - ko + 1) * In->dmin);
    if (only_list)
      return 0;
    run_concat(G, In, trials, nerr, verbose, showv);
    return 0;
  }
  fprintf(stderr, "unknown code '%s' (see --help)\n", code);
  return 1;
}

#ifndef CODES_NO_MAIN
int main(int argc, char **argv) { return codes_run(argc, argv); }
#endif