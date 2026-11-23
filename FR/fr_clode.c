/* standalone test of fr_vote.inc on the Hermitian curve y^q+y = x^(q+1), q=4,
 * GF(16) */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef uint16_t fe;
#define MAXB 200
#define MAXT 64
#define SGMAX 400
static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}
static int FM, FS, FO;
static fe *gexp, *glog;
static int gf_init(int m, unsigned poly) {
  FM = m;
  FS = 1 << m;
  FO = FS - 1;
  gexp = malloc(sizeof(fe) * (2 * FO + 4));
  glog = malloc(sizeof(fe) * FS);
  unsigned x = 1;
  for (int i = 0; i < FO; ++i) {
    gexp[i] = x;
    glog[x] = i;
    x <<= 1;
    if (x & (unsigned)FS)
      x ^= poly;
  }
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
  return gexp[(int)(((long long)glog[a] * e) % FO)];
}

typedef struct {
  int rho;
  fe *val;
} Basis;
static Basis basis[MAXB];
static int nbasis;
static int in_H[SGMAX], idx_of_ord[SGMAX];
static int M_SYND, M_EXT, GENUS, npts, NUM_ERRORS;
static fe *PX, *PY;
static const fe *recv;
static int *nz_idx;
static int nz_cnt;
static int use_poly = 1;
static int *bas_ei, *bas_ej;

typedef struct {
  int T, nfound, resolved, overflow, failed;
  int pos[MAXT + 1];
  fe val[MAXT + 1];
  uint8_t rowset[SGMAX], colset[SGMAX];
  int vote_steps, vote_wrong, vote_tie, vote_min_margin;
  double t_main, t_extract, t_resolve;
} Result;

static int count_basis_upto(int rho) {
  int n = 0;
  for (int i = 0; i < nbasis; ++i)
    if (basis[i].rho <= rho)
      ++n;
  return n;
}
static fe synd1(int ia) {
  fe acc = 0;
  for (int n = 0; n < nz_cnt; ++n)
    acc ^= mul(recv[nz_idx[n]], basis[ia].val[nz_idx[n]]);
  return acc;
}
static fe true_syndrome(int n) {
  const fe *ph = basis[idx_of_ord[n]].val;
  fe acc = 0;
  for (int i = 0; i < nz_cnt; ++i)
    acc ^= mul(recv[nz_idx[i]], ph[nz_idx[i]]);
  return acc;
}
static fe aug[MAXB][MAXT + 2];
static fe err_val[MAXT + 1];
static int resolve_by_values(int *found, int *nfound) {
  int n = *nfound, m = count_basis_upto(M_SYND);
  if (n > MAXT)
    return 0;
  for (int a = 0; a < m; ++a) {
    for (int k = 0; k < n; ++k)
      aug[a][k] = basis[a].val[found[k]];
    aug[a][n] = synd1(a);
  }
  for (int c = 0; c < n; ++c) {
    int p = -1;
    for (int a = c; a < m; ++a)
      if (aug[a][c]) {
        p = a;
        break;
      }
    if (p < 0)
      return 0;
    if (p != c)
      for (int k = 0; k <= n; ++k) {
        fe t = aug[p][k];
        aug[p][k] = aug[c][k];
        aug[c][k] = t;
      }
    fe iv = inv(aug[c][c]);
    for (int k = c; k <= n; ++k)
      aug[c][k] = mul(aug[c][k], iv);
    for (int a = 0; a < m; ++a) {
      fe f = aug[a][c];
      if (a == c || !f)
        continue;
      for (int k = c; k <= n; ++k)
        aug[a][k] ^= mul(f, aug[c][k]);
    }
  }
  for (int a = n; a < m; ++a)
    if (aug[a][n])
      return 0;
  int keep = 0;
  for (int k = 0; k < n; ++k)
    if (aug[k][n]) {
      found[keep] = found[k];
      err_val[keep] = aug[k][n];
      ++keep;
    }
  *nfound = keep;
  return 1;
}
static void resolve_and_store(Result *R) {
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
}

/* ---- monomial tables for y^4 = y + x^5 (cone i,j>=0, weight 4i+5j) ---- */
static int NPT, *pp_i, *pp_j, *pp_w, *pp_q, *pp_low, *pp_dep, *pp_ws, *pp_we,
    pp_bw, pp_bh, *pp_box;
static fe *pp_S, *pp_lam, *pp_K;
static inline int pp_at(int i, int j) {
  if (i < 0 || j < 0 || i >= pp_bw || j >= pp_bh)
    return -1;
  return pp_box[i * pp_bh + j];
}
typedef struct {
  int i, j, w;
} PP;
static int cmpp(const void *a, const void *b) {
  const PP *x = a, *y = b;
  if (x->w != y->w)
    return x->w - y->w;
  return x->j - y->j;
}
static void poly_setup(int Mx) {
  int cap = 0;
  PP *P = malloc(sizeof(PP) * 100000);
  for (int i = 0; 4 * i <= Mx; ++i)
    for (int j = 0; 4 * i + 5 * j <= Mx; ++j) {
      P[cap].i = i;
      P[cap].j = j;
      P[cap].w = 4 * i + 5 * j;
      cap++;
    }
  qsort(P, cap, sizeof(PP), cmpp);
  NPT = cap;
  pp_i = malloc(4 * NPT);
  pp_j = malloc(4 * NPT);
  pp_w = malloc(4 * NPT);
  pp_q = malloc(4 * NPT);
  pp_low = malloc(4 * NPT);
  pp_dep = malloc(4 * NPT);
  pp_bw = Mx / 4 + 2;
  pp_bh = Mx / 5 + 2;
  pp_box = malloc(4 * pp_bw * pp_bh);
  for (int x = 0; x < pp_bw * pp_bh; ++x)
    pp_box[x] = -1;
  for (int p = 0; p < NPT; ++p) {
    pp_i[p] = P[p].i;
    pp_j[p] = P[p].j;
    pp_w[p] = P[p].w;
    pp_box[P[p].i * pp_bh + P[p].j] = p;
  }
  pp_ws = calloc(Mx + 2, 4);
  pp_we = calloc(Mx + 2, 4);
  for (int p = 0; p < NPT; ++p) {
    int w = pp_w[p];
    if (pp_ws[w] == 0 && pp_we[w] == 0)
      pp_ws[w] = p;
    pp_we[w] = p + 1;
    pp_dep[p] = pp_j[p] >= 4;
    if (pp_dep[p]) {
      pp_q[p] = pp_at(pp_i[p] + 5, pp_j[p] - 4);
      pp_low[p] = pp_at(pp_i[p], pp_j[p] - 3);
    }
  }
  pp_S = calloc(NPT, sizeof(fe));
  pp_lam = calloc(NPT, sizeof(fe));
  pp_K = calloc(NPT, sizeof(fe));
}
static void poly_syndromes(void) {
  for (int p = 0; p < NPT; ++p) {
    if (pp_w[p] > M_SYND) {
      pp_S[p] = 0;
      continue;
    }
    fe acc = 0;
    for (int z = 0; z < nz_cnt; ++z) {
      int k = nz_idx[z];
      acc ^= mul(recv[k], mul(gpow(PX[k], pp_i[p]), gpow(PY[k], pp_j[p])));
    }
    pp_S[p] = acc;
  }
}
static void poly_prepare(int n) {
  for (int p = pp_ws[n]; p < pp_we[n]; ++p) {
    if (!pp_dep[p]) {
      pp_lam[p] = 1;
      pp_K[p] = 0;
    } else {
      int q = pp_q[p];
      pp_lam[p] = pp_lam[q];
      pp_K[p] = pp_K[q] ^ pp_S[pp_low[p]];
    }
  }
}
static void poly_finalize(int n, fe x) {
  for (int p = pp_ws[n]; p < pp_we[n]; ++p)
    pp_S[p] = mul(pp_lam[p], x) ^ pp_K[p];
}

#include "fr_vote.inc"

static uint64_t rng = 88172645463325252ULL;
static uint64_t rnd(void) {
  rng ^= rng << 13;
  rng ^= rng >> 7;
  rng ^= rng << 17;
  return rng;
}
static int true_pos[MAXT];
static fe true_val[MAXT];

int main(int argc, char **argv) {
  int M = argc > 1 ? atoi(argv[1]) : 56, t = argc > 2 ? atoi(argv[2]) : 10,
      trials = argc > 3 ? atoi(argv[3]) : 20;
  if (argc > 4)
    rng ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL;
  gf_init(4, 0x13);
  GENUS = 6;
  M_SYND = M;
  M_EXT = M + GENUS;
  NUM_ERRORS = t;
  PX = malloc(sizeof(fe) * 64);
  PY = malloc(sizeof(fe) * 64);
  npts = 0;
  for (int x = 0; x < 16; ++x)
    for (int y = 0; y < 16; ++y)
      if ((gpow(y, 4) ^ y) == gpow(x, 5)) {
        PX[npts] = x;
        PY[npts] = y;
        npts++;
      }
  printf("n=%d points, M=%d, g=%d, t=%d (basic bound %d, voting bound %d)\n",
         npts, M, GENUS, t, (M - 3 * GENUS + 1) / 2, (M - 2 * GENUS + 1) / 2);
  /* basis x^i y^j, j<4, rho=4i+5j <= M+g */
  int cnt = 0;
  int ri[MAXB], rj[MAXB], rr[MAXB];
  for (int j = 0; j < 4; ++j)
    for (int i = 0; 4 * i + 5 * j <= M_EXT; ++i) {
      ri[cnt] = i;
      rj[cnt] = j;
      rr[cnt] = 4 * i + 5 * j;
      cnt++;
    }
  for (int a = 1; a < cnt; ++a) {
    int x = a;
    while (x > 0 && rr[x - 1] > rr[x]) {
      int t1 = rr[x];
      rr[x] = rr[x - 1];
      rr[x - 1] = t1;
      t1 = ri[x];
      ri[x] = ri[x - 1];
      ri[x - 1] = t1;
      t1 = rj[x];
      rj[x] = rj[x - 1];
      rj[x - 1] = t1;
      x--;
    }
  }
  nbasis = cnt;
  bas_ei = malloc(4 * cnt);
  bas_ej = malloc(4 * cnt);
  for (int x = 0; x < SGMAX; ++x) {
    in_H[x] = x > M_EXT;
    idx_of_ord[x] = -1;
  }
  for (int a = 0; a < cnt; ++a) {
    basis[a].rho = rr[a];
    bas_ei[a] = ri[a];
    bas_ej[a] = rj[a];
    in_H[rr[a]] = 1;
    idx_of_ord[rr[a]] = a;
    basis[a].val = malloc(sizeof(fe) * npts);
    for (int k = 0; k < npts; ++k)
      basis[a].val[k] = mul(gpow(PX[k], ri[a]), gpow(PY[k], rj[a]));
  }
  printf("basis size %d (expect M+g+1-g = %d)\n", cnt, M + 1);
  poly_setup(M_EXT);
  nz_idx = malloc(4 * npts);
  fe *r = malloc(sizeof(fe) * npts);
  int ok = 0, wrongvotes = 0;
  for (int tr = 0; tr < trials; ++tr) {
    memset(r, 0, sizeof(fe) * npts);
    for (int e = 0; e < t; ++e) {
      int p, dup;
      do {
        p = rnd() % npts;
        dup = 0;
        for (int k = 0; k < e; ++k)
          if (true_pos[k] == p)
            dup = 1;
      } while (dup);
      true_pos[e] = p;
      do {
        r[p] = rnd() % FS;
      } while (!r[p]);
      true_val[e] = r[p];
    }
    recv = r;
    nz_cnt = 0;
    for (int k = 0; k < npts; ++k)
      if (r[k])
        nz_idx[nz_cnt++] = k;
    poly_syndromes();
    Result res;
    int rc = decode_fr_vote(&res, 0, 1);
    int same = 0;
    if (!res.failed)
      for (int m = 0; m < res.nfound; ++m)
        for (int e = 0; e < t; ++e)
          if (true_pos[e] == res.pos[m] && true_val[e] == res.val[m])
            ++same;
    int good = !res.failed && !res.overflow && res.resolved &&
               res.nfound == t && same == t;
    ok += good;
    wrongvotes += res.vote_wrong;
    if (trials <= 3 || !good)
      printf(" trial %d: rc=%d T=%d found=%d same=%d wrong_votes=%d "
             "minmargin=%d -> %s\n",
             tr, rc, res.T, res.nfound, same, res.vote_wrong,
             res.vote_steps ? res.vote_min_margin : 0, good ? "OK" : "FAIL");
  }
  printf("RESULT: %d/%d decoded, total wrong votes %d\n", ok, trials,
         wrongvotes);
  return 0;
}