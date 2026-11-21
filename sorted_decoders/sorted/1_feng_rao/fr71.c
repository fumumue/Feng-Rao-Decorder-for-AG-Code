/*
 * bbgs_toric_fr.c -- GF(2^m) 上の BBGS 曲線
 *   X^(q^2) + Y + X^(q^2-1)Y^q + X^(q^2-q)Y^(q^2) = 0
 * の Feng-Rao(多数決)復号器。bbgs_toric.c の基本アルゴリズム版に FR
 * を追加したもの。
 *
 *   ・Newton 多角形から関数空間の基底を構成（局所展開・solve_L は使わない）
 *   ・パリティ検査行列は作らず、誤り位置と誤り値からシンドロームを計算
 *   ・既定は FR: 単項式順序 (qi+j, i)
 * の辞書式順序で行を並べ、シンドローム行列に Sakata
 * 型の逐次ガウス消去をかける。未知のシンドローム S(c) は (1) 曲線の式 F
 * が与える関係式 T(c)=T(c+(-q^2,1))+T(c+(-1,q))+T(c+(-q,q^2))
 * で決まるならそれを使い、 (2) 決まらなければ、"well-behaved" な対 (u,w) (行 u
 * が未ピボット・列 w が未使用) による多数決で決める。 ・--basic
 * で従来の基本アルゴリズム(核法)に切り替え
 *   ・どちらの方式も、復元した誤りから全シンドロームを再計算して照合するので、成功と表示されたら本物。
 *
 * F の Newton 多角形は (0,1), (q^2,0), (q^2-q,q^2) を頂点とする三角形。
 *   E0: 原点            v(x^i y^j) = i + q^2 j
 *   E1: 次数 q の無限遠 v(x^i y^j) = -q i - j
 *   E2: q-1 個の無限遠有理点  v(x^i y^j) = (q+1)i - qj
 * Delta(a,b) = { qi+j <= a, qj-(q+1)i <= b, i+q^2 j >= 0 }。
 *
 * ビルド: cc -O2 -std=gnu11 -o bbgs_toric_fr bbgs_toric_fr.c
 * 実行  : ./bbgs_toric_fr [--m 9] [--q 8] [--errors 256] [--len 8192] [--a A
 * --b B]
 *                         [--pa PA --pb PB] [--basic] [--seed s] [--mem MB]
 * [--force] [--dump]
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
typedef uint16_t fe;

/* ---------------- GF(2^m) の演算（m <= 11） ---------------- */
static int FM, FS, FO;
static fe *gexp, *glog;
static int gf_init(int m, unsigned poly) {
  FM = m;
  FS = 1 << m;
  FO = FS - 1;
  gexp = malloc(sizeof(fe) * (2 * FO + 4));
  glog = malloc(sizeof(fe) * FS);
  unsigned x = 1;
  for (int i = 0; i < FO; i++) {
    if (i > 0 && x == 1)
      return -1;
    gexp[i] = x;
    glog[x] = i;
    x <<= 1;
    if (x & FS)
      x ^= poly;
  }
  if (x != 1)
    return -1;
  for (int i = FO; i < 2 * FO + 4; i++)
    gexp[i] = gexp[i - FO];
  glog[0] = 0;
  return 0;
}
static inline fe mul(fe a, fe b) {
  return (a && b) ? gexp[glog[a] + glog[b]] : 0;
}
static inline fe inv(fe a) { return gexp[FO - glog[a]]; }
static inline fe monval(int lx, int ly, int i, int j) {
  long long e = ((long long)i * lx + (long long)j * ly) % FO;
  if (e < 0)
    e += FO;
  return gexp[e];
}
static double mem_mb_opt = 0;
static int dump_all = 0;
static double mem_limit_bytes(void) {
  if (mem_mb_opt > 0)
    return mem_mb_opt * 1048576.0;
  double avail = 0;
  FILE *f = fopen("/proc/meminfo", "r");
  if (f) {
    char l[256];
    while (fgets(l, sizeof l, f)) {
      long long kb;
      if (sscanf(l, "MemAvailable: %lld kB", &kb) == 1) {
        avail = kb * 1024.0;
        break;
      }
    }
    fclose(f);
  }
  if (avail <= 0) {
    long pg = sysconf(_SC_AVPHYS_PAGES), ps = sysconf(_SC_PAGESIZE);
    if (pg > 0 && ps > 0)
      avail = (double)pg * ps;
  }
  if (avail <= 0)
    avail = 2e9;
  return 0.7 * avail;
}
static int mem_check(const char *what, double need) {
  double lim = mem_limit_bytes();
  if (need <= lim)
    return 1;
  fprintf(stderr,
          "warning: %s needs %.0f MB > memory budget %.0f MB: search cut off\n",
          what, need / 1048576.0, lim / 1048576.0);
  return 0;
}
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + 1e-9 * t.tv_nsec;
}
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
  rs ^= rs << 13;
  rs ^= rs >> 7;
  rs ^= rs << 17;
  return rs;
}

/* ---------------- Newton 多角形による基底構成 ---------------- */
static int Q, QQ;
static int fdiv_(int a, int b) {
  int d = a / b;
  if ((a % b != 0) && ((a < 0) != (b < 0)))
    d--;
  return d;
}
static int cdiv_(int a, int b) { return -fdiv_(-a, b); }
static int jrange(int A1, int A2, int A0, int i, int *lo, int *hi) {
  *lo = cdiv_(A0 - i, QQ);
  int h1 = A1 - Q * i, h2 = fdiv_(A2 + (Q + 1) * i, Q);
  *hi = h1 < h2 ? h1 : h2;
  return *hi >= *lo;
}
typedef struct {
  int a, b, n, nind;
  int *pi, *pj;
  char *ind;
  int imin, imax, jmin, jmax;
} Poly;
static int inH(int a, int b, int hi, int hj) {
  return Q * hi + hj <= a - Q * QQ && Q * hj - (Q + 1) * hi <= b - Q &&
         hi + QQ * hj >= -QQ;
}
static void poly_build(Poly *P, int a, int b) {
  P->a = a;
  P->b = b;
  int cnt = 0, i0 = -(b + Q + 5),
      i1 = (int)((long long)a * QQ / ((long long)Q * QQ - 1)) + 3;
  P->imin = 1 << 30;
  P->imax = -(1 << 30);
  P->jmin = 1 << 30;
  P->jmax = -(1 << 30);
  for (int pass = 0; pass < 2; pass++) {
    int k = 0;
    for (int i = i0; i <= i1; i++) {
      int lo, hi;
      if (!jrange(a, b, 0, i, &lo, &hi))
        continue;
      for (int j = lo; j <= hi; j++) {
        if (pass == 1) {
          P->pi[k] = i;
          P->pj[k] = j;
          P->ind[k] = !inH(a, b, i - QQ, j);
        }
        k++;
      }
      if (pass == 0) {
        if (i < P->imin)
          P->imin = i;
        if (i > P->imax)
          P->imax = i;
        if (lo < P->jmin)
          P->jmin = lo;
        if (hi > P->jmax)
          P->jmax = hi;
      }
    }
    if (pass == 0) {
      cnt = k;
      P->n = cnt;
      P->pi = malloc(sizeof(int) * (cnt + 1));
      P->pj = malloc(sizeof(int) * (cnt + 1));
      P->ind = malloc(cnt + 1);
    }
  }
  P->nind = 0;
  for (int k = 0; k < P->n; k++)
    P->nind += P->ind[k];
}

/* ---------------- 曲線上の点（原点を除外し、x,y はともに非零）
 * ---------------- */
static int npts;
static fe *PX, *PY;
static int *LX, *LY;
static void enumerate_points(int len) {
  int cap = 1 << 16;
  npts = 0;
  PX = malloc(sizeof(fe) * cap);
  PY = malloc(sizeof(fe) * cap);
  for (int x = 1; x < FS; x++) {
    int lx = glog[x];
    for (int y = 1; y < FS; y++) {
      int ly = glog[y];
      fe s = gexp[(QQ * lx) % FO];
      s ^= y;
      s ^= gexp[(((long long)(QQ - 1) * lx + (long long)Q * ly) % FO)];
      s ^= gexp[(((long long)(QQ - Q) * lx + (long long)QQ * ly) % FO)];
      if (!s) {
        if (npts == cap) {
          cap *= 2;
          PX = realloc(PX, sizeof(fe) * cap);
          PY = realloc(PY, sizeof(fe) * cap);
        }
        PX[npts] = x;
        PY[npts] = y;
        npts++;
        if (len > 0 && npts >= len)
          goto done;
      }
    }
  }
done:
  LX = malloc(sizeof(int) * npts);
  LY = malloc(sizeof(int) * npts);
  for (int k = 0; k < npts; k++) {
    LX[k] = glog[PX[k]];
    LY[k] = glog[PY[k]];
  }
}

/* ---------------- Delta(G) 上のシンドローム表 ---------------- */
typedef struct {
  Poly *G;
  int W;
  fe *T;
} Tab;
static inline fe *Tp(const Tab *S, int i, int j) {
  return &S->T[(size_t)(i - S->G->imin) * S->W + (j - S->G->jmin)];
}
static void syndrome_table(const Tab *S, const int *pos, const fe *val, int t) {
  memset(S->T, 0, sizeof(fe) * (size_t)(S->G->imax - S->G->imin + 1) * S->W);
  for (int u = 0; u < t; u++) {
    int k = pos[u];
    int le = glog[val[u]];
    for (int p = 0; p < S->G->n; p++) {
      long long ex = ((long long)S->G->pi[p] * LX[k] +
                      (long long)S->G->pj[p] * LY[k] + le) %
                     FO;
      if (ex < 0)
        ex += FO;
      *Tp(S, S->G->pi[p], S->G->pj[p]) ^= gexp[ex];
    }
  }
}
/* 独立成分から従属成分を復元する。F*x^h=0 */
static void syndrome_extend(const Tab *S) {
  const int vi[3] = {0, QQ - 1, QQ - Q};
  const int vj[3] = {1, Q, QQ};
  for (int p = 0; p < S->G->n; p++)
    if (!S->G->ind[p]) {
      int hi = S->G->pi[p] - QQ, hj = S->G->pj[p];
      fe acc = 0;
      for (int v = 0; v < 3; v++)
        acc ^= *Tp(S, hi + vi[v], hj + vj[v]);
      *Tp(S, S->G->pi[p], S->G->pj[p]) = acc;
    }
}

/* ---------------- 線形代数 ---------------- */
static int nullspace(fe *A, int R, int C, fe **out) {
  int *pc = malloc(sizeof(int) * (C + 1)), rk = 0,
      *lr = malloc(sizeof(int) * C);
  for (int c = 0; c < C && rk < R; c++) {
    int p = rk;
    while (p < R && !A[(size_t)p * C + c])
      p++;
    if (p == R)
      continue;
    if (p != rk)
      for (int k = 0; k < C; k++) {
        fe t = A[(size_t)p * C + k];
        A[(size_t)p * C + k] = A[(size_t)rk * C + k];
        A[(size_t)rk * C + k] = t;
      }
    fe *Rw = A + (size_t)rk * C;
    fe iv = inv(Rw[c]);
    for (int k = c; k < C; k++)
      Rw[k] = mul(Rw[k], iv);
    for (int k = c; k < C; k++)
      lr[k] = Rw[k] ? glog[Rw[k]] : -1;
    for (int r2 = 0; r2 < R; r2++) {
      if (r2 == rk)
        continue;
      fe *D = A + (size_t)r2 * C;
      fe f = D[c];
      if (!f)
        continue;
      int lf = glog[f];
      for (int k = c; k < C; k++)
        if (lr[k] >= 0)
          D[k] ^= gexp[lf + lr[k]];
    }
    pc[rk++] = c;
  }
  char *isp = calloc(C, 1);
  for (int i = 0; i < rk; i++)
    isp[pc[i]] = 1;
  int kd = C - rk;
  fe *B = calloc((size_t)(kd ? kd : 1) * C, sizeof(fe));
  int bi = 0;
  for (int f = 0; f < C; f++) {
    if (isp[f])
      continue;
    fe *x = B + (size_t)bi * C;
    x[f] = 1;
    for (int i = 0; i < rk; i++)
      x[pc[i]] = A[(size_t)i * C + f];
    bi++;
  }
  free(pc);
  free(lr);
  free(isp);
  *out = B;
  return kd;
}
/* 候補点集合 Z 上の誤り値を求める。Delta(G) の独立な全 (i,j) で Σ_z e_z x_z^i
 * y_z^j=T(i,j) を解く */
static int values_from_syndrome(const Tab *S, const int *Z, int nz, int *pos,
                                fe *val) {
  if (nz == 0)
    return 0;
  Poly *G = S->G;
  int nr = G->nind, W = nz + 1;
  if (nz > nr)
    return -1;
  if (!mem_check("value system", (double)nr * W * sizeof(fe)))
    return -1;
  fe *B = malloc(sizeof(fe) * (size_t)nr * W);
  int r = 0;
  for (int p = 0; p < G->n; p++)
    if (G->ind[p]) {
      for (int c = 0; c < nz; c++)
        B[(size_t)r * W + c] = monval(LX[Z[c]], LY[Z[c]], G->pi[p], G->pj[p]);
      B[(size_t)r * W + nz] = *Tp(S, G->pi[p], G->pj[p]);
      r++;
    }
  int *lr = malloc(sizeof(int) * W), ok = 1;
  for (int c = 0; c < nz && ok; c++) {
    int p = c;
    while (p < nr && !B[(size_t)p * W + c])
      p++;
    if (p == nr) {
      ok = 0;
      break;
    }
    if (p != c)
      for (int k = 0; k < W; k++) {
        fe t = B[(size_t)p * W + k];
        B[(size_t)p * W + k] = B[(size_t)c * W + k];
        B[(size_t)c * W + k] = t;
      }
    fe *Rw = B + (size_t)c * W;
    fe iv = inv(Rw[c]);
    for (int k = c; k < W; k++)
      Rw[k] = mul(Rw[k], iv);
    for (int k = c; k < W; k++)
      lr[k] = Rw[k] ? glog[Rw[k]] : -1;
    for (int r2 = 0; r2 < nr; r2++) {
      if (r2 == c)
        continue;
      fe *D = B + (size_t)r2 * W;
      fe f = D[c];
      if (!f)
        continue;
      int lf = glog[f];
      for (int k = c; k < W; k++)
        if (lr[k] >= 0)
          D[k] ^= gexp[lf + lr[k]];
    }
  }
  int cnt = -1;
  if (ok)
    for (int r2 = nz; r2 < nr; r2++)
      if (B[(size_t)r2 * W + nz])
        ok = 0;
  if (ok) {
    cnt = 0;
    for (int c = 0; c < nz; c++) {
      fe v = B[(size_t)c * W + nz];
      if (v) {
        pos[cnt] = Z[c];
        val[cnt] = v;
        cnt++;
      }
    }
  }
  free(B);
  free(lr);
  return cnt;
}

/* ---------------- 診断情報の表示 ---------------- */
typedef struct {
  int pos;
  fe val;
} ErrorEntry;
static int compare_error_entry(const void *a, const void *b) {
  const ErrorEntry *x = a, *y = b;
  return (x->pos > y->pos) - (x->pos < y->pos);
}
static int has_duplicate_positions(const int *pos, int n) {
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      if (pos[i] == pos[j])
        return 1;
  return 0;
}
static void print_error_comparison(const int *bp, const fe *bv, int bn,
                                   const int *ap, const fe *av, int an) {
  int total = bn + an;
  ErrorEntry *entry = malloc(sizeof(*entry) * (size_t)(total + 1));
  for (int i = 0; i < bn; i++) {
    entry[i].pos = bp[i];
    entry[i].val = bv[i];
  }
  for (int i = 0; i < an; i++) {
    entry[bn + i].pos = ap[i];
    entry[bn + i].val = av[i];
  }
  qsort(entry, (size_t)total, sizeof(*entry), compare_error_entry);
  printf("\nERROR VECTOR COMPARISON (sorted by point-index)\n");
  printf("  %5s | %5s | %5s %5s | %10s | %10s | %s\n", "No.", "index", "x", "y",
         "before", "after", "result");
  printf(
      "  ------+-------+-------------+------------+------------+---------\n");
  int row = 0, nmatch = 0;
  for (int i = 0; i < total;) {
    int k = entry[i].pos;
    fe before = 0, after = 0;
    int hb = 0, ha = 0;
    while (i < total && entry[i].pos == k)
      i++;
    for (int j = 0; j < bn; j++)
      if (bp[j] == k) {
        before = bv[j];
        hb = 1;
        break;
      }
    for (int j = 0; j < an; j++)
      if (ap[j] == k) {
        after = av[j];
        ha = 1;
        break;
      }
    char bt[16], at[16];
    if (hb)
      snprintf(bt, sizeof bt, "0x%03x", (unsigned)before);
    else
      snprintf(bt, sizeof bt, "-");
    if (ha)
      snprintf(at, sizeof at, "0x%03x", (unsigned)after);
    else
      snprintf(at, sizeof at, "-");
    const char *res = hb && ha && before == after ? "MATCH"
                      : hb && ha                  ? "DIFF"
                                                  : "MISSING";
    if (hb && ha && before == after)
      nmatch++;
    row++;
    printf("  %5d | %5d | 0x%03x 0x%03x | %10s | %10s | %s\n", row, k,
           (unsigned)PX[k], (unsigned)PY[k], bt, at, res);
  }
  printf("  rows=%d, before=%d errors, after=%d errors, MATCH=%d\n", row, bn,
         an, nmatch);
  free(entry);
}

/* ======================================================================
 *  基本アルゴリズム（核法）: G=F+H
 * ====================================================================== */
static int error_from_syndrome(const Tab *S, Poly *F, Poly *H, int *pos,
                               fe *val, int *info) {
  int na = F->nind, nb = H->nind;
  if (!mem_check("locator matrix", (double)na * nb * sizeof(fe)))
    return -1;
  syndrome_extend(S);
  int *ai = malloc(sizeof(int) * na), *aj = malloc(sizeof(int) * na),
      *bi = malloc(sizeof(int) * nb), *bj = malloc(sizeof(int) * nb);
  int x = 0, y = 0;
  for (int p = 0; p < F->n; p++)
    if (F->ind[p]) {
      ai[x] = F->pi[p];
      aj[x] = F->pj[p];
      x++;
    }
  for (int p = 0; p < H->n; p++)
    if (H->ind[p]) {
      bi[y] = H->pi[p];
      bj[y] = H->pj[p];
      y++;
    }
  fe *A = malloc(sizeof(fe) * (size_t)nb * na);
  for (int b = 0; b < nb; b++)
    for (int a = 0; a < na; a++)
      A[(size_t)b * na + a] = *Tp(S, ai[a] + bi[b], aj[a] + bj[b]);
  fe *ker;
  int kd = nullspace(A, nb, na, &ker);
  free(A);
  int *Z = malloc(sizeof(int) * npts), nz = 0;
  fe *mv = malloc(sizeof(fe) * na);
  for (int k = 0; k < npts; k++) {
    for (int a = 0; a < na; a++)
      mv[a] = monval(LX[k], LY[k], ai[a], aj[a]);
    int vanish = 1;
    for (int v = 0; v < kd && vanish; v++) {
      fe acc = 0;
      const fe *kv = ker + (size_t)v * na;
      for (int a = 0; a < na; a++)
        if (kv[a] && mv[a])
          acc ^= mul(kv[a], mv[a]);
      if (acc)
        vanish = 0;
    }
    if (vanish)
      Z[nz++] = k;
  }
  info[0] = na;
  info[1] = nb;
  info[2] = kd;
  info[3] = nz;
  free(ker);
  free(mv);
  free(ai);
  free(aj);
  free(bi);
  free(bj);
  if (kd == 0) {
    free(Z);
    return -1;
  }
  int cnt = values_from_syndrome(S, Z, nz, pos, val);
  free(Z);
  return cnt;
}

/* ======================================================================
 *  Feng-Rao 多数決（Sakata 型の逐次ガウス消去 + 多数決）
 *
 *  行・列の添字集合 P = Delta(pa,pb) の独立単項式（単項式順序 (qi+j, i)
 * で整列）。 行列 S[u][w] = T(m_u + m_w)。T は格子点 c ごとの値。 格子点 c =
 * m_u+m_w を順序の小さい方から処理する。T(c) が未知なら (1) F
 * の関係式で決まるときはそれを使う（誤りの入りようがない） (2)
 * そうでなければ、行 u が未ピボットかつ列 w
 * が未使用の対(well-behaved)の候補値で多数決 既知の T(c) について、行 u
 * が未ピボットな各対で  R = T(c) + Σ_{a<u} f_u[a] T(m_a+m_w) を計算。 列 w
 * が未使用で R!=0 → (u,w) がピボット。 列 w が使用済み(行 u0 が使用)で R!=0 →
 * f_u <- f_u - R/δ0 * f_u0。 最後に未ピボット行の f_u が誤り位置多項式。
 * ====================================================================== */
typedef struct {
  int stop_c; /* 処理を打ち切った格子点の通し番号（-1: 最後まで処理） */
  int rank;   /* 見つかったピボット数 */
  int nvote, nrel, nknown,
      nweak; /* 多数決回数 / 関係式で決めた数 / 既知 / 僅差の多数決 */
  int nrows;
} FRInfo;

static int ord_less(int i1, int j1, int i2, int j2) {
  int l1 = Q * i1 + j1, l2 = Q * i2 + j2;
  if (l1 != l2)
    return l1 < l2;
  return i1 < i2;
}
static Poly *sortP;
static int cmp_ord_idx(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  if (ord_less(sortP->pi[x], sortP->pj[x], sortP->pi[y], sortP->pj[y]))
    return -1;
  if (ord_less(sortP->pi[y], sortP->pj[y], sortP->pi[x], sortP->pj[x]))
    return 1;
  return 0;
}

static int fr_decode(const Tab *S, Poly *Pp, Poly *Dp, int a_known, int b_known,
                     int tmax, int *pos, fe *val, FRInfo *fi) {
  memset(fi, 0, sizeof *fi);
  fi->stop_c = -1;
  /* 行・列: P の独立単項式 */
  int N = Pp->nind;
  int *rI = malloc(sizeof(int) * N), *rJ = malloc(sizeof(int) * N);
  {
    int *id = malloc(sizeof(int) * Pp->n), k = 0;
    for (int p = 0; p < Pp->n; p++)
      if (Pp->ind[p])
        id[k++] = p;
    sortP = Pp;
    qsort(id, N, sizeof(int), cmp_ord_idx);
    for (int u = 0; u < N; u++) {
      rI[u] = Pp->pi[id[u]];
      rJ[u] = Pp->pj[id[u]];
    }
    free(id);
  }
  fi->nrows = N;
  int pW = Pp->jmax - Pp->jmin + 1, pH = Pp->imax - Pp->imin + 1;
  int *pidx = malloc(sizeof(int) * (size_t)pW * pH);
  for (size_t k = 0; k < (size_t)pW * pH; k++)
    pidx[k] = -1;
  for (int u = 0; u < N; u++)
    pidx[(size_t)(rI[u] - Pp->imin) * pW + (rJ[u] - Pp->jmin)] = u;
  /* T 表: Delta(D) の全格子点 */
  int dW = Dp->jmax - Dp->jmin + 1, dH = Dp->imax - Dp->imin + 1;
  size_t dsz = (size_t)dW * dH;
  if (!mem_check("FR table", (double)dsz * 3 + (double)N * N * sizeof(fe)))
    return -1;
  fe *T = calloc(dsz, sizeof(fe));
  unsigned char *inD = calloc(dsz, 1), *det = calloc(dsz, 1);
  for (int p = 0; p < Dp->n; p++) {
    int i = Dp->pi[p], j = Dp->pj[p];
    size_t id = (size_t)(i - Dp->imin) * dW + (j - Dp->jmin);
    inD[id] = 1;
    if (Q * i + j <= a_known &&
        Q * j - (Q + 1) * i <= b_known) { /* i+q^2 j>=0 は D に含まれる */
      T[id] = *Tp(S, i, j);
      det[id] = 1;
      fi->nknown++;
    }
  }
#define DIDX(i, j) ((size_t)((i) - Dp->imin) * dW + ((j) - Dp->jmin))
#define INBOX(i, j)                                                            \
  ((i) >= Dp->imin && (i) <= Dp->imax && (j) >= Dp->jmin && (j) <= Dp->jmax)
  /* D の格子点を順序で整列 */
  int nD = Dp->n;
  int *ord = malloc(sizeof(int) * nD);
  for (int p = 0; p < nD; p++)
    ord[p] = p;
  sortP = Dp;
  qsort(ord, nD, sizeof(int), cmp_ord_idx);

  fe **Fm = malloc(sizeof(fe *) * N); /* f_u : 係数は添字 0..u */
  for (int u = 0; u < N; u++) {
    Fm[u] = calloc(u + 1, sizeof(fe));
    Fm[u][u] = 1;
  }
  char *rowPiv = calloc(N, 1);
  int *colPiv = malloc(sizeof(int) * N);
  fe *pivVal = calloc(N, sizeof(fe));
  for (int w = 0; w < N; w++)
    colPiv[w] = -1;
  int *cntv = calloc(FS, sizeof(int)), *touched = malloc(sizeof(int) * (N + 1));
  fe *cand = malloc(sizeof(fe) * (N + 1));
  int *pairU = malloc(sizeof(int) * (N + 1)),
      *pairW = malloc(sizeof(int) * (N + 1));
  int blocked = 0;

  for (int oc = 0; oc < nD && !blocked; oc++) {
    int ci = Dp->pi[ord[oc]], cj = Dp->pj[ord[oc]];
    size_t cid = DIDX(ci, cj);
    /* この格子点を作る対 (u,w) を列挙 */
    int np = 0;
    for (int u = 0; u < N; u++) {
      int wi = ci - rI[u], wj = cj - rJ[u];
      if (wi < Pp->imin || wi > Pp->imax || wj < Pp->jmin || wj > Pp->jmax)
        continue;
      int w = pidx[(size_t)(wi - Pp->imin) * pW + (wj - Pp->jmin)];
      if (w < 0)
        continue;
      pairU[np] = u;
      pairW[np] = w;
      np++;
    }
    if (np == 0 && det[cid])
      continue;
    /* 各対の候補値（f_u による線形結合の T(c) を除いた部分） */
    int need = 0; /* T(c) が必要な対の数 */
    int nvoter = 0;
    for (int k = 0; k < np; k++) {
      int u = pairU[k], w = pairW[k];
      if (rowPiv[u]) {
        cand[k] = 0;
        continue;
      }
      need++;
      fe acc = 0;
      const fe *fu = Fm[u];
      for (int a = 0; a < u; a++)
        if (fu[a]) {
          int ti = rI[a] + rI[w], tj = rJ[a] + rJ[w];
          size_t tid = DIDX(ti, tj);
          if (!det[tid]) {
            blocked = 1;
            break;
          }
          acc ^= mul(fu[a], T[tid]);
        }
      if (blocked)
        break;
      cand[k] = acc;
      if (colPiv[w] < 0)
        nvoter++;
    }
    if (blocked) {
      fi->stop_c = oc;
      break;
    }
    if (!det[cid]) {
      /* (1) 関係式 */
      int ai = ci - QQ, aj = cj + 1;  /* c+(-q^2,1) */
      int bi_ = ci - 1, bj_ = cj + Q; /* c+(-1,q)   */
      int di = ci - Q, dj = cj + QQ;  /* c+(-q,q^2) */
      if (INBOX(ai, aj) && INBOX(bi_, bj_) && INBOX(di, dj) &&
          det[DIDX(ai, aj)] && det[DIDX(bi_, bj_)] && det[DIDX(di, dj)] &&
          inD[DIDX(ai, aj)] && inD[DIDX(bi_, bj_)] && inD[DIDX(di, dj)]) {
        T[cid] = T[DIDX(ai, aj)] ^ T[DIDX(bi_, bj_)] ^ T[DIDX(di, dj)];
        det[cid] = 1;
        fi->nrel++;
      } else if (nvoter > 0) {
        /* (2) 多数決 */
        int nt = 0, tot = 0;
        for (int k = 0; k < np; k++) {
          int u = pairU[k], w = pairW[k];
          if (rowPiv[u] || colPiv[w] >= 0)
            continue;
          fe v = cand[k];
          if (cntv[v] == 0)
            touched[nt++] = v;
          cntv[v]++;
          tot++;
        }
        int best = -1, bc = 0, second = 0;
        for (int k = 0; k < nt; k++) {
          int v = touched[k];
          if (cntv[v] > bc) {
            second = bc;
            bc = cntv[v];
            best = v;
          } else if (cntv[v] > second)
            second = cntv[v];
        }
        for (int k = 0; k < nt; k++)
          cntv[touched[k]] = 0;
        if (2 * bc > tot) {
          T[cid] = (fe)best;
          det[cid] = 1;
          fi->nvote++;
          if (bc - second <= 2)
            fi->nweak++;
        } else {
          blocked = 1;
          fi->stop_c = oc;
          break;
        }
      } else if (need > 0) {
        blocked = 1;
        fi->stop_c = oc;
        break; /* T(c) が要るのに決められない */
      } else
        continue; /* 不要な未知セル */
    }
    /* 消去 */
    fe tc = T[cid];
    for (int k = 0; k < np; k++) {
      int u = pairU[k], w = pairW[k];
      if (rowPiv[u])
        continue;
      fe R = tc ^ cand[k];
      if (!R)
        continue;
      int u0 = colPiv[w];
      if (u0 < 0) {
        rowPiv[u] = 1;
        colPiv[w] = u;
        pivVal[w] = R;
        fi->rank++;
      } else {
        fe ratio = mul(R, inv(pivVal[w]));
        int lr = glog[ratio];
        const fe *f0 = Fm[u0];
        fe *fu = Fm[u];
        for (int a = 0; a <= u0; a++)
          if (f0[a])
            fu[a] ^= gexp[lr + glog[f0[a]]];
      }
    }
  }
  /* 未ピボット行 f_u の共通零点 */
  int *Z = malloc(sizeof(int) * npts), nz = npts;
  for (int k = 0; k < npts; k++)
    Z[k] = k;
  int cnt = -1;
  for (int u = 0; u < N && nz > fi->rank; u++) {
    if (rowPiv[u])
      continue;
    int m = 0;
    int *Zn = malloc(sizeof(int) * (nz + 1));
    for (int z = 0; z < nz; z++) {
      int k = Z[z];
      fe acc = 0;
      for (int a = 0; a <= u; a++)
        if (Fm[u][a])
          acc ^= mul(Fm[u][a], monval(LX[k], LY[k], rI[a], rJ[a]));
      if (!acc)
        Zn[m++] = k;
    }
    /* 打切り後の未完成な行は誤り位置まで消してしまうことがある。ピボット数より減るなら採用しない
     */
    if (m >= fi->rank) {
      memcpy(Z, Zn, sizeof(int) * m);
      nz = m;
    }
    free(Zn);
  }
  if (nz >= fi->rank && nz <= 4 * tmax + 64)
    cnt = values_from_syndrome(S, Z, nz, pos, val);
  if (dump_all)
    fprintf(stderr, "FR: rank=%d nz=%d\n", fi->rank, nz);
  free(Z);
  for (int u = 0; u < N; u++)
    free(Fm[u]);
  free(Fm);
  free(rI);
  free(rJ);
  free(pidx);
  free(T);
  free(inD);
  free(det);
  free(ord);
  free(rowPiv);
  free(colPiv);
  free(pivVal);
  free(cntv);
  free(touched);
  free(cand);
  free(pairU);
  free(pairW);
  return cnt;
}

int main(int argc, char **argv) {
  int m = 9, q = 8, t = 256, len = 8192, a_req = -1, b_req = -1, pa_req = -1,
      pb_req = -1;
  int force = 0, basic = 0;
  unsigned seed = 1;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--m") && i + 1 < argc)
      m = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--q") && i + 1 < argc)
      q = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--errors") && i + 1 < argc)
      t = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--len") && i + 1 < argc)
      len = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--a") && i + 1 < argc)
      a_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--b") && i + 1 < argc)
      b_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--pa") && i + 1 < argc)
      pa_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--pb") && i + 1 < argc)
      pb_req = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--seed") && i + 1 < argc)
      seed = (unsigned)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--mem") && i + 1 < argc)
      mem_mb_opt = atof(argv[++i]);
    else if (!strcmp(argv[i], "--force"))
      force = 1;
    else if (!strcmp(argv[i], "--basic"))
      basic = 1;
    else if (!strcmp(argv[i], "--dump"))
      dump_all = 1;
    else if (!strcmp(argv[i], "--quiet"))
      dump_all = 0;
    else {
      fprintf(stderr, "unknown option %s\n", argv[i]);
      return 1;
    }
  }
  static const unsigned dp[12] = {0,    3,    7,     0xB,   0x13,  0x25,
                                  0x43, 0x89, 0x11D, 0x211, 0x409, 0x805};
  if (m < 2 || m > 11 || gf_init(m, dp[m])) {
    fprintf(stderr, "bad m\n");
    return 1;
  }
  Q = q;
  QQ = q * q;
  rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
  for (int i = 0; i < 8; i++)
    rnd();
  int g = (q * q * q * q - 3 * q + 2) / 2;
  int basic_deg_sufficient = 2 * t + 3 * g - 1;
  /* 既定の G: FR は基本法より小さい次数 2t+g+...
   * から試す。基本法は十分条件どおり */
  int deg_default = basic
                        ? basic_deg_sufficient
                        : (basic_deg_sufficient -
                           g); /* FR の既定: 基本法の十分条件より g
                                  だけ小さく（経験則。成功は必ず照合される） */
  int a = a_req > 0 ? a_req : (deg_default + 2 * q - 2) / (2 * q - 1),
      b = b_req > 0 ? b_req : a;
  int aH = (t + 2 * g - 1 + 2 * q - 2) / (2 * q - 1), bH = aH, aF = a - aH,
      bF = b - bH;
  double t0 = now();
  Poly G, F, H;
  poly_build(&G, a, b);
  int degG = q * a + (q - 1) * b;
  printf("BBGS 曲線: q=%d, GF(2^%d), genus g=%d, 誤り数 t=%d, 方式=%s\n", q, m,
         g, t, basic ? "基本(核法)" : "Feng-Rao(多数決)");
  printf("除数 G=(E1 上の a=%d, E2 上の b=%d): deg G=%d（基本法の十分条件 "
         "2t+3g-1=%d）\n",
         a, b, degG, basic_deg_sufficient);
  int d_design = degG - 2 * g + 2;
  printf("双対 AG 符号の設計最小距離の下界: d >= deg G - 2g + 2 = "
         "%d（一意復号半径 >= %d）\n",
         d_design, d_design > 0 ? (d_design - 1) / 2 : 0);
  if (basic) {
    poly_build(&F, aF, bF);
    poly_build(&H, aH, bH);
    int degH = q * aH + (q - 1) * bH;
    printf("Newton 多角形の基底構成 (%.3f s): dim L(G)=%d [RR=%d], dim V_F=%d, "
           "dim L(H)=%d [RR=%d]\n",
           now() - t0, G.nind, degG - g + 1, F.nind, H.nind, degH - g + 1);
    if (G.nind != degG - g + 1 || H.nind != degH - g + 1 || degH < 2 * g - 1)
      printf("WARNING: Riemann-Roch による完全性を確認できません\n");
    if (F.nind <= t || degH < t + 2 * g - 1 || degG < basic_deg_sufficient) {
      fprintf(stderr, "基本アルゴリズムの十分条件を満たしていません\n");
      if (!force) {
        fprintf(stderr, "--force で条件を無視して試せます。\n");
        return 1;
      }
    }
  } else {
    printf("基底構成 (%.3f s): dim L(G)=%d [RR=%d], Delta(G) の格子点数=%d\n",
           now() - t0, G.nind, degG - g + 1, G.n);
    if (G.nind != degG - g + 1)
      printf("WARNING: Riemann-Roch による完全性を確認できません\n");
  }
  t0 = now();
  enumerate_points(len);
  printf("符号位置として使用する曲線上の点（原点を除外）: n=%d (%.2f s)\n",
         npts, now() - t0);
  if (t < 0 || t > npts) {
    fprintf(stderr, "誤り数 t=%d は n=%d の範囲外です\n", t, npts);
    return 1;
  }
  if (G.nind >= npts) {
    fprintf(stderr, "n must exceed dim L(G)\n");
    return 1;
  }
  Tab S, D;
  S.G = D.G = &G;
  S.W = D.W = G.jmax - G.jmin + 1;
  size_t tsz = (size_t)(G.imax - G.imin + 1) * S.W;
  S.T = malloc(sizeof(fe) * tsz);
  D.T = malloc(sizeof(fe) * tsz);
  int *tpos = malloc(sizeof(int) * (t + 1));
  fe *tval = malloc(sizeof(fe) * (t + 1));
  for (int u = 0; u < t; u++) {
    int p, dup;
    do {
      p = rnd() % npts;
      dup = 0;
      for (int k = 0; k < u; k++)
        if (tpos[k] == p)
          dup = 1;
    } while (dup);
    tpos[u] = p;
    do
      tval[u] = rnd() % FS;
    while (!tval[u]);
  }
  t0 = now();
  syndrome_table(&S, tpos, tval, t);
  double ts = now() - t0;
  /* 復号器には独立なシンドローム成分（dim L(G) 個）だけを渡す */
  memset(D.T, 0, sizeof(fe) * tsz);
  for (int p = 0; p < G.n; p++)
    if (G.ind[p])
      *Tp(&D, G.pi[p], G.pj[p]) = *Tp(&S, G.pi[p], G.pj[p]);
  int *pos = malloc(sizeof(int) * (npts + 1));
  fe *val = malloc(sizeof(fe) * (npts + 1));
  int info[4] = {0};
  int cnt;
  FRInfo fi;
  memset(&fi, 0, sizeof fi);
  t0 = now();
  if (basic) {
    cnt = error_from_syndrome(&D, &F, &H, pos, val, info);
  } else {
    syndrome_extend(&D);
    /* 行・列の集合 P=Delta(pa,pb) と、T を延長する範囲 D=Delta(2pa,2pb) */
    int pb = pb_req > 0 ? pb_req : b / 2, pa = pa_req > 0 ? pa_req : a;
    Poly P, DD;
    poly_build(&P, pa, pb);
    poly_build(&DD, 2 * pa, 2 * pb);
    printf("FR: 行/列 P=Delta(%d,%d) の次元 N=%d、延長範囲 Delta(%d,%d) "
           "の格子点数=%d\n",
           pa, pb, P.nind, 2 * pa, 2 * pb, DD.n);
    cnt = fr_decode(&D, &P, &DD, a, b, t, pos, val, &fi);
    printf("FR: ピボット(=見つかった誤り数)=%d, 既知=%d, 関係式で決定=%d, "
           "多数決=%d（僅差 %d）, 打切り番号=%d\n",
           fi.rank, fi.nknown, fi.nrel, fi.nvote, fi.nweak, fi.stop_c);
  }
  double td = now() - t0;
  int good = (cnt == t) && !has_duplicate_positions(pos, cnt > 0 ? cnt : 0);
  for (int c = 0; c < cnt && good; c++) {
    int f = 0;
    for (int u = 0; u < t; u++)
      if (tpos[u] == pos[c] && tval[u] == val[c])
        f = 1;
    if (!f)
      good = 0;
  }
  printf("誤りベクトルからのシンドローム計算（検査行列なし）: %.4f s, 独立成分 "
         "%d 個\n",
         ts, G.nind);
  printf("復号: %.3f 秒, 復元した誤り数=%d -> %s\n", td, cnt,
         good ? "成功" : "失敗");
  if (dump_all && cnt >= 0)
    print_error_comparison(tpos, tval, t, pos, val, cnt);
  return good ? 0 : 2;
}