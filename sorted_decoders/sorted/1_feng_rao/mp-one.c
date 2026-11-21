/*
 * 代数幾何符号 (1点符号 / Miura C_ab 型曲線) の Feng-Rao 復号器
 *
 *   F(x,y)=0 の GF(2^7) 上の有理点 + 無限遠点 P_inf
 *   シンドローム s(f) = sum_j e_j f(P_j),  f in L(m P_inf)
 *
 * 復号: Feng-Rao 多数決 (Feng-Rao-Duursma) で未知シンドロームを順に決め、
 *       鍵方程式の核から誤り位置を求め、既知シンドロームから誤り値を解く。
 *
 * 使い方:  ./fr_ag [seed] [誤り数] [曲線名]      (既定: 乱数 / E / tt)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define V 3			/* 変数の数 */
#define P 1024			/* 多項式の最大項数 */
#define Q 2			/* 基礎体 */
#define N 128			/* 定義体 GF(2^7) */
#define E 5			/* 既定の誤り個数 */
#define MAXPT 150000		/* 有理点の最大数 */

typedef struct
{
  unsigned short n[V];		/* x,y,z の指数 */
  unsigned short a;		/* 係数 (対数表示: gf[a] が体の元, 0 は零項) */
} mterm;

typedef struct
{
  mterm x[P];
} MP;

typedef struct
{
  unsigned char z[V][MAXPT];	/* 有理点 (体の元) */
} PO;

unsigned short gf[128] =
  { 0, 1, 2, 4, 8, 16, 32, 64, 65, 67, 71, 79, 95, 127, 63, 126, 61, 122, 53,
106, 21, 42, 84, 105, 19, 38, 76, 89, 115, 39, 78, 93, 123, 55, 110, 29, 58,
116, 41, 82, 101, 11, 22, 44, 88, 113, 35, 70, 77, 91, 119, 47, 94, 125, 59,
118, 45, 90, 117, 43, 86, 109, 27, 54, 108, 25, 50, 100, 9, 18, 36, 72, 81,
99, 7, 14, 28, 56, 112, 33, 66, 69, 75, 87, 111, 31, 62, 124, 57, 114, 37, 74,
85, 107, 23, 46, 92, 121, 51, 102, 13, 26, 52, 104, 17, 34, 68, 73, 83, 103,
15, 30, 60, 120, 49, 98, 5, 10, 20, 40, 80, 97, 3, 6, 12, 24, 48, 96 };
unsigned short fg[128] =
  { 0, 1, 2, 122, 3, 116, 123, 74, 4, 68, 117, 41, 124, 100, 75, 110, 5, 104,
69, 24, 118, 20, 42, 94, 125, 65, 101, 62, 76, 35, 111, 85, 6, 79, 105, 46,
70, 90, 25, 29, 119, 38, 21, 59, 43, 56, 95, 51, 126, 114, 66, 98, 102, 18,
63, 33, 77, 88, 36, 54, 112, 16, 86, 14, 7, 8, 80, 9, 106, 81, 47, 10, 71,
107, 91, 82, 26, 48, 30, 11, 120, 72, 39, 108, 22, 92, 60, 83, 44, 27, 57,
49, 96, 31, 52, 12, 127, 121, 115, 73, 67, 40, 99, 109, 103, 23, 19, 93, 64,
61, 34, 84, 78, 45, 89, 28, 37, 58, 55, 50, 113, 97, 17, 32, 87, 53, 15, 13 };

/* ------------------------------------------------------------------ */
/* GF(2^7) の演算 (mlt/mltn/oinv/inv2 を元の表現で統一)                */
/* ------------------------------------------------------------------ */
static unsigned short expt[2 * N];

static void
gf_init (void)
{
  int k;

  for (k = 1; k < N; k++)
    if (fg[gf[k]] != k)
      {
	fprintf (stderr, "gf/fg テーブルが不整合です\n");
	exit (EXIT_FAILURE);
      }
  for (k = 0; k < 2 * (N - 1); k++)
    expt[k] = gf[k % (N - 1) + 1];
}

static unsigned short
gmul (unsigned short a, unsigned short b)
{
  return (a && b) ? expt[fg[a] + fg[b] - 2] : 0;
}

static unsigned short
ginv (unsigned short a)		/* a != 0 */
{
  return expt[N - fg[a]];
}

static unsigned short
gdiv (unsigned short a, unsigned short b)	/* b != 0 */
{
  return a ? expt[fg[a] - fg[b] + N - 1] : 0;
}

static unsigned short
gpow (unsigned short a, int n)
{
  if (n == 0)
    return 1;
  if (a == 0)
    return 0;
  return expt[(int) (((long) (fg[a] - 1) * n) % (N - 1))];
}

/* ------------------------------------------------------------------ */
/* 多項式 (全てポインタ渡し)                                          */
/* ------------------------------------------------------------------ */
int
terms (const MP * f)
{
  int k = 0;

  while (k < P && f->x[k].a != 0)
    k++;
  return k;
}

unsigned short
degterm (const mterm * z)
{
  int j;
  unsigned short c = 0;

  for (j = 0; j < V; j++)
    c += z->n[j];
  return c;
}

int
mdeg (const MP * f)
{
  int i, k = 0, d, nt = terms (f);

  for (i = 0; i < nt; i++)
    {
      d = degterm (&f->x[i]);
      if (d > k)
	k = d;
    }
  return k;
}

/* f に単項式 o を掛ける (mterml / mtermul の統一版) */
void
mterm_mul (MP * f, const mterm * o)
{
  int i, j, nt = terms (f);

  for (i = 0; i < nt; i++)
    {
      for (j = 0; j < V; j++)
	f->x[i].n[j] += o->n[j];
      f->x[i].a = fg[gmul (gf[f->x[i].a], gf[o->a])];
    }
}

/* F(x,y,z) の値 (otrace の統一版) */
unsigned short
mpoly_eval (const MP * f, unsigned short x, unsigned short y,
	    unsigned short z)
{
  int i, nt = terms (f);
  unsigned short u = 0;

  for (i = 0; i < nt; i++)
    u ^= gmul (gf[f->x[i].a],
	       gmul (gmul (gpow (x, f->x[i].n[0]), gpow (y, f->x[i].n[1])),
		     gpow (z, f->x[i].n[2])));
  return u;
}

/* アフィン有理点 (z=1) を列挙。個数を返す。溢れたら -1 */
int
mtrace (const MP * f, PO * p)
{
  int x, y, count = 0;

  for (x = 0; x < N; x++)
    for (y = 0; y < N; y++)
      if (mpoly_eval (f, x, y, 1) == 0)
	{
	  if (count >= MAXPT)
	    return -1;
	  p->z[0][count] = x;
	  p->z[1][count] = y;
	  p->z[2][count] = 1;
	  count++;
	}
  return count;
}

int
set_curve (MP * s, const unsigned short (*a)[4], int x)
{
  int i, j;

  if (x > P)
    return -1;
  memset (s, 0, sizeof (MP));
  for (i = 0; i < x; i++)
    {
      for (j = 0; j < V; j++)
	s->x[i].n[j] = a[i][j];
      s->x[i].a = a[i][3];
    }
  return x;
}

/* エルミート曲線 x^(Q+1)+y^(Q+1)+z^(Q+1) */
void
define_curve (MP * s)
{
/*
//sc
s.x[0].n[0]=Q*Q-1;
s.x[0].n[1]=Q;
s.x[0].n[2]=1;
s.x[1].n[0]=Q;
s.x[1].n[1]=Q*Q;
s.x[2].n[0]=0;
s.x[2].n[1]=1;
s.x[2].n[2]=4;
s.x[3].n[0]=Q*Q;
s.x[3].n[1]=0;
s.x[3].n[2]=2;
*/
//hermite
  memset (s, 0, sizeof (MP));
  s->x[0].n[0] = Q + 1;
  s->x[0].a = 1;
  s->x[1].n[1] = Q + 1;
  s->x[1].a = 1;
  s->x[2].n[2] = Q + 1;
  s->x[2].a = 1;
}

/* ------------------------------------------------------------------ */
/* Feng-Rao 復号                                                       */
/* ------------------------------------------------------------------ */
/*
 * F = c_A x^A + c_B y^B + (重み < AB の項),  gcd(A,B)=1,  w(x)=B, w(y)=A
 * 基底 x^i y^j (0<=j<B) は重みが全て異なり、重み順に φ_0,φ_1,... と並ぶ。
 * y^B = sum_t rc[t] x^rp[t] y^rq[t]  (標数2)
 */
typedef struct
{
  int A, B, g;			/* 半群 <A,B>, 種数(ギャップ数) */
  int m;			/* 既知シンドロームの最大重み */
  int wmax;			/* 扱う最大重み = 2m */
  int nb, nk;			/* 基底数 / 重み<=m の基底数 */
  int nred;
  unsigned short rho;		/* y^B を x^A に直したときの係数 */
  int rp[P], rq[P];
  unsigned short rc[P];
  int *wt, *mi, *mj;		/* 基底の重み, x の指数, y の指数 */
  int *idx;			/* 重み -> 基底番号 (ギャップは -1) */
} FR;

typedef struct
{
  int steps;			/* 多数決で決めたシンドローム数 */
  int wrong;			/* 真値と違った数 (真値が与えられたときのみ) */
} FRStat;

static int
gcd (int a, int b)
{
  int t;

  while (b)
    {
      t = a % b;
      a = b;
      b = t;
    }
  return a;
}

/* 曲線が C_ab 型か調べ、設計誤り数 tdes に対する符号パラメータを作る */
int
fr_setup (FR * fr, const MP * f, int tdes)
{
  int i, k, n = 0, w, c, A = 0, B = 0, nt = terms (f);
  int tn0[P], tn1[P], *ti, *tj;
  unsigned short tc[P], cx = 0, cy = 0;

  memset (fr, 0, sizeof (FR));

  /* z=1 とした同類項を整理 */
  for (i = 0; i < nt; i++)
    {
      for (k = 0; k < n; k++)
	if (tn0[k] == f->x[i].n[0] && tn1[k] == f->x[i].n[1])
	  break;
      if (k == n)
	{
	  tn0[n] = f->x[i].n[0];
	  tn1[n] = f->x[i].n[1];
	  tc[n++] = 0;
	}
      tc[k] ^= gf[f->x[i].a];
    }
  for (k = i = 0; k < n; k++)
    if (tc[k])
      {
	tn0[i] = tn0[k];
	tn1[i] = tn1[k];
	tc[i++] = tc[k];
      }
  n = i;

  for (k = 0; k < n; k++)
    {
      if (tn1[k] == 0 && tn0[k] > A)
	{
	  A = tn0[k];
	  cx = tc[k];
	}
      if (tn0[k] == 0 && tn1[k] > B)
	{
	  B = tn1[k];
	  cy = tc[k];
	}
    }
  if (A < 1 || B < 1 || gcd (A, B) != 1)
    {
      fprintf (stderr,
	       "C_ab 型ではありません (x^A=%d, y^B=%d が互いに素でない/無い)\n",
	       A, B);
      return -1;
    }
  for (k = 0; k < n; k++)
    {
      if ((tn0[k] == A && tn1[k] == 0) || (tn0[k] == 0 && tn1[k] == B))
	continue;
      if (tn0[k] * B + tn1[k] * A >= A * B)
	{
	  fprintf (stderr,
		   "C_ab 型ではありません: x^%d y^%d の重みが x^%d,y^%d 以上\n",
		   tn0[k], tn1[k], A, B);
	  return -1;
	}
    }

  fr->A = A;
  fr->B = B;
  fr->g = (A - 1) * (B - 1) / 2;
  fr->rho = gdiv (cx, cy);
  for (k = 0; k < n; k++)
    {
      if (tn0[k] == 0 && tn1[k] == B)
	continue;
      fr->rp[fr->nred] = tn0[k];
      fr->rq[fr->nred] = tn1[k];
      fr->rc[fr->nred++] = gdiv (tc[k], cy);
    }

  fr->m = 2 * tdes + 2 * fr->g - 1;
  fr->wmax = 2 * fr->m;

  fr->idx = malloc ((fr->wmax + 1) * sizeof (int));
  ti = malloc ((fr->wmax + 1) * sizeof (int));
  tj = malloc ((fr->wmax + 1) * sizeof (int));
  if (!fr->idx || !ti || !tj)
    return -1;
  for (w = 0; w <= fr->wmax; w++)
    fr->idx[w] = -1;
  for (c = 0; c < B; c++)
    for (i = 0; i * B + c * A <= fr->wmax; i++)
      {
	w = i * B + c * A;
	fr->idx[w] = 0;
	ti[w] = i;
	tj[w] = c;
      }
  for (w = 0; w <= fr->wmax; w++)
    if (fr->idx[w] == 0)
      fr->nb++;
  fr->wt = malloc (fr->nb * sizeof (int));
  fr->mi = malloc (fr->nb * sizeof (int));
  fr->mj = malloc (fr->nb * sizeof (int));
  if (!fr->wt || !fr->mi || !fr->mj)
    return -1;
  for (k = w = 0; w <= fr->wmax; w++)
    if (fr->idx[w] == 0)
      {
	fr->wt[k] = w;
	fr->mi[k] = ti[w];
	fr->mj[k] = tj[w];
	fr->idx[w] = k++;
      }
  for (fr->nk = 0; fr->nk < fr->nb && fr->wt[fr->nk] <= fr->m; fr->nk++);
  free (ti);
  free (tj);
  return 0;
}

void
fr_free (FR * fr)
{
  free (fr->wt);
  free (fr->mi);
  free (fr->mj);
  free (fr->idx);
}

/* s(x^i y^j): j>=B のときは曲線の式で簡約する */
static unsigned short
mono_syn (const FR * fr, const unsigned short *s, int i, int j)
{
  int t;
  unsigned short r = 0;

  if (j < fr->B)
    return s[fr->idx[i * fr->B + j * fr->A]];
  for (t = 0; t < fr->nred; t++)
    r ^= gmul (fr->rc[t],
	       mono_syn (fr, s, i + fr->rp[t], j - fr->B + fr->rq[t]));
  return r;
}

/*
 * 組 (a,b) が Feng-Rao の candidate か判定し、そうなら
 *   rank S[0..a][0..b] = rank S[0..a-1][0..b-1]
 * を保つ S_ab の値 *x を返す (戻り値 1)。work は (nb+2)^2 個以上。
 */
static int
fr_cand (const unsigned short *S, int nb, int a, int b, unsigned short *x,
	 unsigned short *work, int *pc)
{
  int i, j, p, nr = 0, st = b + 1, rmax = a < b ? a : b;
  unsigned short *w = work + (size_t) rmax * st, *u = w + st, *row, c, iv,
    xv = 0;

  for (i = 0; i < a; i++)
    {
      memcpy (w, S + (size_t) i * nb, st * sizeof (unsigned short));
      for (p = 0; p < nr; p++)
	{
	  c = w[pc[p]];
	  if (c)
	    {
	      row = work + (size_t) p * st;
	      for (j = 0; j <= b; j++)
		w[j] ^= gmul (c, row[j]);
	    }
	}
      for (j = 0; j < b && !w[j]; j++);
      if (j < b)
	{
	  iv = ginv (w[j]);
	  row = work + (size_t) nr * st;
	  for (p = 0; p <= b; p++)
	    row[p] = gmul (w[p], iv);
	  pc[nr++] = j;
	}
      else if (w[b])
	return 0;		/* rank S[0..a-1][0..b] が増える */
    }

  memcpy (u, S + (size_t) a * nb, b * sizeof (unsigned short));
  for (p = 0; p < nr; p++)
    {
      c = u[pc[p]];
      if (c)
	{
	  row = work + (size_t) p * st;
	  for (j = 0; j < b; j++)
	    u[j] ^= gmul (c, row[j]);
	  xv ^= gmul (c, row[b]);
	}
    }
  for (j = 0; j < b; j++)
    if (u[j])
      return 0;			/* rank S[0..a][0..b-1] が増える */
  *x = xv;
  return 1;
}

/*
 * 重み Lam までのシンドロームから鍵方程式 sum_k f_k s(φ_i φ_k)=0 の核を求め、
 * 核の関数の共通零点を誤り位置とし、既知シンドローム(重み<=m)から誤り値を解く。
 * 成功なら誤り個数、失敗なら -1。
 */
static int
fr_extract (const FR * fr, const unsigned short *Phi, int npt,
	    const unsigned short *S, int Lam, int tmax, unsigned short *e,
	    const unsigned short *s)
{
  int nb = fr->nb, nk = fr->nk, ni = 0, i, j, k, r = 0, nc, cnt, ret = -1;
  unsigned short *K = NULL, *f = NULL, *A = NULL, v, iv;
  int *piv = NULL, *cl = NULL, *pr = NULL;
  size_t ci;

  while (ni < nk && 2 * fr->wt[ni] <= Lam)
    ni++;
  if (ni == 0)
    return -1;

  K = malloc ((size_t) ni * ni * sizeof (unsigned short));
  f = malloc (ni * sizeof (unsigned short));
  piv = malloc (ni * sizeof (int));
  cl = malloc (npt * sizeof (int));
  if (!K || !f || !piv || !cl)
    goto done;
  for (i = 0; i < ni; i++)
    for (k = 0; k < ni; k++)
      K[(size_t) i * ni + k] = S[(size_t) i * nb + k];

  /* 被約階段形 */
  for (k = 0; k < ni && r < ni; k++)
    {
      for (i = r; i < ni && !K[(size_t) i * ni + k]; i++);
      if (i == ni)
	continue;
      if (i != r)
	for (j = 0; j < ni; j++)
	  {
	    v = K[(size_t) i * ni + j];
	    K[(size_t) i * ni + j] = K[(size_t) r * ni + j];
	    K[(size_t) r * ni + j] = v;
	  }
      iv = ginv (K[(size_t) r * ni + k]);
      for (j = 0; j < ni; j++)
	K[(size_t) r * ni + j] = gmul (K[(size_t) r * ni + j], iv);
      for (i = 0; i < ni; i++)
	if (i != r && K[(size_t) i * ni + k])
	  {
	    v = K[(size_t) i * ni + k];
	    for (j = 0; j < ni; j++)
	      K[(size_t) i * ni + j] ^= gmul (v, K[(size_t) r * ni + j]);
	  }
      piv[r++] = k;
    }
  if (r == ni)
    goto done;			/* 核が自明 */

  /* 核の各ベクトルの共通零点 */
  nc = npt;
  for (i = 0; i < npt; i++)
    cl[i] = i;
  for (k = 0; k < ni && nc > 0; k++)
    {
      for (i = 0; i < r && piv[i] != k; i++);
      if (i < r)
	continue;		/* 自由列でない */
      memset (f, 0, ni * sizeof (unsigned short));
      f[k] = 1;
      for (i = 0; i < r; i++)
	f[piv[i]] = K[(size_t) i * ni + k];
      cnt = 0;
      for (ci = 0; ci < (size_t) nc; ci++)
	{
	  v = 0;
	  for (j = 0; j < ni; j++)
	    if (f[j])
	      v ^= gmul (f[j], Phi[(size_t) j * npt + cl[ci]]);
	  if (v == 0)
	    cl[cnt++] = cl[ci];
	}
      nc = cnt;
    }
  if (nc == 0 || nc > nk)
    goto done;

  /* 誤り値: sum_c e_c φ_k(P_c) = s_k (重み<=m) */
  A = malloc ((size_t) nk * (nc + 1) * sizeof (unsigned short));
  pr = malloc (nc * sizeof (int));
  if (!A || !pr)
    goto done;
  for (k = 0; k < nk; k++)
    {
      for (j = 0; j < nc; j++)
	A[(size_t) k * (nc + 1) + j] = Phi[(size_t) k * npt + cl[j]];
      A[(size_t) k * (nc + 1) + nc] = s[k];
    }
  for (j = 0; j < nc; j++)
    {
      for (i = j; i < nk && !A[(size_t) i * (nc + 1) + j]; i++);
      if (i == nk)
	goto done;		/* 列階数不足: 解が一意でない */
      if (i != j)
	for (k = 0; k <= nc; k++)
	  {
	    v = A[(size_t) i * (nc + 1) + k];
	    A[(size_t) i * (nc + 1) + k] = A[(size_t) j * (nc + 1) + k];
	    A[(size_t) j * (nc + 1) + k] = v;
	  }
      iv = ginv (A[(size_t) j * (nc + 1) + j]);
      for (k = 0; k <= nc; k++)
	A[(size_t) j * (nc + 1) + k] = gmul (A[(size_t) j * (nc + 1) + k], iv);
      for (i = 0; i < nk; i++)
	if (i != j && A[(size_t) i * (nc + 1) + j])
	  {
	    v = A[(size_t) i * (nc + 1) + j];
	    for (k = 0; k <= nc; k++)
	      A[(size_t) i * (nc + 1) + k] ^=
		gmul (v, A[(size_t) j * (nc + 1) + k]);
	  }
    }
  for (i = nc; i < nk; i++)
    if (A[(size_t) i * (nc + 1) + nc])
      goto done;		/* 矛盾 */
  cnt = 0;
  for (j = 0; j < nc; j++)
    if (A[(size_t) j * (nc + 1) + nc])
      cnt++;
  if (cnt > tmax)
    goto done;
  memset (e, 0, npt * sizeof (unsigned short));
  for (j = 0; j < nc; j++)
    e[cl[j]] = A[(size_t) j * (nc + 1) + nc];
  ret = cnt;

done:
  free (K);
  free (f);
  free (piv);
  free (cl);
  free (A);
  free (pr);
  return ret;
}

/*
 * s0[k] (k<nk) : 受信語のシンドローム (重み<=m)
 * s_true       : 検証用の真のシンドローム (不要なら NULL)
 * 誤り個数 (>=0) か、復号失敗なら -1 を返す。
 */
int
fr_decode (const FR * fr, const unsigned short *Phi, int npt,
	   const unsigned short *s0, const unsigned short *s_true, int tmax,
	   unsigned short *e, FRStat * stat)
{
  int nb = fr->nb, nk = fr->nk, a, b, k, l, lam, ncand, ret = -1, mx, tie;
  unsigned short *s, *S, *work, x, val, R, c;
  int *pc, votes[N];

  s = calloc (nb, sizeof (unsigned short));
  S = calloc ((size_t) nb * nb, sizeof (unsigned short));
  work = malloc ((size_t) (nb + 2) * (nb + 2) * sizeof (unsigned short));
  pc = malloc (nb * sizeof (int));
  if (!s || !S || !work || !pc)
    goto done;

  stat->steps = stat->wrong = 0;
  memcpy (s, s0, nk * sizeof (unsigned short));
  for (k = 0; k < nk && !s[k]; k++);
  if (k == nk)			/* シンドローム 0 : 誤り無し */
    {
      memset (e, 0, npt * sizeof (unsigned short));
      ret = 0;
      goto done;
    }

  for (a = 0; a < nb; a++)
    for (b = 0; b < nb && fr->wt[a] + fr->wt[b] <= fr->m; b++)
      S[(size_t) a * nb + b] =
	mono_syn (fr, s, fr->mi[a] + fr->mi[b], fr->mj[a] + fr->mj[b]);

  ret = fr_extract (fr, Phi, npt, S, fr->m, tmax, e, s);
  for (lam = fr->m + 1; ret < 0 && lam <= fr->wmax; lam++)
    {
      l = fr->idx[lam];
      if (l < 0)
	continue;		/* ギャップ */

      /* 多数決 */
      memset (votes, 0, sizeof (votes));
      ncand = 0;
      s[l] = 0;
      for (a = 0; a < nb && fr->wt[a] <= lam; a++)
	{
	  b = fr->idx[lam - fr->wt[a]];
	  if (b < 0 || !fr_cand (S, nb, a, b, &x, work, pc))
	    continue;
	  R = mono_syn (fr, s, fr->mi[a] + fr->mi[b], fr->mj[a] + fr->mj[b]);
	  c = (fr->mj[a] + fr->mj[b] >= fr->B) ? fr->rho : 1;
	  votes[gdiv (x ^ R, c)]++;
	  ncand++;
	}
      if (ncand == 0)
	break;
      mx = -1;
      tie = 0;
      val = 0;
      for (k = 0; k < N; k++)
	{
	  if (votes[k] > mx)
	    {
	      mx = votes[k];
	      val = k;
	      tie = 0;
	    }
	  else if (votes[k] == mx)
	    tie = 1;
	}
      if (tie)
	break;
      s[l] = val;
      stat->steps++;
      if (s_true && s_true[l] != val)
	stat->wrong++;

      for (a = 0; a < nb && fr->wt[a] <= lam; a++)
	{
	  b = fr->idx[lam - fr->wt[a]];
	  if (b >= 0)
	    S[(size_t) a * nb + b] =
	      mono_syn (fr, s, fr->mi[a] + fr->mi[b], fr->mj[a] + fr->mj[b]);
	}
      ret = fr_extract (fr, Phi, npt, S, lam, tmax, e, s);
    }

done:
  free (s);
  free (S);
  free (work);
  free (pc);
  return ret;
}

/* ------------------------------------------------------------------ */
/* 曲線の定義 (係数・指数は元のまま)                                  */
/* ------------------------------------------------------------------ */
//gf256 g=1 elliptic
static const unsigned short el[4][4] =
  { {0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1} };
//gf256 g=1 elloptic
static const unsigned short el2[5][4] =
  { {0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1}, {2, 0, 1, 1} };
//gf8 g=6 Generalized Hermitian
static const unsigned short sc[4][4] =
  { {3, 2, 0, 1}, {2, 4, 0, 1}, {0, 1, 0, 1}, {4, 0, 0, 1} };
//gf8 g=3 klein
static const unsigned short kl[3][4] = { {3, 1, 0, 1}, {0, 3, 0, 1}, {1, 0, 0, 1} };
//gfQ*Q Hermitian
static const unsigned short he[3][4] = { {Q + 1, 0, 0, 1}, {0, Q, 0, 1}, {0, 1, 0, 1} };
//gf16 g=21 #N=121 Generalized Hermitian
static const unsigned short gu[5][4] =
  { {7, 4, 0, 1}, {6, 8, 0, 1}, {4, 1, 0, 1}, {0, 2, 0, 1}, {8, 0, 0, 1} };
//gf32 g=75 #N=497 Generalized Hermitian
static const unsigned short ge[6][4] =
  { {15, 8, 0, 1}, {14, 16, 0, 1}, {12, 1, 0, 1}, {8, 2, 0, 1}, {0, 4, 0, 1},
{16, 0, 0, 1} };
//gf64 g=212 #N=2017 Generalized Hermitian
static const unsigned short gg[7][4] =
  { {31, 8, 0, 1}, {30, 16, 0, 1}, {28, 32, 0, 1}, {24, 1, 0, 1}, {16, 2, 0, 1},
{0, 4, 0, 1}, {32, 0, 0, 1} };
//gf256 g=2413 Generalized Hermitian
static const unsigned short gd[9][4] =
  { {127, 8, 0, 1}, {126, 16, 0, 1}, {124, 32, 0, 1}, {120, 64, 0, 1},
{112, 128, 0, 1}, {96, 1, 0, 1}, {64, 2, 0, 1}, {0, 4, 0, 1}, {128, 0, 0, 1} };
//gf128 g=315 Generalized Hermitian
static const unsigned short cc[8][4] =
  { {63, 8, 0, 1}, {62, 16, 0, 1}, {60, 32, 0, 1}, {56, 64, 0, 1}, {48, 1, 0, 1},
{32, 2, 0, 1}, {0, 4, 0, 1}, {64, 0, 0, 1} };
//gf256 y^(Q+1)=X^8+x^4+x^2+x kummer
static const unsigned short ku[5][4] =
  { {0, 17, 0, 1}, {8, 0, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };
//gf16 kummer
static const unsigned short ku3[5][4] =
  { {0, 5, 0, 1}, {12, 0, 0, 1}, {9, 0, 0, 1}, {6, 0, 0, 1}, {3, 0, 0, 1} };
//gf64 kummer g=56
static const unsigned short ku4[5][4] =
  { {0, 9, 0, 1}, {40, 0, 0, 1}, {33, 0, 0, 1}, {12, 0, 0, 1}, {5, 0, 0, 1} };
static const unsigned short lo[3][4] = { {2, 0, 0, 1}, {1, 0, 0, 3}, {0, 1, 0, 6} };
static const unsigned short lk[6][4] =
  { {0, 2, 0, 1}, {0, 1, 0, 3}, {0, 0, 1, 6}, {3, 1, 0, 1}, {0, 3, 1, 1},
{1, 0, 3, 1} };
//gf32 g=26 #N=157
static const unsigned short ts[3][4] = { {2, 2, 5, 1}, {7, 0, 2, 1}, {0, 9, 0, 1} };
//gf128 g=78 #N=891
static const unsigned short tt[3][4] = { {3, 1, 0, 1}, {13, 0, 0, 1}, {0, 14, 0, 1} };
//gf512 Generalized Hermitian
static const unsigned short gt[10][4] =
  { {255, 16, 0, 1}, {254, 32, 0, 1}, {252, 64, 0, 1}, {248, 128, 0, 1},
{240, 256, 0, 1}, {224, 1, 0, 1}, {192, 2, 0, 1}, {128, 4, 0, 1}, {0, 8, 0, 1},
{256, 0, 0, 1} };
//over gf128 suzuki #N=16384
static const unsigned short su[4][4] =
  { {0, 128, 0, 1}, {0, 1, 0, 1}, {136, 0, 0, 1}, {9, 0, 0, 1} };
//gf32 suzuki #N=1024
static const unsigned short s2[4][4] =
  { {0, 32, 0, 1}, {0, 1, 0, 1}, {36, 0, 0, 1}, {5, 0, 0, 1} };
//gf8 suzuki
static const unsigned short s3[4][4] =
  { {0, 8, 0, 1}, {0, 1, 0, 1}, {10, 0, 0, 1}, {3, 0, 0, 1} };
//y9 = x4 + x2 + x gf64 kummer
static const unsigned short ku2[4][4] =
  { {0, 9, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };
//y^9=x^2+x gf64 g=4
static const unsigned short ku5[3][4] = { {0, 9, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1} };

typedef struct
{
  const char *name;
  const unsigned short (*c)[4];
  int nt;
} CurveDef;

static const CurveDef curves[] = {
  {"el", el, 4}, {"el2", el2, 5}, {"sc", sc, 4}, {"kl", kl, 3},
  {"he", he, 3}, {"gu", gu, 5}, {"ge", ge, 6}, {"gg", gg, 7},
  {"gd", gd, 9}, {"cc", cc, 8}, {"ku", ku, 5}, {"ku3", ku3, 5},
  {"ku4", ku4, 5}, {"lo", lo, 3}, {"lk", lk, 6}, {"ts", ts, 3},
  {"tt", tt, 3}, {"gt", gt, 10}, {"su", su, 4}, {"s2", s2, 4},
  {"s3", s3, 4}, {"ku2", ku2, 4}, {"ku5", ku5, 3}
};

/* ------------------------------------------------------------------ */
int
main (int argc, char **argv)
{
  unsigned int seed =
    (argc > 1) ? (unsigned int) strtoul (argv[1], NULL, 10)
    : (unsigned int) (clock () + time (NULL));
  int nerr = (argc > 2) ? atoi (argv[2]) : E;
  const char *cname = (argc > 3) ? argv[3] : "tt";
  const CurveDef *cd = NULL;
  MP *s;
  PO *pts;
  FR fr;
  FRStat st;
  unsigned short *Phi = NULL, *s0 = NULL, *st_true = NULL, *ev = NULL,
    *dec = NULL, xx, yy, v;
  int *pos = NULL;
  int i, j, k, n, found, ok = 0, ret = EXIT_FAILURE;

  for (i = 0; i < (int) (sizeof (curves) / sizeof (curves[0])); i++)
    if (strcmp (curves[i].name, cname) == 0)
      cd = &curves[i];
  if (!cd || nerr < 0)
    {
      fprintf (stderr, "使い方: %s [seed] [誤り数] [曲線名]\n", argv[0]);
      return EXIT_FAILURE;
    }

  memset (&fr, 0, sizeof (fr));
  gf_init ();
  s = malloc (sizeof (MP));
  pts = malloc (sizeof (PO));
  if (!s || !pts)
    return EXIT_FAILURE;
  set_curve (s, cd->c, cd->nt);

  n = mtrace (s, pts);
  if (n < 0)
    {
      fprintf (stderr, "有理点が %d 個を超えました\n", MAXPT);
      goto end;
    }
  if (fr_setup (&fr, s, nerr > 0 ? nerr : 1) < 0)
    goto end;
  if (nerr > n)
    {
      fprintf (stderr, "誤り数が点の数 %d を超えています\n", n);
      goto end;
    }
  printf ("curve=%s  deg=%d  n=%d  (A,B)=(%d,%d)  g=%d  m=%d  seed=%u\n",
	  cd->name, mdeg (s), n, fr.A, fr.B, fr.g, fr.m, seed);

  /* 検査行列 Phi[k][j] = φ_k(P_j) */
  Phi = malloc ((size_t) fr.nk * n * sizeof (unsigned short));
  s0 = calloc (fr.nk, sizeof (unsigned short));
  st_true = calloc (fr.nb, sizeof (unsigned short));
  ev = calloc (n, sizeof (unsigned short));
  dec = calloc (n, sizeof (unsigned short));
  pos = malloc ((nerr > 0 ? nerr : 1) * sizeof (int));
  if (!Phi || !s0 || !st_true || !ev || !dec || !pos)
    goto end;
  for (k = 0; k < fr.nk; k++)
    for (j = 0; j < n; j++)
      Phi[(size_t) k * n + j] =
	gmul (gpow (pts->z[0][j], fr.mi[k]), gpow (pts->z[1][j], fr.mj[k]));

  /* ランダムな誤り */
  srand (seed);
  for (i = 0; i < nerr;)
    {
      j = rand () % n;
      if (ev[j] == 0)
	{
	  ev[j] = 1 + rand () % (N - 1);
	  pos[i++] = j;
	}
    }
  for (i = 0; i < nerr; i++)
    {
      xx = pts->z[0][pos[i]];
      yy = pts->z[1][pos[i]];
      for (k = 0; k < fr.nb; k++)
	{
	  v = gmul (ev[pos[i]],
		    gmul (gpow (xx, fr.mi[k]), gpow (yy, fr.mj[k])));
	  st_true[k] ^= v;
	  if (k < fr.nk)
	    s0[k] ^= v;
	}
    }

  printf ("error positions / values:\n");
  for (j = 0; j < n; j++)
    if (ev[j])
      printf ("  #%d (%d,%d): %d\n", j, pts->z[0][j], pts->z[1][j], ev[j]);

  found = fr_decode (&fr, Phi, n, s0, st_true, nerr > 0 ? nerr : 1, dec, &st);
  printf ("majority voting: %d syndromes, %d wrong\n", st.steps, st.wrong);
  if (found < 0)
    printf ("decoding failure\n");
  else
    {
      printf ("decoded %d errors:\n", found);
      for (j = 0; j < n; j++)
	if (dec[j])
	  printf ("  #%d (%d,%d): %d\n", j, pts->z[0][j], pts->z[1][j],
		  dec[j]);
      ok = (memcmp (ev, dec, n * sizeof (unsigned short)) == 0);
    }
  printf (ok ? "SUCCESS\n" : "FAILURE\n");
  ret = ok ? EXIT_SUCCESS : EXIT_FAILURE;

end:
  fr_free (&fr);
  free (Phi);
  free (s0);
  free (st_true);
  free (ev);
  free (dec);
  free (pos);
  free (s);
  free (pts);
  return ret;
}