#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

/****** GF(2^m) only ********/
// 5-error-correction

#define V 3 // 変数の数
#define P 256 //項の数の上界
#define Q 4       // 基礎体
#define N Q*Q*Q // 定義体
//#define N Q*Q*Q*Q*Q 
//#define N Q*Q
#define I Q + 1   // 曲線の次数
#define J 8
int K;                             // 項の最大次数
#define H (K + 1) * (K + 2) / 2         // シンドローム行列の横ベクトルの長さ
#define F (J - K + 1) * (J - K + 2) / 2 // シンドローム行列の縦ベクトル
#define U 26
#define E 3
#define TT 32 //項の数（設定値）


typedef struct
{

  unsigned short n[V];
  unsigned short a;
  short t;
} mterm;

typedef struct
{

  mterm x[P];
  short t;

} MP;

typedef struct
{
  unsigned short m[256][256][256];
  short t;

} mvec;

typedef struct
{

  unsigned char z[V][150000];

} PO;

// unsigned short gf[8]={0,1,2,4,3,6,7,5};
// unsigned short fg[8]={0,1,2,4,3,7,5,6};
/*
//nomal
unsigned char gf[N] =
  { 0, 1, 2, 4, 8, 9, 11, 15, 7, 14, 5, 10, 13, 3, 6, 12 };
unsigned char fg[N] =
  { 0, 1, 2, 13, 3, 10, 14, 8, 4, 5, 11, 6, 15, 12, 9, 7 };
*/
/*
unsigned char gf[32]={
0,1,2,4,8,16,23,25,5,10,20,
31,9,18,19,17,21,29,13,26,3,
6,12,24,7,14,28,15,30,11,22,
27};
unsigned char fg[32]={0,1,2,20,3,8,21,24,4,12,9,29,22,18,25,27,5,15,13,14,10,16,30,6,23,7,19,31,26,17,28,11};
*/

//unsigned char gf[16]={0,1,2,4,8,3,6,12,11,5,10,7,14,15,13,9};
//unsigned char fg[16]={0,1,2,5,3,9,6,11,4,15,10,8,7,14,12,13};

//unsigned char gf[64] = {0, 1, 2, 4, 8, 16, 32, 33, 35, 39, 47, 63, 31, 62, 29, 58, 21, 42, 53, 11, 22, 44, 57, 19, 38, 45, 59, 23, 46, 61, 27, 54, 13, 26, 52, 9, 18, 36, 41, 51, 7, 14, 28, 56, 17, 34, 37, 43, 55, 15, 30, 60, 25, 50, 5, 10, 20, 40, 49, 3, 6, 12, 24, 48};
//unsigned char fg[64] = {0, 1, 2, 59, 3, 54, 60, 40, 4, 35, 55, 19, 61, 32, 41, 49, 5, 44, 36, 23, 56, 16, 20, 27, 62, 52, 33, 30, 42, 14, 50, 12, 6, 7, 45, 8, 37, 46, 24, 9, 57, 38, 17, 47, 21, 25, 28, 10, 63, 58, 53, 39, 34, 18, 31, 48, 43, 22, 15, 26, 51, 29, 13, 11};
unsigned char gf[64]={0,1,2,4,8,16,32,27,54,55,53,49,57,41,9,18,36,19,38,23,46,7,14,28,56,43,13,26,52,51,61,33,25,50,63,37,17,34,31,62,39,21,42,15,30,60,35,29,58,47,5,10,20,40,11,22,44,3,6,12,24,48,59,45,};
unsigned char fg[64]={0,1,2,57,3,50,58,21,4,14,51,54,59,26,22,43,5,36,15,17,52,41,55,19,60,32,27,7,23,47,44,38,6,31,37,46,16,35,18,40,53,13,42,25,56,63,20,49,61,11,33,29,28,10,8,9,24,12,48,62,45,30,39,34,};

// unsigned short gf[128]={0,1,2,4,8,16,32,64,65,67,71,79,95,127,63,126,61,122,53,106,21,42,84,105,19,38,76,89,115,39,78,93,123,55,110,29,58,116,41,82,101,11,22,44,88,113,35,70,77,91,119,47,94,125,59,118,45,90,117,43,86,109,27,54,108,25,50,100,9,18,36,72,81,99,7,14,28,56,112,33,66,69,75,87,111,31,62,124,57,114,37,74,85,107,23,46,92,121,51,102,13,26,52,104,17,34,68,73,83,103,15,30,60,120,49,98,5,10,20,40,80,97,3,6,12,24,48,96};
// unsigned short fg[128]={0,1,2,122,3,116,123,74,4,68,117,41,124,100,75,110,5,104,69,24,118,20,42,94,125,65,101,62,76,35,111,85,6,79,105,46,70,90,25,29,119,38,21,59,43,56,95,51,126,114,66,98,102,18,63,33,77,88,36,54,112,16,86,14,7,8,80,9,106,81,47,10,71,107,91,82,26,48,30,11,120,72,39,108,22,92,60,83,44,27,57,49,96,31,52,12,127,121,115,73,67,40,99,109,103,23,19,93,64,61,34,84,78,45,89,28,37,58,55,50,113,97,17,32,87,53,15,13};

//unsigned char gf[256]={0,1,2,4,8,16,32,64,128,29,58,116,232,205,135,19,38,76,152,45,90,180,117,234,201,143,3,6,12,24,48,96,192,157,39,78,156,37,74,148,53,106,212,181,119,238,193,159,35,70,140,5,10,20,40,80,160,93,186,105,210,185,111,222,161,95,190,97,194,153,47,94,188,101,202,137,15,30,60,120,240,253,231,211,187,107,214,177,127,254,225,223,163,91,182,113,226,217,175,67,134,17,34,68,136,13,26,52,104,208,189,103,206,129,31,62,124,248,237,199,147,59,118,236,197,151,51,102,204,133,23,46,92,184,109,218,169,79,158,33,66,132,21,42,84,168,77,154,41,82,164,85,170,73,146,57,114,228,213,183,115,230,209,191,99,198,145,63,126,252,229,215,179,123,246,241,255,227,219,171,75,150,49,98,196,149,55,110,220,165,87,174,65,130,25,50,100,200,141,7,14,28,56,112,224,221,167,83,166,81,162,89,178,121,242,249,239,195,155,43,86,172,69,138,9,18,36,72,144,61,122,244,245,247,243,251,235,203,139,11,22,44,88,176,125,250,233,207,131,27,54,108,216,173,71,142};
//unsigned char fg[256]={0,1,2,26,3,51,27,199,4,224,52,239,28,105,200,76,5,101,225,15,53,142,240,130,29,194,106,249,201,9,77,114,6,139,102,48,226,37,16,34,54,148,143,219,241,19,131,70,30,182,195,126,107,40,250,186,202,155,10,121,78,229,115,167,7,192,140,99,103,222,49,254,227,153,38,180,17,146,35,137,55,209,149,207,144,151,220,190,242,211,20,93,132,57,71,65,31,67,183,164,196,73,127,111,108,59,41,85,251,134,187,62,203,95,156,160,11,22,122,44,79,213,230,173,116,244,168,88,8,113,193,248,141,129,100,14,104,75,223,238,50,198,255,25,228,166,154,120,39,185,181,125,18,69,147,218,36,33,138,47,56,64,210,92,150,189,208,206,145,136,152,179,221,253,191,98,243,87,212,172,21,43,94,159,133,61,58,84,72,110,66,163,32,46,68,217,184,124,165,119,197,24,74,237,128,13,112,247,109,162,60,83,42,158,86,171,252,97,135,178,188,205,63,91,204,90,96,177,157,170,161,82,12,246,23,236,123,118,45,216,80,175,214,234,231,232,174,233,117,215,245,235,169,81,89,176};


unsigned short S[256][256] = {0};

unsigned int cnt = 0;
PO p;
mterm base[1024] = {0};
// static mvec g = {0};

int tdegv(mvec a)
{
  int d = 0, e = 0;

  for (int i = 0; i < TT; i++)
  {
    for (int j = 0; j < TT; j++)
    {
      for (int k = 0; k < TT; k++)
        if (a.m[i][j][k] > 0)
        {
          d = (i + j + k);
          printf("d=%d\n", d);
          if (e < d)
            e = d;
        }
    }
  }

  return e;
}

int tdeg(MP f)
{
  int i, j, k=0;

  for (i = 0; i < P; i++)
  {
    if (f.x[i].a > 0)
    {
      j = f.x[i].n[0] + f.x[i].n[1] + f.x[i].n[2];
      if (k < j)
        k = j;
    }
  }

  return k;
}

MP m2p(mvec a)
{
  int i, j, k, count = 0;
  MP p = {0};

  for (i = 0; i < TT; i++)
  {
    for (j = 0; j < TT; j++)
    {
      for (k = 0; k < 1; k++)
        if (a.m[i][j][k] > 0)
        {
          p.x[count].n[0] = i;
          p.x[count].n[1] = j;
          p.x[count].n[2] = k;
          p.x[count++].a = a.m[i][j][k];
        }
    }
  }

  return p;
}

mvec p2m(MP p)
{
  int i, j, k;
  mvec v = {0};

  for (j = 0; j < P; j++)
  {
    //for (i = 0; i < V; i++)
    {
      if (p.x[j].a > 0)
        v.m[p.x[j].n[0]][p.x[j].n[1]][p.x[j].n[2]] ^= p.x[j].a;
    }
  }

  return v;
}

// ランダム多項式の生成
MP minit(int a)
{
  int ii = 0, jj = 0, kk = 0, count = 0, k = 0, n[V] = {0};
  mvec gg = {0};

  printf("in ginit\n");

  gg.m[0][0][0]=rand()%(N-1)+1;
  while (count < a-1)
  {
    ii = rand() % (K);
    jj = rand() % (K);
    kk = 0; // rand() % K;
    printf("ii=%d,jj=%d,kk=%d %d\n", ii, jj, kk, count);
    printf("in whule\n");
    // int j = rand() % (K);
    if (gg.m[ii][jj][kk] == 0 && (ii + jj + kk) < K)
    {
      int l = 1; //rand() % (2); // or N;
      printf("Ah!\n");
      if (l > 0)
      {
        gg.m[ii][jj][kk] = l;
        count++;
      }
    }
  }
  gg.t = a;

  MP f = m2p(gg);

  return f;
}

MP mkpol(int a)
{
  int i, j, k, count = 0;
  MP w = {0};

  // minit();
  while (count < a)
  {
    i = rand() % K;
    j = rand() % K;
    k = 0; // rand() % K;
    if (i + j + k < K)
    {
      w.x[count].a = rand() % 2; //(N-1)+1;
      if (w.x[count].a > 0)
      {
        w.x[count].n[0] = i;
        w.x[count].n[1] = j;
        w.x[count].n[2] = k;
        count++;
      }
    }
  }
  /*
  j = 1;
  for (i = 0; i < a; i++)
  {
    for (j = 1; j < a; j++)
    {
      if (w.x[i].n[0] == w.x[j].n[0] && w.x[i].n[1] == w.x[j].n[1] && w.x[i].n[2] == w.x[j].n[2] && w.x[j].a>0)
        w.x[j].a = 0;
    }
  }
*/

  w.t = a;

  return w;
}

void printm(MP f)
{

  for (int i = 0; i < P; i++)
    if (f.x[i].a > 0)
      printf("%d*X^%d*Y^%d*Z^%d+", f.x[i].a, f.x[i].n[0], f.x[i].n[1], f.x[i].n[2]);
}

void printv(mvec a)
{
  for (int i = 0; i < TT; i++)
  {
    for (int j = 0; j < TT; j++)
    {
      for (int k = 0; k < 1; k++)
        if (a.m[i][j][k] > 0)
          printf("%d*X^%d*Y^%d*Z^%d+", a.m[i][j][k], i, j, k);
    }
  }
}

short v2a(mterm a)
{
  int i, j;

  if (a.a == 0)
    return 0;
  if (a.a > N)
    return -1;

  // printf("aa=%d\n",a.a);
  for (int j = 0; j < N; j++)
  {
    if (gf[j] == a.a && a.a > 0)
    {
      // printf("j==%d\n",j);
      return j - 1;
    }
  }
  printf("v2a baka %d\n", a.a);
  exit(1);
}

void mprintsage(MP f)
{
  printf("poly=");
  for (int i = 0; i < P; i++)
    if (f.x[i].a > 0)
      printf("+B('a^%d')*X^%d*Y^%d*Z^%d", v2a(f.x[i]), f.x[i].n[0], f.x[i].n[1], f.x[i].n[2]);
}

void mprintpol(MP f)
{
  printf("poly=");
  for (int i = 0; i < P; i++)
    if (f.x[i].a > 0)
      printf("+%d*X^%d*Y^%d*Z^%d", (f.x[i].a), f.x[i].n[0], f.x[i].n[1], f.x[i].n[2]);
}

void mprintpoln(MP f)
{
  printf("poly=");
  for (int i = 0; i < P; i++)
    if (f.x[i].a > 0)
      printf("+%d*X^%d*Y^%d*Z^%d", (f.x[i].a), f.x[i].n[0], f.x[i].n[1], f.x[i].n[2]);
printf("\n");
}

void vprintsage(mvec a)
{
  int i, j, k;
  mterm b;

  printf("poly=");
  for (int i = 0; i < TT; i++)
  {
    for (int j = 0; j < TT; j++)
    {
      for (int k = 0; k < 1; k++)
      {
        if (a.m[i][j][k] > 0)
        {
          b.a = a.m[i][j][k];
          b.n[0] = i;
          b.n[1] = j;
          b.n[2] = k;
          int jj = v2a(b);
          // printf("%d,==ba\n",b.a);
          // printf ("X**%d+", i); //for GF2
          printf("B('a^%d')*X**%d*Y**%d*Z**%d+", jj, b.n[0], b.n[1], b.n[2]); // for GF(2^m)
        }
      }
    }
  }
}


/*
 * Multiplication in GF(2^8)
 * http://en.wikipedia.org/wiki/Finite_field_arithmetic
 * Irreducible polynomial m(x) = x8 + x4 + x3 + x + 1
 *
 * NOTE: This function can be easily replaced with a look up table for a speed
 *       boost, at the expense of an increase in memory size (around 65 KB). See
 *       the aes.h header file to find the macro definition.
 *
 */
unsigned short gmult(unsigned short a, unsigned short b)
{

  unsigned short p = 0, i = 0, hbs = 0;

  for (i = 0; i < 9; i++)
  {
    if (b & 1)
    {
      p ^= a;
    }

    hbs = a & (0x80);
    a <<= 1;
    if (hbs)
      a ^= 0x1b; // 0000 0001 0001 1011
    b >>= 1;
  }

  return (unsigned short)p;
}


int mlt(int x, int y)
{

  if (x == 0 || y == 0)
    return 0;

  return ((x + y - 2) % (N - 1)) + 1;
}

int mltn(int n, int x)
{
  int i, j;

  if (n == 0)
  {
    return 1;
  }
  if (x == 0)
  {
    return 0;
  }
  else
  {
    i = x;
    for (j = 0; j < n - 1; j++)
      i = mlt(i, x);

    return i;
  }
}

unsigned short
oinv(unsigned short a)
{
  int i;

  if (a == 0)
    return 0;

  for (i = 0; i < N; i++)
  {
    if (gf[mlt(fg[a], i)] == 1)
      return (unsigned short)i;
  }
}

int inv2(int a, int b)
{
  int i = 0;

  if (a == 0)
    return 0;

  for (i = 0; i < N; i++)
  {
    if (b == gf[mlt(fg[a], i)])
      return i;
  }
}

void param(int n, int g)
{
  int i, j, h, ij, t, delta, ips;

  //  g=6;
  j = I - 2;
  //  ij=k+g-1;
  //  ij=1;
  //  exit(1);
  //    n-=4;
  printf("n=%d ", n);
  printf("k=%d\n", U);
  printf("d=%d\n", U - g + 1);
  printf("t=%d~%d\n", (U - g) / 2);

  delta = 1;
  ips = 0;
  while (delta * I < Q * Q * Q)
  {
    for (ips = 0; ips < I; ips++)
    {
      if (U + ((I * (I - 1)) / 2) == delta * I + ips)
        printf("ips=%d delta=%d\n", ips, delta);
    }
    delta++;
  }
}

void vec_diff(unsigned short a[N], unsigned short b[N])
{
  /* Calcurate the difference of two vectors. Be caution that b[N] changes. */
  for (int i = 0; i < N; i++)
  {
    b[i] ^= a[i];
  }
}

int gauss()
{
  unsigned short m[N][N] = {{7, 2, 5}, {2, 5, 2}, {5, 2, 7}}; // The matrix
  unsigned short b[N] = {5, 7, 0};
  unsigned short mm[N] = {0};

  printf("The coefficient matrix is : \n");
  for (int i = 0; i < N; i++)
  {
    for (int j = 0; j < N; j++)
    {
      printf("%d ", m[i][j]);
      if (j == N - 1)
      {
        printf("\n");
      }
    }
  }

  printf("\nUse Gauss method to solve equations : \n");
  for (int i = 0; i < N; i++)
  {
    for (int j = i + 1; j < N; j++)
    {
      unsigned short coef = mlt(fg[m[j][i]], oinv(fg[m[i][i]]));
      unsigned short del[N];

      for (int k = 0; k < N; k++)
      {
        del[k] = gf[mlt(fg[m[i][k]], coef)];
      }
      // for(int ii=0;ii<N;ii++)
      // mm[ii]=m[j][ii];
      vec_diff(del, m[j]);
      b[j] ^= gf[mlt(fg[b[i]], coef)];
    }
  }

  for (int i = N - 1; i >= 0; i--)
  {
    unsigned short x = gf[oinv(fg[m[i][i]])];
    m[i][i] = gf[mlt(fg[m[i][i]], fg[x])];
    b[i] = gf[mlt(fg[b[i]], fg[x])];

    for (int j = 0; j < i; j++)
    {
      b[j] ^= gf[mlt(fg[b[i]], fg[m[j][i]])];
      m[j][i] = 0;
    }
  }

  for (int i = 0; i < N; i++)
  {
    for (int j = 0; j < N; j++)
    {
      printf("%d ", m[i][j]);
      if (j == N - 1)
      {
        printf("\n");
      }
    }
  }

  for (int i = 0; i < N; i++)
  {
    printf("%d ", b[i]);
  }

  return 0;
}

mterm term(MP f, unsigned int i)
{

  return f.x[i];
}

int mterms(mvec a)
{
  int i, j, k, count = 0;

  for (i = 0; i < TT; i++)
  {
    for (j = 0; j < TT; j++)
    {
      for (k = 0; k < 1; k++)
        if (a.m[i][j][k] > 0)
          count++;
    }
  }

  return count;
}

int terms(MP f)
{
  int i, j, k = 0, flg;

  for (i = 0; i < P; i++)
  {
    flg = 0;
    //for (j = 0; j < V; j++)
    {
      if (f.x[i].a > 0)
        k++;
    }
  }

  return k;
}

unsigned short
degterm(mterm z)
{
  int j, k;
  // mterm z;
  unsigned short c = 0;

  //   z=term(f,i);
  for (j = 0; j < V; j++)
  {
    if (z.n[j] > 0)
      c += z.n[j];
  }

  return c;
}

MP mterml(MP f, mterm m)
{
  int i, j, k;

  for (i = 0; i < P; i++)
  {
    if (f.x[i].a > 0){
    for (j = 0; j < V; j++)
      f.x[i].n[j] += m.n[j];
      f.x[i].a = gf[mlt(fg[f.x[i].a], fg[m.a])];
    }
  }

  return f;
}

mterm mLT(MP f)
{
  int i, j = 0, k, l, ll = mterms(p2m(f));
  mterm m = {0}, mm;

  for (i = 0; i < ll; i++)
  {
    mm = term(f, i);
    k = degterm(mm);
    if (j < K && f.x[i].a>0)
    {
      m = f.x[i];
    }
    else if (j == k)
    {
      for (l = 0; l < V; l++)
        if (m.n[l] < f.x[i].n[l] && f.x[i].a > 0)
        {
          m = f.x[i];
          return m;
        }
    }
  }

  return m;
}


/*
MP sort(mvec m)
{
  MP f = {0};
  int count = m.t, deg = tdegv(m);
  mterm tmp = {0};

  printf("deg=%d\n", tdegv(m));

  for (int i = 0; i < TT; i++)
  {
    for (int j = 0; j < TT; j++)
    {
      for (int k = 0; k < TT; k++)
      {
        if (m.m[i][j][k] > 0 && f.x[count].a == 0 && deg < i + j + k)
          f.x[count].a = m.m[i][j][k];

        if (f.x[count].a > 0 && m.m[i][j][k] > 0 && deg < i + j + k)
        {
          tmp = f.x[count];
          if (i >= j && j >= k)
          {
            f.x[count].a = m.m[i][j][k];
            f.x[count].n[0] = i;
            f.x[count].n[1] = j;
            f.x[count].n[2] = k;
            count--;
            f.x[count] = tmp;
          }
        }
        if (i + j + k == deg)
        {
          f.x[m.t].a = m.m[i][j][k];
          f.x[m.t].n[0] = i;
          f.x[m.t].n[1] = j;
          f.x[m.t].n[2] = k;
        }
      }
    }
  }
  return f;
}
*/

MP mdel(MP f, mterm m)
{
  int i, j, k;

  m = mLT(f);
  for (i = 0; i < terms(f); i++)
  {
    if (m.n[0] == f.x[i].n[0] && m.n[1] == f.x[i].n[1] && m.n[2] == f.x[i].n[1])
    {
      for (j = 0; j < V; j++)
        f.x[i].n[j] = 0;
      f.x[i].a ^= m.a;
    }
  }

  return f;
}

MP lex(MP f)
{
  MP g = {0};
  int i, j, k;
  mterm m = {0};

  for (i = 0; i < terms(f); i++)
  {
    m = mLT(f);
    f = mdel(f, m);
    g.x[i] = m;
  }

  return g;
}

int rank(int mat[][100], int n)
{
  int ltmp[100], tmp, a_tmp[100], b_tmp[100];
  int i, j, k;
  int count;
  int all_zero;

  for (i = 0; i < n; i++)
  {
    all_zero = 0;
    if (mat[i][i] == 0)
    {
      for (j = 0; j < n; j++)
      {
        if (mat[j][i] != 0)
        {
          for (k = 0; k < n; k++)
          {
            tmp = mat[i][k];
            mat[i][k] = mat[j][k];
            mat[j][k] = tmp;
          }
        }
        else if (j == n - 1)
          all_zero = 1;
      }
    }

    if (!all_zero)
    {
      for (j = i + 1; j < n; j++)
      {
        for (k = 0; k < n; k++)
        {
          a_tmp[k] = mlt(mat[i][k], mat[j][i]);
          b_tmp[k] = mlt(mat[j][k], mat[i][i]);
        }
        for (k = 0; k < n; k++)
          mat[j][k] = fg[gf[b_tmp[k]] ^ gf[a_tmp[k]]];
      }
    }
  }

  count = 0;
  for (i = 0; i < n; i++)
  {
    if (mat[i][n] == 0)
      count++;
  }

  return (n - count);
}

int mdeg(MP f)
{
  int i, tmp = 0, j, k=0;

  for (i = 0; i < 256; i++)
  {
    tmp=0;
    for (j = 0; j < V; j++)
    {
      tmp += f.x[i].n[j];
    }
    if (k < tmp)
      k = tmp;
  }

  return k;
}

mterm mtermul2(mterm a, mterm b)
{
  mterm c = {0};

  c.n[0] = a.n[0] + b.n[0];
  c.n[1] = a.n[1] + b.n[1];
  c.a = gf[mlt(fg[a.a], fg[b.a])];

  return c;
}

MP mtermul(MP f, mterm o)
{
  int i, j, k, l = mterms(p2m(f));

  for (i = 0; i < l; i++)
  {
    for (j = 0; j < V; j++)
      f.x[i].n[j] += o.n[j];
    f.x[i].a = gf[mlt(fg[f.x[i].a], fg[o.a])];
  }

  return f;
}

unsigned short
otrace(mterm a, int i, int j, int k)
{
  unsigned short u;

  // if (i == 0 && j == 0)
  //   return 0;

  u =
      mlt(mlt(mltn(a.n[0], i), mltn(a.n[1], j)),
          mlt(mltn(a.n[2], k), fg[a.a]));

  if (a.n[0] == 0 && a.n[1] == 0 && a.n[2] == 0)
    return a.a;

  return gf[u];
}

unsigned int
mtrace(MP f)
{
  int i, j, k, ii;
  unsigned int u, n, count = 0, f1, f2, f3, f4;
  mterm o[4];

  u = 0;
  n = 6; //terms(f);
  printf("%d\n", n);
  // exit(1);

  /*
       i=0;j=1;k=0;
       for(ii=0;ii<n;ii++){
       u^=otrace(f.x[ii],0,1,0);
       printf("%d\n",u);
       }
  //     u^=1;
       if(u==0){
          printf("%d %d %d\n",0,1,0);
       p.z[0][count]=0;
       p.z[1][count]=1;
       p.z[2][count]=0;
       count++;
       }
     //exit(1);

       k=0;i=1;u=0;
       for(j=0;j<N;j++){
       for(ii=0;ii<n;ii++)
       u^=otrace(f.x[ii],1,j,0);
       //u^=1;
       if(u==0){
       printf("%d %d %d\n",1,j,0);
       p.z[0][count]=1;
       p.z[1][count]=j;
       p.z[2][count]=0;
       count++;
       }
       u=0;
       }
     //exit(1);
  */

  k = 1;
  u = 0;
  for (i = 0; i < N; i++)
  {
    for (j = 0; j < N; j++)
    {
      for (ii = 0; ii < n; ii++)
        u ^= otrace(f.x[ii], i, j, 1);
      // u^=1;
      if (u == 0)
      {
        printf("%d %d %d\n", i, j, k);

        p.z[0][count] = i;
        p.z[1][count] = j;
        p.z[2][count] = 1;

        count++;
      }
      u = 0;
    }
  }

  return count;
}

mterm obase(int a, int b)
{
  int i, j, k;
  mterm c = {0};

  c.n[0] = a;
  c.n[1] = b;

  return c;
}

int bases(int a)
{
  int i = 0, j = 0, count = 0;

  for (i = 0; i < N - 1; i++)
  {
    for (j = 0; j < N - 1; j++)
    {
      //      if(i+j<a){
      base[count].n[0] = i;
      base[count++].n[1] = j;
      //    }
      if (count > N * N)
      {
        printf("baka\n");
        break;
      }
    }
  }

  //  printf("count=%d\n",count);
  //  exit(1);

  return count;
}

int mkbase(mterm *aa)
{
  int i, j, k, l, count;
  int d[256][2] = {0};
  int bb[256][2] = {0};

  count = 1;

  for (i = 0; i < 20; i++)
  {
    k = 0;
    j = i;
    while ((d[i][0] + d[i][1]) < i && i < 5)
    {
      d[k][1] = k;
      d[k][0] = j - k;
      printf("k1=%d %d\n", j - k, k);
      k++;
    }
    for (l = 0; l < k; l++)
    {
      bb[count][0] = d[l][0];
      bb[count++][1] = d[l][1];
      //    printf("a%d %d\n",d[l][0],d[l][1]);
    }

    if (i > 4)
    {
      l = i - 4;
      j = 4;
      while (d[i][0] + d[i][1] < i && l < N - 1)
      {
        d[k][0] = j;
        d[k][1] = l;
        k++;
        j--;
        l++;
        printf("k2=%d", k);
        if (j < 0)
          break;
      }
      for (l = 0; l < k; l++)
      {
        bb[count][0] = d[l][0];
        bb[count++][1] = d[l][1];
        //    printf("a%d %d\n",d[l][0],d[l][1]);
      }
    }
  }

  for (i = 0; i < 15 * 15; i++)
    printf("d=%d %d\n", bb[i][0], bb[i][1]);
  // exit(1);

  for (i = 0; i < 15 * 15; i++)
  {
    printf("%d %d\n", bb[i][0], bb[i][1]);
    // for(j=0;j<N-1;j++){
    //   if(bb[i][0]+bb[i][1]<10){
    aa[i] = obase(bb[i][0], bb[i][1]);
    aa[i].a = 1;
    //      }
    // }
  }
  // exit(1);

  return count;
}

int test(unsigned short x, unsigned short y)
{
  int count = 0, f1, f2, f3;

  f1 = gf[mlt(x, x)];
  f2 = gf[mlt(3, x)];
  f3 = gf[mlt(6, y)];

  if ((f1 ^ f2 ^ f3) == 0)
  {
    printf("%d %d\n", gf[x], gf[y]);
    count++;
  }

  return count;
}

MP define_curve(void)
{
  int i, j, k;
  MP s = {0};

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

  // hermite
  s.x[0].n[0] = Q + 1;
  s.x[1].n[1] = Q + 1;
  s.x[2].n[2] = Q + 1;

  return s;
}

void anybear(mvec a)
{
  for (int i = 0; i < TT; i++)
    printf("y^%d ", i);
  for (int i = 0; i < TT; i++)
  {
    printf("x^%d ", i);
    for (int j = 0; j < TT; j++)
      printf("%d ", a.m[i][j]);
    printf("\n");
  }
}

mvec madd(mvec a, mvec b)
{
  int i, j, k;
  mvec c = {0};

  for (i = 0; i < TT; i++)
  {
    for (j = 0; j < TT; j++)
    {
      for (int k = 0; k < 1; k++)
        c.m[i][j][k] ^= a.m[i][j][k] ^ b.m[i][j][k];
    }
  }

  return c;
}

int meq(mvec a, mvec b)
{
  int i, j, k;
  mvec c = {0};

  for (i = 0; i < TT; i++)
  {
    for (j = 0; j < TT; j++)
    {
      for (int k = 0; k < 1; k++)
        if (a.m[i][j][k] != b.m[i][j][k])
          return -1;
    }
  }

  return 1;
}

// aに何をかけたらbになるか
unsigned short
equ(unsigned short a, unsigned short b)
{
  int i;

  if(a==0 || b==0)
  return 0;
  //for(int i=0;i<N;i++)
  //if(gf[mlt(fg[a],i)]==b)
  //return gf[i];
  return gf[mlt(oinv(a), fg[b])];
}

// リーディグタームを抽出(default)
mterm vLT(MP f)
{
  int i, j, k = 0, count = 0;
  mterm t = {0}, tmp[100] = {0};

  // k = deg (o2v (f));
  for (i = 0; i < P; i++)
  {
    {
      //
      if (f.x[i].a > 0)
      {
        printf("avlt=%d %d %d %d\n", i, f.x[i].a, f.x[i].n[0], f.x[i].n[1]);
        //
        // if (k < f.x[i].n[0] + f.x[i].n[1] + f.x[i].n[2])
        if (k < f.x[i].n[0]) // && k < f.x[i].n[0]+f.x[i].n[1] + f.x[i].n[2])
        {
          // if (t.n[1] < f.x[i].n[1])
          {
            t.n[0] = f.x[i].n[0];
            t.n[1] = f.x[i].n[1];
            t.n[2] = f.x[i].n[2];
            k = f.x[i].n[1]; // + f.x[i].n[0] + f.x[i].n[2];
            t.a = f.x[i].a;
          }
        }

        if (k == f.x[i].n[1]) // f.x[i].n[0] + f.x[i].n[1] + f.x[i].n[2])
        {
          if (t.n[1] < f.x[i].n[1])
          {
            t.n[0] = f.x[i].n[0];
            t.n[1] = f.x[i].n[1];
            t.n[2] = f.x[i].n[2];
            k = f.x[i].n[1]; //+ f.x[i].n[0] + f.x[i].n[2];
            t.a = f.x[i].a;
          }
        }
      }
    }
  }

  return t;
}

mterm mdivLT(MP f, mterm m)
{
  int i, j, k;
  mterm g = {0};
  mterm mm = {0}; // vLT(m2v(f));
  mterm null={0};

  printm((f));
  printf("\n");
  //for (i = 0; i < TT; i++)
  {
    mm = vLT(f);
    if (mm.a == 0)
      return null;
    printf("in glt1 %dx^%dy^%dz^%d\n", mm.a, mm.n[0], mm.n[1], mm.n[2]);
    printf("in glt! %dx^%dy^%dz^%d\n", m.a, m.n[0], m.n[1], m.n[2]);
    if ((mm.n[0] >= m.n[0]) && (mm.n[1] >= m.n[1]) && (mm.n[2] >= m.n[2]))
    {
      g.n[0] = mm.n[0] - m.n[0];
      g.n[1] = mm.n[1] - m.n[1];
      g.n[2] = mm.n[2] - m.n[2];
      g.a = equ(m.a, mm.a);
    }else{
    return null;
    }
  }

  printf("in glt3 %dx^%dy^%dz^%d\n", g.a, g.n[0], g.n[1], g.n[2]);
  // exit(1);
  return g;
}

MP oadd(MP f, mterm o)
{
  int i, j, k;
  for (i = 0; i < TT; i++)
  {
    if (f.x[i].n[0] == o.n[0] && f.x[i].n[1] == o.n[1] && f.x[i].n[2] == o.n[2])
      f.x[i].a ^= o.a;
  }

  return f;
}



mterm terml(mterm a, mterm b)
{
  mterm r = {0};

  r.a = gf[mlt(fg[a.a], fg[b.a])];
  r.n[0] = a.n[0] + b.n[0];
  r.n[1] = a.n[1] + b.n[1];
  r.n[2] = a.n[2] + b.n[2];

  return r;
}

mvec vmul(MP f, MP g)
{
  mvec c = {0},a=p2m(f),b=p2m(g);
  int i, j, k, l, m;

  for(m=0;m<1;m++){
  for (i = 0; i < TT; i++)
  {
    for(int u=0;u<TT;u++){
    for (j = 0; j < TT; j++)
    {
      l=0;
      for (k = 0; k < TT; k++){
      if(a.m[i][u][m]>0 && b.m[k][j][m]>0)
      {
       c.m[i][j][m] ^= gf[mlt(fg[a.m[u][k][m]],fg[b.m[k][j][m]])];
      //printf("l=%d\n",l);
      }
      }
    }
    }
  }
  }

return c;
}

MP mmul(MP a, MP b)
{
  int i, j, k, d = 0;
  MP c = {0};
  mvec m={0};
  mterm t = {0};

  for (i = 0; i < P; i++)
  {
    for (j = 0; j < P; j++)
    {
      if (a.x[i].a > 0 && b.x[j].a > 0)
        c.x[d++] = terml(a.x[i], b.x[j]);
      //if (a.x[i].a > 0 && b.x[j].a > 0)
      //  m.m[a.x[i].n[0]+b.x[j].n[0]][a.x[i].n[1]+b.x[j].n[1]][0] ^= gf[mlt(fg[a.x[i].a], fg[b.x[j].a])];

    }
  }
  c = m2p(p2m(c));

  return c;
}


// 多項式の掛け算
MP pmul(MP f, MP g)
{

  // assert (vec_verify (f));
  // assert (vec_verify (g));
  mterm t = {0};
  MP h = {0}, e = {0}, r = {0};

  // for (int i = 0; i < 2; i++)
  //     printf("%d\n", g.x[i]);
  //  exit(1);

  for (int i = 0; i < P; i++)
  {
    t = (g.x[i]);
    // t.n = i;
    //  t.n=i;
    if (t.a > 0 && t.a < N)
    {
      printf("t[%d]=%d,%d,%d,%d\n", i, t.a, t.n[0], t.n[1], t.n[2]);
      e = mterml(f, t);
      h = m2p(madd(p2m(h), p2m(e)));
      printm((h));
      printf(" =h\n");
    }
  }
  printm((f));
  printf(" =hf!\n");
  printm((g));
  printf(" =hg!\n");
  printm((h));
  printf(" =hh!\n");

  return h;
}


unsigned short gcd(unsigned short a, unsigned short b)
{
  int r, tmp;

  /* 自然数 a > b を確認・入替 */
  if (a < b)
  {
    tmp = a;
    a = b;
    b = tmp;
  }

  /* ユークリッドの互除法 */
  r = (a % b);
  while (r != 0)
  {
    a = b;
    b = r;
    r = (a % b);
  }

  /* 最大公約数を出力 */
  //printf("最大公約数 = %d\n", b);
  if(b!=1)
  {
    printf("(a,b)!=1\n");
    return -1;
  }

  return b;
}


// 整数の逆数
short inv(short a, short n)
{

    if(gcd(a,n)!=1){
        printf("(a,n)!=1\n");
        return -1;
    }
    short d = n;
    short x = 0;
    short s = 1;
    while (a != 0)
    {
        short q = d / a;
        short r = d % a;
        d = a;
        a = r;
        short t = x - q * s;
        x = s;
        s = t;
    }
    short gcd = d; // $\gcd(a, n)$

    return ((x + n) % (n / d));
}


typedef struct
{
  MP f;
  MP g;
} pair;

mterm max(MP f){
int i,j,k[V]={0},n[V]={0};
mterm m={0};

  for(i=0;i<256;i++){
    for(j=0;j<V;j++){
      k[j]=f.x[i].n[j];
      if(n[j]<k[j])
        n[j]=k[j];
    }
  }
  for(i=0;i<V;i++)
    m.n[i]=n[i];

  return m;
}

mvec s_ply(MP f,MP g){
mterm n=max(f);
mterm m=max(g);
int i,k[V]={0};
mterm t={0};

  for(i=0;i<V;i++){
    if(n.n[i]<m.n[i])
      k[i]=m.n[i];
    if(n.n[i]>=m.n[i])
      k[i]=n.n[i];
  }
  for(i=0;i<V;i++)
  t.n[i]=k[i];

  f=mterml(f,t);
  g=mterml(g,t);
  
  return madd(p2m(f),p2m(g));
}


MP vmod(MP f, MP g)
{
    MP h = {0};
    mterm b = {0}, c = {0};

    if (mdeg(g) == 0)
        return g;
    // printf("vmod-bl=%d k=%d\n",deg(f),deg(g));
    if (mdeg((f)) < mdeg((g)))
    {
        //    exit(1);
        return f;
    }

    b = vLT(g);

    //mprintsage(g);
    printf("%d %d %d %d\n",vLT(g).a,vLT(g).n[0],vLT(g).n[1],vLT(g).n[2]);
     printf(" ogooo\n");
    printf("%d %d %d %d\n",vLT(f).a,vLT(f).n[0],vLT(f).n[1],vLT(f).n[2]);
     printf(" agaaa\n");
    while (1)
    {
        //b = vLT(g);
        // printf("@\n");
        c = mdivLT(f, b);
        printf("%d ",c.a);
        for(int i=0;i<V;i++)
        printf("%d,",c.n[i]);
        printf("\n");
        h = mterml((g), c);
        f = m2p(madd(p2m(f), p2m(h)));
        mprintsage((h));
        printf(" ===h\n");
        mprintsage((f));
        printf(" ===f\n");
        if (mdeg((f)) == 0 || mdeg((h)) == 0)
        {
            break;
        }

        if (multideg(c) == 0)
            break;
    }
    // printf("vmod-baka== %d %d\n",deg(f),deg(g));
    return f;
}


//モニック多項式にする
MP coeff(MP f,  short d)
{
  int i;

  for (i = 0; i < 256; i++)
    f.x[i].a = (f.x[i].a*inv(d,N))%N;

  return f;
}

int multideg(mterm m){

  return m.n[0]+m.n[1]+m.n[2];
}

//多項式の商を取る
MP vdiv(mvec f, mvec g)
{

  int i = 0, j, n, k;
  mvec h = {0}, e = {0};
  MP tt = {0};
  mterm a, b = {0}, c = {0};

  if (mdeg(m2p(f)) == 0 && vLT(m2p(g)).a == 0)
  {
    printf("baka^\n");
    //return f;
    exit(1);
  }
  if (vLT(m2p(g)).a == 0)
  {
    exit(1);
  }
  if (mdeg(m2p(g)) == 0 && mLT(m2p(g)).a > 1)
    return (coeff(m2p(f), vLT(m2p(g)).a));

  k = mdeg(m2p(g));
  b = vLT(m2p(g));
  if (b.a == 1 && multideg((b)) == 0)
    return m2p(f);
  if (b.a == 0 && multideg((b)) == 0)
  {
    printf("baka in vdiv\n");
    exit(1);
  }
  if (mdeg(m2p(f)) < mdeg(m2p(g)))
  {
    return m2p(f);
    //  a=LT(f);
  }

  i = 0;
  while (1)
  {
    c = mdivLT(m2p(f), b);
    assert(multideg(c) < 256);
    tt.x[i] = c;
    i++;

    h = p2m(mterml(m2p(g), c));

    f = madd(f, h);
    if (mdeg(m2p(f)) == 0 || mdeg(m2p(g)) == 0)
    {
      //printf ("blake2\n");
      break;
    }

    if (multideg(c) == 0)
      break;
  }

  // tt は逆順に入ってるので入れ替える
  return tt;
}

pair mmod(MP f, MP g)
{
  MP h = {0}, d = {0}, r = {0}, tmp = {0}, cc = {0};
  mterm b = {0}, c = {0};
  int count = 0, c2 = 0, c3 = 0;
  printf("vmod-bl=%d k=%d\n", tdeg(f), tdeg(g));

  int iy = 0;
  while (1)
  {
    b = vLT(g);
    printf("%d %d %d==b\n", b.a, b.n[0], b.n[1]);
    c = mdivLT(f, b);
    if (c.a > 0)
      cc.x[c2++] = c;
    printf("%d %d %d==c\n", c.a, c.n[0], c.n[1]);
    h = mterml(g, c);
    tmp = mterml(tmp, c);
    mprintsage(h);
    printf(" ==h\n");
    mprintsage(f);
    printf(" ==f2\n");
    f = m2p(madd(madd(p2m(f), p2m(h)), p2m(tmp)));
    // f = padd(padd((f), (h)),(tmp));
    mprintsage(f);
    printf(" ===f\n");
    mprintsage(g);
    printf(" ==dlt\n");
    if (c.a == 0)
    {
      // tmp.x[c3++]=vLT(d);
      // d=oadd(d,vLT(d));
      r.x[count++] = vLT(f);
      f = oadd(f, vLT(f));

      mprintsage(f);
      printf(" ==ff\n");
      mprintsage(r);
      printf(" ==r\n");
     break;
      // exit(1);
    }
    // exit(1);
    for (int i = 0; i < TT; i++){
      if (f.x[i].a > N)
      {
        printf("nipple\n");
        exit(1);
      }
    }
    if (vLT((f)).a == 0)
    {
      mprintsage(g);
      printf(" ==princes\n");
      // b=LT(d);
      break;
    }
    if (vLT(g).a == 0)
    {
       r.x[count++]=vLT(f);
       f=oadd(f,vLT(f));
      printf("iine\n");
      // exit(1);
    }
  }

  r = m2p(madd(p2m(f), p2m(r)));
  mprintsage(cc);
  printf(" == lemon\n");
  pair t;
  t.f = r;
  t.g = cc;
  // printf("vmod-baka== %d %d\n",deg(f),deg(g));
  return t;
}

MP mmod2(MP f, MP g)
{
  MP h = {0};
  mterm b = {0}, c = {0};

  // printf("vmod-bl=%d k=%d\n",deg(f),deg(g));
  if (tdeg(f) < tdeg(g))
  {
    //    exit(1);
    // return f;
  }

  // b = vLT(g);
  MP d = g;
  // printpol(f);
  // printf(" ==f\n");
  while (1)
  {
    b = vLT(d);
    c = mdivLT(f, b);
    printf("c== %d %d\n", c.n[0], c.n[1]);
    d = oadd(d, b);
    // if (c.a == 0)
    //   f = oadd(f, b);
    h = mterml(g, c);
    f = m2p(madd(p2m(f), p2m(h)));

    if (tdeg((f)) == 0 || tdeg((d)) == 0)
    {
      // return f;
      break;
    }

    if (vLT(d).a == 0)
      break;
    printf("!!!%d %d %d\n", b.a, b.n[0], b.n[1]);
  }
  // printf("vmod-baka== %d %d\n",deg(f),deg(g));
  return f;
}


MP xgcd(MP a, MP b)
{
  MP r, tmp;

  /* 自然数 a > b を確認・入替 */
  if (mdeg(a) < mdeg(b))
  {
    tmp = a;
    a = b;
    b = tmp;
  }

  /* ユークリッドの互除法 */
  r = vdiv(p2m(a) , p2m(b));
  while (mdeg(r) != 0)
  {
    a = b;
    b = r;
    r = vmod(a , b);
  }

  /* 最大公約数を出力 */
  //printf("最大公約数 = %d\n", b);
  if(mdeg(b)!=0)
  {
    printf("(a,b)!=1\n");
    return b;
  }

  return b;
}


// invert of polynomial
MP vinv(MP a, MP n)
{
    MP d = n;
    MP x = {0};
    MP s = {0};
    MP t={0},r={0};
    MP tt=n;

    s.x[0].n[0]=0;
    s.x[0].n[1]=0;
    s.x[0].n[2]=0;
    s.x[0].a=1;

    while (mdeg(a)>0)
    {
        MP q = (vmod((d) , (a)));
        r = (vdiv(p2m(d) , p2m(a)));
        d = a;
        a = r;
        t = m2p(madd(p2m(x), p2m(mmul((q), (s)))));
        x = s;
        s = t;
        mprintpol(a);
        printf(" ===ghgh\n");
    }
    d = a;
    a = r;
    x = s;
    s = t;
    
    MP gcd = d; // $\gcd(a, n)$
    MP u=(mmod(m2p(madd(p2m(x) , p2m(n))),(tt)).f);
    u=(mmod((u), (d)).g);
 
    return  u;
}


// invert of polynomial
MP invpol(MP a, MP n)
{
    MP d = {0}, x = {0}, s = {0}, q = {0}, r = {0}, t = {0}, u = {0}, v = {0}, w = {0}, tt = {0}, gcd = {0}, tmp = {0};
    mterm b = mLT(a);
    MP vv = {0}, xx = {
                      0};

    if (mdeg((a)) > mdeg((n)))
    {
        tmp = a;
        a = n;
        n = tmp;
        printf("baka_i\n");
        // exit (1);
    }
    if (vLT(a).a == 0)
    {
        printf(" a ga 0\n");
        printf("%d*X^%d*Y^%d*Z^%d",b.a,b.n[0],b.n[1],b.n[2]);
        exit(1);
    }

    tt = n;

    d = n;
    x.x[0].a = 0;
    s.x[0].a = 1;
    s.x[0].a = 0;
    while (mdeg((a)) > 0)
    {
        if (mdeg((a)) > 0)
            r = mmod(d, a).f;
        if (vLT(a).a == 0)
          exit(1);
        //break;
        if (vLT(a).a > 0)
            q = mmod(d, a).g;

        d = a;
        a = r;
        t = m2p(madd(p2m(x), (p2m(mmul((q), (s))))));
        ////printpol ( (a));
        // printf ("\nin rovec a==================%d\n", deg ((a)));
        // printf ("\n");

        x = s;
        s = t;
        printf("agaaa\n");
    }
    // exit(1);
    //  if(vLT(a).a>0){
    d = a;
    a = r;
    ////printpol ( (a));
    // printf ("\nin rovec a|==================%d\n", deg ((a)));
    // printf ("\n");

    x = s;
    s = t;

    ////printpol ( (d));
    // printf ("\nout1================\n");
    gcd = d; // $\gcd(a, n)$
    mprintpol(gcd);
    printf(" =========gcd\n");
    // exit(1);
    // printf ("\n");
    ////printpol ( (n));
    // printf ("\n");
    // printf ("out2===============\n");

    printf("before vdiv\n");
    // w=tt;

    b = vLT(w);
    ////printpol ( (w));
    // printf ("\nw=======%d %d\n", b.a, b.n);
    // w=tt;
    v = m2p(madd(p2m(x), p2m(n)));
    ////printpol ( (v));
    // printf ("\n");
    /*
     if (vLT (v).a == 0)
     {
     printf ("v=============0\n");
     }
     printf ("d==============\n");
   */
    //  } //end of a>0
    w = tt;
    ////printpol ( (v));
    // printf ("\n");
    // printf ("ss==============\n");
    //        exit(1);
    //  if(deg((w))>0)
    if (vLT(v).n > 0 && vLT(w).n > 0)
    {
        u = (mmod((v), (w)).f);
    }
    else
    {
        // printpol ( (v));
        printf(" v===========\n");
        // printpol ( (x));
        printf(" x==0?\n");
        // printpol ( (n));
        printf(" n==0?\n");

        exit(1);
    }
    // caution !!
    if (vLT(u).a > 0 && vLT(d).a > 0)
    {
        u = (mmod((u), (d)).g);
    }

    if (vLT(u).a == 0 || vLT(d).a == 0)
    {
        printf("inv div u or d==0\n");
        // exit(1);
    }
    // u=coeff(u,d.x[0]);
    ////printpol ( (u));
    // printf ("\nu==================\n");
    if (vLT(u).a == 0)
    {
        printf("no return at u==0\n");
        exit(1);
    }

    return u;
}


int more(int a, int b)
{
  int i, j, k;

  printf("in more\n");
  if (b >= I - 1)
  {
    return S[a][b] ^ S[a][b - I + 2];
  }
  else
  {
    printf("%d %d\n", S[a][b + I - 1], S[a][b + 1]);
    return S[a][b + I - 1] ^ S[a][b + 1];
  }
}

MP set_curve(unsigned short a[9][4], int x)
{
  MP s = {0};
  int i, j;

  for (i = 0; i < x; i++)
  {
    for (j = 0; j < V; j++)
    {
      s.x[i].n[j] = a[i][j];
    }
    s.x[i].a = a[i][3];
  }

  return s;
}

int bin(int x, int y, int z)
{
  int i, j, f1, f2, f3, f4, f5, add(), mlt();
  int a, b, p = 0;
  int fnc, xx, count = 0;

  f1 = gf[mlt(mlt(x, x), mlt(y, x))];
  f2 = gf[mlt(mlt(y, y), mlt(y, z))];
  f3 = gf[mlt(mlt(y, y), mlt(z, z))];
  f4 = gf[mlt(mlt(z, z), mlt(z, z))];

  /*

   * ( baby step gaint step )
   * void jac(int x,int y)

   */
  /*
f1=gf[mlt(mlt(y,y),1)];
f2=gf[mlt(mlt(x,y),1)];
f3=gf[mlt(mlt(x,x),x)];
f4=gf[mlt(mlt(1,1),1)];
f5=gf[mlt(mlt(x,x),1)];
  */

  if ((f1 ^ f2 ^ f3 ^ f4) == 0)
  {
    count++;
    printf("%d %d %d\n", x, y, z);
  }
  //  printf("%d\n",count);
  /*
  for(a=0;a<N;a++){
    for(b=0;b<N;b++){
fnc=add(mlt(a,x),b);
  if(y==fnc){
    for(xx=0;xx<N;xx++){
      fnc=add(mlt(a,xx),b);
  */
  //    if(((add(mlt(fnc,fnc),mlt(xx,fnc)))==(add(mltn(3,xx),1))) ){
  // printf("a= %d b= %d : (%d,%d)\n",a,b,xx,fnc); /* intersection */

  /*
  p=x;
  for(y=0;y<N;y++){
  if(add(add(mlt(y,y),mlt(p,y)),add(mltn(3,x),1))==0)
  printf("%d,%d\n",p,y);  jac(x,y)?
  }
  */
  //	    } /* if */
  //	  } /* for */
  //	  } /* if */

  //}
  // printf("\n");
  //    }

  /*
     lx[k]=x;
     ly[k]=y;
     lz[k]=z;
  */
  //  k++;
  //}

  return count;
}

int main(void)
{
  int i, j, k = 0, a, b, c, count = 0, x, y, z, g, n;
  unsigned int u = 0, v = 0, delta = 7, ips = 1;
  static MP s = {0};
  unsigned char **HH;
  static unsigned short tmp[256][1] = {0};

  unsigned short gh3[6][4] =
      {{0, Q*Q, 0, 1}, {0, Q, 0, 1}, {0, 1, 0, 1}, {Q*Q+Q, 0, 0, 1}, {Q+1, 0, 0, 1}, {Q*Q+1, 0, 0, 1}};
  // gf256 g=1 elliptic
  static unsigned short el[4][4] =
      {{0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1}};
  // gf256 g=1 elloptic
  static unsigned short el2[5][4] =
      {{0, 2, 1, 1}, {1, 1, 1, 1}, {3, 0, 0, 1}, {0, 0, 3, 1}, {2, 0, 1, 1}};
  // gf8 g=6 Generalized Hermitian
  static unsigned short sc[4][4] =
      {{Q*Q-1, Q, 0, 1}, {Q, Q*Q, 0, 1}, {0, 1, 0, 1}, {Q*Q, 0, 0, 1}};
  // gf64 GH
  static unsigned short gr[4][4] = {{16, 15, 0, 1}, {1, 12, 0, 1}, {4, 0, 0, 1}, {0, 16, 0, 1}};
  // gf8 g=3 klein
  static unsigned short kl[3][4] = {{3, 1, 0, 1}, {0, 3, 0, 1}, {1, 0, 0, 1}};
  // GF(64) #=113,g=3
  static unsigned short g3[4][4] = {{3, 1, 0, 1}, {0, 3, 0, 1}, {0, 2, 0, 1}, {0, 0, 0, 1}};
  // g=6 GF(8)
  static unsigned short g6[4][4] = {{4, 3, 0, 1}, {0, 4, 0, 1}, {1, 2, 0, 1}, {2, 0, 0, 1}};
  // gfQ*Q Hermitian
  static unsigned short he[3][4] = {{Q + 1, 0, 0, 1}, {0, Q, 0, 1}, {0, 1, 0, 1}};
  // gf16 g=21 #N=121 Generalized Hermitian
  static unsigned short gu[5][4] =
      {{7, 4, 0, 1}, {6, 8, 0, 1}, {4, 1, 0, 1}, {0, 2, 0, 1}, {8, 0, 0, 1}};
  // gf32 g=75 #N=497 Generalized Hermitian
  static unsigned short ge[6][4] =
      {{Q*Q*Q*Q-1, Q*Q*Q, 0, 1}, {Q*Q*Q*Q-Q, Q*Q*Q*Q, 0, 1}, {Q*Q*Q*Q-Q*Q, 1, 0, 1}, {Q*Q*Q, Q, 0, 1}, {0, Q*Q, 0, 1}, {Q*Q*Q*Q, 0, 0, 1}};
  static unsigned short gh[4][4] = {{16, 15, 0, 1}, {1, 12, 0, 1}, {4, 0, 0, 1}, {0, 16, 0, 1}};
  // gf64 g=212 #N=2017 Generalized Hermitian
  static unsigned short gg[7][4] =
      {{31, 8, 0, 1}, {30, 16, 0, 1}, {28, 32, 0, 1}, {24, 1, 0, 1}, {16, 2, 0, 1}, {0, 4, 0, 1}, {32, 0, 0, 1}};
  // gf256 g=2413 Generalized Hermitian
  static unsigned short gd[9][4] =
      {{127, 8, 0, 1}, {126, 16, 0, 1}, {124, 32, 0, 1}, {120, 64, 0, 1}, {112, 128, 0, 1}, {96, 1, 0, 1}, {64, 2, 0, 1}, {0, 4, 0, 1}, {128, 0, 0, 1}};
  // gf128 g=315 Generalized Hermitian
  static unsigned short cc[8][4] =
      {{63, 8, 0, 1}, {62, 16, 0, 1}, {60, 32, 0, 1}, {56, 64, 0, 1}, {48, 1, 0, 1}, {32, 2, 0, 1}, {0, 4, 0, 1}, {64, 0, 0, 1}};
  // gf256 y^(Q+1)=X^8+x^4+x^2+x kummer
  static unsigned short ku[5][4] =
      {{0, 17, 0, 1}, {8, 0, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1}};
  // gf16 kummer
  static unsigned short ku3[5][4] =
      {{0, 5, 0, 1}, {12, 0, 0, 1}, {9, 0, 0, 1}, {6, 0, 0, 1}, {3, 0, 0, 1}};
  // gf64 kummer g=56
  static unsigned short ku4[5][4] =
      {{0, 9, 0, 1}, {40, 0, 0, 1}, {33, 0, 0, 1}, {12, 0, 0, 1}, {5, 0, 0, 1}};
  static unsigned short lo[3][4] = {{2, 0, 0, 1}, {1, 0, 0, 3}, {0, 1, 0, 6}};
  static unsigned short lk[6][4] =
      {{0, 2, 0, 1}, {0, 1, 0, 3}, {0, 0, 1, 6}, {3, 1, 0, 1}, {0, 3, 1, 1}, {1, 0, 3, 1}};
  // gf32 g=26 #N=157
  static unsigned short ts[3][4] = {{2, 2, 5, 1}, {7, 0, 2, 1}, {0, 9, 0, 1}};
  // gf128 g=78 #N=891
  static unsigned short tt[3][4] = {{3, 1, 0, 1}, {13, 0, 0, 1}, {0, 14, 0, 1}};
  // gf512 Generalized Hermitian
  static unsigned short gt[10][4] =
      {{255, 16, 0, 1}, {254, 32, 0, 1}, {252, 64, 0, 1}, {248, 128, 0, 1}, {240, 256, 0, 1}, {224, 1, 0, 1}, {192, 2, 0, 1}, {128, 4, 0, 1}, {0, 8, 0, 1}, {256, 0, 0, 1}};
  // over gf128 suzuki #N=16384
  static unsigned short su[4][4] =
      {{0, 128, 0, 1}, {0, 1, 0, 1}, {136, 0, 0, 1}, {9, 0, 0, 1}};
  // gf32 suzuki #N=1024
  static unsigned short s2[4][4] =
      {{0, 32, 0, 1}, {0, 1, 0, 1}, {36, 0, 0, 1}, {5, 0, 0, 1}};
  // gf8 suzuki
  static unsigned short s3[4][4] =
      {{0, 8, 0, 1}, {0, 1, 0, 1}, {10, 0, 0, 1}, {3, 0, 0, 1}};
  // y9 = x4 + x2 + x gf64 kummer
  static unsigned short ku2[4][4] =
      {{0, 9, 0, 1}, {4, 0, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1}};
  // y^9=x^2+x gf64 g=4
  static unsigned short ku5[3][4] = {{0, 9, 0, 1}, {2, 0, 0, 1}, {1, 0, 0, 1}};
  static unsigned short gl[6][4] = {{8, 16, 0, 1}, {12, 8, 0, 1}, {14, 4, 0, 1}, {15, 2, 0, 1}, {16, 0, 0, 1}, {0, 1, 0, 1}};

  static unsigned int bb[256][2] = {0}; //{{0,0},{1,0},{0,1},{2,0},{1,1},{0,2},{3,0},{2,1},{1,2},{0,3},{4,0},{3,1},{2,2},{1,3},{0,4},{5,0},{4,1},{3,2},{2,3},{1,4},{6,0},{5,1},{4,2},{3,3},{2,4},{7,0},{6,1},{5,2},{4,3},{3,4}};
  mterm aa[1256] = {0};
  mterm oo = {0};
  static unsigned int d[256][2] = {0};
  static unsigned char e[64] =
      {0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0};

  // unsigned char ee[64]={0,1,2,3,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

  //  unsigned char ee[150000]={0,0,0,0,12,0,0,0,0,11,0,0,2,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0};

  //  unsigned short ee[64]={0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,4,0,0,0,0,0,0,0,0,0,0};

  unsigned char ee[64] = {0};

  PO t = {0};
  unsigned short ss[N * N] = {0};
  //unsigned short M[K][K] = {0};

  unsigned short sy[N * N] = {0};
  unsigned short SS[256][256] = {0};
  unsigned short dd[30][2] = {0};
  int l;
  unsigned short *B[256];
  unsigned short G[256][256] = {0};
  int ii, jj, kk;
  time_t pp;

  srand(clock());

label:
  MP f = {0}; //minit(31);
  MP ga = {0}; //minit(23);
  MP h = {0};
/*
  if(E==2)
  s=set_curve(he,3);
  if(E==3)
  s = set_curve(sc, 4);
  if(E==5)
  s = set_curve(ge, 6);
*/
s=set_curve(gh3,6);
  /*
  x=0;y=1;z=0;
  count=bin(x,y,z);

  z=0;x=1;
  for(y=0;y<N;y++)
  count+=bin(x,y,z);

  z=1;
  for(x=0;x<N;x++){
    for(y=0;y<N;y++)
    count+=bin(x,y,z);
  }
  */
  printm(s);
  printf("count=%d\n", count);

  //u = mtrace(s);
  //  v=u;
  printf("count=%d\n\n", u);
  //exit(1);

//vprintsage((vmul(f,ga)));
//printf(" m\n");
//mprintsage((mmul((f),(ga))));
//printf(" p\n");
//exit(1);

  
    f.x[0].n[0]=2;
    f.x[0].n[1]=1;
    f.x[1].n[0]=1;
    f.x[1].n[1]=2;
    f.x[2].n[0]=0;
    f.x[2].n[1]=2;
    //f.x[3].n[0]=1;
    //f.x[3].n[1]=0;
    //f.x[4].n[1]=1;
    f.x[0].a=1;
    f.x[1].a=2;
    f.x[2].a=12;
    //f.x[3].a=1;
    //f.x[3].a=1;
    //f.x[4].a=1;

    ga.x[0].n[0]=0;
    ga.x[0].n[1]=0;
    ga.x[1].n[0]=1;
    ga.x[1].n[1]=1;
    //ga.x[2].n[0]=4;
    ga.x[0].a=1;
    ga.x[1].a=1;
    //ga.x[2].a=1;
    //ga.x[2].a=1;

printf("deg(ga)==%d\n",mdeg(ga));
printf("deg(f)==%d\n",mdeg(f));

mprintsage(vdiv(p2m(f), p2m(ga)));
  printf("\n");
  exit(1);

  mprintsage(f);
  printf(" ==f\n");
  mprintsage(ga);
  printf(" ==ga\n");
  //exit(1);
  mprintpol((f));
  printf("\n.f");
  //mprintpol(mmod(f,ga).g);
  //printf("\n");
  //mterm sx=vLT(f);
  //printf("%d*X^%d*Y^%d*Z^%d\n",sx.a,sx.n[0],sx.n[1],sx.n[2]);
  mprintsage(xgcd((f),(ga)));
  printf(" ==gcd\n");
  mprintsage(f);
  printf(" ==f\n");
  mprintsage(ga);
  printf(" ==ga\n");
  exit(1);

mprintpoln(vinv(ga, f));
exit(1);


    f.x[0].n[0]=5;
    f.x[0].n[1]=0;
    f.x[1].n[0]=3;
    f.x[1].n[1]=0;
    f.x[2].n[0]=2;
    f.x[2].n[1]=0;
    f.x[3].n[0]=1;
    f.x[3].n[1]=0;
    //f.x[4].n[1]=1;
    f.x[0].a=1;
    f.x[1].a=1;
    f.x[2].a=1;
    f.x[3].a=1;
    //f.x[3].a=1;
    //f.x[4].a=1;

    ga.x[0].n[0]=2;
    ga.x[0].n[1]=0;
    ga.x[1].n[0]=1;
    ga.x[1].n[1]=0;
    //ga.x[2].n[0]=4;
    ga.x[0].a=1;
    ga.x[1].a=1;
    ga.x[2].a=1;
    //ga.x[2].a=1;



  mterm o = {0}; // mdivLT(f,vLT(ga));
  // f=m2p(madd(p2m(f),p2m(mterml(ga,o))));
  // mprintsage(f);
  // printf(" ==1st\n");
  o = vLT(f);
  printf("%d %d %d %d\n", o.a, o.n[0], o.n[1], o.n[2]);
  o = vLT(ga);
  printf("%d %d %d %d\n", o.a, o.n[0], o.n[1], o.n[2]);
  // exit(1);

  pair mvp = mmod(f, ga);
  if (meq(p2m(mvp.f), p2m(f)) == 1)
    goto label;
  printf("Uh1");
  mprintsage((mvp.f));
  printf("\n");
  printf("Uh2");
  mprintsage((f));
  printf("\n");
  printf("Uh3");
  mprintsage((ga));
  printf("\n");
  printf("Uh2poly%Uh3poly==Uh1poly\n");
  if (meq(madd(p2m(mmul((ga), (mvp.g))), p2m(mvp.f)), p2m(f)) != 1)
  {
    printf("baka\n");
    exit(1);
  }
  // goto label;
  //  printm(sort(p2m(f)));
  //  printf("\n");

  exit(1);
/*
  memset(S, 0, sizeof(S));
  //    memset(SS,0,sizeof(SS));

  for (i = 0; i < 256; i++)
  {
    for (j = 0; j < 256; j++)
    {
      SS[i][j] = 0;
      S[i][j] = 0;
    }
  }

  i = 0;
  while (i < E)
  {
    ii = rand() % 16;
    jj = rand() % 63;
    if (ii > 0 && ee[jj] == 0 && jj > 0)
    {
      ee[jj] = ii;
      i++;
    }
  }

  // s=define_curve();

  HH = malloc(sizeof(unsigned short *) * 500);
  for (i = 0; i < N * N; i++)
    HH[i] = malloc(sizeof(unsigned short) * 15000);
*/
int uu[32][32][1000]={0};
//MP f={0};

l=0;
K=5;
for(i=0;i<1000;i++){
  //for(K=5;K<13;K++)
  {
    for(int j=3;j<13;j++){
  //s = set_curve(gg, 7);
  f=minit(j);
  u = mtrace(f);
  if((u==0||u>400) && u<=16*2*(K-1)*(K-2)/2+1+N && tdeg(f)>0){
  //if(u>60){
  mprintsage(f);
  printf(" #N=%d soo-tie %d\n",u,16*2*(K-1)*(K-2)/2+1+N); 
  uu[K][j][u]++;
  //exit(1);
  }
  l+=u;
}
}
}

//for(int k=5;k<13;k++){
k=5;
for(i=3;i<13;i++){
  for(int j=0;j<1000;j++){
  //if(uu[k][i][j]>0 && (j==0 || j>(N+1+8)) && u<=4*2*(k-1)*(k-2)/2+1+N)
  if(uu[k][i][j]>0)
printf("tietie deg=%d kou=%d, #N=%d,#C=%d\n",k,i,j,uu[k][i][j]);
//printf("\n");
}
}
//}

printf("tie count=%f\n", l/1000.0);
exit(1);

  s = set_curve(he, 3);

  /*
  x=0;y=1;z=0;
  count=bin(x,y,z);

  z=0;x=1;
  for(y=0;y<N;y++)
  count+=bin(x,y,z);

  z=1;
  for(x=0;x<N;x++){
    for(y=0;y<N;y++)
    count+=bin(x,y,z);
  }
  */

  printf("count=%d\n", count);

  u = mtrace(s);
  //  v=u;
  printf("count=%d\n\n", u);
  exit(1);

  v = mkbase(aa);
  printf("mkcount=%d\n", v);
  //  exit(1);

  for (i = 0; i < u; i++)
  {
    printf("%d,%d %d\n", gf[p.z[0][i]], gf[p.z[1][i]], gf[p.z[2][i]]);
  }
  //  exit(1);

  unsigned short sk[256] = {0};

  for (i = 0; i < v; i++)
  {
#pragma omp parallel for
    for (j = 0; j < u; j++)
    {
      //      if(p.z[0][j]>0)
      HH[i][j] = fg[otrace(aa[i], p.z[0][j], p.z[1][j], 1)];
    }
  }

  for (i = 0; i < v; i++)
  {
    printf("(%d,%d): ", aa[i].n[0], aa[i].n[1]);
    for (j = 0; j < u; j++)
      printf("%d ", HH[i][j]);
    printf("\n");
  }

  for (i = 0; i < 225; i++)
  {
    sk[i] = 0;
    // #pragma omp parallel for
    for (j = 0; j < Q * Q * Q; j++)
    {
      sk[i] ^= gf[mlt(fg[ee[j]], HH[i][j])];
    }
    //    if(ss[i]>0)
  }
  printf("\n");

  // exit(1);
  //
  for (i = 0; i < U; i++)
  {
    ss[i] = 0;
    // #pragma omp parallel for
    for (j = 0; j < u; j++)
    {
      ss[i] ^= gf[mlt(fg[ee[j]], HH[i][j])];
    }
    //    if(ss[i]>0)
    printf("syn[%d,%d]=%d\n", aa[i].n[0], aa[i].n[1], ss[i]);
    //      if(aa[i].n[0]==4){
    S[aa[i].n[0] + I][aa[i].n[1]] =
        S[aa[i].n[0]][aa[i].n[1] - I + 1] ^ S[aa[i].n[0]][aa[i].n[1] - I + 2];
    //  printf("S[%d,%d]=%d\n",aa[i].n[0],aa[i].n[1],S[aa[i].n[0]][aa[i].n[1]]);
    //    }
  }
  printf("\n");
  //    printf("6=%d\n",13^4);
  //  exit(1);

  //    a=0;
  x = 0;
  j = 0;
  // printf("%d %d\n",p.z[0][0],p.z[1][0]);
  printf("v=%d\n", v);
  // exit(1);

  //    exit(1);

  for (i = 0; i < U; i++)
  {
    S[aa[i].n[0]][aa[i].n[1]] = ss[i];
    //    for(j=0;j<2;j++)
    printf("%d", ss[i]);
    printf("\n");
  }
  for (i = 0; i < 16; i++)
  {
    for (j = 0; j < 16; j++)
      printf("%d ", S[i][j]);
    printf("\n");
  }
  printf("\n\n");

  // param(U,6);
  //   exit(1);

  for (i = 0; i < U; i++)
  {
    for (k = 0; k < U; k++)
    {
      SS[i][k] = S[aa[i].n[0] + aa[k].n[0]][aa[i].n[1] + aa[k].n[1]];
      // printf("%d %d %d %d|",i,k,aa[i].n[i]+aa[k].n[0],aa[i].n[1]+aa[k].n[1]);
      printf("%2d,%2d ", aa[i].n[0] + aa[k].n[0],
             aa[i].n[1] + aa[k].n[1]);
    }
    printf("\n");
  }
  // exit(1);

  // gauss
  for (i = 0; i < U; i++)
  {
    printf("i=%d\n", i);
    for (j = 0; j < U; j++)
    {
      for (k = 0; k < U; k++)
      {
        printf("%d ", SS[j][k]);
      }
      printf("\n");
    }
    printf("\n");
    for (k = i + 1; k < 75 - U; k++)
    {
      if (SS[i][i] > 0)
      {
        b = inv2(SS[i][i], SS[i][k]);
        for (j = 0; j < U; j++)
          SS[j][k] ^= gf[mlt(fg[SS[j][i]], b)];
      }
      else
      {
        j = i;
        while (SS[i][j] == 0)
        {
          j++;
          if (j == U)
          {
            i++;
            j = i;
            break;
          }
        }
        if (SS[i][j] > 0)
        {
          for (ii = i; ii < U; ii++)
            SS[ii][i] ^= SS[ii][j];
        }
      }
    }
  }

  printf("\n\n");
  for (i = 0; i < U; i++)
  {
    for (j = 0; j < U; j++)
      printf("%d ", SS[i][j]);
    printf("\n");
  }

  printf("(8,0)=%d\n", S[3][1] ^ 13);
  //    S[3][4]=13;
  // S[8][0]=7;
  //      exit(1);

  for (i = 0; i < 16; i++)
  {
    for (j = 0; j < 16; j++)
      printf("%d ", S[i][j]);
    printf("\n");
  }
  // exit(1);

  for (i = 0; i < 256; i++)
  {
    for (j = 0; j < 256; j++)
      G[i][j] = SS[i][j];
  }

  for (i = 0; i < N - 1; i++)
  {
    for (j = 0; j < N - 1; j++)
      printf("%d,", S[i][j]);
    printf("\n");
  }
  // exit(1);

  for (i = 0; i < 256; i++)
    B[i] = S[i];

  bases(2 * N);
  for (i = 0; i < 225; i++)
    base[i].a = 1;

  count = U - 1;
  for (l = 0; l < 75 - U; l++)
  {
    count++;

    // begin
    //  for(a=0;a<15;a++){
    // for(b=0;b<15;b++){
    i = aa[count].n[0];
    j = aa[count].n[1];

    for (a = 0; a < 15; a++)
    {
      for (b = 0; b < 15; b++)
      {
        if (S[a + I][b] == 0 && U > ((I - 1) * (I - 2)) / 2)
        {
          S[a + I][b] = more(a, b);
          printf("S=%d %d %d %d\n", S[a + I][b], a + I, a, b);
          if (delta - 2 * I + 2 + ips >= 0 && (S[I - 1 - ips][delta - I + 1 + ips] > 0 && S[I - 1 - ips][delta - 2 * I + 3 + ips] > 0))
          {
            S[2 * I - 1 - ips][delta - 2 * I + 2 + ips] =
                S[I - 1 - ips][delta - I + 1 + ips] ^ S[I - 1 -
                                                        ips][delta -
                                                             2 * I +
                                                             3 + ips];
            printf("Ha!\n");
            // exit(1);
          }
        }
        else
        {
          printf("baka\n");
          break;
          // exit(1);
        }
      }
      if (S[a + I][b] != 0 || U <= (I - 1) * (I - 2) / 2)
        break;
    }

    // exit(1);

    for (i = 0; i < 16; i++)
    {
      for (j = 0; j < 16; j++)
        printf("%d ", S[i][j]);
      printf("\n");
    }
    printf("\n\n");

    //    exit(1);

    for (i = 0; i < 28 + l; i++)
    {
      for (k = 0; k < 28 + l; k++)
        SS[i][k] = S[aa[i].n[0] + aa[k].n[0]][aa[i].n[1] + aa[k].n[1]];
    }

    for (i = 0; i < 28 + l; i++)
    {
      for (j = 0; j < 28 + l; j++)
      {
        // printf("%d ",SS[i][j]);
        printf("%d ", SS[i][j]);
      }
      printf("\n");
    }
    //    exit(1);

    // gauss
    /*
       for(i=0;i<U+l;i++){
       printf("i=%d\n",i);
       for(j=0;j<U+l;j++){
       for(k=0;k<U+l;k++){
       printf("%d ",SS[j][k]);
       }
       printf("\n");
       }
       printf("\n");
       if(SS[i][i]>0){
       for(k=i+1;k<U+l;k++){
       b=inv2(SS[i][i],SS[i][k]);
       for(j=0;j<U+l;j++)
       SS[j][k]^=gf[mlt(fg[SS[j][i]],b)];
       }
       }
       if(SS[i][i]==0){
       for(j=i;j<U+l;j++){
       if(SS[i][j]>0)
       break;
       }
       for(jj=j+1;jj<U+l;jj++){
       b=inv2(SS[i][j],SS[i][jj]);
       for(ii=0;ii<U+l;ii++)
       SS[ii][jj]^=gf[mltn(fg[SS[i][ii]],b)];
       }
       }
       }
     */

    // gauss

    for (i = 0; i < 28 + l; i++)
    {
      printf("i=%d\n", i);
      for (j = 0; j < 28 + l; j++)
      {
        for (k = 0; k < 28 + l; k++)
        {
          printf("%d ", SS[j][k]);
        }
        printf("\n");
      }
      printf("\n");
      if (SS[i][i] > 0)
      {
        for (k = i + 1; k < 28 + l; k++)
        {
          b = inv2(SS[i][i], SS[i][k]);
          for (j = 0; j < 28 + l; j++)
            SS[j][k] ^= gf[mlt(fg[SS[j][i]], b)];
        }
      }
    }

    int nn = 0, d, e, f, x0, x1, x2, x3;

    printf("\n\n");
    for (i = 0; i < 28 + l; i++)
    {
      for (j = 0; j < 28 + l; j++)
        printf("%d ", SS[i][j]);
      printf("\n");
    }

    for (i = 0; i < 16; i++)
    {
      for (j = 0; j < 16; j++)
        printf("%d ", S[i][j]);
      printf("\n");
    }
    for (i = 0; i < 16; i++)
      sy[i] = 0;

    nn = -1;
    for (i = 0; i < 28 + l; i++)
    {
      //      nn=0;
      for (k = 0; k < 28 + l; k++)
      {
        // SS[i][k]=S[aa[i].n[0]+aa[k].n[0]][aa[i].n[1]+aa[k].n[1]];
        if (aa[i].n[0] + aa[k].n[0] == aa[count].n[0] && aa[i].n[1] + aa[k].n[1] == aa[count].n[1])
        {
          printf("SS[%2d][%2d]=%2d %d:(%d,%d)%",
                 aa[i].n[0] + aa[k].n[0], aa[i].n[1] + aa[k].n[1],
                 SS[i][k], sk[count], i, k);
          //  nn=0;
          if (k == 7)
            x = SS[i][k];
          if (k == 10)
            y = SS[i][k];
          if (k == 32)
            z = SS[i][k];
          if (k == 22)
            a = SS[i][k];
          if (k == 17)
            b = SS[i][k];
          if (k == 8)
            c = SS[i][k];
          if (k == 13)
            d = SS[i][k];
          if (k == 31)
            e = SS[i][k];
          if (k == 33)
            f = SS[i][k];
          if (k == 30)
            x0 = SS[i][k];
          if (k == 9)
            x1 = SS[i][k];

          if (k > 5 && k < 15)
          {
            if (SS[i][k] == SS[i - 1][k + 1])
            {
              nn = SS[i][k];
              printf("NN=%d %d %d,%d %d\n", nn, SS[i][k],
                     SS[i - 1][k + 1], i, k);
              // nn=n;
            } // else{
            // nn=SS[i][7];
            // }
            sy[SS[i][k]]++;
          }
          // sy[SS[i][k]]++;
        }
        //      if(aa[i].n[0]+aa[k].n[0]==7 && aa[i].n[1]+aa[k].n[1]==5)
        // printf("SS[%2d][%2d]=%2d %",aa[i].n[0]+aa[k].n[0],aa[i].n[1]+aa[k].n[1],SS[i][k]);
      }

      printf("\n");
    }

    ii = 0;
    jj = 0;
    kk = 0;

    for (ii = 0; ii < 16; ii++)
    {
      kk += sy[ii];
      printf("%d %d,", sy[ii], ii);
    }
    printf("\n");
    for (ii = 0; ii < 16; ii++)
    {
      if (nn == -1)
      {
        //      printf("SS=%d %d\n",ii,sy[ii]);
        if (jj < sy[ii] && ii > 0)
        {
          if (sy[ii] > 0)
          {
            jj = sy[ii];
            n = ii;
          }
        }
        else if (sy[0] > kk / 2)
        {
          jj = sy[0];
          n = 0;
        }
      }
      else if (nn >= 0)
      {
        n = nn;
      }
    }

    printf("max=%d %d %d\n", n, sy[n], sk[count]);
    /*
       for(k=0;k<64;k++)
       printf("%d,",ee[k]);
       printf("\n");
     */
    if (n != sk[count])
    {
      // n=SS[67][7];
      // printf("x=%d\n",x);
      //  scanf("%d",&n);
      n = a;
    }
    if (n != sk[count])
    {
      n = y;
    }
    if (n != sk[count])
    {
      n = x;
    }
    if (n != sk[count])
    {
      n = z;
    }
    if (n != sk[count])
    {
      n = b;
    }
    if (n != sk[count])
    {
      n = c;
    }
    if (n != sk[count])
    {
      n = d;
    }
    if (n != sk[count])
    {
      n = e;
    }
    if (n != sk[count])
    {
      n = f;
    }
    if (n != sk[count])
    {
      n = x0;
    }
    if (n != sk[count])
    {
      n = x1;
    }

    assert(n == sk[count]);
    // exit(1);

    // scanf("%d",&n);

    for (ii = 0; ii < 16; ii++)
      sy[ii] = 0;
    S[aa[count].n[0]][aa[count].n[1]] = n;
    S[aa[count].n[0] + I][aa[count].n[1]] =
        S[aa[count].n[0]][aa[count].n[1] - I +
                          1] ^
        S[aa[count].n[0]][aa[count].n[1] - I + 2];
    printf("S=%d\n", S[aa[count].n[0] + I][aa[count].n[1]]);
    printf("%d %d\n", S[7][1], S[2][2] ^ 8);
    //    S[7][5]=15;
  }

  for (i = 5; i < 15; i++)
  {
    for (j = 0; j < 15; j++)
      S[i][j] =
          S[(i - 5) % 15][(j + 4) % 15] ^ S[(i - 5) % 15][(j + 1) % 15];
  }
  printf("\n\ncomplete table\n\n");
  for (i = 0; i < 15; i++)
  {
    for (j = 0; j < 15; j++)
      printf("%d ", S[i][j]);
    printf("\n");
  }

  int vv;
  vv = bases(2 * N);
  printf("bases=%d\n", vv);

  //  exit(1);

  for (i = 0; i < vv; i++)
  {
    printf("%d %d\n", base[i].n[0], base[i].n[1]);
    base[i].a = 1;
  }

  for (i = 0; i < 15 * 15; i++)
  {
    ss[i] = S[base[i].n[0]][base[i].n[1]];
    printf("syn[%d,%d]=%d\n", base[i].n[0], base[i].n[1], ss[i]);
  }
  // exit(1);

  x = 0;
  j = 0;
  printf("%d %d\n", p.z[0][0], p.z[1][0]);
  printf("v=%d\n", v);
  //    exit(1);

  for (j = 0; j < 64; j++)
  {
    sy[j] = 0;
    x = 0;
    for (i = 0; i < 15 * 15; i++)
    {

      x ^= gf[mlt(fg[ss[i]], oinv(otrace(base[i], p.z[0][j], p.z[1][j], 1)))];

      // sy[i]=mlt(mlt(base[i].n[0],p.z[0][4]),
      //         mlt(base[i].n[1],p.z[1][4]));
      //       printf("ss=%d\n",ss[i]);
      // printf("e=%d %d %d %d %d %d\n",x,j,otrace(base[i],p.z[0][j],p.z[1][j],1),ss[i],base[i].n[0],base[i].n[1]);
    }
    if(x>0)
    printf("e=%d \n", x, j,
           otrace(base[i], p.z[0][j], p.z[1][j], 1), ss[i]);
  }
  printf("print error\n");
  //exit(1);

  for (i = 0; i < 64; i++){
  if(ee[i]>0)
    printf("%d ", ee[i]);
  }
  printf("\n");
  printf("answer\n");
/*
  exit(1);
  // printf("e=%d %d\n",x,j);
  //     }
  //     for(j=0;j<u;j++){
  for (i = 0; i < v; i++)
  {
    printf("sy[%d]=%d %d\n", i, sy[i], HH[i][4]);
  }
  // printf("e=%d %d\n",x,j);
  //     }
*/
  free(HH);
  exit(1);

  g = (I - 1) * (I - 2) / 2;
  //  g=2413;
  param(u, g);

  // exit(1);
  /*
     for(i=0;i<3;i++){
     for(j=0;j<u;j++)
     p.z[i][j]=0;
     }
   */
  /*
     s=set_curve(lo,3);
     u=mtrace(s);
     printf("count=%d\n\n",u);
     //    exit(1);
     for(i=0;i<u;i++)
     printf("%d,%d %d\n",gf[p.z[0][i]],gf[p.z[1][i]],gf[p.z[2][i]]);
     count=0;
     for(i=0;i<v;i++){
     for(j=0;j<u;j++){
     if(t.z[0][i]==p.z[0][j] && t.z[1][i]==p.z[1][j] && t.z[2][i]==p.z[2][j]){
     printf("intersection points=%d %d %d\n",gf[t.z[0][i]],gf[t.z[1][i]],gf[t.z[2][i]]);
     count++;
     }
     }
     }
     printf("%d\n",count);
     exit(1);
   */

  //  printf("%d\n",fg[gf[5]^gf[2]^gf[6]]);

  return 0;
}
