/*
 * BBGS one-point/ECP decoder - single-file configurable prototype (extended)
 *
 * Curve family: binary BBGS model (q=2), parameter pair (a,b), c=a+b.
 * The defining relation is centralized in bbgs_define_equation()/bb_H().
 * The shared ECP decoder does not depend on a,b or on the curve equation.
 *
 * Build:   cc -O2 -std=c11 -Wall -Wextra -o bbgs_ag_decoder bbgs_ag_decoder.c
 * Example: ./bbgs_ag_decoder --a 3 --b 2 --v 149 --t 80 --errors 10
 *
 * Extensions in this version
 *   - any a>b (a odd, gcd(a,b)=1, b>=2) with c=a+b <= 12, up to 256 injected errors
 *   - --auto 1 chooses v,t automatically from --errors
 *   - error locator function(s) printed as polynomial in x,z,w
 *   - table of error positions / values (decoded vs injected)
 *   - --list 0|1 and --locator N control the report (first trial only)
 *
 * Note: the basis/genus formulas were derived for a=b+1; for other a>b they are
 * used as-is and NOT proven here. The self-checks (A*B subset H, decode results)
 * are evidence only. For large n (c>=9) use --fast 1.
 *
 * Current algebraic scope: the BBGS family and the matching Hu Omega-lattice
 * basis formulas below. Replacing bb_H alone by an unrelated equation does
 * NOT preserve those basis/divisor identities; a new family needs matching
 * bb_point_data() and bb_build_basis() formulas too.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_M 12
#define MAX_ERRORS 256

typedef uint16_t GF;

static int GQ; /* q = 2^m */
static GF EXPT[2 * (1 << MAX_M)];
static int LOGT[1 << MAX_M];

static int gf_init(int m)
{
    /* primitive polynomials x^m + ... for m = 2..13 */
    static const unsigned poly[MAX_M + 1] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D, 0x211, 0x409,
                                             0x805, 0x1053};
    if (m < 2 || m > MAX_M)
        return 0;
    GQ = 1 << m;
    unsigned x = 1;
    for (int i = 0; i < GQ - 1; ++i)
    {
        EXPT[i] = (GF)x;
        LOGT[x] = i;
        x <<= 1;
        if (x & (unsigned)GQ)
            x ^= poly[m];
    }
    for (int i = GQ - 1; i < 2 * (GQ - 1); ++i)
        EXPT[i] = EXPT[i - (GQ - 1)];
    return 1;
}
static inline GF gmul(GF a, GF b)
{
    return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0;
}
static inline GF ginv(GF a)
{
    return a ? EXPT[(GQ - 1) - LOGT[a]] : 0;
}
static GF gpow(GF a, int e)
{
    if (e == 0)
        return 1;
    if (!a)
        return 0;
    return EXPT[(int)(((long)LOGT[a] * e) % (GQ - 1))];
}

/* 元を g^k (g = 生成元) の形で表示 */
static void pe(GF x)
{
    if (!x) printf("0");
    else printf("g^%d", LOGT[x]);
}

static uint64_t rng_state;
static uint64_t rnd(void)
{
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* ------------------------------------------------------------------ */
/* 線形代数 (行列は行優先の1次元配列)                                   */
/* ------------------------------------------------------------------ */
static int rref(GF *m, int rows, int cols, int *piv)
{
    int rank = 0;
    for (int col = 0; col < cols && rank < rows; ++col)
    {
        int p = rank;
        while (p < rows && m[(size_t)p * cols + col] == 0)
            ++p;
        if (p == rows)
            continue;
        if (p != rank)
            for (int j = 0; j < cols; ++j)
            {
                GF t = m[(size_t)rank * cols + j];
                m[(size_t)rank * cols + j] = m[(size_t)p * cols + j];
                m[(size_t)p * cols + j] = t;
            }
        GF s = ginv(m[(size_t)rank * cols + col]);
        for (int j = 0; j < cols; ++j)
            m[(size_t)rank * cols + j] = gmul(m[(size_t)rank * cols + j], s);
        for (int i = 0; i < rows; ++i)
        {
            if (i == rank)
                continue;
            GF f = m[(size_t)i * cols + col];
            if (!f)
                continue;
            for (int j = 0; j < cols; ++j)
                m[(size_t)i * cols + j] ^= gmul(f, m[(size_t)rank * cols + j]);
        }
        piv[rank++] = col;
    }
    return rank;
}

/* in (rows x cols) の右零空間の基底 (dim x cols) を返す */
static GF *nullspace(const GF *in, int rows, int cols, int *dim)
{
    GF *m = malloc(((size_t)rows * cols + 1) * sizeof(GF));
    int *piv = malloc(sizeof(int) * (rows + 1));
    int *isp = calloc(cols + 1, sizeof(int));
    memcpy(m, in, (size_t)rows * cols * sizeof(GF));
    int rank = rref(m, rows, cols, piv);
    for (int i = 0; i < rank; ++i)
        isp[piv[i]] = 1;
    *dim = cols - rank;
    GF *basis = calloc((size_t)(*dim) * cols + 1, sizeof(GF));
    int d = 0;
    for (int fc = 0; fc < cols; ++fc)
    {
        if (isp[fc])
            continue;
        basis[(size_t)d * cols + fc] = 1;
        for (int r = 0; r < rank; ++r)
            basis[(size_t)d * cols + piv[r]] = m[(size_t)r * cols + fc]; /* 標数2: -x = x */
        ++d;
    }
    free(m);
    free(piv);
    free(isp);
    return basis;
}

typedef struct { GF x, y; } Point;

typedef struct
{
    int cnt;
    GF *v; /* cnt x n */
    int64_t *ei, *ej, *ek; /* BBGS monomial exponents; NULL for plane bases */
} Basis;

typedef struct
{
    int n;
    Basis A, B, H;
} Code;

static GF *PZ, *PW;          /* 各評価点での補助関数 z, w の値 */
static const Point *PTS;     /* 評価点 */

/* 基底 b の i 番目の関数の点 p での値。v を持たない基底は単項式から直接計算 */
static inline GF bval(const Basis *b, int n, int i, int p)
{
    if (b->v) return b->v[(size_t)i * n + p];
    if (!PZ[p]) return 0;
    int em = (int)((b->ei[i] % (GQ - 1) + (GQ - 1)) % (GQ - 1));
    int jm = (int)((b->ej[i] % (GQ - 1) + (GQ - 1)) % (GQ - 1));
    int km = (int)((b->ek[i] % (GQ - 1) + (GQ - 1)) % (GQ - 1));
    return gmul(gpow(PTS[p].x, em), gmul(gpow(PZ[p], jm), gpow(PW[p], km)));
}

/* 復号の途中結果 (誤り位置関数の表示用) */
typedef struct
{
    int dimk;   /* 核の次元 */
    GF *ker;    /* dimk x K1 : L(A) の基底に関する係数 */
    int nz;     /* 核の共通零点の個数 */
    int *Z;     /* その点の番号 */
} Report;

static int in_code(const Code *c, const GF *w)
{
    for (int r = 0; r < c->H.cnt; ++r)
    {
        GF z = 0;
        for (int p = 0; p < c->n; ++p)
            z ^= gmul(c->H.v[(size_t)r * c->n + p], w[p]);
        if (z)
            return 0;
    }
    return 1;
}

/*
 * 誤り位置集合 Z 上の誤り値を、シンドローム S_ij = sum_k e_k a_i(Z_k) b_j(Z_k)
 * から解く。nsel < total のときは (i,j) をランダムに nsel 本だけ使う
 * (誤り256個でも高速に動かすため)。成功なら 1、sol[0..nz-1] に誤り値。
 */
static int solve_rows(const Code *c, const GF *S, const int *Z, int nz,
                      long total, long nsel, GF *sol)
{
    int n = c->n, K2 = c->B.cnt, cols = nz + 1;
    GF *aug = calloc((size_t)nsel * cols + 1, sizeof(GF));
    int *piv = malloc(sizeof(int) * (nsel + 1));
    for (long r = 0; r < nsel; ++r)
    {
        long idx = (nsel == total) ? r : (long)(rnd() % (uint64_t)total);
        int i = (int)(idx / K2), j = (int)(idx % K2);
        for (int k = 0; k < nz; ++k)
            aug[(size_t)r * cols + k] =
                gmul(c->A.v[(size_t)i * n + Z[k]], bval(&c->B, n, j, Z[k]));
        aug[(size_t)r * cols + nz] = S[(size_t)i * K2 + j];
    }
    int rank = rref(aug, (int)nsel, cols, piv);
    int good = (rank == nz);
    for (int r = 0; r < rank && good; ++r)
        if (piv[r] == nz)
            good = 0; /* 矛盾した連立方程式 */
    if (good)
        for (int k = 0; k < nz; ++k)
            sol[k] = aug[(size_t)k * cols + nz];
    free(aug);
    free(piv);
    return good;
}

/* 成功なら 1 を返し out に訂正語, *nerr に見つけた誤り個数。rep != NULL なら途中結果を格納 */
static int decode(const Code *c, const GF *rcv, GF *out, int *nerr, Report *rep)
{
    int n = c->n, K1 = c->A.cnt, K2 = c->B.cnt;
    int ok = 0;
    GF *S = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *ST = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *AR = malloc((size_t)n*sizeof(GF));
    int allzero = 1;
    *nerr = 0;
    memcpy(out, rcv, (size_t)n * sizeof(GF));

    /* rcv の非零位置だけを使ってシンドロームを計算 (疎な誤りで高速) */
    int *NZP = malloc(sizeof(int) * (size_t)(n + 1));
    int nnz = 0;
    for (int p = 0; p < n; ++p)
        if (rcv[p]) NZP[nnz++] = p;
    GF *BN = malloc((size_t)K2 * nnz * sizeof(GF) + 1);
    if (!BN) { free(NZP); goto done; }
    for (int j = 0; j < K2; ++j)
        for (int s2 = 0; s2 < nnz; ++s2)
            BN[(size_t)j * nnz + s2] = bval(&c->B, n, j, NZP[s2]);
    for (int i = 0; i < K1; ++i)
    {
        for (int s2 = 0; s2 < nnz; ++s2)
            AR[s2] = gmul(rcv[NZP[s2]], c->A.v[(size_t)i * n + NZP[s2]]);
        for (int j = 0; j < K2; ++j)
        {
            GF z = 0;
            const GF *bj = BN + (size_t)j * nnz;
            for (int s2 = 0; s2 < nnz; ++s2)
                z ^= gmul(AR[s2], bj[s2]);
            S[(size_t)i * K2 + j] = z;
            ST[(size_t)j * K1 + i] = z;
            if (z)
                allzero = 0;
        }
    }
    free(BN);
    free(NZP);
    if (allzero)
    {
        ok = in_code(c, rcv);
        goto done;
    }

    int dimk;
    GF *ker = nullspace(ST, K2, K1, &dimk);
    if (dimk == 0)
    {
        free(ker);
        goto done;
    }
    int *Z = malloc(sizeof(int) * n);
    int nz = 0;
    for (int p = 0; p < n; ++p)
    {
        int common = 1;
        for (int v = 0; v < dimk && common; ++v)
        {
            GF z = 0;
            for (int i = 0; i < K1; ++i)
                z ^= gmul(ker[(size_t)v * K1 + i], c->A.v[(size_t)i * n + p]);
            if (z)
                common = 0;
        }
        if (common)
            Z[nz++] = p;
    }
    if (rep)
    {
        rep->dimk = dimk;
        rep->ker = malloc((size_t)dimk * K1 * sizeof(GF) + 1);
        memcpy(rep->ker, ker, (size_t)dimk * K1 * sizeof(GF));
        rep->nz = nz;
        rep->Z = malloc(sizeof(int) * (nz + 1));
        memcpy(rep->Z, Z, sizeof(int) * nz);
    }
    free(ker);
    if (nz == 0 || (long)nz > (long)K1 * K2)
    {
        free(Z);
        goto done;
    }
    {
        long total = (long)K1 * K2;
        long nsel = 3L * nz + 64;
        if (nsel > total) nsel = total;
        GF *sol = malloc(sizeof(GF) * (nz + 1));
        int good = solve_rows(c, S, Z, nz, total, nsel, sol);
        if (!good && nsel < total)
            good = solve_rows(c, S, Z, nz, total, total, sol);
        if (good)
        {
            for (int k = 0; k < nz; ++k)
                out[Z[k]] ^= sol[k];
            if (in_code(c, out))
            {
                ok = 1;
                for (int k = 0; k < nz; ++k)
                    if (sol[k])
                        ++*nerr;
            }
        }
        free(sol);
    }
    free(Z);
done:
    free(S);
    free(ST);
    free(AR);
    return ok;
}

static int parse_int(const char *s, int *v)
{
    char *e = NULL;
    long x = strtol(s, &e, 10);
    if (!s[0] || !e || *e || x < 0 || x > 1000000)
        return 0;
    *v = (int)x;
    return 1;
}

/* ---------------- BBGS (binary q=2) ---------------- */
static int BB_A, BB_B, BB_C;
static GF frob2(GF x, int k);

/*
 * BBGS defining relation:
 *   H(x,y) = sum_{k=0}^{c-1} y^(2^(a+k)) / x^(2^k) = 1.
 * This is the single place where the family equation is assembled.
 * The Frobenius exponents are reduced modulo c in GF(2^c).
 */
static GF bbgs_define_equation(GF x, GF y)
{
    GF sum = 0;
    for (int k = 0; k < BB_C; ++k) {
        int e = (BB_A + k) % BB_C;
        GF numerator = frob2(y, e);
        GF denominator = frob2(x, k);
        if (!denominator) return 0;
        sum ^= gmul(numerator, ginv(denominator));
    }
    return sum;
}

static GF frob2(GF x, int k) {
    while (k--) x = gmul(x,x);
    return x;
}
/* 曲線上の点であることが既知の場合の補助関数値 (H の再評価を省く) */
static int bb_point_data_nc(GF x,GF y,GF *z,GF *w) {
    /* p=2, a odd, so a^{-1}=1 in F_2. */
    GF u = 1 ^ gmul(frob2(y,BB_A),ginv(x))
                  ^ gmul(frob2(y,1),ginv(frob2(x,BB_A)));
    if (!u) return 0;
    *z=gmul(y,ginv(frob2(x,BB_B)));
    *w=gmul(gmul(frob2(y,BB_A),ginv(x)),ginv(u));
    return 1;
}

static int64_t floor_div_posden(int64_t x,int64_t d) {
    if (x>=0) return x/d;
    return - ((-x+d-1)/d);
}
static int64_t ceil_div_posden(int64_t x,int64_t d) {
    return -floor_div_posden(-x,d);
}
/* i が基底に入るか判定し、対応する j,k を返す */
static int bb_cand_ok(int64_t i,int rdiv,int sdiv,int tdiv,int64_t *pj,int64_t *pk) {
    const int64_t Nc=((int64_t)1<<BB_C)-1;
    const int64_t Nb=((int64_t)1<<BB_B)-1;
    int64_t j=ceil_div_posden((((int64_t)1<<BB_A)*i)-sdiv,Nc);
    int64_t k=ceil_div_posden(-i-rdiv,Nc);
    int64_t lhs=(((int64_t)1<<(BB_A-1))*Nb)*i
                - (((int64_t)1<<(BB_B-1))*Nc)*j + tdiv;
    int64_t rhs=((((int64_t)1<<(BB_A-1))-1)*Nc)*k;
    *pj=j; *pk=k;
    return lhs>=rhs;
}
/* Basis from Hu's Omega lattice: x^i z^j w^k.
 * store=0: 値を保持せず指数だけ記録 (bval で必要時に計算)
 * check=0: 点上の線形独立性チェックを省略 (deg < n のとき独立と仮定) */
static Basis bb_build_basis(int v,int rdiv,int sdiv,int tdiv,const Point *pts,int n,int store,int check) {
    int64_t start=-(int64_t)v;
    /* Hu, Proposition 6: exact finite i-range; j,k are ceilings from the divisor inequalities. */
    int64_t stop=(((int64_t)1<<(BB_A-1))-1)*rdiv
                 + ((int64_t)1<<(BB_B-1))*sdiv + tdiv;
    int64_t valid=0, j0, k0;
    for (int64_t i=start;i<=stop;i++) if (bb_cand_ok(i,rdiv,sdiv,tdiv,&j0,&k0)) valid++;
    int cap=(int)((check && valid>n)?n:valid), rank=0;
    GF *ech=NULL,*vec=NULL,*raw=NULL,*out=NULL; int *piv=NULL;
    if (check) { ech=calloc((size_t)cap*n+1,sizeof(GF)); vec=malloc((size_t)n*sizeof(GF)); piv=calloc(cap+1,sizeof(int)); }
    if (store) out=calloc((size_t)cap*n+1,sizeof(GF));
    if (store||check) raw=malloc((size_t)n*sizeof(GF));
    int64_t *ei=calloc(cap+1,sizeof(int64_t)), *ej=calloc(cap+1,sizeof(int64_t)), *ek=calloc(cap+1,sizeof(int64_t));
    if ((check&&(!ech||!vec||!piv)) || (store&&!out) || ((store||check)&&!raw)) {
        fprintf(stderr,"Basis allocation failed (%d x %d).\n",cap,n); exit(1);
    }
    for (int64_t i=start;i<=stop;i++) {
        int64_t j,k;
        if (!bb_cand_ok(i,rdiv,sdiv,tdiv,&j,&k)) continue;
        if (rank>=cap) break; /* rank==n (check有効時) */
        if (store||check) {
            int ei_m=(int)((i%(GQ-1)+(GQ-1))%(GQ-1));
            int ej_m=(int)((j%(GQ-1)+(GQ-1))%(GQ-1));
            int ek_m=(int)((k%(GQ-1)+(GQ-1))%(GQ-1));
            for (int p=0;p<n;p++) {
                if (!PZ[p]) { raw[p]=0; continue; }
                raw[p]=gmul(gpow(pts[p].x,ei_m),
                            gmul(gpow(PZ[p],ej_m), gpow(PW[p],ek_m)));
            }
        }
        if (check) {
            memcpy(vec,raw,(size_t)n*sizeof(GF));
            for (int r=0;r<rank;r++) {
                GF f=vec[piv[r]];
                if (!f) continue;
                for (int p=0;p<n;p++) vec[p]^=gmul(f,ech[(size_t)r*n+p]);
            }
            int pv=0; while(pv<n && !vec[pv]) pv++;
            if(pv==n) continue;
            GF inv=ginv(vec[pv]);
            for(int p=0;p<n;p++) ech[(size_t)rank*n+p]=gmul(vec[p],inv);
            piv[rank]=pv;
        }
        if (store) memcpy(out+(size_t)rank*n,raw,(size_t)n*sizeof(GF));
        ei[rank]=i; ej[rank]=j; ek[rank]=k;
        rank++;
    }
    free(ech); free(vec); free(raw); free(piv);
    Basis bs={rank,out,ei,ej,ek}; return bs;
}
static int bb_verify_product_basis(const Basis *A,const Basis *B,const Basis *H,int n) {
    GF *echelon=malloc((size_t)H->cnt*n*sizeof(GF));
    GF *prod=malloc((size_t)n*sizeof(GF));
    int *piv=malloc((size_t)(H->cnt+1)*sizeof(int));
    if(!echelon||!prod||!piv) { free(echelon);free(prod);free(piv);return 0; }
    memcpy(echelon,H->v,(size_t)H->cnt*n*sizeof(GF));
    int rank=rref(echelon,H->cnt,n,piv);
    if(rank!=H->cnt) { free(echelon);free(prod);free(piv);return 0; }
    for(int i=0;i<A->cnt;i++) for(int j=0;j<B->cnt;j++) {
        for(int p=0;p<n;p++) prod[p]=gmul(A->v[(size_t)i*n+p],B->v[(size_t)j*n+p]);
        for(int r=0;r<rank;r++) {
            GF f=prod[piv[r]];
            if(!f) continue;
            for(int p=0;p<n;p++) prod[p]^=gmul(f,echelon[(size_t)r*n+p]);
        }
        for(int p=0;p<n;p++) if(prod[p]) {
            fprintf(stderr,"A*B row-space test failed at basis pair (%d,%d).\n",i,j);
            free(echelon);free(prod);free(piv);return 0;
        }
    }
    free(echelon);free(prod);free(piv);return 1;
}

static int gcd(int x,int y) { while(y){int z=x%y;x=y;y=z;} return x; }

/* ------------------------------------------------------------------ */
/* 表示: 誤り位置関数と誤りリスト                                       */
/* ------------------------------------------------------------------ */
static void print_term(const Code *c, GF co, int i)
{
    printf("  ");
    pe(co);
    if (c->A.ei)
        printf(" * x^(%lld) * z^(%lld) * w^(%lld)",
               (long long)c->A.ei[i], (long long)c->A.ej[i], (long long)c->A.ek[i]);
    else
        printf(" * basis[%d]", i);
}

/*
 * 誤り位置多項式: 核の基底の先頭(最小)のもの。L(A) の基底は極の位数の昇順に
 * 並んでいるので、これは「誤り位置で 0 になる関数のうち位数が最小」のもので、
 * スカラー倍を除いて一意。先頭係数を 1 に正規化し、高位の項から順に表示する。
 * nloc >= 2 のときは、参考として核の他の元も続けて表示する。
 */
static void show_locator(const Code *c, const Report *rep, const int *errpos, int nerrpos, int nloc)
{
    int n = c->n, K1 = c->A.cnt;
    printf("\n==== Error locator polynomial ====\n");
    if (!rep->ker || rep->dimk == 0) { printf("(no locator found: kernel is empty)\n"); return; }
    int show = rep->dimk < nloc ? rep->dimk : nloc;
    for (int v = 0; v < show; ++v)
    {
        const GF *co = rep->ker + (size_t)v * K1;
        int hi = -1, terms = 0, zeros = 0, allerr = 1;
        for (int i = 0; i < K1; ++i) if (co[i]) { hi = i; ++terms; }
        if (hi < 0) continue;
        GF inv = ginv(co[hi]);
        for (int p = 0; p < n; ++p)
        {
            GF z = 0;
            for (int i = 0; i <= hi; ++i)
                z ^= gmul(co[i], c->A.v[(size_t)i * n + p]);
            if (!z) ++zeros;
        }
        for (int k = 0; k < nerrpos; ++k)
        {
            GF z = 0;
            for (int i = 0; i <= hi; ++i)
                z ^= gmul(co[i], c->A.v[(size_t)i * n + errpos[k]]);
            if (z) allerr = 0;
        }
        if (v == 0)
            printf("Sigma(x,z,w) = monic, minimal-order function vanishing at the error positions\n");
        else
            printf("\n(kernel element #%d, for reference)\n", v + 1);
        printf("leading basis index = %d (uses the first %d functions of L(A)), %d terms, g = primitive element of GF(2^%d)\n",
               hi, hi + 1, terms, BB_C);
        int first = 1;
        for (int i = hi; i >= 0; --i)
        {
            if (!co[i]) continue;
            GF cs = gmul(co[i], inv);
            printf("%s", first ? "   " : " + ");
            print_term(c, cs, i);
            printf("\n");
            first = 0;
        }
        printf("  -> vanishes at %d of %d rational points; vanishes at all decoded error positions: %s\n",
               zeros, n, allerr ? "yes" : "NO");
    }
    printf("\n(kernel dimension = %d; common zero set |Z| = %d points contains the error positions)\n",
           rep->dimk, rep->nz);
}

static void show_errors(const Code *c, const Point *pts, const GF *rcv, const GF *dec,
                        const GF *err, int decoded_ok)
{
    int n = c->n, nd = 0, nt = 0, wrong = 0;
    printf("\n==== Error list ====\n");
    printf("%5s %6s  %-10s %-10s  %-12s %-12s %s\n",
           "#", "pos", "x", "y", "decoded e", "injected e", "check");
    int row = 0;
    for (int p = 0; p < n; ++p)
    {
        GF ed = decoded_ok ? (GF)(rcv[p] ^ dec[p]) : 0;
        GF et = err[p];
        if (!ed && !et) continue;
        ++row;
        if (ed) ++nd;
        if (et) ++nt;
        int match = (ed == et);
        if (!match) ++wrong;
        char sd[24], st[24], sx[24], sy[24];
        if (ed) snprintf(sd, sizeof sd, "g^%d", LOGT[ed]); else snprintf(sd, sizeof sd, "0");
        if (et) snprintf(st, sizeof st, "g^%d", LOGT[et]); else snprintf(st, sizeof st, "0");
        snprintf(sx, sizeof sx, "g^%d", LOGT[pts[p].x]);
        snprintf(sy, sizeof sy, "g^%d", LOGT[pts[p].y]);
        printf("%5d %6d  %-10s %-10s  %-12s %-12s %s\n", row, p, sx, sy, sd, st,
               match ? "OK" : (ed ? (et ? "WRONG VALUE" : "FALSE POSITIVE") : "MISSED"));
    }
    printf("decoded errors = %d, injected errors = %d, mismatching rows = %d\n", nd, nt, wrong);
}

int main(int argc, char **argv)
{
    int a=3, b=2, v=149, t=80, errors=1, seed=1, trials=1, list=1, locator=1, fast=0, autop=0;
    for (int i=1; i<argc; ++i) {
        int *dst=NULL;
        if (!strcmp(argv[i],"--a")) dst=&a;
        else if (!strcmp(argv[i],"--b")) dst=&b;
        else if (!strcmp(argv[i],"--v")) dst=&v;
        else if (!strcmp(argv[i],"--t")) dst=&t;
        else if (!strcmp(argv[i],"--errors")) dst=&errors;
        else if (!strcmp(argv[i],"--seed")) dst=&seed;
        else if (!strcmp(argv[i],"--trials")) dst=&trials;
        else if (!strcmp(argv[i],"--list")) dst=&list;
        else if (!strcmp(argv[i],"--locator")) dst=&locator;
        else if (!strcmp(argv[i],"--fast")) dst=&fast;
        else if (!strcmp(argv[i],"--auto")) dst=&autop;
        else if (!strcmp(argv[i],"--help") || !strcmp(argv[i],"-h")) {
            printf("BBGS binary ECP decoder (q=2)\n"
                   "Usage: %s [--a A --b B --v V --t T --errors E --trials N --seed S\n"
                   "          --list 0|1 --locator N --fast 0|1 --auto 0|1]\n"
                   "  --auto 1     choose v,t automatically from --errors (ignores --v/--t)\n"
                   "  --fast 1     large n (e.g. GF(2^9)): zero codeword, no H/verify/nullspace,\n"
                   "               B evaluated lazily, no independence check (assumes deg < n)\n"
                   "  --errors E   number of injected errors (1..%d)\n"
                   "  --list 0|1   print the error position/value table (first trial)\n"
                   "  --locator N  print up to N locator functions (0 = none, first trial)\n"
                   "Default: a=3 b=2 over GF(2^5), v=149, t=80\n"
                   "Allowed: a>b>=2, a odd, gcd(a,b)=1, a+b<=%d\n"
                   "  e.g. (3,2) (5,2) (5,3) (5,4) (7,2) (7,3) (7,4) (7,5) (9,2)\n"
                   "Large n (c>=9): use --fast 1\n",
                   argv[0], MAX_ERRORS, MAX_M);
            return 0;
        } else { fprintf(stderr,"Unknown option: %s\n",argv[i]); return 2; }
        if (i+1>=argc || !parse_int(argv[++i],dst)) {
            fprintf(stderr,"Bad option value for %s\n",argv[i-1]); return 2;
        }
    }
    if (a<3 || b<2 || a<=b || a+b>MAX_M || !(a&1) || gcd(a,b)!=1 ||
        v<0 || t<0 || errors<1 || trials<1) {
        fprintf(stderr,"Require a>b>=2, a+b<=%d, gcd(a,b)=1, a odd, and nonnegative v,t.\n",MAX_M);
        return 2;
    }
    if (errors>MAX_ERRORS) {
        fprintf(stderr,"--errors must be at most %d.\n",MAX_ERRORS);
        return 2;
    }
    BB_A=a; BB_B=b; BB_C=a+b;
    if (!gf_init(BB_C)) { fprintf(stderr,"GF(2^%d) initialization failed.\n",BB_C); return 2; }

    /*
     * 点の列挙: H(x,y) は y について F_2 線形 (Frobenius は加法的) なので、
     * 各 x で L_x(e_i) を 13 個計算し、y を Gray code で全走査して L_x(y)=1 を探す。
     */
    size_t pcap=(size_t)1<<20, pn=0;
    Point *pts=malloc(pcap*sizeof(*pts));
    if (!pts) { fprintf(stderr,"Point allocation failed.\n"); return 1; }
    {
        static GF FROB[MAX_M][MAX_M]; /* FROB[e][i] = (2^i)^(2^e) */
        for (int e=0;e<BB_C;++e) for (int i=0;i<BB_C;++i) FROB[e][i]=frob2((GF)(1u<<i),e);
        GF T[MAX_M], invx[MAX_M];
        for (int x=1; x<GQ; ++x) {
            GF xx=(GF)x;
            for (int k=0;k<BB_C;++k) invx[k]=ginv(frob2(xx,k));
            for (int i=0;i<BB_C;++i) {
                GF sum=0;
                for (int k=0;k<BB_C;++k)
                    sum^=gmul(FROB[(BB_A+k)%BB_C][i],invx[k]);
                T[i]=sum;
            }
            GF y=0, val=0;
            for (unsigned idx=1; idx<(unsigned)GQ; ++idx) {
                int bit=__builtin_ctz(idx);
                y^=(GF)(1u<<bit); val^=T[bit];
                if (val==1) {
                    if (pn==pcap) {
                        pcap*=2;
                        Point *np=realloc(pts,pcap*sizeof(*pts));
                        if (!np) { fprintf(stderr,"Point allocation failed.\n"); return 1; }
                        pts=np;
                    }
                    pts[pn++]=(Point){xx,y};
                }
            }
        }
    }
    int n=(int)pn;
    /* 走査結果の確認: 定義式 bbgs_define_equation で一部の点を再検証 */
    for (int p=0; p<n; p+=(n/64>0?n/64:1))
        if (bbgs_define_equation(pts[p].x,pts[p].y)!=1) {
            fprintf(stderr,"Point enumeration inconsistent with the defining equation.\n");
            return 1;
        }

    int64_t qc=(int64_t)1<<BB_C;
    int64_t genus=((qc-2)*(((int64_t)1<<(a-1))+((int64_t)1<<(b-1))-2)+(qc-2))/2;
    printf("BBGS binary curve: q=2, a=%d, b=%d, c=%d over GF(2^%d)\n",a,b,a+b,a+b);
    printf("Defining equation: sum[k=0..%d] y^(2^(a+k))/x^(2^k) = 1\n",BB_C-1);
    printf("Affine candidate points n=%d; genus formula g=%lld\n",n,(long long)genus);
    if (!n) { fprintf(stderr,"No affine rational points.\n"); free(pts); return 1; }
    if (autop) {
        /* t: 2^(b-1)*t - 2g + 1 >= errors,  v: l(A) = #{i in [-v,0] admissible} >= errors+1 */
        int64_t d=(int64_t)1<<(b-1);
        int64_t tt=(2*genus-1+errors+d-1)/d;
        int64_t cntA=0, vv=0, j0, k0;
        for (vv=0; vv<=(int64_t)64*genus+100000; ++vv) {
            if (bb_cand_ok(-vv,0,0,0,&j0,&k0)) ++cntA;
            if (cntA>=errors+1) break;
        }
        t=(int)tt; v=(int)vv;
        printf("auto: v=%d, t=%d (for %d errors)\n",v,t,errors);
    }
    if (!fast && n>20000) printf("Note: n=%d is large; --fast 1 is recommended.\n",n);

    /* 補助関数 z,w の値を全点で一度だけ計算 */
    PZ=calloc((size_t)n,sizeof(GF)); PW=calloc((size_t)n,sizeof(GF));
    for (int p=0;p<n;p++)
        if (!bb_point_data_nc(pts[p].x,pts[p].y,&PZ[p],&PW[p])) {
            fprintf(stderr,"Some evaluation points are incompatible with the BBGS auxiliary functions (u=0).\n");
            free(pts); return 1;
        }

    PTS=pts;
    Code code; code.n=n;
    int cdim=0;
    GF *ker=NULL;
    if (fast) {
        code.A=bb_build_basis(v,0,0,0,pts,n,1,0);
        code.B=bb_build_basis(0,0,t,0,pts,n,0,0);
        code.H=(Basis){0,NULL,NULL,NULL,NULL};
        if (!code.A.cnt || !code.B.cnt) {
            fprintf(stderr,"A required Omega/RR basis is empty; adjust --v/--t.\n");
            free(pts); return 1;
        }
        printf("fast mode: zero codeword, H/verification skipped, B evaluated lazily.\n");
    } else {
        code.A=bb_build_basis(v,0,0,0,pts,n,1,1);
        code.B=bb_build_basis(0,0,t,0,pts,n,1,1);
        code.H=bb_build_basis(v,0,t,0,pts,n,1,1);
        if (!code.A.cnt || !code.B.cnt || !code.H.cnt) {
            fprintf(stderr,"A required Omega/RR basis is empty; adjust --v/--t.\n");
            free(pts); return 1;
        }
        if (!bb_verify_product_basis(&code.A,&code.B,&code.H,n)) {
            fprintf(stderr,"A*B subset H verification failed.\n");
            free(pts); return 1;
        }
        printf("A*B subset H: verified (%d x %d basis products).\n",code.A.cnt,code.B.cnt);
        ker=nullspace(code.H.v,code.H.cnt,n,&cdim);
        if (!ker || cdim<=0) { fprintf(stderr,"Code dimension is zero or nullspace allocation failed.\n"); free(pts); return 1; }
    }
    int64_t degB=(int64_t)t*((int64_t)1<<(b-1));
    int guarantee=degB>2*genus-2 ? (int)(degB-2*genus+1) : 0;
    if (code.A.cnt-1<guarantee) guarantee=code.A.cnt-1;
    if (fast) printf("Dimensions: l(A)=%d, l(B)=%d (fast mode)\n",code.A.cnt,code.B.cnt);
    else printf("Dimensions: l(A)=%d, l(B)=%d, l(A+B)=%d; dim(C)=%d\n",
           code.A.cnt,code.B.cnt,code.H.cnt,cdim);
    printf("ECP bound estimate: errors <= %d (under divisor/basis hypotheses).\n",guarantee);
    if (errors>n) { fprintf(stderr,"--errors exceeds n.\n"); free(ker); free(pts); return 2; }
    if (errors>guarantee)
        printf("Warning: requested errors (%d) exceed the estimate; decoding may fail.\n",errors);

    rng_state=(uint64_t)(unsigned)seed*0x2545F4914F6CDD1DULL+12345;
    GF *cw=calloc((size_t)n,sizeof(GF)), *rcv=malloc((size_t)n*sizeof(GF));
    GF *err=calloc((size_t)n,sizeof(GF)), *dec=malloc((size_t)n*sizeof(GF));
    int *idx=malloc((size_t)n*sizeof(int));
    if (!cw||!rcv||!err||!dec||!idx) { fprintf(stderr,"Trial allocation failed.\n"); return 1; }
    int succ=0,fail=0,miscor=0;
    for (int tr=0; tr<trials; ++tr) {
        memset(cw,0,(size_t)n*sizeof(GF));
        for (int k=0;k<cdim;k++) {
            GF co=(GF)(rnd()%(uint64_t)GQ);
            for (int p=0;p<n;p++) cw[p]^=gmul(co,ker[(size_t)k*n+p]);
        }
        memset(err,0,(size_t)n*sizeof(GF));
        for (int p=0;p<n;p++) idx[p]=p;
        for (int e=0;e<errors;e++) {
            int j=e+(int)(rnd()%(uint64_t)(n-e));
            int z=idx[e]; idx[e]=idx[j]; idx[j]=z;
            err[idx[e]]=(GF)(1+rnd()%(uint64_t)(GQ-1));
        }
        for (int p=0;p<n;p++) rcv[p]=cw[p]^err[p];
        Report rep={0,NULL,0,NULL};
        int ne=0, ok=decode(&code,rcv,dec,&ne,&rep), same=ok&&!memcmp(cw,dec,(size_t)n*sizeof(GF));
        if (same) succ++; else if (ok) miscor++; else fail++;
        if (trials==1) printf("Decode: %s (injected=%d, recovered=%d)\n",
                              same?"PASS":ok?"MISCORRECTION":"FAIL",errors,ne);
        if (tr==0 && (list || locator>0)) {
            if (trials>1) printf("--- details of trial 1: %s (injected=%d, recovered=%d) ---\n",
                                 same?"PASS":ok?"MISCORRECTION":"FAIL",errors,ne);
            int *ep=malloc(sizeof(int)*(size_t)(n+1)), nep=0;
            for (int p=0;p<n;p++) if (ok && (rcv[p]^dec[p])) ep[nep++]=p;
            if (locator>0) show_locator(&code,&rep,ep,nep,locator);
            if (list) show_errors(&code,pts,rcv,dec,err,ok);
            free(ep);
        }
        free(rep.ker); free(rep.Z);
    }
    if (trials>1) printf("%d trials: success=%d, miscorrection=%d, failure=%d\n",trials,succ,miscor,fail);

    free(cw); free(rcv); free(err); free(dec); free(idx); free(ker); free(pts); free(PZ); free(PW);
    free(code.A.v); free(code.B.v); free(code.H.v);
    free(code.A.ei); free(code.A.ej); free(code.A.ek);
    free(code.B.ei); free(code.B.ej); free(code.B.ek);
    free(code.H.ei); free(code.H.ej); free(code.H.ek);
    return fail||miscor ? 1 : 0;
}