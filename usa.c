/*
 * BBGS one-point/ECP decoder - single-file configurable prototype
 *
 * Curve family: binary BBGS model (q=2), parameter pair (a,b), c=a+b.
 * The defining relation is centralized in bbgs_define_equation()/bb_H().
 * The shared ECP decoder does not depend on a,b or on the curve equation.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -o bbgs_ag_decoder bbgs_ag_decoder.c
 * Example: ./bbgs_ag_decoder --a 3 --b 2 --v 149 --t 80 --errors 1 --trials 10
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

typedef uint16_t GF;

static int GQ; /* q = 2^m */
static GF EXPT[1024];
static int LOGT[512];

static int gf_init(int m)
{
    static const unsigned poly[10] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D, 0x211};
    if (m < 2 || m > 8)
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

/* 成功なら 1 を返し out に訂正語, *nerr に見つけた誤り個数 */
static int decode(const Code *c, const GF *rcv, GF *out, int *nerr)
{
    int n = c->n, K1 = c->A.cnt, K2 = c->B.cnt;
    int ok = 0;
    GF *S = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *ST = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *AR = malloc((size_t)n*sizeof(GF));
    int allzero = 1;
    *nerr = 0;
    memcpy(out, rcv, (size_t)n * sizeof(GF));

    for (int i = 0; i < K1; ++i)
    {
        for (int p = 0; p < n; ++p)
            AR[p] = gmul(rcv[p], c->A.v[(size_t)i * n + p]);
        for (int j = 0; j < K2; ++j)
        {
            GF z = 0;
            for (int p = 0; p < n; ++p)
                z ^= gmul(AR[p], c->B.v[(size_t)j * n + p]);
            S[(size_t)i * K2 + j] = z;
            ST[(size_t)j * K1 + i] = z;
            if (z)
                allzero = 0;
        }
    }
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
    free(ker);
    if (nz == 0 || nz > K1 * K2)
    {
        free(Z);
        goto done;
    }
    {
        int rows = K1 * K2, cols = nz + 1;
        GF *aug = calloc((size_t)rows * cols, sizeof(GF));
        int *piv = malloc(sizeof(int) * (rows + 1));
        for (int i = 0; i < K1; ++i)
            for (int j = 0; j < K2; ++j)
            {
                int r = i * K2 + j;
                for (int k = 0; k < nz; ++k)
                    aug[(size_t)r * cols + k] =
                        gmul(c->A.v[(size_t)i * n + Z[k]], c->B.v[(size_t)j * n + Z[k]]);
                aug[(size_t)r * cols + nz] = S[(size_t)i * K2 + j];
            }
        int rank = rref(aug, rows, cols, piv);
        int good = (rank == nz);
        for (int r = 0; r < rank && good; ++r)
            if (piv[r] == nz)
                good = 0; /* 矛盾した連立方程式 */
        if (good)
        {
            for (int k = 0; k < nz; ++k)
                out[Z[k]] ^= aug[(size_t)k * cols + nz];
            if (in_code(c, out))
            {
                ok = 1;
                for (int k = 0; k < nz; ++k)
                    if (aug[(size_t)k * cols + nz])
                        ++*nerr;
            }
        }
        free(aug);
        free(piv);
    }
    free(Z);
done:
    free(S);
    free(ST);
    free(AR);
    return ok;
}

static uint64_t rng_state;
static uint64_t rnd(void)
{
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
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
static GF bb_H(GF x, GF y) { return bbgs_define_equation(x, y); }
static int bb_point_data(GF x,GF y,GF *z,GF *w) {
    if (!x || !y || bb_H(x,y)!=1) return 0;
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
/* Basis from Hu's Omega lattice: x^i z^j w^k. */
static Basis bb_build_basis(int v,int rdiv,int sdiv,int tdiv,const Point *pts,int n) {
    const int64_t qc=((int64_t)1<<BB_C);
    const int64_t Nc=qc-1;
    const int64_t Nb=((int64_t)1<<BB_B)-1;
    const int64_t den=Nc;
    int cap=20000, rank=0;
    GF *ech=calloc((size_t)cap*n,sizeof(GF)), *out=calloc((size_t)cap*n,sizeof(GF));
    int64_t *ei=calloc(cap,sizeof(int64_t)), *ej=calloc(cap,sizeof(int64_t)), *ek=calloc(cap,sizeof(int64_t));
    GF *vec=malloc((size_t)n*sizeof(GF)), *raw=malloc((size_t)n*sizeof(GF));
    int *piv=calloc(cap,sizeof(int));
    int64_t start=-(int64_t)v;
    /* Hu, Proposition 6: exact finite i-range; j,k are ceilings from the divisor inequalities. */
    int64_t stop=(((int64_t)1<<(BB_A-1))-1)*rdiv
                 + ((int64_t)1<<(BB_B-1))*sdiv + tdiv;
    for (int64_t i=start;i<=stop;i++) {
        int64_t j=ceil_div_posden((((int64_t)1<<BB_A)*i)-sdiv,den);
        int64_t k=ceil_div_posden(-i-rdiv,den);
        int64_t lhs=(((int64_t)1<<(BB_A-1))*Nb)*i
                    - (((int64_t)1<<(BB_B-1))*Nc)*j + tdiv;
        int64_t rhs=((((int64_t)1<<(BB_A-1))-1)*Nc)*k;
        if (lhs < rhs) continue;
        if (rank>=cap) { fprintf(stderr,"BBGS basis capacity exceeded\n"); break; }
        for (int p=0;p<n;p++) {
            GF z,w;
            if (!bb_point_data(pts[p].x,pts[p].y,&z,&w)) { raw[p]=0; continue; }
            GF val=gmul(gpow(pts[p].x,(int)((i%(GQ-1)+(GQ-1))%(GQ-1))),
                             gmul(gpow(z,(int)((j%(GQ-1)+(GQ-1))%(GQ-1))),
                                  gpow(w,(int)((k%(GQ-1)+(GQ-1))%(GQ-1)))));
            raw[p]=val;
        }
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
        memcpy(out+(size_t)rank*n,raw,(size_t)n*sizeof(GF));
        ei[rank]=i; ej[rank]=j; ek[rank]=k;
        rank++;
    }
    free(ech); free(vec); free(raw); free(piv);
    Basis b={rank,out,ei,ej,ek}; return b;
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

static int bb_eval_check(const Point *pts,int n) {
    for(int p=0;p<n;p++) {
        GF z,w;
        if(!bb_point_data(pts[p].x,pts[p].y,&z,&w)) return 0;
    }
    return 1;
}

static int gcd(int x,int y) { while(y){int z=x%y;x=y;y=z;} return x; }


int main(int argc, char **argv)
{
    int a=3, b=2, v=149, t=80, errors=1, seed=1, trials=1;
    for (int i=1; i<argc; ++i) {
        int *dst=NULL;
        if (!strcmp(argv[i],"--a")) dst=&a;
        else if (!strcmp(argv[i],"--b")) dst=&b;
        else if (!strcmp(argv[i],"--v")) dst=&v;
        else if (!strcmp(argv[i],"--t")) dst=&t;
        else if (!strcmp(argv[i],"--errors")) dst=&errors;
        else if (!strcmp(argv[i],"--seed")) dst=&seed;
        else if (!strcmp(argv[i],"--trials")) dst=&trials;
        else if (!strcmp(argv[i],"--help") || !strcmp(argv[i],"-h")) {
            printf("BBGS binary ECP decoder (q=2)\n"
                   "Usage: %s [--a A --b B --v V --t T --errors E --trials N --seed S]\n"
                   "Default: a=3 b=2 over GF(2^5), v=149, t=80\n", argv[0]);
            return 0;
        } else { fprintf(stderr,"Unknown option: %s\n",argv[i]); return 2; }
        if (i+1>=argc || !parse_int(argv[++i],dst)) {
            fprintf(stderr,"Bad option value for %s\n",argv[i-1]); return 2;
        }
    }
    if (a<3 || b<2 || a!=b+1 || a+b>8 || !(a&1) || gcd(a,b)!=1 ||
        v<0 || t<0 || errors<1 || trials<1) {
        fprintf(stderr,"Require a=b+1, b>=2, a+b<=8, gcd(a,b)=1, a odd, and nonnegative v,t.\n");
        return 2;
    }
    BB_A=a; BB_B=b; BB_C=a+b;
    if (!gf_init(BB_C)) { fprintf(stderr,"GF(2^%d) initialization failed.\n",BB_C); return 2; }

    size_t max_points=(size_t)GQ*GQ;
    Point *pts=malloc(max_points*sizeof(*pts));
    if (!pts) { fprintf(stderr,"Point allocation failed.\n"); return 1; }
    int n=0;
    for (int x=1; x<GQ; ++x)
        for (int y=1; y<GQ; ++y)
            if (bb_H((GF)x,(GF)y)==1)
                pts[n++]=(Point){(GF)x,(GF)y};

    int64_t qc=(int64_t)1<<BB_C;
    int64_t genus=((qc-2)*(((int64_t)1<<(a-1))+((int64_t)1<<(b-1))-2)+(qc-2))/2;
    printf("BBGS binary curve: q=2, a=%d, b=%d, c=%d over GF(2^%d)\n",a,b,a+b,a+b);
    printf("Defining equation: sum[k=0..%d] y^(2^(a+k))/x^(2^k) = 1\n",BB_C-1);
    printf("Affine candidate points n=%d; genus formula g=%lld\n",n,(long long)genus);
    if (!n) { fprintf(stderr,"No affine rational points.\n"); free(pts); return 1; }
    if (!bb_eval_check(pts,n)) {
        fprintf(stderr,"Some evaluation points are incompatible with the BBGS auxiliary functions (u=0).\n");
        free(pts); return 1;
    }

    Code code; code.n=n;
    code.A=bb_build_basis(v,0,0,0,pts,n);
    code.B=bb_build_basis(0,0,t,0,pts,n);
    code.H=bb_build_basis(v,0,t,0,pts,n);
    if (!code.A.cnt || !code.B.cnt || !code.H.cnt) {
        fprintf(stderr,"A required Omega/RR basis is empty; adjust --v/--t.\n");
        free(pts); return 1;
    }
    if (!bb_verify_product_basis(&code.A,&code.B,&code.H,n)) {
        fprintf(stderr,"A*B subset H verification failed.\n");
        free(pts); return 1;
    }
    printf("A*B subset H: verified (%d x %d basis products).\n",code.A.cnt,code.B.cnt);

    int cdim=0;
    GF *ker=nullspace(code.H.v,code.H.cnt,n,&cdim);
    if (!ker || cdim<=0) { fprintf(stderr,"Code dimension is zero or nullspace allocation failed.\n"); free(pts); return 1; }
    int64_t degB=(int64_t)t*((int64_t)1<<(b-1));
    int guarantee=degB>2*genus-2 ? (int)(degB-2*genus+1) : 0;
    if (code.A.cnt-1<guarantee) guarantee=code.A.cnt-1;
    printf("Dimensions: l(A)=%d, l(B)=%d, l(A+B)=%d; dim(C)=%d\n",
           code.A.cnt,code.B.cnt,code.H.cnt,cdim);
    printf("ECP bound estimate: errors <= %d (under divisor/basis hypotheses).\n",guarantee);
    if (errors>n) { fprintf(stderr,"--errors exceeds n.\n"); free(ker); free(pts); return 2; }

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
        int ne=0, ok=decode(&code,rcv,dec,&ne), same=ok&&!memcmp(cw,dec,(size_t)n*sizeof(GF));
        if (same) succ++; else if (ok) miscor++; else fail++;
        if (trials==1) printf("Decode: %s (injected=%d, recovered=%d)\n",
                              same?"PASS":ok?"MISCORRECTION":"FAIL",errors,ne);
    }
    if (trials>1) printf("%d trials: success=%d, miscorrection=%d, failure=%d\n",trials,succ,miscor,fail);

    free(cw); free(rcv); free(err); free(dec); free(idx); free(ker); free(pts);
    free(code.A.v); free(code.B.v); free(code.H.v);
    free(code.A.ei); free(code.A.ej); free(code.A.ek);
    free(code.B.ei); free(code.B.ej); free(code.B.ek);
    free(code.H.ei); free(code.H.ej); free(code.H.ek);
    return fail||miscor ? 1 : 0;
}
