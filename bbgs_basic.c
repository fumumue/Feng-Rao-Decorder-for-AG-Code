/*
 * BBGS tower: first non-rational level E_2, experimental basic syndrome decoder.
 * Binary characteristic prototype: p=2, n=2m+1, m=1 or 2.
 *
 * E_2/F_(2^n)(x) is defined by
 *   Tr_j(y / x^(2^k)) + Tr_k(y^(2^j) / x) = 1,
 * where j=m if m is odd, otherwise j=m+1, and k=n-j.
 * We enumerate affine rational points with x != 0.
 *
 * The parity-check matrix evaluates all monomials x^a y^b of total degree
 * <= u+v. The syndrome matrix has entries S_(a+b). Its kernel gives
 * candidate error-locator functions. This is an experimental affine
 * evaluation-code construction, NOT a completed RR/Feng-Rao decoder.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1024
#define MAXMON 256

typedef struct { int x, y; } Point;
typedef struct { int a, b; } Mon;

static int Q, J, K, IRR;
static Point pts[MAXN];
static int npts;

static int gf_mul(int a, int b) {
    int r = 0;
    while (b) {
        if (b & 1) r ^= a;
        b >>= 1;
        a <<= 1;
        if (a & Q) a ^= IRR;
    }
    return r & (Q - 1);
}
static int gf_pow(int a, int e) {
    int r = 1;
    while (e) {
        if (e & 1) r = gf_mul(r, a);
        a = gf_mul(a, a);
        e >>= 1;
    }
    return r;
}
static int gf_inv(int a) { return a ? gf_pow(a, Q - 2) : 0; }
static int trace2(int z, int r) {
    int s = 0;
    for (int i = 0; i < r; ++i) { s ^= z; z = gf_mul(z, z); }
    return s;
}
static int init_field(int m) {
    if (m == 1) { Q = 8; IRR = 0x0b; }
    else if (m == 2) { Q = 32; IRR = 0x25; }
    else return 0;
    J = (m % 2) ? m : m + 1;
    K = 2 * m + 1 - J;
    return 1;
}
static int bbgs_equation(int x, int y) {
    int xpk = gf_pow(x, 1 << K);
    int term1 = trace2(gf_mul(y, gf_inv(xpk)), J);
    int ypj = gf_pow(y, 1 << J);
    int term2 = trace2(gf_mul(ypj, gf_inv(x)), K);
    return (term1 ^ term2) == 1;
}
static void enumerate_points(void) {
    npts = 0;
    for (int x = 1; x < Q; ++x)
        for (int y = 0; y < Q; ++y)
            if (bbgs_equation(x, y) && npts < MAXN) pts[npts++] = (Point){x,y};
}
static int monomials(int d, Mon *out) {
    int n = 0;
    for (int a = 0; a <= d; ++a)
        for (int b = 0; b + a <= d; ++b) out[n++] = (Mon){a,b};
    return n;
}
static int eval_mon(Mon m, Point p) {
    return gf_mul(gf_pow(p.x, m.a), gf_pow(p.y, m.b));
}
static int rref(int *A, int rows, int cols, int *piv) {
    int r = 0;
    for (int c = 0; c < cols && r < rows; ++c) {
        int pr = -1;
        for (int i = r; i < rows; ++i)
            if (A[i*cols+c]) { pr = i; break; }
        if (pr < 0) continue;
        if (pr != r) for (int j = 0; j < cols; ++j) {
            int t=A[r*cols+j]; A[r*cols+j]=A[pr*cols+j]; A[pr*cols+j]=t;
        }
        int iv = gf_inv(A[r*cols+c]);
        for (int j = 0; j < cols; ++j) A[r*cols+j]=gf_mul(iv,A[r*cols+j]);
        for (int i = 0; i < rows; ++i) if (i != r && A[i*cols+c]) {
            int f=A[i*cols+c];
            for (int j = 0; j < cols; ++j) A[i*cols+j] ^= gf_mul(f,A[r*cols+j]);
        }
        piv[r++] = c;
    }
    return r;
}
static int nullspace(const int *A, int rows, int cols, int *out) {
    int R[MAXMON*MAXMON], piv[MAXMON], is_piv[MAXMON]={0};
    if (rows*cols > MAXMON*MAXMON) return -1;
    memcpy(R,A,sizeof(int)*rows*cols);
    int rank=rref(R,rows,cols,piv);
    for (int i=0;i<rank;i++) is_piv[piv[i]]=1;
    int nv=0;
    for (int f=0;f<cols;f++) if (!is_piv[f]) {
        int *v=out+nv*cols; memset(v,0,sizeof(int)*cols); v[f]=1;
        for (int i=0;i<rank;i++) v[piv[i]]=R[i*cols+f];
        nv++;
    }
    return nv;
}
static int solve_unique(int *A, int rows, int cols, const int *rhs, int *x) {
    int aug[MAXMON*(MAXN+1)], piv[MAXN+1];
    if (rows*(cols+1)>MAXMON*(MAXN+1)) return 0;
    for(int i=0;i<rows;i++){
        for(int j=0;j<cols;j++) aug[i*(cols+1)+j]=A[i*cols+j];
        aug[i*(cols+1)+cols]=rhs[i];
    }
    int rank=rref(aug,rows,cols+1,piv);
    for(int i=0;i<rank;i++) if(piv[i]==cols) return 0;
    int cr=0;
    for(int i=0;i<rank;i++) if(piv[i]<cols) cr++;
    if(cr<cols) return 0;
    for(int j=0;j<cols;j++) x[j]=0;
    for(int i=0;i<rank;i++) if(piv[i]<cols) x[piv[i]]=aug[i*(cols+1)+cols];
    return 1;
}
static unsigned rng=1;
static unsigned rnd(void){rng^=rng<<13;rng^=rng>>17;rng^=rng<<5;return rng;}

static int nullspace_large(const int *A, int rows, int cols, int *out) {
    int lim = rows < cols ? rows : cols;
    int *R = (int *)malloc(sizeof(int) * (size_t)rows * (size_t)cols);
    int *piv = (int *)malloc(sizeof(int) * (size_t)lim);
    unsigned char *is_piv = (unsigned char *)calloc((size_t)cols, 1);
    if (!R || !piv || !is_piv) { free(R); free(piv); free(is_piv); return -1; }
    memcpy(R, A, sizeof(int) * (size_t)rows * (size_t)cols);
    int rank = rref(R, rows, cols, piv);
    for (int i = 0; i < rank; ++i) is_piv[piv[i]] = 1;
    int dim = 0;
    for (int f = 0; f < cols; ++f) if (!is_piv[f]) {
        int *vec = out + (size_t)dim * (size_t)cols;
        memset(vec, 0, sizeof(int) * (size_t)cols);
        vec[f] = 1;
        for (int i = 0; i < rank; ++i)
            vec[piv[i]] = R[(size_t)i * (size_t)cols + (size_t)f];
        ++dim;
    }
    free(R); free(piv); free(is_piv);
    return dim;
}

static int make_random_codeword(int degree, int *word, int *dimension) {
    Mon mons[MAXMON];
    int nh = monomials(degree, mons);
    if (nh <= 0 || nh > MAXMON) return 0;
    int *H = (int *)malloc(sizeof(int) * (size_t)nh * (size_t)npts);
    int *basis = (int *)calloc((size_t)npts * (size_t)npts, sizeof(int));
    if (!H || !basis) { free(H); free(basis); return 0; }
    for (int h = 0; h < nh; ++h)
        for (int p = 0; p < npts; ++p)
            H[h*npts+p] = eval_mon(mons[h], pts[p]);
    int dim = nullspace_large(H, nh, npts, basis);
    if (dim <= 0) { free(H); free(basis); return 0; }
    memset(word, 0, sizeof(int) * (size_t)npts);
    for (int z = 0; z < dim; ++z) {
        int coefficient = (int)(rnd() % (unsigned)Q);
        if (!coefficient) continue;
        for (int p = 0; p < npts; ++p)
            word[p] ^= gf_mul(coefficient, basis[z*npts+p]);
    }
    *dimension = dim;
    free(H); free(basis);
    return 1;
}

static int decode(const int *received, int u, int v, int *corrected,
                  int *candidate_count, int *kernel_dim, int *check_rank) {
    Mon Amon[MAXMON],Bmon[MAXMON],Hmon[MAXMON];
    int na=monomials(u,Amon), nb=monomials(v,Bmon), nh=monomials(u+v,Hmon);
    if(na>MAXMON||nb>MAXMON||nh>MAXMON||nh*npts>MAXMON*MAXN) return 0;
    int H[MAXMON*MAXN], syn[MAXMON]={0};
    for(int h=0;h<nh;h++) for(int p=0;p<npts;p++) H[h*npts+p]=eval_mon(Hmon[h],pts[p]);
    for(int h=0;h<nh;h++) for(int p=0;p<npts;p++) syn[h]^=gf_mul(H[h*npts+p],received[p]);

    int MM[MAXMON*MAXMON];
    for(int i=0;i<na;i++) for(int j=0;j<nb;j++) {
        Mon sum={Amon[i].a+Bmon[j].a,Amon[i].b+Bmon[j].b};
        int idx=-1;
        for(int h=0;h<nh;h++)
            if(Hmon[h].a==sum.a&&Hmon[h].b==sum.b){idx=h;break;}
        if(idx<0) return 0;
        MM[j*na+i]=syn[idx];
    }
    int ker[MAXMON*MAXMON], nk=nullspace(MM,nb,na,ker);
    if(nk<0) return 0;
    *kernel_dim=nk;

    int candidates[MAXN],nc=0;
    for(int p=0;p<npts;p++) {
        int common=1;
        for(int z=0;z<nk&&common;z++) {
            int val=0;
            for(int a=0;a<na;a++) val^=gf_mul(ker[z*na+a],eval_mon(Amon[a],pts[p]));
            if(val) common=0;
        }
        if(common) candidates[nc++]=p;
    }
    *candidate_count=nc;
    if(nc<=0||nc>MAXN||nc>nh) return 0;

    int AZ[MAXMON*MAXN],rhs[MAXMON],err[MAXN];
    for(int h=0;h<nh;h++){
        rhs[h]=syn[h];
        for(int z=0;z<nc;z++) AZ[h*nc+z]=H[h*npts+candidates[z]];
    }
    if(!solve_unique(AZ,nh,nc,rhs,err)) return 0;
    memcpy(corrected,received,sizeof(int)*npts);
    for(int z=0;z<nc;z++) corrected[candidates[z]]^=err[z];

    for(int h=0;h<nh;h++){
        int s=0;
        for(int p=0;p<npts;p++) s^=gf_mul(H[h*npts+p],corrected[p]);
        if(s) return 0;
    }
    int *tmp=malloc(sizeof(int)*nh*npts);
    if(tmp){
        memcpy(tmp,H,sizeof(int)*nh*npts);
        int piv[MAXN]; *check_rank=rref(tmp,nh,npts,piv); free(tmp);
    } else *check_rank=-1;
    return 1;
}
static void usage(const char *p) {
    printf("Usage: %s [--m 1|2] [--u N] [--v N] [--errors T] [--seed N] [--trials N]\n",p);
    puts("GF(2^(2m+1)): m=1 gives GF(8), m=2 gives GF(32).");
    puts("u,v are total-degree bounds for the two sides of the syndrome matrix.");
}
int main(int argc,char **argv) {
    int m=2,u=4,v=4,errors=10,seed=1,trials=1;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--help")||!strcmp(argv[i],"-h")){usage(argv[0]);return 0;}
        if(i+1>=argc){fprintf(stderr,"missing value for %s\n",argv[i]);return 2;}
        char *name=argv[i]; int z=atoi(argv[++i]);
        if(!strcmp(name,"--m"))m=z;
        else if(!strcmp(name,"--u"))u=z;
        else if(!strcmp(name,"--v"))v=z;
        else if(!strcmp(name,"--errors"))errors=z;
        else if(!strcmp(name,"--seed"))seed=z;
        else if(!strcmp(name,"--trials"))trials=z;
        else {fprintf(stderr,"unknown option %s\n",name);return 2;}
    }
    if(!init_field(m)||u<0||v<0||u+v>8||errors<0||errors>MAXN||trials<1||trials>10000){
        fprintf(stderr,"unsupported parameters\n");return 2;
    }
    enumerate_points(); rng=(unsigned)seed+1;
    printf("BBGS E2 basic syndrome decoder (experimental affine code)\nGF(2^%d), q=%d, j=%d, k=%d\n",2*m+1,Q,J,K);
    printf("Affine rational support: n=%d (x != 0)\n",npts);
    printf("Locator degrees: u=%d, v=%d; check monomials degree <= %d\n",u,v,u+v);
    if(errors>npts){fprintf(stderr,"errors must be <= n=%d\n",npts);return 2;}
    if(errors==0){
        puts("No-error case: no correction is necessary.");
        return 0;
    }

    int successes=0;
    for(int trial=1;trial<=trials;trial++){
        int original[MAXN]={0},received[MAXN]={0},corrected[MAXN]={0},used[MAXN]={0};
        int code_dim=0;
        if(!make_random_codeword(u+v,original,&code_dim)){
            fprintf(stderr,"could not construct a nontrivial codeword space\n");return 2;
        }
        memcpy(received,original,sizeof(int)*npts);
        for(int i=0;i<errors;i++){
            int pos; do{pos=(int)(rnd()%(unsigned)npts);}while(used[pos]);
            used[pos]=1;
            int e=1+(int)(rnd()%(unsigned)(Q-1));
            received[pos]^=e;
            if(trials==1) printf("error[%d]: point=(%d,%d), value=%d\n",i+1,pts[pos].x,pts[pos].y,e);
        }
        int nc=0,nk=0,rk=0;
        int ok=decode(received,u,v,corrected,&nc,&nk,&rk);
        int exact=ok;
        if(ok) for(int p=0;p<npts;p++) if(corrected[p]!=original[p]) exact=0;
        if(exact) successes++;
        if(trials==1){
            printf("code dimension=%d; check-matrix rank=%d; locator-kernel dimension=%d; common-zero candidates=%d\n",
                   code_dim,rk,nk,nc);
            puts(exact?"DECODE: PASS (arbitrary codeword recovered exactly)":"DECODE: FAIL/AMBIGUOUS");
        }
    }
    if(trials>1) printf("Trials: %d, errors per trial: %d, successes: %d/%d\n",trials,errors,successes,trials);
    return successes==trials ? 0 : 1;
}
