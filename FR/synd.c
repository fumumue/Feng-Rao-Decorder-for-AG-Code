/*
 * syndrome_table.c -- Hermitian one-point code  X^(q+1) = Y^q + Y  over GF(q^2), char 2, no parity-check matrix.
 *
 *   syndrome_table()        : error vector (or received word) r  ->  syndrome table T[i][j] = sum_k r_k x_k^i y_k^j
 *                             for all (i,j) with q*i+(q+1)*j <= M.  Zero r_k are skipped (sparse e costs only t*entries).
 *   syndrome_extend()       : only the entries with j < q are independent syndromes; fills the rest by y^q = x^(q+1)+y.
 *   error_from_syndrome()   : syndrome table -> error positions and values  (basic algorithm, Pellikaan / Skorobogatov-Vladut)
 *                             corrects up to tmax = (M - 3g + 1)/2 errors, g = q(q-1)/2.
 *
 * Build: cc -O2 -std=gnu11 -o syndrome_table syndrome_table.c
 * Run  : ./syndrome_table m M nuse [t [seed [mem_MB]]]   (m even; points = first nuse of the q^3 affine points;
 *        mem_MB: memory budget, default 70% of available RAM; work arrays that do not fit cut the search off)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
typedef uint16_t fe;
static int FM, FS, FO; static fe *gexp, *glog;
static void gf_init(int m, unsigned poly){ FM=m; FS=1<<m; FO=FS-1; gexp=malloc(sizeof(fe)*(2*FO+4)); glog=malloc(sizeof(fe)*FS);
  unsigned x=1; for(int i=0;i<FO;i++){gexp[i]=x; glog[x]=i; x<<=1; if(x&FS) x^=poly;} for(int i=FO;i<2*FO+4;i++) gexp[i]=gexp[i-FO]; glog[0]=0; }
static inline fe mul(fe a, fe b){ return (a&&b)? gexp[glog[a]+glog[b]] : 0; }
static inline fe inv(fe a){ return gexp[FO-glog[a]]; }

/* memory budget: every large work array is checked against it first; if it does not fit the search is cut off (return -1) */
static double mem_mb_opt = 0;
static double mem_limit_bytes(void)
{
    if (mem_mb_opt > 0) return mem_mb_opt * 1048576.0;
    double avail = 0; FILE *f = fopen("/proc/meminfo", "r");
    if (f) { char line[256]; while (fgets(line, sizeof line, f)) { long long kb; if (sscanf(line, "MemAvailable: %lld kB", &kb) == 1) { avail = (double)kb * 1024.0; break; } } fclose(f); }
    if (avail <= 0) { long pg = sysconf(_SC_AVPHYS_PAGES), ps = sysconf(_SC_PAGESIZE); if (pg > 0 && ps > 0) avail = (double)pg * (double)ps; }
    if (avail <= 0) avail = 2e9;
    return 0.7 * avail;
}
static int mem_check(const char *what, double need)
{
    double lim = mem_limit_bytes();
    if (need <= lim) return 1;
    fprintf(stderr, "warning: %s needs %.0f MB > memory budget %.0f MB: search cut off\n", what, need / 1048576.0, lim / 1048576.0);
    return 0;
}

typedef struct { int q, I, J, M; fe *T; } STab;            /* T[i*(J+1)+j] */
static inline int in_tab(const STab*S,int i,int j){ return S->q*i + (S->q+1)*j <= S->M; }
static inline fe *Tp(const STab*S,int i,int j){ return &S->T[(size_t)i*(S->J+1)+j]; }
static void stab_init(STab*S,int q,int M){ S->q=q; S->M=M; S->I=M/q; S->J=M/(q+1); S->T=calloc((size_t)(S->I+1)*(S->J+1),sizeof(fe)); }

/* ---------- 1. syndromes from r without any parity-check matrix ---------- */
static void syndrome_table(const STab *S, const fe *r, const fe *X, const fe *Y, int n)
{
    memset(S->T, 0, sizeof(fe)*(size_t)(S->I+1)*(S->J+1));
    fe *yp = malloc(sizeof(fe)*(S->J+1));
    for (int k=0;k<n;k++){
        if(!r[k]) continue;
        yp[0]=r[k]; for(int j=1;j<=S->J;j++) yp[j]=mul(yp[j-1],Y[k]);
        fe xp=1;
        for(int i=0;i<=S->I;i++){
            for(int j=0;j<=S->J && in_tab(S,i,j);j++) *Tp(S,i,j)^=mul(xp,yp[j]);
            xp=mul(xp,X[k]);
        }
    }
    free(yp);
}

/* ---------- 2. fill the dependent entries (j >= q) from the independent ones (j < q) ---------- */
static void syndrome_extend(STab *S)
{
    int q=S->q;
    for(int j=q;j<=S->J;j++) for(int i=0;i<=S->I && in_tab(S,i,j);i++)
        *Tp(S,i,j) = *Tp(S,i+q+1,j-q) ^ *Tp(S,i,j-q+1);          /* y^j = x^(q+1) y^(j-q) + y^(j-q+1) */
}

/* ---------- 3. syndromes -> error vector ---------- */
static int mk_basis(int q,int bound,int *bi,int *bj){ int n=0; for(int j=0;j<q;j++) for(int i=0;q*i+(q+1)*j<=bound;i++){bi[n]=i;bj[n]=j;n++;} return n; }

/* Gauss-Jordan; A is R x C (destroyed).  Returns kernel dimension, kernel basis in *out (dim x C). */
static int nullspace(fe *A,int R,int C,fe **out)
{
    int *pc=malloc(sizeof(int)*(C+1)), rk=0; int *lr=malloc(sizeof(int)*C);
    for(int c=0;c<C&&rk<R;c++){
        int p=rk; while(p<R && !A[(size_t)p*C+c]) p++;
        if(p==R) continue;
        if(p!=rk) for(int k=0;k<C;k++){ fe t=A[(size_t)p*C+k]; A[(size_t)p*C+k]=A[(size_t)rk*C+k]; A[(size_t)rk*C+k]=t; }
        fe *Rw=A+(size_t)rk*C; fe iv=inv(Rw[c]);
        for(int k=c;k<C;k++) Rw[k]=mul(Rw[k],iv);
        for(int k=c;k<C;k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0;r2<R;r2++){ if(r2==rk) continue; fe *D=A+(size_t)r2*C; fe f=D[c]; if(!f) continue; int lf=glog[f];
            for(int k=c;k<C;k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]]; }
        pc[rk++]=c;
    }
    char *isp=calloc(C,1); for(int i=0;i<rk;i++) isp[pc[i]]=1;
    int kd=C-rk; fe *B=calloc((size_t)(kd?kd:1)*C,sizeof(fe)); int bi=0;
    for(int f=0;f<C;f++){ if(isp[f]) continue; fe *x=B+(size_t)bi*C; x[f]=1; for(int i=0;i<rk;i++) x[pc[i]]=A[(size_t)i*C+f]; bi++; }
    free(pc);free(lr);free(isp); *out=B; return kd;
}


/* error values on a candidate set Z: solve  sum_z e_z x_z^i y_z^j = S(i,j)  for all independent (i,j).
 * returns the number of non-zero values (positions in pos[], values in val[]), or -1 if inconsistent. */
static int values_from_syndrome(const STab*S,const fe*X,const fe*Y,const int*Z,int nz,int*pos,fe*val)
{
    int q=S->q, M=S->M;
    if(nz==0) return 0;
    int *ri=malloc(sizeof(int)*(M+2)),*rj=malloc(sizeof(int)*(M+2)); int nr=mk_basis(q,M,ri,rj);
    int W=nz+1;
    if(!mem_check("value system",(double)nr*W*sizeof(fe))){ free(ri); free(rj); return -1; }
    fe *B=malloc(sizeof(fe)*(size_t)nr*W);
    fe *xp=malloc(sizeof(fe)*(S->I+2)), *yp=malloc(sizeof(fe)*q);
    for(int c=0;c<nz;c++){ int k=Z[c];
        xp[0]=1; for(int i=1;i<=S->I;i++) xp[i]=mul(xp[i-1],X[k]);
        yp[0]=1; for(int j=1;j<q;j++) yp[j]=mul(yp[j-1],Y[k]);
        for(int r=0;r<nr;r++) B[(size_t)r*W+c]=mul(xp[ri[r]],yp[rj[r]]); }
    for(int r=0;r<nr;r++) B[(size_t)r*W+nz]=*Tp(S,ri[r],rj[r]);
    int *lr=malloc(sizeof(int)*W), ok=1;
    for(int c=0;c<nz&&ok;c++){
        int p=c; while(p<nr && !B[(size_t)p*W+c]) p++;
        if(p==nr){ ok=0; break; }
        if(p!=c) for(int k=0;k<W;k++){ fe t=B[(size_t)p*W+k]; B[(size_t)p*W+k]=B[(size_t)c*W+k]; B[(size_t)c*W+k]=t; }
        fe *Rw=B+(size_t)c*W; fe iv=inv(Rw[c]);
        for(int k=c;k<W;k++) Rw[k]=mul(Rw[k],iv);
        for(int k=c;k<W;k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0;r2<nr;r2++){ if(r2==c) continue; fe *D=B+(size_t)r2*W; fe f=D[c]; if(!f) continue; int lf=glog[f];
            for(int k=c;k<W;k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]]; }
    }
    int cnt=-1;
    if(ok){ for(int r=nz;r<nr;r++) if(B[(size_t)r*W+nz]) ok=0; }
    if(ok){ cnt=0; for(int c=0;c<nz;c++){ fe v=B[(size_t)c*W+nz]; if(v){ pos[cnt]=Z[c]; val[cnt]=v; cnt++; } } }
    free(B);free(lr);free(ri);free(rj);free(xp);free(yp);
    return cnt;
}

/* returns the number of errors found, or -1 if the syndrome is not that of <= tmax errors.
 * info[0]=tmax info[1]=dim L(F) info[2]=dim L(H) info[3]=kernel dim info[4]=common zeros */
static int error_from_syndrome(STab *S,const fe*X,const fe*Y,int n,int *pos,fe *val,int *info)
{
    int q=S->q, M=S->M, g=q*(q-1)/2;
    int tmax=(M-3*g+1)/2; if(tmax<0) return -1;
    int lo=tmax+g, hi=M-(tmax+2*g-1), F=(lo+hi)/2, H=M-F;
    syndrome_extend(S);
    int *ai=malloc(sizeof(int)*(F+2)),*aj=malloc(sizeof(int)*(F+2)),*bi=malloc(sizeof(int)*(H+2)),*bj=malloc(sizeof(int)*(H+2));
    int na=mk_basis(q,F,ai,aj), nb=mk_basis(q,H,bi,bj);
    if(!mem_check("locator matrix",(double)nb*na*sizeof(fe))){ free(ai);free(aj);free(bi);free(bj); return -1; }
    fe *A=malloc(sizeof(fe)*(size_t)nb*na);
    for(int b=0;b<nb;b++) for(int a=0;a<na;a++) A[(size_t)b*na+a]=*Tp(S,ai[a]+bi[b],aj[a]+bj[b]);      /* S(f_a h_b) */
    fe *ker; int kd=nullspace(A,nb,na,&ker); free(A);
    /* common zeros of the kernel functions among the n points */
    int *Z=malloc(sizeof(int)*n), nz=0, imax=F/q;
    fe *xp=malloc(sizeof(fe)*(S->I+2)), *yp=malloc(sizeof(fe)*q), *mv=malloc(sizeof(fe)*na);
    for(int k=0;k<n;k++){
        xp[0]=1; for(int i=1;i<=imax;i++) xp[i]=mul(xp[i-1],X[k]);
        yp[0]=1; for(int j=1;j<q;j++) yp[j]=mul(yp[j-1],Y[k]);
        for(int a=0;a<na;a++) mv[a]=mul(xp[ai[a]],yp[aj[a]]);
        int vanish=1;
        for(int v=0;v<kd&&vanish;v++){ fe acc=0; const fe *kv=ker+(size_t)v*na; for(int a=0;a<na;a++) if(kv[a]&&mv[a]) acc^=mul(kv[a],mv[a]); if(acc) vanish=0; }
        if(vanish) Z[nz++]=k;
    }
    info[0]=tmax; info[1]=na; info[2]=nb; info[3]=kd; info[4]=nz;
    free(ker); free(ai);free(aj);free(bi);free(bj);free(mv);
    if(nz==0){ free(Z);free(xp);free(yp); return 0; }
    int cnt=values_from_syndrome(S,X,Y,Z,nz,pos,val);
    free(Z);free(xp);free(yp);
    return cnt;
}


/* ======================================================================
 *  Feng-Rao (FR) decoder on the syndrome table
 *    - every S(f_a f_b) is a table lookup  T[i_a+i_b][j_a+j_b]     (no parity-check matrix, no point sums)
 *    - omega = x  (smallest non-constant function, pole order q)
 * ====================================================================== */
static int inH_herm(int q,int s){ return s>=0 && s >= (q+1)*(s%q); }

/* d_FR(M) = min { nu(s) : s > M, s in H },  nu(s) = #{(a,b) in H^2 : a+b = s} */
static int dfr_herm(int q,int M)
{
    int best=1<<30, span=400;
    for(int s=M+1;s<=M+span;s++){ if(!inH_herm(q,s)) continue; int c=0; for(int a=0;a<=s;a++) if(inH_herm(q,a)&&inH_herm(q,s-a)) c++; if(c<best) best=c; }
    return best;
}

static int mat_inverse(fe *A,fe *out,int n)         /* Gauss-Jordan, A is destroyed */
{
    for(int i=0;i<n;i++){ for(int j=0;j<n;j++) out[(size_t)i*n+j]=0; out[(size_t)i*n+i]=1; }
    for(int c=0;c<n;c++){
        int p=-1; for(int r=c;r<n;r++) if(A[(size_t)r*n+c]){p=r;break;}
        if(p<0) return 0;
        if(p!=c) for(int k=0;k<n;k++){ fe t;
            t=A[(size_t)p*n+k];A[(size_t)p*n+k]=A[(size_t)c*n+k];A[(size_t)c*n+k]=t;
            t=out[(size_t)p*n+k];out[(size_t)p*n+k]=out[(size_t)c*n+k];out[(size_t)c*n+k]=t; }
        fe iv=inv(A[(size_t)c*n+c]);
        for(int k=0;k<n;k++){ A[(size_t)c*n+k]=mul(A[(size_t)c*n+k],iv); out[(size_t)c*n+k]=mul(out[(size_t)c*n+k],iv); }
        for(int r=0;r<n;r++){ fe f=A[(size_t)r*n+c]; if(r==c||!f) continue;
            for(int k=0;k<n;k++){ A[(size_t)r*n+k]^=mul(f,A[(size_t)c*n+k]); out[(size_t)r*n+k]^=mul(f,out[(size_t)c*n+k]); } }
    }
    return 1;
}

/* characteristic polynomial of the n x n matrix H (Hessenberg reduction + recurrence); g[0..n]; H is destroyed */
static void charpoly(fe *H,int n,fe *g)
{
#define Hm(a,b) H[(size_t)(a)*n+(b)]
    for(int k=0;k+2<n;k++){
        int p=-1; for(int i=k+1;i<n;i++) if(Hm(i,k)){p=i;break;}
        if(p<0) continue;
        if(p!=k+1){ for(int j=0;j<n;j++){ fe t=Hm(p,j);Hm(p,j)=Hm(k+1,j);Hm(k+1,j)=t; }
                    for(int i=0;i<n;i++){ fe t=Hm(i,p);Hm(i,p)=Hm(i,k+1);Hm(i,k+1)=t; } }
        fe iv=inv(Hm(k+1,k));
        for(int i=k+2;i<n;i++){ if(!Hm(i,k)) continue; fe f=mul(Hm(i,k),iv);
            for(int j=0;j<n;j++) Hm(i,j)^=mul(f,Hm(k+1,j));
            for(int r=0;r<n;r++) Hm(r,k+1)^=mul(f,Hm(r,i)); }
    }
    fe *pol=calloc((size_t)(n+1)*(n+1),sizeof(fe)); size_t W=n+1;
    pol[0]=1;
    for(int k=1;k<=n;k++){
        fe prod=1;
        for(int d=0;d<k;d++){ pol[k*W+d+1]^=pol[(k-1)*W+d]; pol[k*W+d]^=mul(Hm(k-1,k-1),pol[(k-1)*W+d]); }
        for(int i=1;i<=k-1;i++){
            prod=mul(prod,Hm(k-i,k-i-1)); if(!prod) break;
            fe c=mul(Hm(k-i-1,k-1),prod); if(!c) continue;
            for(int d=0;d<=k-i-1;d++) pol[k*W+d]^=mul(c,pol[(size_t)(k-i-1)*W+d]);
        }
    }
    for(int d=0;d<=n;d++) g[d]=pol[(size_t)n*W+d];
    free(pol);
#undef Hm
}

/* info[0]=tbasic info[1]=pivots(=estimated t) info[2]=#locators info[3]=distinct x-roots info[4]=common zeros info[5]=d_FR */
static int error_from_syndrome_fr(STab *S,const fe*X,const fe*Y,int n,int *pos,fe *val,int *info)
{
    int q=S->q, M=S->M, g=q*(q-1)/2;
    int tb=(M-3*g+1)/2; if(tb<0) return -1;
    int Ldeg=tb+g, dfr=dfr_herm(q,M);
    syndrome_extend(S);
    /* basis f_s (monomials) sorted by pole order s in H, s <= M */
    int nb=0; int *bi=malloc(sizeof(int)*(M+2)),*bj=malloc(sizeof(int)*(M+2)),*rho=malloc(sizeof(int)*(M+2)),*cle=malloc(sizeof(int)*(M+2));
    for(int s=0;s<=M;s++){ if(inH_herm(q,s)){ int j=s%q; bj[nb]=j; bi[nb]=(s-(q+1)*j)/q; rho[nb]=s; nb++; } cle[s]=nb; }   /* cle[s] = #basis with rho <= s */
    int nrows=cle[M-q], nl=cle[Ldeg<=M?Ldeg:M];
    { double need=0; for(int i=0;i<nrows;i++) need+=(double)(cle[M-rho[i]]+i+1)*sizeof(fe);
      if(!mem_check("FR reduction tables",need)){ free(bi);free(bj);free(rho);free(cle); return -1; } }
    fe **red=malloc(sizeof(fe*)*nrows), **cm=malloc(sizeof(fe*)*nrows);
    int *pivcol=malloc(sizeof(int)*nrows), *rowofcol=malloc(sizeof(int)*nb); fe *pivinv=malloc(sizeof(fe)*nrows);
    for(int j=0;j<nb;j++) rowofcol[j]=-1;
    for(int i=0;i<nrows;i++){
        int ncol=cle[M-rho[i]];
        red[i]=malloc(sizeof(fe)*ncol); cm[i]=calloc(i+1,sizeof(fe)); cm[i][i]=1; pivcol[i]=-1;
        for(int j=0;j<ncol;j++) red[i][j]=*Tp(S,bi[i]+bi[j],bj[i]+bj[j]);                 /* S(f_i f_j) */
        for(int j=0;j<ncol;j++){
            fe v=red[i][j]; if(!v) continue;
            int p=rowofcol[j];
            if(p>=0){ fe f=mul(v,pivinv[p]);
                for(int jj=j;jj<ncol;jj++) red[i][jj]^=mul(f,red[p][jj]);
                for(int k=0;k<=p;k++) cm[i][k]^=mul(f,cm[p][k]);
            } else { pivcol[i]=j; rowofcol[j]=i; pivinv[i]=inv(v); break; }
        }
    }
    int T_=0, nloc=0; int *Rr=malloc(sizeof(int)*nrows),*Cc=malloc(sizeof(int)*nrows);
    for(int i=0;i<nrows;i++) if(pivcol[i]>=0){ Rr[T_]=i; Cc[T_]=pivcol[i]; T_++; }
    for(int i=0;i<nl;i++) if(pivcol[i]<0) nloc++;
    info[0]=tb; info[1]=T_; info[2]=nloc; info[3]=info[4]=0; info[5]=dfr;
    int ret=-1;
    if(T_==0){ ret=0; goto done; }
    for(int a=0;a<T_;a++) for(int b=0;b<T_;b++) if(rho[Rr[a]]+rho[Cc[b]]+q>M) goto done;     /* syndromes too short */
    {
        fe *S0=malloc(sizeof(fe)*(size_t)T_*T_),*SX=malloc(sizeof(fe)*(size_t)T_*T_),*S0i=malloc(sizeof(fe)*(size_t)T_*T_),*Q=calloc((size_t)T_*T_,sizeof(fe));
        for(int a=0;a<T_;a++) for(int b=0;b<T_;b++){
            S0[(size_t)a*T_+b]=*Tp(S,bi[Rr[a]]+bi[Cc[b]],  bj[Rr[a]]+bj[Cc[b]]);                 /* S(f_a f_b)     */
            SX[(size_t)a*T_+b]=*Tp(S,bi[Rr[a]]+bi[Cc[b]]+1,bj[Rr[a]]+bj[Cc[b]]);                 /* S(f_a f_b x)   */
        }
        int inv_ok=mat_inverse(S0,S0i,T_);
        if(inv_ok){
            for(int a=0;a<T_;a++) for(int b=0;b<T_;b++){ fe acc=0; for(int k=0;k<T_;k++) acc^=mul(S0i[(size_t)a*T_+k],SX[(size_t)k*T_+b]); Q[(size_t)a*T_+b]=acc; }
            fe *gp=malloc(sizeof(fe)*(T_+1)); charpoly(Q,T_,gp);
            /* roots theta = x-coordinates of the errors; candidate points have x = theta */
            char *isroot=calloc(FS,1); int nroots=0;
            for(int th=0;th<FS;th++){ fe acc=gp[T_]; for(int d=T_-1;d>=0;d--) acc=(fe)(mul(acc,th)^gp[d]); if(!acc){ isroot[th]=1; nroots++; } }
            info[3]=nroots;
            int *Z=malloc(sizeof(int)*n), nz=0; fe *xp=malloc(sizeof(fe)*(S->I+2)),*yp=malloc(sizeof(fe)*q),*mv=malloc(sizeof(fe)*(nl+1));
            for(int k=0;k<n;k++){
                if(!isroot[X[k]]) continue;
                xp[0]=1; for(int i=1;i<=S->I;i++) xp[i]=mul(xp[i-1],X[k]);
                yp[0]=1; for(int j=1;j<q;j++) yp[j]=mul(yp[j-1],Y[k]);
                for(int a=0;a<nl;a++) mv[a]=mul(xp[bi[a]],yp[bj[a]]);
                int vanish=1;
                for(int i=0;i<nl&&vanish;i++){ if(pivcol[i]>=0) continue; fe acc=0; for(int a=0;a<=i;a++) if(cm[i][a]&&mv[a]) acc^=mul(cm[i][a],mv[a]); if(acc) vanish=0; }
                if(vanish) Z[nz++]=k;
            }
            info[4]=nz;
            ret=values_from_syndrome(S,X,Y,Z,nz,pos,val);
            free(gp);free(isroot);free(Z);free(xp);free(yp);free(mv);
        }
        free(S0);free(SX);free(S0i);free(Q);
    }
done:
    for(int i=0;i<nrows;i++){ free(red[i]); free(cm[i]); }
    free(red);free(cm);free(pivcol);free(rowofcol);free(pivinv);free(Rr);free(Cc);free(bi);free(bj);free(rho);free(cle);
    return ret;
}

/* ---------- test harness ---------- */
static uint64_t rs=88172645463325252ULL; static uint64_t rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}

int main(int argc,char**argv){
    int m=argc>1?atoi(argv[1]):4, q=1<<(m/2), g=q*(q-1)/2;
    int M=argc>2?atoi(argv[2]):23, nuse=argc>3?atoi(argv[3]):1<<30, targ=argc>4?atoi(argv[4]):-1;
    unsigned poly[]={0,3,7,0xB,0x13,0x25,0x43,0x89,0x11D,0x211,0x409};
    gf_init(m,poly[m]);
    if(argc>6) mem_mb_opt=atof(argv[6]);
    if(argc>5) rs ^= (uint64_t)atoi(argv[5])*0x9E3779B97F4A7C15ULL;
    int cap=q*q*q, n=0; fe *X=malloc(sizeof(fe)*cap),*Y=malloc(sizeof(fe)*cap);
    for(int x=0;x<FS;x++){ fe xq=1; for(int k=0;k<q+1;k++) xq=mul(xq,x);
        for(int y=0;y<FS;y++){ fe yq=1; for(int k=0;k<q;k++) yq=mul(yq,y); if((yq^y)==xq){X[n]=x;Y[n]=y;n++;} } }
    if(nuse<n) n=nuse;
    int tmax=(M-3*g+1)/2;
    printf("GF(2^%d), q=%d, g=%d, n=%d, M=%d  ->  tmax=%d\n",m,q,g,n,M,tmax);
    STab S; stab_init(&S,q,M);
    STab D; stab_init(&D,q,M);
    int ts[4]={0,1,tmax>1?tmax/2:1,tmax}, nt=4;
    if(targ>=0){ ts[0]=targ; nt=1; }
    fe *e=calloc(n,sizeof(fe)); int *pos=malloc(sizeof(int)*(n+1)); fe *val=malloc(sizeof(fe)*(n+1));
    for(int ti=0;ti<nt;ti++){
        int t=ts[ti]; memset(e,0,sizeof(fe)*n);
        for(int u=0;u<t;u++){ int p; do p=rnd()%n; while(e[p]); do e[p]=rnd()%FS; while(!e[p]); }
        double t0=now(); syndrome_table(&S,e,X,Y,n); double t_syn=now()-t0;
        /* hand the decoder ONLY the independent syndromes (j<q) */
        memset(D.T,0,sizeof(fe)*(size_t)(D.I+1)*(D.J+1));
        for(int i=0;i<=S.I;i++) for(int j=0;j<q&&in_tab(&S,i,j);j++) *Tp(&D,i,j)=*Tp(&S,i,j);
        int info[6]={0}; t0=now(); int cnt=error_from_syndrome(&D,X,Y,n,pos,val,info); double t_dec=now()-t0;
        int extok=!memcmp(S.T,D.T,sizeof(fe)*(size_t)(S.I+1)*(S.J+1));
        int good=(cnt==t);
        for(int c=0;c<cnt&&good;c++) if(e[pos[c]]!=val[c]) good=0;
        printf("t=%3d : syndrome %.4f s | KERNEL %.3f s found %d %s (dimL(F)=%d ker=%d zeros=%d) | extend==direct:%s\n",
               t,t_syn,t_dec,cnt,good?"OK":"FAIL",info[1],info[3],info[4],extok?"yes":"NO");
        int infof[6]={0}; t0=now(); int cf=error_from_syndrome_fr(&D,X,Y,n,pos,val,infof); double t_fr=now()-t0;
        int goodf=(cf==t); for(int c=0;c<cf&&goodf;c++) if(e[pos[c]]!=val[c]) goodf=0;
        printf("        FR     %.3f s found %d %s (pivots=%d locators=%d x-roots=%d zeros=%d, d_FR=%d -> t_FR=%d)\n",
               t_fr,cf,goodf?"OK":"FAIL",infof[1],infof[2],infof[3],infof[4],infof[5],(infof[5]-1)/2);
    }
    return 0;
}