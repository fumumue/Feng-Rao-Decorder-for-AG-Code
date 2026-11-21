/*
 * bbgs_toric.c -- BBGS curve  X^(q^2) + Y + X^(q^2-1) Y^q + X^(q^2-q) Y^(q^2) = 0  over GF(2^m):
 *   function-space basis from the Newton polygon (NO local expansions, NO linear algebra, NO solve_L)
 *   + syndromes from error positions/values without any parity-check matrix
 *   + syndromes -> error vector (basic Feng-Rao / Pellikaan kernel algorithm)
 *
 * Idea.  The Newton polygon of F is the triangle (0,1),(q^2,0),(q^2-q,q^2).  Its three edges give the places
 *   E0 : the origin (x=y=0),             v(x^i y^j) = i + q^2 j
 *   E1 : places at infinity (degree q),  v(x^i y^j) = -q i - j
 *   E2 : q-1 rational places at infinity, v(x^i y^j) = (q+1) i - q j
 * For the divisor G = a*(places of E1) + b*(places of E2) every Laurent monomial x^i y^j with
 *   q i + j <= a ,  q j - (q+1) i <= b ,  i + q^2 j >= 0                       (lattice polygon  Delta(a,b))
 * lies in L(G).  Modulo the multiples of F the monomials of Delta(a,b) are independent; a basis is
 *   { (i,j) in Delta(a,b) :  (i,j) - (q^2,0)  is NOT in  H(a,b) },   H = { h : h + Newton(F) inside Delta }.
 * Its size equals deg G - g + 1 (Riemann-Roch) -- checked at run time -- so it is a complete basis of L(G).
 *
 * Build: cc -O2 -std=gnu11 -o bbgs_toric bbgs_toric.c
 * Run  : ./bbgs_toric [--m 9] [--q 8] [--errors 256] [--len 8192] [--a A --b B] [--seed s] [--mem MB]
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
typedef uint16_t fe;

/* ---------------- GF(2^m), m <= 11 ---------------- */
static int FM, FS, FO; static fe *gexp, *glog;
static int gf_init(int m, unsigned poly){ FM=m; FS=1<<m; FO=FS-1; gexp=malloc(sizeof(fe)*(2*FO+4)); glog=malloc(sizeof(fe)*FS);
  unsigned x=1; for(int i=0;i<FO;i++){ if(i>0&&x==1) return -1; gexp[i]=x; glog[x]=i; x<<=1; if(x&FS) x^=poly; } if(x!=1) return -1;
  for(int i=FO;i<2*FO+4;i++) gexp[i]=gexp[i-FO]; glog[0]=0; return 0; }
static inline fe mul(fe a, fe b){ return (a&&b)? gexp[glog[a]+glog[b]] : 0; }
static inline fe inv(fe a){ return gexp[FO-glog[a]]; }
/* x^i y^j for a point given by logs (lx,ly) -- i,j may be negative */
static inline fe monval(int lx,int ly,int i,int j){ long long e=((long long)i*lx+(long long)j*ly)%FO; if(e<0) e+=FO; return gexp[e]; }

static double mem_mb_opt=0;
static double mem_limit_bytes(void){ if(mem_mb_opt>0) return mem_mb_opt*1048576.0; double avail=0; FILE*f=fopen("/proc/meminfo","r");
  if(f){ char l[256]; while(fgets(l,sizeof l,f)){ long long kb; if(sscanf(l,"MemAvailable: %lld kB",&kb)==1){avail=kb*1024.0;break;} } fclose(f); }
  if(avail<=0){ long pg=sysconf(_SC_AVPHYS_PAGES),ps=sysconf(_SC_PAGESIZE); if(pg>0&&ps>0) avail=(double)pg*ps; } if(avail<=0) avail=2e9; return 0.7*avail; }
static int mem_check(const char*what,double need){ double lim=mem_limit_bytes(); if(need<=lim) return 1;
  fprintf(stderr,"warning: %s needs %.0f MB > memory budget %.0f MB: search cut off\n",what,need/1048576.0,lim/1048576.0); return 0; }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static uint64_t rs=88172645463325252ULL; static uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

/* ---------------- Newton polygon basis ---------------- */
static int Q, QQ;                                   /* q, q^2 */
static int fdiv_(int a,int b){ int d=a/b; if((a%b!=0)&&((a<0)!=(b<0))) d--; return d; }
static int cdiv_(int a,int b){ return -fdiv_(-a,b); }
/* j-range of column i of the polygon  { q i + j <= A1,  q j - (q+1) i <= A2,  i + q^2 j >= A0 } */
static int jrange(int A1,int A2,int A0,int i,int *lo,int *hi){
    *lo=cdiv_(A0-i,QQ); int h1=A1-Q*i, h2=fdiv_(A2+(Q+1)*i,Q); *hi=h1<h2?h1:h2; return *hi>=*lo; }

typedef struct { int a,b,n,nind; int *pi,*pj; char *ind; int imin,imax,jmin,jmax; } Poly;
/* is h = (hi,hj) in H(a,b):  h + Newton(F) inside Delta(a,b) */
static int inH(int a,int b,int hi,int hj){ return Q*hi+hj <= a-Q*QQ && Q*hj-(Q+1)*hi <= b-Q && hi+QQ*hj >= -QQ; }
static void poly_build(Poly *P,int a,int b){
    P->a=a; P->b=b; int cnt=0, i0=-(b+Q+5), i1=a/Q+3;
    P->imin=1<<30; P->imax=-(1<<30); P->jmin=1<<30; P->jmax=-(1<<30);
    for(int pass=0;pass<2;pass++){
        int k=0;
        for(int i=i0;i<=i1;i++){ int lo,hi; if(!jrange(a,b,0,i,&lo,&hi)) continue;
            for(int j=lo;j<=hi;j++){
                if(pass==1){ P->pi[k]=i; P->pj[k]=j; P->ind[k]=!inH(a,b,i-QQ,j); }
                k++; }
            if(pass==0){ if(i<P->imin)P->imin=i; if(i>P->imax)P->imax=i; if(lo<P->jmin)P->jmin=lo; if(hi>P->jmax)P->jmax=hi; } }
        if(pass==0){ cnt=k; P->n=cnt; P->pi=malloc(sizeof(int)*cnt); P->pj=malloc(sizeof(int)*cnt); P->ind=malloc(cnt); }
    }
    P->nind=0; for(int k=0;k<P->n;k++) P->nind+=P->ind[k];
}
static void poly_free(Poly*P){ free(P->pi);free(P->pj);free(P->ind); }

/* ---------------- points of the curve (origin excluded: x,y != 0) ---------------- */
static int npts; static fe *PX,*PY; static int *LX,*LY;
static void enumerate_points(int len){
    int cap=1<<16; npts=0; PX=malloc(sizeof(fe)*cap); PY=malloc(sizeof(fe)*cap);
    for(int x=1;x<FS;x++){ int lx=glog[x];
        for(int y=1;y<FS;y++){ int ly=glog[y];
            fe s=gexp[(QQ*lx)%FO]; s^=y; s^=gexp[(((long long)(QQ-1)*lx+(long long)Q*ly)%FO)]; s^=gexp[(((long long)(QQ-Q)*lx+(long long)QQ*ly)%FO)];
            if(!s){ if(npts==cap){cap*=2;PX=realloc(PX,sizeof(fe)*cap);PY=realloc(PY,sizeof(fe)*cap);} PX[npts]=x; PY[npts]=y; npts++; if(len>0&&npts>=len) goto done; } } }
done:
    LX=malloc(sizeof(int)*npts); LY=malloc(sizeof(int)*npts);
    for(int k=0;k<npts;k++){ LX[k]=glog[PX[k]]; LY[k]=glog[PY[k]]; }
}

/* ---------------- syndrome table on Delta(G) (dense box, indexed by (i,j)) ---------------- */
typedef struct { Poly *G; int W; fe *T; } Tab;
static inline fe *Tp(const Tab*S,int i,int j){ return &S->T[(size_t)(i-S->G->imin)*S->W+(j-S->G->jmin)]; }
/* all lattice points of Delta(G):  T(i,j) = sum_k e_k x_k^i y_k^j       (no parity-check matrix) */
static void syndrome_table(const Tab*S,const int*pos,const fe*val,int t){
    memset(S->T,0,sizeof(fe)*(size_t)(S->G->imax-S->G->imin+1)*S->W);
    for(int u=0;u<t;u++){ int k=pos[u]; fe e=val[u]; int le=glog[e];
        for(int p=0;p<S->G->n;p++){ long long ex=((long long)S->G->pi[p]*LX[k]+(long long)S->G->pj[p]*LY[k]+le)%FO; if(ex<0)ex+=FO; *Tp(S,S->G->pi[p],S->G->pj[p])^=gexp[ex]; } }
}
/* the dependent entries from the independent ones:  F * x^h = 0   (all coefficients 1)  */
static void syndrome_extend(const Tab*S){
    const int vi[3]={0,QQ-1,QQ-Q}, vj[3]={1,Q,QQ};
    for(int p=0;p<S->G->n;p++) if(!S->G->ind[p]){
        int hi=S->G->pi[p]-QQ, hj=S->G->pj[p]; fe acc=0;
        for(int v=0;v<3;v++) acc^=*Tp(S,hi+vi[v],hj+vj[v]);
        *Tp(S,S->G->pi[p],S->G->pj[p])=acc; }
}

/* ---------------- linear algebra ---------------- */
static int nullspace(fe *A,int R,int C,fe **out){
    int *pc=malloc(sizeof(int)*(C+1)),rk=0,*lr=malloc(sizeof(int)*C);
    for(int c=0;c<C&&rk<R;c++){ int p=rk; while(p<R&&!A[(size_t)p*C+c])p++; if(p==R)continue;
        if(p!=rk) for(int k=0;k<C;k++){ fe t=A[(size_t)p*C+k]; A[(size_t)p*C+k]=A[(size_t)rk*C+k]; A[(size_t)rk*C+k]=t; }
        fe*Rw=A+(size_t)rk*C; fe iv=inv(Rw[c]); for(int k=c;k<C;k++) Rw[k]=mul(Rw[k],iv); for(int k=c;k<C;k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0;r2<R;r2++){ if(r2==rk)continue; fe*D=A+(size_t)r2*C; fe f=D[c]; if(!f)continue; int lf=glog[f]; for(int k=c;k<C;k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]]; }
        pc[rk++]=c; }
    char*isp=calloc(C,1); for(int i=0;i<rk;i++) isp[pc[i]]=1; int kd=C-rk; fe*B=calloc((size_t)(kd?kd:1)*C,sizeof(fe)); int bi=0;
    for(int f=0;f<C;f++){ if(isp[f])continue; fe*x=B+(size_t)bi*C; x[f]=1; for(int i=0;i<rk;i++) x[pc[i]]=A[(size_t)i*C+f]; bi++; }
    free(pc);free(lr);free(isp); *out=B; return kd; }

/* error values on the candidate set Z: sum_z e_z x_z^i y_z^j = T(i,j) for all independent (i,j) of Delta(G) */
static int values_from_syndrome(const Tab*S,const int*Z,int nz,int*pos,fe*val){
    if(nz==0) return 0; Poly*G=S->G; int nr=G->nind, W=nz+1;
    if(!mem_check("value system",(double)nr*W*sizeof(fe))) return -1;
    fe*B=malloc(sizeof(fe)*(size_t)nr*W); int r=0;
    for(int p=0;p<G->n;p++) if(G->ind[p]){ for(int c=0;c<nz;c++) B[(size_t)r*W+c]=monval(LX[Z[c]],LY[Z[c]],G->pi[p],G->pj[p]); B[(size_t)r*W+nz]=*Tp(S,G->pi[p],G->pj[p]); r++; }
    int*lr=malloc(sizeof(int)*W),ok=1;
    for(int c=0;c<nz&&ok;c++){ int p=c; while(p<nr&&!B[(size_t)p*W+c])p++; if(p==nr){ok=0;break;}
        if(p!=c) for(int k=0;k<W;k++){ fe t=B[(size_t)p*W+k]; B[(size_t)p*W+k]=B[(size_t)c*W+k]; B[(size_t)c*W+k]=t; }
        fe*Rw=B+(size_t)c*W; fe iv=inv(Rw[c]); for(int k=c;k<W;k++) Rw[k]=mul(Rw[k],iv); for(int k=c;k<W;k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0;r2<nr;r2++){ if(r2==c)continue; fe*D=B+(size_t)r2*W; fe f=D[c]; if(!f)continue; int lf=glog[f]; for(int k=c;k<W;k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]]; } }
    int cnt=-1; if(ok){ for(int r2=nz;r2<nr;r2++) if(B[(size_t)r2*W+nz]) ok=0; }
    if(ok){ cnt=0; for(int c=0;c<nz;c++){ fe v=B[(size_t)c*W+nz]; if(v){ pos[cnt]=Z[c]; val[cnt]=v; cnt++; } } }
    free(B);free(lr); return cnt; }

/* syndromes -> errors.  F,H polygons with G = F+H.  info: 0=dimL(F) 1=dimL(H) 2=kernel dim 3=common zeros */
static int error_from_syndrome(const Tab*S,Poly*F,Poly*H,int*pos,fe*val,int*info){
    int na=F->nind, nb=H->nind;
    if(!mem_check("locator matrix",(double)na*nb*sizeof(fe))) return -1;
    syndrome_extend(S);
    int *ai=malloc(sizeof(int)*na),*aj=malloc(sizeof(int)*na),*bi=malloc(sizeof(int)*nb),*bj=malloc(sizeof(int)*nb); int x=0,y=0;
    for(int p=0;p<F->n;p++) if(F->ind[p]){ ai[x]=F->pi[p]; aj[x]=F->pj[p]; x++; }
    for(int p=0;p<H->n;p++) if(H->ind[p]){ bi[y]=H->pi[p]; bj[y]=H->pj[p]; y++; }
    fe*A=malloc(sizeof(fe)*(size_t)nb*na);
    for(int b=0;b<nb;b++) for(int a=0;a<na;a++) A[(size_t)b*na+a]=*Tp(S,ai[a]+bi[b],aj[a]+bj[b]);                /* S(f_a h_b) */
    fe*ker; int kd=nullspace(A,nb,na,&ker); free(A);
    int*Z=malloc(sizeof(int)*npts),nz=0; fe*mv=malloc(sizeof(fe)*na);
    for(int k=0;k<npts;k++){
        for(int a=0;a<na;a++) mv[a]=monval(LX[k],LY[k],ai[a],aj[a]);
        int vanish=1;
        for(int v=0;v<kd&&vanish;v++){ fe acc=0; const fe*kv=ker+(size_t)v*na; for(int a=0;a<na;a++) if(kv[a]&&mv[a]) acc^=mul(kv[a],mv[a]); if(acc) vanish=0; }
        if(vanish) Z[nz++]=k; }
    info[0]=na; info[1]=nb; info[2]=kd; info[3]=nz;
    free(ker);free(mv);free(ai);free(aj);free(bi);free(bj);
    int cnt=values_from_syndrome(S,Z,nz,pos,val); free(Z); return cnt; }

int main(int argc,char**argv){
    int m=9,q=8,t=256,len=8192,a_req=-1,b_req=-1; unsigned seed=1;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--m")&&i+1<argc) m=atoi(argv[++i]); else if(!strcmp(argv[i],"--q")&&i+1<argc) q=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--errors")&&i+1<argc) t=atoi(argv[++i]); else if(!strcmp(argv[i],"--len")&&i+1<argc) len=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--a")&&i+1<argc) a_req=atoi(argv[++i]); else if(!strcmp(argv[i],"--b")&&i+1<argc) b_req=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--seed")&&i+1<argc) seed=(unsigned)atoi(argv[++i]); else if(!strcmp(argv[i],"--mem")&&i+1<argc) mem_mb_opt=atof(argv[++i]);
        else { fprintf(stderr,"unknown option %s\n",argv[i]); return 1; } }
    static const unsigned dp[12]={0,3,7,0xB,0x13,0x25,0x43,0x89,0x11D,0x211,0x409,0x805};
    if(m<2||m>11||gf_init(m,dp[m])){ fprintf(stderr,"bad m\n"); return 1; }
    Q=q; QQ=q*q; rs^=(uint64_t)seed*0x9E3779B97F4A7C15ULL; for(int i=0;i<8;i++) rnd();
    int g=(q*q*q*q-3*q+2)/2, dmin=2*t+3*g-1;
    int a=a_req>0?a_req:(dmin+2*q-2)/(2*q-1), b=b_req>0?b_req:a;
    int aH=(t+2*g-1+2*q-2)/(2*q-1), bH=aH, aF=a-aH, bF=b-bH;          /* H as small as the basic algorithm allows, F = G - H */
    double t0=now();
    Poly G,F,H; poly_build(&G,a,b); poly_build(&F,aF,bF); poly_build(&H,aH,bH);
    int degG=q*a+(q-1)*b, degF=q*aF+(q-1)*bF, degH=q*aH+(q-1)*bH;
    printf("BBGS q=%d over GF(2^%d): g=%d, errors t=%d\n",q,m,g,t);
    printf("divisor G=(a=%d on E1, b=%d on E2): deg G=%d (need >= 2t+3g-1=%d), F: deg %d, H: deg %d\n",a,b,degG,dmin,degF,degH);
    printf("basis from the Newton polygon (%.3f s): dim L(G)=%d [RR %d], dim V_F=%d [RR %d, >= is fine], dim L(H)=%d [RR %d]  lattice points of Delta(G): %d\n",
           now()-t0,G.nind,degG-g+1,F.nind,degF-g+1,H.nind,degH-g+1,G.n);
    /* G and H must be COMPLETE (dim = deg - g + 1, certified by Riemann-Roch since deg >= 2g-1);
       F only needs dim > t: its kernel functions vanish on the error positions whatever F is */
    if(G.nind!=degG-g+1||H.nind!=degH-g+1||degH<2*g-1) printf("WARNING: L(G) or L(H) is not certified complete by Riemann-Roch\n");
    if(F.nind<=t||degH<t+2*g-1||degG<dmin){ fprintf(stderr,"degrees too small for the basic algorithm (dim V_F=%d, need > t)\n",F.nind); return 1; }
    t0=now(); enumerate_points(len);
    printf("curve points used as code positions (origin excluded): n=%d  (%.2f s)\n",npts,now()-t0);
    if(G.nind>=npts){ fprintf(stderr,"n must exceed dim L(G)\n"); return 1; }
    Tab S,D; S.G=D.G=&G; S.W=D.W=G.jmax-G.jmin+1;
    size_t tsz=(size_t)(G.imax-G.imin+1)*S.W; S.T=malloc(sizeof(fe)*tsz); D.T=malloc(sizeof(fe)*tsz);
    int*tpos=malloc(sizeof(int)*t); fe*tval=malloc(sizeof(fe)*t);
    for(int u=0;u<t;u++){ int p,dup; do{ p=rnd()%npts; dup=0; for(int k=0;k<u;k++) if(tpos[k]==p) dup=1; }while(dup); tpos[u]=p; do tval[u]=rnd()%FS; while(!tval[u]); }
    t0=now(); syndrome_table(&S,tpos,tval,t); double ts=now()-t0;
    /* give the decoder only the independent syndromes (dim L(G) of them) */
    memset(D.T,0,sizeof(fe)*tsz); for(int p=0;p<G.n;p++) if(G.ind[p]) *Tp(&D,G.pi[p],G.pj[p])=*Tp(&S,G.pi[p],G.pj[p]);
    int*pos=malloc(sizeof(int)*(npts+1)); fe*val=malloc(sizeof(fe)*(npts+1)); int info[4]={0};
    t0=now(); int cnt=error_from_syndrome(&D,&F,&H,pos,val,info); double td=now()-t0;
    int extok=!memcmp(S.T,D.T,sizeof(fe)*tsz);
    int good=(cnt==t); for(int c=0;c<cnt&&good;c++){ int f=0; for(int u=0;u<t;u++) if(tpos[u]==pos[c]&&tval[u]==val[c]) f=1; if(!f) good=0; }
    printf("syndrome from errors (no parity-check matrix): %.4f s, %d independent syndromes\n",ts,G.nind);
    printf("dependent entries rebuilt from the independent ones == direct: %s\n",extok?"yes":"NO");
    printf("decode: %.3f s, found %d errors (dimL(F)=%d dimL(H)=%d kernel=%d common zeros=%d)  ->  %s\n",td,cnt,info[0],info[1],info[2],info[3],good?"OK":"FAIL");
    return good?0:2;
}