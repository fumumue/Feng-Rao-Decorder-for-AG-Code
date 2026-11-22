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
 * Run  : ./bbgs_toric [--m 9] [--q 8] [--errors 256] [--len 8192] [--a A --b B] [--seed s] [--mem MB] [--dump]
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
  for(int i=FO;i<2*FO+4;i++) gexp[i]=gexp[i-FO];
  glog[0]=0;
  return 0;
}
static inline fe mul(fe a, fe b){ return (a&&b)? gexp[glog[a]+glog[b]] : 0; }
static inline fe inv(fe a){ return gexp[FO-glog[a]]; }
/* x^i y^j for a point given by logs (lx,ly) -- i,j may be negative */
static inline fe monval(int lx,int ly,int i,int j){ long long e=((long long)i*lx+(long long)j*ly)%FO; if(e<0) e+=FO; return gexp[e]; }

static double mem_mb_opt=0;
static int dump_all=0;
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

typedef struct { int a0,a1,a2,n,nind; int *pi,*pj; char *ind; int imin,imax,jmin,jmax; } Poly;
/* is h = (hi,hj) in H(a,b):  h + Newton(F) inside Delta(a,b) */
static int inH(int a0,int a1,int a2,int hi,int hj){
    return Q*hi+hj <= a1-Q*QQ &&
           Q*hj-(Q+1)*hi <= a2-Q &&
           hi+QQ*hj >= -a0-QQ;
}
static void poly_build(Poly *P,int a0,int a1,int a2){
    P->a0=a0; P->a1=a1; P->a2=a2;
    int cnt=0;
    int i0=cdiv_(-(Q*a0+QQ*a2), QQ*(Q+1)+Q);
    int i1=fdiv_(QQ*a1+a0, Q*QQ-1);
    P->imin=1<<30; P->imax=-(1<<30); P->jmin=1<<30; P->jmax=-(1<<30);
    for(int pass=0;pass<2;pass++){
        int k=0;
        for(int i=i0;i<=i1;i++){
            int lo,hi;
            if(!jrange(a1,a2,-a0,i,&lo,&hi)) continue;
            for(int j=lo;j<=hi;j++){
                if(pass==1){
                    P->pi[k]=i; P->pj[k]=j;
                    P->ind[k]=!inH(a0,a1,a2,i-QQ,j);
                }
                k++;
            }
            if(pass==0){
                if(i<P->imin)P->imin=i;
                if(i>P->imax)P->imax=i;
                if(lo<P->jmin)P->jmin=lo;
                if(hi>P->jmax)P->jmax=hi;
            }
        }
        if(pass==0){
            cnt=k; P->n=cnt;
            P->pi=malloc(sizeof(int)*(size_t)cnt);
            P->pj=malloc(sizeof(int)*(size_t)cnt);
            P->ind=malloc((size_t)cnt);
            if(!P->pi||!P->pj||!P->ind){ fprintf(stderr,"out of memory building polygon\n"); exit(1); }
        }
    }
    P->nind=0;
    for(int k=0;k<P->n;k++) P->nind+=P->ind[k];
}

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
    if(nz==0) return 0;
    Poly*G=S->G;
    int nr=G->nind, W=nz+1;
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

/* ---------------- human-readable diagnostic output ---------------- */
static void print_poly_basis(const char *name,const Poly *P){
    printf("\n%s: %d independent monomials\n",name,P->nind);
    for(int k=0;k<P->n;k++) if(P->ind[k])
        printf("  x^(%d) y^(%d)\n",P->pi[k],P->pj[k]);
}
static void print_syndromes(const Tab *S){
    printf("\nSYNDROME (all lattice entries; * = independent basis entry)\n");
    for(int p=0;p<S->G->n;p++)
        printf("  (%d,%d)%s : 0x%03x\n",S->G->pi[p],S->G->pj[p],S->G->ind[p]?" *":"  ",(unsigned)*Tp(S,S->G->pi[p],S->G->pj[p]));
}
static void print_error_vector(const char *name,const int *pos,const fe *val,int n){
    printf("\n%s: weight=%d\n",name,n);
    for(int i=0;i<n;i++) printf("  point-index=%d  (x,y)=(0x%03x,0x%03x)  e=0x%03x\n",
        pos[i],(unsigned)PX[pos[i]],(unsigned)PY[pos[i]],(unsigned)val[i]);
}
static void print_locator_basis(const fe *ker,int kd,int na,const int *ai,const int *aj){
    printf("\nERROR-LOCATION POLYNOMIAL BASIS: %d common-zero equations\n",kd);
    for(int v=0;v<kd;v++){
        printf("  L%d(x,y) =",v);
        int first=1;
        for(int a=0;a<na;a++) if(ker[(size_t)v*na+a]){
            printf("%s0x%03x*x^(%d)*y^(%d)",first?" ":" + ",
                (unsigned)ker[(size_t)v*na+a],ai[a],aj[a]); first=0;
        }
        if(first) printf(" 0");
        printf("\n");
    }
    printf("  Error positions are the common zeros of all listed L_v on the enumerated curve points.\n");
}

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
    if(dump_all) print_locator_basis(ker,kd,na,ai,aj);
    free(ker);free(mv);free(ai);free(aj);free(bi);free(bj);
    int cnt=values_from_syndrome(S,Z,nz,pos,val); free(Z); return cnt; }

static int divisor_degree(int a0,int a1,int a2){
    return a0+Q*a1+(Q-1)*a2;
}
static int choose_h(int g0,int g1,int g2,int target,int min_f,
                    int *h0,int *h1,int *h2){
    int best=1<<30, found=0;
    for(int x=0;x<=g0;x++){
        for(int y=0;y<=g1;y++){
            int rem=target-x-Q*y;
            int z=rem<=0?0:(rem+Q-2)/(Q-1);
            if(z<0)z=0;
            if(z>g2)continue;
            int dh=divisor_degree(x,y,z);
            int df=divisor_degree(g0-x,g1-y,g2-z);
            if(dh>=target && df>=min_f && dh<best){
                best=dh; *h0=x; *h1=y; *h2=z; found=1;
            }
        }
    }
    return found;
}
static void usage(const char *p){
    printf("Usage: %s [--m 5] [--q 2] [--errors 3] [--len 0] [--places ORIGIN,INF_E1,INF_E2]\n"
           "          [--g0 n --g1 n --g2 n] [--seed n] [--dump]\n"
           "  ORIGIN : affine place (0,0), degree 1\n"
           "  INF_E1 : degree-q place at infinity\n"
           "  INF_E2 : symmetric sum of all q-1 rational branches of the second infinity edge\n"
           "  --g0/--g1/--g2 are divisor multiplicities; zero omits that support.\n"
           "  For q=2, INF_E2 consists of one branch.\n",p);
}
int main(int argc,char**argv){
    int m=5,q=2,t=3,len=0;
    int g0=-1,g1=-1,g2=-1, seed=1;
    int use0=1,use1=1,use2=1;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--help")||!strcmp(argv[i],"-h")){usage(argv[0]);return 0;}
        else if(!strcmp(argv[i],"--m")&&i+1<argc)m=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--q")&&i+1<argc)q=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--errors")&&i+1<argc)t=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--len")&&i+1<argc)len=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--seed")&&i+1<argc)seed=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--g0")&&i+1<argc)g0=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--g1")&&i+1<argc)g1=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--g2")&&i+1<argc)g2=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--places")&&i+1<argc){
            use0=use1=use2=0;
            char *v=argv[++i], *save=NULL;
            for(char *tok=strtok_r(v,",",&save);tok;tok=strtok_r(NULL,",",&save)){
                if(!strcmp(tok,"ORIGIN"))use0=1;
                else if(!strcmp(tok,"INF_E1"))use1=1;
                else if(!strcmp(tok,"INF_E2")||!strcmp(tok,"INF_E2_ALL"))use2=1;
                else if(!strcmp(tok,"INF_E2_1")&&q==2)use2=1;
                else {fprintf(stderr,"unsupported place selector: %s (individual INF_E2 branches are only identified here for q=2)\n",tok);return 1;}
            }
        } else if(!strcmp(argv[i],"--dump"))dump_all=1;
        else {fprintf(stderr,"unknown option %s\n",argv[i]);return 1;}
    }
    static const unsigned dp[12]={0,3,7,0xB,0x13,0x25,0x43,0x89,0x11D,0x211,0x409,0x805};
    if(m<2||m>11||gf_init(m,dp[m])){fprintf(stderr,"bad m\n");return 1;}
    if(q<2||q>32||(q&(q-1))!=0||t<0){
        fprintf(stderr,"q must be a power of two in [2,32], and errors must be nonnegative\n");
        return 1;
    }
    Q=q; QQ=q*q;
    rs^=(uint64_t)(unsigned)seed*0x9E3779B97F4A7C15ULL;
    for(int i=0;i<8;i++)rnd();

    int selected=(use0?1:0)+(use1?1:0)+(use2?1:0);
    if(selected<1||selected>3){
        fprintf(stderr,"select between one and three support components\n");
        return 1;
    }
    if(q>2&&use2){
        fprintf(stderr,"NOTE: INF_E2 is currently the symmetric sum of all %d rational branches;\n",q-1);
        fprintf(stderr,"      individual INF_E2 branch selection is implemented only for q=2.\n");
    }
    int genus=(q*q*q*q-3*q+2)/2;
    int dmin=2*t+3*genus-1;
    int weight0=use0?1:0, weight1=use1?q:0, weight2=use2?q-1:0;
    int total_weight=weight0+weight1+weight2;
    if(total_weight==0){fprintf(stderr,"at least one support place is required\n");return 1;}
    int c=(dmin+total_weight-1)/total_weight;
    int A0=g0>=0?g0:(use0?c:0);
    int A1=g1>=0?g1:(use1?c:0);
    int A2=g2>=0?g2:(use2?c:0);
    if((!use0&&A0)||(!use1&&A1)||(!use2&&A2)||A0<0||A1<0||A2<0){
        fprintf(stderr,"multiplicity conflicts with --places or is negative\n");return 1;
    }
    if((use0&&A0==0)||(use1&&A1==0)||(use2&&A2==0)){
        fprintf(stderr,"selected support places need positive multiplicities\n");return 1;
    }
    int degG=divisor_degree(A0,A1,A2);
    if(degG<dmin){fprintf(stderr,"deg(G)=%d is below designed requirement %d; increase --g0/--g1/--g2\n",degG,dmin);return 1;}

    int H0=0,H1=0,H2=0;
    int targetH=t+2*genus-1, minF=t+genus;
    if(!choose_h(A0,A1,A2,targetH,minF,&H0,&H1,&H2)){
        fprintf(stderr,"cannot split G into H and F with deg(H)>=%d and deg(F)>=%d\n",targetH,minF);
        return 1;
    }
    int F0=A0-H0,F1=A1-H1,F2=A2-H2;
    int degH=divisor_degree(H0,H1,H2),degF=divisor_degree(F0,F1,F2);

    double t0=now();
    Poly G,F,H;
    poly_build(&G,A0,A1,A2);
    poly_build(&F,F0,F1,F2);
    poly_build(&H,H0,H1,H2);
    printf("BBGS q=%d over GF(2^%d): genus=%d, errors t=%d\n",q,m,genus,t);
    printf("G = %d*ORIGIN + %d*INF_E1 + %d*INF_E2_ALL, degree=%d (required >= %d)\n",
           A0,A1,A2,degG,dmin);
    printf("F coefficients=(%d,%d,%d), degree=%d; H coefficients=(%d,%d,%d), degree=%d\n",
           F0,F1,F2,degF,H0,H1,H2,degH);
    printf("Newton polygon candidate bases (%.3f s): dim L(G)=%d [RR %d], dim V_F=%d [RR lower bound %d], dim L(H)=%d [RR %d]\n",
           now()-t0,G.nind,degG-genus+1,F.nind,degF-genus+1,H.nind,degH-genus+1);
    if(G.nind!=degG-genus+1||H.nind!=degH-genus+1||degH<2*genus-1){
        fprintf(stderr,"RR basis check failed for G or H; refusing to decode\n");return 1;
    }
    if(F.nind<=t){fprintf(stderr,"dim V_F=%d is not > t=%d\n",F.nind,t);return 1;}

    t0=now(); enumerate_points(len);
    /* The origin is a support point of G, not an evaluation position. */
    int keep=0;
    for(int k=0;k<npts;k++){
        if(PX[k]==0&&PY[k]==0)continue;
        PX[keep]=PX[k];PY[keep]=PY[k];keep++;
    }
    npts=keep;
    free(LX);free(LY);
    LX=malloc(sizeof(int)*(size_t)npts);LY=malloc(sizeof(int)*(size_t)npts);
    for(int k=0;k<npts;k++){LX[k]=glog[PX[k]];LY[k]=glog[PY[k]];}
    printf("smooth affine evaluation points (origin excluded): n=%d (%.3f s)\n",npts,now()-t0);
    if(npts<=G.nind){fprintf(stderr,"evaluation length n=%d must exceed dim L(G)=%d\n",npts,G.nind);return 1;}

    Tab S,D;S.G=D.G=&G;S.W=D.W=G.jmax-G.jmin+1;
    size_t tsz=(size_t)(G.imax-G.imin+1)*S.W;
    S.T=calloc(tsz,sizeof(fe));D.T=calloc(tsz,sizeof(fe));
    int *tpos=malloc(sizeof(int)*(size_t)t);fe*tval=malloc(sizeof(fe)*(size_t)t);
    if(!S.T||!D.T||!tpos||!tval){fprintf(stderr,"out of memory\n");return 1;}
    if(t>npts){fprintf(stderr,"error count exceeds evaluation length\n");return 1;}
    for(int u=0;u<t;u++){
        int p,dup;
        do{p=(int)(rnd()%(uint64_t)npts);dup=0;for(int k=0;k<u;k++)if(tpos[k]==p)dup=1;}while(dup);
        tpos[u]=p;do{tval[u]=(fe)(rnd()%FS);}while(!tval[u]);
    }
    if(dump_all)print_error_vector("INPUT ERROR VECTOR",tpos,tval,t);
    t0=now();syndrome_table(&S,tpos,tval,t);double ts=now()-t0;
    if(dump_all){print_poly_basis("BASIS OF L(G)",&G);print_syndromes(&S);}
    for(int p=0;p<G.n;p++)if(G.ind[p])*Tp(&D,G.pi[p],G.pj[p])=*Tp(&S,G.pi[p],G.pj[p]);
    int *pos=malloc(sizeof(int)*(size_t)(npts+1));fe*val=malloc(sizeof(fe)*(size_t)(npts+1));
    int info[4]={0};t0=now();
    int cnt=error_from_syndrome(&D,&F,&H,pos,val,info);double td=now()-t0;
    int extok=!memcmp(S.T,D.T,sizeof(fe)*tsz);
    int good=(cnt==t);
    for(int c0=0;c0<cnt&&good;c0++){
        int found=0;for(int u=0;u<t;u++)if(tpos[u]==pos[c0]&&tval[u]==val[c0])found=1;
        if(!found)good=0;
    }
    printf("syndrome generation: %.4f s, %d independent syndrome entries\n",ts,G.nind);
    printf("dependent syndrome reconstruction agrees with direct values: %s\n",extok?"yes":"NO");
    printf("decode: %.4f s, found %d errors (dimF=%d dimH=%d kernel=%d common zeros=%d) -> %s\n",
           td,cnt,info[0],info[1],info[2],info[3],good?"OK":"FAIL");
    if(dump_all&&cnt>=0)print_error_vector("DECODED ERROR VECTOR",pos,val,cnt);
    return good?0:2;
}
