/*
 * bbgs_toric.c -- GF(2^m) 上の BBGS 曲線
 *   X^(q^2) + Y + X^(q^2-1)Y^q + X^(q^2-q)Y^(q^2) = 0
 *
 * 機能:
 *   ・Newton 多角形から関数空間の基底を構成する（局所展開・連立一次方程式・solve_L は使わない）
 *   ・パリティ検査行列を作らず、誤り位置と誤り値からシンドロームを計算する
 *   ・基本 Feng-Rao / Pellikaan の核アルゴリズムでシンドロームから誤りベクトルを復元する
 *
 * F の Newton 多角形は (0,1), (q^2,0), (q^2-q,q^2) を頂点とする三角形である。
 * その3辺に対応する場所は次のとおり。
 *   E0: 原点 (x=y=0)                 v(x^i y^j) = i + q^2 j
 *   E1: 無限遠の場所（次数 q）       v(x^i y^j) = -q i - j
 *   E2: 無限遠の q-1 個の有理点      v(x^i y^j) = (q+1)i - qj
 *
 * G = a*(E1 の場所) + b*(E2 の場所) とする。
 *   qi+j <= a, qj-(q+1)i <= b, i+q^2j >= 0
 * を満たす Laurent 単項式 x^i y^j が Delta(a,b) に属する。
 * F の倍数を法として、Delta(a,b) の単項式から独立な基底を選ぶ。
 * 基底の個数は deg(G)-g+1 と一致する（Riemann-Roch による完全性を実行時に確認）。
 *
 * ビルド: cc -O2 -std=gnu11 -o bbgs_toric bbgs_toric.c
 * 実行  : ./bbgs_toric [--m 9] [--q 8] [--errors 256] [--len 8192] [--a A --b B] [--seed s] [--mem MB] [--force] [--quiet]
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
typedef uint16_t fe;

/* ---------------- GF(2^m) の演算（m <= 11） ---------------- */
static int FM, FS, FO;
static fe *gexp, *glog;
static int gf_init(int m, unsigned poly) {
    FM=m;
    FS=1<<m;
    FO=FS-1;
    gexp=malloc(sizeof(fe)*(2*FO+4));
    glog=malloc(sizeof(fe)*FS);
    unsigned x=1;
    for(int i=0; i<FO; i++) {
        if(i>0&&x==1) return -1;
        gexp[i]=x;
        glog[x]=i;
        x<<=1;
        if(x&FS) x^=poly;
    }
    if(x!=1) return -1;
    for(int i=FO; i<2*FO+4; i++) gexp[i]=gexp[i-FO];
    glog[0]=0;
    return 0;
}
static inline fe mul(fe a, fe b) {
    return (a&&b)? gexp[glog[a]+glog[b]] : 0;
}
static inline fe inv(fe a) {
    return gexp[FO-glog[a]];
}
/* 対数 (lx,ly) で表した点における x^i y^j の値。i,j は負でもよい */
static inline fe monval(int lx, int ly, int i, int j) {
    long long e=((long long)i*lx+(long long)j*ly)%FO;
    if(e<0) e+=FO;
    return gexp[e];
}
static double mem_mb_opt=0;
static int dump_all=1; /* 既定では診断用のベクトル・シンドローム・基底を表示する */
static double mem_limit_bytes(void) {
    if(mem_mb_opt>0) return mem_mb_opt*1048576.0;
    double avail=0;
    FILE*f=fopen("/proc/meminfo", "r");
    if(f) {
        char l[256];
        while(fgets(l, sizeof l, f)) {
            long long kb;
            if(sscanf(l, "MemAvailable: %lld kB", &kb)==1) {
                avail=kb*1024.0;
                break;
            }
        }
        fclose(f);
    }
    if(avail<=0) {
        long pg=sysconf(_SC_AVPHYS_PAGES), ps=sysconf(_SC_PAGESIZE);
        if(pg>0&&ps>0) avail=(double)pg*ps;
    }
    if(avail<=0) avail=2e9;
    return 0.7*avail;
}
static int mem_check(const char*what, double need) {
    double lim=mem_limit_bytes();
    if(need<=lim) return 1;
    fprintf(stderr, "warning: %s needs %.0f MB > memory budget %.0f MB: search cut off\n", what, need/1048576.0, lim/1048576.0);
    return 0;
}
static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec+1e-9*t.tv_nsec;
}
static uint64_t rs=88172645463325252ULL;
static uint64_t rnd(void) {
    rs^=rs<<13;
    rs^=rs>>7;
    rs^=rs<<17;
    return rs;
}

/* ---------------- Newton 多角形による基底構成 ---------------- */
static int Q, QQ;
/* q と q^2 */
static int fdiv_(int a, int b) {
    int d=a/b;
    if((a%b!=0)&&((a<0)!=(b<0))) d--;
    return d;
}
static int cdiv_(int a, int b) {
    return -fdiv_(-a, b);
}
/* 多角形 {qi+j<=A1, qj-(q+1)i<=A2, i+q^2j>=A0} における列 i の j の範囲 */
static int jrange(int A1, int A2, int A0, int i, int *lo, int *hi) {
    *lo=cdiv_(A0-i, QQ);
    int h1=A1-Q*i, h2=fdiv_(A2+(Q+1)*i, Q);
    *hi=h1<h2?h1:h2;
    return *hi>=*lo;
}
typedef struct {
    int a, b, n, nind;
    int *pi, *pj;
    char *ind;
    int imin, imax, jmin, jmax;
}
Poly;
/* h=(hi,hj) が H(a,b) に属するか。すなわち h+Newton(F) が Delta(a,b) に含まれるか */
static int inH(int a, int b, int hi, int hj) {
    return Q*hi+hj <= a-Q*QQ && Q*hj-(Q+1)*hi <= b-Q && hi+QQ*hj >= -QQ;
}
static void poly_build(Poly *P, int a, int b) {
    P->a=a;
    P->b=b;
    int cnt=0, i0=-(b+Q+5), i1=a/Q+3;
    P->imin=1<<30;
    P->imax=-(1<<30);
    P->jmin=1<<30;
    P->jmax=-(1<<30);
    for(int pass=0; pass<2; pass++) {
        int k=0;
        for(int i=i0; i<=i1; i++) {
            int lo, hi;
            if(!jrange(a, b, 0, i, &lo, &hi)) continue;
            for(int j=lo; j<=hi; j++) {
                if(pass==1) {
                    P->pi[k]=i;
                    P->pj[k]=j;
                    P->ind[k]=!inH(a, b, i-QQ, j);
                }
                k++;
            }
            if(pass==0) {
                if(i<P->imin)P->imin=i;
                if(i>P->imax)P->imax=i;
                if(lo<P->jmin)P->jmin=lo;
                if(hi>P->jmax)P->jmax=hi;
            }
        }
        if(pass==0) {
            cnt=k;
            P->n=cnt;
            P->pi=malloc(sizeof(int)*cnt);
            P->pj=malloc(sizeof(int)*cnt);
            P->ind=malloc(cnt);
        }
    }
    P->nind=0;
    for(int k=0; k<P->n; k++) P->nind+=P->ind[k];
}

/* ---------------- 曲線上の点（原点を除外し、x,y はともに非零） ---------------- */
static int npts;
static fe *PX, *PY;
static int *LX, *LY;
static void enumerate_points(int len) {
    int cap=1<<16;
    npts=0;
    PX=malloc(sizeof(fe)*cap);
    PY=malloc(sizeof(fe)*cap);
    for(int x=1; x<FS; x++) {
        int lx=glog[x];
        for(int y=1; y<FS; y++) {
            int ly=glog[y];
            fe s=gexp[(QQ*lx)%FO];
            s^=y;
            s^=gexp[(((long long)(QQ-1)*lx+(long long)Q*ly)%FO)];
            s^=gexp[(((long long)(QQ-Q)*lx+(long long)QQ*ly)%FO)];
            if(!s) {
                if(npts==cap) {
                    cap*=2;
                    PX=realloc(PX, sizeof(fe)*cap);
                    PY=realloc(PY, sizeof(fe)*cap);
                }
                PX[npts]=x;
                PY[npts]=y;
                npts++;
                if(len>0&&npts>=len) goto done;
            }
        }
    }
done:
    LX=malloc(sizeof(int)*npts);
    LY=malloc(sizeof(int)*npts);
    for(int k=0; k<npts; k++) {
        LX[k]=glog[PX[k]];
        LY[k]=glog[PY[k]];
    }
}

/* ---------------- Delta(G) 上のシンドローム表（(i,j) で添字付けした密な配列） ---------------- */
typedef struct {
    Poly *G;
    int W;
    fe *T;
}
Tab;
static inline fe *Tp(const Tab*S, int i, int j) {
    return &S->T[(size_t)(i-S->G->imin)*S->W+(j-S->G->jmin)];
}
/* Delta(G) の全格子点について T(i,j)=Σ_k e_k x_k^i y_k^j を計算する（検査行列は使わない） */
static void syndrome_table(const Tab*S, const int*pos, const fe*val, int t) {
    memset(S->T, 0, sizeof(fe)*(size_t)(S->G->imax-S->G->imin+1)*S->W);
    for(int u=0; u<t; u++) {
        int k=pos[u];
        fe e=val[u];
        int le=glog[e];
        for(int p=0; p<S->G->n; p++) {
            long long ex=((long long)S->G->pi[p]*LX[k]+(long long)S->G->pj[p]*LY[k]+le)%FO;
            if(ex<0)ex+=FO;
            *Tp(S, S->G->pi[p], S->G->pj[p])^=gexp[ex];
        }
    }
}
/* 独立成分から従属成分を復元する。F*x^h=0（この曲線式の係数はすべて1） */
static void syndrome_extend(const Tab*S) {
    const int vi[3] = {0, QQ - 1, QQ - Q};
    const int vj[3] = {1, Q, QQ};
    for(int p=0; p<S->G->n; p++) if(!S->G->ind[p]) {
        int hi=S->G->pi[p]-QQ, hj=S->G->pj[p];
        fe acc=0;
        for(int v=0; v<3; v++) acc^=*Tp(S, hi+vi[v], hj+vj[v]);
        *Tp(S, S->G->pi[p], S->G->pj[p])=acc;
    }
}

/* ---------------- 線形代数 ---------------- */
static int nullspace(fe *A, int R, int C, fe **out) {
    int *pc=malloc(sizeof(int)*(C+1)), rk=0, *lr=malloc(sizeof(int)*C);
    for(int c=0; c<C&&rk<R; c++) {
        int p=rk;
        while(p<R&&!A[(size_t)p*C+c])p++;
        if(p==R)continue;
        if(p!=rk) for(int k=0; k<C; k++) {
            fe t=A[(size_t)p*C+k];
            A[(size_t)p*C+k]=A[(size_t)rk*C+k];
            A[(size_t)rk*C+k]=t;
        }
        fe*Rw=A+(size_t)rk*C;
        fe iv=inv(Rw[c]);
        for(int k=c; k<C; k++) Rw[k]=mul(Rw[k], iv);
        for(int k=c; k<C; k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0; r2<R; r2++) {
            if(r2==rk)continue;
            fe*D=A+(size_t)r2*C;
            fe f=D[c];
            if(!f)continue;
            int lf=glog[f];
            for(int k=c; k<C; k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]];
        }
        pc[rk++]=c;
    }
    char*isp=calloc(C, 1);
    for(int i=0; i<rk; i++) isp[pc[i]]=1;
    int kd=C-rk;
    fe*B=calloc((size_t)(kd?kd:1)*C, sizeof(fe));
    int bi=0;
    for(int f=0; f<C; f++) {
        if(isp[f])continue;
        fe*x=B+(size_t)bi*C;
        x[f]=1;
        for(int i=0; i<rk; i++) x[pc[i]]=A[(size_t)i*C+f];
        bi++;
    }
    free(pc);
    free(lr);
    free(isp);
    *out=B;
    return kd;
}
/* 候補点集合 Z 上の誤り値を求める。Delta(G) の独立な全 (i,j) で Σ_z e_z x_z^i y_z^j=T(i,j) を解く */
static int values_from_syndrome(const Tab*S, const int*Z, int nz, int*pos, fe*val) {
    if(nz==0) return 0;
    Poly*G=S->G;
    int nr=G->nind, W=nz+1;
    if(!mem_check("value system", (double)nr*W*sizeof(fe))) return -1;
    fe*B=malloc(sizeof(fe)*(size_t)nr*W);
    int r=0;
    for(int p=0; p<G->n; p++) if(G->ind[p]) {
        for(int c=0; c<nz; c++) B[(size_t)r*W+c]=monval(LX[Z[c]], LY[Z[c]], G->pi[p], G->pj[p]);
        B[(size_t)r*W+nz]=*Tp(S, G->pi[p], G->pj[p]);
        r++;
    }
    int*lr=malloc(sizeof(int)*W), ok=1;
    for(int c=0; c<nz&&ok; c++) {
        int p=c;
        while(p<nr&&!B[(size_t)p*W+c])p++;
        if(p==nr) {
            ok=0;
            break;
        }
        if(p!=c) for(int k=0; k<W; k++) {
            fe t=B[(size_t)p*W+k];
            B[(size_t)p*W+k]=B[(size_t)c*W+k];
            B[(size_t)c*W+k]=t;
        }
        fe*Rw=B+(size_t)c*W;
        fe iv=inv(Rw[c]);
        for(int k=c; k<W; k++) Rw[k]=mul(Rw[k], iv);
        for(int k=c; k<W; k++) lr[k]=Rw[k]?glog[Rw[k]]:-1;
        for(int r2=0; r2<nr; r2++) {
            if(r2==c)continue;
            fe*D=B+(size_t)r2*W;
            fe f=D[c];
            if(!f)continue;
            int lf=glog[f];
            for(int k=c; k<W; k++) if(lr[k]>=0) D[k]^=gexp[lf+lr[k]];
        }
    }
    int cnt=-1;
    if(ok) {
        for(int r2=nz; r2<nr; r2++) if(B[(size_t)r2*W+nz]) ok=0;
    }
    if(ok) {
        cnt=0;
        for(int c=0; c<nz; c++) {
            fe v=B[(size_t)c*W+nz];
            if(v) {
                pos[cnt]=Z[c];
                val[cnt]=v;
                cnt++;
            }
        }
    }
    free(B);
    free(lr);
    return cnt;
}

/* ---------------- 診断情報の表示 ---------------- */
static void print_poly_basis(const char *name, const Poly *P) {
    printf("\n%s: %d independent monomials\n", name, P->nind);
    for (int k = 0; k < P->n; k++) {
        if (P->ind[k]) printf("  x^(%d) y^(%d)\n", P->pi[k], P->pj[k]);
    }
}
static void print_syndromes(const Tab *S) {
    printf("\nSYNDROME (all lattice entries; * = independent basis entry)\n");
    for (int p = 0; p < S->G->n; p++) {
        printf("  (%d,%d)%s : 0x%03x\n", S->G->pi[p], S->G->pj[p], S->G->ind[p] ? " *" : "  ", (unsigned)*Tp(S, S->G->pi[p], S->G->pj[p]));
    }
}
typedef struct {
    int pos;
    fe val;
} ErrorEntry;

static int compare_error_entry(const void *a, const void *b) {
    const ErrorEntry *x = a;
    const ErrorEntry *y = b;
    return (x->pos > y->pos) - (x->pos < y->pos);
}

static int has_duplicate_positions(const int *pos, int n) {
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (pos[i] == pos[j]) return 1;
    return 0;
}

static void print_error_comparison(const int *before_pos, const fe *before_val, int before_n,
                                  const int *after_pos, const fe *after_val, int after_n) {
    int total = before_n + after_n;
    ErrorEntry *entry = malloc(sizeof(*entry) * (size_t)total);
    if (!entry && total > 0) {
        fprintf(stderr, "cannot allocate memory to sort error comparison\n");
        return;
    }

    for (int i = 0; i < before_n; i++) {
        entry[i].pos = before_pos[i];
        entry[i].val = before_val[i];
    }
    for (int i = 0; i < after_n; i++) {
        entry[before_n + i].pos = after_pos[i];
        entry[before_n + i].val = after_val[i];
    }
    qsort(entry, (size_t)total, sizeof(*entry), compare_error_entry);

    printf("\nERROR VECTOR COMPARISON (sorted by point-index)\n");
    printf("  %5s | %5s | %5s %5s | %10s | %10s | %s\n",
           "No.", "index", "x", "y", "before", "after", "result");
    printf("  ------+-------+-------------+------------+------------+---------\n");

    int row = 0;
    for (int i = 0; i < total; ) {
        int k = entry[i].pos;
        fe before = 0, after = 0;
        int has_before = 0, has_after = 0;

        while (i < total && entry[i].pos == k) i++;
        for (int j = 0; j < before_n; j++) {
            if (before_pos[j] == k) {
                before = before_val[j];
                has_before = 1;
                break;
            }
        }
        for (int j = 0; j < after_n; j++) {
            if (after_pos[j] == k) {
                after = after_val[j];
                has_after = 1;
                break;
            }
        }

        char before_text[16], after_text[16];
        if (has_before) snprintf(before_text, sizeof(before_text), "0x%03x", (unsigned)before);
        else snprintf(before_text, sizeof(before_text), "-");
        if (has_after) snprintf(after_text, sizeof(after_text), "0x%03x", (unsigned)after);
        else snprintf(after_text, sizeof(after_text), "-");

        const char *result = has_before && has_after && before == after ? "MATCH" :
                             has_before && has_after ? "DIFF" : "MISSING";
        row++;
        printf("  %5d | %5d | 0x%03x 0x%03x | %10s | %10s | %s\n",
               row, k, (unsigned)PX[k], (unsigned)PY[k],
               before_text, after_text, result);
    }
    printf("  rows=%d, before=%d errors, after=%d errors\n", row, before_n, after_n);
    printf("  duplicate positions: before=%s, after=%s\n",
           has_duplicate_positions(before_pos, before_n) ? "YES" : "no",
           has_duplicate_positions(after_pos, after_n) ? "YES" : "no");
    free(entry);
}
static void print_locator_basis(const fe *ker, int kd, int na, const int *ai, const int *aj) {
    printf("\nERROR-LOCATION POLYNOMIAL BASIS: %d common-zero equations\n", kd);
    for (int v = 0; v < kd; v++) {
        printf("  L%d(x,y) =", v);
        int first = 1;
        for (int a = 0; a < na; a++) {
            fe c = ker[(size_t)v * na + a];
            if (c) {
                printf("%s0x%03x*x^(%d)*y^(%d)", first ? " " : " + ", (unsigned)c, ai[a], aj[a]);
                first = 0;
            }
        }
        if (first) printf(" 0");
        printf("\n");
    }
    printf("  Error positions are the common zeros of all listed L_v on the enumerated curve points.\n");
}
/* シンドロームから誤りを復元する。G=F+H。info: 0=dimL(F), 1=dimL(H), 2=核の次元, 3=共通零点数 */
static int error_from_syndrome(const Tab*S, Poly*F, Poly*H, int*pos, fe*val, int*info) {
    int na=F->nind, nb=H->nind;
    if(!mem_check("locator matrix", (double)na*nb*sizeof(fe))) return -1;
    syndrome_extend(S);
    int *ai=malloc(sizeof(int)*na), *aj=malloc(sizeof(int)*na), *bi=malloc(sizeof(int)*nb), *bj=malloc(sizeof(int)*nb);
    int x=0, y=0;
    for(int p=0; p<F->n; p++) if(F->ind[p]) {
        ai[x]=F->pi[p];
        aj[x]=F->pj[p];
        x++;
    }
    for(int p=0; p<H->n; p++) if(H->ind[p]) {
        bi[y]=H->pi[p];
        bj[y]=H->pj[p];
        y++;
    }
    fe*A=malloc(sizeof(fe)*(size_t)nb*na);
    for(int b=0; b<nb; b++) for(int a=0; a<na; a++) A[(size_t)b*na+a]=*Tp(S, ai[a]+bi[b], aj[a]+bj[b]);
    /* S(f_a h_b) */
    fe*ker;
    int kd=nullspace(A, nb, na, &ker);
    free(A);
    int*Z=malloc(sizeof(int)*npts), nz=0;
    fe*mv=malloc(sizeof(fe)*na);
    for(int k=0; k<npts; k++) {
        for(int a=0; a<na; a++) mv[a]=monval(LX[k], LY[k], ai[a], aj[a]);
        int vanish=1;
        for(int v=0; v<kd&&vanish; v++) {
            fe acc=0;
            const fe*kv=ker+(size_t)v*na;
            for(int a=0; a<na; a++) if(kv[a]&&mv[a]) acc^=mul(kv[a], mv[a]);
            if(acc) vanish=0;
        }
        if(vanish) Z[nz++]=k;
    }
    info[0]=na;
    info[1]=nb;
    info[2]=kd;
    info[3]=nz;
    if (dump_all) print_locator_basis(ker, kd, na, ai, aj);
    if(kd==0) {
        fprintf(stderr, "位置多項式の核が零次元です。全 %d 点が共通零点となり、誤り位置を絞り込めません。\n", nz);
        free(ker);
        free(mv);
        free(ai);
        free(aj);
        free(bi);
        free(bj);
        free(Z);
        return -1;
    }
    free(ker);
    free(mv);
    free(ai);
    free(aj);
    free(bi);
    free(bj);
    int cnt=values_from_syndrome(S, Z, nz, pos, val);
    free(Z);
    return cnt;
}
int main(int argc, char**argv) {
    int m=9, q=8, t=256, len=8192, a_req=-1, b_req=-1;
    int force=0;
    unsigned seed=1;
    for(int i=1; i<argc; i++) {
        if(!strcmp(argv[i], "--m")&&i+1<argc) m=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--q")&&i+1<argc) q=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--errors")&&i+1<argc) t=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--len")&&i+1<argc) len=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--a")&&i+1<argc) a_req=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--b")&&i+1<argc) b_req=atoi(argv[++i]);
        else if(!strcmp(argv[i], "--seed")&&i+1<argc) seed=(unsigned)atoi(argv[++i]);
        else if(!strcmp(argv[i], "--mem")&&i+1<argc) mem_mb_opt=atof(argv[++i]);
        else if(!strcmp(argv[i], "--force")) force=1;
        else if(!strcmp(argv[i], "--dump")) dump_all=1;
        else if(!strcmp(argv[i], "--quiet")) dump_all=0;
        else {
            fprintf(stderr, "unknown option %s\n", argv[i]);
            return 1;
        }
    }
    static const unsigned dp[12]= {
        0, 3, 7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D, 0x211, 0x409, 0x805
    }
    ;
    if(m<2||m>11||gf_init(m, dp[m])) {
        fprintf(stderr, "bad m\n");
        return 1;
    }
    Q=q;
    QQ=q*q;
    rs^=(uint64_t)seed*0x9E3779B97F4A7C15ULL;
    for(int i=0; i<8; i++) rnd();
    int g=(q*q*q*q-3*q+2)/2;
    int basic_deg_sufficient=2*t+3*g-1;
    int a=a_req>0?a_req:(basic_deg_sufficient+2*q-2)/(2*q-1), b=b_req>0?b_req:a;
    int aH=(t+2*g-1+2*q-2)/(2*q-1), bH=aH, aF=a-aH, bF=b-bH;
    /* 基本アルゴリズムの条件を満たす範囲で H を小さくし、F=G-H とする */
    double t0=now();
    Poly G, F, H;
    poly_build(&G, a, b);
    poly_build(&F, aF, bF);
    poly_build(&H, aH, bH);
    int degG=q*a+(q-1)*b, degF=q*aF+(q-1)*bF, degH=q*aH+(q-1)*bH;
    printf("BBGS 曲線: q=%d, GF(2^%d), genus g=%d, 誤り数 t=%d\n", q, m, g, t);
    printf("除数 G=(E1 上の a=%d, E2 上の b=%d): deg G=%d（基本法の十分条件 2t+3g-1=%d）, deg F=%d, deg H=%d\n", a, b, degG, basic_deg_sufficient, degF, degH);
    int d_design=degG-2*g+2;
    int t_design=(d_design>0)?(d_design-1)/2:0;
    int t_divisor=(degG-3*g+1)/2;
    printf("双対 AG 符号の設計最小距離の下界: d >= deg G - 2g + 2 = %d; 保証される一意復号半径 >= %d\n", d_design, t_design);
    printf("G を固定した場合に基本法の十分条件が保証する誤り数: t <= floor((deg G - 3g + 1)/2) = %d\n", t_divisor);
    printf("Newton 多角形の基底構成 (%.3f s): dim L(G)=%d [RR=%d], dim V_F=%d [RR=%d], dim L(H)=%d [RR=%d], Delta(G) の格子点数=%d\n", now()-t0, G.nind, degG-g+1, F.nind, degF-g+1, H.nind, degH-g+1, G.n);
    /* G と H は完全な空間でなければならない（deg>=2g-1 なら Riemann-Roch により dim=deg-g+1）。
       F は dim(F)>t であればよい。F の核に属する関数は誤り位置で消える。 */
    if(G.nind!=degG-g+1||H.nind!=degH-g+1||degH<2*g-1)
        printf("WARNING: L(G) または L(H) の完全性を Riemann-Roch で確認できません\n");
    if(F.nind<=t || degH<t+2*g-1 || degG<basic_deg_sufficient) {
        fprintf(stderr, "基本アルゴリズムの十分条件を満たしていません: ");
        if(degG<basic_deg_sufficient)
            fprintf(stderr, "deg G=%d < 2t+3g-1=%d（固定した G の次数条件）; ", degG, basic_deg_sufficient);
        if(F.nind<=t)
            fprintf(stderr, "dim V_F=%d <= t=%d; ", F.nind, t);
        if(degH<t+2*g-1)
            fprintf(stderr, "deg H=%d < t+2g-1=%d; ", degH, t+2*g-1);
        fprintf(stderr, "\n");
        if(!force) {
            fprintf(stderr, "復号は実行しません。条件を無視して実験する場合だけ --force を指定してください。\n");
            return 1;
        }
        fprintf(stderr, "警告: --force により条件を無視して復号処理を試します。\n");
    }
    t0=now();
    enumerate_points(len);
    printf("符号位置として使用する曲線上の点（原点を除外）: n=%d (%.2f s)\n", npts, now()-t0);
    if(t<0 || t>npts) {
        fprintf(stderr, "誤り数 t=%d は使用可能な点数 n=%d の範囲外です\n", t, npts);
        return 1;
    }
    if (dump_all) {
        printf("\nCURVE: x^(%d) + y + x^(%d)*y^(%d) + x^(%d)*y^(%d) = 0 over GF(2^%d)\n", QQ, QQ - 1, Q, QQ - Q, QQ, m);
    }
    if(G.nind>=npts) {
        fprintf(stderr, "n must exceed dim L(G)\n");
        return 1;
    }
    Tab S, D;
    S.G=D.G=&G;
    S.W=D.W=G.jmax-G.jmin+1;
    size_t tsz=(size_t)(G.imax-G.imin+1)*S.W;
    S.T=malloc(sizeof(fe)*tsz);
    D.T=malloc(sizeof(fe)*tsz);
    int*tpos=malloc(sizeof(int)*t);
    fe*tval=malloc(sizeof(fe)*t);
    for(int u=0; u<t; u++) {
        int p, dup;
        do {
            p=rnd()%npts;
            dup=0;
            for(int k=0; k<u; k++) if(tpos[k]==p) dup=1;
        }
        while(dup);
        tpos[u]=p;
        do tval[u]=rnd()%FS;
        while(!tval[u]);
    }
    t0=now();
    syndrome_table(&S, tpos, tval, t);
    double ts=now()-t0;
    if (dump_all) {
        print_poly_basis("BASIS OF L(G)", &G);
        print_syndromes(&S);
    }
    /* 復号器には独立なシンドローム成分（dim L(G) 個）だけを渡す */
    memset(D.T, 0, sizeof(fe)*tsz);
    for(int p=0; p<G.n; p++) if(G.ind[p]) *Tp(&D, G.pi[p], G.pj[p])=*Tp(&S, G.pi[p], G.pj[p]);
    int*pos=malloc(sizeof(int)*(npts+1));
    fe*val=malloc(sizeof(fe)*(npts+1));
    int info[4]= {
        0
    }
    ;
    t0=now();
    int cnt=error_from_syndrome(&D, &F, &H, pos, val, info);
    double td=now()-t0;
    int extok=!memcmp(S.T, D.T, sizeof(fe)*tsz);
    int good=(cnt==t) && !has_duplicate_positions(pos, cnt);
    for(int c=0; c<cnt&&good; c++) {
        int f=0;
        for(int u=0; u<t; u++) if(tpos[u]==pos[c]&&tval[u]==val[c]) f=1;
        if(!f) good=0;
    }
    printf("誤りベクトルからのシンドローム計算（検査行列なし）: %.4f s, 独立成分 %d 個\n", ts, G.nind);
    printf("独立成分から復元した従属成分と直接計算した値の一致: %s\n", extok?"はい":"いいえ");
    printf("復号: %.3f 秒, 復元した誤り数=%d（核の次元=%d, 共通零点数=%d） -> %s\n", td, cnt, info[2], info[3], good?"成功":"失敗");
    if (dump_all && cnt >= 0) print_error_comparison(tpos, tval, t, pos, val, cnt);
    return good?0:2;
}
