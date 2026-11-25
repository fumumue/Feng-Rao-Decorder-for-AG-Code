/*
 * bbgs_newton.c -- generalized BBGS family: point enumeration + Newton bases
 *
 * Fixed family choice: a=1, b=terms-2, c=terms-1 (terms=4..10).
 * Curve over GF(2^m):
 *   X^(q^(c-1)) + sum_{k=0}^{b-1} X^(q^(c-1)-q^k)Y^(q^(1+k))
 *                    + Y = 0.
 *
 * This program does NOT decode. It enumerates affine rational points and builds
 * candidate one-point L(MP) monomial bases for every primitive Newton edge.
 * Completeness is checked against Riemann-Roch when M >= 2g-1.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <math.h>

typedef uint16_t fe;
typedef struct { int x, y; } Term;
typedef struct { int x, y, dx, dy, len, wx, wy; } Edge;
typedef struct { int i, j; unsigned char have; } Rep;

static const unsigned prim_poly[12] = {0,3,7,0x0B,0x13,0x25,0x43,0x89,0x11D,0x211,0x409,0x805};
static int FM, FS, FO;
static fe *expt, *logt;
static int gf_init(int m, unsigned poly) {
    FM=m; FS=1<<m; FO=FS-1;
    expt=calloc((size_t)(2*FO+4),sizeof(fe));
    logt=calloc((size_t)FS,sizeof(fe));
    if(!expt||!logt) return -1;
    unsigned x=1;
    for(int i=0;i<FO;i++) {
        if(i && x==1) return -1;
        expt[i]=(fe)x; logt[x]=(fe)i;
        x<<=1; if(x&(unsigned)FS) x^=poly;
    }
    if(x!=1) return -1;
    for(int i=FO;i<2*FO+4;i++) expt[i]=expt[i-FO];
    return 0;
}
static inline fe fpow(fe a, unsigned n) {
    if(!n) return 1;
    if(!a) return 0;
    return expt[((uint64_t)logt[a]*(uint64_t)n)%(uint64_t)FO];
}
static inline fe fmul(fe a, fe b) {
    return (!a||!b)?0:expt[(unsigned)logt[a]+(unsigned)logt[b]];
}
static int gcd_i(int a,int b) { a=abs(a); b=abs(b); while(b){int t=a%b;a=b;b=t;} return a; }
static long long cross(Term a,Term b,Term c) {
    return (long long)(b.x-a.x)*(c.y-a.y)-(long long)(b.y-a.y)*(c.x-a.x);
}
static int cmp_term(const void *aa,const void *bb) {
    const Term *a=aa,*b=bb;
    if(a->x!=b->x) return a->x<b->x?-1:1;
    if(a->y!=b->y) return a->y<b->y?-1:1;
    return 0;
}
static int make_terms(int q,int a,int b,Term *t) {
    int c=a+b;
    uint64_t Q=1;
    for(int k=0;k<c-1;k++) {
        if(Q>(uint64_t)INT_MAX/(uint64_t)q) return 0;
        Q*= (uint64_t)q;
    }
    int n=0;
    uint64_t qk=1;
    for(int k=0;k<b;k++) {
        uint64_t ypow=1;
        for(int z=0;z<a+k;z++) {
            if(ypow>(uint64_t)INT_MAX/(uint64_t)q) return 0;
            ypow*= (uint64_t)q;
        }
        t[n++]=(Term){(int)(Q-qk),(int)ypow};
        if(k+1<b) qk*= (uint64_t)q;
    }
    qk=1;
    uint64_t qb=1;
    for(int z=0;z<b;z++) qb*= (uint64_t)q;
    for(int k=0;k<a;k++) {
        t[n++]=(Term){(int)(Q-qb*qk),(int)qk};
        if(k+1<a) qk*= (uint64_t)q;
    }
    t[n++]=(Term){(int)Q,0};
    return n;
}
static int make_hull(const Term *terms,int nt,Term *h) {
    Term p[64]; memcpy(p,terms,(size_t)nt*sizeof(Term));
    qsort(p,(size_t)nt,sizeof(Term),cmp_term);
    int n=0; for(int i=0;i<nt;i++) if(!i||p[i].x!=p[i-1].x||p[i].y!=p[i-1].y) p[n++]=p[i];
    if(n<3) return 0;
    Term lo[128],up[128]; int nl=0,nu=0;
    for(int i=0;i<n;i++){while(nl>=2&&cross(lo[nl-2],lo[nl-1],p[i])<=0)nl--;lo[nl++]=p[i];}
    for(int i=n-1;i>=0;i--){while(nu>=2&&cross(up[nu-2],up[nu-1],p[i])<=0)nu--;up[nu++]=p[i];}
    int k=0; for(int i=0;i<nl-1;i++)h[k++]=lo[i]; for(int i=0;i<nu-1;i++)h[k++]=up[i];
    return k;
}
static int make_edges(const Term *h,int nh,Edge *e,int *genus) {
    long long a2=0; int boundary=0;
    for(int k=0;k<nh;k++) {
        Term p=h[k],r=h[(k+1)%nh]; int dx=r.x-p.x,dy=r.y-p.y,g=gcd_i(dx,dy);
        if(!g) return 0;
        e[k]=(Edge){p.x,p.y,dx,dy,g,-dy/g,dx/g};
        a2+=(long long)p.x*r.y-(long long)r.x*p.y; boundary+=g;
    }
    if(a2<0)a2=-a2;
    *genus=(int)((a2-boundary+2)/2);
    return 1;
}

static int pdeg(const unsigned char *p,int n) { while(n>=0&&!p[n])n--; return n; }
static int face_squarefree(const Term *terms,int nt,const Edge *e) {
    int len=e->len;
    unsigned char *f=calloc((size_t)len+1,1), *a=calloc((size_t)len+1,1), *b=calloc((size_t)len+1,1);
    if(!f||!a||!b){free(f);free(a);free(b);return 0;}
    int ux=e->dx/len,uy=e->dy/len;
    for(int k=0;k<nt;k++) {
        Term p=terms[k],s={e->x,e->y};
        if(cross(s,(Term){e->x+e->dx,e->y+e->dy},p)!=0) continue;
        if(p.x<(e->x<e->x+e->dx?e->x:e->x+e->dx)||p.x>(e->x>e->x+e->dx?e->x:e->x+e->dx)||
           p.y<(e->y<e->y+e->dy?e->y:e->y+e->dy)||p.y>(e->y>e->y+e->dy?e->y:e->y+e->dy)) continue;
        int t;
        if(ux) { int d=p.x-e->x; if(d%ux)continue; t=d/ux; }
        else { int d=p.y-e->y; if(d%uy)continue; t=d/uy; }
        if(t>=0&&t<=len) f[t]^=1;
    }
    int df=pdeg(f,len);
    for(int k=1;k<=df;k++) if(k&1) b[k-1]=f[k];
    int da=df,db=pdeg(b,df-1);
    memcpy(a,f,(size_t)len+1);
    while(db>=0) {
        while(da>=db) {
            int sh=da-db;
            for(int k=0;k<=db;k++) a[k+sh]^=b[k];
            da=pdeg(a,da);
        }
        unsigned char *tmp=a;a=b;b=tmp;
        int td=da;da=db;db=td;
    }
    int ok=(da==0 && a[0]!=0);
    free(f);free(a);free(b);
    return ok;
}
static int polygon_nondegenerate(const Term *terms,int nt,const Edge *edges,int ne) {
    for(int k=0;k<ne;k++) if(!face_squarefree(terms,nt,&edges[k])) return 0;
    return 1; /* affine smoothness follows from F_Y=1 in characteristic two */
}
static fe curve_eval(fe x,fe y,const Term *t,int nt) {
    fe z=0;
    for(int k=0;k<nt;k++) z^=fmul(fpow(x,(unsigned)t[k].x),fpow(y,(unsigned)t[k].y));
    return z;
}
static long long floor_div(long long a,long long b) { /* b>0 */
    long long q=a/b,r=a%b; if(r<0) --q; return q;
}
static int build_basis(int edge_id,const Edge *edges,int ne,int M,int genus,Rep **out,int *count,int *laurent) {
    Rep *r=calloc((size_t)M+1,sizeof(*r)); if(!r)return -1;
    const Edge *pe=&edges[edge_id]; int bad=0;
    /* Scan both sides of the i-axis. The feasible region is convex. */
    for(int dir=0;dir<2&&!bad;dir++) {
        long long i0=dir?-1:0;
        for(long long i=i0;;i+=dir?-1:1) {
            long long jl=LLONG_MIN/4,jh=LLONG_MAX/4;
            long double rl=-1e30L,rh=1e30L; int empty=0;
            for(int k=0;k<ne;k++) {
                long long a=edges[k].wx,b=edges[k].wy,ck=(k==edge_id)?M:0;
                long long v=a*i+ck;
                if(b==0) { if(v<0){empty=1;break;} }
                else if(b>0) {
                    long long l=-floor_div(v,b); if(l>jl)jl=l;
                    long double rr=-(long double)v/(long double)b; if(rr>rl)rl=rr;
                } else {
                    long long u=floor_div(v,-b); if(u<jh)jh=u;
                    long double rr=(long double)v/(long double)(-b); if(rr<rh)rh=rr;
                }
            }
            if(empty||rl>rh+1e-12L) break;
            if(jl<=jh) for(long long j=jl;j<=jh;j++) {
                long long rho=-((long long)pe->wx*i+(long long)pe->wy*j);
                if(rho<0||rho>M) { bad=1; break; }
                int neg=(i<0||j<0);
                if(!r[rho].have || (!neg&&(r[rho].i<0||r[rho].j<0))) {
                    if(i<INT_MIN||i>INT_MAX||j<INT_MIN||j>INT_MAX){bad=1;break;}
                    r[rho].i=(int)i; r[rho].j=(int)j; r[rho].have=1;
                }
            }
            if(bad)break;
            if(i>2000000||i< -2000000){bad=1;break;}
        }
    }
    int n=0,neg=0; for(int k=0;k<=M;k++)if(r[k].have){n++;if(r[k].i<0||r[k].j<0)neg++;}
    *out=r; *count=n; *laurent=(neg>0);
    if(bad) return -2;
    (void)genus;
    return 0;
}
static uint64_t count_points(const Term *t,int nt) {
    uint64_t n=0;
    for(int x=0;x<FS;x++) for(int y=0;y<FS;y++)
        if(curve_eval((fe)x,(fe)y,t,nt)==0) n++;
    return n;
}
static void usage(const char *p) {
    printf("Usage: %s --terms 4..10 --q 2^r --m M [--a A --b B | --genus G] [--poly P] [--M pole-order] [--edge E|-1] [--out PREFIX] [--list-points] [--dump-basis]\n",p);
    puts("Without --a/--b/--genus, search all coprime a+b=terms-1 and select the largest point count; also report the best pair for each genus.");
}
typedef struct { int a,b,g,basis,ndeg; uint64_t n; } Candidate;
int main(int argc,char **argv) {
    int terms=4,q=2,m=3,M=-1,edge_req=-1,list=0,dump=0;
    int a_req=-1,b_req=-1,genus_req=-1;
    unsigned poly=0; const char *prefix=NULL;
    for(int i=1;i<argc;i++) {
        if(!strcmp(argv[i],"--terms")&&i+1<argc)terms=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--q")&&i+1<argc)q=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--m")&&i+1<argc)m=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--a")&&i+1<argc)a_req=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--b")&&i+1<argc)b_req=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--genus")&&i+1<argc)genus_req=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--poly")&&i+1<argc)poly=(unsigned)strtoul(argv[++i],NULL,0);
        else if(!strcmp(argv[i],"--M")&&i+1<argc)M=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--edge")&&i+1<argc)edge_req=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--out")&&i+1<argc)prefix=argv[++i];
        else if(!strcmp(argv[i],"--list-points"))list=1;
        else if(!strcmp(argv[i],"--dump-basis"))dump=1;
        else if(!strcmp(argv[i],"--help")||!strcmp(argv[i],"-h")){usage(argv[0]);return 0;}
        else {fprintf(stderr,"unknown/incomplete option: %s\n",argv[i]);return 2;}
    }
    if(terms<4||terms>10||q<2||(q&(q-1))||m<2||m>11){fprintf(stderr,"terms=4..10, q=power of two >=2, m=2..11 required\n");return 2;}
    if((a_req<0)!=(b_req<0)){fprintf(stderr,"--a and --b must be specified together\n");return 2;}
    if(a_req>=0 && genus_req>=0){fprintf(stderr,"use either --a/--b or --genus, not both\n");return 2;}
    int rlog=0;for(int v=q;v>1;v>>=1)rlog++;
    int c=terms-1,need=rlog*c;
    if(need>m||m%need){fprintf(stderr,"field mismatch: require %d | m because GF(q^%d) must embed in GF(2^m) (m<=11 here)\n",need,c);return 2;}
    if(!poly)poly=prim_poly[m];
    if(gf_init(m,poly)){fprintf(stderr,"GF(2^%d) init failed (polynomial 0x%X is not primitive/valid)\n",m,poly);return 2;}

    Candidate cand[32]; int nc=0;
    if(a_req>=0) {
        if(a_req<1||b_req<1||a_req+b_req!=c||gcd_i(a_req,b_req)!=1){fprintf(stderr,"require a,b>0, a+b=terms-1, gcd(a,b)=1\n");return 2;}
        cand[nc++]=(Candidate){a_req,b_req,0,0,0,0};
    } else {
        for(int a=1;a<c;a++) { int b=c-a; if(gcd_i(a,b)!=1)continue;
            Term tt[64],hh[64]; Edge ee[64]; int nn=make_terms(q,a,b,tt),nh=make_hull(tt,nn,hh),gg=0;
            if(!nn||nh<3||!make_edges(hh,nh,ee,&gg)){fprintf(stderr,"candidate Newton polygon failed for a=%d b=%d\n",a,b);return 1;}
            uint64_t np=count_points(tt,nn);
            int ndeg=polygon_nondegenerate(tt,nn,ee,nh);
            int has_basis=0; for(int z=0;z<nh;z++) if(ee[z].len==1) has_basis=1;
            cand[nc++]=(Candidate){a,b,gg,has_basis&&ndeg,ndeg,np};
        }
        if(!nc){fprintf(stderr,"no coprime BBGS parameter pair found\n");return 1;}
        printf("Candidate search for terms=%d, q=%d over GF(2^%d):\n",terms,q,m);
        for(int i=0;i<nc;i++) {
            int best=1; for(int j=0;j<nc;j++)if(j!=i && cand[j].g==cand[i].g && (cand[j].n>cand[i].n || (cand[j].n==cand[i].n && j<i)))best=0;
            if(best) {
                int bi=-1;
                for(int j=0;j<nc;j++) if(cand[j].g==cand[i].g && cand[j].basis && (bi<0 || cand[j].n>cand[bi].n)) bi=j;
                printf("  genus=%d: max-points a=%d b=%d n=%llu; Newton-basis candidate=",cand[i].g,cand[i].a,cand[i].b,(unsigned long long)cand[i].n);
                if(bi>=0) printf("a=%d b=%d n=%llu\n",cand[bi].a,cand[bi].b,(unsigned long long)cand[bi].n);
                else puts("none (no primitive edge)");
            }
        }
        int chosen=-1;
        for(int i=0;i<nc;i++) {
            if(!cand[i].basis)continue;
            if(genus_req>=0 && cand[i].g!=genus_req)continue;
            if(chosen<0 || cand[i].n>cand[chosen].n)chosen=i;
        }
        if(chosen<0){fprintf(stderr,"no Newton-basis-capable candidate for genus=%d; choose another genus or explicit parameters\n",genus_req);return 2;}
        a_req=cand[chosen].a;b_req=cand[chosen].b;
        printf("Selected basis-capable curve: a=%d b=%d genus=%d affine_points=%llu%s\n",a_req,b_req,cand[chosen].g,(unsigned long long)cand[chosen].n,genus_req>=0?" (requested genus)":" (maximum points among basis-capable candidates)");
    }
    Term t[64],h[64]; int nt=make_terms(q,a_req,b_req,t); if(!nt){fprintf(stderr,"curve exponents exceed supported range\n");return 2;}
    int nh=make_hull(t,nt,h); Edge ed[64]; int genus=0; if(nh<3||!make_edges(h,nh,ed,&genus)){fprintf(stderr,"Newton polygon construction failed\n");return 1;}
    int ndeg=polygon_nondegenerate(t,nt,ed,nh);
    uint64_t npts=count_points(t,nt);
    if(M<0) M=2*genus-1;
    if(M<0||M>200000){fprintf(stderr,"M must be in 0..200000\n");return 2;}
    if(edge_req < -1 || edge_req >= nh){fprintf(stderr,"--edge must be -1 or a valid Newton edge index\n");return 2;}
    char ppoints[1024],pbasis[1024],pmeta[1024]; FILE *fp=NULL,*fb=NULL,*fmta=NULL;
    if(prefix){snprintf(ppoints,sizeof ppoints,"%s.points.tsv",prefix);snprintf(pbasis,sizeof pbasis,"%s.basis.tsv",prefix);snprintf(pmeta,sizeof pmeta,"%s.meta.txt",prefix);
        fp=fopen(ppoints,"w");fb=fopen(pbasis,"w");fmta=fopen(pmeta,"w");if(!fp||!fb||!fmta){perror("open output");return 1;}}
    printf("BBGS family: terms=%d, q=%d, a=%d, b=%d, c=%d\n",terms,q,a_req,b_req,c);
    printf("Field: GF(2^%d), polynomial=0x%X; required subfield GF(2^%d)\n",m,poly,need);
    printf("F(X,Y) ="); for(int k=0;k<nt;k++){ if(t[k].x==0)printf(" + Y^%d",t[k].y); else if(t[k].y==0)printf(" + X^%d",t[k].x); else printf(" + X^%d Y^%d",t[k].x,t[k].y); } puts(" = 0");
    printf("Newton polygon vertices (%d):",nh);for(int k=0;k<nh;k++)printf(" (%d,%d)",h[k].x,h[k].y);puts("");
    printf("Newton arithmetic genus g=%d; toric nondegeneracy=%s; M=%d; RR target dim=%d%s\n",genus,ndeg?"PASS":"FAIL",M,M+1-genus,(M>=2*genus-1)?" (M>=2g-1)":" (below 2g-1; completeness not certified by RR formula)");
    for(int k=0;k<nh;k++)printf("edge E%d: start=(%d,%d), direction=(%d,%d), lattice length=%d, inward weight=(%d,%d)%s\n",k,ed[k].x,ed[k].y,ed[k].dx,ed[k].dy,ed[k].len,ed[k].wx,ed[k].wy,ed[k].len==1?" [primitive edge]":" [edge length > 1; branch decomposition needed]");
    if(fp)fprintf(fp,"x\ty\teval_nonzero_xy\n");
    for(int x=0;x<FS;x++)for(int y=0;y<FS;y++)if(curve_eval((fe)x,(fe)y,t,nt)==0){if(list)printf("P\t%d\t%d\n",x,y);if(fp)fprintf(fp,"%d\t%d\t%d\n",x,y,(x!=0&&y!=0));}
    printf("Affine rational points over GF(2^%d): %llu\n",m,(unsigned long long)npts);
    if(fp)printf("Wrote points: %s\n",ppoints);
    if(fb)fprintf(fb,"edge\tpole_order\ti\tj\tmonomial\n");
    int all_ok=1,nbuilt=0,rr_checked=0;
    for(int e=0;e<nh;e++) {
        if(ed[e].len!=1 || !ndeg)continue;
        if(edge_req>=0&&edge_req!=e)continue;
        Rep *reps=NULL;int cnt=0,laurent=0;int rc=build_basis(e,ed,nh,M,genus,&reps,&cnt,&laurent);
        int expected=(M>=2*genus-1)?M+1-genus:-1;
        if(expected>=0) rr_checked=1;
        int ok=(rc==0 && (expected<0||cnt==expected)); if(!ok)all_ok=0; nbuilt++;
        printf("Newton basis E%d: dimension=%d",e,cnt);if(expected>=0)printf(", RR target=%d, check=%s",expected,ok?"PASS":"FAIL");else printf(", RR dimension check not applicable");
        printf(", %s monomials\n",laurent?"Laurent":"polynomial");
        if(dump)for(int rho=0;rho<=M;rho++)if(reps&&reps[rho].have)printf("B E%d rho=%d: x^(%d)y^(%d)\n",e,rho,reps[rho].i,reps[rho].j);
        if(fb)for(int rho=0;rho<=M;rho++)if(reps&&reps[rho].have)fprintf(fb,"%d\t%d\t%d\t%d\tx^(%d)y^(%d)\n",e,rho,reps[rho].i,reps[rho].j,reps[rho].i,reps[rho].j);
        free(reps);
    }
    if(!nbuilt){fprintf(stderr,"no primitive edge selected; choose an edge with lattice length 1\n");all_ok=0;}
    if(!all_ok) printf("Basis status: FAIL (one or more checks failed or no basis was built)\n");
    else if(rr_checked) printf("Basis status: PASS (all selected Newton/RR dimension checks passed)\n");
    else printf("Basis status: candidate generated; Riemann-Roch completeness not checked because M<2g-1\n");
    if(fmta){
        fprintf(fmta,"terms=%d\nq=%d\nm=%d\na=%d\nb=%d\npoly=0x%X\nM=%d\nnewton_arithmetic_genus=%d\naffine_rational_points=%llu\n",terms,q,m,a_req,b_req,poly,M,genus,(unsigned long long)npts);
        fprintf(fmta,"newton_toric_nondegenerate=%d\n",ndeg);
        fprintf(fmta,"basis_dimension_formula_valid=%d\n",M>=2*genus-1);
        fprintf(fmta,"evaluation_note=Basis may contain negative exponents; exclude points with x=0 or y=0 from evaluation. points.tsv marks these with eval_nonzero_xy=0.\n");
        fprintf(fmta,"basis_rr_dimension_checks=%s\n",!all_ok?"FAIL":(rr_checked?"PASS":"NOT_CHECKED"));
        fclose(fmta);fclose(fp);fclose(fb);printf("Wrote basis: %s\nWrote metadata: %s\n",pbasis,pmeta);
    }
    free(expt);free(logt);
    return all_ok?0:1;
}
