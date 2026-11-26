/*
 * Binary Reed-Muller RM(r,m): encoder and exact hard-decision ML decoder.
 * c(x) = sum_{|S|<=r} a_S product_{i in S} x_i over GF(2).
 * n=2^m, k=sum_{j=0}^r C(m,j), d=2^(m-r).
 *
 * Build: cc -O3 -std=c11 -Wall -Wextra -o reed_muller reed_muller.c
 * Run:   ./reed_muller --r 2 --m 4 --errors 3 --trials 100 --seed 1
 *
 * The decoder exhaustively searches all 2^k codewords. It is exact ML, but
 * exponential; this reference implementation limits k to 24.
 */
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAX_M 10
#define MAX_K 24

typedef struct {
    int r, m, n, k;
    uint16_t *monomial;
    uint8_t *basis;
} RMCode;

static uint64_t rng_state = UINT64_C(0x9e3779b97f4a7c15);
static uint64_t rng_next(void) {
    uint64_t x = rng_state;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rng_state = x;
    return x * UINT64_C(2685821657736338717);
}
static int pc(unsigned x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcount(x);
#else
    int n=0; while(x){n+=(int)(x&1u);x>>=1;} return n;
#endif
}
static int binom(int n,int r) {
    if(r<0||r>n)return 0;
    if(r>n-r)r=n-r;
    int64_t v=1;
    for(int i=1;i<=r;i++)v=v*(n-r+i)/i;
    return (int)v;
}
static void rm_free(RMCode *c) {
    free(c->monomial); free(c->basis); memset(c,0,sizeof(*c));
}
static int rm_init(RMCode *c,int r,int m) {
    memset(c,0,sizeof(*c));
    if(m<1||m>MAX_M||r<0||r>m)return -1;
    c->r=r;c->m=m;c->n=1<<m;
    for(int j=0;j<=r;j++)c->k+=binom(m,j);
    if(c->k>MAX_K)return -2;
    c->monomial=malloc((size_t)c->k*sizeof(*c->monomial));
    c->basis=calloc((size_t)c->k*(size_t)c->n,sizeof(*c->basis));
    if(!c->monomial||!c->basis){rm_free(c);return -3;}
    int j=0;
    for(unsigned mask=0;mask<(unsigned)c->n;mask++)
        if(pc(mask)<=r)c->monomial[j++]=(uint16_t)mask;
    for(int b=0;b<c->k;b++){
        unsigned mask=c->monomial[b];
        for(int x=0;x<c->n;x++)
            c->basis[(size_t)b*c->n+x]=(uint8_t)(((unsigned)x&mask)==mask);
    }
    return 0;
}
static void rm_encode(const RMCode *c,const uint8_t *msg,uint8_t *word) {
    memset(word,0,(size_t)c->n);
    for(int b=0;b<c->k;b++)if(msg[b]){
        const uint8_t *v=c->basis+(size_t)b*c->n;
        for(int x=0;x<c->n;x++)word[x]^=v[x];
    }
}
static int hamming(const uint8_t *a,const uint8_t *b,int n) {
    int d=0;for(int i=0;i<n;i++)d+=(a[i]!=b[i]);return d;
}
/* Gray-code enumeration: one generator row toggles per candidate. */
static int rm_decode_ml(const RMCode *c,const uint8_t *received,
                        uint8_t *decoded,uint8_t *decoded_msg,
                        uint64_t *tested) {
    uint64_t total=UINT64_C(1)<<c->k, prev=0, count=0;
    uint8_t *candidate=calloc((size_t)c->n,1);
    if(!candidate)return -1;
    int best=c->n+1;
    for(uint64_t i=0;i<total;i++){
        uint64_t gray=i^(i>>1);
        if(i){
            uint64_t changed=gray^prev;
#if defined(__GNUC__) || defined(__clang__)
            int b=__builtin_ctzll(changed);
#else
            int b=0;while(((changed>>b)&1u)==0)b++;
#endif
            const uint8_t *v=c->basis+(size_t)b*c->n;
            for(int x=0;x<c->n;x++)candidate[x]^=v[x];
        }
        prev=gray;
        int d=hamming(candidate,received,c->n);count++;
        if(d<best){
            best=d;memcpy(decoded,candidate,(size_t)c->n);
            for(int b=0;b<c->k;b++)decoded_msg[b]=(uint8_t)((gray>>b)&1u);
            if(!best)break;
        }
    }
    free(candidate);if(tested)*tested=count;return best;
}
static void usage(const char *p) {
    printf("Usage: %s --r R --m M [--errors T] [--trials N] [--seed S]\n",p);
    puts("Binary RM(r,m), exact hard-decision ML decoder.");
    puts("  --r R       order (0 <= R <= M)");
    puts("  --m M       variables (1 <= M <= 10)");
    puts("  --errors T  injected bit errors (default 1)");
    puts("  --trials N  trials (default 1)");
    puts("  --seed S    unsigned seed (default fixed seed)");
    puts("  --help      show help");
    puts("Exact decoding is limited to dimension k <= 24 (2^k candidates).");
}
int main(int argc,char **argv) {
    int r=-1,m=-1,errors=1,trials=1;
    uint64_t seed=UINT64_C(0x9e3779b97f4a7c15);
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--help")||!strcmp(argv[i],"-h")){usage(argv[0]);return 0;}
        if((!strcmp(argv[i],"--r")||!strcmp(argv[i],"--m")||
            !strcmp(argv[i],"--errors")||!strcmp(argv[i],"--trials")||
            !strcmp(argv[i],"--seed"))&&i+1<argc){
            const char *opt=argv[i++];char *end=NULL;errno=0;
            if(!strcmp(opt,"--seed"))seed=strtoull(argv[i],&end,0);
            else{
                long v=strtol(argv[i],&end,10);
                if(!strcmp(opt,"--r"))r=(int)v;
                else if(!strcmp(opt,"--m"))m=(int)v;
                else if(!strcmp(opt,"--errors"))errors=(int)v;
                else trials=(int)v;
            }
            if(errno||!end||*end){fprintf(stderr,"Invalid value for %s: %s\n",opt,argv[i]);return 2;}
        }else{fprintf(stderr,"Unknown/incomplete option: %s\n",argv[i]);usage(argv[0]);return 2;}
    }
    if(r<0||m<1||errors<0||trials<1){usage(argv[0]);return 2;}
    RMCode c;int rc=rm_init(&c,r,m);
    if(rc){
        if(rc==-2)fprintf(stderr,"RM(%d,%d) dimension exceeds exact-decoder limit k=%d.\n",r,m,MAX_K);
        else fprintf(stderr,"Invalid parameters or allocation failure (code %d).\n",rc);
        return 2;
    }
    if(errors>c.n){fprintf(stderr,"--errors must be <= n=%d\n",c.n);rm_free(&c);return 2;}
    uint8_t *msg=calloc((size_t)c.k,1),*dmsg=calloc((size_t)c.k,1);
    uint8_t *word=calloc((size_t)c.n,1),*recv=calloc((size_t)c.n,1),*decoded=calloc((size_t)c.n,1);
    int *perm=malloc((size_t)c.n*sizeof(*perm));
    if(!msg||!dmsg||!word||!recv||!decoded||!perm){
        fprintf(stderr,"Out of memory.\n");free(msg);free(dmsg);free(word);free(recv);free(decoded);free(perm);rm_free(&c);return 2;
    }
    rng_state=seed?seed:1;
    int dmin=1<<(m-r),tbound=(dmin-1)/2,success=0;
    uint64_t candidates=0;
    clock_t start=clock();
    printf("# RM(%d,%d): n=%d k=%d d=%d guaranteed_t=%d\n",r,m,c.n,c.k,dmin,tbound);
    puts("# decoder: exact hard-decision maximum likelihood");
    for(int trial=0;trial<trials;trial++){
        for(int b=0;b<c.k;b++)msg[b]=(uint8_t)(rng_next()&1u);
        rm_encode(&c,msg,word);memcpy(recv,word,(size_t)c.n);
        for(int x=0;x<c.n;x++)perm[x]=x;
        for(int e=0;e<errors;e++){
            int j=e+(int)(rng_next()%(uint64_t)(c.n-e));
            int tmp=perm[e];perm[e]=perm[j];perm[j]=tmp;recv[perm[e]]^=1u;
        }
        uint64_t tested=0;
        int dist=rm_decode_ml(&c,recv,decoded,dmsg,&tested);candidates+=tested;
        int exact=dist>=0&&!memcmp(decoded,word,(size_t)c.n);
        if(exact)success++;
        printf("# trial %d: distance=%d candidates=%" PRIu64 " %s\n",
               trial+1,dist,tested,exact?"RECOVERED":"NOT_RECOVERED");
    }
    printf("# result: %d/%d exact recoveries\n",success,trials);
    printf("# candidates tested: %" PRIu64 "\n",candidates);
    printf("# CPU time: %.6f s\n",(double)(clock()-start)/CLOCKS_PER_SEC);
    free(msg);free(dmsg);free(word);free(recv);free(decoded);free(perm);rm_free(&c);
    return success==trials?0:1;
}
