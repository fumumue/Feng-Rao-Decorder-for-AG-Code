#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define Q 8
#define N 62
#define MAX_RR 63
#define MAX_SEMIGROUP 4096
#define MAX_ERRORS 12
#define FIELD_POLY 0x0Bu
typedef struct { uint8_t x, y; } Point;
typedef struct { int a, b; uint8_t value[N]; } SemigroupFunction;
typedef struct { int a, b; uint8_t value[N]; } RRFunction;
typedef struct { int a, b; uint8_t value[N]; } Generator;
static uint8_t gf_mul(uint8_t a, uint8_t b)
{
uint8_t z = 0;
while (b) {
if (b & 1u) z ^= a;
b >>= 1;
a <<= 1;
if (a & 8u) a ^= FIELD_POLY;
}
return (uint8_t)(z & 7u);
}
static uint8_t gf_pow(uint8_t a, unsigned e)
{
uint8_t z = 1;
while (e) {
if (e & 1u) z = gf_mul(z, a);
a = gf_mul(a, a);
e >>= 1;
}
return z;
}
static uint8_t gf_inv(uint8_t a) { return a ? gf_pow(a, 6) : 0; }
static int rref(uint8_t *m, int rows, int cols, int *pivots)
{
int rank = 0;
for (int col = 0; col < cols && rank < rows; ++col) {
int p = rank;
while (p < rows && m[p * cols + col] == 0) ++p;
if (p == rows) continue;
if (p != rank) {
for (int j = 0; j < cols; ++j) {
uint8_t t = m[rank * cols + j];
m[rank * cols + j] = m[p * cols + j];
m[p * cols + j] = t;
}
}
uint8_t s = gf_inv(m[rank * cols + col]);
for (int j = 0; j < cols; ++j)
m[rank * cols + j] = gf_mul(m[rank * cols + j], s);
for (int i = 0; i < rows; ++i) {
if (i == rank) continue;
uint8_t f = m[i * cols + col];
if (!f) continue;
for (int j = 0; j < cols; ++j)
m[i * cols + j] ^= gf_mul(f, m[rank * cols + j]);
}
pivots[rank++] = col;
}
return rank;
}
static int nullspace(const uint8_t *input, int rows, int cols,
uint8_t basis[N][N])
{
uint8_t m[MAX_RR * N];
int pivots[MAX_RR], is_pivot[N] = {0};
if (rows > MAX_RR || cols > N) return -1;
memset(m, 0, sizeof(m));
memcpy(m, input, (size_t)rows * (size_t)cols);
int rank = rref(m, rows, cols, pivots);
for (int i = 0; i < rank; ++i) is_pivot[pivots[i]] = 1;
int dim = 0;
for (int free_col = 0; free_col < cols; ++free_col) {
if (is_pivot[free_col]) continue;
memset(basis[dim], 0, N);
basis[dim][free_col] = 1;
for (int row = 0; row < rank; ++row)
basis[dim][pivots[row]] = m[row * cols + free_col];
++dim;
}
return dim;
}
static int pair_equal(int a, int b, int c, int d) { return a == c && b == d; }
static int find_pair(const SemigroupFunction *s, int count, int a, int b)
{
for (int i = 0; i < count; ++i)
if (pair_equal(s[i].a, s[i].b, a, b)) return i;
return -1;
}
static void generator_values(uint8_t x, uint8_t y, uint8_t vals[22])
{
    uint8_t y2=gf_mul(y,y), y3=gf_mul(y2,y), y4=gf_mul(y2,y2);
    uint8_t x2=gf_mul(x,x), x5=gf_mul(gf_mul(x2,x2),x);
    uint8_t v=y4^x5;
    uint8_t w=gf_mul(x,y4)^gf_pow(v,4);
    if (w==0) { fprintf(stderr,"Internal error: denominator vanishes on support.\n"); exit(EXIT_FAILURE); }
    uint8_t iw=gf_inv(w), iw2=gf_mul(iw,iw), iw3=gf_mul(iw2,iw);
    vals[0]=gf_mul(v,iw); vals[1]=gf_mul(y,iw);
    vals[2]=gf_mul(x,iw); vals[3]=iw;
    vals[4]=x; vals[5]=y; vals[6]=v; vals[7]=w;
    static const int gp[14][2]={{1,27},{2,19},{3,11},{4,17},{5,9},{6,15},{7,7},
        {9,5},{11,3},{14,14},{15,6},{17,4},{19,2},{27,1}};
    vals[8]=gf_mul(y4,iw);
    vals[9]=gf_mul(gf_mul(v,y2),iw);
    vals[10]=gf_mul(gf_mul(v,v),iw);
    vals[11]=gf_mul(y3,iw);
    vals[12]=gf_mul(gf_mul(v,y),iw);
    vals[13]=gf_mul(gf_mul(x,y2),iw);
    vals[14]=gf_mul(y2,iw);
    vals[15]=gf_mul(gf_mul(x,y),iw);
    vals[16]=gf_mul(x2,iw);
    vals[17]=gf_mul(y4,iw2);
    vals[18]=gf_mul(gf_mul(v,y2),iw2);
    vals[19]=gf_mul(y3,iw2);
    vals[20]=gf_mul(gf_mul(x,y2),iw2);
    vals[21]=gf_mul(y4,iw3);
    (void)gp;
}
static void make_points_and_generators(Point points[N], Generator gen[22], Generator shifted[22])
{
    int np=0;
    for (int x=0;x<Q;++x) for (int y=0;y<Q;++y) {
        if ((x==0 && y==0) || (x==0 && y==1)) continue;
        points[np++]=(Point){(uint8_t)x,(uint8_t)y};
    }
    if (np!=N) { fprintf(stderr,"Unexpected support size: %d\n",np); exit(EXIT_FAILURE); }
    static const int aa[4]={8,10,12,13};
    static const int bb[4]={8,10,12,13};
    static const int gp[14][2]={{1,27},{2,19},{3,11},{4,17},{5,9},{6,15},{7,7},
        {9,5},{11,3},{14,14},{15,6},{17,4},{19,2},{27,1}};
    for (int k=0;k<4;++k) { gen[k].a=aa[k]; gen[k].b=0; shifted[k].a=aa[k]; shifted[k].b=0; }
    for (int k=0;k<4;++k) { gen[4+k].a=0; gen[4+k].b=bb[k]; shifted[4+k].a=0; shifted[4+k].b=bb[k]; }
    for (int k=0;k<14;++k) {
        gen[8+k].a=gp[k][0]; gen[8+k].b=gp[k][1];
        shifted[8+k].a=gp[k][0]; shifted[8+k].b=gp[k][1];
    }
    for (int p=0;p<N;++p) {
        uint8_t v[22], vs[22];
        generator_values(points[p].x,points[p].y,v);
        generator_values(points[p].x,(uint8_t)(points[p].y^1u),vs);
        for (int k=0;k<22;++k) { gen[k].value[p]=v[k]; shifted[k].value[p]=vs[k]; }
    }
}
static int add_independent(RRFunction out[MAX_RR], int *nr,
uint8_t echelon[MAX_RR][N], int pivots[MAX_RR],
int *rank, int a, int b, const uint8_t value[N])
{
if (*nr >= MAX_RR) return 0;
uint8_t v[N]; memcpy(v, value, N);
for (int r = 0; r < *rank; ++r) {
uint8_t f = v[pivots[r]];
if (!f) continue;
for (int c = 0; c < N; ++c) v[c] ^= gf_mul(f, echelon[r][c]);
}
int pivot = 0;
while (pivot < N && v[pivot] == 0) ++pivot;
if (pivot == N) return 1;
uint8_t inv = gf_inv(v[pivot]);
for (int c = 0; c < N; ++c) echelon[*rank][c] = gf_mul(v[c], inv);
pivots[*rank] = pivot;
++*rank;
out[*nr].a = a; out[*nr].b = b;
memcpy(out[*nr].value, value, N);
++*nr;
return 1;
}
static int build_rr_basis(int A, int B, const Generator gen[22], RRFunction out[MAX_RR])
{
SemigroupFunction *s = calloc(MAX_SEMIGROUP, sizeof(*s));
if (!s) return -1;
int ns = 1, nr = 0, rank = 0;
uint8_t echelon[MAX_RR][N] = {{0}};
int pivots[MAX_RR] = {0};
s[0].a = s[0].b = 0;
memset(s[0].value, 1, N);
for (int head = 0; head < ns; ++head) {
if (s[head].b != 0) continue;
for (int g = 0; g < 4; ++g) {
int na = s[head].a + gen[g].a;
if (na > A || find_pair(s, ns, na, 0) >= 0) continue;
if (ns >= MAX_SEMIGROUP) { free(s); return -1; }
s[ns].a = na; s[ns].b = 0;
for (int p = 0; p < N; ++p)
s[ns].value[p] = gf_mul(s[head].value[p], gen[g].value[p]);
++ns;
}
}
for (int head = 0; head < ns; ++head) {
if (s[head].a != 0) continue;
for (int g = 4; g < 8; ++g) {
int nb = s[head].b + gen[g].b;
if (nb > B || find_pair(s, ns, 0, nb) >= 0) continue;
if (ns >= MAX_SEMIGROUP) { free(s); return -1; }
s[ns].a = 0; s[ns].b = nb;
for (int p = 0; p < N; ++p)
s[ns].value[p] = gf_mul(s[head].value[p], gen[g].value[p]);
++ns;
}
}
for (int g = 8; g < 22; ++g) {
int na = gen[g].a, nb = gen[g].b;
if (na > A || nb > B || find_pair(s, ns, na, nb) >= 0) continue;
if (ns >= MAX_SEMIGROUP) { free(s); return -1; }
s[ns].a = na; s[ns].b = nb;
memcpy(s[ns].value, gen[g].value, N);
++ns;
}
for (int i = 0; i < ns; ++i)
if (!add_independent(out, &nr, echelon, pivots, &rank,
s[i].a, s[i].b, s[i].value)) { free(s); return -1; }
for (int i = 0; i < ns; ++i) {
for (int j = i + 1; j < ns; ++j) {
int pa = s[i].a > s[j].a ? s[i].a : s[j].a;
int pb = s[i].b > s[j].b ? s[i].b : s[j].b;
if (pa > A || pb > B) continue;
for (int c = 1; c < Q; ++c) {
uint8_t value[N];
for (int p = 0; p < N; ++p)
value[p] = s[i].value[p] ^ gf_mul((uint8_t)c, s[j].value[p]);
if (!add_independent(out, &nr, echelon, pivots, &rank,
pa, pb, value)) { free(s); return -1; }
if (rank >= MAX_RR) break;
}
}
}
free(s);
return nr;
}
typedef struct { int a,b,c; uint8_t value[N]; } ThreeFunction;
static int add_three_independent(ThreeFunction out[MAX_RR], int *nr,
    uint8_t echelon[MAX_RR][N], int pivots[MAX_RR], int *rank,
    int a,int b,int c,const uint8_t value[N])
{
    uint8_t v[N]; memcpy(v,value,N);
    for (int r=0;r<*rank;++r) {
        uint8_t f=v[pivots[r]];
        if (!f) continue;
        for (int col=0;col<N;++col) v[col]^=gf_mul(f,echelon[r][col]);
    }
    int pivot=0; while (pivot<N && v[pivot]==0) ++pivot;
    if (pivot==N) return 1;
    if (*nr>=MAX_RR || *rank>=MAX_RR) return 0;
    uint8_t inv=gf_inv(v[pivot]);
    for (int col=0;col<N;++col) echelon[*rank][col]=gf_mul(v[col],inv);
    pivots[*rank]=pivot; ++*rank;
    out[*nr].a=a; out[*nr].b=b; out[*nr].c=c;
    memcpy(out[*nr].value,value,N); ++*nr;
    return 1;
}
/*
 * P00=(0,0), P01=(0,1), Pinf.
 * y -> y+1 preserves y^8+y=x^10+x^3 and sends P00 to P01.
 * If f has pole bounds (a,c) at (P00,Pinf), and f^tau has
 * bounds (b,c') at (P01,Pinf), then f*f^tau has bounds
 * (a,b,c+c') at the three places.
 */
static int build_three_basis(int A,int B,int C,const Generator gen[22],
    const Generator shifted[22],ThreeFunction out[MAX_RR])
{
    RRFunction left[MAX_RR],right[MAX_RR];
    int nl=build_rr_basis(A,C,gen,left);
    int nr=build_rr_basis(B,C,shifted,right);
    if (nl<0 || nr<0) return -1;
    int count=0,rank=0;
    uint8_t echelon[MAX_RR][N]={{0}};
    int pivots[MAX_RR]={0};
    for (int i=0;i<nl;++i) for (int j=0;j<nr;++j) {
        int inf=left[i].b+right[j].b;
        if (inf>C) continue;
        uint8_t value[N];
        for (int p=0;p<N;++p)
            value[p]=gf_mul(left[i].value[p],right[j].value[p]);
        if (!add_three_independent(out,&count,echelon,pivots,&rank,
                left[i].a,right[j].a,inf,value)) return -1;
    }
    return count;
}
static uint8_t dot(const uint8_t *a, const uint8_t *b, int n)
{
uint8_t z = 0;
for (int i = 0; i < n; ++i) z ^= gf_mul(a[i], b[i]);
return z;
}
static int check_word(const uint8_t *h, int rows, const uint8_t *word)
{
for (int r = 0; r < rows; ++r)
if (dot(h + r*N, word, N) != 0) return 0;
return 1;
}
static void print_vector(const char *name, const uint8_t *v)
{
printf("%s = [", name);
for (int i = 0; i < N; ++i) printf("%s%u", i ? "," : "", v[i]);
puts("]");
}
static int parse_int_arg(const char *s, int *v)
{
char *end = NULL; long x = strtol(s, &end, 10);
if (!s[0] || !end || *end || x < 0 || x > 1000000) return 0;
*v = (int)x; return 1;
}
int main(int argc,char **argv)
{
    int A=10,B=10,C=10,errors=2,seed=7;
    for (int i=1;i<argc;++i) {
        if ((!strcmp(argv[i],"--a")||!strcmp(argv[i],"-a"))&&i+1<argc) {
            if (!parse_int_arg(argv[++i],&A)) return 2;
        } else if ((!strcmp(argv[i],"--b")||!strcmp(argv[i],"-b"))&&i+1<argc) {
            if (!parse_int_arg(argv[++i],&B)) return 2;
        } else if ((!strcmp(argv[i],"--c")||!strcmp(argv[i],"-c"))&&i+1<argc) {
            if (!parse_int_arg(argv[++i],&C)) return 2;
        } else if (!strcmp(argv[i],"--errors")&&i+1<argc) {
            if (!parse_int_arg(argv[++i],&errors)) return 2;
        } else if (!strcmp(argv[i],"--seed")&&i+1<argc) {
            if (!parse_int_arg(argv[++i],&seed)) return 2;
        } else if (!strcmp(argv[i],"--help")||!strcmp(argv[i],"-h")) {
            printf("Usage: %s [--a N] [--b N] [--c N] [--errors T] [--seed N]\n",argv[0]);
            printf("G = a P00 + b P01 + c Pinf; default: --a 10 --b 10 --c 10 --errors 2\n");
            return 0;
        } else { fprintf(stderr,"Unknown or incomplete argument: %s\n",argv[i]); return 2; }
    }
    if (A<0||B<0||C<0||A+B+C>60||errors<1||errors>MAX_ERRORS) {
        fprintf(stderr,"Require a,b,c >= 0, a+b+c <= 60, and 1 <= errors <= %d.\n",MAX_ERRORS);
        return EXIT_FAILURE;
    }
    Point points[N]; Generator gen[22],shifted[22];
    make_points_and_generators(points,gen,shifted);
    ThreeFunction basis_g[MAX_RR],basis_2g[MAX_RR];
    int k=build_three_basis(A,B,C,gen,shifted,basis_g);
    int m=build_three_basis(2*A,2*B,2*C,gen,shifted,basis_2g);
    if (k<=errors || m<=0 || m>=N) {
        fprintf(stderr,"RR subspace dimensions unsuitable: dim U=%d, dim U2=%d.\n",k,m);
        fprintf(stderr,"Try different a,b,c (with a+b+c <= 60) or fewer errors.\n");
        return EXIT_FAILURE;
    }
    if (basis_g[0].a||basis_g[0].b||basis_g[0].c||
        basis_2g[0].a||basis_2g[0].b||basis_2g[0].c) {
        fprintf(stderr,"Constant function missing from the constructed spaces.\n");
        return EXIT_FAILURE;
    }
    uint8_t H[MAX_RR*N]={0};
    for (int r=0;r<m;++r) memcpy(H+r*N,basis_2g[r].value,N);
    uint8_t code_kernel[N][N]={{0}};
    int code_dim=nullspace(H,m,N,code_kernel);
    if (code_dim<=0) { fprintf(stderr,"The evaluation code has zero dimension.\n"); return EXIT_FAILURE; }
    uint8_t codeword[N]={0},received[N]={0},error[N]={0};
    for (int p=0;p<N;++p) {
        codeword[p]=code_kernel[0][p];
        if (code_dim>1) codeword[p]^=gf_mul(2,code_kernel[1][p]);
        if (code_dim>2) codeword[p]^=gf_mul(3,code_kernel[2][p]);
    }
    if (!check_word(H,m,codeword)) { fprintf(stderr,"Codeword check failed.\n"); return EXIT_FAILURE; }
    memcpy(received,codeword,N);
    srand((unsigned)seed);
    int err_pos[MAX_ERRORS]; uint8_t err_val[MAX_ERRORS];
    for (int e=0;e<errors;++e) {
        int p,used;
        do {
            p=rand()%N; used=0;
            for (int j=0;j<e;++j) if (err_pos[j]==p) used=1;
        } while (used);
        err_pos[e]=p; err_val[e]=(uint8_t)(1+rand()%7);
        error[p]=err_val[e]; received[p]^=err_val[e];
    }
    uint8_t S[MAX_RR*MAX_RR]={0};
    for (int i=0;i<k;++i) for (int j=0;j<k;++j) {
        uint8_t z=0;
        for (int p=0;p<N;++p)
            z^=gf_mul(received[p],gf_mul(basis_g[i].value[p],basis_g[j].value[p]));
        S[i*k+j]=z;
    }
    uint8_t syndrome_kernel[N][N]={{0}};
    int sk=nullspace(S,k,k,syndrome_kernel);
    if (sk<=0) { fprintf(stderr,"Syndrome matrix has trivial kernel; decoding failed.\n"); return EXIT_FAILURE; }
    int decoded[MAX_ERRORS],nd=0;
    for (int p=0;p<N;++p) {
        int common_zero=1;
        for (int v=0;v<sk&&common_zero;++v) {
            uint8_t z=0;
            for (int i=0;i<k;++i)
                z^=gf_mul(syndrome_kernel[v][i],basis_g[i].value[p]);
            if (z) common_zero=0;
        }
        if (common_zero) {
            if (nd<MAX_ERRORS) decoded[nd]=p;
            ++nd;
        }
    }
    if (nd!=errors) {
        fprintf(stderr,"Locator found %d candidates; injected errors=%d.\n",nd,errors);
        fprintf(stderr,"This parameter/seed is outside the demonstrated decoding range.\n");
        return EXIT_FAILURE;
    }
    uint8_t aug[MAX_ERRORS*(MAX_ERRORS+1)]={0};
    for (int r=0;r<errors;++r) {
        for (int c=0;c<errors;++c) aug[r*(errors+1)+c]=basis_g[r].value[decoded[c]];
        uint8_t z=0;
        for (int p=0;p<N;++p)
            z^=gf_mul(received[p]^codeword[p],basis_g[r].value[p]);
        aug[r*(errors+1)+errors]=z;
    }
    int piv[MAX_ERRORS]={0};
    int rank=rref(aug,errors,errors+1,piv);
    if (rank!=errors) { fprintf(stderr,"Error-value system is singular.\n"); return EXIT_FAILURE; }
    uint8_t corrected[N]; memcpy(corrected,received,N);
    uint8_t decoded_values[MAX_ERRORS];
    for (int e=0;e<errors;++e) {
        if (piv[e]!=e) { fprintf(stderr,"Unexpected pivot layout.\n"); return EXIT_FAILURE; }
        decoded_values[e]=aug[e*(errors+1)+errors];
        corrected[decoded[e]]^=decoded_values[e];
    }
    if (memcmp(corrected,codeword,N)!=0||!check_word(H,m,corrected)) {
        fprintf(stderr,"Correction verification failed.\n"); return EXIT_FAILURE;
    }
    puts("Three-point Suzuki AG-derived code / basic syndrome-matrix decoder");
    puts("Curve: y^8 + y = x^10 + x^3 over GF(8)");
    printf("Divisor G = %d P00 + %d P01 + %d Pinf; support n=%d\n",A,B,C,N);
    printf("Constructed RR subspace dimensions: dim U=%d, dim U2=%d\n",k,m);
    printf("Code dimension=%d; syndrome rank=%d; kernel dimension=%d\n",code_dim,k-sk,sk);
    puts("\nEvaluation support (index : (x,y)):");
    for (int p=0;p<N;++p) printf("%2d : (%u,%u)%s",p,points[p].x,points[p].y,(p%4==3||p==N-1)?"\n":"   ");
    puts("Injected errors (index : point : value):");
    for (int e=0;e<errors;++e)
        printf("%d : (%u,%u) : %u\n",err_pos[e],points[err_pos[e]].x,points[err_pos[e]].y,err_val[e]);
    puts("Decoded errors:");
    for (int e=0;e<errors;++e)
        printf("%d : (%u,%u) : %u\n",decoded[e],points[decoded[e]].x,points[decoded[e]].y,decoded_values[e]);
    print_vector("codeword",codeword);
    print_vector("error_vector",error);
    print_vector("corrected",corrected);
    puts("Result: PASS (received word corrected to the original codeword)");
    return EXIT_SUCCESS;
}
