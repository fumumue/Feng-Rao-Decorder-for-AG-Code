/*
 * BBGS E2 over GF(8): one-point AG code and a small bounded-distance decoder.
 *
 * Curve (q=2,c=3,a=1,b=2), written without rational functions:
 *   x^3*y^2 + x^2*y^4 + x^4*y + x^4 = 0.
 * This is the denominator-cleared form of the trace equation on x != 0.
 * D consists of the 28 affine rational places (x,y), x != 0.
 * P1=(x=0,y=0,x^(-4)y=1) is the unique rational place in P.
 * It is not a rational point at infinity.
 *
 * For this curve:
 *   div(x)=P1+3V-2Q, div(y)=4P1-2V-Q.
 * A rational-function basis of L(11P1) is:
 *   x^-1 y^-2, y^-2, y^-1, 1, x y^-3, x y^-2.
 *
 * Since x and y are nonzero at every evaluation point in D, multiply
 * every basis function by the common nonzero factor x*y^3. The resulting
 * polynomial basis is:
 *   y, x*y, x*y^2, x*y^3, x^2, x^2*y.
 * This changes the evaluation vector at each point by the same nonzero
 * coordinate multiplier x*y^3, so the code is monomially equivalent:
 * n, k and minimum distance are unchanged. The parity-check matrix is
 * reconstructed from this polynomial generator matrix.
 *
 * The decoder constructs H as a nullspace basis of G and exhaustively
 * searches error supports of weight <= 3. It is a syndrome decoder for
 * this code, but is not claimed to be a Feng-Rao decoder or an 8-error
 * decoder. The designed-distance bound is 17; exact d=18 is verified
 * by exhaustive enumeration of all 8^6 codewords with --distance.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 8
#define MOD 0x0B
#define N 28
#define K 6
#define R (N-K)
#define MAX_T 3

typedef unsigned char gf;
typedef struct { gf x, y; } Point;
typedef struct { unsigned i, j; } Monomial;

static Point points[N];
static Monomial basis[K];
static gf G[K][N];
static gf H[R][N];

static gf mul(gf a, gf b) {
    gf r = 0;
    while (b) {
        if (b & 1u) r ^= a;
        b >>= 1;
        a <<= 1;
        if (a & 8u) a ^= MOD;
    }
    return (gf)(r & 7u);
}
static gf power(gf a, unsigned e) {
    gf r = 1;
    while (e) {
        if (e & 1u) r = mul(r, a);
        a = mul(a, a);
        e >>= 1;
    }
    return r;
}
static gf inverse(gf a) { return a ? power(a, 6u) : 0; }
static gf divide(gf a, gf b) { return mul(a, inverse(b)); }
static gf trace2(gf a, unsigned n) {
    gf s = 0;
    for (unsigned i = 0; i < n; ++i) { s ^= a; a = mul(a, a); }
    return s;
}
static gf eval_monomial(Monomial m, Point p) {
    return mul(power(p.x, m.i), power(p.y, m.j));
}
static int on_curve(gf x, gf y) {
    /* Polynomial form: x^3*y^2 + x^2*y^4 + x^4*y + x^4 = 0. */
    gf x2 = power(x, 2u), x3 = power(x, 3u), x4 = power(x, 4u);
    gf y2 = power(y, 2u), y4 = power(y, 4u);
    gf v = mul(x3, y2) ^ mul(x2, y4) ^ mul(x4, y) ^ x4;
    return v == 0;
}
static int enumerate_points(void) {
    int n = 0;
    for (gf x = 1; x < Q; ++x)
        for (gf y = 0; y < Q; ++y)
            if (on_curve(x, y)) {
                if (n >= N) return -1;
                points[n++] = (Point){x, y};
            }
    return n;
}

/* Polynomial basis obtained by multiplying the RR basis by x*y^3. */
static int construct_basis(void) {
    static const Monomial polynomial_basis[K] = {
        {0,1},  /* y    */
        {1,1},  /* x*y  */
        {1,2},  /* x*y^2 */
        {1,3},  /* x*y^3 */
        {2,0},  /* x^2 */
        {2,1}   /* x^2*y */
    };
    memcpy(basis, polynomial_basis, sizeof basis);
    return K;
}

/* RREF over GF(8); A is packed with the given row stride 'cols'. */
static int rref(gf *A, int rows, int cols, int *pivot_cols) {
    int rank = 0;
    for (int c = 0; c < cols && rank < rows; ++c) {
        int p = rank;
        while (p < rows && A[p*cols+c] == 0) ++p;
        if (p == rows) continue;
        if (p != rank)
            for (int j = 0; j < cols; ++j) {
                gf z = A[rank*cols+j]; A[rank*cols+j] = A[p*cols+j]; A[p*cols+j] = z;
            }
        gf iv = inverse(A[rank*cols+c]);
        for (int j = 0; j < cols; ++j) A[rank*cols+j] = mul(A[rank*cols+j], iv);
        for (int r = 0; r < rows; ++r) if (r != rank && A[r*cols+c]) {
            gf f = A[r*cols+c];
            for (int j = 0; j < cols; ++j)
                A[r*cols+j] ^= mul(f, A[rank*cols+j]);
        }
        pivot_cols[rank++] = c;
    }
    return rank;
}

static int construct_matrices(void) {
    for (int r = 0; r < K; ++r)
        for (int c = 0; c < N; ++c)
            G[r][c] = eval_monomial(basis[r], points[c]);

    gf A[K][N];
    memcpy(A, G, sizeof A);
    int piv[K];
    int rank = rref(&A[0][0], K, N, piv);
    if (rank != K) return -1;

    int is_pivot[N] = {0};
    for (int r = 0; r < rank; ++r) is_pivot[piv[r]] = 1;
    int hrow = 0;
    for (int f = 0; f < N; ++f) if (!is_pivot[f]) {
        for (int c = 0; c < N; ++c) H[hrow][c] = 0;
        H[hrow][f] = 1;
        for (int r = 0; r < rank; ++r) H[hrow][piv[r]] = A[r][f];
        ++hrow;
    }
    if (hrow != R) return -1;

    /* Verify H G^T = 0. */
    for (int h = 0; h < R; ++h)
        for (int g = 0; g < K; ++g) {
            gf s = 0;
            for (int p = 0; p < N; ++p) s ^= mul(H[h][p], G[g][p]);
            if (s) return -1;
        }
    return 0;
}

static void encode(const gf msg[K], gf word[N]) {
    memset(word, 0, N * sizeof(gf));
    for (int r = 0; r < K; ++r)
        for (int p = 0; p < N; ++p)
            word[p] ^= mul(msg[r], G[r][p]);
}
static void syndrome(const gf word[N], gf s[R]) {
    for (int h = 0; h < R; ++h) {
        s[h] = 0;
        for (int p = 0; p < N; ++p) s[h] ^= mul(H[h][p], word[p]);
    }
}

/* Solve H[:,support] * e = s; return 1 iff the solution is unique. */
static int solve_support(const gf s[R], const int support[], int t, gf err[MAX_T]) {
    gf A[R * (MAX_T+1)];
    for (int r = 0; r < R; ++r) {
        for (int c = 0; c < t; ++c) A[r*(t+1)+c] = H[r][support[c]];
        A[r*(t+1)+t] = s[r];
    }
    int piv[MAX_T+1];
    int rank = rref(A, R, t+1, piv);
    int coeff_rank = 0;
    for (int r = 0; r < rank; ++r) {
        if (piv[r] == t) return 0;
        if (piv[r] < t) ++coeff_rank;
    }
    if (coeff_rank != t) return 0;
    for (int c = 0; c < t; ++c) err[c] = 0;
    for (int r = 0; r < rank; ++r)
        if (piv[r] < t) err[piv[r]] = A[r*(t+1)+t];
    for (int c = 0; c < t; ++c) if (!err[c]) return 0;
    return 1;
}

static int try_support(const gf s[R], const int support[], int t,
                       gf corrected[N], const gf received[N]) {
    gf err[MAX_T] = {0};
    if (!solve_support(s, support, t, err)) return 0;
    memcpy(corrected, received, N * sizeof(gf));
    for (int c = 0; c < t; ++c) corrected[support[c]] ^= err[c];
    gf check[R]; syndrome(corrected, check);
    for (int r = 0; r < R; ++r) if (check[r]) return 0;
    return 1;
}

/* Exhaustive syndrome decoding for weights 0..3. */
static int decode(const gf received[N], gf corrected[N], int *weight_out) {
    gf s[R]; syndrome(received, s);
    int zero = 1;
    for (int r = 0; r < R; ++r) if (s[r]) { zero = 0; break; }
    if (zero) { memcpy(corrected, received, N*sizeof(gf)); *weight_out = 0; return 1; }

    int pos[MAX_T];
    for (int t = 1; t <= MAX_T; ++t) {
        if (t == 1) {
            for (pos[0] = 0; pos[0] < N; ++pos[0])
                if (try_support(s, pos, 1, corrected, received)) { *weight_out=1; return 1; }
        } else if (t == 2) {
            for (pos[0] = 0; pos[0] < N; ++pos[0])
                for (pos[1] = pos[0]+1; pos[1] < N; ++pos[1])
                    if (try_support(s, pos, 2, corrected, received)) { *weight_out=2; return 1; }
        } else {
            for (pos[0] = 0; pos[0] < N; ++pos[0])
                for (pos[1] = pos[0]+1; pos[1] < N; ++pos[1])
                    for (pos[2] = pos[1]+1; pos[2] < N; ++pos[2])
                        if (try_support(s, pos, 3, corrected, received)) { *weight_out=3; return 1; }
        }
    }
    return 0;
}

static unsigned rng_state = 1;
static unsigned rnd(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 17; rng_state ^= rng_state << 5;
    return rng_state;
}
static int same(const gf a[N], const gf b[N]) {
    return memcmp(a, b, N*sizeof(gf)) == 0;
}
static int exhaustive_minimum_distance(void) {
    int best = N + 1;
    gf msg[K], word[N];
    unsigned total = 1u;
    for (int i = 0; i < K; ++i) total *= Q;
    for (unsigned z0 = 1; z0 < total; ++z0) {
        unsigned z = z0;
        for (int i = 0; i < K; ++i) { msg[i] = (gf)(z & 7u); z >>= 3; }
        encode(msg, word);
        int wt = 0;
        for (int p = 0; p < N; ++p) if (word[p]) ++wt;
        if (wt < best) best = wt;
    }
    return best;
}
static void usage(const char *p) {
    printf("Usage: %s [--errors 0..3] [--seed N] [--trials N] [--distance]\n", p);
    puts("Constructs C_L(D,11P1) over GF(8), encodes a random message, adds errors, and decodes.");
    puts("--distance exhaustively checks all 8^6 codewords to determine the exact minimum distance.");
}

int main(int argc, char **argv) {
    int errors = 2, seed = 1, trials = 1, check_distance = 0;
    for (int a = 1; a < argc; ++a) {
        if (!strcmp(argv[a], "--help") || !strcmp(argv[a], "-h")) { usage(argv[0]); return 0; }
        if (!strcmp(argv[a], "--distance")) { check_distance = 1; continue; }
        if (a+1 >= argc) { fprintf(stderr, "missing value for %s\n", argv[a]); return 2; }
        const char *opt = argv[a++]; int v = atoi(argv[a]);
        if (!strcmp(opt, "--errors")) errors = v;
        else if (!strcmp(opt, "--seed")) seed = v;
        else if (!strcmp(opt, "--trials")) trials = v;
        else { fprintf(stderr, "unknown option: %s\n", opt); return 2; }
    }
    if (errors < 0 || errors > MAX_T || trials < 1 || trials > 10000) {
        fprintf(stderr, "errors must be 0..3 and trials 1..10000\n"); return 2;
    }
    if (enumerate_points() != N) { fprintf(stderr, "expected 28 affine rational points\n"); return 1; }
    if (construct_basis() != K) { fprintf(stderr, "expected six L(11P1) basis monomials\n"); return 1; }
    if (construct_matrices()) { fprintf(stderr, "generator/parity-check construction failed\n"); return 1; }

    printf("BBGS E2 over GF(8): C_L(D,11P1)\n");
    puts("Polynomial curve: x^3*y^2 + x^2*y^4 + x^4*y + x^4 = 0");
    puts("P1=(x=0,y=0,x^(-4)y=1); this is the rational one-point place, not an infinity point.");
    printf("n=%d, k=%d, genus=6, designed distance >=17, guaranteed radius >=8\n", N, K);
    printf("Decoder implementation: exhaustive syndrome search up to %d errors\n", MAX_T);
    puts("Polynomial basis (common factor x*y^3 applied to the RR basis):");
    for (int r = 0; r < K; ++r) printf("  x^(%d) y^(%d)\n", basis[r].i, basis[r].j);
    if (check_distance) {
        int d = exhaustive_minimum_distance();
        printf("Exact minimum distance (exhaustive 8^6 search): d=%d\n", d);
        printf("Exact unique-decoding radius: %d\n", (d-1)/2);
    }

    rng_state = (unsigned)seed + 1u;
    int successes = 0;
    for (int trial = 1; trial <= trials; ++trial) {
        gf msg[K], codeword[N], received[N], corrected[N];
        for (int i = 0; i < K; ++i) msg[i] = (gf)(rnd() & 7u);
        encode(msg, codeword);
        memcpy(received, codeword, sizeof received);
        int used[N] = {0};
        for (int i = 0; i < errors; ++i) {
            int p; do { p = (int)(rnd() % N); } while (used[p]);
            used[p] = 1;
            gf e; do { e = (gf)(1u + (rnd() % 7u)); } while (!e);
            received[p] ^= e;
        }
        int decoded_weight = -1;
        int ok = decode(received, corrected, &decoded_weight);
        if (ok && same(corrected, codeword)) ++successes;
        if (trials == 1) {
            printf("message:"); for (int i=0;i<K;++i) printf(" %u", msg[i]); puts("");
            printf("injected errors: %d\n", errors);
            printf("decoder status: %s\n", ok ? "PASS" : "FAIL");
            if (ok) printf("located error weight: %d\n", decoded_weight);
            printf("exact original codeword recovered: %s\n", (ok && same(corrected,codeword)) ? "YES" : "NO");
        }
    }
    if (trials > 1) printf("trials=%d, errors=%d, exact recoveries=%d/%d\n", trials, errors, successes, trials);
    return successes == trials ? 0 : 1;
}
