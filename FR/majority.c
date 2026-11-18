#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * Feng-Rao majority voting demo for the Hermitian curve over GF(4):
 *     y^2 + y = x^3
 *
 * The affine curve has 8 rational points, genus 1, and H(P_inf)=<2,3>.
 * Basis functions, in increasing pole order, are x^a y^b (b=0 or 1):
 *   1, x, y, x^2, xy, x^3, x^2 y, x^4, ...
 *
 * This program starts with the syndromes s(f) known for pole orders <= 5,
 * uses Feng-Rao majority voting to extend the missing syndromes, and then
 * locates a single error using the already-known syndromes s(1), s(x), s(y).
 *
 * GF(4) representation: 0,1,a,a+1, with a^2=a+1. Addition is XOR.
 */

#define MAXB 12
#define MAXP 8

static unsigned char gf_mul(unsigned char a, unsigned char b) {
    unsigned char r = 0;
    while (b) {
        if (b & 1) r ^= a;
        b >>= 1;
        a <<= 1;
        if (a & 4) a ^= 7; /* z^2+z+1 */
    }
    return r & 3;
}
static unsigned char gf_pow(unsigned char a, int n) {
    unsigned char r = 1;
    while (n--) r = gf_mul(r, a);
    return r;
}
static unsigned char gf_inv(unsigned char a) {
    if (!a) return 0;
    return gf_pow(a, 2);
}
static unsigned char gf_div(unsigned char a, unsigned char b) {
    return b ? gf_mul(a, gf_inv(b)) : 0;
}
static void gf_print(unsigned char a) {
    static const char *s[] = {"0", "1", "a", "a+1"};
    printf("%s", s[a & 3]);
}

typedef struct { int a, b, rho; } Basis;
static Basis B[MAXB];
static int NB;
static int points_x[MAXP], points_y[MAXP], NP;
static unsigned char syn[MAXB];

static void make_basis(int count) {
    int w;
    NB = 0;
    for (w = 0; NB < count; ++w) {
        int b;
        for (b = 0; b <= 1; ++b) {
            int rem = w - 3*b;
            if (rem >= 0 && rem % 2 == 0) {
                B[NB].a = rem / 2;
                B[NB].b = b;
                B[NB].rho = w;
                ++NB;
                break;
            }
        }
    }
}
static int basis_index_by_weight(int rho) {
    int i;
    for (i = 0; i < NB; ++i) if (B[i].rho == rho) return i;
    return -1;
}
static unsigned char eval_basis(int k, unsigned char x, unsigned char y) {
    return gf_mul(gf_pow(x, B[k].a), B[k].b ? y : 1);
}
static void enumerate_points(void) {
    int x, y;
    NP = 0;
    for (x = 0; x < 4; ++x) for (y = 0; y < 4; ++y) {
        unsigned char lhs = gf_mul((unsigned char)y, (unsigned char)y) ^ (unsigned char)y;
        unsigned char rhs = gf_pow((unsigned char)x, 3);
        if (lhs == rhs) {
            points_x[NP] = x; points_y[NP] = y; ++NP;
        }
    }
}
static unsigned char syndrome_of(int k, const unsigned char *received) {
    unsigned char s = 0;
    int p;
    for (p = 0; p < NP; ++p)
        s ^= gf_mul(received[p], eval_basis(k, (unsigned char)points_x[p], (unsigned char)points_y[p]));
    return s;
}

/* For basis functions f_r=x^a y^b and f_c=x^u y^v:
 * if b+v<=1, product is exactly the basis function of weight rho_r+rho_c.
 * if b=v=1, y^2=x^3+y, so product = leading term + lower term
 * and s(f_r f_c)=s_{rho_r+rho_c}+s_{rho_r+rho_c-3}.
 */
static unsigned char matrix_entry(int r, int c) {
    int w = B[r].rho + B[c].rho;
    int idx = basis_index_by_weight(w);
    unsigned char v;
    if (idx < 0) return 0;
    v = syn[idx];
    if (B[r].b && B[c].b) {
        int lo = basis_index_by_weight(w - 3);
        if (lo >= 0) v ^= syn[lo];
    }
    return v;
}

static int rank_matrix(int rows, int cols, int row0, int col0) {
    unsigned char a[MAXB][MAXB];
    int r, c, rank = 0;
    memset(a, 0, sizeof(a));
    for (r = 0; r < rows; ++r)
        for (c = 0; c < cols; ++c)
            a[r][c] = matrix_entry(row0 + r, col0 + c);
    for (c = 0; c < cols && rank < rows; ++c) {
        int p;
        for (p = rank; p < rows && a[p][c] == 0; ++p) {}
        if (p == rows) continue;
        if (p != rank) {
            int t;
            for (t = c; t < cols; ++t) {
                unsigned char z = a[p][t]; a[p][t] = a[rank][t]; a[rank][t] = z;
            }
        }
        {
            unsigned char inv = gf_inv(a[rank][c]);
            int t;
            for (t = c; t < cols; ++t) a[rank][t] = gf_mul(a[rank][t], inv);
        }
        for (p = rank + 1; p < rows; ++p) if (a[p][c]) {
            unsigned char q = a[p][c];
            int t;
            for (t = c; t < cols; ++t) a[p][t] ^= gf_mul(q, a[rank][t]);
        }
        ++rank;
    }
    return rank;
}

/* Solve sum_r alpha[r]*S(r,c)=S(i,c), c=0..j-1.
 * Free variables are set to zero. Candidate rank conditions guarantee
 * that the resulting predicted bottom-right entry is independent of choice.
 */
static int row_relation(int i, int j, unsigned char *alpha) {
    unsigned char a[MAXB][MAXB+1];
    int eq = j, vars = i, r, c, pivrow = 0;
    int pivot_col[MAXB];
    memset(a, 0, sizeof(a));
    memset(alpha, 0, MAXB);
    for (c = 0; c < eq; ++c) {
        for (r = 0; r < vars; ++r) a[c][r] = matrix_entry(r, c);
        a[c][vars] = matrix_entry(i, c);
    }
    for (r = 0; r < vars; ++r) pivot_col[r] = -1;
    for (c = 0; c < vars && pivrow < eq; ++c) {
        int p;
        for (p = pivrow; p < eq && a[p][c] == 0; ++p) {}
        if (p == eq) continue;
        if (p != pivrow) {
            int t;
            for (t = c; t <= vars; ++t) {
                unsigned char z = a[p][t]; a[p][t] = a[pivrow][t]; a[pivrow][t] = z;
            }
        }
        {
            unsigned char inv = gf_inv(a[pivrow][c]);
            int t;
            for (t = c; t <= vars; ++t) a[pivrow][t] = gf_mul(a[pivrow][t], inv);
        }
        for (p = 0; p < eq; ++p) if (p != pivrow && a[p][c]) {
            unsigned char q = a[p][c];
            int t;
            for (t = c; t <= vars; ++t) a[p][t] ^= gf_mul(q, a[pivrow][t]);
        }
        pivot_col[pivrow] = c;
        ++pivrow;
    }
    for (r = 0; r < eq; ++r) {
        int allzero = 1;
        for (c = 0; c < vars; ++c) if (a[r][c]) { allzero = 0; break; }
        if (allzero && a[r][vars]) return 0;
    }
    for (r = 0; r < pivrow; ++r) alpha[pivot_col[r]] = a[r][vars];
    return 1;
}

static int majority_vote(int target_index) {
    int i, j, votes[4] = {0,0,0,0}, candidates = 0, winner = -1;
    int target = B[target_index].rho;
    for (i = 1; i < target_index; ++i) for (j = 1; j < target_index; ++j) {
        unsigned char alpha[MAXB], predicted, vote;
        int r0, r1, r2, k;
        if (B[i].rho + B[j].rho != target) continue;
        r0 = rank_matrix(i, j, 0, 0);       /* S(i-1,j-1) */
        r1 = rank_matrix(i, j+1, 0, 0);     /* S(i-1,j) */
        r2 = rank_matrix(i+1, j, 0, 0);     /* S(i,j-1) */
        if (!(r0 == r1 && r1 == r2)) continue;
        if (!row_relation(i, j, alpha)) continue;
        predicted = 0;
        for (k = 0; k < i; ++k)
            predicted ^= gf_mul(alpha[k], matrix_entry(k, j));
        vote = predicted;
        if (B[i].b && B[j].b) {
            int lo = basis_index_by_weight(target - 3);
            if (lo >= 0) vote ^= syn[lo];
        }
        ++votes[vote];
        ++candidates;
        printf("  candidate (i=%d,j=%d), predicted s_ij=", i, j);
        gf_print(predicted);
        printf(", vote for s_%d=", target_index);
        gf_print(vote);
        printf("\n");
    }
    if (!candidates) {
        printf("  no candidates for pole order %d\n", target);
        return 0;
    }
    /* Require a strict majority, not merely a unique plurality. */
    {
        int maxv = 0, ties = 0;
        for (i = 0; i < 4; ++i) if (votes[i] > maxv) maxv = votes[i];
        for (i = 0; i < 4; ++i) if (votes[i] == maxv) {
            ++ties;
            winner = i;
        }
        if (ties != 1 || 2 * maxv <= candidates) {
            printf("  no strict majority (%d candidates); cannot extend safely\n", candidates);
            return 0;
        }
    }
    printf("  votes:");
    for (i = 0; i < 4; ++i) if (votes[i]) { printf(" "); gf_print((unsigned char)i); printf("=%d", votes[i]); }
    printf(" -> majority "); gf_print((unsigned char)winner); printf("\n");
    syn[target_index] = (unsigned char)winner;
    return 1;
}

int main(void) {
    unsigned char received[MAXP] = {0};
    int i, p, target;
    make_basis(8);
    enumerate_points();
    printf("Hermitian curve y^2+y=x^3 over GF(4)\n");
    printf("affine rational points: %d (expected 8)\n", NP);
    printf("basis:");
    for (i = 0; i < NB; ++i) printf(" %d", B[i].rho);
    printf(" (pole orders)\n\n");
    if (NP != 8) return 1;

    /* Inject one error: value a at point (x,y)=(1,a). */
    for (p = 0; p < NP; ++p)
        if (points_x[p] == 1 && points_y[p] == 2) break;
    if (p == NP) return 1;
    received[p] = 2;
    printf("Injected test error: point (1,a), value a.\n\n");

    /* Known syndromes for all basis functions with pole order <= 5. */
    for (i = 0; i < NB && B[i].rho <= 5; ++i) syn[i] = syndrome_of(i, received);
    printf("Known syndromes (rho <= 5):\n");
    for (i = 0; i < NB && B[i].rho <= 5; ++i) {
        printf("  s_%d = ", i); gf_print(syn[i]); printf("\n");
    }
    printf("\nMajority voting for unknown syndromes:\n");
    for (target = 0; target < NB; ++target) if (B[target].rho > 5) {
        printf("pole order %d (basis index %d):\n", B[target].rho, target);
        if (!majority_vote(target)) {
            printf("FAILED: no unique majority.\n");
            return 2;
        }
        printf("  recovered s_%d = ", target); gf_print(syn[target]);
        printf("\n");
    }

    printf("\nCheck against directly computed syndromes (test only):\n");
    for (i = 0; i < NB; ++i) {
        unsigned char actual = syndrome_of(i, received);
        printf("  rho=%d recovered=", B[i].rho); gf_print(syn[i]);
        printf(" actual="); gf_print(actual);
        printf(" %s\n", syn[i] == actual ? "OK" : "MISMATCH");
        if (syn[i] != actual) return 3;
    }

    /* One-error location from s(1), s(x), s(y). */
    if (syn[0] == 0) {
        printf("No error detected by s(1).\n");
        return 0;
    }
    {
        unsigned char xhat = gf_div(syn[1], syn[0]);
        unsigned char yhat = gf_div(syn[2], syn[0]);
        printf("\nSingle-error location from known syndromes:\n  x = "); gf_print(xhat);
        printf(", y = "); gf_print(yhat);
        printf(", error value = "); gf_print(syn[0]); printf("\n");
        for (p = 0; p < NP; ++p)
            if (points_x[p] == xhat && points_y[p] == yhat) break;
        if (p == NP) {
            printf("ERROR: recovered location is not on the affine point list.\n");
            return 4;
        }
        printf("Location check: %s\n", (xhat == 1 && yhat == 2) ? "OK" : "unexpected point");
    }
    printf("\nAll checks passed.\n");
    return 0;
}
