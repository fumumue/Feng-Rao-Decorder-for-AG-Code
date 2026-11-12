/*
 * BBGS E2 basic syndrome decoder -- minimal working baseline.
 *
 * This program uses all affine BBGS E2 points with x != 0 over GF(32)
 * (or GF(8) with --m 1).  The parity checks are the evaluations of
 * 1, x, y.  The code is C = ker(H), where H has these three rows.
 *
 * Since every support point has a distinct pair (x,y), a single error
 * e at P=(x,y) has syndrome (e,e*x,e*y), which identifies P and e.
 * This is an exact one-error syndrome decoder, not yet a multi-error
 * Feng-Rao decoder.  A random codeword is generated from ker(H), then
 * one error is injected, decoded, and compared with the original.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -Werror -o bbgs_basic_working bbgs_basic_working.c
 * Run:   ./bbgs_basic_working --m 2 --seed 7
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1024

typedef struct { int x, y; } Point;

static int Q, J, K, IRR;
static Point pts[MAXN];
static int npts;
static unsigned rng = 1;

static unsigned rnd_u32(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

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

static int gf_inv(int a) {
    return a ? gf_pow(a, Q - 2) : 0;
}

static int trace_p2(int z, int degree) {
    int s = 0;
    for (int i = 0; i < degree; ++i) {
        s ^= z;
        z = gf_mul(z, z);
    }
    return s;
}

static int init_field(int m) {
    if (m == 1) {
        Q = 8;
        IRR = 0x0b; /* X^3 + X + 1 */
    } else if (m == 2) {
        Q = 32;
        IRR = 0x25; /* X^5 + X^2 + 1 */
    } else {
        return 0;
    }
    J = (m & 1) ? m : m + 1;
    K = 2 * m + 1 - J;
    return 1;
}

/* BBGS tower equation in characteristic two:
 * Tr_J(y / x^(2^K)) + Tr_K(y^(2^J) / x) = 1.
 */
static int is_bbgs_e2_point(int x, int y) {
    int xpow = gf_pow(x, 1 << K);
    int lhs1 = trace_p2(gf_mul(y, gf_inv(xpow)), J);
    int ypow = gf_pow(y, 1 << J);
    int lhs2 = trace_p2(gf_mul(ypow, gf_inv(x)), K);
    return (lhs1 ^ lhs2) == 1;
}

static void enumerate_points(void) {
    npts = 0;
    for (int x = 1; x < Q; ++x) {
        for (int y = 0; y < Q; ++y) {
            if (is_bbgs_e2_point(x, y)) {
                if (npts >= MAXN) {
                    fprintf(stderr, "too many support points\n");
                    exit(2);
                }
                pts[npts++] = (Point){x, y};
            }
        }
    }
}

/* H has rows 1, x, y. */
static void syndrome(const int *word, int s[3]) {
    s[0] = s[1] = s[2] = 0;
    for (int i = 0; i < npts; ++i) {
        s[0] ^= word[i];
        s[1] ^= gf_mul(pts[i].x, word[i]);
        s[2] ^= gf_mul(pts[i].y, word[i]);
    }
}

/* RREF of a 3 x n matrix; returns rank and pivot-column indices. */
static int rref_h(int *a, int piv[3]) {
    int rank = 0;
    for (int col = 0; col < npts && rank < 3; ++col) {
        int pr = -1;
        for (int r = rank; r < 3; ++r) {
            if (a[r * npts + col]) {
                pr = r;
                break;
            }
        }
        if (pr < 0) continue;
        if (pr != rank) {
            for (int c = 0; c < npts; ++c) {
                int t = a[rank * npts + c];
                a[rank * npts + c] = a[pr * npts + c];
                a[pr * npts + c] = t;
            }
        }
        int inv = gf_inv(a[rank * npts + col]);
        for (int c = 0; c < npts; ++c)
            a[rank * npts + c] = gf_mul(a[rank * npts + c], inv);

        for (int r = 0; r < 3; ++r) {
            if (r == rank) continue;
            int f = a[r * npts + col];
            if (!f) continue;
            for (int c = 0; c < npts; ++c)
                a[r * npts + c] ^= gf_mul(f, a[rank * npts + c]);
        }
        piv[rank++] = col;
    }
    return rank;
}

/* Generate a uniformly structured random member of ker(H):
 * choose free coordinates randomly, then solve pivot coordinates.
 */
static int make_codeword(int *word, int *dimension) {
    int a[3 * MAXN] = {0};
    int piv[3] = {-1, -1, -1};
    for (int i = 0; i < npts; ++i) {
        a[i] = 1;
        a[npts + i] = pts[i].x;
        a[2 * npts + i] = pts[i].y;
    }

    int rank = rref_h(a, piv);
    if (rank != 3) return 0;
    *dimension = npts - rank;

    int is_pivot[MAXN] = {0};
    for (int r = 0; r < rank; ++r) is_pivot[piv[r]] = 1;
    for (int i = 0; i < npts; ++i)
        word[i] = is_pivot[i] ? 0 : (int)(rnd_u32() % (unsigned)Q);

    for (int r = 0; r < rank; ++r) {
        int value = 0;
        for (int c = 0; c < npts; ++c) {
            if (!is_pivot[c])
                value ^= gf_mul(a[r * npts + c], word[c]);
        }
        word[piv[r]] = value;
    }

    int s[3];
    syndrome(word, s);
    return (s[0] == 0 && s[1] == 0 && s[2] == 0);
}

/* Basic one-error syndrome decoding.
 * For one nonzero error e at P=(x,y), s=(e,e*x,e*y).
 */
static int decode_one_error(const int *received, int *corrected,
                            int *error_position, int *error_value) {
    int s[3];
    syndrome(received, s);
    memcpy(corrected, received, (size_t)npts * sizeof(int));

    if (s[0] == 0) {
        if (s[1] == 0 && s[2] == 0) {
            *error_position = -1;
            *error_value = 0;
            return 1; /* no error */
        }
        return 0;
    }

    int e = s[0];
    int found = -1;
    for (int i = 0; i < npts; ++i) {
        if (gf_mul(e, pts[i].x) == s[1] &&
            gf_mul(e, pts[i].y) == s[2]) {
            if (found >= 0) return 0; /* ambiguous */
            found = i;
        }
    }
    if (found < 0) return 0;

    corrected[found] ^= e;
    *error_position = found;
    *error_value = e;

    int check[3];
    syndrome(corrected, check);
    return check[0] == 0 && check[1] == 0 && check[2] == 0;
}

static void usage(const char *program) {
    printf("Usage: %s [--m 1|2] [--seed N]\n", program);
    puts("  --m 1   BBGS E2 over GF(8)");
    puts("  --m 2   BBGS E2 over GF(32) (default)");
    puts("  --seed N  random seed");
    puts("This baseline corrects exactly one nonzero error.");
}

int main(int argc, char **argv) {
    int m = 2;
    unsigned seed = 7;

    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
            usage(argv[0]);
            return 0;
        }
        if (i + 1 >= argc) {
            fprintf(stderr, "missing value for %s\n", argv[i]);
            return 2;
        }
        const char *option = argv[i];
        const char *value = argv[++i];
        if (!strcmp(option, "--m")) {
            m = atoi(value);
        } else if (!strcmp(option, "--seed")) {
            seed = (unsigned)strtoul(value, NULL, 10);
        } else {
            fprintf(stderr, "unknown option: %s\n", option);
            return 2;
        }
    }

    if (!init_field(m)) {
        usage(argv[0]);
        return 2;
    }
    rng = seed ? seed : 1;
    enumerate_points();
    if (npts < 4) {
        fprintf(stderr, "not enough BBGS support points: %d\n", npts);
        return 2;
    }

    int original[MAXN] = {0};
    int received[MAXN] = {0};
    int corrected[MAXN] = {0};
    int dimension = 0;

    if (!make_codeword(original, &dimension)) {
        fprintf(stderr, "failed to construct a codeword in ker(H)\n");
        return 1;
    }
    memcpy(received, original, (size_t)npts * sizeof(int));

    int error_pos = (int)(rnd_u32() % (unsigned)npts);
    int error_value = 1 + (int)(rnd_u32() % (unsigned)(Q - 1));
    received[error_pos] ^= error_value;

    int decoded_pos = -1, decoded_value = 0;
    int ok = decode_one_error(received, corrected,
                              &decoded_pos, &decoded_value);
    int exact = ok;
    if (ok) {
        for (int i = 0; i < npts; ++i) {
            if (corrected[i] != original[i]) {
                exact = 0;
                break;
            }
        }
    }

    printf("BBGS E2 one-error basic decoder\n");
    printf("Field: GF(2^%d), q=%d, j=%d, k=%d\n", 2 * m + 1, Q, J, K);
    printf("Affine support size (x != 0): %d\n", npts);
    printf("Parity checks: 1, x, y; rank = 3\n");
    printf("Code parameters: length n=%d, dimension k=%d (constructed ker(H))\n",
           npts, dimension);
    printf("Injected error: position=%d, point=(%d,%d), value=%d\n",
           error_pos, pts[error_pos].x, pts[error_pos].y, error_value);
    printf("Decoded error:  position=%d, value=%d\n",
           decoded_pos, decoded_value);
    puts(exact ? "PASS: recovered the original codeword exactly."
               : "FAIL: decoding did not recover the original codeword.");
    return exact ? 0 : 1;
}
