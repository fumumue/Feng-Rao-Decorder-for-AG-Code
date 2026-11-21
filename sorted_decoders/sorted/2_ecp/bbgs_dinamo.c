/*
 * BBGS E2 experimental basic syndrome decoder
 * Dynamic-memory version for larger monomial spaces.
 *
 * Build:
 *   gcc -O2 -std=c11 -Wall -Wextra -o bbgs_decoder bbgs_decoder.c
 *
 * Example:
 *   ./bbgs_decoder --m 2 --u 49 --v 47 --errors 145 --seed 1
 *
 * This remains an experimental affine evaluation-code decoder.
 * It is NOT a proof of RR/Feng-Rao decoding.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>

#define MAXN 1024
#define MAX_DEG 96

typedef struct { int x, y; } Point;
typedef struct { int a, b; } Mon;

static int Q, J, K, IRR;
static Point pts[MAXN];
static int npts;
static int verbose = 0;
static uint32_t rng = 1;

static void *xcalloc(size_t n, size_t size) {
    if (size && n > SIZE_MAX / size) return NULL;
    return calloc(n, size);
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
static int gf_inv(int a) { return a ? gf_pow(a, Q - 2) : 0; }

static int trace2(int z, int r) {
    int s = 0;
    for (int i = 0; i < r; ++i) {
        s ^= z;
        z = gf_mul(z, z);
    }
    return s;
}

static int init_field(int m) {
    if (m == 1) { Q = 8; IRR = 0x0b; }
    else if (m == 2) { Q = 32; IRR = 0x25; }
    else return 0;
    J = (m % 2) ? m : m + 1;
    K = 2 * m + 1 - J;
    return 1;
}

static int bbgs_equation(int x, int y) {
    int xpk = gf_pow(x, 1 << K);
    int term1 = trace2(gf_mul(y, gf_inv(xpk)), J);
    int ypj = gf_pow(y, 1 << J);
    int term2 = trace2(gf_mul(ypj, gf_inv(x)), K);
    return (term1 ^ term2) == 1;
}

static void enumerate_points(void) {
    npts = 0;
    for (int x = 1; x < Q; ++x)
        for (int y = 0; y < Q; ++y)
            if (bbgs_equation(x, y) && npts < MAXN)
                pts[npts++] = (Point){x, y};
}

static int monomial_count(int d) {
    if (d < 0) return 0;
    return (d + 1) * (d + 2) / 2;
}

static Mon *make_monomials(int d, int *count) {
    int n = monomial_count(d);
    Mon *out = (Mon *)xcalloc((size_t)n, sizeof(Mon));
    if (!out) return NULL;
    int z = 0;
    for (int a = 0; a <= d; ++a)
        for (int b = 0; a + b <= d; ++b)
            out[z++] = (Mon){a, b};
    *count = n;
    return out;
}

static int eval_mon(Mon m, Point p) {
    return gf_mul(gf_pow(p.x, m.a), gf_pow(p.y, m.b));
}

/* RREF over GF(2^n). A is row-major and is modified in place. */
static int rref(int *A, int rows, int cols, int *piv) {
    int r = 0;
    for (int c = 0; c < cols && r < rows; ++c) {
        int pr = -1;
        for (int i = r; i < rows; ++i)
            if (A[(size_t)i * cols + c]) { pr = i; break; }
        if (pr < 0) continue;

        if (pr != r) {
            for (int j = 0; j < cols; ++j) {
                int t = A[(size_t)r * cols + j];
                A[(size_t)r * cols + j] = A[(size_t)pr * cols + j];
                A[(size_t)pr * cols + j] = t;
            }
        }

        int iv = gf_inv(A[(size_t)r * cols + c]);
        for (int j = 0; j < cols; ++j)
            A[(size_t)r * cols + j] =
                gf_mul(iv, A[(size_t)r * cols + j]);

        for (int i = 0; i < rows; ++i) if (i != r) {
            int f = A[(size_t)i * cols + c];
            if (f)
                for (int j = 0; j < cols; ++j)
                    A[(size_t)i * cols + j] ^=
                        gf_mul(f, A[(size_t)r * cols + j]);
        }
        piv[r++] = c;
    }
    return r;
}

/* Returns nullity. Basis is row-major: nullity vectors, each of length cols. */
static int nullspace(const int *A, int rows, int cols, int **basis_out) {
    *basis_out = NULL;
    int *R = (int *)xcalloc((size_t)rows * cols, sizeof(int));
    int *piv = (int *)xcalloc((size_t)(rows < cols ? rows : cols), sizeof(int));
    int *is_piv = (int *)xcalloc((size_t)cols, sizeof(int));
    if (!R || !piv || !is_piv) {
        free(R); free(piv); free(is_piv);
        return -1;
    }
    memcpy(R, A, sizeof(int) * (size_t)rows * cols);
    int rank = rref(R, rows, cols, piv);
    for (int i = 0; i < rank; ++i) is_piv[piv[i]] = 1;

    int nullity = cols - rank;
    int *basis = (int *)xcalloc((size_t)nullity * cols, sizeof(int));
    if (nullity && !basis) {
        free(R); free(piv); free(is_piv);
        return -1;
    }

    int z = 0;
    for (int f = 0; f < cols; ++f) if (!is_piv[f]) {
        int *v = basis + (size_t)z * cols;
        v[f] = 1;
        for (int i = 0; i < rank; ++i)
            v[piv[i]] = R[(size_t)i * cols + f];
        ++z;
    }

    free(R); free(piv); free(is_piv);
    *basis_out = basis;
    return nullity;
}

static int solve_unique(const int *A, int rows, int cols,
                        const int *rhs, int *x) {
    size_t width = (size_t)cols + 1;
    int *aug = (int *)xcalloc((size_t)rows * width, sizeof(int));
    int *piv = (int *)xcalloc(width, sizeof(int));
    if (!aug || !piv) { free(aug); free(piv); return 0; }

    for (int i = 0; i < rows; ++i) {
        memcpy(aug + (size_t)i * width,
               A + (size_t)i * cols, sizeof(int) * (size_t)cols);
        aug[(size_t)i * width + cols] = rhs[i];
    }

    int rank = rref(aug, rows, cols + 1, piv);
    for (int i = 0; i < rank; ++i) {
        if (piv[i] == cols) {
            free(aug); free(piv);
            return 0; /* inconsistent */
        }
    }

    int coefficient_rank = 0;
    for (int i = 0; i < rank; ++i)
        if (piv[i] < cols) ++coefficient_rank;

    if (coefficient_rank < cols) {
        free(aug); free(piv);
        return 0; /* not unique */
    }

    memset(x, 0, sizeof(int) * (size_t)cols);
    for (int i = 0; i < rank; ++i)
        if (piv[i] < cols)
            x[piv[i]] = aug[(size_t)i * width + cols];

    free(aug); free(piv);
    return 1;
}

static uint32_t rnd(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

static int mon_index(const Mon *H, int nh, int a, int b) {
    for (int h = 0; h < nh; ++h)
        if (H[h].a == a && H[h].b == b) return h;
    return -1;
}

static void print_poly(const Mon *mon, const int *c, int n) {
    int first = 1;
    for (int i = n - 1; i >= 0; --i) {
        if (!c[i]) continue;
        if (!first) printf(" + ");
        first = 0;
        printf("%d", c[i]);
        if (mon[i].a) printf("*x^%d", mon[i].a);
        if (mon[i].b) printf("*y^%d", mon[i].b);
    }
    if (first) printf("0");
}

static int locator_zeros(const Mon *Amon, int na, const int *c, int *zeros) {
    int nz = 0;
    for (int p = 0; p < npts; ++p) {
        int val = 0;
        for (int a = 0; a < na; ++a)
            if (c[a])
                val ^= gf_mul(c[a], eval_mon(Amon[a], pts[p]));
        if (!val) zeros[nz++] = p;
    }
    return nz;
}

/*
 * Build the syndrome matrix for A-space degree d and B-space degree v.
 * Search d upward, but only while dim(A_d) <= dim(B_v).
 */
static int build_locator(const int *syn, const Mon *Hmon, int nh,
                         int dmax, int v,
                         int **loc_out, int *nk_out, int *na_out,
                         Mon **Aout_out) {
    int nb = 0;
    Mon *Bmon = make_monomials(v, &nb);
    if (!Bmon) return -1;

    for (int d = 0; d <= dmax; ++d) {
        int na = 0;
        Mon *Amon = make_monomials(d, &na);
        if (!Amon) { free(Bmon); return -1; }
        if (na > nb) { free(Amon); break; }

        int *MM = (int *)xcalloc((size_t)nb * na, sizeof(int));
        if (!MM) { free(Amon); free(Bmon); return -1; }

        int bad = 0;
        for (int i = 0; i < na && !bad; ++i)
            for (int j = 0; j < nb; ++j) {
                int idx = mon_index(Hmon, nh,
                                    Amon[i].a + Bmon[j].a,
                                    Amon[i].b + Bmon[j].b);
                if (idx < 0) { bad = 1; break; }
                MM[(size_t)j * na + i] = syn[idx];
            }

        int *basis = NULL;
        int nk = bad ? -1 : nullspace(MM, nb, na, &basis);
        free(MM);
        free(Bmon);

        if (nk < 0) { free(Amon); free(basis); return -1; }
        if (nk > 0) {
            *loc_out = basis;
            *nk_out = nk;
            *na_out = na;
            *Aout_out = Amon;
            return d;
        }
        free(basis);
        free(Amon);

        Bmon = make_monomials(v, &nb);
        if (!Bmon) return -1;
    }
    free(Bmon);
    return -1;
}

static int decode(const int *received, int u, int v, int *corrected,
                  int *candidate_count, int *kernel_dim, int *check_rank) {
    int na = 0, nb = 0, nh = 0;
    Mon *Amon = make_monomials(u, &na);
    Mon *Bmon = make_monomials(v, &nb);
    Mon *Hmon = make_monomials(u + v, &nh);
    int *H = NULL, *syn = NULL, *MM = NULL, *ker = NULL;
    int *candidates = NULL, *AZ = NULL, *rhs = NULL, *err = NULL;
    int success = 0;

    if (!Amon || !Bmon || !Hmon) goto cleanup;

    H = (int *)xcalloc((size_t)nh * npts, sizeof(int));
    syn = (int *)xcalloc((size_t)nh, sizeof(int));
    if (!H || !syn) goto cleanup;

    for (int h = 0; h < nh; ++h)
        for (int p = 0; p < npts; ++p)
            H[(size_t)h * npts + p] = eval_mon(Hmon[h], pts[p]);

    for (int h = 0; h < nh; ++h)
        for (int p = 0; p < npts; ++p)
            syn[h] ^= gf_mul(H[(size_t)h * npts + p], received[p]);

    if (verbose) {
        int *loc = NULL, nkl = 0, nal = 0;
        Mon *Aloc = NULL;
        int d = build_locator(syn, Hmon, nh, u, v,
                              &loc, &nkl, &nal, &Aloc);
        if (d < 0) {
            puts("locator: not found");
        } else {
            printf("locator: minimum degree d=%d, kernel dimension=%d\n", d, nkl);
            for (int z = 0; z < nkl; ++z) {
                int *zeros = (int *)xcalloc((size_t)npts, sizeof(int));
                printf("  L%d(x,y) = ", z + 1);
                print_poly(Aloc, loc + (size_t)z * nal, nal);
                int nz = zeros ? locator_zeros(Aloc, nal,
                                      loc + (size_t)z * nal, zeros) : -1;
                printf("\n    zeros on affine support = %d\n", nz);
                free(zeros);
            }
        }
        free(loc);
        free(Aloc);
    }

    MM = (int *)xcalloc((size_t)nb * na, sizeof(int));
    if (!MM) goto cleanup;
    for (int i = 0; i < na; ++i)
        for (int j = 0; j < nb; ++j) {
            int idx = mon_index(Hmon, nh,
                               Amon[i].a + Bmon[j].a,
                               Amon[i].b + Bmon[j].b);
            if (idx < 0) goto cleanup;
            MM[(size_t)j * na + i] = syn[idx];
        }

    int nk = nullspace(MM, nb, na, &ker);
    if (nk < 0) goto cleanup;
    *kernel_dim = nk;

    candidates = (int *)xcalloc((size_t)npts, sizeof(int));
    if (!candidates) goto cleanup;
    int nc = 0;
    for (int p = 0; p < npts; ++p) {
        int common = 1;
        for (int z = 0; z < nk && common; ++z) {
            int val = 0;
            for (int a = 0; a < na; ++a)
                if (ker[(size_t)z * na + a])
                    val ^= gf_mul(ker[(size_t)z * na + a],
                                  eval_mon(Amon[a], pts[p]));
            if (val) common = 0;
        }
        if (common) candidates[nc++] = p;
    }
    *candidate_count = nc;

    if (nc <= 0 || nc > nh) goto cleanup;

    AZ = (int *)xcalloc((size_t)nh * nc, sizeof(int));
    rhs = (int *)xcalloc((size_t)nh, sizeof(int));
    err = (int *)xcalloc((size_t)nc, sizeof(int));
    if (!AZ || !rhs || !err) goto cleanup;

    for (int h = 0; h < nh; ++h) {
        rhs[h] = syn[h];
        for (int z = 0; z < nc; ++z)
            AZ[(size_t)h * nc + z] =
                H[(size_t)h * npts + candidates[z]];
    }

    if (!solve_unique(AZ, nh, nc, rhs, err)) goto cleanup;

    memcpy(corrected, received, sizeof(int) * (size_t)npts);
    for (int z = 0; z < nc; ++z)
        corrected[candidates[z]] ^= err[z];

    for (int h = 0; h < nh; ++h) {
        int s = 0;
        for (int p = 0; p < npts; ++p)
            s ^= gf_mul(H[(size_t)h * npts + p], corrected[p]);
        if (s) goto cleanup;
    }

    {
        int *tmp = (int *)xcalloc((size_t)nh * npts, sizeof(int));
        int *piv = (int *)xcalloc((size_t)(nh < npts ? nh : npts), sizeof(int));
        if (tmp && piv) {
            memcpy(tmp, H, sizeof(int) * (size_t)nh * npts);
            *check_rank = rref(tmp, nh, npts, piv);
        } else {
            *check_rank = -1;
        }
        free(tmp);
        free(piv);
    }
    success = 1;

cleanup:
    free(Amon); free(Bmon); free(Hmon);
    free(H); free(syn); free(MM); free(ker);
    free(candidates); free(AZ); free(rhs); free(err);
    return success;
}


/*
 * Automatic parameter search.
 * The search is balanced: for each total degree D, test
 * (u,v)=(floor(D/2), ceil(D/2)). This avoids an exhaustive O(D)
 * scan over every split at each D.
 *
 * The requested error count is used as a support-size criterion:
 * accept only if decoding succeeds and the common-zero candidate
 * count equals the known injected error count.
 */
static int find_auto_parameters(const int *received, int expected_errors,
                                int *corrected, int *u_out, int *v_out,
                                int *candidate_count, int *kernel_dim,
                                int *check_rank) {
    int saved_verbose = verbose;
    verbose = 0;

    for (int total = 0; total <= MAX_DEG; ++total) {
        int u = total / 2;
        int v = total - u;

        if (monomial_count(u) > 5000 ||
            monomial_count(v) > 5000 ||
            monomial_count(total) > 5000)
            continue;

        int nc = 0, nk = 0, rk = -1;
        int *trial_corrected =
            (int *)xcalloc((size_t)npts, sizeof(int));
        if (!trial_corrected) {
            verbose = saved_verbose;
            return 0;
        }

        int ok = decode(received, u, v, trial_corrected,
                        &nc, &nk, &rk);

        if (ok && nc == expected_errors) {
            memcpy(corrected, trial_corrected,
                   sizeof(int) * (size_t)npts);
            *u_out = u;
            *v_out = v;
            *candidate_count = nc;
            *kernel_dim = nk;
            *check_rank = rk;
            free(trial_corrected);
            verbose = saved_verbose;
            return 1;
        }
        free(trial_corrected);
    }

    verbose = saved_verbose;
    return 0;
}

static void usage(const char *p) {
    printf("Usage: %s [--m 1|2] [--u N --v N] [--errors T] [--seed N] [--trials N]\n", p);
    puts("If both --u and --v are omitted, balanced u,v are searched automatically.");
    puts("GF(2^(2m+1)): m=1 gives GF(8), m=2 gives GF(32).");
    puts("Supported here: u+v <= 96; memory use grows with the monomial counts.");
}

int main(int argc, char **argv) {
    int m = 2, u = -1, v = -1, errors = 145, seed = 1, trials = 1;
    int have_u = 0, have_v = 0;

    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
            usage(argv[0]); return 0;
        }
        if (i + 1 >= argc) {
            fprintf(stderr, "missing value for %s\n", argv[i]); return 2;
        }
        char *name = argv[i];
        char *end = NULL;
        long parsed = strtol(argv[++i], &end, 10);
        if (!end || *end || parsed < INT_MIN || parsed > INT_MAX) {
            fprintf(stderr, "invalid integer for %s\n", name); return 2;
        }
        int z = (int)parsed;
        if (!strcmp(name, "--m")) m = z;
        else if (!strcmp(name, "--u")) { u = z; have_u = 1; }
        else if (!strcmp(name, "--v")) { v = z; have_v = 1; }
        else if (!strcmp(name, "--errors")) errors = z;
        else if (!strcmp(name, "--seed")) seed = z;
        else if (!strcmp(name, "--trials")) trials = z;
        else { fprintf(stderr, "unknown option %s\n", name); return 2; }
    }

    if (!init_field(m) || (have_u != have_v) ||
        (have_u && (u < 0 || v < 0 || u + v > MAX_DEG)) ||
        errors < 0 || errors > MAXN || trials < 1 || trials > 10000) {
        fprintf(stderr, "unsupported parameters (specify both --u and --v, or neither)\n");
        return 2;
    }

    if (have_u &&
        (monomial_count(u) > 5000 || monomial_count(v) > 5000 ||
         monomial_count(u + v) > 5000)) {
        fprintf(stderr, "monomial space too large\n");
        return 2;
    }

    verbose = (trials == 1);
    enumerate_points();
    if (npts == 0) {
        fprintf(stderr, "no affine rational support points found\n");
        return 2;
    }

    rng = (uint32_t)seed;
    if (rng == 0) rng = 1;

    printf("BBGS E2 basic decoder prototype (automatic u,v)\n");
    printf("GF(2^%d), q=%d, j=%d, k=%d\n", 2 * m + 1, Q, J, K);
    printf("Affine rational support: n=%d (x != 0)\n", npts);
    if (have_u)
        printf("Parameter mode: manual u=%d, v=%d\n", u, v);
    else
        puts("Parameter mode: AUTO (balanced degree search)");

    if (errors == 0) {
        puts("No-error case: zero error vector is already a codeword.");
        return 0;
    }
    if (errors > npts) {
        fprintf(stderr, "errors must be <= n\n");
        return 2;
    }

    int successes = 0;
    for (int trial = 1; trial <= trials; ++trial) {
        int *received = (int *)xcalloc((size_t)npts, sizeof(int));
        int *corrected = (int *)xcalloc((size_t)npts, sizeof(int));
        int *used = (int *)xcalloc((size_t)npts, sizeof(int));
        int *original = (int *)xcalloc((size_t)npts, sizeof(int));
        if (!received || !corrected || !used || !original) {
            fprintf(stderr, "memory allocation failed\n");
            free(received); free(corrected); free(used); free(original);
            return 2;
        }

        for (int i = 0; i < errors; ++i) {
            int pos;
            do { pos = (int)(rnd() % (uint32_t)npts); } while (used[pos]);
            used[pos] = 1;
            int e = 1 + (int)(rnd() % (uint32_t)(Q - 1));
            received[pos] = e;
            original[pos] = e;
            if (verbose)
                printf("error[%d]: point=(%d,%d), value=%d\n",
                       i + 1, pts[pos].x, pts[pos].y, e);
        }

        int nc = 0, nk = 0, rk = -1;
        int trial_u = u, trial_v = v;
        int ok;

        if (have_u) {
            ok = decode(received, u, v, corrected, &nc, &nk, &rk);
        } else {
            ok = find_auto_parameters(received, errors, corrected,
                                      &trial_u, &trial_v, &nc, &nk, &rk);
        }

        int exact = ok;
        if (ok) {
            for (int p = 0; p < npts; ++p)
                if ((received[p] ^ corrected[p]) != original[p]) {
                    exact = 0;
                    break;
                }
        }
        if (exact) ++successes;

        if (verbose) {
            if (ok)
                printf("selected u=%d, v=%d, total degree=%d\n",
                       trial_u, trial_v, trial_u + trial_v);
            else if (!have_u)
                puts("AUTO SEARCH: no parameter pair found");
            printf("check-matrix rank=%d, locator-kernel dimension=%d, "
                   "common-zero candidates=%d\n", rk, nk, nc);
            puts(ok ? "PARITY CHECKS: PASS" : "PARITY CHECKS: FAIL/AMBIGUOUS");
            puts(exact ? "ERROR VECTOR: EXACT MATCH" :
                         "ERROR VECTOR: NOT VERIFIED");
        } else {
            printf("trial %d: %s", trial, exact ? "EXACT MATCH" : "FAIL");
            if (ok) printf(" (u=%d, v=%d, candidates=%d)",
                           trial_u, trial_v, nc);
            putchar('\n');
        }

        free(received); free(corrected); free(used); free(original);
    }

    if (trials > 1)
        printf("Trials: %d, errors per trial: %d, exact recoveries: %d/%d\n",
               trials, errors, successes, trials);

    return successes == trials ? 0 : 1;
}
