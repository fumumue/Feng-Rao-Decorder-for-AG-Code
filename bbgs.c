/*
 * BBGS tower: first non-rational level E_2, basic syndrome decoder
 * with error-locator CURVES.   Binary characteristic prototype: p=2,
 * n=2m+1, m=1 or 2.
 *
 * E_2/F_(2^n)(x) is defined by
 *   Tr_j(y / x^(2^k)) + Tr_k(y^(2^j) / x) = 1,
 * where j=m if m is odd, otherwise j=m+1, and k=n-j.
 * We enumerate affine rational points with x != 0.
 *
 * Parity-check matrix H : all monomials x^a y^b of total degree <= u+v
 * evaluated at the points.  Syndrome S_(a,b) = sum_p H[(a,b)][p] * r[p].
 *
 * Syndrome matrix  M[(a2,b2)][(a1,b1)] = S_(a1+a2, b1+b2)
 *   rows   : monomials of degree <= v
 *   columns: monomials of degree <= d   (d = 0..u)
 * A kernel vector c gives L(x,y) = sum c_i x^a_i y^b_i which vanishes at
 * all error positions.  L(x,y)=0 is an "error-locator curve"; its
 * rational intersection points with E_2 contain the error positions.
 *
 * Three ways to get the error positions are compared:
 *   [A] ONE locator curve: the kernel combination whose intersection with
 *       E_2 has the fewest rational points (greedy search).
 *   [B] intersection of several random combinations of the kernel basis.
 *   [C] common zeros of the whole kernel basis (original method).
 * For each method the smallest degree d that works is used.
 * Error values are then solved from the syndromes and verified.
 *
 * NOTE: this is still an experimental affine evaluation-code construction,
 *       NOT a completed RR/Feng-Rao (majority voting) decoder.
 *
 * Build:  gcc -O2 -o bbgs_e2_locator bbgs_e2_locator.c
 * Run  :  ./bbgs_e2_locator --m 2 --u 4 --v 4 --errors 3 --seed 1
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1024
#define MAXMON 256

typedef struct { int x, y; } Point;
typedef struct { int a, b; } Mon;

static int Q, J, K, IRR;
static Point pts[MAXN];
static int npts;

/* ---------- GF(2^n) ---------- */
static int MUL[32][32], INV[32];

static int gf_mul_slow(int a, int b) {
    int r = 0;
    while (b) {
        if (b & 1) r ^= a;
        b >>= 1;
        a <<= 1;
        if (a & Q) a ^= IRR;
    }
    return r & (Q - 1);
}
static void init_tables(void) {
    for (int a = 0; a < Q; ++a)
        for (int b = 0; b < Q; ++b) MUL[a][b] = gf_mul_slow(a, b);
    INV[0] = 0;
    for (int a = 1; a < Q; ++a)
        for (int b = 1; b < Q; ++b)
            if (MUL[a][b] == 1) { INV[a] = b; break; }
}
static inline int gf_mul(int a, int b) { return MUL[a][b]; }
static int gf_pow(int a, int e) {
    int r = 1;
    while (e) {
        if (e & 1) r = gf_mul(r, a);
        a = gf_mul(a, a);
        e >>= 1;
    }
    return r;
}
static inline int gf_inv(int a) { return INV[a]; }
static int trace2(int z, int r) {
    int s = 0;
    for (int i = 0; i < r; ++i) { s ^= z; z = gf_mul(z, z); }
    return s;
}
static int init_field(int m) {
    if (m == 1) { Q = 8; IRR = 0x0b; }
    else if (m == 2) { Q = 32; IRR = 0x25; }
    else return 0;
    J = (m % 2) ? m : m + 1;
    K = 2 * m + 1 - J;
    init_tables();
    return 1;
}

/* ---------- curve E_2 and its rational points ---------- */
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
            if (bbgs_equation(x, y) && npts < MAXN) pts[npts++] = (Point){x, y};
}

/* ---------- monomials ---------- */
static int monomials(int d, Mon *out) {
    int n = 0;
    for (int a = 0; a <= d; ++a)
        for (int b = 0; b + a <= d; ++b) out[n++] = (Mon){a, b};
    return n;
}
static int eval_mon(Mon m, Point p) {
    return gf_mul(gf_pow(p.x, m.a), gf_pow(p.y, m.b));
}
static int mon_index(const Mon *H, int n, int a, int b) {
    for (int h = 0; h < n; ++h)
        if (H[h].a == a && H[h].b == b) return h;
    return -1;
}
/* print sum c[i] x^a y^b  (coefficients are field elements as integers) */
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

/* ---------- linear algebra over GF(2^n) ---------- */
static int rref(int *A, int rows, int cols, int *piv) {
    int r = 0;
    for (int c = 0; c < cols && r < rows; ++c) {
        int pr = -1;
        for (int i = r; i < rows; ++i)
            if (A[i * cols + c]) { pr = i; break; }
        if (pr < 0) continue;
        if (pr != r)
            for (int j = 0; j < cols; ++j) {
                int t = A[r * cols + j];
                A[r * cols + j] = A[pr * cols + j];
                A[pr * cols + j] = t;
            }
        int iv = gf_inv(A[r * cols + c]);
        for (int j = 0; j < cols; ++j) A[r * cols + j] = gf_mul(iv, A[r * cols + j]);
        for (int i = 0; i < rows; ++i)
            if (i != r && A[i * cols + c]) {
                int f = A[i * cols + c];
                for (int j = 0; j < cols; ++j)
                    A[i * cols + j] ^= gf_mul(f, A[r * cols + j]);
            }
        piv[r++] = c;
    }
    return r;
}
/* kernel basis of A (rows x cols): returns dimension, vectors in out */
static int nullspace(const int *A, int rows, int cols, int *out) {
    static int R[MAXMON * MAXMON];
    int piv[MAXMON], is_piv[MAXMON];
    if (rows * cols > MAXMON * MAXMON || cols > MAXMON) return -1;
    memset(is_piv, 0, sizeof is_piv);
    memcpy(R, A, sizeof(int) * rows * cols);
    int rank = rref(R, rows, cols, piv);
    for (int i = 0; i < rank; i++) is_piv[piv[i]] = 1;
    int nv = 0;
    for (int f = 0; f < cols; f++)
        if (!is_piv[f]) {
            int *v = out + nv * cols;
            memset(v, 0, sizeof(int) * cols);
            v[f] = 1;
            for (int i = 0; i < rank; i++) v[piv[i]] = R[i * cols + f];
            nv++;
        }
    return nv;
}
/* unique solution of A x = rhs (A: rows x cols) */
static int solve_unique(const int *A, int rows, int cols, const int *rhs, int *x) {
    static int aug[MAXMON * (MAXN + 1)];
    int piv[MAXN + 1];
    if (rows * (cols + 1) > MAXMON * (MAXN + 1)) return 0;
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) aug[i * (cols + 1) + j] = A[i * cols + j];
        aug[i * (cols + 1) + cols] = rhs[i];
    }
    int rank = rref(aug, rows, cols + 1, piv);
    for (int i = 0; i < rank; i++) if (piv[i] == cols) return 0;
    int cr = 0;
    for (int i = 0; i < rank; i++) if (piv[i] < cols) cr++;
    if (cr < cols) return 0;
    for (int j = 0; j < cols; j++) x[j] = 0;
    for (int i = 0; i < rank; i++) if (piv[i] < cols) x[piv[i]] = aug[i * (cols + 1) + cols];
    return 1;
}

static unsigned rng = 1;
static unsigned rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }

/* ---------- parity-check matrix (built once) ---------- */
static Mon Hmon[MAXMON];
static int nh;
static int H[MAXMON * MAXN];

static int setup_code(int u, int v) {
    nh = monomials(u + v, Hmon);
    if (nh > MAXMON || nh * npts > MAXMON * MAXN) return 0;
    for (int h = 0; h < nh; h++)
        for (int p = 0; p < npts; p++) H[h * npts + p] = eval_mon(Hmon[h], pts[p]);
    return 1;
}

/* ---------- error-locator machinery ---------- */

/* kernel of the syndrome matrix with columns = monomials of degree <= d,
   rows = monomials of degree <= v.  returns kernel dim, -1 if na > nb */
static int kernel_of_degree(const int *syn, int d, int v, Mon *Amon, int *aidx,
                            int *na_out, int *loc) {
    static Mon Bmon[MAXMON];
    static int MM[MAXMON * MAXMON];
    int nb = monomials(v, Bmon);
    int na = monomials(d, Amon);
    if (na > nb) return -1;
    for (int i = 0; i < na; ++i) aidx[i] = mon_index(Hmon, nh, Amon[i].a, Amon[i].b);
    for (int i = 0; i < na; ++i)
        for (int j = 0; j < nb; ++j) {
            int idx = mon_index(Hmon, nh, Amon[i].a + Bmon[j].a, Amon[i].b + Bmon[j].b);
            if (idx < 0) return -1;
            MM[j * na + i] = syn[idx];
        }
    *na_out = na;
    return nullspace(MM, nb, na, loc);
}

/* values of the kernel basis functions at all points: VZ[z][p] */
static int VZ[MAXMON][MAXN];
static void eval_basis(const int *aidx, int na, const int *loc, int nk) {
    for (int z = 0; z < nk; ++z)
        for (int p = 0; p < npts; ++p) {
            int s = 0;
            for (int a = 0; a < na; ++a) {
                int c = loc[z * na + a];
                if (c) s ^= gf_mul(c, H[aidx[a] * npts + p]);
            }
            VZ[z][p] = s;
        }
}

/* [A] ONE locator curve: greedy search for the kernel combination
   with the fewest zeros on the point set.  c: coefficients (na),
   zeros: point indices.  returns number of zeros. */
static int single_locator(const int *loc, int na, int nk, int *c, int *zeros) {
    static int vc[MAXN];
    memset(c, 0, sizeof(int) * na);
    memset(vc, 0, sizeof(int) * npts);
    int best = npts + 1;
    for (;;) {
        int bz = -1, bl = 0, bn = best;
        for (int z = 0; z < nk; ++z)
            for (int lam = 1; lam < Q; ++lam) {
                int nz = 0;
                for (int p = 0; p < npts; ++p)
                    if (vc[p] == gf_mul(lam, VZ[z][p])) nz++;
                if (nz < bn) {
                    int nonzero = 0;
                    for (int a = 0; a < na && !nonzero; ++a)
                        if (c[a] != gf_mul(lam, loc[z * na + a])) nonzero = 1;
                    if (nonzero) { bn = nz; bz = z; bl = lam; }
                }
            }
        if (bz < 0) break;
        for (int a = 0; a < na; ++a) c[a] ^= gf_mul(bl, loc[bz * na + a]);
        for (int p = 0; p < npts; ++p) vc[p] ^= gf_mul(bl, VZ[bz][p]);
        best = bn;
    }
    int n = 0;
    for (int p = 0; p < npts; ++p) if (!vc[p]) zeros[n++] = p;
    return n;
}

/* [B] intersection of the zero sets of ntry random combinations */
static int combo_zeros(int nk, int ntry, int *zeros) {
    static char alive[MAXN];
    memset(alive, 1, npts);
    for (int t = 0; t < ntry; ++t) {
        int lam[MAXMON];
        for (int z = 0; z < nk; ++z) lam[z] = 1 + rnd() % (Q - 1);
        for (int p = 0; p < npts; ++p) {
            if (!alive[p]) continue;
            int s = 0;
            for (int z = 0; z < nk; ++z) s ^= gf_mul(lam[z], VZ[z][p]);
            if (s) alive[p] = 0;
        }
    }
    int n = 0;
    for (int p = 0; p < npts; ++p) if (alive[p]) zeros[n++] = p;
    return n;
}

/* [C] common zeros of the whole kernel basis */
static int full_zeros(int nk, int *zeros) {
    int n = 0;
    for (int p = 0; p < npts; ++p) {
        int ok = 1;
        for (int z = 0; z < nk && ok; ++z) if (VZ[z][p]) ok = 0;
        if (ok) zeros[n++] = p;
    }
    return n;
}

/* solve error values on the candidate positions and verify all checks */
static int solve_candidates(const int *syn, const int *cand, int nc, int *e) {
    static int AZ[MAXMON * MAXN];
    int sol[MAXN];
    if (nc <= 0 || nc > nh) return 0;
    for (int h = 0; h < nh; ++h)
        for (int z = 0; z < nc; ++z) AZ[h * nc + z] = H[h * npts + cand[z]];
    if (!solve_unique(AZ, nh, nc, syn, sol)) return 0;
    memset(e, 0, sizeof(int) * npts);
    for (int z = 0; z < nc; ++z) e[cand[z]] = sol[z];
    for (int h = 0; h < nh; ++h) {            /* verify */
        int s = 0;
        for (int p = 0; p < npts; ++p) if (e[p]) s ^= gf_mul(H[h * npts + p], e[p]);
        if (s != syn[h]) return 0;
    }
    return 1;
}

/* ---------- decoder driver ---------- */
#define NMETH 3
static const char *mname[NMETH] = {
    "A: 単一ロケーター曲線",
    "B: 乱数結合の交差",
    "C: 核全体の共通零点"
};
typedef struct { int solved, correct, deg, ncand; } Res;
static Res res[NMETH];
static int errv[NMETH][MAXN];
/* the single curve of method A */
static int curveC[MAXMON], curveNa;
static Mon curveMon[MAXMON];

/* ロケーター関数 L(x,y) を表示し、E2 との有理交点(零点)も列挙する。
   mon, c, na : L の単項式列・係数・項数
   zeros, nz  : 零点の点インデックスと個数 (zeros=NULL なら列挙しない) */
static void print_locator(const char *name, const Mon *mon, const int *c, int na,
                          const int *zeros, int nz) {
    printf("%s(x,y) = ", name);
    print_poly(mon, c, na);
    printf("\n");
    if (zeros) {
        printf("  E2との有理交点 %d 個:", nz);
        for (int i = 0; i < nz; ++i)
            printf(" (%d,%d)", pts[zeros[i]].x, pts[zeros[i]].y);
        printf("\n");
    }
}

/* エラー位置と誤り値を表示する。
   e    : 推定した誤りベクトル (長さ npts)
   truth: 真の誤りベクトル (比較しないなら NULL) */
static void print_error_positions(const int *e, const int *truth) {
    int w = 0;
    printf("エラー位置:\n");
    for (int p = 0; p < npts; ++p) {
        if (!e[p]) continue;
        printf("  [%3d] (x,y)=(%2d,%2d)  value=%2d", p, pts[p].x, pts[p].y, e[p]);
        if (truth) printf("  %s", truth[p] == e[p] ? "OK" : "NG");
        printf("\n");
        ++w;
    }
    if (truth)                      /* 見逃した誤りも表示 */
        for (int p = 0; p < npts; ++p)
            if (truth[p] && !e[p])
                printf("  [%3d] (x,y)=(%2d,%2d)  真の誤り value=%2d を見逃し\n",
                       p, pts[p].x, pts[p].y, truth[p]);
    printf("  推定誤り数 = %d\n", w);
}


static void decode_all(const int *received, int u, int v, int verbose) {
    int syn[MAXMON];
    memset(res, 0, sizeof res);
    for (int h = 0; h < nh; h++) {
        syn[h] = 0;
        for (int p = 0; p < npts; p++) if (received[p]) syn[h] ^= gf_mul(H[h * npts + p], received[p]);
    }
    static int loc[MAXMON * MAXMON];
    Mon Amon[MAXMON];
    int aidx[MAXMON];
    int shown = 0;
    for (int d = 0; d <= u; ++d) {
        int na = 0, nk = kernel_of_degree(syn, d, v, Amon, aidx, &na, loc);
        if (nk < 0) break;           /* na > nb: conditions insufficient */
        if (nk == 0) continue;
        eval_basis(aidx, na, loc, nk);

        if (verbose && !shown) {
            shown = 1;
            printf("最小次数のロケーター曲線: d=%d, 核の次元=%d\n", d, nk);
            for (int z = 0; z < nk && z < 4; ++z) {
                int n = 0;
                for (int p = 0; p < npts; ++p) if (!VZ[z][p]) n++;
                printf("  L%d(x,y) = ", z + 1);
                print_poly(Amon, loc + z * na, na);
                printf("   [E2との有理交点 %d 個]\n", n);
            }
        }

        int allsolved = 1;
        for (int m = 0; m < NMETH; ++m) {
            if (res[m].solved) continue;
            int cand[MAXN], nc = 0, c[MAXMON];
            if (m == 0) nc = single_locator(loc, na, nk, c, cand);
            else if (m == 1) nc = combo_zeros(nk, 4, cand);
            else nc = full_zeros(nk, cand);
            if (solve_candidates(syn, cand, nc, errv[m])) {
                res[m].solved = 1;
                res[m].deg = d;
                res[m].ncand = nc;
                res[m].correct = (memcmp(errv[m], received, sizeof(int) * npts) == 0);
                if (m == 0) {
                    curveNa = na;
                    memcpy(curveC, c, sizeof(int) * na);
                    memcpy(curveMon, Amon, sizeof(Mon) * na);
                }
            } else allsolved = 0;
        }
        if (allsolved) break;
    }

    if (1) {
        for (int m = 0; m < NMETH; ++m) {
            printf("[%s]\n", mname[m]);
            if (!res[m].solved) { puts("  失敗/曖昧 (u,v を増やすか誤り数を減らす)"); continue; }
            printf("  次数 d=%d, 交点(誤り位置候補) %d 個\n", res[m].deg, res[m].ncand);
            if (m == 0) {
                int zeros[MAXN], nz = 0;       // 曲線A上の有理点を数え直す 
                for (int p = 0; p < npts; ++p) {
                    int val = 0;
                    for (int a = 0; a < curveNa; ++a)
                        if (curveC[a])
                            val ^= gf_mul(curveC[a], eval_mon(curveMon[a], pts[p]));
                    if (!val) zeros[nz++] = p;
                }
                print_locator("  L", curveMon, curveC, curveNa, zeros, nz);
            }
            print_error_positions(errv[m], received);
        }
    }
    

    if (1) {
        for (int m = 0; m < NMETH; ++m) {
            printf("[%s]\n", mname[m]);
            if (!res[m].solved) { puts("  失敗/曖昧 (u,v を増やすか誤り数を減らす)"); continue; }
            printf("  次数 d=%d, E2との有理交点(誤り位置候補) %d 個\n", res[m].deg, res[m].ncand);
            if (m == 0) {
                printf("  エラーロケーター曲線 L(x,y) = ");
                print_poly(curveMon, curveC, curveNa);
                puts("  = 0");
            }
            int w = 0;
            for (int p = 0; p < npts; ++p) if (errv[m][p]) {
                printf("  error at (%d,%d), value=%d\n", pts[p].x, pts[p].y, errv[m][p]);
                w++;
            }
            printf("  推定誤り数=%d, 真の誤りと%s\n", w, res[m].correct ? "一致" : "不一致");
        }
    }
        
}

static void usage(const char *p) {
    printf("Usage: %s [--m 1|2] [--u N] [--v N] [--errors T] [--seed N] [--trials N]\n", p);
    puts("GF(2^(2m+1)): m=1 gives GF(8), m=2 gives GF(32).");
    puts("u: locator curve max degree, v: row-monomial degree (u+v <= 8).");
}

int main(int argc, char **argv) {
    int m = 2, u = 4, v = 4, errors = 3, seed = 1, trials = 1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) { usage(argv[0]); return 0; }
        if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", argv[i]); return 2; }
        char *name = argv[i]; int z = atoi(argv[++i]);
        if (!strcmp(name, "--m")) m = z;
        else if (!strcmp(name, "--u")) u = z;
        else if (!strcmp(name, "--v")) v = z;
        else if (!strcmp(name, "--errors")) errors = z;
        else if (!strcmp(name, "--seed")) seed = z;
        else if (!strcmp(name, "--trials")) trials = z;
        else { fprintf(stderr, "unknown option %s\n", name); return 2; }
    }
    if (!init_field(m) || u < 0 || v < 0 || u + v > 8 || errors < 0 || errors > MAXN ||
        trials < 1 || trials > 10000) {
        fprintf(stderr, "unsupported parameters\n"); return 2;
    }
    enumerate_points();
    rng = (unsigned)seed + 1;
    if (!setup_code(u, v)) { fprintf(stderr, "code too large\n"); return 2; }
    printf("BBGS E2 decoder with error-locator curves\nGF(2^%d), q=%d, j=%d, k=%d\n", 2 * m + 1, Q, J, K);
    printf("Affine rational support: n=%d (x != 0)\n", npts);
    printf("Locator degree <= %d, row degree v=%d; check monomials degree <= %d (%d rows)\n", u, v, u + v, nh);
    if (errors == 0) { puts("No-error case: zero error vector is already a codeword."); return 0; }
    if (errors > npts) { fprintf(stderr, "errors must be <= n\n"); return 2; }

    int succ[NMETH] = {0}, solved[NMETH] = {0};
    long degsum[NMETH] = {0};
    for (int trial = 1; trial <= trials; trial++) {
        int received[MAXN] = {0}, used[MAXN] = {0};
        for (int i = 0; i < errors; i++) {
            int pos; do { pos = rnd() % npts; } while (used[pos]); used[pos] = 1;
            int e = 1 + (rnd() % (Q - 1)); received[pos] = e;
            if (trials == 1) printf("error[%d]: point=(%d,%d), value=%d\n", i + 1, pts[pos].x, pts[pos].y, e);
        }
        decode_all(received, u, v, trials == 1);
        for (int k = 0; k < NMETH; ++k) {
            solved[k] += res[k].solved;
            succ[k] += res[k].correct;
            if (res[k].solved) degsum[k] += res[k].deg;
        }
    }
    if (trials > 1) {
        printf("Trials: %d, errors per trial: %d\n", trials, errors);
        for (int k = 0; k < NMETH; ++k)
            printf("  %s : 正しく復号 %d/%d (検査通過 %d, 平均次数 %.2f)\n", mname[k], succ[k], trials,
                   solved[k], solved[k] ? (double)degsum[k] / solved[k] : 0.0);
    }
    return (trials == 1 && succ[0] == 0 && succ[1] == 0 && succ[2] == 0) ? 1 : 0;
}