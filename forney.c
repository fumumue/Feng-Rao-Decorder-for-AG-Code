#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXR 8

static int P, M, Q;
static int *EXPT, *LOGT, *NEGT, *ADDT;

static int gf_init(int p, int m)
{
    int q = 1, i, a, b;
    for (i = 0; i < m; i++) q *= p;
    P = p; M = m; Q = q;
    int *seq = malloc(sizeof(int) * (q > 1 ? q - 1 : 1));
    int *seen = malloc(sizeof(int) * q);
    int *c = calloc(m, sizeof(int));
    int *v = calloc(m, sizeof(int));
    int found = 0;
    long total = 1;
    for (i = 0; i < m; i++) total *= p;
    for (long idx = 0; idx < total && !found; idx++) {
        long t = idx;
        for (i = 0; i < m; i++) { c[i] = (int)(t % p); t /= p; }
        if (c[0] == 0) continue;
        memset(seen, 0, sizeof(int) * q);
        for (i = 0; i < m; i++) v[i] = 0;
        v[0] = 1;
        int ok = 1;
        for (int step = 0; step < q - 1; step++) {
            int val = 0, pw = 1;
            for (i = 0; i < m; i++) { val += v[i] * pw; pw *= p; }
            if (seen[val]) { ok = 0; break; }
            seen[val] = 1;
            seq[step] = val;
            int top = v[m - 1];
            for (i = m - 1; i > 0; i--) v[i] = v[i - 1];
            v[0] = 0;
            for (i = 0; i < m; i++) v[i] = (((v[i] - top * c[i]) % p) + p) % p;
        }
        if (ok) {
            int one = (v[0] == 1);
            for (i = 1; i < m; i++) if (v[i]) one = 0;
            if (one) found = 1;
        }
    }
    if (!found) { fprintf(stderr, "no primitive poly\n"); return 0; }
    EXPT = malloc(sizeof(int) * 2 * (q - 1));
    LOGT = malloc(sizeof(int) * q);
    NEGT = malloc(sizeof(int) * q);
    for (i = 0; i < q - 1; i++) { EXPT[i] = EXPT[i + q - 1] = seq[i]; LOGT[seq[i]] = i; }
    LOGT[0] = -1;
    ADDT = NULL;
    for (a = 0; a < q; a++) {
        int val = 0, pw = 1, t = a;
        for (i = 0; i < m; i++) { int d = t % p; t /= p; val += ((p - d) % p) * pw; pw *= p; }
        NEGT[a] = val;
    }
    if (p != 2) {
        ADDT = malloc(sizeof(int) * (size_t)q * q);
        for (a = 0; a < q; a++)
            for (b = 0; b < q; b++) {
                int x = a, y = b, val = 0, pw = 1;
                for (i = 0; i < m; i++) { val += (((x % p) + (y % p)) % p) * pw; x /= p; y /= p; pw *= p; }
                ADDT[(size_t)a * q + b] = val;
            }
    }
    free(seq); free(seen); free(c); free(v);
    return 1;
}

static inline int gf_add(int a, int b) { return P == 2 ? (a ^ b) : ADDT[(size_t)a * Q + b]; }
static inline int gf_sub(int a, int b) { return gf_add(a, NEGT[b]); }
static inline int gf_neg(int a) { return NEGT[a]; }
static inline int gf_mul(int a, int b) { return (a == 0 || b == 0) ? 0 : EXPT[LOGT[a] + LOGT[b]]; }
static inline int gf_inv(int a) { return EXPT[(Q - 1) - LOGT[a]]; }
static int gf_pow(int a, int e)
{
    if (e == 0) return 1;
    if (a == 0) return 0;
    long k = ((long)LOGT[a] * e) % (Q - 1);
    if (k < 0) k += Q - 1;
    return EXPT[k];
}

static int floordiv(int a, int b) { return a >= 0 ? a / b : -((-a + b - 1) / b); }
static int gcd_int(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int rref(int *A, int rows, int cols, int *piv)
{
    int r = 0;
    for (int c = 0; c < cols && r < rows; c++) {
        int pr = -1;
        for (int i = r; i < rows; i++) if (A[(size_t)i * cols + c]) { pr = i; break; }
        if (pr < 0) continue;
        if (pr != r)
            for (int j = 0; j < cols; j++) {
                int t = A[(size_t)r * cols + j];
                A[(size_t)r * cols + j] = A[(size_t)pr * cols + j];
                A[(size_t)pr * cols + j] = t;
            }
        int iv = gf_inv(A[(size_t)r * cols + c]);
        for (int j = 0; j < cols; j++) A[(size_t)r * cols + j] = gf_mul(iv, A[(size_t)r * cols + j]);
        for (int i = 0; i < rows; i++) {
            if (i == r) continue;
            int f = A[(size_t)i * cols + c];
            if (!f) continue;
            for (int j = 0; j < cols; j++)
                A[(size_t)i * cols + j] = gf_sub(A[(size_t)i * cols + j], gf_mul(f, A[(size_t)r * cols + j]));
        }
        piv[r++] = c;
    }
    return r;
}

static int *nullspace(const int *A, int rows, int cols, int *nvec)
{
    int *R = malloc(sizeof(int) * (size_t)(rows ? rows : 1) * cols);
    int *piv = malloc(sizeof(int) * (cols + 1));
    int *ispiv = calloc(cols, sizeof(int));
    if (rows) memcpy(R, A, sizeof(int) * (size_t)rows * cols);
    int rk = rows ? rref(R, rows, cols, piv) : 0;
    for (int i = 0; i < rk; i++) ispiv[piv[i]] = 1;
    int nf = cols - rk;
    int *out = malloc(sizeof(int) * (size_t)(nf ? nf : 1) * cols);
    int vi = 0;
    for (int fc = 0; fc < cols; fc++) {
        if (ispiv[fc]) continue;
        int *v = out + (size_t)vi * cols;
        memset(v, 0, sizeof(int) * cols);
        v[fc] = 1;
        for (int i = 0; i < rk; i++) v[piv[i]] = gf_neg(R[(size_t)i * cols + fc]);
        vi++;
    }
    free(R); free(piv); free(ispiv);
    *nvec = nf;
    return out;
}

static int solve_unique(const int *A, int rows, int n, const int *s, int *x)
{
    int cols = n + 1;
    int *aug = malloc(sizeof(int) * (size_t)rows * cols);
    int *piv = malloc(sizeof(int) * (cols + 1));
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < n; j++) aug[(size_t)i * cols + j] = A[(size_t)i * n + j];
        aug[(size_t)i * cols + n] = s[i];
    }
    int rk = rref(aug, rows, cols, piv);
    int ok = 1;
    for (int i = 0; i < rk; i++) if (piv[i] == n) ok = 0;
    if (ok && rk < n) ok = 0;
    if (ok) {
        for (int j = 0; j < n; j++) x[j] = 0;
        for (int i = 0; i < rk; i++) x[piv[i]] = aug[(size_t)i * cols + n];
    }
    free(aug); free(piv);
    return ok;
}

typedef struct { int j, k; int ns[MAXR]; } Mono;

typedef struct {
    int a, b, m0, r, ms[MAXR], roots[256];
    int g, degG, tmax;
    int n, *px, *py;
    int nH, *H;
    int k;
} Code;

static Mono *basis_L(const Code *C, int m0, const int *ms, int *count)
{
    int a = C->a, b = C->b, r = C->r, cnt = 0;
    int j, i, k;
    for (j = 0; j < a; j++) {
        int N = 0;
        for (i = 0; i < r; i++) N += floordiv(ms[i] + j, a);
        int D = N + floordiv(m0 - b * j, a);
        if (D >= 0) cnt += D + 1;
    }
    Mono *B = malloc(sizeof(Mono) * (cnt ? cnt : 1));
    int t = 0;
    for (j = 0; j < a; j++) {
        int ns[MAXR], N = 0;
        for (i = 0; i < r; i++) { ns[i] = floordiv(ms[i] + j, a); N += ns[i]; }
        int D = N + floordiv(m0 - b * j, a);
        for (k = 0; k <= D; k++) {
            B[t].j = j; B[t].k = k;
            for (i = 0; i < r; i++) B[t].ns[i] = ns[i];
            t++;
        }
    }
    *count = cnt;
    return B;
}

static int *evaluate(const Code *C, const Mono *B, int cnt)
{
    int *E = malloc(sizeof(int) * (size_t)(cnt ? cnt : 1) * C->n);
    for (int t = 0; t < cnt; t++)
        for (int p = 0; p < C->n; p++) {
            int x = C->px[p], y = C->py[p];
            int v = gf_mul(gf_pow(y, B[t].j), gf_pow(x, B[t].k));
            for (int i = 0; i < C->r; i++)
                if (B[t].ns[i]) v = gf_mul(v, gf_pow(gf_sub(x, C->roots[i]), -B[t].ns[i]));
            E[(size_t)t * C->n + p] = v;
        }
    return E;
}

static unsigned long long rng_state = 88172645463325252ULL;
static unsigned rnd(void)
{
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
    return (unsigned)(rng_state >> 11);
}

static int code_init(Code *C, int a, int b, int m0, int r, const int *ms,
                     const int *roots_in, unsigned seed)
{
    int i;
    memset(C, 0, sizeof(*C));
    if (gcd_int(a, b) != 1) { fprintf(stderr, "gcd(a,b)=1 needed\n"); return 0; }
    if (a % P == 0) { fprintf(stderr, "p divides a\n"); return 0; }
    if (b > Q || b > 256) { fprintf(stderr, "b <= q needed\n"); return 0; }
    if (r > b || r > MAXR) { fprintf(stderr, "too many ms\n"); return 0; }
    for (i = 0; i < r; i++) if (ms[i] < 0) { fprintf(stderr, "ms nonneg\n"); return 0; }
    C->a = a; C->b = b; C->m0 = m0; C->r = r;
    for (i = 0; i < r; i++) C->ms[i] = ms[i];
    rng_state ^= (unsigned long long)seed * 2654435761ULL + 1;
    if (roots_in) {
        for (i = 0; i < b; i++) {
            if (roots_in[i] < 0 || roots_in[i] >= Q) { fprintf(stderr, "root range\n"); return 0; }
            for (int j = 0; j < i; j++)
                if (roots_in[j] == roots_in[i]) { fprintf(stderr, "dup roots\n"); return 0; }
            C->roots[i] = roots_in[i];
        }
    } else {
        int *perm = malloc(sizeof(int) * Q);
        for (i = 0; i < Q; i++) perm[i] = i;
        for (i = Q - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (i = 0; i < b; i++) C->roots[i] = perm[i];
        free(perm);
    }
    C->g = (a - 1) * (b - 1) / 2;
    C->degG = m0;
    for (i = 0; i < r; i++) C->degG += ms[i];
    C->tmax = (C->degG - 3 * C->g + 1) / 2;
    if (C->degG - 3 * C->g + 1 < 0) C->tmax = 0;
    C->px = malloc(sizeof(int) * (size_t)Q * a);
    C->py = malloc(sizeof(int) * (size_t)Q * a);
    int *pa = malloc(sizeof(int) * Q);
    for (int y = 0; y < Q; y++) pa[y] = gf_pow(y, a);
    pa[0] = 0;
    for (int x = 0; x < Q; x++) {
        int fx = 1;
        for (i = 0; i < b; i++) fx = gf_mul(fx, gf_sub(x, C->roots[i]));
        for (int y = 0; y < Q; y++) {
            if (pa[y] != fx) continue;
            int excl = 0;
            for (i = 0; i < r; i++) if (ms[i] > 0 && x == C->roots[i] && y == 0) excl = 1;
            if (excl) continue;
            C->px[C->n] = x; C->py[C->n] = y; C->n++;
        }
    }
    free(pa);
    int cnt;
    Mono *B = basis_L(C, m0, ms, &cnt);
    int *E = evaluate(C, B, cnt);
    int *piv = malloc(sizeof(int) * (C->n + 1));
    int rk = cnt ? rref(E, cnt, C->n, piv) : 0;
    C->nH = rk;
    C->H = malloc(sizeof(int) * (size_t)(rk ? rk : 1) * C->n);
    if (rk) memcpy(C->H, E, sizeof(int) * (size_t)rk * C->n);
    C->k = C->n - rk;
    free(B); free(E); free(piv);
    return 1;
}

static void code_free(Code *C) { free(C->px); free(C->py); free(C->H); }

static void syndrome(const Code *C, const int *r, int *s)
{
    for (int i = 0; i < C->nH; i++) {
        int acc = 0;
        for (int k = 0; k < C->n; k++) {
            int h = C->H[(size_t)i * C->n + k];
            if (h && r[k]) acc = gf_add(acc, gf_mul(h, r[k]));
        }
        s[i] = acc;
    }
}

static void random_codeword(const Code *C, int *c)
{
    int nv, i, k;
    int *V = nullspace(C->H, C->nH, C->n, &nv);
    for (k = 0; k < C->n; k++) c[k] = 0;
    for (i = 0; i < nv; i++) {
        int co = rnd() % Q;
        if (!co) continue;
        for (k = 0; k < C->n; k++) c[k] = gf_add(c[k], gf_mul(co, V[(size_t)i * C->n + k]));
    }
    free(V);
}

static int decode(const Code *C, const int *r, int *out, int *nerr)
{
    int n = C->n, g = C->g, i, k;
    int *s = malloc(sizeof(int) * (C->nH ? C->nH : 1));
    syndrome(C, r, s);
    int zero = 1;
    for (i = 0; i < C->nH; i++) if (s[i]) zero = 0;
    if (zero) { memcpy(out, r, sizeof(int) * n); *nerr = 0; free(s); return 1; }

    int zeros[MAXR] = {0};
    for (int t = 1; t <= C->tmax; t++) {
        int degF = t + g, nF, nFp;
        Mono *bF = basis_L(C, degF, zeros, &nF);
        Mono *bFp = basis_L(C, C->m0 - degF, C->ms, &nFp);
        if (nF == 0 || nFp == 0) { free(bF); free(bFp); continue; }
        int *EF = evaluate(C, bF, nF);
        int *EFp = evaluate(C, bFp, nFp);
        int *Mx = malloc(sizeof(int) * (size_t)nFp * nF);
        int *w = malloc(sizeof(int) * n);
        for (int j = 0; j < nFp; j++) {
            for (k = 0; k < n; k++) w[k] = gf_mul(r[k], EFp[(size_t)j * n + k]);
            for (i = 0; i < nF; i++) {
                int acc = 0;
                for (k = 0; k < n; k++) {
                    int wk = w[k], fk = EF[(size_t)i * n + k];
                    if (wk && fk) acc = gf_add(acc, gf_mul(wk, fk));
                }
                Mx[(size_t)j * nF + i] = acc;
            }
        }
        int nk;
        int *ker = nullspace(Mx, nFp, nF, &nk);
        int success = 0;
        if (nk > 0) {
            char *inZ = malloc(n);
            memset(inZ, 1, n);
            for (int v = 0; v < nk; v++)
                for (k = 0; k < n; k++) {
                    int val = 0;
                    for (i = 0; i < nF; i++) {
                        int ci = ker[(size_t)v * nF + i];
                        if (ci) val = gf_add(val, gf_mul(ci, EF[(size_t)i * n + k]));
                    }
                    if (val) inZ[k] = 0;
                }
            int *Z = malloc(sizeof(int) * n), nz = 0;
            for (k = 0; k < n; k++) if (inZ[k]) Z[nz++] = k;
            if (nz > 0 && nz <= t + g) {
                int *Hz = malloc(sizeof(int) * (size_t)C->nH * nz);
                for (i = 0; i < C->nH; i++)
                    for (int z = 0; z < nz; z++) Hz[(size_t)i * nz + z] = C->H[(size_t)i * n + Z[z]];
                int *e = malloc(sizeof(int) * nz);
                if (solve_unique(Hz, C->nH, nz, s, e)) {
                    int wt = 0;
                    for (int z = 0; z < nz; z++) if (e[z]) wt++;
                    if (wt <= C->tmax) {
                        memcpy(out, r, sizeof(int) * n);
                        for (int z = 0; z < nz; z++) if (e[z]) out[Z[z]] = gf_sub(out[Z[z]], e[z]);
                        *nerr = wt;
                        success = 1;
                    }
                }
                free(Hz); free(e);
            }
            free(inZ); free(Z);
        }
        free(ker); free(Mx); free(w); free(EF); free(EFp); free(bF); free(bFp);
        if (success) { free(s); return 1; }
    }
    free(s);
    return 0;
}

/* ================= Kotter (BMS) + Theorem 5 error values, one-point C_ab ================= */
typedef struct { long fp, fa, na, mm; } KStats;

static int K_A, K_B, K_U, K_ovf, K_unk, K_bad, K_umax, K_m0;
static int *K_Su;
static int K_fc[300];

static int gint(int n) { return n % P; }           /* integer -> prime subfield element */
static int *pnew(void) { return calloc((size_t)K_A * K_U, sizeof(int)); }
static void pzero(int *x) { memset(x, 0, sizeof(int) * (size_t)K_A * K_U); }
static void pcopy(int *d, const int *s) { memcpy(d, s, sizeof(int) * (size_t)K_A * K_U); }
static void padd1(int *Pl, int c, int u, int v)
{
    if (u >= K_U) { K_ovf = 1; return; }
    Pl[c * K_U + u] = gf_add(Pl[c * K_U + u], v);
}
static int prho(const int *Pl)
{
    int best = -1;
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++)
            if (Pl[c * K_U + u]) { int r = K_A * u + K_B * c; if (r > best) best = r; }
    return best;
}
/* dst = y^j * src  (reduced by y^A = f(x)) */
static void pmuly(int *dst, const int *src, int j)
{
    pzero(dst);
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++) {
            int v = src[c * K_U + u];
            if (!v) continue;
            int c2 = c + j;
            if (c2 < K_A) padd1(dst, c2, u, v);
            else { c2 -= K_A; for (int l = 0; l <= K_B; l++) if (K_fc[l]) padd1(dst, c2, u + l, gf_mul(v, K_fc[l])); }
        }
}
/* dst += coef * x^sh * src   (sh >= 0) */
static void paxpy(int *dst, const int *src, int sh, int coef)
{
    if (!coef) return;
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++) {
            int v = src[c * K_U + u];
            if (!v) continue;
            if (u + sh >= K_U) { K_ovf = 1; continue; }
            padd1(dst, c, u + sh, gf_mul(coef, v));
        }
}
static int sget(int u, int c)
{
    if (u < 0) return 0;
    if (u > K_umax || K_A * u + K_B * c > K_m0) { K_unk = 1; return 0; }
    return K_Su[u * K_A + c];
}
static int kmu(const int *ft, int r)
{
    int acc = 0;
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++) {
            int v = ft[c * K_U + u];
            if (!v) continue;
            int s = sget(u + r, c);
            if (s) acc = gf_add(acc, gf_mul(v, s));
        }
    return acc;
}
static int peval(const int *Pl, int x0, int y0)
{
    int acc = 0;
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++) {
            int v = Pl[c * K_U + u];
            if (v) acc = gf_add(acc, gf_mul(v, gf_mul(gf_pow(x0, u), gf_pow(y0, c))));
        }
    return acc;
}
/* d/dx at a point with y0 != 0, using dy/dx = f'(x)/(A y^(A-1)) */
static int pdx(const int *Pl, int x0, int y0)
{
    int fp = 0;
    for (int l = 1; l <= K_B; l++)
        if (K_fc[l] && gint(l)) fp = gf_add(fp, gf_mul(gf_mul(gint(l), K_fc[l]), gf_pow(x0, l - 1)));
    int dydx = gf_mul(fp, gf_inv(gf_mul(gint(K_A), gf_pow(y0, K_A - 1))));
    int acc = 0;
    for (int c = 0; c < K_A; c++)
        for (int u = 0; u < K_U; u++) {
            int v = Pl[c * K_U + u];
            if (!v) continue;
            int t1 = 0, t2 = 0;
            if (u >= 1 && gint(u)) t1 = gf_mul(gint(u), gf_mul(gf_pow(x0, u - 1), gf_pow(y0, c)));
            if (c >= 1 && gint(c)) t2 = gf_mul(gf_mul(gint(c), gf_mul(gf_pow(x0, u), gf_pow(y0, c - 1))), dydx);
            acc = gf_add(acc, gf_mul(v, gf_add(t1, t2)));
        }
    return acc;
}

static int kdecode(const Code *C, const int *r, int *out, int *nerr, KStats *st)
{
    int A = C->a, B = C->b, n = C->n, m0 = C->m0, i, j, k;
    memset(st, 0, sizeof(*st));
    int *s = malloc(sizeof(int) * (C->nH ? C->nH : 1));
    syndrome(C, r, s);
    int zero = 1;
    for (i = 0; i < C->nH; i++) if (s[i]) zero = 0;
    if (zero) { memcpy(out, r, sizeof(int) * n); *nerr = 0; free(s); return 1; }

    K_A = A; K_B = B; K_m0 = m0; K_U = m0 / A + B + 16; K_ovf = K_unk = K_bad = 0;
    K_umax = m0 / A;
    for (i = 0; i <= B; i++) K_fc[i] = 0;
    K_fc[0] = 1;
    { int deg = 0;
      for (int t = 0; t < B; t++) {
          int al = C->roots[t];
          for (int l = deg + 1; l >= 0; l--) {
              int lo = l > 0 ? K_fc[l - 1] : 0;
              K_fc[l] = gf_sub(lo, gf_mul(al, K_fc[l]));
          }
          deg++;
      } }
    K_Su = calloc((size_t)(K_umax + 1) * A, sizeof(int));
    for (int u = 0; u <= K_umax; u++)
        for (int c = 0; c < A; c++) {
            if (A * u + B * c > m0) continue;
            int acc = 0;
            for (k = 0; k < n; k++) {
                if (!r[k]) continue;
                acc = gf_add(acc, gf_mul(r[k], gf_mul(gf_pow(C->px[k], u), gf_pow(C->py[k], c))));
            }
            K_Su[u * A + c] = acc;
        }

    int **f = malloc(sizeof(int *) * A), **g = malloc(sizeof(int *) * A), *T[5], *ft = pnew();
    for (i = 0; i < A; i++) { f[i] = pnew(); g[i] = pnew(); f[i][i * K_U + 0] = 1; }
    for (i = 0; i < 5; i++) T[i] = pnew();

    for (int m = 0; m <= m0 && !K_bad && !K_ovf; m++)
        for (i = 0; i < A; i++) {
            int need = (((m - B * i) % A) + A) % A;
            for (j = 0; j < A; j++) if ((B * j) % A == need) break;
            if (j < i) continue;
            int di = prho(f[i]), dj = prho(f[j]);
            int ni = m - di - B * j, nj = m - dj - B * i;
            if (ni % A || nj % A || (di + dj - m) % A) { K_bad = 1; break; }
            int ri = ni / A, rj = nj / A, p = (di + dj - m) / A - 1;
            pmuly(ft, f[i], j);
            int mu_i = kmu(ft, ri), mu_j = mu_i;
            if (i != j) { pmuly(ft, f[j], i); mu_j = kmu(ft, rj); if (mu_i != mu_j) st->mm++; }
            int *nfi = T[0], *nfj = T[1], *ngi = T[2], *ngj = T[3];
            pzero(nfi); pzero(nfj); pzero(ngi); pzero(ngj);
            if (!(mu_i && p < 0)) {
                pcopy(nfi, f[i]); paxpy(nfi, g[j], p, gf_neg(mu_i)); pcopy(ngj, g[j]);
            } else {
                paxpy(nfi, f[i], -p, 1); paxpy(nfi, g[j], 0, gf_neg(mu_i)); paxpy(ngj, f[i], 0, gf_inv(mu_i));
            }
            if (i != j) {
                if (!(mu_j && p < 0)) {
                    pcopy(nfj, f[j]); paxpy(nfj, g[i], p, gf_neg(mu_j)); pcopy(ngi, g[i]);
                } else {
                    paxpy(nfj, f[j], -p, 1); paxpy(nfj, g[i], 0, gf_neg(mu_j)); paxpy(ngi, f[j], 0, gf_inv(mu_j));
                }
            }
            pcopy(f[i], nfi); pcopy(g[j], ngj);
            if (i != j) { pcopy(f[j], nfj); pcopy(g[i], ngi); }
        }

    int success = 0;
    if (!K_bad && !K_ovf && !K_unk) {
        int *Z = malloc(sizeof(int) * n), nz = 0;
        for (k = 0; k < n; k++) {
            int allz = 1;
            for (i = 0; i < A && allz; i++) if (peval(f[i], C->px[k], C->py[k])) allz = 0;
            if (allz) Z[nz++] = k;
        }
        if (nz > 0 && nz <= C->tmax) {
            int *Hz = malloc(sizeof(int) * (size_t)C->nH * nz), *ref = malloc(sizeof(int) * nz);
            for (i = 0; i < C->nH; i++)
                for (int z = 0; z < nz; z++) Hz[(size_t)i * nz + z] = C->H[(size_t)i * n + Z[z]];
            if (solve_unique(Hz, C->nH, nz, s, ref)) {
                int wt = 0;
                for (int z = 0; z < nz; z++) if (ref[z]) wt++;
                if (wt <= C->tmax) {
                    memcpy(out, r, sizeof(int) * n);
                    for (int z = 0; z < nz; z++) {
                        int kk = Z[z], ev = ref[z], x0 = C->px[kk], y0 = C->py[kk];
                        if (y0 != 0) {
                            int den = 0;
                            for (i = 0; i < A; i++)
                                den = gf_add(den, gf_mul(pdx(f[i], x0, y0), peval(g[i], x0, y0)));
                            if (den) { int ef = gf_inv(den); st->fp++; if (ef == ref[z]) st->fa++; ev = ef; }
                            else st->na++;
                        } else st->na++;
                        if (ev) out[kk] = gf_sub(out[kk], ev);
                    }
                    *nerr = wt; success = 1;
                }
            }
            free(Hz); free(ref);
        }
        free(Z);
    }
    for (i = 0; i < A; i++) { free(f[i]); free(g[i]); }
    for (i = 0; i < 5; i++) free(T[i]);
    free(f); free(g); free(ft); free(K_Su); free(s);
    return success;
}

/* 誤りベクトル e の非零成分を「位置 k (x,y) = 値」で表示。値は体の元の整数表現(0..q-1) */
static void show_errvec(const char *label, const int *e, int n, const Code *C)
{
    int w = 0;
    for (int k = 0; k < n; k++) if (e[k]) w++;
    printf("      %-14s 重み %d:", label, w);
    if (w == 0) printf(" (なし)");
    for (int k = 0; k < n; k++)
        if (e[k]) printf("  [%d](%d,%d)=%d", k, C->px[k], C->py[k], e[k]);
    printf("\n");
}

static int parse_list(const char *str, int *out, int maxn)
{
    int n = 0;
    const char *p = str;
    while (*p) {
        char *end;
        long v = strtol(p, &end, 10);
        if (end == p) return -1;
        if (n >= maxn) return -1;
        out[n++] = (int)v;
        p = end;
        if (*p == ',') p++;
        else if (*p) return -1;
    }
    return n;
}

static int parse_int(const char *name, const char *str, int *out)
{
    char *end;
    long v = strtol(str, &end, 10);
    if (*str == '\0' || *end != '\0') { fprintf(stderr, "%s needs int: %s\n", name, str); return 0; }
    *out = (int)v;
    return 1;
}

int main(int argc, char **argv)
{
    int p = 2, m = 6, a = 3, b = 4, m0 = 20, trials = 30, errors = -1, seed = 1;
    int ms[MAXR] = { 6, 6 }, r = 2;
    int roots[256], nroots = 0, kflag = 0, show = 0;

    for (int i = 1; i < argc; i++) {
        char *arg = argv[i], *val = NULL;
        if (strncmp(arg, "--", 2) != 0) { fprintf(stderr, "bad arg: %s\n", arg); return 1; }
        char *eq = strchr(arg, '=');
        char name[32];
        size_t len = eq ? (size_t)(eq - arg) : strlen(arg);
        if (len >= sizeof(name)) { fprintf(stderr, "bad option: %s\n", arg); return 1; }
        memcpy(name, arg, len); name[len] = '\0';
        if (!strcmp(name, "--koetter")) { kflag = 1; continue; }
        if (eq) val = eq + 1;
        else if (i + 1 < argc) val = argv[++i];
        else { fprintf(stderr, "%s needs value\n", name); return 1; }

        if (!strcmp(name, "--p")) { if (!parse_int(name, val, &p)) return 1; }
        else if (!strcmp(name, "--m")) { if (!parse_int(name, val, &m)) return 1; }
        else if (!strcmp(name, "--a")) { if (!parse_int(name, val, &a)) return 1; }
        else if (!strcmp(name, "--b")) { if (!parse_int(name, val, &b)) return 1; }
        else if (!strcmp(name, "--m0")) { if (!parse_int(name, val, &m0)) return 1; }
        else if (!strcmp(name, "--trials")) { if (!parse_int(name, val, &trials)) return 1; }
        else if (!strcmp(name, "--errors")) { if (!parse_int(name, val, &errors)) return 1; }
        else if (!strcmp(name, "--seed")) { if (!parse_int(name, val, &seed)) return 1; }
        else if (!strcmp(name, "--show")) { if (!parse_int(name, val, &show)) return 1; }
        else if (!strcmp(name, "--ms")) {
            r = parse_list(val, ms, MAXR);
            if (r < 0) { fprintf(stderr, "bad --ms\n"); return 1; }
            if (r == 1 && ms[0] == 0) r = 0;
        }
        else if (!strcmp(name, "--roots")) {
            nroots = parse_list(val, roots, 256);
            if (nroots < 0) { fprintf(stderr, "bad --roots\n"); return 1; }
        }
        else { fprintf(stderr, "unknown option: %s\n", name); return 1; }
    }
    if (nroots && nroots != b) { fprintf(stderr, "--roots needs b=%d\n", b); return 1; }
    if (!gf_init(p, m)) return 1;
    Code C;
    if (!code_init(&C, a, b, m0, r, ms, nroots ? roots : NULL, (unsigned)seed)) return 1;

    printf("GF(%d^%d) y^%d=f(x), deg f=%d, g=%d\n", p, m, a, b, C.g);
    printf("roots:");
    for (int i = 0; i < b; i++) printf(" %d", C.roots[i]);
    printf("\nG = %d*Pinf", m0);
    for (int i = 0; i < r; i++) printf(" + %d*Q%d", ms[i], i + 1);
    printf("  (deg G=%d, %d-point)\n", C.degG, r + 1);
    printf("n=%d, k=%d, d>=%d, t<=%d\n", C.n, C.k, C.degG - 2 * C.g + 2, C.tmax);
    if (C.k <= 0) { printf("k<=0\n"); code_free(&C); return 0; }

    int n = C.n;
    int *c = malloc(sizeof(int) * n), *rr = malloc(sizeof(int) * n);
    int *out = malloc(sizeof(int) * n), *idx = malloc(sizeof(int) * n), *out2 = malloc(sizeof(int) * n);
    int tlo = 0, thi = C.tmax + 2;
    if (errors >= 0) tlo = thi = errors;
    for (int t = tlo; t <= thi && t <= n; t++) {
        int good = 0, kgood = 0; KStats tot = {0,0,0,0};
        for (int tr = 0; tr < trials; tr++) {
            random_codeword(&C, c);
            memcpy(rr, c, sizeof(int) * n);
            for (int i = 0; i < n; i++) idx[i] = i;
            for (int i = 0; i < t; i++) {
                int j = i + rnd() % (n - i);
                int tmp = idx[i]; idx[i] = idx[j]; idx[j] = tmp;
                rr[idx[i]] = gf_add(rr[idx[i]], 1 + rnd() % (Q - 1));
            }
            int ne;
            int dok = decode(&C, rr, out, &ne);
            if (dok && memcmp(out, c, sizeof(int) * n) == 0) good++;
            int kok = 0;
            if (kflag && r == 0) { KStats ks; int ne2; kok = kdecode(&C, rr, out2, &ne2, &ks); if (kok && memcmp(out2, c, sizeof(int) * n) == 0) kgood++;
                tot.fp += ks.fp; tot.fa += ks.fa; tot.na += ks.na; tot.mm += ks.mm; }
            if (tr < show) {
                int *ev = malloc(sizeof(int) * n);
                printf("    試行 %d:\n", tr + 1);
                for (int k = 0; k < n; k++) ev[k] = gf_sub(rr[k], c[k]);
                show_errvec("元の誤り", ev, n, &C);
                if (dok) { for (int k = 0; k < n; k++) ev[k] = gf_sub(rr[k], out[k]);
                           show_errvec("SV復号", ev, n, &C);
                           printf("      -> SV: %s\n", memcmp(out, c, sizeof(int) * n) == 0 ? "一致" : "不一致"); }
                else printf("      SV復号         復号失敗\n");
                if (kflag && r == 0) {
                    if (kok) { for (int k = 0; k < n; k++) ev[k] = gf_sub(rr[k], out2[k]);
                               show_errvec("Koetter復号", ev, n, &C);
                               printf("      -> Koetter: %s\n", memcmp(out2, c, sizeof(int) * n) == 0 ? "一致" : "不一致"); }
                    else printf("      Koetter復号    復号失敗\n");
                }
                free(ev);
            }
        }
        printf("  errors %2d: %d/%d ok%s\n", t, good, trials, t > C.tmax ? "  (beyond guarantee)" : "");
        if (kflag && r == 0) printf("           Koetter: %d/%d ok | formula agrees %ld/%ld (n/a %ld, mu mismatch %ld)\n", kgood, trials, tot.fa, tot.fp, tot.na, tot.mm);
    }
    free(c); free(rr); free(out); free(idx);
    code_free(&C);
    return 0;
}

