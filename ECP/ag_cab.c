/*
 * ag_cab_ecp.c - one-point AG code decoder (basic algorithm / ECP) for C_ab curves
 *                over GF(2^m), m <= 10.  Single file, no dependencies.
 *
 * Curve: affine plane curve F(x,u) = 0 of "C_ab" type
 *   deg_u F = a, deg_x F = b, gcd(a,b)=1, F contains u^a and x^b, and every other
 *   monomial x^i u^j has a*i + b*j < a*b.   Then there is exactly one place P at
 *   infinity, ord_P(x) = a, ord_P(u) = b (pole orders), genus g = (a-1)(b-1)/2,
 *   and L(mP) has the basis { x^i u^j : 0 <= j < a, a*i + b*j <= m }.
 *   (Affine nonsingularity is checked at rational points only.)
 *
 * Code:  C = { c in F^n : sum_p c_p h(p) = 0 for all h in L((m1+m2)P) },
 *        decoded with A = L(m1 P), B = L(m2 P)  (A*B is contained in L((m1+m2)P)).
 *
 * Output: error locator polynomial (monic, minimal pole order, written in the
 *         monomials x^i u^j) and a table of error positions / values.
 *
 * Build:   cc -O2 -std=c11 -Wall -Wextra -o ag_cab_ecp ag_cab_ecp.c
 * Examples:
 *   ./ag_cab_ecp --m 6 --curve hermitian --errors 10            (u^8+u = x^9 over GF(64))
 *   ./ag_cab_ecp --m 6 --curve file --file curve.txt --errors 10
 *     curve.txt: one monomial per line "ex eu coef" or "ex eu 0 coef"
 *                (coef = GF element as integer bit-vector, 1 = one)
 *     e.g. u^8 + u + x^9 :   0 8 1 / 0 1 1 / 9 0 1
 *
 * Options (all integers except --curve/--file):
 *   --m M  --curve hermitian|file  --file PATH  --errors E  --trials N  --seed S
 *   --m1 A --m2 B        pole-order bounds of A and B (default: chosen from --errors)
 *   --fast 1             zero codeword, skip H / verification
 *   --list 0|1  --locator N
 *
 * The error bound used is  errors <= min(l(A)-1, m2-2g+1)  (basic algorithm).
 * NOTE: this is the basic (ECP) algorithm, not Feng-Rao majority voting.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_M 10
#define MAX_TERMS 64

typedef uint16_t GF;

static int GQ; /* q = 2^m */
static GF EXPT[2 * (1 << MAX_M)];
static int LOGT[1 << MAX_M];

static int gf_init(int m)
{
    static const unsigned poly[MAX_M + 1] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D, 0x211, 0x409};
    if (m < 2 || m > MAX_M) return 0;
    GQ = 1 << m;
    unsigned x = 1;
    for (int i = 0; i < GQ - 1; ++i) {
        EXPT[i] = (GF)x;
        LOGT[x] = i;
        x <<= 1;
        if (x & (unsigned)GQ) x ^= poly[m];
    }
    for (int i = GQ - 1; i < 2 * (GQ - 1); ++i) EXPT[i] = EXPT[i - (GQ - 1)];
    return 1;
}
static inline GF gmul(GF a, GF b) { return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0; }
static inline GF ginv(GF a) { return a ? EXPT[(GQ - 1) - LOGT[a]] : 0; }
static GF gpow(GF a, int e)
{
    if (e == 0) return 1;
    if (!a) return 0;
    return EXPT[(int)(((long)LOGT[a] * e) % (GQ - 1))];
}
static void pe(GF x)
{
    if (!x) printf("0");
    else printf("g^%d", LOGT[x]);
}

static uint64_t rng_state;
static uint64_t rnd(void)
{
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* ---------------- linear algebra over GF(2^m) ---------------- */
static int rref(GF *m, int rows, int cols, int *piv)
{
    int rank = 0;
    for (int col = 0; col < cols && rank < rows; ++col) {
        int p = rank;
        while (p < rows && m[(size_t)p * cols + col] == 0) ++p;
        if (p == rows) continue;
        if (p != rank)
            for (int j = 0; j < cols; ++j) {
                GF t = m[(size_t)rank * cols + j];
                m[(size_t)rank * cols + j] = m[(size_t)p * cols + j];
                m[(size_t)p * cols + j] = t;
            }
        GF s = ginv(m[(size_t)rank * cols + col]);
        for (int j = 0; j < cols; ++j) m[(size_t)rank * cols + j] = gmul(m[(size_t)rank * cols + j], s);
        for (int i = 0; i < rows; ++i) {
            if (i == rank) continue;
            GF f = m[(size_t)i * cols + col];
            if (!f) continue;
            for (int j = 0; j < cols; ++j) m[(size_t)i * cols + j] ^= gmul(f, m[(size_t)rank * cols + j]);
        }
        piv[rank++] = col;
    }
    return rank;
}

static GF *nullspace(const GF *in, int rows, int cols, int *dim)
{
    GF *m = malloc(((size_t)rows * cols + 1) * sizeof(GF));
    int *piv = malloc(sizeof(int) * (rows + 1));
    int *isp = calloc(cols + 1, sizeof(int));
    memcpy(m, in, (size_t)rows * cols * sizeof(GF));
    int rank = rref(m, rows, cols, piv);
    for (int i = 0; i < rank; ++i) isp[piv[i]] = 1;
    *dim = cols - rank;
    GF *basis = calloc((size_t)(*dim) * cols + 1, sizeof(GF));
    int d = 0;
    for (int fc = 0; fc < cols; ++fc) {
        if (isp[fc]) continue;
        basis[(size_t)d * cols + fc] = 1;
        for (int r = 0; r < rank; ++r) basis[(size_t)d * cols + piv[r]] = m[(size_t)r * cols + fc];
        ++d;
    }
    free(m); free(piv); free(isp);
    return basis;
}

/* ---------------- curve ---------------- */
typedef struct { GF x, u; } Point;
typedef struct { int ex, eu; GF c; } Term;
static Term TERMS[MAX_TERMS];
static int NT;
static int CA, CB; /* a = deg_u F = ord(x),  b = deg_x F = ord(u) */

static GF feval(GF x, GF u)
{
    GF s = 0;
    for (int t = 0; t < NT; ++t) s ^= gmul(TERMS[t].c, gmul(gpow(x, TERMS[t].ex), gpow(u, TERMS[t].eu)));
    return s;
}
static void fgrad(GF x, GF u, GF *fx, GF *fu)
{
    GF sx = 0, su = 0;
    for (int t = 0; t < NT; ++t) {
        if (TERMS[t].ex & 1) sx ^= gmul(TERMS[t].c, gmul(gpow(x, TERMS[t].ex - 1), gpow(u, TERMS[t].eu)));
        if (TERMS[t].eu & 1) su ^= gmul(TERMS[t].c, gmul(gpow(x, TERMS[t].ex), gpow(u, TERMS[t].eu - 1)));
    }
    *fx = sx; *fu = su;
}
static int gcd(int x, int y) { while (y) { int z = x % y; x = y; y = z; } return x; }

static void add_term(int ex, int eu, GF c)
{
    for (int t = 0; t < NT; ++t)
        if (TERMS[t].ex == ex && TERMS[t].eu == eu) { TERMS[t].c ^= c; return; }
    if (NT < MAX_TERMS) { TERMS[NT].ex = ex; TERMS[NT].eu = eu; TERMS[NT].c = c; ++NT; }
}

static int analyze_curve(void)
{
    int a = 0, b = 0;
    for (int t = 0; t < NT; ++t) {
        if (!TERMS[t].c) continue;
        if (TERMS[t].eu > a) a = TERMS[t].eu;
        if (TERMS[t].ex > b) b = TERMS[t].ex;
    }
    int hasU = 0, hasX = 0;
    for (int t = 0; t < NT; ++t) {
        if (!TERMS[t].c) continue;
        if (TERMS[t].ex == 0 && TERMS[t].eu == a) hasU = 1;
        if (TERMS[t].eu == 0 && TERMS[t].ex == b) hasX = 1;
    }
    if (a < 2 || b < 2 || gcd(a, b) != 1) {
        fprintf(stderr, "Not a C_ab curve: deg_u=%d, deg_x=%d must be >=2 and coprime.\n", a, b);
        return 0;
    }
    if (!hasU || !hasX) {
        fprintf(stderr, "Not a C_ab curve: F must contain both u^%d and x^%d as pure monomials.\n", a, b);
        return 0;
    }
    for (int t = 0; t < NT; ++t) {
        if (!TERMS[t].c) continue;
        int w = a * TERMS[t].ex + b * TERMS[t].eu;
        int top = (TERMS[t].ex == 0 && TERMS[t].eu == a) || (TERMS[t].eu == 0 && TERMS[t].ex == b);
        if (w > a * b || (w == a * b && !top)) {
            fprintf(stderr, "Not a C_ab curve: monomial x^%d u^%d has weight %d >= a*b=%d (weights: x=%d, u=%d).\n",
                    TERMS[t].ex, TERMS[t].eu, w, a * b, a, b);
            return 0;
        }
    }
    CA = a; CB = b;
    return 1;
}

/* ---------------- bases of L(mP) ---------------- */
typedef struct { int cnt; GF *v; int *ei, *ej, *w; } Basis;
typedef struct { int n; Basis A, B, H; } Code;
typedef struct { int w, i, j; } Mono;
static int cmp_mono(const void *p, const void *q) { return ((const Mono *)p)->w - ((const Mono *)q)->w; }

static int count_l(int M)
{
    int c = 0;
    for (int j = 0; j < CA; ++j)
        for (int i = 0; CA * i + CB * j <= M; ++i) ++c;
    return c;
}

static Basis build_basis(int M, const Point *pts, int n)
{
    int cnt = count_l(M);
    Mono *mo = malloc(sizeof(Mono) * (cnt + 1));
    int k = 0;
    for (int j = 0; j < CA; ++j)
        for (int i = 0; CA * i + CB * j <= M; ++i) { mo[k].w = CA * i + CB * j; mo[k].i = i; mo[k].j = j; ++k; }
    qsort(mo, cnt, sizeof(Mono), cmp_mono);
    Basis b;
    b.cnt = cnt;
    b.v = malloc((size_t)cnt * n * sizeof(GF) + 1);
    b.ei = malloc(sizeof(int) * (cnt + 1)); b.ej = malloc(sizeof(int) * (cnt + 1)); b.w = malloc(sizeof(int) * (cnt + 1));
    for (int r = 0; r < cnt; ++r) {
        b.ei[r] = mo[r].i; b.ej[r] = mo[r].j; b.w[r] = mo[r].w;
        for (int p = 0; p < n; ++p) b.v[(size_t)r * n + p] = gmul(gpow(pts[p].x, mo[r].i), gpow(pts[p].u, mo[r].j));
    }
    free(mo);
    return b;
}

static void free_basis(Basis *b) { free(b->v); free(b->ei); free(b->ej); free(b->w); }

static int in_code(const Code *c, const GF *w)
{
    for (int r = 0; r < c->H.cnt; ++r) {
        GF z = 0;
        for (int p = 0; p < c->n; ++p) z ^= gmul(c->H.v[(size_t)r * c->n + p], w[p]);
        if (z) return 0;
    }
    return 1;
}

static int verify_product(const Basis *A, const Basis *B, const Basis *H, int n)
{
    GF *ech = malloc((size_t)H->cnt * n * sizeof(GF) + 1);
    GF *prod = malloc((size_t)n * sizeof(GF));
    int *piv = malloc(sizeof(int) * (H->cnt + 1));
    memcpy(ech, H->v, (size_t)H->cnt * n * sizeof(GF));
    int rank = rref(ech, H->cnt, n, piv);
    int ok = 1;
    for (int i = 0; i < A->cnt && ok; ++i)
        for (int j = 0; j < B->cnt && ok; ++j) {
            for (int p = 0; p < n; ++p) prod[p] = gmul(A->v[(size_t)i * n + p], B->v[(size_t)j * n + p]);
            for (int r = 0; r < rank; ++r) {
                GF f = prod[piv[r]];
                if (!f) continue;
                for (int p = 0; p < n; ++p) prod[p] ^= gmul(f, ech[(size_t)r * n + p]);
            }
            for (int p = 0; p < n; ++p)
                if (prod[p]) { fprintf(stderr, "A*B row-space test failed at pair (%d,%d).\n", i, j); ok = 0; break; }
        }
    free(ech); free(prod); free(piv);
    return ok;
}

/* ---------------- decoder (basic algorithm) ---------------- */
typedef struct { int dimk; GF *ker; int nz; int *Z; } Report;

static int solve_rows(const Code *c, const GF *S, const int *Z, int nz, long total, long nsel, GF *sol)
{
    int n = c->n, K2 = c->B.cnt, cols = nz + 1;
    GF *aug = calloc((size_t)nsel * cols + 1, sizeof(GF));
    int *piv = malloc(sizeof(int) * (nsel + 1));
    for (long r = 0; r < nsel; ++r) {
        long idx = (nsel == total) ? r : (long)(rnd() % (uint64_t)total);
        int i = (int)(idx / K2), j = (int)(idx % K2);
        for (int k = 0; k < nz; ++k)
            aug[(size_t)r * cols + k] = gmul(c->A.v[(size_t)i * n + Z[k]], c->B.v[(size_t)j * n + Z[k]]);
        aug[(size_t)r * cols + nz] = S[(size_t)i * K2 + j];
    }
    int rank = rref(aug, (int)nsel, cols, piv);
    int good = (rank == nz);
    for (int r = 0; r < rank && good; ++r)
        if (piv[r] == nz) good = 0;
    if (good) for (int k = 0; k < nz; ++k) sol[k] = aug[(size_t)k * cols + nz];
    free(aug); free(piv);
    return good;
}

static int decode(const Code *c, const GF *rcv, GF *out, int *nerr, Report *rep)
{
    int n = c->n, K1 = c->A.cnt, K2 = c->B.cnt, ok = 0;
    GF *S = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *ST = calloc((size_t)K1 * K2 + 1, sizeof(GF));
    GF *AR = malloc((size_t)n * sizeof(GF) + 1);
    int *NZP = malloc(sizeof(int) * (size_t)(n + 1));
    int allzero = 1, nnz = 0;
    *nerr = 0;
    memcpy(out, rcv, (size_t)n * sizeof(GF));
    for (int p = 0; p < n; ++p) if (rcv[p]) NZP[nnz++] = p;
    for (int i = 0; i < K1; ++i) {
        for (int s2 = 0; s2 < nnz; ++s2) AR[s2] = gmul(rcv[NZP[s2]], c->A.v[(size_t)i * n + NZP[s2]]);
        for (int j = 0; j < K2; ++j) {
            GF z = 0;
            for (int s2 = 0; s2 < nnz; ++s2) z ^= gmul(AR[s2], c->B.v[(size_t)j * n + NZP[s2]]);
            S[(size_t)i * K2 + j] = z;
            ST[(size_t)j * K1 + i] = z;
            if (z) allzero = 0;
        }
    }
    if (allzero) { ok = in_code(c, rcv); goto done; }
    {
        int dimk;
        GF *ker = nullspace(ST, K2, K1, &dimk);
        if (dimk == 0) { free(ker); goto done; }
        int *Z = malloc(sizeof(int) * (size_t)(n + 1));
        int nz = 0;
        for (int p = 0; p < n; ++p) {
            int common = 1;
            for (int v = 0; v < dimk && common; ++v) {
                GF z = 0;
                for (int i = 0; i < K1; ++i) z ^= gmul(ker[(size_t)v * K1 + i], c->A.v[(size_t)i * n + p]);
                if (z) common = 0;
            }
            if (common) Z[nz++] = p;
        }
        if (rep) {
            rep->dimk = dimk;
            rep->ker = malloc((size_t)dimk * K1 * sizeof(GF) + 1);
            memcpy(rep->ker, ker, (size_t)dimk * K1 * sizeof(GF));
            rep->nz = nz;
            rep->Z = malloc(sizeof(int) * (nz + 1));
            memcpy(rep->Z, Z, sizeof(int) * nz);
        }
        free(ker);
        if (nz == 0 || (long)nz > (long)K1 * K2) { free(Z); goto done; }
        long total = (long)K1 * K2, nsel = 3L * nz + 64;
        if (nsel > total) nsel = total;
        GF *sol = malloc(sizeof(GF) * (nz + 1));
        int good = solve_rows(c, S, Z, nz, total, nsel, sol);
        if (!good && nsel < total) good = solve_rows(c, S, Z, nz, total, total, sol);
        if (good) {
            for (int k = 0; k < nz; ++k) out[Z[k]] ^= sol[k];
            if (in_code(c, out)) {
                ok = 1;
                for (int k = 0; k < nz; ++k) if (sol[k]) ++*nerr;
            }
        }
        free(sol); free(Z);
    }
done:
    free(S); free(ST); free(AR); free(NZP);
    return ok;
}

/* ---------------- report ---------------- */
static void show_locator(const Code *c, const Report *rep, const int *errpos, int nerrpos, int nloc)
{
    int n = c->n, K1 = c->A.cnt;
    printf("\n==== Error locator polynomial ====\n");
    if (!rep->ker || rep->dimk == 0) { printf("(no locator found: kernel is empty)\n"); return; }
    int show = rep->dimk < nloc ? rep->dimk : nloc;
    for (int v = 0; v < show; ++v) {
        const GF *co = rep->ker + (size_t)v * K1;
        int hi = -1, terms = 0, zeros = 0, allerr = 1;
        for (int i = 0; i < K1; ++i) if (co[i]) { hi = i; ++terms; }
        if (hi < 0) continue;
        GF inv = ginv(co[hi]);
        for (int p = 0; p < n; ++p) {
            GF z = 0;
            for (int i = 0; i <= hi; ++i) z ^= gmul(co[i], c->A.v[(size_t)i * n + p]);
            if (!z) ++zeros;
        }
        for (int k = 0; k < nerrpos; ++k) {
            GF z = 0;
            for (int i = 0; i <= hi; ++i) z ^= gmul(co[i], c->A.v[(size_t)i * n + errpos[k]]);
            if (z) allerr = 0;
        }
        if (v == 0) printf("Sigma(x,u) = monic function of minimal pole order vanishing at the error positions\n");
        else printf("\n(kernel element #%d, for reference)\n", v + 1);
        printf("pole order of Sigma = %d, %d terms, g = primitive element of GF(2^%d)\n", c->A.w[hi], terms, 0 + (int)(LOGT[2] == 1 ? 0 : 0) + 0);
        int first = 1;
        for (int i = hi; i >= 0; --i) {
            if (!co[i]) continue;
            printf("%s", first ? "   " : " + ");
            pe(gmul(co[i], inv));
            printf(" * x^%d * u^%d   (pole order %d)\n", c->A.ei[i], c->A.ej[i], c->A.w[i]);
            first = 0;
        }
        printf("  -> vanishes at %d of %d rational points; vanishes at all decoded error positions: %s\n",
               zeros, n, allerr ? "yes" : "NO");
    }
    printf("\n(kernel dimension = %d; common zero set |Z| = %d points contains the error positions)\n", rep->dimk, rep->nz);
}

static void show_errors(const Code *c, const Point *pts, const GF *rcv, const GF *dec, const GF *err, int decoded_ok)
{
    int n = c->n, nd = 0, nt = 0, wrong = 0, row = 0;
    printf("\n==== Error list ====\n");
    printf("%5s %6s  %-10s %-10s  %-12s %-12s %s\n", "#", "pos", "x", "u", "decoded e", "injected e", "check");
    for (int p = 0; p < n; ++p) {
        GF ed = decoded_ok ? (GF)(rcv[p] ^ dec[p]) : 0, et = err[p];
        if (!ed && !et) continue;
        ++row;
        if (ed) ++nd;
        if (et) ++nt;
        int match = (ed == et);
        if (!match) ++wrong;
        char sd[24], st[24], sx[24], su[24];
        if (ed) snprintf(sd, sizeof sd, "g^%d", LOGT[ed]); else snprintf(sd, sizeof sd, "0");
        if (et) snprintf(st, sizeof st, "g^%d", LOGT[et]); else snprintf(st, sizeof st, "0");
        if (pts[p].x) snprintf(sx, sizeof sx, "g^%d", LOGT[pts[p].x]); else snprintf(sx, sizeof sx, "0");
        if (pts[p].u) snprintf(su, sizeof su, "g^%d", LOGT[pts[p].u]); else snprintf(su, sizeof su, "0");
        printf("%5d %6d  %-10s %-10s  %-12s %-12s %s\n", row, p, sx, su, sd, st,
               match ? "OK" : (ed ? (et ? "WRONG VALUE" : "FALSE POSITIVE") : "MISSED"));
    }
    printf("decoded errors = %d, injected errors = %d, mismatching rows = %d\n", nd, nt, wrong);
}

static int parse_int(const char *s, int *v)
{
    char *e = NULL;
    long x = strtol(s, &e, 10);
    if (!s[0] || !e || *e || x < 0 || x > 1000000) return 0;
    *v = (int)x;
    return 1;
}

static int read_curve_file(const char *path)
{
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); return 0; }
    char line[256];
    while (fgets(line, sizeof line, f)) {
        int ex, eu, ez, co;
        if (line[0] == '#' || line[0] == '\n') continue;
        if (sscanf(line, "%d %d %d %d", &ex, &eu, &ez, &co) == 4) {
            if (ez != 0) { fprintf(stderr, "Third column must be 0 (only x,u supported).\n"); fclose(f); return 0; }
        } else if (sscanf(line, "%d %d %d", &ex, &eu, &co) != 3) {
            fprintf(stderr, "Bad line: %s", line); fclose(f); return 0;
        }
        if (co < 0 || co >= GQ) { fprintf(stderr, "Coefficient %d not in GF(2^m).\n", co); fclose(f); return 0; }
        add_term(ex, eu, (GF)co);
    }
    fclose(f);
    return 1;
}

int main(int argc, char **argv)
{
    int m = 6, errors = 1, seed = 1, trials = 1, list = 1, locator = 1, fast = 0, m1 = -1, m2 = -1;
    const char *curve = "hermitian", *file = NULL;
    for (int i = 1; i < argc; ++i) {
        int *dst = NULL;
        if (!strcmp(argv[i], "--m")) dst = &m;
        else if (!strcmp(argv[i], "--errors")) dst = &errors;
        else if (!strcmp(argv[i], "--seed")) dst = &seed;
        else if (!strcmp(argv[i], "--trials")) dst = &trials;
        else if (!strcmp(argv[i], "--list")) dst = &list;
        else if (!strcmp(argv[i], "--locator")) dst = &locator;
        else if (!strcmp(argv[i], "--fast")) dst = &fast;
        else if (!strcmp(argv[i], "--m1")) dst = &m1;
        else if (!strcmp(argv[i], "--m2")) dst = &m2;
        else if (!strcmp(argv[i], "--curve") || !strcmp(argv[i], "--file")) {
            if (i + 1 >= argc) { fprintf(stderr, "Missing value for %s\n", argv[i]); return 2; }
            if (!strcmp(argv[i], "--curve")) curve = argv[i + 1]; else file = argv[i + 1];
            ++i; continue;
        } else if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
            printf("One-point AG code decoder (basic algorithm/ECP) for C_ab curves over GF(2^m), m<=%d\n"
                   "Usage: %s --m M --curve hermitian|file [--file PATH] --errors E [--trials N --seed S]\n"
                   "          [--m1 A --m2 B] [--fast 1] [--list 0|1] [--locator N]\n"
                   "  hermitian: u^q + u = x^(q+1) over GF(q^2), needs even M\n"
                   "  file: lines 'ex eu coef' or 'ex eu 0 coef' (coef = GF element as integer)\n",
                   MAX_M, argv[0]);
            return 0;
        } else { fprintf(stderr, "Unknown option: %s\n", argv[i]); return 2; }
        if (i + 1 >= argc) { fprintf(stderr, "Missing value for %s (write e.g. %s 1)\n", argv[i], argv[i]); return 2; }
        if (!parse_int(argv[++i], dst)) { fprintf(stderr, "Bad value '%s' for %s\n", argv[i], argv[i - 1]); return 2; }
    }
    if (errors < 1 || trials < 1) { fprintf(stderr, "--errors and --trials must be >= 1.\n"); return 2; }
    if (!gf_init(m)) { fprintf(stderr, "GF(2^%d) not supported (2..%d).\n", m, MAX_M); return 2; }

    if (!strcmp(curve, "hermitian")) {
        if (m & 1) { fprintf(stderr, "hermitian needs even --m (field GF(q^2)).\n"); return 2; }
        int q = 1 << (m / 2);
        add_term(0, q, 1); add_term(0, 1, 1); add_term(q + 1, 0, 1);
    } else if (!strcmp(curve, "file")) {
        if (!file) { fprintf(stderr, "--curve file needs --file PATH\n"); return 2; }
        if (!read_curve_file(file)) return 2;
    } else { fprintf(stderr, "Unknown curve '%s'\n", curve); return 2; }
    if (!analyze_curve()) return 2;
    int g = (CA - 1) * (CB - 1) / 2;

    size_t pcap = 1024, pn = 0;
    Point *pts = malloc(pcap * sizeof(*pts));
    for (int x = 0; x < GQ; ++x)
        for (int u = 0; u < GQ; ++u) {
            if (feval((GF)x, (GF)u)) continue;
            GF fx, fu;
            fgrad((GF)x, (GF)u, &fx, &fu);
            if (!fx && !fu) { fprintf(stderr, "Curve is singular at rational point (x=%d,u=%d); not supported.\n", x, u); return 2; }
            if (pn == pcap) { pcap *= 2; pts = realloc(pts, pcap * sizeof(*pts)); }
            pts[pn++] = (Point){(GF)x, (GF)u};
        }
    int n = (int)pn;
    printf("C_ab curve over GF(2^%d): deg_u F = a = %d (= pole order of x), deg_x F = b = %d (= pole order of u)\n", m, CA, CB);
    printf("F(x,u) =");
    for (int t = 0; t < NT; ++t) if (TERMS[t].c) { printf(" + "); pe(TERMS[t].c); printf("*x^%d*u^%d", TERMS[t].ex, TERMS[t].eu); }
    printf("\ngenus g = (a-1)(b-1)/2 = %d; affine rational points n = %d (+1 point at infinity)\n", g, n);
    if (errors > n) { fprintf(stderr, "--errors exceeds n.\n"); return 2; }

    if (m1 < 0 || m2 < 0) {
        m2 = 2 * g - 1 + errors;
        m1 = 0;
        while (count_l(m1) < errors + 1) ++m1;
        printf("auto: m1=%d, m2=%d (for %d errors)\n", m1, m2, errors);
    }
    Code code; code.n = n;
    code.A = build_basis(m1, pts, n);
    code.B = build_basis(m2, pts, n);
    code.H = (Basis){0, NULL, NULL, NULL, NULL};
    GF *ker = NULL; int cdim = 0;
    if (!fast) {
        code.H = build_basis(m1 + m2, pts, n);
        if (!verify_product(&code.A, &code.B, &code.H, n)) { fprintf(stderr, "A*B subset H verification failed.\n"); return 1; }
        printf("A*B subset H: verified (%d x %d basis products).\n", code.A.cnt, code.B.cnt);
        ker = nullspace(code.H.v, code.H.cnt, n, &cdim);
        if (cdim <= 0) { fprintf(stderr, "Code dimension is zero: reduce --errors or use --fast 1.\n"); return 1; }
        printf("Dimensions: l(A)=%d, l(B)=%d, l(A+B)=%d; dim(C)=%d, n=%d\n", code.A.cnt, code.B.cnt, code.H.cnt, cdim, n);
    } else {
        printf("fast mode: zero codeword, H/verification skipped.\n");
        printf("Dimensions: l(A)=%d, l(B)=%d, n=%d\n", code.A.cnt, code.B.cnt, n);
    }
    int guarantee = (m2 > 2 * g - 2) ? m2 - 2 * g + 1 : 0;
    if (code.A.cnt - 1 < guarantee) guarantee = code.A.cnt - 1;
    printf("ECP bound estimate: errors <= %d\n", guarantee);
    if (errors > guarantee) printf("Warning: requested errors (%d) exceed the estimate; decoding may fail.\n", errors);

    rng_state = (uint64_t)(unsigned)seed * 0x2545F4914F6CDD1DULL + 12345;
    GF *cw = calloc((size_t)n, sizeof(GF)), *rcv = malloc((size_t)n * sizeof(GF));
    GF *err = calloc((size_t)n, sizeof(GF)), *dec = malloc((size_t)n * sizeof(GF));
    int *idx = malloc(sizeof(int) * (size_t)n);
    int succ = 0, fail = 0, miscor = 0;
    for (int tr = 0; tr < trials; ++tr) {
        memset(cw, 0, (size_t)n * sizeof(GF));
        for (int k = 0; k < cdim; ++k) {
            GF co = (GF)(rnd() % (uint64_t)GQ);
            for (int p = 0; p < n; ++p) cw[p] ^= gmul(co, ker[(size_t)k * n + p]);
        }
        memset(err, 0, (size_t)n * sizeof(GF));
        for (int p = 0; p < n; ++p) idx[p] = p;
        for (int e = 0; e < errors; ++e) {
            int j = e + (int)(rnd() % (uint64_t)(n - e));
            int z = idx[e]; idx[e] = idx[j]; idx[j] = z;
            err[idx[e]] = (GF)(1 + rnd() % (uint64_t)(GQ - 1));
        }
        for (int p = 0; p < n; ++p) rcv[p] = cw[p] ^ err[p];
        Report rep = {0, NULL, 0, NULL};
        int ne = 0, ok = decode(&code, rcv, dec, &ne, &rep), same = ok && !memcmp(cw, dec, (size_t)n * sizeof(GF));
        if (same) succ++; else if (ok) miscor++; else fail++;
        if (trials == 1) printf("Decode: %s (injected=%d, recovered=%d)\n", same ? "PASS" : ok ? "MISCORRECTION" : "FAIL", errors, ne);
        if (tr == 0 && (list || locator > 0)) {
            if (trials > 1) printf("--- details of trial 1: %s (injected=%d, recovered=%d) ---\n", same ? "PASS" : ok ? "MISCORRECTION" : "FAIL", errors, ne);
            int *ep = malloc(sizeof(int) * (size_t)(n + 1)), nep = 0;
            for (int p = 0; p < n; ++p) if (ok && (rcv[p] ^ dec[p])) ep[nep++] = p;
            if (locator > 0) show_locator(&code, &rep, ep, nep, locator);
            if (list) show_errors(&code, pts, rcv, dec, err, ok);
            free(ep);
        }
        free(rep.ker); free(rep.Z);
    }
    if (trials > 1) printf("%d trials: success=%d, miscorrection=%d, failure=%d\n", trials, succ, miscor, fail);
    free(cw); free(rcv); free(err); free(dec); free(idx); free(ker); free(pts);
    free_basis(&code.A); free_basis(&code.B); free_basis(&code.H);
    return fail || miscor ? 1 : 0;
}