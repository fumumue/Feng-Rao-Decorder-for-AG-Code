/*
 * bbgs_opt.c
 *
 * Search BBGS plane curves over GF(2^m), maximizing n/g.
 *
 * The curve terms are generated exactly as in the BBGS branch of fr_simd.c:
 *   X^(q^(c-1))
 *   + sum_{k=0}^{b-1} X^(q^(c-1)-q^k) Y^(q^(a+k))
 *   + sum_{k=0}^{a-1} X^(q^(c-1)-q^(b+k)) Y^(q^k) = 0,
 * where c=a+b, gcd(a,b)=1, q=2^(m/c), and q^c=2^m.
 *
 * Genus: interior lattice-point count of the Newton polygon (Pick's theorem),
 * under the same nondegenerate Newton-polygon assumption used by fr_simd.c.
 * n: exact number of affine GF(2^m)-rational solutions, counted directly.
 *
 * Build: cc -O3 -std=c11 -Wall -Wextra -o bbgs_opt bbgs_opt.c
 * Run:   ./bbgs_opt --m 12 --poly 0x1053
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define MAXTERM 64
#define MAXM 12

typedef struct { int x, y; } Point;
typedef struct {
    int a, b, c, q, m, terms, max_edge;
    uint64_t genus, n;
    double ratio;
} Candidate;

static int M, FS, FO;
static unsigned POLY;
static uint16_t *exptab, *logtab;

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int gf_init(int m, unsigned poly) {
    M = m; FS = 1 << m; FO = FS - 1; POLY = poly;
    exptab = malloc((size_t)(2 * FO + 2) * sizeof(*exptab));
    logtab = malloc((size_t)FS * sizeof(*logtab));
    if (!exptab || !logtab) return -1;
    unsigned x = 1;
    for (int i = 0; i < FO; ++i) {
        if (i && x == 1) return -1;
        exptab[i] = (uint16_t)x;
        logtab[x] = (uint16_t)i;
        x <<= 1;
        if (x & (unsigned)FS) x ^= poly;
    }
    if (x != 1) return -1;
    for (int i = FO; i < 2 * FO + 2; ++i)
        exptab[i] = exptab[i - FO];
    logtab[0] = 0;
    return 0;
}
static inline uint16_t gf_mul(uint16_t a, uint16_t b) {
    return (a && b) ? exptab[logtab[a] + logtab[b]] : 0;
}
static uint16_t gf_pow_u(uint16_t a, unsigned e) {
    if (!e) return 1;
    if (!a) return 0;
    return exptab[((uint64_t)logtab[a] * e) % FO];
}
static long long cross(Point a, Point b, Point c) {
    return (long long)(b.x-a.x)*(c.y-a.y)
         - (long long)(b.y-a.y)*(c.x-a.x);
}
static int cmp_point(const void *aa, const void *bb) {
    const Point *a = aa, *b = bb;
    if (a->x != b->x) return (a->x > b->x) - (a->x < b->x);
    return (a->y > b->y) - (a->y < b->y);
}

/* Returns genus by Pick's theorem and maximum lattice length of an edge. */
static uint64_t polygon_genus(const Point *p, int n, int *max_edge) {
    Point s[2 * MAXTERM], h[2 * MAXTERM];
    memcpy(s, p, (size_t)n * sizeof(Point));
    qsort(s, n, sizeof(Point), cmp_point);
    int ns = 0;
    for (int i = 0; i < n; ++i)
        if (!ns || s[i].x != s[ns-1].x || s[i].y != s[ns-1].y)
            s[ns++] = s[i];

    int k = 0;
    for (int i = 0; i < ns; ++i) {
        while (k >= 2 && cross(h[k-2], h[k-1], s[i]) <= 0) --k;
        h[k++] = s[i];
    }
    int lower = k;
    for (int i = ns - 2; i >= 0; --i) {
        while (k > lower && cross(h[k-2], h[k-1], s[i]) <= 0) --k;
        h[k++] = s[i];
    }
    if (k <= 3) return 0;
    --k;

    long long area2 = 0;
    uint64_t boundary = 0;
    int me = 0;
    for (int i = 0; i < k; ++i) {
        Point u = h[i], v = h[(i+1)%k];
        area2 += (long long)u.x*v.y - (long long)v.x*u.y;
        int dx = abs(v.x-u.x), dy = abs(v.y-u.y);
        int el = gcd_int(dx, dy);
        boundary += (unsigned)el;
        if (el > me) me = el;
    }
    if (area2 < 0) area2 = -area2;
    if (max_edge) *max_edge = me;
    /* I = (2A - B + 2)/2 */
    return (uint64_t)((area2 - (long long)boundary + 2) / 2);
}

static int make_terms(int q, int a, int b, int *xe, int *ye) {
    int c = a + b;
    int qp[16];
    qp[0] = 1;
    for (int i = 1; i <= c; ++i) qp[i] = qp[i-1] * q;
    int t = 0;
    xe[t] = qp[c-1]; ye[t++] = 0;
    for (int j = 0; j < b; ++j) {
        xe[t] = qp[c-1] - qp[j];
        ye[t++] = qp[a+j];
    }
    for (int j = 0; j < a; ++j) {
        xe[t] = qp[c-1] - qp[b+j];
        ye[t++] = qp[j];
    }
    return t;
}

/* Exact affine point count, matching the point enumeration in fr_simd.c. */
static uint64_t count_affine_points(int terms, const int *xe, const int *ye) {
    uint16_t *yp = malloc((size_t)terms * FS * sizeof(uint16_t));
    uint16_t *xp = malloc((size_t)terms * FS * sizeof(uint16_t));
    if (!yp || !xp) {
        fprintf(stderr, "out of memory in point counter\n");
        exit(2);
    }
    for (int t = 0; t < terms; ++t)
        for (int y = 0; y < FS; ++y)
            yp[(size_t)t*FS+y] = gf_pow_u((uint16_t)y, (unsigned)ye[t]);

    uint64_t count = 0;
    for (int x = 0; x < FS; ++x) {
        for (int t = 0; t < terms; ++t)
            xp[(size_t)t*FS+x] = gf_pow_u((uint16_t)x, (unsigned)xe[t]);

        for (int y = 0; y < FS; ++y) {
            uint16_t z = 0;
            for (int t = 0; t < terms; ++t)
                z ^= gf_mul(xp[(size_t)t*FS+x], yp[(size_t)t*FS+y]);
            if (!z) ++count;
        }
    }
    free(yp); free(xp);
    return count;
}

static int cmp_candidate(const void *aa, const void *bb) {
    const Candidate *a = aa, *b = bb;
    if (a->ratio < b->ratio) return 1;
    if (a->ratio > b->ratio) return -1;
    if (a->genus > b->genus) return 1;
    if (a->genus < b->genus) return -1;
    return 0;
}
static void usage(const char *p) {
    printf("Usage: %s --m M [--poly P] [--max-c C] [--edge-limit L]\n"
           "  --m M          defining field GF(2^M), 1 <= M <= 12 (required)\n"
           "  --poly P       primitive polynomial (default 0x1053 for m=12;\n"
           "                 otherwise found automatically)\n"
           "  --max-c C      maximum a+b to examine (default 12)\n"
           "  --edge-limit L show whether max Newton-edge length fits L (default 320)\n"
           "  --help         show this help\n", p);
}
int main(int argc, char **argv) {
    int m = 0, maxc = 12, edge_limit = 320;
    unsigned poly = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--m") && i+1 < argc) m = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--poly") && i+1 < argc)
            poly = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--max-c") && i+1 < argc)
            maxc = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--edge-limit") && i+1 < argc)
            edge_limit = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--help")) { usage(argv[0]); return 0; }
        else { usage(argv[0]); return 1; }
    }
    if (m < 1 || m > MAXM || maxc < 2 || maxc > 12 || edge_limit < 1) {
        usage(argv[0]); return 1;
    }
    if (!poly) {
        if (m == 12) poly = 0x1053u;
        else {
            /* Find a primitive polynomial automatically. */
            unsigned first = (1u << m) | 1u;
            unsigned last  = (1u << (m + 1)) - 1u;
            for (unsigned p = first; p <= last; p += 2) {
                if (gf_init(m, p) == 0) { poly = p; break; }
                free(exptab); free(logtab);
                exptab = logtab = NULL;
            }
            if (!poly) {
                fprintf(stderr, "could not find a primitive polynomial for m=%d\\n", m);
                return 1;
            }
        }
    }
    if (!exptab && gf_init(m, poly)) {
        fprintf(stderr, "GF(2^%d) polynomial 0x%x is not primitive/valid\\n", m, poly);
        return 1;
    }

    Candidate cand[256];
    int ncand = 0;
    for (int c = 2; c <= maxc && c <= m; ++c) {
        if (m % c) continue;       /* q^c = 2^m, q must be a power of two */
        int r = m / c;
        if (r < 1 || r > 10) continue;
        int q = 1 << r;
        for (int a = 1; a < c; ++a) {
            int b = c-a;
            if (gcd_int(a,b) != 1) continue;
            int xe[MAXTERM], ye[MAXTERM], terms = make_terms(q,a,b,xe,ye);
            Point pts[MAXTERM];
            for (int t = 0; t < terms; ++t)
                pts[t] = (Point){xe[t], ye[t]};
            int max_edge = 0;
            uint64_t g = polygon_genus(pts, terms, &max_edge);
            if (!g) continue;
            uint64_t n = count_affine_points(terms, xe, ye);
            Candidate *v = &cand[ncand++];
            *v = (Candidate){a,b,c,q,m,terms,max_edge,g,n,(double)n/(double)g};
        }
    }
    if (!ncand) {
        fprintf(stderr, "No candidates for GF(2^%d) under the requested limits.\n",m);
        return 1;
    }
    qsort(cand, ncand, sizeof(cand[0]), cmp_candidate);

    printf("# BBGS search over GF(2^%d), polynomial 0x%x\n", m, poly);
    printf("# n is exact affine-point count; g is Newton-polygon interior count.\n");
    printf("# edge_limit=%d; current decoder caps: MAXB=400000, MAXGENUS=1310006.\n", edge_limit);
    printf("# rank  q  m  a  b  c  genus_g  affine_n  n_over_g  max_edge  edge_ok  2g_fits_MAXB\n");
    for (int i = 0; i < ncand; ++i) {
        Candidate *v = &cand[i];
        printf("%-5d %-4d %-3d %-3d %-3d %-3d %-10" PRIu64 " %-12" PRIu64
               " %-14.9f %-10d %-8s %s\n",
               i+1, v->q, v->m, v->a, v->b, v->c, v->genus, v->n,
               v->ratio, v->max_edge, v->max_edge <= edge_limit ? "yes" : "no",
               (2*v->genus + 1 <= 400000 && v->genus <= 1310006) ? "yes" : "no");
    }
    printf("# best: q=%d m=%d a=%d b=%d g=%" PRIu64 " n=%" PRIu64
           " n/g=%.9f\n",
           cand[0].q, cand[0].m, cand[0].a, cand[0].b,
           cand[0].genus, cand[0].n, cand[0].ratio);
    free(exptab); free(logtab);
    return 0;
}
