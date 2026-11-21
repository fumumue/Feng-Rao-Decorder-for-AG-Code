/* ============================================================
 * mkbase2: Newton多角形に基づく一点符号 L(mP) の基底
 * ============================================================ */
#define MK2_MAXW 4096
#define MK2_MAXC 48
#define MK2_MAXE 40

typedef struct { int w, i, j; } Mono2;

typedef struct {
    int ok, laurent, pole;
    int px, py;
    int edge_len, genus;
    int ncons, cx[MK2_MAXC], cy[MK2_MAXC];
    int nedge, enx[MK2_MAXE], eny[MK2_MAXE], elen[MK2_MAXE];
} MK2Info;

static MK2Info mk2;
static int g_mk2_sx = 0, g_mk2_sy = 0;

static int igcd(int a, int b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int floor_div(int a, int b) /* floor(a/b), b>0 */
{
    int q = a / b;
    if ((a % b) && (a < 0)) --q;
    return q;
}

static int cross3(const int *o, const int *a, const int *b)
{
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0]);
}

static int hull_ccw(int P[][2], int n, int H[][2])
{
    int k = 0;
    for (int i = 0; i < n; ++i) {
        while (k >= 2 && cross3(H[k-2], H[k-1], P[i]) <= 0) --k;
        H[k][0] = P[i][0]; H[k][1] = P[i][1]; ++k;
    }
    for (int i = n - 2, t = k + 1; i >= 0; --i) {
        while (k >= t && cross3(H[k-2], H[k-1], P[i]) <= 0) --k;
        H[k][0] = P[i][0]; H[k][1] = P[i][1]; ++k;
    }
    return k - 1;
}

/* a*i + b*j + c >= 0 を j について解いた整数区間。実数として空なら -1 */
static int mk2_jrange(int i, int maxw, int *lo, int *hi, int *real_empty)
{
    long jl = -(1L << 40), jh = (1L << 40);
    double rl = -1e18, rh = 1e18;
    *real_empty = 0;

    for (int c = 0; c <= mk2.ncons; ++c) {
        long a, b, k;
        if (c < mk2.ncons) { a = mk2.cx[c]; b = mk2.cy[c]; k = 0; }
        else               { a = mk2.px;    b = mk2.py;    k = maxw; }
        long v = a * i + k;
        if (b == 0) {
            if (v < 0) { *real_empty = 1; return 0; }
        } else if (b > 0) {
            long l = -floor_div((int)v, (int)b);          /* ceil(-v/b) */
            if (l > jl) jl = l;
            double r = -(double)v / (double)b;
            if (r > rl) rl = r;
        } else {
            long h = floor_div((int)v, (int)(-b));        /* floor(v/(-b)) */
            if (h < jh) jh = h;
            double r = (double)v / (double)(-b);
            if (r < rh) rh = r;
        }
    }
    if (rl > rh + 1e-9) { *real_empty = 1; return 0; }
    *lo = (int)jl; *hi = (int)jh;
    return jl <= jh;
}

static int mono_cmp(const void *a, const void *b)
{
    const Mono2 *x = a, *y = b;
    if (x->w != y->w) return x->w - y->w;
    return y->i - x->i;
}

/* 重み <= maxw の錐内の格子点を重み昇順に列挙。out=NULLなら個数のみ。
 * 戻り値: 個数, 容量超過 -1, 錐が有界でない -2 */
static int mk2_enum(Mono2 *out, int cap, int maxw)
{
    int n = 0;
    for (int dir = 0; dir < 2; ++dir) {
        for (int i = dir ? -1 : 0; ; i += dir ? -1 : 1) {
            if (i > (1 << 15) || i < -(1 << 15)) return -2;
            int lo = 0, hi = -1, re;
            int ok = mk2_jrange(i, maxw, &lo, &hi, &re);
            if (re) break;
            if (!ok) continue;
            for (int j = lo; j <= hi; ++j) {
                if (out) {
                    if (n >= cap) return -1;
                    out[n].i = i; out[n].j = j;
                    out[n].w = -(mk2.px * i + mk2.py * j);
                }
                ++n;
            }
        }
    }
    if (out) qsort(out, (size_t)n, sizeof(*out), mono_cmp);
    return n;
}

static void mk2_select(int e)
{
    mk2.pole = e;
    mk2.px = mk2.enx[e];
    mk2.py = mk2.eny[e];
    mk2.edge_len = mk2.elen[e];
    mk2.laurent = !(mk2.px < 0 && mk2.py < 0);
    mk2.ncons = 0;
    for (int k = 0; k < mk2.nedge && mk2.ncons < MK2_MAXC - 2; ++k)
        if (k != e) {
            mk2.cx[mk2.ncons] = mk2.enx[k];
            mk2.cy[mk2.ncons] = mk2.eny[k];
            ++mk2.ncons;
        }
    if (!mk2.laurent) {
        mk2.cx[mk2.ncons] = 1; mk2.cy[mk2.ncons] = 0; ++mk2.ncons;
        mk2.cx[mk2.ncons] = 0; mk2.cy[mk2.ncons] = 1; ++mk2.ncons;
    }
}

/* 一点符号として妥当か: [0,2g-1] にちょうど g 個の異なる重みがあるか */
static int mk2_valid(void)
{
    int g = mk2.genus;
    if (g <= 0) return 1;
    int lim = 2 * g - 1;
    int n = mk2_enum(NULL, 0, lim);
    if (n <= 0) return 0;
    Mono2 *m = malloc((size_t)n * sizeof(*m));
    char *seen = calloc((size_t)lim + 1, 1);
    if (!m || !seen) { free(m); free(seen); return 0; }
    int r = mk2_enum(m, n, lim), cnt = 0;
    if (r == n)
        for (int k = 0; k < n; ++k)
            if (m[k].w >= 0 && m[k].w <= lim && !seen[m[k].w]) {
                seen[m[k].w] = 1;
                ++cnt;
            }
    free(m); free(seen);
    return r == n && cnt == g;
}

/* force_pole < 0: 自動選択(格子長1の辺のうち妥当なもの。多項式で済む辺を優先) */
static int mk2_init(int force_pole)
{
    int P[16][2], n = 0;
    for (int s = 0; s < curve->nterms; ++s) {
        int i = curve->t[s][0], j = curve->t[s][1], dup = 0;
        for (int k = 0; k < n; ++k)
            if (P[k][0] == i && P[k][1] == j) dup = 1;
        if (!dup && n < 16) { P[n][0] = i; P[n][1] = j; ++n; }
    }
    for (int a = 1; a < n; ++a) {
        int x = P[a][0], y = P[a][1], b = a - 1;
        while (b >= 0 && (P[b][0] > x || (P[b][0] == x && P[b][1] > y))) {
            P[b+1][0] = P[b][0]; P[b+1][1] = P[b][1]; --b;
        }
        P[b+1][0] = x; P[b+1][1] = y;
    }

    int Hl[2 * 16 + 2][2];
    int h = n >= 3 ? hull_ccw(P, n, Hl) : 0;
    if (h < 3 || h > MK2_MAXE) return 0;

    memset(&mk2, 0, sizeof mk2);
    int area2 = 0, bd = 0;
    mk2.nedge = h;
    for (int e = 0; e < h; ++e) {
        const int *a = Hl[e], *b = Hl[(e + 1) % h];
        int dx = b[0] - a[0], dy = b[1] - a[1], g = igcd(dx, dy);
        mk2.enx[e] = -dy / g;
        mk2.eny[e] =  dx / g;
        mk2.elen[e] = g;
        area2 += a[0]*b[1] - a[1]*b[0];
        bd += g;
    }
    mk2.genus = (area2 - bd + 2) / 2;

    int best = -1, best_poly = 0;
    for (int e = 0; e < h; ++e) {
        if (force_pole >= 0 && e != force_pole) continue;
        if (force_pole < 0 && mk2.elen[e] != 1) continue;
        mk2_select(e);
        int valid = mk2_valid();
        if (g_verbose)
            fprintf(stderr, "mkbase2: edge %d v=(%d,%d) len=%d -> %s\n",
                    e, mk2.enx[e], mk2.eny[e], mk2.elen[e],
                    valid ? "valid one-point basis" : "not valid");
        if (!valid) continue;
        int poly = !mk2.laurent;
        if (best < 0 || (poly && !best_poly)) { best = e; best_poly = poly; }
    }
    if (best < 0) return 0;
    mk2_select(best);
    mk2.ok = 1;
    return 1;
}

/* 錐内の重み<=maxw の最小指数から、全指数を非負にするシフトを求める */
static int mk2_natural_shift(int maxw, int *sx, int *sy)
{
    *sx = *sy = 0;
    if (!mk2.laurent) return 1;
    int n = mk2_enum(NULL, 0, maxw);
    if (n <= 0) return 0;
    Mono2 *m = malloc((size_t)n * sizeof(*m));
    if (!m) return 0;
    if (mk2_enum(m, n, maxw) != n) { free(m); return 0; }
    for (int k = 0; k < n; ++k) {
        if (-m[k].i > *sx) *sx = -m[k].i;
        if (-m[k].j > *sy) *sy = -m[k].j;
    }
    free(m);
    return 1;
}

/* A, B に同じシフト s, H に 2s を使う。A*B ⊂ H が保たれる */
static int mk2_set_shift(int da, int db)
{
    int ax, ay, bx, by, hx, hy;
    if (!mk2_natural_shift(da, &ax, &ay) ||
        !mk2_natural_shift(db, &bx, &by) ||
        !mk2_natural_shift(da + db, &hx, &hy))
        return 0;
    int sx = ax > bx ? ax : bx, sy = ay > by ? ay : by;
    if (2 * sx < hx) sx = (hx + 1) / 2;
    if (2 * sy < hy) sy = (hy + 1) / 2;
    g_mk2_sx = sx; g_mk2_sy = sy;
    return 1;
}

/* Laurent基底はシフトで x^sx y^sy 倍するので x=0, y=0 の点は除く */
static int mk2_filter_points(void)
{
    if (!mk2.laurent) return nD;
    int k = 0;
    for (int p = 0; p < nD; ++p)
        if (D[p].x && D[p].y) D[k++] = D[p];
    nD = k;
    return nD;
}

static int mk2_count(int maxw)
{
    int n = mk2_enum(NULL, 0, maxw);
    return n < 0 ? 0 : n;
}

/* shift_mult=1: A,B 用, 2: H 用 */
static int build_mk2_basis(int maxw, int shift_mult, EvalBasis *out)
{
    memset(out, 0, sizeof(*out));
    int n = mk2_enum(NULL, 0, maxw);
    if (n <= 0 || n > MAX_MONOMIALS) return 0;

    Mono2 *m = malloc((size_t)n * sizeof(*m));
    int (*lst)[2] = malloc((size_t)n * sizeof(*lst));
    if (!m || !lst || mk2_enum(m, n, maxw) != n) {
        free(m); free(lst);
        return 0;
    }
    int sx = g_mk2_sx * shift_mult, sy = g_mk2_sy * shift_mult;
    for (int k = 0; k < n; ++k) {
        lst[k][0] = m[k].i + sx;
        lst[k][1] = m[k].j + sy;
        if (lst[k][0] < 0 || lst[k][1] < 0) {
            free(m); free(lst);
            return 0;
        }
    }
    int r = build_basis_from_list(lst, n, out);
    free(m); free(lst);
    return r;
}