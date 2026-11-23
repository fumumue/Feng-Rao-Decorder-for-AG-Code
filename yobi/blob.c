/*
 * BBGS塔 (Bassa-Beelen-Garcia-Stichtenoth) : 再帰方程式の生成, 有理点の探索, 種数と N/g の比較
 * 参考: Bassa-Beelen-Garcia-Stichtenoth, "Towers of function fields over non-prime
 *       finite fields", Moscow Math. J. 15 (2015)  (arXiv:1202.5922)
 *
 * 体: F_l,  l = q^n = p^M  (q は素数冪 q=p^e, n >= 2, M = e*n)
 * 方程式 (論文 (9) 式):  Tr_j(Y/X^(q^k)) + Tr_k(Y^(q^j)/X) = 1,   j+k=n, gcd(j,k)=1
 *          Tr_a(T) = T + T^q + ... + T^(q^(a-1))
 * 分母を払った多項式 (係数は +1 / -1 のみ):
 *   P(X,Y) = sum_{s<j} X^(q^(n-1)-q^(k+s)) Y^(q^s)
 *          + sum_{s<k} X^(q^(n-1)-q^s)     Y^(q^(j+s))
 *          - X^(q^(n-1))
 * 塔: F_1 = F_l(x_1),  F_{i+1} = F_i(x_{i+1}),  P(x_i, x_{i+1}) = 0
 *
 * 点の数 (論文 Prop 2.5, Cor 3.2):
 *   [F_{i+1}:F_i] = q^(n-1),  [F_i:F_1] = q^((n-1)(i-1)).
 *   x_1 = beta (beta in F_l^*) の place は F_i で完全分解するので、
 *   x_1,...,x_i が全て F_l^* の元で P(x_j,x_{j+1})=0 を満たす列 (x_1,...,x_i) の個数 N_i は
 *   N_i = (l-1) * q^((n-1)(i-1)) 個の「F_l 有理place」に正確に一致する。
 *   x_1 = 0, x_1 = infinity の上にも有理placeがありうるので、F_i の有理place数 N(F_i) >= N_i。
 * 種数:
 *   g(F_1)=0,  g(F_2) = ((q^n-2)(q^(j-1)+q^(k-1)-2) + (q^n-q)) / 2   (Cor 2.7, 等号)
 *   i>=3:  g(F_i) <= 1 + [F_i:F_1]/2 * ((q^n-1)/(q^k-1) + (q^n-1)/(q^j-1))   (論文 (26) 式, 上界)
 *   よって N(F_i)/g(F_i) >= N_i / g_上界。 塔の極限 lambda >= 2/(1/(q^j-1)+1/(q^k-1))。
 *   (論文は p が j を割らないと仮定している: 割る場合は警告を出す)
 *
 * コンパイル: gcc -O2 -o bbgs_tower bbgs_tower.c -lm
 * 実行:
 *   ./bbgs_tower q n [k] [levels] [list]    方程式 + 有理点の探索 + 種数と比
 *                                           k を省略 (または auto / 0) すると、F_2 が最大曲線になる k を自動選択
 *   ./bbgs_tower cube p m [levels] [list]   F_{p^{3m}} 上の塔 (q=p^m, n=3, k=2) を一発で
 *   ./bbgs_tower compare p m [levels]       F_{p^m} 上の全ての (q,n,k) を比較
 *   ./bbgs_tower maximal p m_lo [m_hi]      F_2 が最大曲線になるものだけを表示
 *   ./bbgs_tower verify q n k              論文の式(Prop 2.2,2.3,2.5, Cor 2.7)で実際に確認
 *   ./bbgs_tower best p m                   F_{p^m} 上で元を代入して数え、上界に最も近い曲線を1つ選ぶ
 *   例: ./bbgs_tower 4 3 2 3 1      GF(64), X^16+Y+X^15Y^4+X^12Y^16=0 の形
 *       ./bbgs_tower compare 2 6 4  GF(64) 上の全ての塔を比較
 *   表示: 元は 0 または a^e (a は GF(l) の原始元)。
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef unsigned long long u64;

#define MAXTERM 256
typedef struct { u64 dx, dy; int c; } term;      /* c は {1,-1} */

static u64 gcd(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

static int char_of(u64 q)
{
    for (u64 d = 2; d * d <= q; d++)
        if (q % d == 0) {
            u64 t = q;
            while (t % d == 0) t /= d;
            return t == 1 ? (int)d : -1;
        }
    return (int)q;
}

static u64 ipow(u64 q, int e)
{
    u64 r = 1;
    for (int i = 0; i < e; i++) {
        if (r > 0xFFFFFFFFFFFFFFFFULL / q) { fprintf(stderr, "指数が64bitを超えます\n"); exit(1); }
        r *= q;
    }
    return r;
}

static int build_poly(u64 q, int n, int k, term *t)
{
    int j = n - k, m = 0;
    u64 top = ipow(q, n - 1);
    for (int s = 0; s < j; s++) { t[m].dx = top - ipow(q, k + s); t[m].dy = ipow(q, s);     t[m].c = 1; m++; }
    for (int s = 0; s < k; s++) { t[m].dx = top - ipow(q, s);     t[m].dy = ipow(q, j + s); t[m].c = 1; m++; }
    t[m].dx = top; t[m].dy = 0; t[m].c = -1; m++;
    return m;
}

static void print_mono(u64 dx, u64 dy, int i)
{
    int first = 1;
    if (dx) { printf("x%d", i);     if (dx > 1) printf("^%llu", dx); first = 0; }
    if (dy) { printf("%sx%d", first ? "" : "*", i + 1); if (dy > 1) printf("^%llu", dy); first = 0; }
    if (first) printf("1");
}

/* ================= GF(p^M) : 元は M 桁の p 進整数, log/exp 表 ================= */
static int P_, M_;
static u64 L_;              /* l = p^M */
static u64 N1_;             /* l - 1  (乗法群の位数) */
static unsigned *EXP_, *LOG_;

static unsigned gf_add(unsigned a, unsigned b)
{
    if (P_ == 2) return a ^ b;
    unsigned r = 0, w = 1;
    for (int i = 0; i < M_; i++) {
        r += (unsigned)(((a % P_) + (b % P_)) % P_) * w;
        a /= P_; b /= P_; w *= P_;
    }
    return r;
}
static unsigned gf_neg(unsigned a)
{
    if (P_ == 2) return a;
    unsigned r = 0, w = 1;
    for (int i = 0; i < M_; i++) {
        r += (unsigned)((P_ - a % P_) % P_) * w;
        a /= P_; w *= P_;
    }
    return r;
}
/* a * alpha  (alpha^M = rr) */
static unsigned mul_alpha(unsigned a, unsigned rr, unsigned pM1)
{
    if (P_ == 2) { unsigned t = a >> (M_ - 1); return ((a << 1) & ((1u << M_) - 1)) ^ (t ? rr : 0); }
    unsigned top = a / pM1;                  /* 最上位桁 */
    unsigned low = (a % pM1) * P_;           /* 1桁左シフト */
    unsigned r = 0;
    /* top * rr を桁ごとに足す */
    unsigned t = rr, w = 1, add = 0;
    for (int i = 0; i < M_; i++) { add += ((t % P_) * top % P_) * w; t /= P_; w *= P_; }
    r = gf_add(low, add);
    return r;
}

/* 原始多項式を探して exp/log 表を作る。成功で 0 */
static int gf_init(int p, int M)
{
    P_ = p; M_ = M;
    L_ = 1; for (int i = 0; i < M; i++) L_ *= p;
    if (L_ > (1ULL << 24)) { fprintf(stderr, "l=%llu は大きすぎます (<= 2^24)\n", L_); return -1; }
    N1_ = L_ - 1;
    unsigned pM1 = (unsigned)(L_ / p);
    EXP_ = malloc(sizeof(unsigned) * L_);
    LOG_ = malloc(sizeof(unsigned) * L_);
    for (unsigned rr = 1; rr < L_; rr++) {   /* alpha^M = rr (rr の最下位桁 != 0) */
        if (rr % p == 0) continue;
        unsigned a = 1; u64 i;
        for (i = 0; i < N1_; i++) {
            EXP_[i] = a;
            a = mul_alpha(a, rr, pM1);
            if (a == 1) { i++; break; }
        }
        if (i == N1_ && a == 1) {            /* 位数がちょうど l-1 */
            for (u64 e = 0; e < L_; e++) LOG_[e] = 0;
            for (u64 e = 0; e < N1_; e++) LOG_[EXP_[e]] = (unsigned)e;
            return 0;
        }
    }
    return -1;
}

/* a^e (a != 0 は log、a == 0 は e==0 のとき 1) */
static unsigned gf_pow(unsigned a, u64 e)
{
    if (a == 0) return e == 0 ? 1 : 0;
    return EXP_[(u64)LOG_[a] * (e % N1_) % N1_];
}
static unsigned gf_mul(unsigned a, unsigned b)
{
    if (!a || !b) return 0;
    return EXP_[((u64)LOG_[a] + LOG_[b]) % N1_];
}
static void print_elem(unsigned a)
{
    if (a == 0) printf("0"); else printf("a^%u", LOG_[a]);
}

/* ================= 有理点の探索 ================= */
typedef struct { unsigned x, y; } edge;

/* 各 x != 0 について P(x,y) = 0 を満たす全ての y in F_l を求める。辺の個数を返す */
static u64 find_edges(const term *t, int m, edge **out)
{
    u64 cap = 1024, cnt = 0;
    edge *ed = malloc(sizeof(edge) * cap);
    unsigned *coef = malloc(sizeof(unsigned) * m);
    for (unsigned x = 1; x < L_; x++) {
        for (int a = 0; a < m; a++) {                      /* 係数 c * x^dx */
            unsigned v = gf_pow(x, t[a].dx);
            coef[a] = (t[a].c == 1) ? v : gf_neg(v);
        }
        for (unsigned y = 0; y < L_; y++) {
            unsigned s = 0;
            for (int a = 0; a < m; a++)
                s = gf_add(s, gf_mul(coef[a], gf_pow(y, t[a].dy)));
            if (s == 0) {
                if (cnt == cap) { cap *= 2; ed = realloc(ed, sizeof(edge) * cap); }
                ed[cnt].x = x; ed[cnt].y = y; cnt++;
            }
        }
    }
    free(coef);
    *out = ed;
    return cnt;
}

/* x_1,...,x_i (全て F_l^*) の列の個数 N_i を DP で求める (i = 1..levels) */
static void count_tower_points(const edge *ed, u64 ne, int levels)
{
    u64 *cur = calloc(L_, sizeof(u64)), *nxt = calloc(L_, sizeof(u64));
    u64 total = 0;
    for (unsigned x = 1; x < L_; x++) { cur[x] = 1; total++; }
    printf("N_1 = %llu  (x_1 in F_l^*)\n", total);
    for (int i = 2; i <= levels; i++) {
        memset(nxt, 0, sizeof(u64) * L_);
        for (u64 e = 0; e < ne; e++) nxt[ed[e].y] += cur[ed[e].x];
        total = 0;
        for (unsigned x = 1; x < L_; x++) total += nxt[x];
        printf("N_%d = %llu\n", i, total);
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    free(cur); free(nxt);
}


/* ================= 種数と N/g (論文の式) ================= */
typedef struct { long double deg, N, g; int exact; } stat_t;

static stat_t tower_stats(u64 q, int n, int k, int i)
{
    stat_t s;
    int j = n - k;
    long double ql = (long double)q, l = powl(ql, n);
    s.deg = powl(ql, (long double)(n - 1) * (i - 1));          /* [F_i:F_1] */
    s.N   = (l - 1) * s.deg;                                      /* x_1 != 0 上の有理place数 */
    if (i == 1) { s.g = 0; s.exact = 1; return s; }
    if (i == 2) {
        s.g = 0.5L * ((l - 2) * (powl(ql, j - 1) + powl(ql, k - 1) - 2) + (l - ql));
        s.exact = 1;
    } else {
        long double b = (l - 1) / (powl(ql, k) - 1) + (l - 1) / (powl(ql, j) - 1);
        s.g = 1 + s.deg / 2 * b;
        s.exact = 0;
    }
    return s;
}

static long double lambda_bound(u64 q, int n, int k)
{
    long double ql = (long double)q;
    return 2.0L / (1.0L / (powl(ql, n - k) - 1) + 1.0L / (powl(ql, k) - 1));
}

static void print_stats(u64 q, int n, int k, int levels)
{
    long double l = powl((long double)q, n);
    printf("\n[種数と N/g]  (論文の式による。g は i=2 のみ厳密, i>=3 は上界)\n");
    printf("  i   [F_i:F_1]       N_i(下界)         g(F_i)            N_i/g\n");
    for (int i = 1; i <= levels; i++) {
        stat_t s = tower_stats(q, n, k, i);
        if (i == 1) printf("  %-3d %-15.0Lf %-17.0Lf 0                 -\n", i, s.deg, s.N);
        else printf("  %-3d %-15.0Lf %-17.0Lf %s%-15.1Lf  %.4Lf\n", i, s.deg, s.N,
                    s.exact ? "=" : "<=", s.g, s.N / s.g);
    }
    printf("塔の極限の下界 lambda >= %.4Lf   (Drinfeld-Vladut 上界 sqrt(l)-1 = %.4Lf)\n",
           lambda_bound(q, n, k), sqrtl(l) - 1);
}

/* F_{p^m} 上の全ての (q,n,k) を比較 */
static void compare(int p, int m, int levels)
{
    u64 l = ipow(p, m);
    printf("F_%llu = F_%d^%d 上の BBGS 塔  (比較段 i=%d)\n", l, p, m, levels);
    printf("  q    n  k  j   [F2:F1]  g(F_2)     lambda下界  N_i/g_i上界比  備考\n");
    int e;
    for (e = 1; e < m; e++) {
        if (m % e) continue;
        u64 q = ipow(p, e);
        int n = m / e;
        for (int k = 1; k < n; k++) {
            if (gcd(n, k) != 1) continue;
            int j = n - k;
            stat_t s2 = tower_stats(q, n, k, 2);
            stat_t si = tower_stats(q, n, k, levels);
            printf("  %-4llu %-2d %-2d %-3d %-8.0Lf %-10.0Lf %-11.4Lf %-14.4Lf %s\n",
                   q, n, k, j, s2.deg, s2.g, lambda_bound(q, n, k),
                   levels >= 2 ? si.N / si.g : 0.0L,
                   (j % p == 0) ? "p|j (論文の仮定外)" : "");
        }
    }
    printf("lambda下界が大きい塔ほど、段を重ねたときの点数/種数の比が大きくなる。\n");
}

/* ================= 最大曲線 (F_2 = F_l(x,y)) の判定 =================
 * 最大曲線: N = l + 1 + 2 g sqrt(l)  (l が平方数でなければ起こらない)
 * F_2 の g は厳密 (Cor 2.7)。N は論文の Kummer 表示 (Prop 2.3, 2.6) から厳密に数える:
 *   F = K(x,u), x^(l-1) = c(u) = -Tr_j(u) / (Tr_k(u)+alpha)^(q^j),  alpha = j^{-1} in F_p
 *   F_l 有理place = u in F_l ごとに
 *     Tr_j(u)=0 または Tr_k(u)+alpha=0 : 完全分岐で有理place 1 個
 *     それ以外で c(u)=1                 : l-1 個 (c(u) != 1 なら有理placeなし)
 *   + [u=infinity] の上: q-1 個 (-1 が (q-1) 乗元のとき。p=2 または n 偶数)、それ以外は 0 個
 * F_i (i>=3) の判定には N(F_i) と g(F_i) の厳密値が要るので、ここでは扱わない。
 */
static void gf_free(void) { free(EXP_); free(LOG_); EXP_ = LOG_ = NULL; }

static unsigned tr_a(unsigned b, int a, const u64 *qp)
{
    unsigned r = 0;
    for (int s = 0; s < a; s++) r = gf_add(r, gf_pow(b, qp[s]));
    return r;
}

static u64 isqrt_u64(u64 x)
{
    u64 r = (u64)sqrtl((long double)x);
    while (r * r > x) r--;
    while ((r + 1) * (r + 1) <= x) r++;
    return r;
}

/* F_2 の K 有理place数を u 上の全探索で数える (gf_init 済み: K = GF(L_), L_ = l0^r, l0 = q^n)。p∤j が前提
 * 論文 Prop 2.3, 2.6: F = K(x,u),  x^(l0-1) = c(u) = -Tr_j(u)/(Tr_k(u)+alpha)^(q^j)
 *   u in K で Tr_j(u)=0 または Tr_k(u)+alpha=0 : 完全分岐, 有理place 1 個
 *   それ以外: c(u) が K^* の (l0-1) 乗元なら l0-1 個, そうでなければ 0 個
 *   [u=infinity]: q-1 個 (−1 が K^* の (q-1) 乗元のとき), それ以外 0 個 */
static u64 count_F2(int p, u64 q, int n, int k, u64 *cnt1_out)
{
    int j = n - k;
    u64 l = L_, l0 = ipow(q, n), qp[64];
    for (int s = 0; s < n && s < 64; s++) qp[s] = ipow(q, s);
    unsigned alpha = 1;
    for (int a = 1; a < p; a++) if ((u64)a * (j % p) % p == 1) alpha = a;
    u64 cnt1 = 0, nG = 0, nD = 0, ex = N1_ / (l0 - 1);
    for (unsigned b = 0; b < l; b++) {
        unsigned B = gf_add(tr_a(b, k, qp), alpha), A = tr_a(b, j, qp);
        if (B == 0) { nD++; continue; }
        if (A == 0) { nG++; continue; }
        unsigned Bq  = gf_pow(B, qp[j]);
        unsigned inv = EXP_[(N1_ - LOG_[Bq]) % N1_];
        unsigned c   = gf_neg(gf_mul(A, inv));
        if (gf_pow(c, ex) == 1) cnt1++;
    }
    u64 ninf = (gf_pow(gf_neg(1), N1_ / (q - 1)) == 1) ? q - 1 : 0;
    if (cnt1_out) *cnt1_out = cnt1;
    return (l0 - 1) * cnt1 + nG + nD + ninf;
}

static u64 genus_F2(u64 q, int n, int k)
{
    int j = n - k;
    u64 l = ipow(q, n);
    return ((l - 2) * (ipow(q, j - 1) + ipow(q, k - 1) - 2) + (l - q)) / 2;
}

static int maximal_scan(int p, int m_lo, int m_hi)
{
    int found = 0;
    printf("F_2 (塔の第1段) が最大曲線になる BBGS 曲線:  p=%d,  m=%d..%d  (l=p^m)\n", p, m_lo, m_hi);
    printf("  l        q     n  k  j   g(F_2)    N(F_2)     l+1+2g√l\n");
    for (int m = (m_lo < 2 ? 2 : m_lo); m <= m_hi; m++) {
        if (gf_init(p, m) != 0) continue;
        u64 l = L_, sq = isqrt_u64(l);
        for (int e = 1; e < m; e++) {
            if (m % e) continue;
            u64 q = ipow(p, e);
            int n = m / e;
            for (int k = 1; k < n; k++) {
                int j = n - k;
                if (gcd(n, k) != 1 || j % p == 0) continue;
                u64 cnt1, N = count_F2(p, q, n, k, &cnt1), g = genus_F2(q, n, k);
                if (cnt1 != ipow(q, n - 1)) fprintf(stderr, "(警告) #{c=1} が q^(n-1) と不一致\n");
                if (sq * sq == l && N == l + 1 + 2 * g * sq) {
                    printf("  %-8llu %-5llu %-2d %-2d %-3d %-10llu %-10llu %llu\n", l, q, n, k, j, g, N, l + 1 + 2 * g * sq);
                    found++;
                }
            }
        }
        gf_free();
    }
    if (!found) printf("  該当なし\n");
    return found;
}

/* x=0 のアフィン解の個数 (y in F_l を総当たり) */
static u64 brute_x0(const term *t, int m)
{
    u64 cnt = 0;
    for (unsigned y = 0; y < L_; y++) {
        unsigned s = 0;
        for (int a = 0; a < m; a++) {
            if (t[a].dx != 0) continue;                       /* x=0 で 0 になる項 */
            unsigned v = gf_pow(y, t[a].dy);
            s = gf_add(s, t[a].c == 1 ? v : gf_neg(v));
        }
        if (s == 0) cnt++;
    }
    return cnt;
}

/* F_{p^m} 上で、元を代入して数えた F_2 の有理点数が Serre 上界に最も近い曲線を1つ選ぶ */
static void best_curve(int p, int m)
{
    if (gf_init(p, m) != 0) { fprintf(stderr, "GF(%d^%d) を作れません\n", p, m); return; }
    u64 l = L_, serre_w = isqrt_u64(4 * l);                    /* floor(2 sqrt(l)) */
    int bq_e = 0, bn = 0, bk = 0, have = 0, ncand = 0;
    long double bratio = -1;
    u64 bN = 0, bg = 0, bS = 0, bbrute = 0;
    printf("F_%llu = F_%d^%d:  各 (q,n,k) で元を代入して F_2 の点を数え、Serre 上界 l+1+g*floor(2√l) と比較\n", l, p, m);
    printf("  q    n  k  j   g     アフィン解(x,y全探索)  有理place数N   Serre上界   N/上界\n");
    for (int e = 1; e < m; e++) {
        if (m % e) continue;
        u64 q = ipow(p, e);
        int n = m / e;
        for (int k = 1; k < n; k++) {
            int j = n - k;
            if (gcd(n, k) != 1 || j % p == 0) continue;
            term t[MAXTERM];
            int nt = build_poly(q, n, k, t);
            u64 brute = 0;
            if (l <= 4096) { edge *ed; brute = find_edges(t, nt, &ed); free(ed); brute += brute_x0(t, nt); }
            u64 cnt1, N = count_F2(p, q, n, k, &cnt1), g = genus_F2(q, n, k);
            u64 S = l + 1 + g * serre_w;
            long double r = (long double)N / S;
            printf("  %-4llu %-2d %-2d %-3d %-5llu %-22llu %-13llu %-11llu %.4Lf\n", q, n, k, j, g, brute, N, S, r);
            ncand++;
            if (r > bratio) { bratio = r; bq_e = e; bn = n; bk = k; bN = N; bg = g; bS = S; bbrute = brute; have = 1; }
        }
    }
    if (!have) { printf("該当する (q,n,k) がありません\n"); gf_free(); return; }
    u64 q = ipow(p, bq_e);
    printf("\n=> 最も上界に近い曲線 (候補 %d 個中): q=%llu, n=%d, k=%d, j=%d\n", ncand, q, bn, bk, bn - bk);
    term t[MAXTERM]; int nt = build_poly(q, bn, bk, t);
    printf("   方程式: ");
    for (int a = 0; a < nt; a++) {
        int c = (t[a].c == 1) ? 1 : p - 1;
        if (a) printf(" + ");
        if (c != 1) printf("%d*", c);
        print_mono(t[a].dx, t[a].dy, 1);
    }
    printf(" = 0\n   g(F_2)=%llu,  N(F_2)=%llu,  Serre上界=%llu,  差=%llu\n", bg, bN, bS, bS - bN);
    (void)bbrute;
    gf_free();
}

/* ================= 論文の式による検証 (verify q n k) =================
 * (A) 論文の方程式 (9) を、分母を払わず Tr_j(y/x^(q^k)) + Tr_k(y^(q^j)/x) = 1 のまま全ての
 *     x,y in F_l^* で評価し、プログラムの多項式 P(x,y)=0 と同値であることを確認
 * (B) Prop 2.5: 各 x in F_l^* に対し解 y がちょうど q^(n-1) 個で、全て F_l^* の元
 * (C) Prop 2.2/2.3: 解 (x,y) ごとに R=y/x^(q^k), S=y^(q^j)/x から u in F_l が
 *     Tr_k(u)+alpha=R, Tr_j(u)=-S で一意に定まり、x^(l-1) = -Tr_j(u)/(Tr_k(u)+alpha)^(q^j) (=1) を満たす
 * (D) Cor 2.7 の種数: F_{l^r} 上の有理place数 N_1..N_g から L 多項式を作り、
 *     関数等式で補って N_{g+1}, N_{g+2}... を予測し、実際に数えた値と比較
 */
static int verify_points(int p, u64 q, int n, int k)
{
    int j = n - k, nt, fails = 0;
    u64 l = L_, qp[64];
    if (l > 1024) { printf("(A)-(C) は l<=1024 のみ対応 (l=%llu)\n", l); return 0; }
    for (int s = 0; s < n; s++) qp[s] = ipow(q, s);
    unsigned alpha = 1;
    for (int a = 1; a < p; a++) if ((u64)a * (j % p) % p == 1) alpha = a;
    term t[MAXTERM]; nt = build_poly(q, n, k, t);

    /* (u の対応表) (Tr_k(u), Tr_j(u)) -> u+1 */
    unsigned *tab = calloc(l * l, sizeof(unsigned));
    int inj_ok = 1;
    for (unsigned u = 0; u < l; u++) {
        unsigned idx = tr_a(u, k, qp) * (unsigned)l + tr_a(u, j, qp);
        if (tab[idx]) inj_ok = 0;
        tab[idx] = u + 1;
    }
    u64 equiv_bad = 0, pts = 0, perx_bad = 0, u_missing = 0, c_bad = 0;
    for (unsigned x = 1; x < l; x++) {
        u64 ny = 0;
        for (unsigned y = 0; y < l; y++) {
            /* 論文の方程式 (9) そのまま */
            unsigned xk = gf_pow(x, qp[k]);
            unsigned R = gf_mul(y, EXP_[(N1_ - LOG_[xk]) % N1_]);
            unsigned S = gf_mul(gf_pow(y, qp[j]), EXP_[(N1_ - LOG_[x]) % N1_]);
            int orig = (gf_add(tr_a(R, j, qp), tr_a(S, k, qp)) == 1);
            /* 分母を払った多項式 */
            unsigned sum = 0;
            for (int a = 0; a < nt; a++) {
                unsigned v = gf_mul(gf_pow(x, t[a].dx), gf_pow(y, t[a].dy));
                sum = gf_add(sum, t[a].c == 1 ? v : gf_neg(v));
            }
            int poly0 = (sum == 0);
            if (orig != poly0) equiv_bad++;
            if (!poly0) continue;
            ny++; pts++;
            if (y == 0) perx_bad++;
            /* (C) u の復元 */
            unsigned Rm = gf_add(R, gf_neg(alpha)), Sm = gf_neg(S);   /* Tr_k(u)=R-alpha, Tr_j(u)=-S */
            unsigned u1 = tab[Rm * (unsigned)l + Sm];
            if (!u1) { u_missing++; continue; }
            unsigned u = u1 - 1;
            unsigned A = tr_a(u, j, qp), B = gf_add(tr_a(u, k, qp), alpha);
            if (B == 0 || A == 0) { c_bad++; continue; }
            unsigned c = gf_neg(gf_mul(A, EXP_[(N1_ - LOG_[gf_pow(B, qp[j])]) % N1_]));
            if (c != gf_pow(x, l - 1)) c_bad++;                       /* x^(l-1) は x≠0 なら 1 */
        }
        if (ny != qp[n - 1]) perx_bad++;
    }
    free(tab);
    printf("(A) 論文の式(9)と P(x,y)=0 の同値性 (全 %llu 組, x,y!=0 かつ y=0 も含む): 不一致 %llu 件  %s\n",
           (l - 1) * l, equiv_bad, equiv_bad ? "NG" : "OK");
    printf("(B) Prop 2.5: 各 x の解の個数 = q^(n-1) = %llu, 全て y!=0: 違反 %llu 件  %s   (解の総数 %llu)\n",
           qp[n - 1], perx_bad, perx_bad ? "NG" : "OK", pts);
    printf("(C) Prop 2.2: u の一意性(写像の単射) %s;  解から u を復元できない %llu 件;  Prop 2.3 の式との不一致 %llu 件  %s\n",
           inj_ok ? "OK" : "NG", u_missing, c_bad, (inj_ok && !u_missing && !c_bad) ? "OK" : "NG");
    fails = equiv_bad || perx_bad || !inj_ok || u_missing || c_bad;
    return !fails;
}

typedef __int128 i128;

static void verify_genus(int p, u64 q, int n, int k)
{
    int e = 0; { u64 tq = q; while (tq > 1) { tq /= p; e++; } }
    int M = e * n;
    u64 l0 = ipow(q, n);
    long long g = (long long)genus_F2(q, n, k);
    printf("(D) 種数 g(F_2)=%lld (Cor 2.7) の検証: F_{l^r} 上の有理place数 N_r から L 多項式を作って予測と比較\n", g);
    if (g < 1) { printf("    g=0 のため省略\n"); return; }
    int rmax = 0;                                       /* l0^r <= 2^24 となる最大の r */
    { double lg = (double)M; while ((rmax + 1) * lg <= 24.0 + 1e-9) rmax++; }
    if (rmax < g + 1) { printf("    N_1..N_%lld が必要ですが、体の大きさの上限(2^24)により r<=%d までしか数えられません: 省略\n", g + 1, rmax); return; }
    i128 N[40], P[40], E[100], lp[40];
    if (rmax > 30) rmax = 30;
    lp[0] = 1;
    for (int r = 1; r <= rmax; r++) lp[r] = lp[r - 1] * (i128)l0;
    for (int r = 1; r <= rmax; r++) {
        if (gf_init(p, M * r) != 0) { printf("    GF(%d^%d) を作れません\n", p, M * r); rmax = r - 1; break; }
        N[r] = (i128)count_F2(p, q, n, k, NULL);
        P[r] = lp[r] + 1 - N[r];
        gf_free();
        if (r >= g + 3) { rmax = r; break; }
    }
    /* Newton: m e_m = sum_{i=1..m} (-1)^(i-1) e_{m-i} p_i  (m=1..g) */
    E[0] = 1;
    int ok = 1;
    for (int m = 1; m <= g; m++) {
        i128 sm = 0;
        for (int i = 1; i <= m; i++) sm += ((i % 2) ? 1 : -1) * E[m - i] * P[i];
        if (sm % m != 0) { ok = 0; printf("    Newton の割り算が整数にならない (m=%d): g が違う可能性\n", m); }
        E[m] = sm / m;
    }
    /* 関数等式 e_{2g-i} = l^(g-i) e_i */
    for (int i = 0; i <= g; i++) E[2 * g - i] = lp[g - i] * E[i];
    for (int m = 2 * g + 1; m < 100; m++) E[m] = 0;
    printf("    N_r (r=1..%d): ", rmax);
    for (int r = 1; r <= rmax; r++) printf("%lld ", (long long)N[r]);
    printf("\n");
    int checked = 0;
    for (int m = g + 1; m <= rmax; m++) {
        i128 sm = (i128)m * E[m];
        for (int i = 1; i < m; i++) sm -= ((i % 2) ? 1 : -1) * E[m - i] * P[i];
        i128 pm = ((m - 1) % 2 ? -1 : 1) * sm;
        i128 Npred = lp[m] + 1 - pm;
        int same = (Npred == N[m]);
        printf("    予測 N_%d = %lld,  実測 N_%d = %lld   %s\n", m, (long long)Npred, m, (long long)N[m], same ? "一致" : "不一致");
        if (!same) ok = 0;
        checked++;
    }
    printf("    => 種数 g=%lld は %s (g が違えば予測は外れる)\n", g, (ok && checked) ? "OK" : "NG");
}

static void verify_all(int p, u64 q, int n, int k)
{
    int e = 0; { u64 tq = q; while (tq > 1) { tq /= p; e++; } }
    if (gf_init(p, e * n) != 0) { printf("体を作れません\n"); return; }
    printf("検証: q=%llu, n=%d, k=%d (j=%d), l=%llu\n", q, n, k, n - k, L_);
    verify_points(p, q, n, k);
    gf_free();
    verify_genus(p, q, n, k);
}

int main(int argc, char **argv)
{
    if (argc >= 5 && strcmp(argv[1], "verify") == 0) {
        u64 qq = strtoull(argv[2], NULL, 10); int nn = atoi(argv[3]), kk = atoi(argv[4]);
        int pp = char_of(qq);
        if (pp < 0 || nn < 2 || kk < 1 || kk >= nn || gcd(nn, kk) != 1 || (nn - kk) % pp == 0) { fprintf(stderr, "引数が不正 (q 素数冪, n>=2, 0<k<n, gcd(n,k)=1, p∤j)\n"); return 1; }
        verify_all(pp, qq, nn, kk);
        return 0;
    }
    if (argc >= 4 && strcmp(argv[1], "best") == 0) {
        best_curve(atoi(argv[2]), atoi(argv[3]));
        return 0;
    }
    if (argc >= 4 && strcmp(argv[1], "maximal") == 0) {
        int pp = atoi(argv[2]), lo = atoi(argv[3]);
        maximal_scan(pp, lo, argc > 4 ? atoi(argv[4]) : lo);
        return 0;
    }
    if (argc >= 4 && strcmp(argv[1], "compare") == 0) {
        int pp = atoi(argv[2]), mm = atoi(argv[3]);
        compare(pp, mm, argc > 4 ? atoi(argv[4]) : 4);
        return 0;
    }
    if (argc < 3) { fprintf(stderr, "使い方: %s q n [k] [levels] [list]\n       %s cube p m [levels] [list]\n       %s compare p m [levels]\n", argv[0], argv[0], argv[0]); return 1; }
    u64 q; int n, k, levels, list, auto_k = 0;
    if (argc >= 4 && strcmp(argv[1], "cube") == 0) {      /* F_{p^{3m}}: q=p^m, n=3, k=2 (j=1) */
        int pp = atoi(argv[2]), mm = atoi(argv[3]);
        if (char_of(pp) != pp || mm < 1) { fprintf(stderr, "p は素数, m >= 1 にしてください\n"); return 1; }
        q = ipow(pp, mm); n = 3; k = 2;
        levels = argc > 4 ? atoi(argv[4]) : 4;
        list = argc > 5 ? atoi(argv[5]) : 0;
    } else {
        q = strtoull(argv[1], NULL, 10);
        n = atoi(argv[2]);
        auto_k = (argc <= 3 || strcmp(argv[3], "auto") == 0 || atoi(argv[3]) == 0);
        k = auto_k ? 0 : atoi(argv[3]);
        levels = argc > 4 ? atoi(argv[4]) : 4;
        list = argc > 5 ? atoi(argv[5]) : 0;
    }

    int p = char_of(q);
    if (p < 0 || q < 2)                    { fprintf(stderr, "q は素数冪にしてください\n"); return 1; }
    if (n < 2)                             { fprintf(stderr, "n >= 2 が必要 (非素体)\n"); return 1; }
    if (auto_k) {
        int ee = 0; { u64 tq = q; while (tq > 1) { tq /= p; ee++; } }
        if (gf_init(p, ee * n) != 0) { fprintf(stderr, "GF(%d^%d) を作れません\n", p, ee * n); return 1; }
        u64 ll = L_, sq = isqrt_u64(ll);
        int pick = 0, nfound = 0;
        printf("k を自動選択: F_%llu 上 (q=%llu, n=%d) で F_2 が最大曲線になる k を探します\n", ll, q, n);
        for (int kk = 1; kk < n; kk++) {
            int jj = n - kk;
            if (gcd(n, kk) != 1 || jj % p == 0) continue;
            u64 N = count_F2(p, q, n, kk, NULL), g = genus_F2(q, n, kk);
            int mx = (sq * sq == ll) && (N == ll + 1 + 2 * g * sq);
            printf("  k=%d (j=%d): g(F_2)=%llu, N(F_2)=%llu, 上限 l+1+2g√l %s %llu  %s\n", kk, jj, g, N,
                   sq * sq == ll ? "=" : "(l が平方数でない)", sq * sq == ll ? ll + 1 + 2 * g * sq : 0ULL,
                   mx ? "<- 最大曲線" : "");
            if (mx) { if (!pick) pick = kk; nfound++; }
        }
        gf_free();
        if (!pick) { printf("最大曲線になる k はありません (q=%llu, n=%d)\n", q, n); return 0; }
        k = pick;
        printf("=> k=%d を使います%s\n\n", k, nfound > 1 ? " (複数該当: 最小の k)" : "");
    }
    if (k < 1 || k >= n || gcd(n, k) != 1) { fprintf(stderr, "0<k<n かつ gcd(n,k)=1 が必要\n"); return 1; }

    term t[MAXTERM];
    int m = build_poly(q, n, k, t);

    int e = 0; { u64 tq = q; while (tq > 1) { tq /= p; e++; } }
    int M = e * n;
    u64 l = ipow(q, n);
    if ((n - k) % p == 0) fprintf(stderr, "(注意) p が j=%d を割ります: 論文の仮定 (p∤j) の外です\n", n - k);
    printf("体 F_l: l = %llu^%d = %llu = %d^%d (標数 %d),  j = %d, k = %d\n", q, n, l, p, M, p, n - k, k);

    u64 degy = 0;
    for (int i = 0; i < m; i++) if (t[i].dy > degy) degy = t[i].dy;
    printf("各段の拡大次数 [F_(i+1):F_i] = deg_Y P = %llu\n", degy);

    printf("F_1 = F_l(x_1)\n");
    for (int i = 1; i < levels; i++) {
        printf("F_%d = F_%d(x_%d):  ", i + 1, i, i + 1);
        for (int a = 0; a < m; a++) {
            int c = (t[a].c == 1) ? 1 : p - 1;
            if (a) printf(" + ");
            if (c != 1) printf("%d*", c);
            print_mono(t[a].dx, t[a].dy, i);
        }
        printf(" = 0\n");
    }

    /* ---- 有理点の探索 ---- */
    if (gf_init(p, M) != 0) { fprintf(stderr, "GF(%d^%d) の構成に失敗\n", p, M); return 1; }
    if (l > 4096) fprintf(stderr, "(注意) l=%llu: 探索は O(l^2) なので時間がかかります\n", l);

    edge *ed; u64 ne = find_edges(t, m, &ed);
    printf("\n[F_l 有理点の候補]  l = %llu\n", l);
    printf("P(x1,x2)=0 の解で x1,x2 in F_l^* : %llu 個 (これが N_2)\n", ne);
    if (list) {
        for (u64 i = 0; i < ne; i++) {
            printf("(");  print_elem(ed[i].x);  printf(", ");  print_elem(ed[i].y);  printf(")\n");
        }
    }
    count_tower_points(ed, ne, levels);
    free(ed);
    print_stats(q, n, k, levels);
    return 0;
}