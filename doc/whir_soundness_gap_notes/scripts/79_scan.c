// Note 79: three-member patterns (L = 2) for the mixed tree code V1 over GF(2^64).
// Exhaustive over the 5^n patterns of weight >= 2k (n <= 8) or sampled; reports the patterns that carry a list.
// usage: 79_scan v r d ptype seed mode [samples]
//   ptype: n (no mixing), a (uniform permutations), c (one n-cycle each), x (xor with a fixed mask each), s (sibling), r (bit reversal)
//   mode: e (exhaustive), s (sampled, weight exactly 2k, biased to triples)
#include "75_gf.h"
#define MAXN 64
#define MAXK 32
static int v, r, n, k, d;
static fe g[MAXN][MAXK], h[MAXN][MAXK];
static int pi_[4][MAXN];
static fe mu[4][MAXN];
static void build(char ptype) {
    static fe tw[8][MAXN];
    for (int i = 0; i < v; i++) for (int p = 0; p < (n >> i); p++) tw[i][p] = rnd();
    for (int y = 0; y < n; y++) for (int e = 0; e < k; e++) { fe a = 1; for (int i = 0; i < v; i++) if ((e >> i) & 1) a = gf_mul(a, tw[i][y >> i]); g[y][e] = a; }
    for (int a = 0; a < d; a++) {
        int *p = pi_[a];
        if (ptype == 'a') { for (int i = 0; i < n; i++) p[i] = i; for (int i = n - 1; i > 0; i--) { int j = (int)rnd_below(i + 1), t = p[i]; p[i] = p[j]; p[j] = t; } }
        else if (ptype == 'c') { int o[MAXN]; for (int i = 0; i < n; i++) o[i] = i; for (int i = n - 1; i > 0; i--) { int j = (int)rnd_below(i + 1), t = o[i]; o[i] = o[j]; o[j] = t; } for (int i = 0; i < n; i++) p[o[i]] = o[(i + 1) % n]; }
        else if (ptype == 'x') { int m = 1 + (int)rnd_below(n - 1); for (int i = 0; i < n; i++) p[i] = i ^ m; }
        else if (ptype == 's') { for (int i = 0; i < n; i++) p[i] = i ^ 1; }
        else if (ptype == 'r') { for (int i = 0; i < n; i++) { int o = 0; for (int b = 0; b < v + r; b++) if ((i >> b) & 1) o |= 1 << (v + r - 1 - b); p[i] = o; } }
        for (int i = 0; i < n; i++) mu[a][i] = rnd() | 1;
    }
    for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) { fe s = g[x][e]; for (int a = 0; a < d; a++) s ^= gf_mul(mu[a][x], g[pi_[a][x]][e]); h[x][e] = s; }
}
// returns kernel dimension; *list = 1 if the kernel has a point with d1, d2, d1+d2 all nonzero
static int solve(const int *cls, int *list) {
    static fe A[2 * MAXN * 2 * MAXK], Kb[2 * MAXK * 2 * MAXK]; int piv[2 * MAXK];
    int C = 2 * k, R = 0;
    for (int x = 0; x < n; x++) {
        int c = cls[x]; if (!c) continue;
        if (c == 1 || c == 4) { for (int e = 0; e < k; e++) { A[R * C + e] = h[x][e]; A[R * C + k + e] = 0; } R++; }
        if (c == 2 || c == 4) { for (int e = 0; e < k; e++) { A[R * C + e] = 0; A[R * C + k + e] = h[x][e]; } R++; }
        if (c == 3) { for (int e = 0; e < k; e++) { A[R * C + e] = h[x][e]; A[R * C + k + e] = h[x][e]; } R++; }
    }
    int rk = gf_rref(A, R, C, piv), dim = gf_kernel_from_rref(A, C, piv, Kb);
    (void)rk;
    int n1 = 0, n2 = 0, n3 = 0;
    for (int b = 0; b < dim; b++) for (int e = 0; e < k; e++) { fe a = Kb[b * C + e], c2 = Kb[b * C + k + e]; if (a) n1 = 1; if (c2) n2 = 1; if (a ^ c2) n3 = 1; }
    *list = n1 && n2 && n3;
    return dim;
}
int main(int argc, char **argv) {
    if (argc < 7) { printf("usage: v r d ptype seed mode [samples]\n"); return 1; }
    v = atoi(argv[1]); r = atoi(argv[2]); d = atoi(argv[3]); char ptype = argv[4][0]; rng_seed(strtoull(argv[5], 0, 0)); char mode = argv[6][0];
    long samples = argc > 7 ? atol(argv[7]) : 100000;
    n = 1 << (v + r); k = 1 << v; gf_selftest(); build(ptype);
    printf("(k,n)=(%d,%d) d=%d ptype=%c seed=%s", k, n, d, ptype, argv[5]);
    for (int a = 0; a < d; a++) { printf(" pi%d=[", a); for (int i = 0; i < n && n <= 16; i++) printf("%d%s", pi_[a][i], i + 1 < n ? "," : ""); printf("]"); }
    printf("\n");
    int cls[MAXN]; long tested = 0, viol = 0, maxw = 0; long hist[4 * MAXN] = {0};
    static const int wt[5] = {0, 1, 1, 1, 2};
    if (mode == 'e') {
        long total = 1; for (int i = 0; i < n; i++) total *= 5;
        for (long c = 0; c < total; c++) {
            long t = c; int w = 0; for (int i = 0; i < n; i++) { cls[i] = (int)(t % 5); t /= 5; w += wt[cls[i]]; }
            if (w < 2 * k) continue;
            int list, dim = solve(cls, &list); tested++; (void)dim;
            if (list) { viol++; hist[w]++; if (w > maxw) maxw = w; if (viol <= 5) { printf("  violation w=%d dim=%d classes:", w, dim); for (int i = 0; i < n; i++) printf(" %d", cls[i]); printf("\n"); } }
        }
    } else {
        for (long s = 0; s < samples; s++) {
            int w = 0; for (int i = 0; i < n; i++) cls[i] = 0;
            int ptrip = (int)rnd_below(4); // bias: probability of a triple in quarters
            while (w < 2 * k) { int x = (int)rnd_below(n); if (cls[x] == 4) continue; if (cls[x]) { w += 1; cls[x] = 4; continue; }
                if ((int)rnd_below(4) < ptrip && w + 2 <= 2 * k) { cls[x] = 4; w += 2; } else { cls[x] = 1 + (int)rnd_below(3); w += 1; } }
            int list, dim = solve(cls, &list); tested++; (void)dim;
            if (list) { viol++; hist[w]++; if (viol <= 5) { printf("  violation w=%d dim=%d classes:", w, dim); for (int i = 0; i < n; i++) printf(" %d", cls[i]); printf("\n"); } }
        }
    }
    printf("  patterns of weight >= 2k tested: %ld, carrying a list (violations of GS(2)): %ld", tested, viol);
    if (viol) { printf(", by weight:"); for (int w = 0; w < 4 * MAXN; w++) if (hist[w]) printf(" %d:%ld", w, hist[w]); }
    printf("\n");
    return 0;
}
