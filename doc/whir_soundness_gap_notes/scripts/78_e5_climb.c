// Note 78, experiment 5(a): adaptive search for lists in a variant. Hill-climb on the pattern, keeping it feasible (a kernel
// point with pairwise distinct members). Derived from note 69's 69_t3_climb.c; the code is any spec of 78_var.h.
// usage: 78_e5_climb v r L spec restarts steps seed obj [lift_lo nzeros]
//   obj = a: maximize balanced agreement then weight; w: weight then balanced agreement
//   lift_lo > 0: the code is a TOP code; a pattern is scored by the balanced agreement of its lift by lift_lo bottom layers
//   with nzeros common zeros of the lower factor (2^lift_lo - 1 for a tree code, 2^(lift_lo-1) - 1 for V2 up/dn)
// Starts (cycled): 0 blocks at a random level; 1 random leaves up to weight Lk-1; 2 (V1) classes constant along runs of the
// first partner map; 3 (V1) a block pattern intersected with its pull-back by the partner maps. All trimmed to feasibility.
// Moves: add one membership (sometimes after dropping one elsewhere); add a membership on a whole block of a random level
// (sometimes after clearing that member from another block); for V1 also add the same membership at x and partner(x).
#include "69_pat.h"
#include "78_var.h"
static int v, r, L, n, k, cols; static fe *G, *M, *K; static var_t V;
static int feasible(const uint8_t *cls) {
    int rows = 0;
    for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
        fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
        memcpy(row + (l - 1) * k, G + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, G + (size_t)x * k, sizeof(fe) * k); rows++; } }
    if (rows == 0) return 1;
    int dim = gf_kernel(M, rows, cols, K);
    if (!dim) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) {
        int all = 1;
        for (int t = 0; t < dim && all; t++) for (int e = 0; e < k && all; e++) { fe da = a ? K[(size_t)t * cols + (a - 1) * k + e] : 0, db = K[(size_t)t * cols + (b - 1) * k + e]; all = (da == db); }
        if (all) return 0;
    }
    return 1;
}
static int lift_lo = 0, nzeros = 0;
static void waterfill(int *c, int fl) {
    for (int i = 1; i <= L; i++) { int t = c[i], j = i - 1; while (j >= 0 && c[j] > t) { c[j + 1] = c[j]; j--; } c[j + 1] = t; }
    int m = 1;
    while (fl > 0) {
        while (m <= L && c[m] == c[0]) m++;
        int room = (m <= L) ? (c[m] - c[0]) * m : fl; if (room > fl) room = fl;
        int up = room / m, rem = room % m;
        for (int i = 0; i < m; i++) c[i] += up;
        for (int i = m - rem; i < m; i++) c[i] += 1;
        fl -= room; if (rem) break;
    }
}
static int lifted_balanced(const uint8_t *cls, int *wout) {
    int bs = 1 << lift_lo, cnt[16] = {0}, freeleaves = 0, zb[MAXN] = {0}, w = 0;
    for (int x = 0; x < n; x++) { if (!cls[x]) freeleaves += bs; else w += bs * (__builtin_popcount(cls[x]) - 1); for (int l = 0; l <= L; l++) if ((cls[x] >> l) & 1) cnt[l] += bs; }
    for (int z = 0; z < nzeros; z++) {
        int bb = -1, bvec[16] = {0};
        for (int x = 0; x < n; x++) {
            if (zb[x] == bs) continue;
            int c3[16], f3 = freeleaves - (cls[x] ? 0 : 1); memcpy(c3, cnt, sizeof c3);
            for (int l = 0; l <= L; l++) if (!((cls[x] >> l) & 1)) c3[l]++;
            waterfill(c3, f3 > 0 ? f3 : 0);
            int better = (bb < 0); for (int i = 0; i <= L && !better; i++) { if (c3[i] > bvec[i]) better = 1; else if (c3[i] < bvec[i]) break; }
            if (better) { bb = x; memcpy(bvec, c3, sizeof bvec); }
        }
        zb[bb]++; if (!cls[bb]) freeleaves--; for (int l = 0; l <= L; l++) if (!((cls[bb] >> l) & 1)) cnt[l]++;
        w += L + 1 - (cls[bb] ? __builtin_popcount(cls[bb]) : 1);
    }
    if (wout) *wout = w;
    waterfill(cnt, freeleaves > 0 ? freeleaves : 0);
    return cnt[0];
}
static char obj = 'a';
static long score(const uint8_t *cls) {
    int a, w;
    if (lift_lo) a = lifted_balanced(cls, &w); else { a = pat_balanced(cls, n, L); w = pat_weight(cls, n); }
    return obj == 'a' ? 100000L * a + w : 100000L * w + a;
}
static uint8_t randclass(void) { uint8_t c = 0; int sz = 2 + (int)rng_below(L); while (__builtin_popcount(c) < sz) c |= (uint8_t)(1 << rng_below(L + 1)); return c; }
int main(int argc, char **argv) {
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); const char *spec = argv[4];
    int restarts = atoi(argv[5]), steps = atoi(argv[6]); rng_seed(strtoull(argv[7], 0, 10)); obj = argv[8][0];
    lift_lo = argc > 9 ? atoi(argv[9]) : 0; nzeros = argc > 10 ? atoi(argv[10]) : (lift_lo ? (1 << lift_lo) - 1 : 0);
    gf_init(); n = 1 << (v + r); k = 1 << v; cols = L * k;
    if (!var_make(&V, spec, v, r)) { printf("bad spec\n"); return 1; }
    G = V.G; M = malloc(sizeof(fe) * (size_t)(L * n + 1) * cols); K = malloc(sizeof(fe) * (size_t)cols * cols);
    uint8_t cls[MAXN], trial[MAXN], best[MAXN], bestwp[MAXN]; long bestscore = -1; int bestw = 0, besta = 0;
    for (int rs = 0; rs < restarts; rs++) {
        int st0 = rs % (V.d ? 4 : 2);
        memset(cls, 0, n);
        if (st0 == 0) { int lev = (int)rng_below(v), bs = 1 << lev; for (int b = 0; b < n / bs; b++) { uint8_t c = rng_below(4) ? randclass() : 0; for (int x = 0; x < bs; x++) cls[b * bs + x] = c; } }
        else if (st0 == 1) { while (pat_weight(cls, n) < L * k - 1) cls[rng_below(n)] = randclass(); }
        else if (st0 == 2) { while (pat_weight(cls, n) < L * k - 1) { int x = (int)rng_below(n), len = 1 + (int)rng_below(8); uint8_t c = randclass(); for (int i = 0; i < len; i++) { cls[x] = c; x = V.pi[0][x]; } } }
        else { uint8_t blk[MAXN]; int lev = 1 + (int)rng_below(v + r - 1), bs = 1 << lev; for (int b = 0; b < n / bs; b++) { uint8_t c = rng_below(6) ? randclass() : 0; for (int y = 0; y < bs; y++) blk[b * bs + y] = c; }
            for (int x = 0; x < n; x++) { uint8_t c = blk[x]; for (int a = 0; a < V.d; a++) c &= blk[V.pi[a][x]]; cls[x] = __builtin_popcount(c) >= 2 ? c : 0; } }
        while (!feasible(cls)) {
            int x; do x = (int)rng_below(n); while (!cls[x]);
            int l; do l = (int)rng_below(L + 1); while (!((cls[x] >> l) & 1));
            cls[x] &= (uint8_t)~(1 << l); if (__builtin_popcount(cls[x]) < 2) cls[x] = 0;
        }
        long sc = score(cls);
        for (int st = 0; st < steps; st++) {
            memcpy(trial, cls, n);
            int x = (int)rng_below(n), l = (int)rng_below(L + 1), mv = (int)rng_below(V.d ? 6 : 5);
            if (mv == 0) { int y = (int)rng_below(n); if (trial[y]) { int m; do m = (int)rng_below(L + 1); while (!((trial[y] >> m) & 1)); trial[y] &= (uint8_t)~(1 << m); if (__builtin_popcount(trial[y]) < 2) trial[y] = 0; } }
            int l2; do l2 = (int)rng_below(L + 1); while (l2 == l);
            if (!trial[x]) trial[x] = (uint8_t)((1 << l) | (1 << l2)); else trial[x] |= (uint8_t)(1 << l);
            if (mv == 5) { int y = V.pi[0][x]; if (!trial[y]) trial[y] = (uint8_t)((1 << l) | (1 << l2)); else trial[y] |= (uint8_t)(1 << l); }
            if (mv == 3 || mv == 4) { // block move: the same membership on a whole block (mv 4: after clearing that member from another block)
                int lev = 1 + (int)rng_below(v + r - 1), bs = 1 << lev, b0 = (x >> lev) << lev;
                if (mv == 4) { int b1 = (int)rng_below(n >> lev) << lev; for (int y = b1; y < b1 + bs; y++) { trial[y] &= (uint8_t)~(1 << l); if (__builtin_popcount(trial[y]) < 2) trial[y] = 0; } }
                for (int y = b0; y < b0 + bs; y++) { if (!trial[y]) trial[y] = (uint8_t)((1 << l) | (1 << l2)); else trial[y] |= (uint8_t)(1 << l); }
            }
            long ts = score(trial);
            if (ts < sc || !memcmp(trial, cls, n) || !feasible(trial)) continue;
            memcpy(cls, trial, n); sc = ts;
        }
        if (sc > bestscore) { bestscore = sc; memcpy(best, cls, n); }
        if (pat_weight(cls, n) > bestw) { bestw = pat_weight(cls, n); memcpy(bestwp, cls, n); }
        if (pat_balanced(cls, n, L) > besta) besta = pat_balanced(cls, n, L);
    }
    if (lift_lo) { long nn = (long)n << lift_lo, kk = (long)k << lift_lo; int lw, lb = lifted_balanced(best, &lw); long gs = (nn + L * kk - 1) / (L + 1);
        printf("%s top [%d,%d] members=%d lifted by %d layers with %d common zeros to n=%ld: best balanced agreement %d (gS value %ld, excess %+ld), lifted weight %d (gS %ld, excess %+ld)\n  best: ",
               spec, n, k, L + 1, lift_lo, nzeros, nn, lb, gs, lb - gs, lw, L * kk - 1, lw - (L * kk - 1));
        pat_print(stdout, best, n, L); return 0; }
    long gs = (n + (long)L * k - 1) / (L + 1);
    printf("%s k=%d n=%d members=%d restarts=%d steps=%d obj=%c: best balanced agreement %d (gS value %ld, excess %+ld), best weight %d (gS %d, excess %+d)\n  best: ",
           spec, k, n, L + 1, restarts, steps, obj, besta, gs, besta - gs, bestw, L * k - 1, bestw - (L * k - 1));
    pat_print(stdout, best, n, L); printf("  best weight: "); pat_print(stdout, bestwp, n, L);
    return 0;
}
