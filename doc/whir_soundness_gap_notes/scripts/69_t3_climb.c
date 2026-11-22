// Task 3: adaptive search for lists. For a code (kind) over the compiled field and L+1 members, hill-climb on the
// pattern, keeping it feasible (a kernel point with pairwise distinct members), maximizing the balanced agreement
// and then the weight. Starts: block-structured patterns at a random level (level 0 = random leaves), trimmed to feasibility.
// usage: t3_climb v r L kind restarts steps seed [codes [lift]]   (codes: number of independent code draws, default 1;
// restarts = 0: exhaustive over all patterns instead of climbing;
// lift: score a pattern of this (top) code by the balanced agreement of its lift by that many bottom layers)
#include "69_pat.h"
#include "69_lin.h"
static int v, r, L, n, k, cols; static fe *G, *M, *K;
static int feasible(const uint8_t *cls) {
    int rows = 0;
    for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
        fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
        memcpy(row + (l - 1) * k, G + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, G + (size_t)x * k, sizeof(fe) * k); rows++; } }
    if (rows == 0) return 1;
    int dim = gf_kernel(M, rows, cols, K);
    if (!dim) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) { // does d_a = d_b hold on the whole kernel?
        int all = 1;
        for (int t = 0; t < dim && all; t++) for (int e = 0; e < k && all; e++) {
            fe da = a ? K[(size_t)t * cols + (a - 1) * k + e] : 0, db = K[(size_t)t * cols + (b - 1) * k + e];
            all = (da == db);
        }
        if (all) return 0;
    }
    return 1;
}
static int lift_lo = 0;
// give `fl` free leaves to the smallest counts, one at a time in effect; c[0..L] ends sorted ascending
static void waterfill(int *c, int fl) {
    for (int i = 1; i <= L; i++) { int t = c[i], j = i - 1; while (j >= 0 && c[j] > t) { c[j + 1] = c[j]; j--; } c[j + 1] = t; }
    int m = 1; // the m smallest are level
    while (fl > 0) {
        while (m <= L && c[m] == c[0]) m++;
        int room = (m <= L) ? (c[m] - c[0]) * m : fl; if (room > fl) room = fl;
        int up = room / m, rem = room % m;
        for (int i = 0; i < m; i++) c[i] += up;
        for (int i = m - rem; i < m; i++) c[i] += 1; // the remainder goes to the last of the level ones, keeping the order
        fl -= room; if (rem) break;
    }
}
// Balanced agreement of the lift by lift_lo bottom layers: every leaf here is a block of bs = 2^lift_lo leaves, and
// bs - 1 leaves (the zeros of the common lower factor) take the full class, placed greedily.
static int lifted_balanced(const uint8_t *cls) {
    int bs = 1 << lift_lo, cnt[16] = {0}, freeleaves = 0, zb[MAXN] = {0};
    for (int x = 0; x < n; x++) { if (!cls[x]) freeleaves += bs; for (int l = 0; l <= L; l++) if ((cls[x] >> l) & 1) cnt[l] += bs; }
    int best_total = 0;
    for (int z = 0; z < bs; z++) { // z = bs - 1 zeros placed after the loop body has run bs - 1 times; evaluate at the end
        int c2[16], fl = freeleaves; memcpy(c2, cnt, sizeof c2);
        if (z == bs - 1) { waterfill(c2, fl > 0 ? fl : 0); best_total = c2[0]; break; }
        int bb = -1, bvec[16] = {0};
        for (int x = 0; x < n; x++) { // leximin: the block whose zero gives the lexicographically largest sorted count vector
            if (zb[x] == bs) continue;
            int c3[16], f3 = freeleaves - (cls[x] ? 0 : 1); memcpy(c3, cnt, sizeof c3);
            for (int l = 0; l <= L; l++) if (!((cls[x] >> l) & 1)) c3[l]++;
            waterfill(c3, f3 > 0 ? f3 : 0);
            int better = (bb < 0); for (int i = 0; i <= L && !better; i++) { if (c3[i] > bvec[i]) better = 1; else if (c3[i] < bvec[i]) break; }
            if (better) { bb = x; memcpy(bvec, c3, sizeof bvec); }
        }
        zb[bb]++; if (!cls[bb]) freeleaves--; for (int l = 0; l <= L; l++) if (!((cls[bb] >> l) & 1)) cnt[l]++;
    }
    return best_total;
}
static long score(const uint8_t *cls) { return lift_lo ? 1000L * lifted_balanced(cls) + pat_weight(cls, n) : 1000L * pat_balanced(cls, n, L) + pat_weight(cls, n); }
int main(int argc, char **argv) {
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); char kind = argv[4][0];
    int restarts = atoi(argv[5]), steps = atoi(argv[6]); rng_seed(strtoull(argv[7], 0, 10)); int ncodes = argc > 8 ? atoi(argv[8]) : 1; lift_lo = argc > 9 ? atoi(argv[9]) : 0;
    gf_init(); n = 1 << (v + r); k = 1 << v; cols = L * k;
    G = malloc(sizeof(fe) * n * k); M = malloc(sizeof(fe) * (size_t)(L * n + 1) * cols); K = malloc(sizeof(fe) * (size_t)cols * cols);
    uint8_t cls[MAXN], trial[MAXN], best[MAXN]; long bestscore = -1; int bestw = 0, besta = 0;
    for (int cd = 0; cd < ncodes; cd++) {
        code_gen(kind, v, r, G);
        if (restarts == 0) { // exhaustive over all patterns (small top codes): feasibility only when the score would improve
            uint8_t classes[64]; int C = 0; classes[C++] = 0; for (int t = 1; t < (1 << (L + 1)); t++) if (__builtin_popcount(t) >= 2) classes[C++] = (uint8_t)t;
            int dig[MAXN] = {0};
            for (;;) {
                for (int x = 0; x < n; x++) cls[x] = classes[dig[x]];
                long sc = score(cls);
                if (sc > bestscore && feasible(cls)) { bestscore = sc; memcpy(best, cls, n); bestw = pat_weight(cls, n); besta = pat_balanced(cls, n, L); }
                int x = 0; while (x < n && ++dig[x] == C) dig[x++] = 0;
                if (x == n) break;
            }
        }
        for (int rs = 0; rs < restarts; rs++) {
            int lev = (int)rng_below(v), bs = 1 << lev;
            for (int b = 0; b < n / bs; b++) { // a class of 2..L+1 members or nothing per block
                uint8_t c = 0;
                if (rng_below(4)) { int sz = 2 + (int)rng_below(L); while (__builtin_popcount(c) < sz) c |= (uint8_t)(1 << rng_below(L + 1)); }
                for (int x = 0; x < bs; x++) cls[b * bs + x] = c;
            }
            while (!feasible(cls)) { // trim random memberships
                int x; do x = (int)rng_below(n); while (!cls[x]);
                int l; do l = (int)rng_below(L + 1); while (!((cls[x] >> l) & 1));
                cls[x] &= (uint8_t)~(1 << l); if (__builtin_popcount(cls[x]) < 2) cls[x] = 0;
            }
            long sc = score(cls);
            for (int st = 0; st < steps; st++) {
                memcpy(trial, cls, n);
                int x = (int)rng_below(n), l = (int)rng_below(L + 1);
                if (rng_below(3) == 0) { // move: drop one membership elsewhere first
                    int y = (int)rng_below(n);
                    if (trial[y]) { int m; do m = (int)rng_below(L + 1); while (!((trial[y] >> m) & 1)); trial[y] &= (uint8_t)~(1 << m); if (__builtin_popcount(trial[y]) < 2) trial[y] = 0; }
                }
                if (!trial[x]) { int l2; do l2 = (int)rng_below(L + 1); while (l2 == l); trial[x] = (uint8_t)((1 << l) | (1 << l2)); }
                else trial[x] |= (uint8_t)(1 << l);
                long ts = score(trial);
                if (ts < sc || !memcmp(trial, cls, n) || !feasible(trial)) continue;
                memcpy(cls, trial, n); sc = ts;
            }
            if (sc > bestscore) { bestscore = sc; memcpy(best, cls, n); }
            if (pat_weight(cls, n) > bestw) bestw = pat_weight(cls, n);
            if (pat_balanced(cls, n, L) > besta) besta = pat_balanced(cls, n, L);
        }
    }
    if (lift_lo) { long nn = (long)n << lift_lo, kk = (long)k << lift_lo; int lb = lifted_balanced(best);
        printf("FB=%d kind=%c top [%d,%d] members=%d lifted by %d layers to n=%ld: best balanced agreement %d = %.4f n (gS value %ld = %.4f n; tau_L for L = members - 1: %.4f)\n  best: ",
               FB, kind, n, k, L + 1, lift_lo, nn, lb, (double)lb / nn, (nn + L * kk - 1) / (L + 1), (double)((nn + L * kk - 1) / (L + 1)) / nn, (1.0 + L * (double)k / n) / (L + 1));
        pat_print(stdout, best, n, L); return 0; }
    long gs = (n + (long)L * k - 1) / (L + 1);
    printf("FB=%d kind=%c k=%d n=%d members=%d codes=%d restarts=%d steps=%d: best balanced agreement %d (gS value %ld), best weight %d (Lk-1 = %d)\n  best: ",
           FB, kind, k, n, L + 1, ncodes, restarts, steps, besta, gs, bestw, L * k - 1);
    pat_print(stdout, best, n, L);
    return 0;
}
