// Note 74, task 4: local search over patterns of a top tree code [N, N/2] (T2, GF(2^64)) with up to 64 members, scored by
// the balanced agreement of the lift by `lo` bottom layers (every block is 2^lo leaves; the 2^lo - 1 zeros of the common
// lower factor are placed by a leximin greedy; leaves of blocks without a class go to the weakest members).
// A pattern is kept only if the top code carries a genuine list on it (kernel with pairwise distinct members, exact).
// usage: 74_climb vtop members lo start steps seed [f]
//   start = F: the one-sided staircase family (block 0 for the zeros, f free blocks, members = random k_up-subsets of the rest)
//   start = S: the same family of the [N/2, N/4] code on pairs of blocks (block 0 in every class, block 1 for the zeros)
//   start = R: random block classes, trimmed until feasible
#include "69_tree.h"
#include "69_lin.h"
typedef uint64_t cl;
static int N, ku, Mm, L, cols, lo; static fe *Gup, *Mx, *Kx;
static long ntests = 0;
static int feasible(const cl *cls) {
    int rows = 0; ntests++;
    for (int q = 0; q < N; q++) { if (__builtin_popcountll(cls[q]) < 2) continue; int l0 = __builtin_ctzll(cls[q]);
        for (int l = l0 + 1; l <= L; l++) if ((cls[q] >> l) & 1) { fe *row = Mx + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * ku, Gup + q * ku, sizeof(fe) * ku); if (l0 >= 1) memcpy(row + (l0 - 1) * ku, Gup + q * ku, sizeof(fe) * ku); rows++; } }
    if (!rows) return 1;
    int dim = gf_kernel(Mx, rows, cols, Kx); if (!dim) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) { int all = 1;
        for (int t = 0; t < dim && all; t++) for (int e = 0; e < ku && all; e++) { fe da = a ? Kx[(size_t)t * cols + (a - 1) * ku + e] : 0, db = Kx[(size_t)t * cols + (b - 1) * ku + e]; all = (da == db); }
        if (all) return 0; }
    return 1;
}
static int cmpi(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }
static void waterfill(int *c, long fl) { // c sorted ascending afterwards
    qsort(c, Mm, sizeof(int), cmpi);
    while (fl > 0) { int m = 1; while (m < Mm && c[m] == c[0]) m++;
        long room = (m < Mm) ? (long)(c[m] - c[0]) * m : fl; if (room > fl) room = fl; if (room == 0) room = fl < m ? fl : m;
        long up = room / m, rem = room % m; for (int i = 0; i < m; i++) c[i] += (int)up; for (int i = m - (int)rem; i < m; i++) c[i]++;
        fl -= room; qsort(c, Mm, sizeof(int), cmpi); if (rem) break; }
}
// returns the minimum agreement of the lift; *tot = sum of the block agreements (second key)
static int score(const cl *cls, long *tot) {
    int bs = 1 << lo, cnt[64] = {0}, zb[64] = {0}; long fl = 0; *tot = 0;
    for (int q = 0; q < N; q++) { if (!cls[q]) fl += bs; for (int l = 0; l < Mm; l++) if ((cls[q] >> l) & 1) { cnt[l] += bs; (*tot)++; } }
    for (int z = 0; z < bs - 1; z++) {
        int bb = -1, bvec[64];
        for (int q = 0; q < N; q++) { if (zb[q] == bs) continue;
            int c3[64]; long f3 = fl - (cls[q] ? 0 : 1); memcpy(c3, cnt, sizeof(int) * Mm);
            for (int l = 0; l < Mm; l++) if (!((cls[q] >> l) & 1)) c3[l]++;
            waterfill(c3, f3 > 0 ? f3 : 0);
            int better = (bb < 0); for (int i = 0; i < Mm && !better; i++) { if (c3[i] > bvec[i]) better = 1; else if (c3[i] < bvec[i]) break; }
            if (better) { bb = q; memcpy(bvec, c3, sizeof(int) * Mm); } }
        zb[bb]++; if (!cls[bb]) fl--; for (int l = 0; l < Mm; l++) if (!((cls[bb] >> l) & 1)) cnt[l]++;
    }
    waterfill(cnt, fl > 0 ? fl : 0); return cnt[0];
}
static void print_pat(const cl *cls) { for (int q = 0; q < N; q++) { if (!cls[q]) printf("."); else for (int l = 0; l < Mm; l++) if ((cls[q] >> l) & 1) printf("%c", l < 10 ? '0' + l : l < 36 ? 'a' + l - 10 : 'A' + l - 36); printf(q + 1 < N ? " " : "\n"); } }
int main(int argc, char **argv) {
    int vt = atoi(argv[1]); Mm = atoi(argv[2]); lo = atoi(argv[3]); char start = argv[4][0]; long steps = atol(argv[5]); rng_seed(strtoull(argv[6], 0, 10)); int f = argc > 7 ? atoi(argv[7]) : 0;
    gf_init(); char modes[MAXV + 1]; for (int i = 0; i < vt; i++) modes[i] = '2'; modes[vt] = 0;
    tree_t T; tree_make(&T, vt, 1, modes); N = T.n; ku = T.k; L = Mm - 1; cols = L * ku;
    Gup = malloc(sizeof(fe) * N * ku); tree_gen(&T, Gup);
    Mx = malloc(sizeof(fe) * (size_t)(N * L + 1) * cols); Kx = malloc(sizeof(fe) * (size_t)cols * cols);
    cl cls[64] = {0}, cur[64];
    if (start == 'F') {
        int mb = N - 1 - f; cl seen[64 * 64]; int ns = 0;
        for (int l = 0; l < Mm; l++) { cl s; int dup;
            do { s = 0; while (__builtin_popcountll(s) < ku) s |= 1ull << (1 + f + rng_below(mb)); dup = 0; for (int a = 0; a < ns; a++) dup |= (seen[a] == s); } while (dup);
            seen[ns++] = s; for (int q = 0; q < N; q++) if ((s >> q) & 1) cls[q] |= 1ull << l; }
    } else if (start == 'S') { // one-sided staircase of the [N/2, N/4] code on pairs of blocks: block 0 in every class, block 1 for the zeros
        cl seen[64 * 64]; int ns = 0, sb = N / 2 - 1;
        for (int l = 0; l < Mm; l++) { cl s; int dup;
            do { s = 0; while (__builtin_popcountll(s) < ku / 2) s |= 1ull << (1 + rng_below(sb)); dup = 0; for (int a = 0; a < ns; a++) dup |= (seen[a] == s); } while (dup);
            seen[ns++] = s; cls[0] |= 1ull << l; for (int q = 2; q < N; q++) if ((s >> (q / 2)) & 1) cls[q] |= 1ull << l; }
    } else {
        for (int q = 0; q < N; q++) for (int l = 0; l < Mm; l++) if (rng_below(100) < 55) cls[q] |= 1ull << l;
        while (!feasible(cls)) { int q = rng_below(N); if (!cls[q]) continue; int l; do l = rng_below(Mm); while (!((cls[q] >> l) & 1)); cls[q] &= ~(1ull << l); if (__builtin_popcountll(cls[q]) == 1 && rng_below(2)) cls[q] = 0; }
    }
    if (!feasible(cls)) { printf("start infeasible\n"); return 1; }
    long tot, btot; int best = score(cls, &btot), start_score = best; long acc = 0, imp = 0;
    for (long st = 0; st < steps; st++) {
        memcpy(cur, cls, sizeof cur);
        int cntb[64] = {0}; for (int q = 0; q < N; q++) for (int l = 0; l < Mm; l++) cntb[l] += (cur[q] >> l) & 1;
        int mn = cntb[0]; for (int l = 1; l < Mm; l++) if (cntb[l] < mn) mn = cntb[l];
        int l, q, kind = rng_below(4);
        if (kind < 3) { do l = rng_below(Mm); while (cntb[l] > mn + (kind == 2)); } else l = rng_below(Mm);
        int tries = 0; do q = rng_below(N); while (((cur[q] >> l) & 1) && ++tries < 100); if (tries >= 100) continue;
        cur[q] |= 1ull << l;
        if (kind >= 1) { int q2 = rng_below(N), l2 = rng_below(Mm), t2 = 0; while ((!((cur[q2] >> l2) & 1) || (q2 == q && l2 == l) || cntb[l2] <= mn) && ++t2 < 200) { q2 = rng_below(N); l2 = rng_below(Mm); } if (t2 < 200 && kind != 1) cur[q2] &= ~(1ull << l2); }
        int sc = score(cur, &tot);
        if (sc < best || (sc == best && tot < btot)) continue; // cheap test first
        if (!feasible(cur)) continue;
        if (sc > best) imp++; acc++; best = sc; btot = tot; memcpy(cls, cur, sizeof cur);
    }
    int nl = N << lo;
    printf("top [%d,%d] members=%d start=%c f=%d lift by %d (n=%d): start score %d = %.4f, best %d = %.4f after %ld steps (%ld accepted, %ld improving, %ld rank tests) | generalized Singleton value %ld | best: ", N, ku, Mm, start, f, lo, nl, start_score, (double)start_score / nl, best, (double)best / nl, steps, acc, imp, ntests, ((long)nl + (long)L * (nl / 2) - 1) / Mm);
    print_pat(cls);
    return 0;
}
