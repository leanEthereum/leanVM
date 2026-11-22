// Referee 80: exact-rank test of note 76's Theorem 4.1 and Corollaries 4.2, 4.3 (rate 1/2, two trees).
// usage: 80_match <v> <members> <variant 1|2> <patterns> <seed>
// For every pattern: rank of the plain incidence system, against
//   (a) sum_x dim(L_x + L_mu(x)) for random bijections mu between the trees and for the best bijection (Hungarian),
//   (b) the sibling bound and cut bounds at every height with random level-swap isomorphisms,
//   (c) Theorem 4.1 with a random choice chi (rank >= rank P^0 + rank P^1 on the upper code).
#include "80_gf.h"

// max-weight perfect matching, k x k integer weights (Hungarian, O(k^3)); returns the weight, match[x] = y
static int hungarian_max(int k, const int *W, int *match) {
    // minimise cost = BIG - W
    int n = k, INF = 1 << 28;
    int *u = calloc(n + 1, sizeof(int)), *vv = calloc(n + 1, sizeof(int)), *p = calloc(n + 1, sizeof(int)), *way = calloc(n + 1, sizeof(int));
    int *minv = malloc(sizeof(int) * (n + 1)); char *used = malloc(n + 1);
    for (int i = 1; i <= n; i++) {
        p[0] = i; int j0 = 0;
        for (int j = 0; j <= n; j++) { minv[j] = INF; used[j] = 0; }
        do {
            used[j0] = 1; int i0 = p[j0], delta = INF, j1 = 0;
            for (int j = 1; j <= n; j++) if (!used[j]) {
                int cur = (100 - W[(i0 - 1) * k + (j - 1)]) - u[i0] - vv[j];
                if (cur < minv[j]) { minv[j] = cur; way[j] = j0; }
                if (minv[j] < delta) { delta = minv[j]; j1 = j; }
            }
            for (int j = 0; j <= n; j++) { if (used[j]) { u[p[j]] += delta; vv[j] -= delta; } else minv[j] -= delta; }
            j0 = j1;
        } while (p[j0] != 0);
        do { int j1 = way[j0]; p[j0] = p[j1]; j0 = j1; } while (j0);
    }
    int tot = 0;
    for (int j = 1; j <= n; j++) { match[p[j] - 1] = j - 1; tot += W[(p[j] - 1) * k + (j - 1)]; }
    free(u); free(vv); free(p); free(way); free(minv); free(used);
    return tot;
}

static unsigned rand_class(int members, double theta) {
    unsigned C = 0;
    for (int l = 0; l < members; l++) if ((rnd64() >> 11) * (1.0 / 9007199254740992.0) < theta) C |= 1u << l;
    return C;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("usage: 80_match v members variant patterns seed\n"); return 1; }
    int v = atoi(argv[1]), members = atoi(argv[2]), variant = atoi(argv[3]), npat = atoi(argv[4]);
    rnd_seed(strtoull(argv[5], 0, 10)); fe_selftest();
    int L = members - 1, k = 1 << v, n = 2 * k;
    unsigned full = (1u << members) - 1;
    tree_t T; tree_init(&T, v, 2, variant);
    // upper tree (one layer less) with the same upper twiddles
    tree_t Tu; Tu.v = v - 1; Tu.k = k / 2; Tu.ntrees = 2; Tu.n = n / 2; Tu.variant = variant;
    for (int i = 0; i + 1 < v; i++) Tu.tw[i] = T.tw[i + 1];
    Tu.G = malloc(sizeof(fe) * (size_t)Tu.n * Tu.k); tree_rows(&Tu);
    fe *M = malloc(sizeof(fe) * (size_t)(n * L + 1) * L * k);
    unsigned *cls = malloc(sizeof(unsigned) * n), *c0 = malloc(sizeof(unsigned) * n), *c1 = malloc(sizeof(unsigned) * n);
    int *W = malloc(sizeof(int) * k * k), *mu = malloc(sizeof(int) * k), *anyp = malloc(sizeof(int) * n); long nany = 0, viol_any = 0;
    long viol_rand = 0, viol_best = 0, viol_sib = 0, viol_cut = 0, viol_split = 0, dep = 0, eq_best = 0, eq_sib = 0, tested = 0, nrand = 0, ncut = 0;
    long kind_cnt[3] = {0, 0, 0}, kind_dep[3] = {0, 0, 0};
    int worst_best = 1 << 20, worst_sib = 1 << 20, worst_split = 1 << 20;
    for (int it = 0; it < npat; it++) {
        int kind = it % 3;
        double theta = 0.35 + 0.1 * (rnd_below(6));
        if (kind == 0) { // random classes
            for (int j = 0; j < n; j++) cls[j] = rand_class(members, theta);
        } else if (kind == 1) { // block-constant classes at a random scale, zeros of a lower factor in some blocks, a few flips
            int i = 1 + rnd_below(v > 1 ? v - 1 : 1), b = 1 << i;
            if (i > v) i = v;
            for (int q = 0; q < n / b; q++) {
                unsigned C = rand_class(members, theta);
                for (int j = 0; j < b; j++) cls[q * b + j] = C;
            }
            int nz = 1 + rnd_below(2);
            for (int z = 0; z < nz; z++) {
                int q = rnd_below(n / b), keep = rnd_below(b);
                for (int j = 0; j < b; j++) cls[q * b + j] = (j == keep) ? (rnd_below(2) ? 0 : 1u << rnd_below(members)) : full;
            }
            if (rnd_below(3) == 0) { int j = rnd_below(n); cls[j] = rand_class(members, theta); }
        } else { // staircase: member l agrees on a random half of the blocks other than q0; b - 1 common zeros in q0
            int i = 1 + rnd_below(v > 1 ? v - 1 : 1), b = 1 << i, N = n / b, q0 = rnd_below(N);
            for (int j = 0; j < n; j++) cls[j] = 0;
            for (int l = 0; l < members; l++) {
                int need = N / 2, left = N - 1;
                for (int q = 0; q < N; q++) {
                    if (q == q0) continue;
                    if ((int)rnd_below(left) < need) { need--; for (int j = 0; j < b; j++) cls[q * b + j] |= 1u << l; }
                    left--;
                }
            }
            int keep = rnd_below(b);
            for (int j = 0; j < b; j++) cls[q0 * b + j] = (j == keep) ? 0 : full;
        }
        int w = pat_matrix(&T, cls, L, M);
        if (w == 0) continue;
        int rk = fe_rank(M, w, L * k);
        tested++; kind_cnt[kind]++;
        if (rk < w) { dep++; kind_dep[kind]++; }
        // (a) random bijections and the best one
        for (int x = 0; x < k; x++) for (int y = 0; y < k; y++) W[x * k + y] = cls_sum_dim(cls[x], cls[k + y]);
        for (int r = 0; r < 20; r++) {
            for (int x = 0; x < k; x++) mu[x] = x;
            for (int x = k - 1; x > 0; x--) { int y = rnd_below(x + 1), t = mu[x]; mu[x] = mu[y]; mu[y] = t; }
            int bd = 0; for (int x = 0; x < k; x++) bd += W[x * k + mu[x]];
            nrand++;
            if (rk < bd) viol_rand++;
        }
        int best = hungarian_max(k, W, mu);
        { int chk = 0; for (int x = 0; x < k; x++) chk += W[x * k + mu[x]]; if (chk != best) { printf("hungarian inconsistent\n"); return 1; } }
        if (rk < best) { viol_best++; if (viol_best <= 5) { printf("VIOLATION best: rank %d bound %d w %d classes:", rk, best, w); for (int j = 0; j < n; j++) printf(" %x", cls[j]); printf("\n"); } }
        if (rk == best) eq_best++;
        if (rk - best < worst_best) worst_best = rk - best;
        // (b) sibling bound and cut bounds
        int sib = 0; for (int p = 0; p < n / 2; p++) sib += cls_sum_dim(cls[2 * p], cls[2 * p + 1]);
        if (rk < sib) { viol_sib++; if (viol_sib <= 5) { printf("VIOLATION sibling: rank %d bound %d w %d classes:", rk, sib, w); for (int j = 0; j < n; j++) printf(" %x", cls[j]); printf("\n"); } }
        if (rk == sib) eq_sib++;
        if (rk - sib < worst_sib) worst_sib = rk - sib;
        for (int h = 2; h <= v + 1; h++) { // node of height h has 2^h leaves; h = v + 1 pairs the two trees
            int half = 1 << (h - 1), bd = 0;
            for (int u = 0; u < n >> h; u++) {
                int mask = rnd_below(half); // level-swap isomorphism between the two children
                for (int x = 0; x < half; x++) bd += cls_sum_dim(cls[(u << h) + x], cls[(u << h) + half + (x ^ mask)]);
            }
            ncut++;
            if (rk < bd) { viol_cut++; if (viol_cut <= 5) printf("VIOLATION cut h=%d: rank %d bound %d\n", h, rk, bd); }
        }
        // (d) control: arbitrary perfect matchings of all n leaves (not covered by the corollaries)
        for (int r = 0; r < 20; r++) {
            for (int x = 0; x < n; x++) anyp[x] = x;
            for (int x = n - 1; x > 0; x--) { int y = rnd_below(x + 1), t = anyp[x]; anyp[x] = anyp[y]; anyp[y] = t; }
            int bd = 0; for (int x = 0; x < n; x += 2) bd += cls_sum_dim(cls[anyp[x]], cls[anyp[x + 1]]);
            nany++;
            if (rk < bd) { viol_any++; if (viol_any <= 2) { printf("  arbitrary matching, rank %d < %d:", rk, bd); for (int x = 0; x < n; x += 2) printf(" (%d,%d)", anyp[x], anyp[x + 1]); printf(" classes:"); for (int j = 0; j < n; j++) printf(" %x", cls[j]); printf("\n"); } }
        }
        // (c) Theorem 4.1 with random chi
        if (v >= 1) {
            for (int p = 0; p < n / 2; p++) { int ch = rnd_below(2); c0[p] = cls[2 * p + ch]; c1[p] = cls[2 * p + 1 - ch]; }
            int w0 = pat_matrix(&Tu, c0, L, M), r0 = w0 ? fe_rank(M, w0, L * k / 2) : 0;
            int w1 = pat_matrix(&Tu, c1, L, M), r1 = w1 ? fe_rank(M, w1, L * k / 2) : 0;
            if (rk < r0 + r1) { viol_split++; if (viol_split <= 5) printf("VIOLATION split: rank %d < %d + %d\n", rk, r0, r1); }
            if (rk - r0 - r1 < worst_split) worst_split = rk - r0 - r1;
        }
    }
    printf("(k,n)=(%d,%d) members=%d variant=T%d: %ld patterns (random %ld, block %ld, staircase %ld), dependent %ld (%ld, %ld, %ld)\n",
           k, n, members, variant, tested, kind_cnt[0], kind_cnt[1], kind_cnt[2], dep, kind_dep[0], kind_dep[1], kind_dep[2]);
    printf("  Cor 4.2: random bijections %ld, violations %ld; best bijection: violations %ld, rank = bound in %ld, least rank - bound %d\n", nrand, viol_rand, viol_best, eq_best, worst_best);
    printf("  Cor 4.3: sibling bound violations %ld (equal in %ld, least rank - bound %d); cut bounds tested %ld, violations %ld\n", viol_sib, eq_sib, worst_sib, ncut, viol_cut);
    printf("  Thm 4.1: violations %ld, least rank - (r0 + r1) = %d\n", viol_split, worst_split);
    printf("  control, arbitrary perfect matchings of the n leaves: %ld tested, bound above the rank in %ld\n", nany, viol_any);
    return 0;
}
