// Task 1: encoder against generator, subspace specialization = Reed-Solomon, singular minors.
// cc -O2 -DFB=64 69_t1_encoder.c -o t1_64 ; usage: t1 v r modes trials seed
#include "69_tree.h"

static int next_comb(int *c, int k, int n) { // next k-subset of [n] in lex order
    int i = k - 1;
    while (i >= 0 && c[i] == n - k + i) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    return 1;
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]); const char *modes = argv[3];
    long trials = atol(argv[4]); rng_seed(strtoull(argv[5], 0, 10));
    gf_init();
    int n = 1 << (v + r), k = 1 << v;
    fe *G = malloc(sizeof(fe) * n * k), *m = malloc(sizeof(fe) * k), *c = malloc(sizeof(fe) * n);
    fe *M = malloc(sizeof(fe) * n * 2 * k);
    // (i) encoder = G m ; (ii) for all-S modes: column space of G = Reed-Solomon code on the subspace
    tree_t T; tree_make(&T, v, r, modes); tree_gen(&T, G);
    for (int e = 0; e < k; e++) m[e] = gf_rand();
    tree_encode(&T, m, c);
    int bad = 0;
    for (int j = 0; j < n; j++) { fe s = 0; for (int e = 0; e < k; e++) s ^= gf_mul(G[j * k + e], m[e]); bad += (s != c[j]); }
    printf("v=%d r=%d modes=%s FB=%d: encoder vs generator mismatches %d of %d\n", v, r, modes, FB, bad, n);
    int allS = 1; for (int i = 0; i < v; i++) allS &= (modes[i] == 'S');
    if (allS) {
        for (int j = 0; j < n; j++) {
            fe y = 0, p = 1; for (int l = 0; l < v + r; l++) if ((j >> l) & 1) y ^= T.beta[l];
            for (int e = 0; e < k; e++) { M[j * 2 * k + e] = G[j * k + e]; M[j * 2 * k + k + e] = p; p = gf_mul(p, y); }
        }
        // rows are leaves; rank of [G | V] as an n x 2k matrix equals k iff the column spaces coincide
        printf("  rank [G | Vandermonde] = %d (k = %d: equal codes iff rank = k)\n", gf_rank(M, n, 2 * k), k);
        int ok = 1; // degree check: X_e has degree exactly e, i.e. V^{-1} G is triangular; test via T1 relation
        for (int i = 0; i < v; i++) for (int q = 0; q < (n >> i); q += 2) ok &= ((T.tw[i][q] ^ T.tw[i][q + 1]) == 1);
        printf("  subspace twiddles satisfy t(p,1) = t(p,0) + 1 at every node: %s\n", ok ? "yes" : "no");
    }
    tree_free(&T);
    // (iii) singular k x k minors over fresh twiddles
    long tested = 0, sing = 0; int comb[64];
    int exhaustive = (n <= 16);
    for (long t = 0; t < trials; t++) {
        tree_make(&T, v, r, modes); tree_gen(&T, G);
        if (exhaustive) {
            for (int i = 0; i < k; i++) comb[i] = i;
            do {
                for (int a = 0; a < k; a++) memcpy(M + a * k, G + comb[a] * k, sizeof(fe) * k);
                tested++; sing += (gf_rank(M, k, k) < k);
            } while (next_comb(comb, k, n));
        } else {
            for (int rep = 0; rep < 200; rep++) {
                int used[1024] = {0};
                for (int a = 0; a < k; a++) { int j; do j = (int)rng_below(n); while (used[j]); used[j] = 1; memcpy(M + a * k, G + j * k, sizeof(fe) * k); }
                tested++; sing += (gf_rank(M, k, k) < k);
            }
        }
        tree_free(&T);
    }
    double frac = (double)sing / tested;
    printf("  minors tested %ld (%s), singular %ld, fraction %.3e, fraction x |F| = %.3f\n", tested, exhaustive ? "all subsets per draw" : "200 random subsets per draw", sing, frac, frac * gf_order());
    return 0;
}
