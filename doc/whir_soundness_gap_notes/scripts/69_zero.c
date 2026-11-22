// Largest zero sets of a tree code over a small field from vanishing minors of its top codes.
// A k_up x k_up minor of nullity nu of the top code at block size b gives a (b nu)-dimensional family vanishing on k
// leaves, hence a nonzero codeword with k + b nu - 1 zeros. usage: zero v r draws seed mode [samples]
#include "69_tree.h"
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]); long draws = atol(argv[3]); rng_seed(strtoull(argv[4], 0, 10)); char mode = argv[5][0];
    long samples = argc > 6 ? atol(argv[6]) : 100000; gf_init();
    char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = mode; modes[v] = 0;
    int n = 1 << (v + r), k = 1 << v; fe *A = malloc(sizeof(fe) * k * k), *row = malloc(sizeof(fe) * k);
    long hist[1024] = {0}, lvl[MAXV] = {0}; double sum = 0;
    for (long d = 0; d < draws; d++) {
        tree_t T; tree_make(&T, v, r, modes);
        int best = 0, bestlev = -1;
        for (int lo = v - 1; lo >= 0; lo--) { // lo = number of bottom layers inside a block
            int ku = k >> lo, N = n >> lo, bs = 1 << lo, comb[1024];
            double cnt = 1; for (int a = 0; a < ku; a++) cnt = cnt * (N - a) / (a + 1);
            int exhaustive = cnt <= (double)samples; long todo = exhaustive ? (long)(cnt + 0.5) : samples;
            for (int a = 0; a < ku; a++) comb[a] = a;
            for (long t = 0; t < todo; t++) {
                if (!exhaustive) { int used[1024] = {0}; for (int a = 0; a < ku; a++) { int p; do p = (int)rng_below(N); while (used[p]); used[p] = 1; comb[a] = p; } }
                for (int a = 0; a < ku; a++) { tree_row(&T, comb[a] << lo, row); for (int e = 0; e < ku; e++) A[a * ku + e] = row[e << lo]; }
                int nu = ku - gf_rank(A, ku, ku);
                if (bs * nu > best) { best = bs * nu; bestlev = lo; }
                if (exhaustive) { int i = ku - 1; while (i >= 0 && comb[i] == N - ku + i) i--; if (i < 0) break; comb[i]++; for (int j = i + 1; j < ku; j++) comb[j] = comb[j - 1] + 1; }
            }
        }
        hist[best]++; sum += best; if (bestlev >= 0) lvl[bestlev]++;
        tree_free(&T);
    }
    printf("FB=%d mode=%c k=%d n=%d draws=%ld (top minors: all when at most %ld, else %ld random ones per level)\n", FB, mode, k, n, draws, samples, samples);
    printf("  excess zeros over k-1 (largest block x nullity found): mean %.2f = %.4f n; distribution:", sum / draws, sum / draws / n);
    for (int e = 0; e < 1024; e++) if (hist[e]) printf(" %d:%ld", e, hist[e]);
    printf("\n  level of the best minor (bottom layers inside a block):"); for (int i = 0; i < v; i++) if (lvl[i]) printf(" %d:%ld", i, lvl[i]);
    printf("\n");
    return 0;
}
