// Note 74, Theorem 4.2 (one functional per leaf): numerical check. Random constant vectors lambda_x in F_2^L \ 0 on a random
// set X of leaves (mode g: graphic vectors e_a - e_b only; mode a: any vector); rows lambda_x (x) g_x of the generic tree code.
// Claim: if no lambda used kills the whole kernel (the kernel is "genuine"), the rows are independent.
// usage: 74_thmA v r L trials seed mode
#include "69_pat.h"
#include "69_lin.h"
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), L = atoi(argv[3]); long trials = atol(argv[4]); rng_seed(strtoull(argv[5], 0, 10)); char mode = argv[6][0];
    gf_init(); int n = 1 << (v + r), k = 1 << v, cols = L * k;
    fe *G = malloc(sizeof(fe) * n * k), *M = malloc(sizeof(fe) * (size_t)n * cols), *Kb = malloc(sizeof(fe) * (size_t)cols * cols);
    long genuine = 0, viol = 0, dependent = 0, depgen = 0; int maxX = 0;
    for (long tr = 0; tr < trials; tr++) {
        if (tr % 2000 == 0) code_gen('2', v, r, G);
        int lam[MAXN], X[MAXN], nx = 0, target = (int)rng_below((uint64_t)(cols < n ? cols : n) + 1), used[1 << 8] = {0};
        // structured draws make dependencies likely: copy the vector of the sibling leaf or block with probability 1/2
        for (int x = 0; x < n; x++) lam[x] = 0;
        int blk = 1 << rng_below(v + 1);
        for (int x = 0; x < n; x++) {
            if ((int)rng_below(n) >= target + 2) continue;
            int l;
            if ((x % blk) && lam[x - 1] && rng_below(4) < 3) l = lam[x - 1];
            else if (mode == 'g') { int a = rng_below(L + 1), b; do b = rng_below(L + 1); while (b == a); l = (a ? 1 << (a - 1) : 0) | (b ? 1 << (b - 1) : 0); }
            else l = 1 + (int)rng_below((1u << L) - 1);
            lam[x] = l; X[nx++] = x; used[l] = 1;
        }
        if (!nx) continue;
        for (int a = 0; a < nx; a++) { fe *row = M + (size_t)a * cols; memset(row, 0, sizeof(fe) * cols);
            for (int l = 0; l < L; l++) if ((lam[X[a]] >> l) & 1) memcpy(row + l * k, G + (size_t)X[a] * k, sizeof(fe) * k); }
        int dim = gf_kernel(M, nx, cols, Kb), rank = cols - dim, gen = dim > 0;
        for (int l = 1; l < (1 << L) && gen; l++) { if (!used[l]) continue; int all = 1;
            for (int t = 0; t < dim && all; t++) for (int e = 0; e < k && all; e++) { fe s = 0; for (int j = 0; j < L; j++) if ((l >> j) & 1) s ^= Kb[(size_t)t * cols + j * k + e]; all = (s == 0); }
            if (all) gen = 0; }
        if (rank < nx) dependent++;
        if (gen) { genuine++; if (nx > maxX) maxX = nx; if (rank < nx) { viol++; depgen++; } }
    }
    printf("v=%d r=%d L=%d mode=%c: trials %ld, dependent rows %ld, genuine kernel %ld (largest |X| among them %d, Lk-1 = %d), genuine AND dependent (violations of the theorem) %ld\n", v, r, L, mode, trials, dependent, genuine, maxX, cols - 1, viol);
    return 0;
}
