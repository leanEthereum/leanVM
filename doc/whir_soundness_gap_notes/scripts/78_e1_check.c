// Note 78, experiment 1: encoder against generator matrix for every variant, and the partner maps' cycle types.
// usage: 78_e1_check seed spec...   (sizes are fixed: (v, r) in {(2,1),(3,1),(4,1),(5,1),(6,1),(2,2),(4,2),(6,2)})
#include "78_var.h"
int main(int argc, char **argv) {
    rng_seed(strtoull(argv[1], 0, 10)); gf_init();
    int sizes[8][2] = {{2, 1}, {3, 1}, {4, 1}, {5, 1}, {6, 1}, {2, 2}, {4, 2}, {6, 2}};
    for (int a = 2; a < argc; a++) {
        long mism = 0, checked = 0, fixed = 0, twoc = 0, same_tree = 0, leaves = 0; int ok = 1, rkfail = 0;
        for (int s = 0; s < 8; s++) {
            int v = sizes[s][0], r = sizes[s][1]; var_t V;
            if (!var_make(&V, argv[a], v, r)) { ok = 0; break; }
            int n = V.n, k = V.k; fe *m = malloc(sizeof(fe) * k), *c = malloc(sizeof(fe) * n);
            for (int rep = 0; rep < 20; rep++) {
                for (int e = 0; e < k; e++) m[e] = gf_rand();
                var_encode(&V, m, c);
                for (int x = 0; x < n; x++) { fe sacc = 0; for (int e = 0; e < k; e++) sacc ^= gf_mul(V.G[(size_t)x * k + e], m[e]); mism += (sacc != c[x]); checked++; }
            }
            for (int d = 0; d < V.d; d++) for (int x = 0; x < n; x++) { leaves++; fixed += (V.pi[d][x] == x); twoc += (V.pi[d][x] != x && V.pi[d][V.pi[d][x]] == x); same_tree += ((V.pi[d][x] >> v) == (x >> v)); }
            fe *Gc = malloc(sizeof(fe) * (size_t)n * k); memcpy(Gc, V.G, sizeof(fe) * (size_t)n * k);
            if (gf_rank(Gc, n, k) != k) rkfail++;
            free(Gc); free(m); free(c); var_free(&V);
        }
        if (!ok) { printf("%-16s spec not accepted at some size\n", argv[a]); continue; }
        printf("%-16s encoder vs generator: %ld mismatches in %ld symbols; generator rank < k at %d of 8 sizes; partners: %ld leaf-partner pairs, %ld fixed points, %ld in 2-cycles, %ld in the leaf's own tree\n",
               argv[a], mism, checked, rkfail, leaves, fixed, twoc, same_tree);
    }
    return 0;
}
