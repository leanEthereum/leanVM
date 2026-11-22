// Referee 80: note 76, Lemma 1.1. For the rate-1/2 tree code with rows g_x, the code with every sibling pair of twiddles exchanged
// (rows g^sw_x) and Delta_x = prod_i (t_i(p,0) + t_i(p,1))^-1 along the path of x: sum_x g_x[e] Delta_x g^sw_x[e'] = 0 for all e, e'.
// usage: 80_dual <seed>   (T2 and T1, v = 1 .. 6)
#include "80_gf.h"
int main(int argc, char **argv) {
    rnd_seed(argc > 1 ? strtoull(argv[1], 0, 10) : 1); fe_selftest();
    for (int variant = 2; variant >= 1; variant--) for (int v = 1; v <= 6; v++) {
        tree_t T, S; tree_init(&T, v, 2, variant);
        S = T; S.G = malloc(sizeof(fe) * (size_t)T.n * T.k);
        for (int i = 0; i < v; i++) { int cnt = T.n >> i; S.tw[i] = malloc(sizeof(fe) * cnt); for (int p = 0; p < cnt; p++) S.tw[i][p] = T.tw[i][p ^ 1]; }
        tree_rows(&S);
        int nonzero = 0, k = T.k, n = T.n;
        fe *D = malloc(sizeof(fe) * n);
        for (int x = 0; x < n; x++) { fe d = 1; for (int i = 0; i < v; i++) d = fe_mul(d, T.tw[i][x >> i] ^ T.tw[i][(x >> i) ^ 1]); D[x] = fe_inv(d); }
        for (int e = 0; e < k; e++) for (int e2 = 0; e2 < k; e2++) {
            fe s = 0;
            for (int x = 0; x < n; x++) s ^= fe_mul(fe_mul(T.G[(size_t)x * k + e], D[x]), S.G[(size_t)x * k + e2]);
            if (s) nonzero++;
        }
        // without the multipliers the product must not vanish (control), and G^sw has rank k
        int ctrl = 0;
        for (int e = 0; e < k && !ctrl; e++) for (int e2 = 0; e2 < k && !ctrl; e2++) { fe s = 0; for (int x = 0; x < n; x++) s ^= fe_mul(T.G[(size_t)x * k + e], S.G[(size_t)x * k + e2]); if (s) ctrl = 1; }
        printf("T%d (k,n)=(%d,%d): nonzero entries of G^T Delta G^sw: %d of %d; rank G^sw = %d; control without Delta nonzero: %d\n", variant, k, n, nonzero, k * k, fe_rank(S.G, n, k), ctrl);
    }
    return 0;
}
