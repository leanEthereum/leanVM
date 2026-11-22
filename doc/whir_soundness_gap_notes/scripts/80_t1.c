// Referee 80: three-member patterns at (8,16) on which the T1 and T2 generic ranks differ (by-product of 80_conj44 rand16).
// usage: 80_t1 <seed> "<16 or 32 leaf types 0..4>" ...   types: 0 none, 1 = {0,1}, 2 = {0,2}, 3 = {1,2}, 4 = {0,1,2}
#include "80_gf.h"
int main(int argc, char **argv) {
    rnd_seed(strtoull(argv[1], 0, 10)); fe_selftest();
    static const unsigned CLS[5] = {0, 3, 5, 6, 7};
    for (int a = 2; a < argc; a++) {
        unsigned cls[32]; int cnt = 0; char buf[512]; strncpy(buf, argv[a], 511); buf[511] = 0;
        for (char *tok = strtok(buf, " "); tok && cnt < 32; tok = strtok(NULL, " ")) cls[cnt++] = CLS[atoi(tok)];
        if (cnt != 16 && cnt != 32) return 1;
        int v = cnt == 16 ? 3 : 4, k = cnt / 2;
        printf("pattern %s:", argv[a]);
        for (int variant = 2; variant >= 1; variant--) {
            tree_t T; tree_init(&T, v, 2, variant);
            static fe M[80 * 32], Kb[32 * 32]; int w = pat_matrix(&T, cls, 2, M), dim = fe_kernel(M, w, 2 * k, Kb);
            int g1 = 0, g2 = 0, g12 = 0;
            for (int d = 0; d < dim; d++) for (int e = 0; e < k; e++) { fe u1 = Kb[d * 2 * k + e], u2 = Kb[d * 2 * k + k + e]; if (u1) g1 = 1; if (u2) g2 = 1; if (u1 ^ u2) g12 = 1; }
            printf("  T%d: weight %d, rank %d, solution space of dimension %d, three distinct codewords: %s;", variant, w, 2 * k - dim, dim, (g1 && g2 && g12) ? "yes" : "no");
        }
        printf("\n");
    }
    return 0;
}
