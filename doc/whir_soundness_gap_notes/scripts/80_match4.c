// Referee 80: does note 76's Corollary 4.2 extend to four trees (rate 1/4)? Leaves are grouped in k groups of four, one leaf of
// each tree; the bound would be rank >= sum over groups of dim(sum of the four spaces). The proof (2-colouring) needs the graph
// "groups joined by sibling pairs" to be bipartite at every level. Test at v = 2 (k = 4, n = 16), general graphic spaces replaced
// with the exact dimension of a sum of graphic spaces (union-find on the members).
// usage: 80_match4 <members> <patterns> <seed> <variant>
#include "80_gf.h"
// dim of the sum of the graphic spaces of several classes: members minus connected components of the union hypergraph
static int sum_dim(const unsigned *c, int cnt, int members) {
    int par[16]; for (int l = 0; l < members; l++) par[l] = l;
    int dim = 0;
    for (int i = 0; i < cnt; i++) { if (popc(c[i]) < 2) continue; int first = -1;
        for (int l = 0; l < members; l++) if ((c[i] >> l) & 1) { int r = l; while (par[r] != r) r = par[r]; if (first < 0) first = r; else if (r != first) { par[r] = first; dim++; } } }
    return dim;
}
int main(int argc, char **argv) {
    int members = atoi(argv[1]), npat = atoi(argv[2]); rnd_seed(strtoull(argv[3], 0, 10)); int variant = argc > 4 ? atoi(argv[4]) : 2; fe_selftest();
    int L = members - 1; tree_t T; tree_init(&T, 2, 4, variant); int k = T.k, n = T.n;
    // group of leaf (tree j, position p): realizable system (same pairing in all trees) and a non-bipartite one (three pairings)
    static const int sysA[4][4] = {{0, 1, 2, 3}, {1, 0, 3, 2}, {2, 3, 0, 1}, {0, 1, 3, 2}}; // siblings always {0,1},{2,3}
    static const int sysB[4][4] = {{0, 1, 2, 3}, {0, 2, 1, 3}, {0, 3, 1, 2}, {0, 1, 2, 3}}; // pairings 01|23, 02|13, 03|12
    fe *M = malloc(sizeof(fe) * (size_t)(n * L + 1) * L * k); unsigned cls[16];
    long violA = 0, violB = 0, tested = 0; int worstA = 99, worstB = 99;
    for (int it = 0; it < npat; it++) {
        int th = 30 + rnd_below(50);
        for (int x = 0; x < n; x++) { cls[x] = 0; for (int l = 0; l < members; l++) if ((int)rnd_below(100) < th) cls[x] |= 1u << l; }
        int w = pat_matrix(&T, cls, L, M); if (!w) continue;
        int rk = fe_rank(M, w, L * k); tested++;
        for (int s = 0; s < 2; s++) {
            unsigned grp[4][4];
            for (int j = 0; j < 4; j++) for (int p = 0; p < 4; p++) grp[s ? sysB[j][p] : sysA[j][p]][j] = cls[j * 4 + p];
            int bd = 0; for (int g = 0; g < 4; g++) bd += sum_dim(grp[g], 4, members);
            if (s == 0) { if (rk < bd) violA++; if (rk - bd < worstA) worstA = rk - bd; }
            else { if (rk < bd) { violB++; if (violB <= 2) { printf("  counterexample (three pairings): rank %d < %d, classes:", rk, bd); for (int x = 0; x < n; x++) printf(" %x", cls[x]); printf("\n"); } } if (rk - bd < worstB) worstB = rk - bd; }
        }
    }
    printf("four trees, (k,n)=(4,16), T%d, %d members, %ld patterns: bipartite group system: %ld violations (least rank - bound %d); system with three pairings: %ld violations (least rank - bound %d)\n", variant, members, tested, violA, worstA, violB, worstB);
    return 0;
}
