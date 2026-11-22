// Coincidences over a small field, exhaustively at k = 8, n = 16 (v = 3, r = 1): every 8-subset Z of leaves, its nullity,
// and whether a vanishing minor of a top code explains it. usage: coinc_exh draws seed mode   (compile with -DFB=8 or 16)
// Level 1: top [8,4] code on the 8 sibling pairs (block 2). Level 2: top [4,2] code on the 4 quads (block 4).
// A top minor P of nullity nu at block size b forces nullity >= b nu - |union(P) \ Z| on Z ("explained").
#include "69_tree.h"
static int next_comb(int *c, int k, int n) { int i = k - 1; while (i >= 0 && c[i] == n - k + i) i--; if (i < 0) return 0; c[i]++; for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1; return 1; }
int main(int argc, char **argv) {
    if (argc < 4) return 1;
    long draws = atol(argv[1]); rng_seed(strtoull(argv[2], 0, 10)); char mode = argv[3][0]; gf_init();
    const int v = 3, r = 1; char modes[4] = {mode, mode, mode, 0};
    fe G[16 * 8], M[8 * 8], row[8];
    long nZ = 0, prim[9] = {0}, exact = 0, more[9] = {0}, contra = 0;
    long l1 = 0, l1prim[5] = {0}, l1expl = 0, l2 = 0, l1tot = 0, l2tot = 0;
    for (long d = 0; d < draws; d++) {
        tree_t T; tree_make(&T, v, r, modes); tree_gen(&T, G);
        // level 2: quads, rows (1, x_2)
        uint32_t m2[8]; int nu2[8], n2 = 0; int c2[2] = {0, 1};
        do { l2tot++; if (T.tw[2][c2[0]] == T.tw[2][c2[1]]) { m2[n2] = (0xFu << (4 * c2[0])) | (0xFu << (4 * c2[1])); nu2[n2++] = 1; } } while (next_comb(c2, 2, 4));
        l2 += n2;
        // level 1: pairs, rows (1, x_1, x_2, x_1 x_2)
        uint32_t m1[80]; int nu1[80], n1 = 0; int c1[4] = {0, 1, 2, 3};
        do {
            l1tot++;
            for (int a = 0; a < 4; a++) { tree_row(&T, c1[a] << 1, row); for (int e = 0; e < 4; e++) M[a * 4 + e] = row[e << 1]; }
            int nu = 4 - gf_rank(M, 4, 4); if (!nu) continue;
            uint32_t mask = 0; for (int a = 0; a < 4; a++) mask |= 3u << (2 * c1[a]);
            int ex = 0; for (int t = 0; t < n2; t++) { int e = 2 * nu2[t] - __builtin_popcount(m2[t] & ~mask) / 2; if (e > ex) ex = e; } // in pairs
            l1++; if (ex >= nu) l1expl++; else l1prim[nu]++;
            m1[n1] = mask; nu1[n1++] = nu;
        } while (next_comb(c1, 4, 8));
        int cz[8] = {0, 1, 2, 3, 4, 5, 6, 7};
        do {
            uint32_t zm = 0; for (int a = 0; a < 8; a++) { zm |= 1u << cz[a]; memcpy(M + a * 8, G + cz[a] * 8, sizeof(fe) * 8); }
            int nu = 8 - gf_rank(M, 8, 8), ex = 0; nZ++;
            for (int t = 0; t < n1; t++) { int e = 2 * nu1[t] - __builtin_popcount(m1[t] & ~zm); if (e > ex) ex = e; }
            for (int t = 0; t < n2; t++) { int e = 4 * nu2[t] - __builtin_popcount(m2[t] & ~zm); if (e > ex) ex = e; }
            if (nu < ex) contra++; else if (ex == 0) { if (nu) prim[nu]++; } else if (nu == ex) exact++; else more[nu - ex]++;
        } while (next_comb(cz, 8, 16));
        tree_free(&T);
    }
    double q = gf_order();
    printf("FB=%d mode=%c k=8 n=16 draws=%ld\n", FB, mode, draws);
    printf("  level 2 (two quads, equal top twiddles): %ld of %ld minors singular (x|F| = %.2f)\n", l2, l2tot, q * l2 / l2tot);
    printf("  level 1 ([8,4] on pairs): %ld of %ld minors singular (x|F| = %.2f); explained by level 2: %ld; primitive with nullity 1: %ld, nullity 2: %ld, nullity 3: %ld\n", l1, l1tot, q * l1 / l1tot, l1expl, l1prim[1], l1prim[2], l1prim[3]);
    printf("  leaf sets Z: %ld; primitive singular (no top minor involved): nullity 1: %ld (x|F| = %.3f), nullity 2: %ld, nullity >= 3: %ld\n", nZ, prim[1], q * prim[1] / nZ, prim[2], prim[3] + prim[4] + prim[5]);
    long expl = exact; for (int i = 1; i < 9; i++) expl += more[i];
    printf("  Z with a forced nullity from a top minor: %ld; nullity exactly as forced: %ld; one more: %ld (fraction x|F| = %.3f); two more: %ld; three or more: %ld; less than forced (must be 0): %ld\n",
           expl, exact, more[1], expl ? q * more[1] / expl : 0.0, more[2], more[3] + more[4] + more[5], contra);
    return 0;
}
