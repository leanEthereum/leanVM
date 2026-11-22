// Planted coincidences over GF(2^64) (or the compiled field): one vanishing minor of a top code, and what it wastes.
// usage: coinc_plant v r depth seed mode     depth j >= 1: the top code of the top j layers, [2^(j+r), 2^j] on blocks of k/2^j leaves.
// depth 1 plants two equal top twiddles in different trees; depth j >= 2 picks 2^j random blocks and solves one twiddle of
// layer v-j so that their minor vanishes. Then: rank on the union B of the blocks, and rank(G_Z) for random leaf sets Z
// against the prediction min(k, |Z \ B| + min(|Z n B|, k - block)), "one block wasted, nothing else".
#include "69_tree.h"
static fe det(const fe *A, int m) { // determinant by elimination (copy)
    fe *M = malloc(sizeof(fe) * m * m), d = 1; memcpy(M, A, sizeof(fe) * m * m);
    for (int c = 0; c < m; c++) {
        int p = -1; for (int i = c; i < m; i++) if (M[i * m + c]) { p = i; break; }
        if (p < 0) { free(M); return 0; }
        if (p != c) for (int j = 0; j < m; j++) { fe t = M[p * m + j]; M[p * m + j] = M[c * m + j]; M[c * m + j] = t; }
        d = gf_mul(d, M[c * m + c]); fe inv = gf_inv(M[c * m + c]);
        for (int i = c + 1; i < m; i++) { fe f = gf_mul(M[i * m + c], inv); if (f) for (int j = c; j < m; j++) M[i * m + j] ^= gf_mul(f, M[c * m + j]); }
    }
    free(M); return d;
}
static void top_rows(const tree_t *T, int lo, const int *P, int ku, fe *A) { // top-code rows of the blocks in P
    fe row[1 << MAXV];
    for (int a = 0; a < ku; a++) { tree_row(T, P[a] << lo, row); for (int e = 0; e < ku; e++) A[a * ku + e] = row[e << lo]; }
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), j = atoi(argv[3]); rng_seed(strtoull(argv[4], 0, 10)); char mode = argv[5][0];
    gf_init(); char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = mode; modes[v] = 0;
    tree_t T; tree_make(&T, v, r, modes);
    int n = T.n, k = T.k, lo = v - j, ku = 1 << j, N = n >> lo, bs = 1 << lo, P[64];
    fe *A = malloc(sizeof(fe) * ku * ku);
    if (j == 1) { P[0] = 0; P[1] = 2; T.tw[v - 1][2] = T.tw[v - 1][0]; if (mode == '1') T.tw[v - 1][3] = T.tw[v - 1][1]; }
    else for (;;) { // random blocks; the last one's layer-(v-j) twiddle is solved from det = det0 + y (det0 + det1) = 0
        int used[1024] = {0}; for (int a = 0; a < ku; a++) { int p; do p = (int)rng_below(N); while (used[p]); used[p] = 1; P[a] = p; }
        int q = P[ku - 1]; fe *slot = &T.tw[lo][q], saved = *slot;
        *slot = 0; top_rows(&T, lo, P, ku, A); fe d0 = det(A, ku);
        *slot = 1; top_rows(&T, lo, P, ku, A); fe d1 = det(A, ku);
        if (d0 == d1) { *slot = saved; continue; }
        *slot = gf_mul(d0, gf_inv(d0 ^ d1));
        if (*slot == T.tw[lo][q ^ 1]) { *slot = saved; continue; } // the root is the sibling's twiddle: not a tree code
        if (mode == '1') T.tw[lo][q ^ 1] = *slot ^ 1; // keep the T1 relation: this moves the sibling block too
        top_rows(&T, lo, P, ku, A); if (det(A, ku)) { fprintf(stderr, "planting failed\n"); return 1; }
        break;
    }
    fe *G = malloc(sizeof(fe) * n * k), *M = malloc(sizeof(fe) * n * k); tree_gen(&T, G);
    int inB[1024] = {0}, rows = 0; for (int a = 0; a < ku; a++) for (int x = 0; x < bs; x++) inB[(P[a] << lo) + x] = 1;
    for (int x = 0; x < n; x++) if (inB[x]) memcpy(M + (size_t)rows++ * k, G + (size_t)x * k, sizeof(fe) * k);
    int rkB = gf_rank(M, rows, k);
    printf("FB=%d mode=%c k=%d n=%d depth=%d: top code [%d,%d], blocks of %d leaves; union of the %d planted blocks has %d leaves, rank %d, nullity %d (one block = %d)\n",
           FB, mode, k, n, j, N, ku, bs, ku, rows, rkB, k - rkB, bs);
    long tests = 0, mism = 0, over = 0; int waste = k - rkB, maxw = 0, shown = 0;
    for (int t = 0; t < 40000; t++) { // leaf sets: a union of random blocks of random levels (half of the time biased to B), plus random leaves
        int sel[1024] = {0}, zin = 0, zout = 0; rows = 0;
        for (int c = (int)rng_below(2 * ku); c > 0; c--) { int lev = (int)rng_below(v), b = (int)rng_below(n >> lev); if ((t & 1) && !inB[b << lev]) continue; for (int x = 0; x < (1 << lev); x++) sel[(b << lev) + x] = 1; }
        for (int c = (int)rng_below(k); c > 0; c--) sel[rng_below(n)] = 1;
        for (int x = 0; x < n; x++) if (sel[x]) { memcpy(M + (size_t)rows++ * k, G + (size_t)x * k, sizeof(fe) * k); if (inB[x]) zin++; else zout++; }
        int sz = rows, rk = gf_rank(M, rows, k), pin = zin < k - waste ? zin : k - waste, pred = zout + pin < k ? zout + pin : k;
        int w = (sz < k ? sz : k) - rk;
        tests++; mism += (rk != pred); if (w > maxw) maxw = w; over += (w > bs);
        if (w > bs && !shown && sz <= k + bs) { shown = 1; // one example, in blocks of the planted level: count of selected leaves per block
            printf("  example wasting %d: planted blocks", w); for (int a = 0; a < ku; a++) printf(" %d", P[a]);
            printf("; |Z| = %d, leaves of Z per block:", sz); for (int b = 0; b < N; b++) { int c = 0; for (int x = 0; x < bs; x++) c += sel[(b << lo) + x]; printf(" %d", c); } printf("\n"); }
    }
    printf("  leaf sets Z (unions of blocks plus leaves): %ld tested; rank differs from the prediction for the planted minor alone in %ld; largest waste min(|Z|,k) - rank = %d; sets wasting more than one block: %ld\n", tests, mism, maxw, over);
    return 0;
}
