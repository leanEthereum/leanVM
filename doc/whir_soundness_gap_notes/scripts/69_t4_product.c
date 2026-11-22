// Task 4: lists of rank-one tensors A_l (x) B. Lower factor B over the bottom i layers (shared), upper factors A_l
// interpolating a random upper word on k_up of the N = n/2^i blocks. Direct check of the agreements by encoding.
// usage: t4_product v r i members seed modes     (modes: one of 1,2,S per layer, bottom first)
#include "69_tree.h"
#include "69_lin.h"
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), lo = atoi(argv[3]), want = atoi(argv[4]);
    rng_seed(strtoull(argv[5], 0, 10)); const char *modes = argv[6]; gf_init();
    tree_t T; tree_make(&T, v, r, modes);
    int n = T.n, k = T.k, N = n >> lo, ku = k >> lo, kl = 1 << lo;
    fe *row = malloc(sizeof(fe) * k), *Gup = malloc(sizeof(fe) * N * ku), *wup = malloc(sizeof(fe) * N);
    for (int p = 0; p < N; p++) { tree_row(&T, p << lo, row); for (int e = 0; e < ku; e++) Gup[p * ku + e] = row[e << lo]; wup[p] = gf_rand(); }
    // members: random k_up-subsets of the blocks
    int *S = malloc(sizeof(int) * want * ku), nm = 0; fe *A = malloc(sizeof(fe) * want * ku), *Ms = malloc(sizeof(fe) * ku * ku), *bs = malloc(sizeof(fe) * ku);
    for (int tries = 0; nm < want && tries < 100 * want; tries++) {
        int used[MAXV * 0 + 1024] = {0}, *s = S + nm * ku;
        for (int a = 0; a < ku; a++) { int p; do p = (int)rng_below(N); while (used[p]); used[p] = 1; }
        for (int p = 0, a = 0; p < N; p++) if (used[p]) s[a++] = p;
        int dup = 0; for (int m = 0; m < nm && !dup; m++) dup = !memcmp(S + m * ku, s, sizeof(int) * ku);
        if (dup) continue;
        for (int a = 0; a < ku; a++) { memcpy(Ms + a * ku, Gup + s[a] * ku, sizeof(fe) * ku); bs[a] = wup[s[a]]; }
        if (gf_solve(Ms, bs, ku, A + nm * ku)) nm++;
    }
    // zeros of B: kl - 1 leaves, placed greedily in the blocks that raise the smallest gains
    int *z = calloc(N, sizeof(int)), *gain = calloc(nm, sizeof(int)), *cover = calloc((size_t)nm * N, sizeof(int));
    for (int m = 0; m < nm; m++) for (int a = 0; a < ku; a++) cover[m * N + S[m * ku + a]] = 1;
    for (int t = 0; t < kl - 1; t++) {
        int mn = gain[0]; for (int m = 1; m < nm; m++) if (gain[m] < mn) mn = gain[m];
        int best = -1; long bs2 = -1;
        for (int p = 0; p < N; p++) {
            if (z[p] == kl) continue;
            long sc = 0; for (int m = 0; m < nm; m++) if (!cover[m * N + p]) sc += (gain[m] == mn) ? 1000000 : 1;
            sc = sc * 4 + (3 - (z[p] < 3 ? z[p] : 3));
            if (sc > bs2) { bs2 = sc; best = p; }
        }
        z[best]++; for (int m = 0; m < nm; m++) if (!cover[m * N + best]) gain[m]++;
    }
    fe *Z = malloc(sizeof(fe) * kl * kl), *B = malloc(sizeof(fe) * kl * kl); int nz = 0;
    for (int p = 0; p < N; p++) for (int a = 0; a < z[p]; a++) { tree_row(&T, (p << lo) + a, row); memcpy(Z + nz * kl, row, sizeof(fe) * kl); nz++; }
    int dB = gf_kernel(Z, nz, kl, B);
    // encode and count
    fe *m = calloc(k, sizeof(fe)), *c = malloc(sizeof(fe) * n), *w = malloc(sizeof(fe) * n);
    memcpy(m, B, sizeof(fe) * kl); tree_encode(&T, m, w);
    int bz = 0; for (int j = 0; j < n; j++) { bz += !w[j]; w[j] = gf_mul(w[j], wup[j >> lo]); }
    int amin = n, amax = 0; long asum = 0;
    for (int l = 0; l < nm; l++) {
        for (int e = 0; e < ku; e++) for (int f = 0; f < kl; f++) m[(e << lo) | f] = gf_mul(A[l * ku + e], B[f]);
        tree_encode(&T, m, c);
        int ag = 0; for (int j = 0; j < n; j++) ag += (c[j] == w[j]);
        if (ag < amin) amin = ag; if (ag > amax) amax = ag; asum += ag;
    }
    int L = nm - 1; long gen = L ? (n + (long)L * k - 1) / (L + 1) : n;
    printf("FB=%d modes=%s k=%d n=%d lower layers=%d k_up=%d N=%d: members=%d (kernel dim of B %d, zeros of B %d) agreement min=%d mean=%.2f max=%d | generalized Singleton bound on the minimum for %d members: %ld | excess %ld leaves = %.4f n\n",
           FB, modes, k, n, lo, ku, N, nm, dB, bz, amin, (double)asum / nm, amax, nm, gen, amin - gen, (double)(amin - gen) / n);
    return 0;
}
