// Note 74, task 4: the one-sided staircase, checked by encoding. Split level lo, N = n/2^lo blocks, k_up = k/2^lo.
// Block 0 carries all 2^lo - 1 zeros of the lower factor B; blocks 1..f are free (their leaves and the last leaf of block 0
// are handed to the weakest members); the members are the interpolants A_S (x) B of a random block word through the
// k_up-subsets S of the other N - 1 - f blocks (all of them, or the first `want` in a random order).
// usage: 74_stair v r lo f want seed
#include "69_tree.h"
#include "69_lin.h"
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), lo = atoi(argv[3]), f = atoi(argv[4]); long want = atol(argv[5]);
    rng_seed(strtoull(argv[6], 0, 10)); gf_init();
    char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = '2'; modes[v] = 0;
    tree_t T; tree_make(&T, v, r, modes);
    int n = T.n, k = T.k, N = n >> lo, ku = k >> lo, kl = 1 << lo, m0 = 1 + f, mb = N - m0;
    fe *row = malloc(sizeof(fe) * k), *Gup = malloc(sizeof(fe) * N * ku), *wup = malloc(sizeof(fe) * N);
    for (int p = 0; p < N; p++) { tree_row(&T, p << lo, row); for (int e = 0; e < ku; e++) Gup[p * ku + e] = row[e << lo]; wup[p] = gf_rand(); }
    // all k_up-subsets of blocks m0..N-1
    long total = 1; for (int a = 0; a < ku; a++) total = total * (mb - a) / (a + 1);
    int *S = malloc(sizeof(int) * (size_t)total * ku), c[64]; long cnt = 0;
    for (int a = 0; a < ku; a++) c[a] = a;
    for (;;) { for (int a = 0; a < ku; a++) S[cnt * ku + a] = m0 + c[a]; cnt++;
        int a = ku - 1; while (a >= 0 && c[a] == mb - ku + a) a--; if (a < 0) break; c[a]++; for (int b = a + 1; b < ku; b++) c[b] = c[b - 1] + 1; }
    if (want < total) { for (long i = 0; i < want; i++) { long j = i + (long)rng_below((uint64_t)(total - i)); for (int a = 0; a < ku; a++) { int t = S[i * ku + a]; S[i * ku + a] = S[j * ku + a]; S[j * ku + a] = t; } } }
    long nm = want < total ? want : total;
    // B: zero on the first kl - 1 leaves of block 0
    fe *Z = malloc(sizeof(fe) * kl * kl), *B = malloc(sizeof(fe) * kl * kl);
    for (int a = 0; a < kl - 1; a++) { tree_row(&T, a, row); memcpy(Z + a * kl, row, sizeof(fe) * kl); }
    int dB = gf_kernel(Z, kl - 1, kl, B);
    fe *m = calloc(k, sizeof(fe)), *cw = malloc(sizeof(fe) * n), *w = malloc(sizeof(fe) * n), *A = malloc(sizeof(fe) * ku), *Ms = malloc(sizeof(fe) * ku * ku), *bs = malloc(sizeof(fe) * ku);
    memcpy(m, B, sizeof(fe) * kl); tree_encode(&T, m, w);
    int bz = 0; for (int j = 0; j < n; j++) { bz += !w[j]; w[j] = gf_mul(w[j], wup[j >> lo]); }
    long *ag = calloc(nm, sizeof(long)); long wrong = 0, singular = 0;
    for (long l = 0; l < nm; l++) {
        int *s = S + l * ku;
        for (int a = 0; a < ku; a++) { memcpy(Ms + a * ku, Gup + s[a] * ku, sizeof(fe) * ku); bs[a] = wup[s[a]]; }
        if (!gf_solve(Ms, bs, ku, A)) { singular++; continue; }
        for (int e = 0; e < ku; e++) for (int ff = 0; ff < kl; ff++) m[(e << lo) | ff] = gf_mul(A[e], B[ff]);
        tree_encode(&T, m, cw);
        // agreement on the non-free blocks m0..N-1 and on the zeros of block 0; it must be exactly the member's blocks plus the zeros
        long a1 = 0, expect = (long)ku * kl + (kl - 1);
        for (int j = 0; j < kl - 1; j++) a1 += (cw[j] == 0);
        for (int j = m0 << lo; j < n; j++) a1 += (cw[j] == w[j]);
        if (a1 != expect) wrong++;
        ag[l] = a1;
    }
    // free leaves: the last leaf of block 0 and the leaves of blocks 1..f, one member each, weakest first
    long freeleaves = 1 + (long)f * kl, base = freeleaves / nm, rem = freeleaves % nm;
    long amin = (long)ku * kl + (kl - 1) + base; (void)rem;
    printf("k=%d n=%d split level %d: N=%d k_up=%d, free blocks %d, members %ld of %ld (zeros of B: %d, kernel dim %d), singular interpolations %ld, members whose agreement on the constrained leaves is not k_up 2^lo + 2^lo - 1: %ld | constrained agreement %ld, with the free leaves: min agreement %ld = %.5f n | generalized Singleton value for %ld members: %ld\n",
           k, n, lo, N, ku, f, nm, total, bz, dB, singular, wrong, (long)ku * kl + (kl - 1), amin, (double)amin / n, nm, (n + (nm - 1) * (long)k - 1) / nm);
    return 0;
}
