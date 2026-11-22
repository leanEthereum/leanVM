// Note 78, experiment 5(b) for V2: a staircase ADAPTED to V2 `up`, checked by encoding only.
// For M = up the messages A(X_up) B(X_low) with B invariant under complementing all `lo` low index bits (B_e = B_{~e}) are
// products for both trees (property (P5) of the note). The space of such B has dimension 2^(lo-1); B is chosen with
// 2^(lo-1) - 1 zeros in block 0 (leaves 0..). beta = encoding of 1 (x) B; the top code is read off the encoder:
// Gtop[q][e] = enc(e (x) B)(x_q) / beta(x_q). Members: interpolants A_S (x) B of a random block word through the k_up-subsets S
// of blocks 1..N-1. The program checks that every member agrees with the word w(x) = wup(block x) beta(x) on exactly its blocks
// and the zeros, i.e. that the list is a genuine list of the V2 code.
// usage: 78_e5_v2stair v r lo want seed spec     (spec: T2:Mup; with T2 the same construction is not a product family: control)
#include "78_var.h"
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), lo = atoi(argv[3]); long want = atol(argv[4]); rng_seed(strtoull(argv[5], 0, 10)); gf_init();
    var_t V; if (!var_make(&V, argv[6], v, r)) { printf("bad spec\n"); return 1; }
    int n = V.n, k = V.k, N = n >> lo, ku = k >> lo, kl = 1 << lo, hb = kl / 2, nz = hb - 1;
    // basis of the complement-invariant B: pairs {e, ~e}; solve for zeros at leaves 0..nz-1
    fe *m = calloc(k, sizeof(fe)), *c = malloc(sizeof(fe) * n), *Zm = malloc(sizeof(fe) * (size_t)(nz + 1) * hb), *Kz = malloc(sizeof(fe) * (size_t)hb * hb);
    for (int b = 0; b < hb; b++) { memset(m, 0, sizeof(fe) * k); m[b] = 1; m[(kl - 1) ^ b] = 1; var_encode(&V, m, c); for (int z = 0; z < nz; z++) Zm[(size_t)z * hb + b] = c[z]; }
    int dB = nz ? gf_kernel(Zm, nz, hb, Kz) : 1; if (!nz) Kz[0] = 1;
    fe *B = calloc(kl, sizeof(fe)); for (int b = 0; b < hb; b++) { B[b] = Kz[b]; B[(kl - 1) ^ b] = Kz[b]; }
    fe *beta = malloc(sizeof(fe) * n); memset(m, 0, sizeof(fe) * k); memcpy(m, B, sizeof(fe) * kl); var_encode(&V, m, beta);
    int bz = 0; for (int x = 0; x < n; x++) bz += !beta[x];
    // top code from the encoder, and the check that it is constant on blocks
    fe *Gup = malloc(sizeof(fe) * (size_t)N * ku); long notconst = 0;
    for (int e = 0; e < ku; e++) {
        memset(m, 0, sizeof(fe) * k); for (int f = 0; f < kl; f++) m[(e << lo) | f] = B[f]; var_encode(&V, m, c);
        for (int q = 0; q < N; q++) { fe val = 0; int have = 0;
            for (int f = 0; f < kl; f++) { int x = (q << lo) + f; if (!beta[x]) continue; fe t = gf_mul(c[x], gf_inv(beta[x])); if (!have) { val = t; have = 1; } else notconst += (t != val); }
            Gup[(size_t)q * ku + e] = val; }
    }
    fe *wup = malloc(sizeof(fe) * N), *w = malloc(sizeof(fe) * n); for (int q = 0; q < N; q++) wup[q] = gf_rand();
    for (int x = 0; x < n; x++) w[x] = gf_mul(wup[x >> lo], beta[x]);
    int mb = N - 1; long total = 1; for (int a = 0; a < ku; a++) total = total * (mb - a) / (a + 1);
    int *S = malloc(sizeof(int) * (size_t)total * ku), cc[64]; long cnt = 0;
    for (int a = 0; a < ku; a++) cc[a] = a;
    for (;;) { for (int a = 0; a < ku; a++) S[cnt * ku + a] = 1 + cc[a]; cnt++;
        int a = ku - 1; while (a >= 0 && cc[a] == mb - ku + a) a--; if (a < 0) break; cc[a]++; for (int b = a + 1; b < ku; b++) cc[b] = cc[b - 1] + 1; }
    if (want < total) for (long i = 0; i < want; i++) { long j = i + (long)rng_below((uint64_t)(total - i)); for (int a = 0; a < ku; a++) { int t = S[i * ku + a]; S[i * ku + a] = S[j * ku + a]; S[j * ku + a] = t; } }
    long nm = want < total ? want : total, singular = 0, amin = n, amax = 0, wrong = 0;
    fe *Ms = malloc(sizeof(fe) * ku * ku), *bs = malloc(sizeof(fe) * ku), *A = malloc(sizeof(fe) * ku);
    for (long l = 0; l < nm; l++) {
        int *s = S + l * ku;
        for (int a = 0; a < ku; a++) { memcpy(Ms + a * ku, Gup + (size_t)s[a] * ku, sizeof(fe) * ku); bs[a] = wup[s[a]]; }
        if (!gf_solve(Ms, bs, ku, A)) { singular++; continue; }
        for (int e = 0; e < ku; e++) for (int f = 0; f < kl; f++) m[(e << lo) | f] = gf_mul(A[e], B[f]);
        var_encode(&V, m, c);
        long ag = 0; for (int x = 0; x < n; x++) ag += (c[x] == w[x]);
        if (ag < amin) amin = ag; if (ag > amax) amax = ag; wrong += (ag != (long)ku * kl + bz);
    }
    long gs = (n + (nm - 1) * (long)k - 1) / nm;
    printf("%s (k,n)=(%d,%d) split level %d: N=%d blocks of %d, k_up=%d; invariant lower factors: dimension %d, zeros of B %d (kernel %d); block values not constant: %ld | members %ld of %ld, singular interpolations %ld, agreement min %ld max %ld = %.4f n (members not at k + zeros: %ld) | gS value for %ld members: %ld | plain tree code's one-sided staircase: %d\n",
           argv[6], k, n, lo, N, kl, ku, hb, bz, dB, notconst, nm, total, singular, amin, amax, (double)amin / n, wrong, nm, gs, k + kl - 1);
    return 0;
}
