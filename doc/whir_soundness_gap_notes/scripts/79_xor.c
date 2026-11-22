// Note 79, Section 4: the one-sided staircase of note 74 (Proposition 6.1) under V1 with d = 1,
// for a partner map x -> x XOR m (m flips the tree bit) and for a uniformly random permutation.
// Members A_S (x) B, S a set of k_up blocks closed under q -> q XOR bl(m); the word is the mixed image of the plain word.
// Checks by encoding over GF(2^64): agreement of every member with the word, and the sum against n + L k.
// usage: 79_xor v i seed   (rate 1/2, blocks of 2^i leaves, N = 2^(v+1-i) blocks)
#include "75_gf.h"
#define MAXN 256
#define MAXK 128
static int v, n, k, ib, N, kup, bs;
static fe tw[8][MAXN];
static fe up_row(int q, int e) { fe a = 1; for (int l = ib; l < v; l++) if ((e >> (l - ib)) & 1) a = gf_mul(a, tw[l][(q << ib) >> l]); return a; }
static fe low_row(int y, int e) { fe a = 1; for (int l = 0; l < ib; l++) if ((e >> l) & 1) a = gf_mul(a, tw[l][y >> l]); return a; }
int main(int argc, char **argv) {
    if (argc < 4) { printf("usage: v i seed\n"); return 1; }
    v = atoi(argv[1]); ib = atoi(argv[2]); rng_seed(strtoull(argv[3], 0, 0)); gf_selftest();
    n = 2 << v; k = 1 << v; bs = 1 << ib; N = n / bs; kup = k / bs;
    for (int l = 0; l < v; l++) for (int p = 0; p < (n >> l); p++) tw[l][p] = rnd();
    int m = n / 2 + 1 + 2 * (int)rnd_below(bs / 2); // flips the tree bit, bit 0 and some low bits: bl(m) = N/2
    int blm = m >> ib, q0 = 0, q1 = q0 ^ blm;
    // zeros of B: pairs {z, z^m} inside blocks q0, q1, plus one more leaf of q0
    int Z[MAXN], nz = 0;
    for (int t = 0; nz + 2 <= bs - 1; t++) { int z = (q0 << ib) + t, z2 = z ^ m, dup = 0; for (int j = 0; j < nz; j++) if (Z[j] == z || Z[j] == z2) dup = 1; if (!dup) { Z[nz++] = z; Z[nz++] = z2; } }
    int closed = nz;
    for (int t = 0; nz < bs - 1; t++) { int z = (q0 << ib) + t, dup = 0; for (int j = 0; j < nz; j++) if (Z[j] == z) dup = 1; if (!dup) Z[nz++] = z; }
    // B: kernel vector of the (bs-1) x bs system
    static fe A[MAXK * MAXK], Kb[MAXK * MAXK]; int piv[MAXK]; fe b[MAXK];
    for (int j = 0; j < nz; j++) for (int e = 0; e < bs; e++) A[j * bs + e] = low_row(Z[j], e);
    gf_rref(A, nz, bs, piv); int dimB = gf_kernel_from_rref(A, bs, piv, Kb); for (int e = 0; e < bs; e++) b[e] = Kb[e];
    static fe Bv[MAXN], beta[MAXN], word[MAXN];
    for (int y = 0; y < n; y++) { fe s = 0; for (int e = 0; e < bs; e++) s ^= gf_mul(b[e], low_row(y, e)); Bv[y] = s; }
    for (int q = 0; q < N; q++) beta[q] = rnd();
    for (int y = 0; y < n; y++) word[y] = gf_mul(beta[y >> ib], Bv[y]);
    // partner maps and mixing coefficients
    static int pix[MAXN], pir[MAXN]; static fe mu[MAXN];
    for (int x = 0; x < n; x++) { pix[x] = x ^ m; pir[x] = x; mu[x] = rnd() | 1; }
    for (int x = n - 1; x > 0; x--) { int j = (int)rnd_below(x + 1), t = pir[x]; pir[x] = pir[j]; pir[j] = t; }
    // block pairs other than {q0, q1}
    int pairs[MAXN], np = 0; for (int q = 0; q < N; q++) { int q2 = q ^ blm; if (q < q2 && q != q0 && q != q1) pairs[np++] = q; }
    int need = kup / 2; long members = 0, sumx = 0, sumr = 0, sumplain = 0; int minx = n, maxr = 0;
    printf("(k,n)=(%d,%d) blocks N=%d of %d leaves, k_up=%d, m=%d (block shift %d), zeros of B: %d of which %d in pairs closed under the mask, dim ker=%d\n", k, n, N, bs, kup, m, blm, nz, closed, dimB);
    for (long mask = 0; mask < (1L << np); mask++) {
        if (__builtin_popcountl(mask) != need) continue;
        int S[MAXK], ns = 0; for (int j = 0; j < np; j++) if ((mask >> j) & 1) { S[ns++] = pairs[j]; S[ns++] = pairs[j] ^ blm; }
        // interpolate A_S: kup unknowns, kup equations, augmented
        static fe T[MAXK * (MAXK + 1)]; int pv[MAXK + 1];
        for (int j = 0; j < kup; j++) { for (int e = 0; e < kup; e++) T[j * (kup + 1) + e] = up_row(S[j], e); T[j * (kup + 1) + kup] = beta[S[j]]; }
        int rk = gf_rref(T, kup, kup + 1, pv); if (rk != kup || pv[kup] >= 0) { printf("singular interpolation\n"); return 1; }
        fe As[MAXK]; for (int e = 0; e < kup; e++) As[e] = T[pv[e] * (kup + 1) + kup];
        static fe c[MAXN]; int ap = 0, ax = 0, ar = 0;
        for (int y = 0; y < n; y++) { fe s = 0; for (int e = 0; e < kup; e++) s ^= gf_mul(As[e], up_row(y >> ib, e)); c[y] = gf_mul(s, Bv[y]); if (c[y] == word[y]) ap++; }
        for (int x = 0; x < n; x++) {
            if ((c[x] ^ gf_mul(mu[x], c[pix[x]])) == (word[x] ^ gf_mul(mu[x], word[pix[x]]))) ax++;
            if ((c[x] ^ gf_mul(mu[x], c[pir[x]])) == (word[x] ^ gf_mul(mu[x], word[pir[x]]))) ar++;
        }
        members++; sumplain += ap; sumx += ax; sumr += ar; if (ax < minx) minx = ax; if (ar > maxr) maxr = ar;
    }
    long L = members - 1;
    printf("  members: %ld; plain agreement (each): %.2f; V1 with xor partner: min %d, sum %ld against n + L k = %ld (GS(L) allows at most n + L k - 1); V1 with a random permutation: max %d, sum %ld\n",
           members, (double)sumplain / members, minx, sumx, (long)n + L * k, maxr, sumr);
    return 0;
}
