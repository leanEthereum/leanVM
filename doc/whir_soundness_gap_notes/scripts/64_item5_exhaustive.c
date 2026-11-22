// Note 64, item 5a: exhaustive check of the first moment for triples at q = 16, N = 4 (D = K), k = 4, cube window.
// Usage: ./64_item5_exhaustive seed nmu
// For each sampled mu: the histogram of u_2 + 2 u_3 (best word) over ALL unordered pairs {d1, d2} of distinct nonzero
// polynomials of degree < 4 (triples (0, d1, d2)), against the exact expectation of Step 1 of note 57:
// non-collinear pairs have per position P(2) = 1/q^2, P(1) = 3(q-1)/q^2 (every window has 5 > 3 points, so no
// window is deficient), collinear pairs (d1 = lam d2) have P(2) = 1/q, independently over the 16 positions.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static uint8_t MT[16][16];
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline uint64_t zmask(uint64_t v) { uint64_t t = v | (v >> 1) | (v >> 2) | (v >> 3); return ~t & 0x1111111111111111ULL; }
int main(int argc, char **argv) {
    rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[1]) * 0x9E3779B97F4A7C15ULL;
    int nmu = atoi(argv[2]), n = 16, k = 4, q = 16;
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) {   // GF(16) = F_2[x]/(x^4 + x + 1)
        int r = 0, aa = a;
        for (int i = 0; i < 4; i++) { if (b >> i & 1) r ^= aa; aa <<= 1; if (aa & 16) aa ^= 0x13; }
        MT[a][b] = r;
    }
    // exact expectation of the histogram over unordered pairs
    double pg[3] = {1 - 3.0 * (q - 1) / (q * q) - 1.0 / (q * q), 3.0 * (q - 1) / (q * q), 1.0 / (q * q)}, dg[40] = {1}, dc[40] = {1};
    for (int x = 0; x < n; x++) {
        double a[40] = {0}, b[40] = {0};
        for (int s = 0; s <= 2 * x; s++) {
            for (int j = 0; j < 3; j++) a[s + j] += dg[s] * pg[j];
            b[s] += dc[s] * (1 - 1.0 / q); b[s + 2] += dc[s] / q;
        }
        for (int s = 0; s < 40; s++) { dg[s] = a[s]; dc[s] = b[s]; }
    }
    double M = 65535.0, ncol = M * (q - 2) / 2, ngen = M * (M - 1) / 2 - ncol, expct[40];
    for (int s = 0; s < 40; s++) expct[s] = ngen * dg[s] + ncol * dc[s];
    static uint64_t cw[65536], zt[65536];
    double avg[40] = {0}; int viol[40] = {0};
    for (int it = 0; it < nmu; it++) {
        uint64_t basis[4] = {0, 0, 0, 0};
        for (int x = 0; x < n; x++) {
            int w[5] = {x, x ^ 1, x ^ 2, x ^ 4, x ^ 8};
            for (int c = 0; c < 5; c++) {
                int mu = rnd() >> 60, pw = 1;
                for (int j = 0; j < k; j++) { basis[j] ^= (uint64_t)MT[mu][pw] << (4 * x); pw = MT[pw][w[c]]; }
            }
        }
        for (int d = 0; d < 65536; d++) {
            uint64_t v = 0;
            for (int j = 0; j < 4; j++) { int c = d >> (4 * j) & 15; if (c) for (int x = 0; x < n; x++) v ^= (uint64_t)MT[c][basis[j] >> (4 * x) & 15] << (4 * x); }
            cw[d] = v; zt[d] = zmask(v);
        }
        uint64_t hist[40] = {0};
        for (int d1 = 1; d1 < 65536; d1++) {
            uint64_t s1 = cw[d1], z1 = zt[d1];
            for (int d2 = d1 + 1; d2 < 65536; d2++) {
                uint64_t z2 = zt[d2], z12 = zmask(s1 ^ cw[d2]);
                hist[__builtin_popcountll(z1 | z2 | z12) + __builtin_popcountll(z1 & z2)]++;
            }
        }
        int mx = 0; for (int s = 0; s < 40; s++) if (hist[s]) mx = s;
        printf("mu %d: max %d; counts from score 8:", it, mx);
        for (int s = 8; s <= mx; s++) printf(" %d:%llu", s, (unsigned long long)hist[s]);
        printf("\n");
        for (int s = 0; s < 40; s++) avg[s] += (double)hist[s] / nmu;
        for (int s = 0; s <= mx; s++) viol[s]++;
    }
    printf("score C | mean count over %d mu | exact expectation | fraction of mu with max >= C | first-moment bound E[N>=C]/45\n", nmu);
    for (int s = 6; s < 20; s++) {
        double tail = 0; for (int u = s; u < 40; u++) tail += expct[u];
        printf("%d | %.4g | %.4g | %.3f | %.4g\n", s, avg[s], expct[s], (double)viol[s] / nmu, fmin(1.0, tail / 45));
    }
    return 0;
}
