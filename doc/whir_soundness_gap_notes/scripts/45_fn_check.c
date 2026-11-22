/* 45_fn_check.c: exhaustive test of Theorem 7 of 45-rate-half-second-attempt.md at n = 64.
 *
 * D = GF(64), word y = X^e with e = 3n/4 - j (j even). Theorem 7: for every degree bound d < e, no polynomial of
 * degree <= d agrees with y on more than W/4 points, W = max(4j + 5d, 2n + 1 + d, 2n + e).
 * The program lists, for given e and d, every polynomial of degree <= d with at least T0 agreements, by
 * interpolation through all (d+1)-subsets of the first n - T0 + d + 1 points (a polynomial with >= T0 agreements
 * agrees on at least d + 1 of them), and prints the histogram of agreements.
 *
 * Build: cc -O2 -o 45_fn_check 45_fn_check.c      Run: ./45_fn_check e d T0      (e.g. 46 5 40)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 64
static unsigned char EXPT[2 * Q], LOGT[Q];
static void gf_init(void) {
    int v = 1;
    for (int i = 0; i < Q - 1; i++) { EXPT[i] = (unsigned char)v; LOGT[v] = (unsigned char)i; v <<= 1; if (v & Q) v ^= 0x43; }
    for (int i = Q - 1; i < 2 * Q; i++) EXPT[i] = EXPT[i - (Q - 1)];
}
static inline int mul(int a, int b) { return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0; }
static inline int inv(int a) { return EXPT[Q - 1 - LOGT[a]]; }
static int fpow(int a, int e) { if (!e) return 1; if (!a) return 0; return EXPT[(LOGT[a] * e) % (Q - 1)]; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s e d T0\n", argv[0]); return 1; }
    int e = atoi(argv[1]), d = atoi(argv[2]), T0 = atoi(argv[3]), n = Q;
    gf_init();
    int y[Q], m = n - T0 + d + 1, k = d + 1;
    for (int x = 0; x < n; x++) y[x] = fpow(x, e);
    long hist[Q + 1]; memset(hist, 0, sizeof hist);
    int idx[16];
    for (int i = 0; i < k; i++) idx[i] = i;
    long subsets = 0;
    /* seen: avoid counting a polynomial once per subset: count it only when the subset is its first k agreements */
    for (;;) {
        subsets++;
        /* Newton interpolation through (idx[i], y[idx[i]]) */
        int c[16], xs[16];
        for (int i = 0; i < k; i++) { xs[i] = idx[i]; c[i] = y[idx[i]]; }
        for (int lev = 1; lev < k; lev++)
            for (int i = k - 1; i >= lev; i--) c[i] = mul(c[i] ^ c[i - 1], inv(xs[i] ^ xs[i - lev]));
        int agree = 0, first = 1, pos = 0;
        for (int x = 0; x < n; x++) {
            int v = c[k - 1];
            for (int i = k - 2; i >= 0; i--) v = mul(v, x ^ xs[i]) ^ c[i];
            if (v == y[x]) {
                agree++;
                if (pos < k) { if (x != idx[pos]) { first = 0; break; } pos++; }
            }
        }
        if (first && agree >= T0) hist[agree]++;
        int i = k - 1;
        while (i >= 0 && idx[i] == m - k + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int t = i + 1; t < k; t++) idx[t] = idx[t - 1] + 1;
    }
    int j = 3 * n / 4 - e;
    int W = 4 * j + 5 * d;
    if (2 * n + 1 + d > W) W = 2 * n + 1 + d;
    if (2 * n + e > W) W = 2 * n + e;
    printf("n = 64, D = GF(64), word X^%d (j = %d), degree <= %d: %ld subsets; W = %d, Theorem 7: no agreement above %d;", e, j, d, subsets, W, W / 4);
    int mx = -1;
    for (int a = T0; a <= n; a++) if (hist[a]) { printf(" [%d agreements: %ld polynomials]", a, hist[a]); mx = a; }
    if (mx < 0) printf(" no polynomial with >= %d agreements", T0);
    printf("  %s\n", (mx <= W / 4) ? "consistent" : "VIOLATION");
    return 0;
}
