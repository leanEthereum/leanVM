// Exhaustive list of the flat word y(a) = a^(n/2-1) at rate 1/4, for 35-large-characteristic-transfer.md.
// Field GF(2^8) = F2[x]/(x^8+x^4+x^3+x^2+1), domain D = F2-span of 1, x, ..., x^(N-1), n = 2^N, k = n/4.
// Enumerates every k-subset of D, interpolates, and prints each polynomial of degree < k with at least
// AMIN agreements once (when the subset is the first k agreement positions), as: agreement, coefficients.
// Build: cc -O2 -o 35_flat_list 35_flat_list.c ; run: ./35_flat_list N AMIN   (N = 4 or 5; N = 5 takes about 20 s)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint8_t EXP[512], LOG[256];
static inline uint8_t mul(uint8_t a, uint8_t b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static inline uint8_t inv(uint8_t a) { return EXP[255 - LOG[a]]; }
int main(int argc, char **argv) {
    int N = argc > 1 ? atoi(argv[1]) : 4, amin = argc > 2 ? atoi(argv[2]) : 7;
    int n = 1 << N, k = n / 4;
    int v = 1;
    for (int i = 0; i < 255; i++) { EXP[i] = v; LOG[v] = i; v <<= 1; if (v >> 8) v ^= 0x11D; }
    for (int i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
    uint8_t D[64], y[64];
    for (int i = 0; i < n; i++) { uint8_t e = 0; for (int b = 0; b < N; b++) if (i >> b & 1) e ^= EXP[b]; D[i] = e; }
    for (int i = 0; i < n; i++) { uint8_t p = 1; for (int j = 0; j < n / 2 - 1; j++) p = mul(p, D[i]); y[i] = D[i] ? p : 0; }
    int idx[16];
    for (int i = 0; i < k; i++) idx[i] = i;
    long found = 0, hist[65] = {0};
    for (;;) {
        // Newton interpolation on the subset
        uint8_t c[16], xs[16];
        for (int i = 0; i < k; i++) { xs[i] = D[idx[i]]; c[i] = y[idx[i]]; }
        for (int j = 1; j < k; j++)
            for (int i = k - 1; i >= j; i--) c[i] = mul(c[i] ^ c[i - 1], inv(xs[i] ^ xs[i - j]));
        // agreement count; require the subset to be the first k agreement positions
        int agree = 0, ok = 1, pos = 0;
        for (int t = 0; t < n && ok; t++) {
            uint8_t r = c[k - 1];
            for (int i = k - 2; i >= 0; i--) r = mul(r, D[t] ^ xs[i]) ^ c[i];
            if (r == y[t]) {
                if (pos < k) { if (idx[pos] != t) ok = 0; pos++; }
                agree++;
            }
        }
        if (ok && agree >= amin) {
            // expand Newton form to monomial coefficients
            uint8_t p[16] = {0};
            p[0] = c[k - 1];
            int deg = 0;
            for (int i = k - 2; i >= 0; i--) {
                for (int d = deg + 1; d >= 1; d--) p[d] = p[d - 1] ^ mul(p[d], xs[i]);
                p[0] = mul(p[0], xs[i]) ^ c[i];
                deg++;
            }
            printf("%d", agree);
            for (int d = 0; d < k; d++) printf(" %d", p[d]);
            printf("\n");
            found++; hist[agree]++;
        }
        int i = k - 1;
        while (i >= 0 && idx[i] == n - k + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < k; j++) idx[j] = idx[j - 1] + 1;
    }
    fprintf(stderr, "N=%d n=%d k=%d: %ld polynomials with agreement >= %d;", N, n, k, found, amin);
    for (int a = amin; a <= n; a++) if (hist[a]) fprintf(stderr, " [%d: %ld]", a, hist[a]);
    fprintf(stderr, "\n");
    return 0;
}
