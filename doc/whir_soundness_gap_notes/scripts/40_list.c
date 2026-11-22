/* 40_list.c: the list of a word by information-set decoding, GF(2^16), for 40-rate-half-residual.md.
 *
 * Reads the points "pt alpha y" of a dump file written by 40_scale, draws random k-subsets of the n
 * positions, interpolates the polynomial of degree < k through them and counts its agreements with the
 * word. A list member with agreement t is found by one trial with probability C(t, k) / C(n, k); the
 * program reports the number of trials so that the miss probability can be bounded.
 *
 * Build: cc -O2 -o 40_list 40_list.c
 * Run:   ./40_list dumpfile T trials [outfile]     prints every polynomial found with agreement >= T
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define Q 65536
static uint16_t EXPT[2 * Q], LOGT[Q];
static void gf_init(void) {
    uint32_t v = 1;
    for (int i = 0; i < Q - 1; i++) { EXPT[i] = (uint16_t)v; LOGT[v] = (uint16_t)i; v <<= 1; if (v & Q) v ^= 0x1002D; }
    for (int i = Q - 1; i < 2 * Q; i++) EXPT[i] = EXPT[i - (Q - 1)];
}
static inline uint16_t mul(uint16_t a, uint16_t b) { return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0; }
static inline uint16_t inv(uint16_t a) { return EXPT[Q - 1 - LOGT[a]]; }
static uint64_t rs = 0x2545F4914F6CDD1DULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 20); }

#define MAXN 256
#define MAXL 4096
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s dumpfile T trials [outfile]\n", argv[0]); return 1; }
    gf_init();
    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 1; }
    char line[256];
    int n = 0;
    uint16_t al[MAXN], y[MAXN];
    while (fgets(line, sizeof line, f)) {
        int a, b;
        if (sscanf(line, "pt %d %d", &a, &b) == 2) { al[n] = (uint16_t)a; y[n] = (uint16_t)b; n++; }
    }
    fclose(f);
    int k = n / 2, T = atoi(argv[2]);
    long trials = atol(argv[3]);
    static uint16_t found[MAXL][MAXN];
    static int agr[MAXL];
    int nf = 0;
    int idx[MAXN];
    for (long t = 0; t < trials; t++) {
        for (int i = 0; i < n; i++) idx[i] = i;
        for (int i = 0; i < k; i++) { int j = i + rnd() % (n - i); int tmp = idx[i]; idx[i] = idx[j]; idx[j] = tmp; }
        /* Lagrange: evaluate the interpolant at the other n - k points via barycentric weights */
        uint16_t w[MAXN];
        for (int i = 0; i < k; i++) {
            uint16_t d = 1;
            for (int j = 0; j < k; j++) if (j != i) d = mul(d, al[idx[i]] ^ al[idx[j]]);
            w[i] = mul(y[idx[i]], inv(d));
        }
        int agree = k;
        for (int p = k; p < n && agree + (n - p) >= T; p++) {
            uint16_t x = al[idx[p]], full = 1, s = 0;
            for (int j = 0; j < k; j++) full = mul(full, x ^ al[idx[j]]);
            for (int i = 0; i < k; i++) s ^= mul(w[i], inv(x ^ al[idx[i]]));
            if (mul(s, full) == y[idx[p]]) agree++;
        }
        if (agree < T) continue;
        /* coefficients of the interpolant: sum_i w_i prod_{j != i} (X - a_j) */
        uint16_t full[MAXN + 1] = {1}, c[MAXN] = {0};
        for (int j = 0; j < k; j++) {
            uint16_t a = al[idx[j]];
            for (int d = j + 1; d >= 1; d--) full[d] = full[d - 1] ^ mul(a, full[d]);
            full[0] = mul(a, full[0]);
        }
        for (int i = 0; i < k; i++) {
            uint16_t a = al[idx[i]], carry = 0, q[MAXN];
            for (int d = k; d >= 1; d--) { carry = full[d] ^ mul(carry, a); q[d - 1] = carry; }
            for (int d = 0; d < k; d++) c[d] ^= mul(w[i], q[d]);
        }
        int dup = 0;
        for (int u = 0; u < nf && !dup; u++) dup = !memcmp(found[u], c, sizeof(uint16_t) * k);
        if (!dup && nf < MAXL) { memcpy(found[nf], c, sizeof(uint16_t) * k); agr[nf] = agree; nf++; }
    }
    int hist[MAXN + 1] = {0};
    for (int u = 0; u < nf; u++) {
        /* recount the agreement exactly */
        int a = 0;
        for (int p = 0; p < n; p++) { uint16_t v = 0; for (int d = k - 1; d >= 0; d--) v = mul(v, al[p]) ^ found[u][d]; a += (v == y[p]); }
        agr[u] = a; hist[a]++;
    }
    printf("n = %d, k = %d, %ld trials, %d polynomials with agreement >= %d:", n, k, trials, nf, T);
    for (int a = T; a <= n; a++) if (hist[a]) printf(" %d at agreement %d;", hist[a], a);
    printf("\n");
    if (argc > 4) {
        FILE *o = fopen(argv[4], "w");
        for (int u = 0; u < nf; u++) { fprintf(o, "poly %d", agr[u]); for (int d = 0; d < k; d++) fprintf(o, " %d", found[u][d]); fprintf(o, "\n"); }
        fclose(o);
    }
    return 0;
}
