/* 53_codes.c: the binary code Gamma_inf(g) = {T subset D : p_k(T) = sum_{alpha in T} alpha^k = 0 for 0 <= k <= g}
 * on an F_2-subspace D of GF(2^m), exact F_2-linear algebra (Section 5 of 53-goppa-structure-degenerate.md).
 *
 *   ./53_codes inf N m kind seed [dumpfile dump_g]
 *       kind = span (D = span(1, x, .., x^(N-1)), x the class of X) or rand (random basis from seed).
 *       Prints dim Gamma_inf(g) after every odd k where it changes (the conditions with even k follow from the
 *       odd ones, p_2k = p_k^2), up to g = n/2. With dumpfile: writes a basis of Gamma_inf(dump_g), one hex
 *       line per vector (bit i = the point with coordinates i in the basis).
 *   ./53_codes bch N g
 *       dimension of the same code on D = GF(2^N): 1 + #{j in [1, 2^N - 2] : every cyclic rotation of the N-bit
 *       string of j exceeds g} (the BCH code with zeros alpha^1 .. alpha^g, extended by the point 0 and parity).
 *
 * cc -O2 -o 53_codes 53_codes.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static int M;
static u64 RED, MASK;

/* low parts of irreducible polynomials x^m + low */
static u64 low_of(int m) {
    switch (m) {
    case 8: return 0x1B; case 9: return 0x11; case 10: return 0x9; case 11: return 0x5; case 12: return 0x53;
    case 13: return 0x1B; case 14: return 0x443; case 15: return 0x3; case 16: return 0x2D; case 18: return 0x9;
    case 20: return 0x9; case 22: return 0x3; case 24: return 0x1B; case 28: return 0x9; case 32: return 0x8D;
    case 40: return 0x39; case 48: return 0x2D; case 56: return 0x95; case 64: return 0x1B;
    }
    fprintf(stderr, "no modulus for m = %d\n", m);
    exit(1);
}

static inline u64 xtime(u64 a) {
    u64 hi = (a >> (M - 1)) & 1;
    a = (a << 1) & MASK;
    return hi ? a ^ RED : a;
}

static u64 gmul(u64 a, u64 b) {
    u64 r = 0;
    while (b) {
        if (b & 1) r ^= a;
        b >>= 1;
        a = xtime(a);
    }
    return r;
}

/* Rabin irreducibility test of x^M + RED: X^(2^M) = X and gcd(X^(2^(M/p)) - X, f) = 1 for the primes p | M.
 * Field arithmetic modulo f is well defined as a ring even if f is reducible. */
static int deg128(u128 a) { int d = -1; while (a) { d++; a >>= 1; } return d; }
static u128 gcd128(u128 a, u128 b) {
    while (b) {
        int da = deg128(a), db = deg128(b);
        if (da < db) { u128 t = a; a = b; b = t; continue; }
        a ^= b << (da - db);
        if (!a) { a = b; b = 0; }
    }
    return a;
}
static int irreducible(void) {
    u128 f = ((u128)1 << M) | RED;
    u64 x = 2, y = x;
    for (int i = 0; i < M; i++) y = gmul(y, y);
    if (y != x) return 0;
    for (int p = 2; p <= M; p++) {
        if (M % p) continue;
        int prime = 1;
        for (int q = 2; q * q <= p; q++) if (p % q == 0) prime = 0;
        if (!prime) continue;
        y = x;
        for (int i = 0; i < M / p; i++) y = gmul(y, y);
        if (gcd128(f, (u128)(y ^ x)) != 1) return 0;
    }
    return 1;
}

static u64 rng_state;
static u64 rnd64(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
    return rng_state;
}

static int run_inf(int N, int m, const char *kind, u64 seed, const char *dump, int dump_g) {
    M = m; RED = low_of(m); MASK = m == 64 ? ~(u64)0 : (((u64)1 << m) - 1);
    if (!irreducible()) { fprintf(stderr, "modulus for m = %d is reducible\n", m); return 1; }
    int n = 1 << N, W = (n + 63) / 64;
    u64 basis[32];
    if (!strcmp(kind, "span")) {
        if (N > m) { fprintf(stderr, "N > m\n"); return 1; }
        for (int i = 0; i < N; i++) basis[i] = (u64)1 << i;
    } else {
        rng_state = seed * 0x9E3779B97F4A7C15ULL + 12345;
        for (;;) {
            for (int i = 0; i < N; i++) basis[i] = rnd64() & MASK;
            /* independence over F_2 */
            u64 ech[64]; int r = 0;
            memset(ech, 0, sizeof ech);
            for (int i = 0; i < N; i++) {
                u64 v = basis[i];
                for (int b = 63; b >= 0 && v; b--) if ((v >> b) & 1) { if (ech[b]) v ^= ech[b]; else { ech[b] = v; r++; v = 0; } }
            }
            if (r == N) break;
        }
    }
    u64 *pt = malloc(sizeof(u64) * n), *pw = malloc(sizeof(u64) * n), *sq = malloc(sizeof(u64) * n);
    for (int a = 0; a < n; a++) {
        u64 v = 0;
        for (int i = 0; i < N; i++) if ((a >> i) & 1) v ^= basis[i];
        pt[a] = v; pw[a] = v; sq[a] = gmul(v, v);
    }
    /* kernel basis: d vectors of W words */
    u64 *vec = calloc((size_t)n * W, sizeof(u64));
    int *alive = malloc(sizeof(int) * n);
    int d = n;
    for (int i = 0; i < n; i++) { vec[(size_t)i * W + i / 64] = (u64)1 << (i % 64); alive[i] = i; }
    u64 *syn = malloc(sizeof(u64) * n);
    printf("# inf N=%d n=%d m=%d kind=%s seed=%llu: (g, dim Gamma_inf(g)) at every change\n", N, n, m, kind,
           (unsigned long long)seed);
    int kmax = n / 2;
    int lastdim = -1;
    for (int k = 0; k <= kmax; k = (k == 0 ? 1 : k + 2)) {
        /* syndromes of the current basis vectors for the functional alpha -> alpha^k */
        for (int t = 0; t < d; t++) {
            u64 *v = vec + (size_t)alive[t] * W, s = 0;
            if (k == 0) { for (int w = 0; w < W; w++) s ^= (u64)__builtin_popcountll(v[w]); s &= 1; }
            else for (int w = 0; w < W; w++) { u64 x = v[w]; while (x) { int b = __builtin_ctzll(x); s ^= pw[w * 64 + b]; x &= x - 1; } }
            syn[t] = s;
        }
        int piv[64]; u64 pivs[64];
        for (int b = 0; b < 64; b++) piv[b] = -1;
        int nd = 0;
        for (int t = 0; t < d; t++) {
            u64 s = syn[t];
            u64 *v = vec + (size_t)alive[t] * W;
            while (s) {
                int b = 63 - __builtin_clzll(s);
                if (piv[b] < 0) { piv[b] = alive[t]; pivs[b] = s; break; }
                s ^= pivs[b];
                u64 *p = vec + (size_t)piv[b] * W;
                for (int w = 0; w < W; w++) v[w] ^= p[w];
            }
            if (!s) alive[nd++] = alive[t];
        }
        d = nd;
        if (d != lastdim) { printf("%d %d\n", k, d); lastdim = d; }
        if (dump && k <= dump_g && (k == 0 ? 1 : k + 2) > dump_g) {
            FILE *f = fopen(dump, "w");
            for (int t = 0; t < d; t++) {
                u64 *v = vec + (size_t)alive[t] * W;
                for (int w = W - 1; w >= 0; w--) fprintf(f, "%016llx", (unsigned long long)v[w]);
                fprintf(f, "\n");
            }
            fclose(f);
            printf("# dumped %d vectors of Gamma_inf(%d) to %s\n", d, dump_g, dump);
        }
        if (k >= 1) for (int a = 0; a < n; a++) pw[a] = gmul(pw[a], sq[a]);
        if (d == 0) break;
    }
    printf("# end\n");
    return 0;
}

static int run_bch(int N, long g) {
    long n = 1L << N, cnt = 1;
    u64 mask = (u64)n - 1;
    for (u64 j = 1; j + 1 < (u64)n; j++) {
        u64 r = j; int ok = 1;
        for (int i = 0; i < N; i++) {
            if ((long)r <= g) { ok = 0; break; }
            r = ((r << 1) | (r >> (N - 1))) & mask;
        }
        cnt += ok;
    }
    printf("bch N=%d g=%ld (g/n = %.4f): dim = %ld\n", N, g, (double)g / n, cnt);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 6 && !strcmp(argv[1], "inf"))
        return run_inf(atoi(argv[2]), atoi(argv[3]), argv[4], strtoull(argv[5], 0, 10), argc >= 8 ? argv[6] : 0,
                       argc >= 8 ? atoi(argv[7]) : 0);
    if (argc >= 4 && !strcmp(argv[1], "bch")) return run_bch(atoi(argv[2]), atol(argv[3]));
    fprintf(stderr, "usage: 53_codes inf N m span|rand seed [dumpfile dump_g] | 53_codes bch N g\n");
    return 1;
}
