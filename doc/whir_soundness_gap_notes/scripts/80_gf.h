// Referee 80: GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), tree codes, linear algebra. Written from scratch.
#ifndef GF80_H
#define GF80_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t fe;

// reduction of a 128-bit carry-less product modulo x^64 + x^4 + x^3 + x + 1 (0x1b)
static inline fe fe_reduce(uint64_t hi, uint64_t lo) {
    uint64_t top = (hi >> 60) ^ (hi >> 61) ^ (hi >> 63); // overflow of hi * 0x1b beyond 64 bits
    uint64_t h = hi ^ top;
    return lo ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4);
}
static inline fe fe_mul_slow(fe a, fe b) { // Russian peasant with reduction at each step
    fe r = 0;
    while (b) {
        if (b & 1) r ^= a;
        b >>= 1;
        a = (a << 1) ^ ((a >> 63) ? 0x1bull : 0);
    }
    return r;
}
#if defined(__aarch64__)
#include <arm_neon.h>
static inline fe fe_mul(fe a, fe b) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    return fe_reduce((uint64_t)(p >> 64), (uint64_t)p);
}
#else
static inline fe fe_mul(fe a, fe b) { return fe_mul_slow(a, b); }
#endif
static inline fe fe_inv(fe a) { // a^(2^64 - 2) = prod_{i=1}^{63} a^(2^i)
    fe r = 1, s = a;
    for (int i = 1; i < 64; i++) { s = fe_mul(s, s); r = fe_mul(r, s); }
    return r;
}
// splitmix64
static uint64_t sm_state = 0x1234567887654321ull;
static inline uint64_t rnd64(void) {
    uint64_t z = (sm_state += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}
static inline void rnd_seed(uint64_t s) { sm_state = s * 0xD6E8FEB86659FD93ull + 0x2545F4914F6CDD1Dull; for (int i = 0; i < 8; i++) rnd64(); }
static inline uint64_t rnd_below(uint64_t m) { return rnd64() % m; }
static inline fe rnd_nz(void) { fe a; do a = rnd64(); while (!a); return a; }
static void fe_selftest(void) {
    for (int i = 0; i < 3000; i++) {
        fe a = rnd64(), b = rnd64(), c = rnd64();
        if (fe_mul(a, b) != fe_mul_slow(a, b)) { printf("gf: fast != slow\n"); exit(1); }
        if (fe_mul(fe_mul(a, b), c) != fe_mul(a, fe_mul(b, c))) { printf("gf: assoc\n"); exit(1); }
        if (fe_mul(a, b ^ c) != (fe_mul(a, b) ^ fe_mul(a, c))) { printf("gf: distr\n"); exit(1); }
        if (a && fe_mul(a, fe_inv(a)) != 1) { printf("gf: inv\n"); exit(1); }
    }
    if (fe_mul(2, 1ull << 63) != 0x1b) { printf("gf: modulus\n"); exit(1); }
}

// ---- linear algebra on row-major R x C matrices ----
// Gauss-Jordan in place; pivcol[r] = pivot column of row r (rows 0..rank-1 are the pivot rows); returns rank
static int fe_rref(fe *A, int R, int C, int *pivcol) {
    int rk = 0;
    for (int c = 0; c < C && rk < R; c++) {
        int p = -1;
        for (int i = rk; i < R; i++) if (A[(size_t)i * C + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = 0; j < C; j++) { fe t = A[(size_t)p * C + j]; A[(size_t)p * C + j] = A[(size_t)rk * C + j]; A[(size_t)rk * C + j] = t; }
        fe iv = fe_inv(A[(size_t)rk * C + c]);
        for (int j = c; j < C; j++) A[(size_t)rk * C + j] = fe_mul(A[(size_t)rk * C + j], iv);
        for (int i = 0; i < R; i++) {
            if (i == rk) continue;
            fe f = A[(size_t)i * C + c];
            if (!f) continue;
            for (int j = c; j < C; j++) A[(size_t)i * C + j] ^= fe_mul(f, A[(size_t)rk * C + j]);
        }
        if (pivcol) pivcol[rk] = c;
        rk++;
    }
    return rk;
}
static int fe_rank(const fe *A, int R, int C) {
    fe *B = malloc((size_t)R * C * sizeof(fe) + 8);
    memcpy(B, A, (size_t)R * C * sizeof(fe));
    int rk = fe_rref(B, R, C, NULL);
    free(B);
    return rk;
}
// kernel {v : A v = 0}: returns dim, writes a basis (dim x C) into Kb (caller allocates C x C)
static int fe_kernel(const fe *A, int R, int C, fe *Kb) {
    fe *B = malloc((size_t)(R + 1) * C * sizeof(fe));
    int *pc = malloc(sizeof(int) * (R + 1));
    char *isp = calloc(C, 1);
    memcpy(B, A, (size_t)R * C * sizeof(fe));
    int rk = fe_rref(B, R, C, pc);
    for (int r = 0; r < rk; r++) isp[pc[r]] = 1;
    int d = 0;
    for (int c = 0; c < C; c++) {
        if (isp[c]) continue;
        fe *v = Kb + (size_t)d * C;
        memset(v, 0, C * sizeof(fe));
        v[c] = 1;
        for (int r = 0; r < rk; r++) v[pc[r]] = B[(size_t)r * C + c]; // characteristic 2
        d++;
    }
    free(B); free(pc); free(isp);
    return d;
}

// ---- tree codes ----
// n = ntrees * 2^v leaves; tw[i][j >> i] is the twiddle of leaf j at layer i (layer 0 = bottom, private to the leaf in T2).
// g_j[e] = prod_{i : bit i of e set} tw[i][j >> i].  variant 2: all twiddles independent; variant 1: sibling = twiddle + 1.
typedef struct { int v, k, n, ntrees, variant; fe *tw[32]; fe *G; } tree_t;
static void tree_rows(tree_t *T) {
    for (int j = 0; j < T->n; j++) {
        fe *g = T->G + (size_t)j * T->k;
        g[0] = 1;
        for (int i = 0; i < T->v; i++) {
            fe t = T->tw[i][j >> i];
            for (int e = 0; e < (1 << i); e++) g[e | (1 << i)] = fe_mul(g[e], t);
        }
    }
}
static void tree_init(tree_t *T, int v, int ntrees, int variant) {
    T->v = v; T->k = 1 << v; T->ntrees = ntrees; T->n = ntrees << v; T->variant = variant;
    for (int i = 0; i < v; i++) {
        int cnt = T->n >> i;
        T->tw[i] = malloc(sizeof(fe) * cnt);
        for (int p = 0; p < cnt; p += 2) {
            fe a = rnd64(), b;
            if (variant == 1) b = a ^ 1; else do b = rnd64(); while (b == a);
            T->tw[i][p] = a; T->tw[i][p + 1] = b;
        }
    }
    T->G = malloc(sizeof(fe) * (size_t)T->n * T->k);
    tree_rows(T);
}
static void tree_free(tree_t *T) { for (int i = 0; i < T->v; i++) free(T->tw[i]); free(T->G); }
// codeword of message m (length k): c[j] = g_j . m
static void tree_encode(const tree_t *T, const fe *m, fe *c) {
    for (int j = 0; j < T->n; j++) {
        fe s = 0; const fe *g = T->G + (size_t)j * T->k;
        for (int e = 0; e < T->k; e++) s ^= fe_mul(g[e], m[e]);
        c[j] = s;
    }
}

// ---- patterns: a class is a bitmask of members 0..L (member 0 is the reference, e_0 = 0) ----
static inline int popc(unsigned x) { return __builtin_popcount(x); }
// dim of span(e_l - e_l' : l, l' in C) = (|C| - 1)_+
static inline int cls_dim(unsigned C) { int c = popc(C); return c > 0 ? c - 1 : 0; }
// dim(Lambda_C + Lambda_D) for two cliques
static inline int cls_sum_dim(unsigned C, unsigned D) {
    if (popc(C) < 2) return cls_dim(D);
    if (popc(D) < 2) return cls_dim(C);
    return (C & D) ? popc(C | D) - 1 : popc(C) + popc(D) - 2;
}
// write the rows Lambda_C (x) vec (vec of length k) into out (rows of length L*k); returns the number of rows.
// functional e_l - e_l0 with l0 the lowest member of C; coordinate of member l >= 1 is l - 1 (e_0 = 0).
static int cls_rows(unsigned C, int L, const fe *vec, int k, fe *out) {
    if (popc(C) < 2) return 0;
    int l0 = __builtin_ctz(C), r = 0;
    for (int l = l0 + 1; l <= L; l++) {
        if (!((C >> l) & 1)) continue;
        fe *row = out + (size_t)r * L * k;
        memset(row, 0, sizeof(fe) * (size_t)L * k);
        memcpy(row + (size_t)(l - 1) * k, vec, sizeof(fe) * k);
        if (l0 >= 1) memcpy(row + (size_t)(l0 - 1) * k, vec, sizeof(fe) * k);
        r++;
    }
    return r;
}
// plain incidence matrix of a pattern cls[0..n-1]; returns the number of rows w; M has room for sum cls_dim rows
static int pat_matrix(const tree_t *T, const unsigned *cls, int L, fe *M) {
    int w = 0;
    for (int j = 0; j < T->n; j++) w += cls_rows(cls[j], L, T->G + (size_t)j * T->k, T->k, M + (size_t)w * L * T->k);
    return w;
}
static int pat_weight(const unsigned *cls, int n) { int w = 0; for (int j = 0; j < n; j++) w += cls_dim(cls[j]); return w; }
#endif
