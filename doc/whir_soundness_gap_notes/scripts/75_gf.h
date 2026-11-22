// Referee 75: GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), written from scratch (shares nothing with 69_*.h / 74_*).
#ifndef GF75_H
#define GF75_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t fe;
static inline fe gf_red(uint64_t hi, uint64_t lo) {
    uint64_t t = hi ^ (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    return lo ^ t ^ (t << 1) ^ (t << 3) ^ (t << 4);
}
static inline fe gf_mul_portable(fe a, fe b) {
    uint64_t hi = 0, lo = 0;
    for (int i = 0; i < 64; i++) if ((b >> i) & 1) { lo ^= a << i; if (i) hi ^= a >> (64 - i); }
    return gf_red(hi, lo);
}
#if defined(__aarch64__)
#include <arm_neon.h>
static inline fe gf_mul(fe a, fe b) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    return gf_red((uint64_t)(p >> 64), (uint64_t)p);
}
#else
static inline fe gf_mul(fe a, fe b) { return gf_mul_portable(a, b); }
#endif
static inline fe gf_inv(fe a) { // a^(2^64 - 2)
    fe r = 1, s = gf_mul(a, a);
    for (int i = 1; i < 64; i++) { r = gf_mul(r, s); s = gf_mul(s, s); }
    return r;
}
static uint64_t rng_s[2] = {0x9E3779B97F4A7C15ull, 0xD1B54A32D192ED03ull};
static inline uint64_t rnd(void) { // xorshift128+
    uint64_t a = rng_s[0], b = rng_s[1]; rng_s[0] = b; a ^= a << 23; a ^= a >> 17; a ^= b ^ (b >> 26); rng_s[1] = a; return a + b;
}
static void rng_seed(uint64_t s) { rng_s[0] = s * 0x9E3779B97F4A7C15ull + 1; rng_s[1] = (s ^ 0xDEADBEEFCAFEF00Dull) * 0xBF58476D1CE4E5B9ull + 7; for (int i = 0; i < 20; i++) rnd(); }
static inline uint64_t rnd_below(uint64_t m) { return rnd() % m; }
static void gf_selftest(void) {
    for (int i = 0; i < 2000; i++) {
        fe a = rnd(), b = rnd(), c = rnd();
        if (gf_mul(a, b) != gf_mul_portable(a, b)) { printf("gf: pmull != portable\n"); exit(1); }
        if (gf_mul(gf_mul(a, b), c) != gf_mul(a, gf_mul(b, c))) { printf("gf: not associative\n"); exit(1); }
        if (gf_mul(a, b ^ c) != (gf_mul(a, b) ^ gf_mul(a, c))) { printf("gf: not distributive\n"); exit(1); }
        if (a && gf_mul(a, gf_inv(a)) != 1) { printf("gf: inverse wrong\n"); exit(1); }
    }
    // x * x^63 = x^64 = x^4 + x^3 + x + 1
    if (gf_mul(2, 1ull << 63) != 0x1b) { printf("gf: modulus wrong\n"); exit(1); }
}
// rank of an R x C matrix (destroyed), fraction-free
static int gf_rank(fe *A, int R, int C) {
    int rk = 0;
    for (int c = 0; c < C && rk < R; c++) {
        int p = -1; for (int i = rk; i < R; i++) if (A[(size_t)i * C + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = 0; j < C; j++) { fe t = A[(size_t)p * C + j]; A[(size_t)p * C + j] = A[(size_t)rk * C + j]; A[(size_t)rk * C + j] = t; }
        fe pv = A[(size_t)rk * C + c];
        for (int i = rk + 1; i < R; i++) { fe f = A[(size_t)i * C + c]; if (!f) continue;
            for (int j = c; j < C; j++) A[(size_t)i * C + j] = gf_mul(A[(size_t)i * C + j], pv) ^ gf_mul(f, A[(size_t)rk * C + j]); }
        rk++;
    }
    return rk;
}
// reduced row echelon form in place; piv[c] = row of the pivot in column c or -1; returns the rank
static int gf_rref(fe *A, int R, int C, int *piv) {
    int rk = 0;
    for (int c = 0; c < C; c++) piv[c] = -1;
    for (int c = 0; c < C && rk < R; c++) {
        int p = -1; for (int i = rk; i < R; i++) if (A[(size_t)i * C + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = 0; j < C; j++) { fe t = A[(size_t)p * C + j]; A[(size_t)p * C + j] = A[(size_t)rk * C + j]; A[(size_t)rk * C + j] = t; }
        fe iv = gf_inv(A[(size_t)rk * C + c]);
        for (int j = c; j < C; j++) A[(size_t)rk * C + j] = gf_mul(A[(size_t)rk * C + j], iv);
        for (int i = 0; i < R; i++) { if (i == rk) continue; fe f = A[(size_t)i * C + c]; if (!f) continue;
            for (int j = c; j < C; j++) A[(size_t)i * C + j] ^= gf_mul(f, A[(size_t)rk * C + j]); }
        piv[c] = rk++;
    }
    return rk;
}
// kernel basis (dim x C) of a matrix given in RREF with pivots piv; returns dim
static int gf_kernel_from_rref(const fe *A, int C, const int *piv, fe *Kb) {
    int d = 0;
    for (int f = 0; f < C; f++) { if (piv[f] >= 0) continue;
        fe *w = Kb + (size_t)d * C; memset(w, 0, sizeof(fe) * C); w[f] = 1;
        for (int c = 0; c < C; c++) if (piv[c] >= 0) w[c] = A[(size_t)piv[c] * C + f];
        d++; }
    return d;
}
#endif
