// Field arithmetic for the tree-code experiments. Compile with -DFB=8, 16 or 64.
// FB=8: GF(2)[x]/(x^8+x^4+x^3+x^2+1). FB=16: GF(2)[x]/(x^16+x^12+x^3+x+1).
// FB=64: GF(2)[x]/(x^64+x^4+x^3+x+1), carry-less multiplication (PMULL on arm64, portable otherwise).
#ifndef GF69_H
#define GF69_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifndef FB
#define FB 64
#endif
typedef uint64_t fe;

static uint64_t rng_s[4] = {0x9E3779B97F4A7C15ull, 0xBF58476D1CE4E5B9ull, 0x94D049BB133111EBull, 0x2545F4914F6CDD1Dull};
static inline uint64_t rotl64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t rng_u64(void) {
    uint64_t r = rotl64(rng_s[1] * 5, 7) * 9, t = rng_s[1] << 17;
    rng_s[2] ^= rng_s[0]; rng_s[3] ^= rng_s[1]; rng_s[1] ^= rng_s[2]; rng_s[0] ^= rng_s[3];
    rng_s[2] ^= t; rng_s[3] = rotl64(rng_s[3], 45);
    return r;
}
static void rng_seed(uint64_t s) {
    for (int i = 0; i < 4; i++) { s += 0x9E3779B97F4A7C15ull; uint64_t z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; rng_s[i] = z ^ (z >> 31); }
}
static inline uint64_t rng_below(uint64_t m) { return rng_u64() % m; }

#if FB == 64
#define FQ_IS_BIG 1
#if defined(__aarch64__)
#include <arm_neon.h>
static inline void clmul64(uint64_t a, uint64_t b, uint64_t *hi, uint64_t *lo) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    *lo = (uint64_t)p; *hi = (uint64_t)(p >> 64);
}
#else
static inline void clmul64(uint64_t a, uint64_t b, uint64_t *hi, uint64_t *lo) {
    uint64_t h = 0, l = 0;
    for (int i = 0; i < 64; i++) if ((b >> i) & 1) { l ^= a << i; if (i) h ^= a >> (64 - i); }
    *hi = h; *lo = l;
}
#endif
static inline fe gf_mul(fe a, fe b) {
    uint64_t hi, lo, h2, l2;
    clmul64(a, b, &hi, &lo);
    clmul64(hi, 0x1Bull, &h2, &l2);
    lo ^= l2;
    lo ^= h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4);
    return lo;
}
static inline fe gf_sqn(fe a, int t) { while (t--) a = gf_mul(a, a); return a; }
static inline fe gf_inv(fe a) { // a^(2^64-2) = (a^(2^63-1))^2, chain 1,2,3,6,7,14,15,30,31,62,63
    fe b2 = gf_mul(gf_sqn(a, 1), a), b3 = gf_mul(gf_sqn(b2, 1), a), b6 = gf_mul(gf_sqn(b3, 3), b3);
    fe b7 = gf_mul(gf_sqn(b6, 1), a), b14 = gf_mul(gf_sqn(b7, 7), b7), b15 = gf_mul(gf_sqn(b14, 1), a);
    fe b30 = gf_mul(gf_sqn(b15, 15), b15), b31 = gf_mul(gf_sqn(b30, 1), a), b62 = gf_mul(gf_sqn(b31, 31), b31);
    return gf_sqn(gf_mul(gf_sqn(b62, 1), a), 1);
}
static inline fe gf_rand(void) { return rng_u64(); }
static void gf_init(void) {}
#define GF_Q_LOG 64
#else
#if FB == 8
#define GF_POLY 0x11Dull
#else
#define GF_POLY 0x1100Bull
#endif
#define GF_Q (1u << FB)
static uint32_t gf_log[GF_Q];
static uint32_t gf_exp[2 * GF_Q];
static void gf_init(void) {
    uint64_t x = 1;
    for (uint32_t i = 0; i < GF_Q - 1; i++) {
        if (i && x == 1) { fprintf(stderr, "polynomial not primitive\n"); exit(1); }
        gf_exp[i] = (uint32_t)x; gf_log[x] = i;
        x <<= 1; if (x & GF_Q) x ^= GF_POLY;
    }
    for (uint32_t i = GF_Q - 1; i < 2 * GF_Q; i++) gf_exp[i] = gf_exp[i - (GF_Q - 1)];
}
static inline fe gf_mul(fe a, fe b) { return (a && b) ? gf_exp[gf_log[a] + gf_log[b]] : 0; }
static inline fe gf_inv(fe a) { return gf_exp[(GF_Q - 1) - gf_log[a]]; }
static inline fe gf_rand(void) { return rng_u64() & (GF_Q - 1); }
#define GF_Q_LOG FB
#endif
static inline fe gf_rand_nz(void) { fe a; do a = gf_rand(); while (!a); return a; }
// |F| as a double, without shifting by the word size when FB = 64
static inline double gf_order(void) { double q = 1; for (int i = 0; i < FB; i++) q *= 2; return q; }
#endif
