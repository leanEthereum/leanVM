// Researcher 18. GF(2^m), 8 <= m <= 64, by carry-less multiply (NEON pmull, portable fallback), with lazily reduced
// inner products. One global field per program.
#ifndef GF18_H
#define GF18_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;

static int FM = 64;
static u64 FR = 0x1b, FMASK = ~0ull;

#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
#include <arm_neon.h>
static inline void clmul(u64 a, u64 b, u64 *lo, u64 *hi) {
  poly128_t p = vmull_p64(a, b);
  *lo = (u64)p;
  *hi = (u64)(p >> 64);
}
#else
static inline void clmul(u64 a, u64 b, u64 *lo, u64 *hi) {
  u64 l = 0, h = 0;
  for (int i = 0; i < 64; i++)
    if (b >> i & 1) { l ^= a << i; if (i) h ^= a >> (64 - i); }
  *lo = l; *hi = h;
}
#endif

static inline u64 gf_red(u64 lo, u64 hi) {
  if (FM == 64) {
    u64 l2, h2, l3, h3;
    clmul(hi, FR, &l2, &h2);
    clmul(h2, FR, &l3, &h3);
    return lo ^ l2 ^ l3;
  }
  for (;;) {
    u64 t = (lo >> FM) | (hi << (64 - FM));
    if (!t) return lo;
    lo &= FMASK;
    u64 l2;
    clmul(t, FR, &l2, &hi);
    lo ^= l2;
  }
}
static inline u64 gf_mul(u64 a, u64 b) {
  u64 lo, hi;
  clmul(a, b, &lo, &hi);
  return gf_red(lo, hi);
}
// sum of a[i] b[i], one reduction
static inline u64 gf_dot(const u64 *a, const u64 *b, int len) {
  u64 lo = 0, hi = 0, l, h;
  for (int i = 0; i < len; i++) { clmul(a[i], b[i], &l, &h); lo ^= l; hi ^= h; }
  return gf_red(lo, hi);
}
static u64 gf_inv(u64 a) { // a^(2^m - 2)
  u64 r = 1, s = gf_mul(a, a);
  for (int i = 1; i < FM; i++) { r = gf_mul(r, s); s = gf_mul(s, s); }
  return r;
}
// lowest-weight irreducible tails used for the small real-shape fields
static void gf_init(int m) {
  static const u64 tail[65] = {[8] = 0x1b, [9] = 0x11, [10] = 0x9, [11] = 0x5, [12] = 0x53, [13] = 0x1b, [14] = 0x443,
                               [15] = 0x3, [16] = 0x2d, [20] = 0x9, [32] = 0x8d, [64] = 0x1b};
  if (m < 8 || m > 64 || !tail[m]) { fprintf(stderr, "no modulus for m = %d\n", m); exit(1); }
  FM = m; FR = tail[m]; FMASK = m == 64 ? ~0ull : (1ull << m) - 1;
  // sanity: x^(2^m) = x, and x^(2^(m/p)) != x for the primes p | m
  u64 y = 2;
  for (int i = 1; i <= m; i++) {
    y = gf_mul(y, y);
    if (i < m && m % i == 0 && y == 2) { fprintf(stderr, "modulus not irreducible\n"); exit(1); }
  }
  if (y != 2) { fprintf(stderr, "modulus not irreducible\n"); exit(1); }
}
static u64 rng_state = 0x9e3779b97f4a7c15ull;
static u64 rnd64(void) {
  u64 z = (rng_state += 0x9e3779b97f4a7c15ull);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}
static u64 gf_rand(void) { return rnd64() & FMASK; }
#endif
