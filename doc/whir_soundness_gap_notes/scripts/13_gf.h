// Researcher 13. GF(2^m) = F_2[x]/(x^m + r(x)) for 8 <= m <= 64 (deg r <= 32 when m = 64), by carry-less multiply
// (NEON pmull, portable fallback). Several fields can coexist: every function takes the field.
// Also: inverse, square root, a linear solver for z^2 + z = c, subspace-polynomial values, a radix sort.
#ifndef GF13_H
#define GF13_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;

typedef struct {
  int m;
  u64 r, mask;
  u64 as_piv[64], as_pre[64]; // echelon basis of the image of z -> z^2 + z, with preimages
  int as_n;
  u64 as_tab[8][256];         // linear section c -> z, z^2 + z = c for c in the image
} gf_t;

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

static inline u64 gf_mul(const gf_t *F, u64 a, u64 b) {
  u64 lo, hi;
  clmul(a, b, &lo, &hi);
  if (F->m == 64) {
    u64 l2, h2;
    clmul(hi, F->r, &l2, &h2); lo ^= l2;
    clmul(h2, F->r, &l2, &hi); lo ^= l2;
    return lo;
  }
  for (;;) {
    u64 t = (lo >> F->m) | (hi << (64 - F->m));
    if (!t) return lo;
    lo &= F->mask;
    u64 l2;
    clmul(t, F->r, &l2, &hi);
    lo ^= l2;
  }
}
static inline u64 gf_sqr(const gf_t *F, u64 a) { return gf_mul(F, a, a); }
static u64 gf_inv(const gf_t *F, u64 a) { // a^(2^m - 2)
  u64 r = 1, s = gf_sqr(F, a);
  for (int i = 1; i < F->m; i++) { r = gf_mul(F, r, s); s = gf_sqr(F, s); }
  return r;
}
static u64 gf_sqrt(const gf_t *F, u64 a) {
  for (int i = 1; i < F->m; i++) a = gf_sqr(F, a);
  return a;
}
static void gf_init(gf_t *F, int m, u64 r) {
  F->m = m; F->r = r; F->mask = m == 64 ? ~0ull : (1ull << m) - 1;
  int dr = 63 - __builtin_clzll(r);
  if (m == 64 ? dr > 32 : dr >= m) { fprintf(stderr, "modulus tail too long\n"); exit(1); }
  // Artin-Schreier solver
  F->as_n = 0;
  u64 piv[64], pre[64]; int has[64]; memset(has, 0, sizeof has);
  for (int i = 0; i < m; i++) {
    u64 z = 1ull << i, v = gf_sqr(F, z) ^ z;
    for (int b = m - 1; b >= 0 && v; b--) if (v >> b & 1) {
      if (has[b]) { v ^= piv[b]; z ^= pre[b]; } else { has[b] = 1; piv[b] = v; pre[b] = z; break; }
    }
  }
  for (int t = 0; t < 8; t++) for (int byte = 0; byte < 256; byte++) {
    u64 c = (u64)byte << (8 * t), z = 0;
    if (8 * t >= m) { F->as_tab[t][byte] = 0; continue; }
    c &= F->mask;
    for (int b = m - 1; b >= 0; b--) if ((c >> b & 1) && has[b]) { c ^= piv[b]; z ^= pre[b]; }
    F->as_tab[t][byte] = z;
  }
}
// a z with z^2 + z = c (c must have trace 0; the caller checks the result when it matters)
static inline u64 gf_as(const gf_t *F, u64 c) {
  u64 z = 0;
  for (int t = 0; t < 8; t++) z ^= F->as_tab[t][(c >> (8 * t)) & 255];
  return z;
}
// values L_V(z_j) of the subspace polynomial of V = span(basis[0..d)) at nz points, in place
static void gf_subspace_eval(const gf_t *F, const u64 *basis, int d, u64 *z, int nz) {
  u64 v[64];
  for (int i = 0; i < d; i++) v[i] = basis[i];
  for (int i = 0; i < d; i++) {
    u64 p = v[i];
    if (!p) { fprintf(stderr, "dependent basis\n"); exit(1); }
    for (int j = i + 1; j < d; j++) v[j] = gf_mul(F, v[j], v[j] ^ p);
    for (int j = 0; j < nz; j++) z[j] = gf_mul(F, z[j], z[j] ^ p);
  }
}
static void radix_sort(u64 *a, size_t n) {
  u64 *b = malloc(n * sizeof(u64));
  if (!b) { fprintf(stderr, "out of memory\n"); exit(1); }
  for (int pass = 0; pass < 4; pass++) {
    size_t *cnt = calloc(65537, sizeof(size_t));
    int sh = 16 * pass;
    for (size_t i = 0; i < n; i++) cnt[((a[i] >> sh) & 65535) + 1]++;
    for (int i = 0; i < 65536; i++) cnt[i + 1] += cnt[i];
    for (size_t i = 0; i < n; i++) b[cnt[(a[i] >> sh) & 65535]++] = a[i];
    free(cnt);
    u64 *t = a; a = b; b = t;
  }
  free(b);
}
static u64 rng_state = 0x9e3779b97f4a7c15ull;
static u64 rnd64(void) {
  u64 z = (rng_state += 0x9e3779b97f4a7c15ull);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}
#endif
