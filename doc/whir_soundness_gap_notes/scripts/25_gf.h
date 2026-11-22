// Researcher 25. GF(2^64) with the leanVM modulus x^64+x^4+x^3+x+1 (NEON pmull, portable fallback),
// a xorshift generator and small dense linear algebra. Shared by the 25_*.c programs.
#ifndef GF25_H
#define GF25_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;

#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
#include <arm_neon.h>
static inline u64 gmul(u64 a, u64 b) {
  poly128_t p = vmull_p64(a, b);
  u64 lo = (u64)p, hi = (u64)(p >> 64);
  poly128_t q = vmull_p64(hi, 0x1b);
  lo ^= (u64)q;
  lo ^= (u64)vmull_p64((u64)(q >> 64), 0x1b);
  return lo;
}
#else
static inline u64 gmul(u64 a, u64 b) {
  u64 r = 0;
  for (int i = 0; i < 64; i++) {
    if (b & 1) r ^= a;
    b >>= 1;
    a = (a << 1) ^ ((a >> 63) ? 0x1b : 0);
  }
  return r;
}
#endif
static inline u64 gsq(u64 a) { return gmul(a, a); }
static u64 gpow(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = gmul(r, a); a = gsq(a); e >>= 1; } return r; }
static u64 ginv(u64 a) { return gpow(a, ~0ull - 1); }
static u64 gsqrt(u64 a) { for (int i = 0; i < 63; i++) a = gsq(a); return a; }

static u64 rng_s = 0x9e3779b97f4a7c15ull;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

// Row reduce the rows x cols matrix m (row-major, stride cols) in place, return the rank.
static int rank_inplace(u64 *m, int rows, int cols) {
  int rk = 0;
  for (int c = 0; c < cols && rk < rows; c++) {
    int p = -1;
    for (int i = rk; i < rows; i++) if (m[i * cols + c]) { p = i; break; }
    if (p < 0) continue;
    if (p != rk) for (int j = 0; j < cols; j++) { u64 t = m[p * cols + j]; m[p * cols + j] = m[rk * cols + j]; m[rk * cols + j] = t; }
    u64 iv = ginv(m[rk * cols + c]);
    for (int j = c; j < cols; j++) m[rk * cols + j] = gmul(m[rk * cols + j], iv);
    for (int i = 0; i < rows; i++) {
      if (i == rk) continue;
      u64 f = m[i * cols + c];
      if (!f) continue;
      for (int j = c; j < cols; j++) m[i * cols + j] ^= gmul(f, m[rk * cols + j]);
    }
    rk++;
  }
  return rk;
}

// Left null space of the rows x cols matrix a: all lambda with lambda a = 0. Writes a basis to out (stride rows),
// returns its dimension. a is not modified.
static int left_null(const u64 *a, int rows, int cols, u64 *out) {
  int w = cols + rows;
  u64 *m = malloc(sizeof(u64) * rows * w);
  for (int i = 0; i < rows; i++) {
    for (int j = 0; j < cols; j++) m[i * w + j] = a[i * cols + j];
    for (int j = 0; j < rows; j++) m[i * w + cols + j] = (i == j);
  }
  int rk = 0;
  for (int c = 0; c < cols && rk < rows; c++) {
    int p = -1;
    for (int i = rk; i < rows; i++) if (m[i * w + c]) { p = i; break; }
    if (p < 0) continue;
    if (p != rk) for (int j = 0; j < w; j++) { u64 t = m[p * w + j]; m[p * w + j] = m[rk * w + j]; m[rk * w + j] = t; }
    u64 iv = ginv(m[rk * w + c]);
    for (int j = 0; j < w; j++) m[rk * w + j] = gmul(m[rk * w + j], iv);
    for (int i = 0; i < rows; i++) {
      if (i == rk) continue;
      u64 f = m[i * w + c];
      if (!f) continue;
      for (int j = 0; j < w; j++) m[i * w + j] ^= gmul(f, m[rk * w + j]);
    }
    rk++;
  }
  for (int i = rk; i < rows; i++) memcpy(out + (size_t)(i - rk) * rows, m + (size_t)i * w + cols, sizeof(u64) * rows);
  free(m);
  return rows - rk;
}

// Intersection of the row spaces of a (ra x cols) and b (rb x cols). Writes a basis to out (stride cols), returns the dimension.
static int row_intersect(const u64 *a, int ra, const u64 *b, int rb, int cols, u64 *out) {
  int rows = ra + rb;
  u64 *st = malloc(sizeof(u64) * rows * cols), *nl = malloc(sizeof(u64) * rows * rows);
  memcpy(st, a, sizeof(u64) * ra * cols);
  memcpy(st + (size_t)ra * cols, b, sizeof(u64) * rb * cols);
  int d = left_null(st, rows, cols, nl);
  // vectors lambda_a a (= lambda_b b). Dependencies inside a alone give zero vectors, removed by a rank pass.
  for (int t = 0; t < d; t++)
    for (int j = 0; j < cols; j++) {
      u64 s = 0;
      for (int i = 0; i < ra; i++) s ^= gmul(nl[(size_t)t * rows + i], a[i * cols + j]);
      out[(size_t)t * cols + j] = s;
    }
  int rk = d ? rank_inplace(out, d, cols) : 0;
  free(st); free(nl);
  return rk;
}
#endif
