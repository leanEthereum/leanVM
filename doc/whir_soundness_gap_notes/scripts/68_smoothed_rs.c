// "Smoothed" codes over GF(2^64) = F_2[x]/(x^64+x^4+x^3+x+1): today's Reed-Solomon code on an F_2-subspace
// (novel basis), plus r hash-like private multiples of raw message symbols at each position.
// Rank of list patterns against Reed-Solomon at random points. Usage: sm v M seed trials mode
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <arm_neon.h>
typedef uint64_t u64;
static inline u64 mul(u64 a, u64 b) {
  poly128_t p = vmull_p64(a, b); u64 lo = (u64)p, hi = (u64)(p >> 64);
  poly128_t t = vmull_p64(hi, 0x1B); lo ^= (u64)t; u64 h2 = (u64)(t >> 64);
  return lo ^ (u64)vmull_p64(h2, 0x1B);
}
static u64 inv(u64 a) { u64 r = 1, b = a; for (int i = 1; i < 64; i++) { b = mul(b, b); r = mul(r, b); } return r; } // a^(2^64-2)
static u64 st;
static u64 rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static u64 rf(void) { u64 x; do x = rnd(); while (!x); return x; }
#define MAXN 256
#define MAXK 128
static int n, k, v;
// today's code: points = span of a random basis, natural order; row = novel-basis polynomials X_e(x)
static void gen_sub(u64 G[MAXN][MAXK]) {
  int m = v + 1; u64 beta[16]; for (int i = 0; i < m; i++) beta[i] = rf();
  // W_i(x) = prod over span(beta_0..beta_{i-1}) (x + s); W_{i+1}(x) = W_i(x) * (W_i(x) + W_i(beta_i))
  u64 wb[16]; // W_i(beta_i)
  for (int i = 0; i < m; i++) { u64 w = beta[i]; for (int j = 0; j < i; j++) w = mul(w, w ^ wb[j]); wb[i] = w; }
  for (int x = 0; x < n; x++) {
    u64 pt = 0; for (int i = 0; i < m; i++) if (x >> i & 1) pt ^= beta[m - 1 - i]; // top bit of x = last basis vector's coset order does not matter
    u64 what[16]; u64 w = pt; for (int i = 0; i < v; i++) { what[i] = mul(w, inv(wb[i])); w = mul(w, w ^ wb[i]); }
    for (int e = 0; e < k; e++) { u64 t = 1; for (int i = 0; i < v; i++) if (e >> i & 1) t = mul(t, what[i]); G[x][e] = t; }
  }
}
static void gen_rs(u64 G[MAXN][MAXK]) { for (int x = 0; x < n; x++) { u64 a = rf(), t = 1; for (int e = 0; e < k; e++) { G[x][e] = t; t = mul(t, a); } } }
static void smooth(u64 G[MAXN][MAXK], const u64 B[MAXN][MAXK], int r, int stride) {
  memcpy(G, B, sizeof(u64) * MAXN * MAXK);
  for (int x = 0; x < n; x++) for (int i = 0; i < r; i++) { int e = (x + i * stride) % k; G[x][e] ^= rf(); }
}
static int rank_mat(u64 *A, int rows, int cols) {
  int r = 0;
  for (int c = 0; c < cols && r < rows; c++) {
    int pv = -1; for (int i = r; i < rows; i++) if (A[i * cols + c]) { pv = i; break; }
    if (pv < 0) continue;
    if (pv != r) for (int j = 0; j < cols; j++) { u64 t = A[r * cols + j]; A[r * cols + j] = A[pv * cols + j]; A[pv * cols + j] = t; }
    u64 iv = inv(A[r * cols + c]);
    for (int j = c; j < cols; j++) A[r * cols + j] = mul(A[r * cols + j], iv);
    for (int i = r + 1; i < rows; i++) { u64 f = A[i * cols + c]; if (!f) continue; for (int j = c; j < cols; j++) A[i * cols + j] ^= mul(f, A[r * cols + j]); }
    r++;
  }
  return r;
}
static u64 *buf;
static int pat_rank(u64 G[MAXN][MAXK], const int *pat, int M) {
  int L = M - 1, cols = L * k, rows = 0;
  for (int x = 0; x < n; x++) { int prev = -1;
    for (int m = 0; m < M; m++) if (pat[x] >> m & 1) {
      if (prev >= 0) { u64 *row = buf + (size_t)rows * cols; memset(row, 0, sizeof(u64) * cols);
        if (prev > 0) for (int e = 0; e < k; e++) row[(prev - 1) * k + e] = G[x][e];
        for (int e = 0; e < k; e++) row[(m - 1) * k + e] = G[x][e]; rows++; }
      prev = m; } }
  if (!rows) return 0; return rank_mat(buf, rows, cols);
}
static int weight(const int *pat, int M) { int w = 0; for (int x = 0; x < n; x++) { int c = __builtin_popcount(pat[x]); if (c >= 2) w += c - 1; } return w; }
#define NC 6
int main(int argc, char **argv) {
  v = atoi(argv[1]); int M = atoi(argv[2]); st = strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL + 1; long trials = atol(argv[4]); int mode = argc > 5 ? atoi(argv[5]) : 0;
  k = 1 << v; n = 2 * k; int L = M - 1; buf = malloc(sizeof(u64) * (size_t)n * L * L * k);
  static u64 G[NC][MAXN][MAXK]; const char *names[NC] = {"RSrand", "today", "today+1", "today+2", "today+3", "today+1b"};
  gen_rs(G[0]); gen_sub(G[1]); smooth(G[2], G[1], 1, 1); smooth(G[3], G[1], 2, 1); smooth(G[4], G[1], 3, 1); smooth(G[5], G[1], 1, 1);
  int nsub = 0, subs[64]; for (int s = 0; s < (1 << M); s++) if (__builtin_popcount(s) != 1) subs[nsub++] = s;
  long hist[NC][8]; memset(hist, 0, sizeof hist); long done = 0; int pat[MAXN]; int shown[NC] = {0};
  for (long t = 0; t < trials; t++) {
    if (mode == 0) { for (int x = 0; x < n; x++) pat[x] = subs[rnd() % nsub]; }
    else { int b = 1 << (1 + rnd() % (v)); for (int x = 0; x < n; x += b) { int s = subs[rnd() % nsub]; for (int y = 0; y < b; y++) pat[x + y] = s; }
      int pert = rnd() % 4; for (int i = 0; i < pert; i++) pat[rnd() % n] = subs[rnd() % nsub]; }
    int w = weight(pat, M); if (w < L * k - 3 || w > L * k + 3) continue;
    int r0 = pat_rank(G[0], pat, M); done++;
    for (int c = 1; c < NC; c++) { int r = pat_rank(G[c], pat, M); int g = r0 - r; if (g < 0) g = 7; if (g > 6) g = 6; hist[c][g]++;
      if (g && c >= 2 && shown[c] < 1) { shown[c]++; printf("  %s gap %d (w %d, RS rank %d):", names[c], g == 7 ? -1 : g, w, r0); for (int x = 0; x < n; x++) { printf(" "); if (!pat[x]) printf("."); for (int m = 0; m < M; m++) if (pat[x] >> m & 1) printf("%d", m); } printf("\n"); } }
  }
  printf("(k,n)=(%d,%d) M=%d mode=%d: %ld near-critical patterns. rank(RSrand)-rank(code) [0,1,2,...; last = above]:\n", k, n, M, mode, done);
  for (int c = 1; c < NC; c++) { printf("  %-9s", names[c]); for (int g = 0; g < 8; g++) printf(" %ld", hist[c][g]); printf("\n"); }
  return 0;
}
