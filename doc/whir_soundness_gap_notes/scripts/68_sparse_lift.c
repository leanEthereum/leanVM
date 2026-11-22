// Adversarial test: lift a three-member list of the top code with a one-hot bottom factor, drop the leaves that
// read a coordinate in its support, and compare ranks: T2, T2 + r private message symbols, RS at random points.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static const u64 P = ((u64)1 << 61) - 1;
static inline u64 mul(u64 a, u64 b) { u128 t = (u128)a * b; u64 r = (u64)(t & P) + (u64)(t >> 61); return r >= P ? r - P : r; }
static inline u64 add(u64 a, u64 b) { u64 r = a + b; return r >= P ? r - P : r; }
static inline u64 sub(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 pw(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = mul(r, a); a = mul(a, a); e >>= 1; } return r; }
static u64 st = 88172645463325252ULL;
static u64 rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static u64 rf(void) { u64 x; do x = rnd() & P; while (x >= P || x == 0); return x; }
#define MAXN 512
#define MAXK 256
static int n, k, v;
static u64 G[MAXN][MAXK], H[MAXN][MAXK], R[MAXN][MAXK];
static void gen_t2(void) {
  static u64 S[MAXN][MAXK], S2[MAXN][MAXK]; int nodes = n / k, len = 1;
  for (int b = 0; b < nodes; b++) S[b][0] = 1;
  for (int lev = 0; lev < v; lev++) {
    for (int b = 0; b < nodes; b++) for (int ch = 0; ch < 2; ch++) { u64 t = rf(); int nb = 2 * b + ch; for (int e = 0; e < len; e++) { S2[nb][e] = S[b][e]; S2[nb][len + e] = mul(t, S[b][e]); } }
    nodes *= 2; len *= 2; memcpy(S, S2, sizeof(S));
  }
  memcpy(G, S, sizeof(G));
}
static int rank_mat(u64 *A, int rows, int cols) {
  int r = 0;
  for (int c = 0; c < cols && r < rows; c++) {
    int pv = -1; for (int i = r; i < rows; i++) if (A[(size_t)i * cols + c]) { pv = i; break; }
    if (pv < 0) continue;
    if (pv != r) for (int j = 0; j < cols; j++) { u64 t = A[(size_t)r * cols + j]; A[(size_t)r * cols + j] = A[(size_t)pv * cols + j]; A[(size_t)pv * cols + j] = t; }
    u64 iv = pw(A[(size_t)r * cols + c], P - 2);
    for (int j = c; j < cols; j++) A[(size_t)r * cols + j] = mul(A[(size_t)r * cols + j], iv);
    for (int i = r + 1; i < rows; i++) { u64 f = A[(size_t)i * cols + c]; if (!f) continue; for (int j = c; j < cols; j++) A[(size_t)i * cols + j] = sub(A[(size_t)i * cols + j], mul(f, A[(size_t)r * cols + j])); }
    r++;
  }
  return r;
}
static int pat_rank(u64 C[MAXN][MAXK], const int *pat, int M, int *wout) {
  int L = M - 1, cols = L * k, rows = 0; u64 *buf = calloc((size_t)n * L * cols, sizeof(u64));
  for (int x = 0; x < n; x++) { int prev = -1;
    for (int m = 0; m < M; m++) if (pat[x] >> m & 1) {
      if (prev >= 0) { u64 *row = buf + (size_t)rows * cols;
        if (prev > 0) for (int e = 0; e < k; e++) row[(prev - 1) * k + e] = C[x][e];
        for (int e = 0; e < k; e++) row[(m - 1) * k + e] = sub(0, C[x][e]); rows++; }
      prev = m; } }
  *wout = rows; int r = rank_mat(buf, rows, cols); free(buf); return r;
}
int main(int argc, char **argv) {
  int vtop = 3; int vb = atoi(argv[1]); int r = atoi(argv[2]); int y0 = 1; // top code (8,16), blocks of 2^vb leaves
  v = vtop + vb; k = 1 << v; n = 2 * k; int b = 1 << vb;
  // top pattern at (8,16): 01 01 01 01 012 012 . 012 02 02 02 02 12 12 12 12
  int top[16] = {3, 3, 3, 3, 7, 7, 0, 7, 5, 5, 5, 5, 6, 6, 6, 6};
  gen_t2();
  for (int x = 0; x < n; x++) { u64 a = rf(), t = 1; for (int e = 0; e < k; e++) { R[x][e] = t; t = mul(t, a); } }
  memcpy(H, G, sizeof(G));
  static int reads[MAXN][8];
  for (int x = 0; x < n; x++) for (int i = 0; i < r; i++) { int e = (x + i * (k / 2 + 1)) % k; reads[x][i] = e; H[x][e] = add(H[x][e], rf()); }
  int pat[MAXN], pat_full[MAXN], removed = 0;
  for (int x = 0; x < n; x++) { pat_full[x] = top[x / b]; int blind = 1;
    for (int i = 0; i < r; i++) if ((reads[x][i] >> vtop) == y0) blind = 0; // message index: low vtop bits = top part, high bits = bottom part
    pat[x] = blind ? pat_full[x] : 0; if (!blind && pat_full[x]) removed++; }
  int w; int cols = 2 * k;
  int a1 = pat_rank(G, pat_full, 3, &w); printf("(k,n)=(%d,%d), r=%d. Full lifted pattern: weight %d, columns %d: rank T2 %d", k, n, r, w, cols, a1);
  int a2 = pat_rank(H, pat_full, 3, &w), a3 = pat_rank(R, pat_full, 3, &w); printf(", T2+pert %d, RS %d\n", a2, a3);
  int c1 = pat_rank(G, pat, 3, &w), c2 = pat_rank(H, pat, 3, &w), c3 = pat_rank(R, pat, 3, &w);
  printf("  minus %d leaves reading the support of the one-hot factor: weight %d: rank T2 %d, T2+pert %d, RS %d\n", removed, w, c1, c2, c3);
  return 0;
}
