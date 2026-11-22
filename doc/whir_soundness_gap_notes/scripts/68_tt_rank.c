// Rank comparison of list patterns: plain T2 tree code, tensor-train variants, Reed-Solomon at random points.
// Field GF(p), p = 2^61 - 1. Usage: ttc v M seed trials mode   (k = 2^v, n = 2k)
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
static u64 st;
static u64 rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static u64 rf(void) { u64 x; do x = rnd() & P; while (x >= P || x == 0); return x; }
#define MAXN 256
#define MAXK 128
#define MAXD 3
static int n, k, v;
// state-valued rows: S[x][e][c], c < d
static void gen_tt(u64 G[MAXN][MAXK], int d, int kind) {
  // kind 0: full random matrices; 1: diagonal (d independent T2 codes); 2: companion
  static u64 S[MAXN][MAXK][MAXD], Tm[MAXN][MAXD][MAXD];
  int nodes = n / k; // start: n/k blocks, each state row = e_0 (length-1 message), vector v0
  u64 v0[MAXD]; for (int c = 0; c < d; c++) v0[c] = (kind == 1) ? 1 : rf();
  if (d == 1) v0[0] = 1;
  for (int b = 0; b < nodes; b++) for (int c = 0; c < d; c++) S[b][0][c] = v0[c];
  int len = 1;
  for (int lev = 0; lev < v; lev++) {
    // each node splits in two children; child row = (r, T r)
    static u64 S2[MAXN][MAXK][MAXD];
    for (int b = 0; b < nodes; b++) for (int ch = 0; ch < 2; ch++) {
      u64 T[MAXD][MAXD];
      for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) {
        if (kind == 0) T[i][j] = rf();
        else if (kind == 1) T[i][j] = (i == j) ? rf() : 0;
        else T[i][j] = (i == d - 1) ? rf() : (j == i + 1 ? 1 : 0);
      }
      int nb = 2 * b + ch;
      for (int e = 0; e < len; e++) for (int c = 0; c < d; c++) {
        S2[nb][e][c] = S[b][e][c];
        u64 s = 0; for (int j = 0; j < d; j++) s = add(s, mul(T[c][j], S[b][e][j]));
        S2[nb][len + e][c] = s;
      }
    }
    nodes *= 2; len *= 2; memcpy(S, S2, sizeof(S));
  }
  for (int x = 0; x < n; x++) {
    u64 u[MAXD]; for (int c = 0; c < d; c++) u[c] = (d == 1) ? 1 : rf(); // private read-out vector
    for (int e = 0; e < k; e++) { u64 s = 0; for (int c = 0; c < d; c++) s = add(s, mul(u[c], S[x][e][c])); G[x][e] = s; }
  }
}

static void gen_sum(u64 G[MAXN][MAXK]) { static u64 A[MAXN][MAXK], B[MAXN][MAXK]; gen_tt(A, 1, 0); gen_tt(B, 1, 0); for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) G[x][e] = add(A[x][e], B[x][e]); }
// plain T2 plus, at each leaf, a private multiple of a local functional: a depth-s T2 network on one message block
static void gen_loc(u64 G[MAXN][MAXK], int s) {
  gen_tt(G, 1, 0); int b = 1 << s;
  for (int B0 = 0; B0 < n / b; B0++) {
    int mb = B0 % (k / b);
    u64 loc[MAXK][MAXK]; // rows of a depth-s rate-1 network on b coordinates
    int nodes = 1, len = 1; loc[0][0] = 1;
    for (int lev = 0; lev < s; lev++) { static u64 t2[MAXK][MAXK];
      for (int q = 0; q < nodes; q++) for (int ch = 0; ch < 2; ch++) { u64 t = rf(); for (int e = 0; e < len; e++) { t2[2 * q + ch][e] = loc[q][e]; t2[2 * q + ch][len + e] = mul(t, loc[q][e]); } }
      nodes *= 2; len *= 2; for (int q = 0; q < nodes; q++) for (int e = 0; e < len; e++) loc[q][e] = t2[q][e]; }
    for (int y = 0; y < b; y++) { u64 tau = rf(); int x = B0 * b + y; for (int e = 0; e < b; e++) G[x][mb * b + e] = add(G[x][mb * b + e], mul(tau, loc[y][e])); }
  }
}
// two-dimensional state on the top j levels only, then a private read-out at each node and scalar T2 below
static void gen_top(u64 G[MAXN][MAXK], int j) {
  static u64 S[MAXN][MAXK][2]; int nodes = n / k, len = 1; u64 v0[2] = {rf(), rf()};
  for (int b = 0; b < nodes; b++) { S[b][0][0] = v0[0]; S[b][0][1] = v0[1]; }
  static u64 R[MAXN][MAXK];
  for (int lev = 0; lev < v; lev++) {
    if (lev < j) { static u64 S2[MAXN][MAXK][2];
      for (int b = 0; b < nodes; b++) for (int ch = 0; ch < 2; ch++) { u64 T[2][2] = {{rf(), rf()}, {rf(), rf()}}; int nb = 2 * b + ch;
        for (int e = 0; e < len; e++) for (int c = 0; c < 2; c++) { S2[nb][e][c] = S[b][e][c]; S2[nb][len + e][c] = add(mul(T[c][0], S[b][e][0]), mul(T[c][1], S[b][e][1])); } }
      nodes *= 2; len *= 2; memcpy(S, S2, sizeof(S));
      if (lev == j - 1) for (int b = 0; b < nodes; b++) { u64 u0 = rf(), u1 = rf(); for (int e = 0; e < len; e++) R[b][e] = add(mul(u0, S[b][e][0]), mul(u1, S[b][e][1])); }
    } else { static u64 R2[MAXN][MAXK];
      if (lev == 0 && j == 0) for (int b = 0; b < nodes; b++) R[b][0] = 1;
      for (int b = 0; b < nodes; b++) for (int ch = 0; ch < 2; ch++) { u64 t = rf(); int nb = 2 * b + ch; for (int e = 0; e < len; e++) { R2[nb][e] = R[b][e]; R2[nb][len + e] = mul(t, R[b][e]); } }
      nodes *= 2; len *= 2; memcpy(R, R2, sizeof(R)); }
  }
  for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) G[x][e] = R[x][e];
}
static void gen_rs(u64 G[MAXN][MAXK]) { for (int x = 0; x < n; x++) { u64 a = rf(), t = 1; for (int e = 0; e < k; e++) { G[x][e] = t; t = mul(t, a); } } }
static int rank_mat(u64 *A, int rows, int cols) {
  int r = 0;
  for (int c = 0; c < cols && r < rows; c++) {
    int pv = -1; for (int i = r; i < rows; i++) if (A[i * cols + c]) { pv = i; break; }
    if (pv < 0) continue;
    if (pv != r) for (int j = 0; j < cols; j++) { u64 t = A[r * cols + j]; A[r * cols + j] = A[pv * cols + j]; A[pv * cols + j] = t; }
    u64 iv = pw(A[r * cols + c], P - 2);
    for (int j = c; j < cols; j++) A[r * cols + j] = mul(A[r * cols + j], iv);
    for (int i = r + 1; i < rows; i++) { u64 f = A[i * cols + c]; if (!f) continue; for (int j = c; j < cols; j++) A[i * cols + j] = sub(A[i * cols + j], mul(f, A[r * cols + j])); }
    r++;
  }
  return r;
}
static u64 *buf;
static int pat_rank(u64 G[MAXN][MAXK], const int *pat, int M) {
  int L = M - 1, cols = L * k, rows = 0;
  for (int x = 0; x < n; x++) {
    int prev = -1;
    for (int m = 0; m < M; m++) if (pat[x] >> m & 1) {
      if (prev >= 0) {
        u64 *row = buf + (size_t)rows * cols; memset(row, 0, sizeof(u64) * cols);
        if (prev > 0) for (int e = 0; e < k; e++) row[(prev - 1) * k + e] = G[x][e];
        for (int e = 0; e < k; e++) row[(m - 1) * k + e] = sub(0, G[x][e]);
        rows++;
      }
      prev = m;
    }
  }
  if (!rows) return 0;
  return rank_mat(buf, rows, cols);
}
static int weight(const int *pat, int M) { int w = 0; for (int x = 0; x < n; x++) { int c = __builtin_popcount(pat[x]); if (c >= 2) w += c - 1; } return w; }
int main(int argc, char **argv) {
  v = atoi(argv[1]); int M = atoi(argv[2]); st = strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL + 1; long trials = atol(argv[4]); int mode = argc > 5 ? atoi(argv[5]) : 0;
  k = 1 << v; n = 2 * k; int L = M - 1;
  buf = malloc(sizeof(u64) * (size_t)n * L * L * k);
  #define NC 11
  static u64 G[NC][MAXN][MAXK]; const char *names[NC] = {"RS", "T2", "TTfull2", "TTdiag2", "SUM", "LOC0", "LOC1", "LOC2", "TOP1", "TOP2", "TOP3"};
  gen_rs(G[0]); gen_tt(G[1], 1, 0); gen_tt(G[2], 2, 0); gen_tt(G[3], 2, 1); gen_sum(G[4]); gen_loc(G[5], 0); gen_loc(G[6], 1); gen_loc(G[7], 2); gen_top(G[8], 1); gen_top(G[9], 2); gen_top(G[10], 3);
  int nsub = 0, subs[64]; for (int s = 0; s < (1 << M); s++) if (__builtin_popcount(s) != 1) subs[nsub++] = s;
  long hist[NC][8]; memset(hist, 0, sizeof hist); long done = 0; int pat[MAXN]; int shown[NC] = {0};
  for (long t = 0; t < trials; t++) {
    if (mode == 0) { for (int x = 0; x < n; x++) pat[x] = subs[rnd() % nsub]; }
    else { // block patterns at a random scale, with a few perturbed leaves
      int b = 1 << (1 + rnd() % (v)); // block size 2..k
      for (int x = 0; x < n; x += b) { int s = subs[rnd() % nsub]; for (int y = 0; y < b; y++) pat[x + y] = s; }
      int pert = rnd() % 4; for (int i = 0; i < pert; i++) pat[rnd() % n] = subs[rnd() % nsub];
    }
    int w = weight(pat, M); if (w < L * k - 3 || w > L * k + 3) continue;
    int r0 = pat_rank(G[0], pat, M); done++;
    for (int c = 1; c < NC; c++) { int r = pat_rank(G[c], pat, M); int g = r0 - r; if (g < 0) g = 7; if (g > 6) g = 6; hist[c][g]++;
      if (g && c >= 2 && shown[c] < 1) { shown[c]++; printf("  %s gap %d (w %d, RS rank %d):", names[c], g == 7 ? -1 : g, w, r0); for (int x = 0; x < n; x++) { printf(" "); if (!pat[x]) printf("."); for (int m = 0; m < M; m++) if (pat[x] >> m & 1) printf("%d", m); } printf("\n"); } }
  }
  printf("(k,n)=(%d,%d) M=%d mode=%d: %ld near-critical patterns. rank(RS)-rank(code) histogram [0,1,2,..; last = code above RS]:\n", k, n, M, mode, done);
  for (int c = 1; c < NC; c++) { printf("  %-8s", names[c]); for (int g = 0; g < 8; g++) printf(" %ld", hist[c][g]); printf("\n"); }
  return 0;
}
