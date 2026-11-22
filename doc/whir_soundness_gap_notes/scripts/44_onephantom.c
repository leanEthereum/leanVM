// 44_onephantom: checks of note 44 Theorem 3.2 (one zero or pole outside D).
//
//   cc -O2 -o 44_onephantom 44_onephantom.c
//   ./44_onephantom N maxmult [seed]      N = 3 or 4
//
// D = span of N random elements of GF(2^64), A = {0, 1, 2, 3} (labels in F_2^N), y_i = 1, 2, 3, y_* = 0.
// Every m : D \ {1,2,3} -> {-maxmult..maxmult} is enumerated. P_i = prod_x (y_i + x)^m(x). The three points have one
// value under xi = c prod (X + x)^m(x) / (X + theta) for some theta iff P_1 a_1 + P_2 a_2 + P_3 a_3 = 0, a_i = y_j + y_k.
// For every such m: theta = y_1 + a_3 P_1/(P_1 + P_2) (infinity if P_1 = P_2), the class of theta (infinity, in D,
// outside D), the size of the whole fibre {y in D : P_y = lambda (y + theta)}, and, when theta is outside D, the
// structure asserted by the theorem: a subspace H with H cap A = 0 and j >= 0 with 2^j |H| >= 4 such that
// m + delta_0 - 2^j 1_H is A-periodic, m(0) = 2^j - 1.
#include "02_gf.h"
static int N, n; static u64 pts[32];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static u64 gpow_s(u64 a, int e) { if (e < 0) { a = ginv(a); e = -e; } u64 r = 1; while (e--) r = gmul(r, a); return r; }
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 44_onephantom N maxmult [seed]\n"); return 1; }
  N = atoi(argv[1]); n = 1 << N; int mm = atoi(argv[2]); u64 seed = argc > 3 ? strtoull(argv[3], 0, 0) : 1;
  gf_init(64, 0x1b); rs = seed * 0x9E3779B97F4A7C15ull + 12345; for (int i = 0; i < 20; i++) rnd();
  u64 b[8]; for (int i = 0; i < N; i++) b[i] = rnd();
  for (int x = 0; x < n; x++) { u64 v = 0; for (int i = 0; i < N; i++) if (x >> i & 1) v ^= b[i]; pts[x] = v; }
  int free_pts[32], nf = 0; for (int x = 0; x < n; x++) if (x < 1 || x > 3) free_pts[nf++] = x;
  // subspaces H of F_2^N with H cap {0,1,2,3} = 0, as bit masks of their elements
  unsigned Hs[4096]; int nH = 0;
  for (unsigned S = 1; S < (1u << n); S += 2) { // contains 0
    int c = __builtin_popcount(S); if (c & (c - 1)) continue; if (S & 0xe) continue;
    int ok = 1; for (int x = 0; x < n && ok; x++) if (S >> x & 1) for (int y = 0; y < n; y++) if ((S >> y & 1) && !(S >> (x ^ y) & 1)) { ok = 0; break; }
    if (ok) Hs[nH++] = S;
    if (n > 16 && S > (1u << 20)) break;
  }
  if (n > 16) { fprintf(stderr, "N <= 4\n"); return 1; }
  int base = 2 * mm + 1; long total = 1; for (int i = 0; i < nf; i++) total *= base;
  long nid = 0, ninf = 0, ninD = 0, nout = 0, bad_fibre = 0, bad_struct = 0, fib_hist[40] = {0}, type_hist[8][8] = {{0}};
  int m[32];
  // table of powers (y_i + x)^e
  static u64 pw[4][32][16]; for (int i = 1; i <= 3; i++) for (int x = 0; x < n; x++) if (x != i) for (int e = -mm; e <= mm; e++) pw[i][x][e + mm] = gpow_s(pts[i] ^ pts[x], e);
  u64 a1 = pts[2] ^ pts[3], a2 = pts[1] ^ pts[3], a3 = pts[1] ^ pts[2];
  for (long code = 0; code < total; code++) {
    long c = code; for (int x = 0; x < n; x++) m[x] = 0;
    u64 P[4] = {0, 1, 1, 1};
    for (int i = 0; i < nf; i++) { int e = (int)(c % base); c /= base; m[free_pts[i]] = e - mm; for (int k = 1; k <= 3; k++) P[k] = gmul(P[k], pw[k][free_pts[i]][e]); }
    if ((gmul(P[1], a1) ^ gmul(P[2], a2) ^ gmul(P[3], a3)) != 0) continue;
    nid++;
    if (P[1] == P[2]) { ninf++; continue; }
    u64 lam = gmul(P[1] ^ P[2], ginv(a3)); u64 theta = pts[1] ^ gmul(P[1], ginv(lam));
    int inD = 0; for (int x = 0; x < n; x++) if (pts[x] == theta) inD = 1;
    // whole fibre
    int fib = 0;
    for (int y = 0; y < n; y++) { if (m[y]) continue; u64 Py = 1; for (int x = 0; x < n; x++) if (m[x]) Py = gmul(Py, gpow_s(pts[y] ^ pts[x], m[x])); if (Py == gmul(lam, pts[y] ^ theta)) fib++; }
    if (inD) { ninD++; continue; }
    nout++; fib_hist[fib]++; if (fib != 3) { bad_fibre++; printf("FIBRE of size %d with theta outside D, code %ld\n", fib, code); }
    // structure
    int found = 0;
    for (int h = 0; h < nH && !found; h++) for (int j = 0; j <= 4 && !found; j++) {
      int q = 1 << j; int sz = __builtin_popcount(Hs[h]); if (q * sz < 4) continue; if (m[0] != q - 1) continue;
      int ok = 1;
      for (int x = 0; x < n && ok; x++) { int g0 = m[x] + (x == 0) - ((Hs[h] >> x & 1) ? q : 0); for (int a = 1; a <= 3; a++) { int z = x ^ a; int g1 = m[z] + (z == 0) - ((Hs[h] >> z & 1) ? q : 0); if (g1 != g0) { ok = 0; break; } } }
      if (ok) { found = 1; int ls = 0; while ((1 << ls) < sz) ls++; type_hist[j][ls]++; }
    }
    if (!found) { bad_struct++; printf("NO STRUCTURE, code %ld\n", code); }
  }
  printf("N=%d, multiplicities in [-%d,%d]: %ld divisors, identity holds for %ld: theta = infinity %ld, theta in D %ld, theta outside D %ld\n", N, mm, mm, total, nid, ninf, ninD, nout);
  printf("theta outside D: fibre sizes"); for (int i = 0; i < 40; i++) if (fib_hist[i]) printf(" %d:%ld", i, fib_hist[i]); printf("; fibres of size != 3: %ld; without the structure of the theorem: %ld\n", bad_fibre, bad_struct);
  for (int j = 0; j < 8; j++) for (int l = 0; l < 8; l++) if (type_hist[j][l]) printf("  (2^j, |H|) = (%d, %d): %ld\n", 1 << j, 1 << l, type_hist[j][l]);
  return 0;
}
