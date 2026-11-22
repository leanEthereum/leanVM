// 30_step: the step of the merge induction at a level WITH multiplicities (note 30, section 6.3).
//
//   cc -O2 -o 30_step 30_step.c
//   ./30_step N s delta extra samples [seed]
//
// A random pattern of three pairwise disjoint sets in F_2^N (|Ri| <= delta, sum = 2 delta + 2 + extra, sizes as
// balanced as the bound allows up to a random perturbation) is pushed forward along a random s-dimensional subspace to
// F_2^(N-s) (multiplicities up to 2^s). If the push-forward is unsolvable (its polynomials Z^{m_i} X^e are linearly
// independent on the generic subspace of dimension N - s), the program asks whether one of its merges to dimension
// N - s - 1 is unsolvable too. Patterns with no such merge are 'terminal': the induction cannot treat them by merging.
#include "02_gf.h"
#define MAXP 64
#define MAXD 40
static int delta;
static u64 pts[7][MAXP];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int kerdim(int d, int m[3][MAXP]) {
  static u64 B[MAXD][3 * MAXD]; static u64 z[3][MAXD * 3]; int dz[3], off[4], cnt[3]; off[0] = 0;
  int np = 1 << d;
  for (int i = 0; i < 3; i++) {
    int tot = 0; for (int p = 0; p < np; p++) tot += m[i][p];
    dz[i] = tot; cnt[i] = tot <= delta ? delta - tot + 1 : 0; off[i + 1] = off[i] + cnt[i];
    if (!cnt[i]) continue;
    z[i][0] = 1; int dd = 0;
    for (int p = 0; p < np; p++) for (int r = 0; r < m[i][p]; r++) { z[i][dd + 1] = 0; for (int j = dd + 1; j >= 1; j--) z[i][j] = z[i][j - 1] ^ gmul(z[i][j], pts[d][p]); z[i][0] = gmul(z[i][0], pts[d][p]); dd++; }
  }
  int nc = off[3], nr = delta + 1;
  for (int r = 0; r < nr; r++) for (int c = 0; c < nc; c++) B[r][c] = 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j < cnt[i]; j++) for (int l = 0; l <= dz[i]; l++) B[j + l][off[i] + j] = z[i][l];
  int rank = 0;
  for (int c = 0; c < nc && rank < nr; c++) {
    int r = rank; while (r < nr && !B[r][c]) r++;
    if (r == nr) continue;
    if (r != rank) for (int c2 = c; c2 < nc; c2++) { u64 t = B[r][c2]; B[r][c2] = B[rank][c2]; B[rank][c2] = t; }
    u64 P = B[rank][c];
    for (int rr = rank + 1; rr < nr; rr++) if (B[rr][c]) { u64 f = B[rr][c]; for (int c2 = c + 1; c2 < nc; c2++) B[rr][c2] = gmul(P, B[rr][c2]) ^ gmul(f, B[rank][c2]); B[rr][c] = 0; }
    rank++;
  }
  return nc - rank;
}
static inline int quo(int p, int a) { int b = __builtin_ctz(a); if (p >> b & 1) p ^= a; return (p & ((1 << b) - 1)) | ((p >> (b + 1)) << b); }
int main(int argc, char **argv) {
  int N = atoi(argv[1]), s = atoi(argv[2]); delta = atoi(argv[3]); int extra = atoi(argv[4]); long samples = atol(argv[5]);
  if (argc > 6) rs ^= strtoull(argv[6], 0, 10) * 0x9e3779b97f4a7c15ull;
  gf_init(64, 0x1b);
  for (int d = 0; d <= N; d++) { u64 b[7]; for (int i = 0; i < d; i++) b[i] = rnd(); for (int p = 0; p < (1 << d); p++) { u64 x = 0; for (int i = 0; i < d; i++) if (p >> i & 1) x ^= b[i]; pts[d][p] = x; } }
  int n = 1 << N, tot = 2 * delta + 2 + extra;
  if (tot > n || tot > 3 * delta) { printf("impossible parameters\n"); return 1; }
  long unsolv = 0, solv = 0, term = 0, hist[64] = {0};
  for (long it = 0; it < samples; it++) {
    int r[3];
    for (;;) { r[0] = tot / 3 + (int)(rnd() % 5) - 2; r[1] = (tot - r[0]) / 2 + (int)(rnd() % 3) - 1; r[2] = tot - r[0] - r[1]; if (r[0] >= 0 && r[1] >= 0 && r[2] >= 0 && r[0] <= delta && r[1] <= delta && r[2] <= delta) break; }
    int perm[MAXP]; for (int p = 0; p < n; p++) perm[p] = p;
    for (int p = n - 1; p > 0; p--) { int q = rnd() % (p + 1); int t = perm[p]; perm[p] = perm[q]; perm[q] = t; }
    int m[3][MAXP]; memset(m, 0, sizeof m);
    for (int j = 0; j < tot; j++) m[j < r[0] ? 0 : j < r[0] + r[1] ? 1 : 2][perm[j]] = 1;
    int d = N;
    for (int st = 0; st < s; st++) { int a = 1 + rnd() % ((1 << d) - 1); int q[3][MAXP]; memset(q, 0, sizeof q); for (int i = 0; i < 3; i++) for (int p = 0; p < (1 << d); p++) q[i][quo(p, a)] += m[i][p]; memcpy(m, q, sizeof m); d--; }
    if (kerdim(d, m)) { solv++; continue; }
    unsolv++;
    int good = 0;
    for (int a = 1; a < (1 << d); a++) { int q[3][MAXP]; memset(q, 0, sizeof q); for (int i = 0; i < 3; i++) for (int p = 0; p < (1 << d); p++) q[i][quo(p, a)] += m[i][p]; if (!kerdim(d - 1, q)) good++; }
    hist[good]++; if (!good) term++;
  }
  printf("N=%d s=%d (level %d, %d points, multiplicities <= %d) delta=%d extra=%d (excess E=%d): samples %ld, solvable %ld, unsolvable %ld, terminal %ld\n", N, s, N - s, 1 << (N - s), 1 << s, delta, extra, extra + 2, samples, solv, unsolv, term);
  printf("  unsolvable push-forwards by number of unsolvable merges:"); for (int g = 0; g < 64; g++) if (hist[g]) printf(" %d:%ld", g, hist[g]); printf("\n");
  return 0;
}
