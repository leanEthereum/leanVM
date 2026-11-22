// 30_crit: test of the corrected three-set statement WITH MULTIPLICITIES (note 30, Conjecture S3) one level down.
//
//   cc -O2 -o 30_crit 30_crit.c
//   ./30_crit N delta [stride] [seed] [dump]      N = 3 or 4
//
// Every pattern of three pairwise disjoint sets in F_2^N with |Ri| <= delta, sum = 2 delta + 2 (0 in R0) is pushed
// forward along every direction a to a pattern of multiplicity vectors (entries 0, 1, 2) on the generic subspace of
// dimension N - 1. For each push-forward the program compares
//   truth:      the delta + 1 polynomials Z^{m_i} X^e, e <= delta - |m_i|, are linearly dependent (random basis in
//               GF(2^64)), and
//   prediction: (D) two of the three spaces meet, |max(m_i, m_j)| <= delta, or
//               (S) there are a subspace U, a Frobenius exponent j, delta_0 >= 0 and multiplicity vectors beta_i on the
//                   quotient by U with sum |beta_i| <= 2 delta_0 + 1 and
//                   sum_x max_i (m_i(x) - 2^j beta_i(x mod U))^+  +  |U| 2^j delta_0  <=  delta.
// (D) and (S) imply dependence on every subspace (proved in the note: u_i = G (v_i o L_U)^{2^j}). The conjecture is the
// converse on a generic subspace. The same comparison is made for the set patterns themselves at level N.
// With stride s only every s-th pattern is examined. The prediction is evaluated for every singular pattern (the
// conjectured direction) and for one nonsingular pattern in 64 (the proved direction, as a check of the program).
#include "02_gf.h"
#define MAXP 16
static int NN, n, delta;
static u64 pts[5][MAXP];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int kerdim(int d, int m[3][MAXP]) {
  static u64 B[24][24]; u64 z[3][24]; int dz[3], off[4], cnt[3]; off[0] = 0;
  int np = 1 << d;
  for (int i = 0; i < 3; i++) {
    z[i][0] = 1; int dd = 0;
    for (int p = 0; p < np; p++) for (int r = 0; r < m[i][p]; r++) { z[i][dd + 1] = 0; for (int j = dd + 1; j >= 1; j--) z[i][j] = z[i][j - 1] ^ gmul(z[i][j], pts[d][p]); z[i][0] = gmul(z[i][0], pts[d][p]); dd++; }
    dz[i] = dd; cnt[i] = dd <= delta ? delta - dd + 1 : 0; off[i + 1] = off[i] + cnt[i];
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

// subspaces of F_2^d as lists of elements
static int nsub[5], subsz[5][70], subel[5][70][16];
static void init_subspaces(void) {
  for (int d = 0; d <= 4; d++) {
    int np = 1 << d; nsub[d] = 0;
    for (unsigned mask = 1; mask < (1u << np); mask += 2) { // contains 0
      int pc = __builtin_popcount(mask); if (pc & (pc - 1)) continue;
      int ok = 1; for (int x = 0; x < np && ok; x++) if (mask >> x & 1) for (int y = 0; y < np; y++) if ((mask >> y & 1) && !(mask >> (x ^ y) & 1)) { ok = 0; break; }
      if (!ok) continue;
      int s = nsub[d]++; subsz[d][s] = 0; for (int x = 0; x < np; x++) if (mask >> x & 1) subel[d][s][subsz[d][s]++] = x;
    }
  }
}
static int predD(int d, int m[3][MAXP]) {
  for (int i = 0; i < 3; i++) { int j = (i + 1) % 3, s = 0; for (int p = 0; p < (1 << d); p++) s += m[i][p] > m[j][p] ? m[i][p] : m[j][p]; if (s <= delta) return 1; }
  return 0;
}
// (S): returns 1 if some (U, j, delta_0, beta) certifies dependence; *wu, *wj, *wd receive the witness
static int predS(int d, int m[3][MAXP], int *wu, int *wj, int *wd) {
  int np = 1 << d, maxm = 0;
  for (int i = 0; i < 3; i++) for (int p = 0; p < np; p++) if (m[i][p] > maxm) maxm = m[i][p];
  int W = 2 * delta + 1;
  for (int s = 0; s < nsub[d]; s++) for (int j = 0; (1 << j) <= (maxm > 1 ? maxm : 1) * 2; j++) {
    int q = 1 << j, usz = subsz[d][s];
    if (usz * q > delta && 0) continue;
    int best[40]; for (int w = 0; w <= W; w++) best[w] = 0;
    char seen[MAXP]; memset(seen, 0, sizeof seen);
    int bmax = (maxm + q - 1) / q;
    for (int p = 0; p < np; p++) if (!seen[p]) {
      int cos[16]; for (int e = 0; e < usz; e++) { cos[e] = p ^ subel[d][s][e]; seen[cos[e]] = 1; }
      int nb[40]; for (int w = 0; w <= W; w++) nb[w] = 1 << 20;
      for (int b0 = 0; b0 <= bmax; b0++) for (int b1 = 0; b1 <= bmax; b1++) for (int b2 = 0; b2 <= bmax; b2++) {
        int wt = b0 + b1 + b2, cost = 0;
        for (int e = 0; e < usz; e++) { int x = cos[e], g = 0, t;
          t = m[0][x] - q * b0; if (t > g) g = t; t = m[1][x] - q * b1; if (t > g) g = t; t = m[2][x] - q * b2; if (t > g) g = t; cost += g; }
        for (int w = wt; w <= W; w++) if (best[w - wt] + cost < nb[w]) nb[w] = best[w - wt] + cost;
      }
      for (int w = 0; w <= W; w++) best[w] = nb[w];
    }
    for (int w = 1; w <= W; w++) if (best[w - 1] < best[w]) best[w] = best[w - 1];
    for (int d0 = 0; usz * q * d0 <= delta; d0++) { int w = 2 * d0 + 1; if (w > W) w = W; if (best[w] + usz * q * d0 <= delta) { *wu = usz; *wj = j; *wd = d0; return 1; } }
  }
  return 0;
}
static long ntot, skipped[2], cnt[2][2][3], wit[2][20][4][8]; // cnt[level][truth][prediction: 0 none, 1 D, 2 S only]
static int dump; static long stride = 1, ctr;
static void classify(int lev, int d, int m[3][MAXP], unsigned R0, unsigned R1, unsigned R2, int a) {
  int truth = kerdim(d, m) > 0, wu = 0, wj = 0, wd = 0;
  if (!truth && (rnd() & 63)) { cnt[lev][0][0]++; skipped[lev]++; return; } // (D) or (S) => singular is proved; it is re-checked on 1 in 64
  int pd = predD(d, m), ps = pd ? 0 : predS(d, m, &wu, &wj, &wd);
  int pr = pd ? 1 : ps ? 2 : 0;
  cnt[lev][truth][pr]++;
  if (pr == 2) wit[lev][wu][wj][wd]++;
  if ((truth && !pr) || (!truth && pr)) {
    if (dump) { printf("MISMATCH level %d truth %d pred %d R=%04x %04x %04x a=%d m=", lev, truth, pr, R0, R1, R2, a); for (int i = 0; i < 3; i++) { for (int p = 0; p < (1 << d); p++) printf("%d", m[i][p]); printf(" "); } printf("\n"); }
  }
}
static void test(unsigned R0, unsigned R1, unsigned R2) {
  if (ctr++ % stride) return;
  ntot++;
  int m[3][MAXP]; memset(m, 0, sizeof m);
  for (int p = 0; p < n; p++) { m[0][p] = R0 >> p & 1; m[1][p] = R1 >> p & 1; m[2][p] = R2 >> p & 1; }
  classify(0, NN, m, R0, R1, R2, 0);
  for (int a = 1; a < n; a++) {
    int q[3][MAXP]; memset(q, 0, sizeof q);
    for (int i = 0; i < 3; i++) for (int p = 0; p < n; p++) q[i][quo(p, a)] += m[i][p];
    classify(1, NN - 1, q, R0, R1, R2, a);
  }
}
typedef struct { unsigned R0, R1; int r0, r1, r2; } ctx_t;
static void subsets(unsigned avail, int r, void (*f)(unsigned, void *), void *ctx) {
  int idx[MAXP], m = 0; for (int p = 0; p < n; p++) if (avail >> p & 1) idx[m++] = p;
  if (r > m) return;
  if (r == 0) { f(0, ctx); return; }
  u64 c = (1ull << r) - 1, lim = 1ull << m;
  while (c < lim) { unsigned S = 0; for (int i = 0; i < m; i++) if (c >> i & 1) S |= 1u << idx[i]; f(S, ctx); u64 t = c | (c - 1); c = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzll(c) + 1)); }
}
static void got_R2(unsigned R2, void *v) { ctx_t *c = v; if (c->r1 == c->r2 && R2 < c->R1) return; test(c->R0, c->R1, R2); }
static void got_R1(unsigned R1, void *v) { ctx_t *c = v; c->R1 = R1; subsets(((1u << n) - 1) & ~c->R0 & ~R1, c->r2, got_R2, c); }
static void got_R0(unsigned R0, void *v) { ctx_t *c = v; if (!(R0 & 1)) return; c->R0 = R0; subsets(((1u << n) - 1) & ~R0, c->r1, got_R1, c); }
int main(int argc, char **argv) {
  NN = atoi(argv[1]); delta = atoi(argv[2]); n = 1 << NN;
  if (argc > 3) stride = atol(argv[3]);
  if (argc > 4) rs ^= strtoull(argv[4], 0, 10) * 0x9e3779b97f4a7c15ull;
  dump = argc > 5;
  gf_init(64, 0x1b); init_subspaces();
  for (int d = 0; d <= NN; d++) { u64 b[5]; for (int i = 0; i < d; i++) b[i] = rnd(); for (int p = 0; p < (1 << d); p++) { u64 x = 0; for (int i = 0; i < d; i++) if (p >> i & 1) x ^= b[i]; pts[d][p] = x; } }
  for (int r0 = delta; r0 >= 0; r0--) for (int r1 = r0; r1 >= 0; r1--) { int r2 = 2 * delta + 2 - r0 - r1; if (r2 > r1 || r2 < 0) continue; if (r0 + r1 + r2 > n) continue;
    ctx_t c = {0, 0, r0, r1, r2}; subsets((1u << n) - 1, r0, got_R0, &c); }
  printf("N=%d delta=%d stride=%ld: %ld set patterns examined\n", NN, delta, stride, ntot);
  for (int lev = 0; lev < 2; lev++) {
    printf("%s: nonsingular %ld (prediction evaluated on %ld of them), of the evaluated: predicted nonsingular %ld, singular/(D) %ld, singular/(S) %ld | MISMATCHES: singular unpredicted %ld, nonsingular but (D) %ld, nonsingular but (S) %ld\n",
           lev ? "push-forwards (dimension N-1, multiplicities <= 2)" : "set patterns (dimension N)", cnt[lev][0][0] + cnt[lev][0][1] + cnt[lev][0][2], cnt[lev][0][0] + cnt[lev][0][1] + cnt[lev][0][2] - skipped[lev], cnt[lev][0][0] - skipped[lev], cnt[lev][1][1], cnt[lev][1][2], cnt[lev][1][0], cnt[lev][0][1], cnt[lev][0][2]);
    printf("   (S) witnesses (|U|, 2^j, delta_0): count:"); for (int u = 0; u < 20; u++) for (int j = 0; j < 4; j++) for (int d0 = 0; d0 < 8; d0++) if (wit[lev][u][j][d0]) printf(" (%d,%d,%d):%ld", u, 1 << j, d0, wit[lev][u][j][d0]); printf("\n");
  }
  return 0;
}
