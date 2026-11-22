// 30_merge: the merge step of the GM-MDS proofs on a generic subspace, three sets.
//
//   cc -O2 -o 30_merge 30_merge.c
//   ./30_merge N delta [seed] [dump] [extra]        N = 3 or 4; extra > 0: overdetermined patterns, sum |Ri| = 2 delta + 2 + extra
//                                                   (then V(k) is not used and 'singular' means 'has a dependency')
//
// Pattern: pairwise disjoint R0, R1, R2 in D = F_2^N (a random N-dimensional subspace of GF(2^64) stands for the
// generic one), |Ri| <= delta, sum |Ri| = 2 delta + 2. It is SINGULAR if the delta + 1 polynomials Z_{Ri} X^e,
// e <= delta - |Ri|, are linearly dependent (Lovett's P(k, V) with k = delta + 1; Yildiz-Hassibi's det M = 0).
// For a direction a != 0 the MERGE of the pattern is its push-forward to D/a (a generic subspace of dimension N - 1):
// multiplicity vectors m_i(xbar) = |Ri cap {x, x + a}|, polynomials prod (X - xbar)^{m_i(xbar)} X^e.
// Rank is lower semicontinuous under specialization, so: merge nonsingular => pattern nonsingular (note 30, Lemma 3.1).
// The program asks the converse question the induction needs: does every nonsingular pattern have a nonsingular merge?
// It also records whether the merged pattern satisfies the counting condition V(k) of Lovett (necessary for
// nonsingularity on any point set), and for the patterns without a nonsingular merge whether the second degeneration
// (one affine hyperplane kept, the other half of D sent to infinity) certifies them.
#include "02_gf.h"
#define MAXP 16
static int NN, n, delta, extra;
static u64 pts[5][MAXP]; // pts[d][label]: generic subspace of dimension d
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

// kernel dimension of the system sum_i Z^{m_i} h_i = 0, deg h_i <= delta - |m_i|, on the 2^d points pts[d]
static int kerdim_inf(int d, int m[3][MAXP], const int *inf) {
  static u64 B[24][24]; u64 z[3][24]; int dz[3], off[4], cnt_[3]; off[0] = 0;
  int np = 1 << d;
  for (int i = 0; i < 3; i++) {
    z[i][0] = 1; int dd = 0;
    for (int p = 0; p < np; p++) for (int r = 0; r < m[i][p]; r++) { z[i][dd + 1] = 0; for (int j = dd + 1; j >= 1; j--) z[i][j] = z[i][j - 1] ^ gmul(z[i][j], pts[d][p]); z[i][0] = gmul(z[i][0], pts[d][p]); dd++; }
    dz[i] = dd; cnt_[i] = dd + inf[i] <= delta ? delta - dd - inf[i] + 1 : 0; off[i + 1] = off[i] + cnt_[i];
  }
  int nc = off[3], nr = delta + 1;
  for (int r = 0; r < nr; r++) for (int c = 0; c < nc; c++) B[r][c] = 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j < cnt_[i]; j++) for (int l = 0; l <= dz[i]; l++) B[j + l][off[i] + j] = z[i][l];
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
static const int NOINF[3] = {0, 0, 0};
static int kerdim(int d, int m[3][MAXP]) { return kerdim_inf(d, m, NOINF); }
// restriction to the affine hyperplane {phi_f = c}, the other half sent to infinity (note 30, section 3.3)
static int restrict_nonsingular(int d, int m[3][MAXP], int f, int c) {
  int q[3][MAXP], inf[3] = {0, 0, 0}; memset(q, 0, sizeof q); int b = __builtin_ctz(f), p0 = c ? (1 << b) : 0;
  for (int i = 0; i < 3; i++) for (int p = 0; p < (1 << d); p++) if (m[i][p]) { if ((__builtin_popcount(p & f) & 1) != c) inf[i] += m[i][p]; else { int y = p ^ p0; q[i][(y & ((1 << b) - 1)) | ((y >> (b + 1)) << b)] += m[i][p]; } }
  int mn = inf[0] < inf[1] ? inf[0] : inf[1]; if (inf[2] < mn) mn = inf[2]; if (mn) return 0;
  return !kerdim_inf(d - 1, q, inf);
}
// quotient label of p modulo a in dimension d
static inline int quo(int p, int a) { int b = __builtin_ctz(a); if (p >> b & 1) p ^= a; return (p & ((1 << b) - 1)) | ((p >> (b + 1)) << b); }
static void push(int d, int m[3][MAXP], int a, int out[3][MAXP]) {
  memset(out, 0, 3 * MAXP * sizeof(int));
  for (int i = 0; i < 3; i++) for (int p = 0; p < (1 << d); p++) out[i][quo(p, a)] += m[i][p];
}
// Lovett's V(k) for three vectors with sum |m_i| = 2 delta + 2: pairs and the triple
static int vk(int d, int m[3][MAXP]) {
  int s[3] = {0, 0, 0}, mn[3] = {0, 0, 0}, all = 0;
  for (int p = 0; p < (1 << d); p++) {
    for (int i = 0; i < 3; i++) s[i] += m[i][p];
    for (int i = 0; i < 3; i++) { int j = (i + 1) % 3, l = (i + 2) % 3; mn[i] += m[j][p] < m[l][p] ? m[j][p] : m[l][p]; }
    int t = m[0][p]; if (m[1][p] < t) t = m[1][p]; if (m[2][p] < t) t = m[2][p]; all += t;
  }
  for (int i = 0; i < 3; i++) if (s[i] > delta) return 0;
  for (int i = 0; i < 3; i++) if (mn[i] > delta + 1 - s[i]) return 0;
  return all == 0;
}
static long ntot, nsing, hist[17], hvk[17], term, termvk, termres, term2;
static int dump;
static void test(unsigned R0, unsigned R1, unsigned R2) {
  int m[3][MAXP]; memset(m, 0, sizeof m);
  for (int p = 0; p < n; p++) { m[0][p] = R0 >> p & 1; m[1][p] = R1 >> p & 1; m[2][p] = R2 >> p & 1; }
  ntot++;
  if (kerdim(NN, m)) { nsing++; return; }
  int good = 0, cnt = 0;
  for (int a = 1; a < n; a++) {
    int q[3][MAXP]; push(NN, m, a, q);
    if (!extra && !vk(NN - 1, q)) continue;
    cnt++;
    if (!kerdim(NN - 1, q)) good++;
  }
  hist[good]++; hvk[cnt]++;
  if (!good) { int res = 0; for (int f = 1; f < n; f++) for (int c = 0; c < 2; c++) res += restrict_nonsingular(NN, m, f, c);
    if (res) termres++; else term2++;
    term++; if (cnt) termvk++; if (dump && !res) printf("TERMINAL R=%04x %04x %04x  directions with V(k): %d\n", R0, R1, R2, cnt); }
}
typedef struct { unsigned R0, R1; int r0, r1, r2; } ctx_t;
static void subsets(unsigned avail, int r, void (*f)(unsigned, void *), void *ctx) {
  int idx[MAXP], m = 0; for (int p = 0; p < n; p++) if (avail >> p & 1) idx[m++] = p;
  if (r > m) return;
  if (r == 0) { f(0, ctx); return; }
  u64 c = (1ull << r) - 1, lim = 1ull << m;
  while (c < lim) { unsigned S = 0; for (int i = 0; i < m; i++) if (c >> i & 1) S |= 1u << idx[i]; f(S, ctx); u64 t = c | (c - 1); c = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzll(c) + 1)); }
}
static void got_R2(unsigned R2, void *v) { ctx_t *c = v; if (c->r1 == c->r2 && R2 < c->R1) return; test(c->R0, c->R1, R2); } // R1, R2 unordered when equal in size
static void got_R1(unsigned R1, void *v) { ctx_t *c = v; c->R1 = R1; subsets(((1u << n) - 1) & ~c->R0 & ~R1, c->r2, got_R2, c); }
static void got_R0(unsigned R0, void *v) { ctx_t *c = v; if (!(R0 & 1)) return; c->R0 = R0; subsets(((1u << n) - 1) & ~R0, c->r1, got_R1, c); } // translation: 0 in R0
int main(int argc, char **argv) {
  NN = atoi(argv[1]); delta = atoi(argv[2]); n = 1 << NN;
  if (argc > 3) rs ^= strtoull(argv[3], 0, 10) * 0x9e3779b97f4a7c15ull;
  dump = argc > 4 && atoi(argv[4]);
  if (argc > 5) extra = atoi(argv[5]);
  gf_init(64, 0x1b);
  for (int d = 0; d <= NN; d++) { u64 b[5]; for (int i = 0; i < d; i++) b[i] = rnd(); for (int p = 0; p < (1 << d); p++) { u64 x = 0; for (int i = 0; i < d; i++) if (p >> i & 1) x ^= b[i]; pts[d][p] = x; } }
  for (int r0 = delta; r0 >= 0; r0--) for (int r1 = r0; r1 >= 0; r1--) { int r2 = 2 * delta + 2 + extra - r0 - r1; if (r2 > r1 || r2 < 0) continue; if (r0 + r1 + r2 > n) continue;
    ctx_t c = {0, 0, r0, r1, r2}; subsets((1u << n) - 1, r0, got_R0, &c); }
  printf("N=%d delta=%d extra=%d: patterns (0 in R0) %ld, singular %ld, nonsingular %ld\n", NN, delta, extra, ntot, nsing, ntot - nsing);
  printf("nonsingular patterns by number of directions with a nonsingular merge:"); for (int g = 0; g < n; g++) if (hist[g]) printf(" %d:%ld", g, hist[g]); printf("\n");
  printf("nonsingular patterns by number of directions whose merge satisfies V(k):"); for (int g = 0; g < n; g++) if (hvk[g]) printf(" %d:%ld", g, hvk[g]); printf("\n");
  printf("terminal (nonsingular, no nonsingular merge): %ld, of which with some direction satisfying V(k): %ld\n", term, termvk);
  printf("terminal patterns certified by a restriction to an affine hyperplane (other half to infinity): %ld, not certified: %ld\n", termres, term2);
  return 0;
}
