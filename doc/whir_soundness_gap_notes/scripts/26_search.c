// 26_search: Conjecture P of note 17 (nu(xi) <= 2 deg(xi) + |Pi(xi)| on a generic F_2-subspace D), new coverage.
//
//   cc -O2 -o 26_search 26_search.c
//   ./26_search all N delta [seed]            every unordered triple of disjoint sets, N <= 4 (validation against note 17)
//   ./26_search dense part parts [seed]       N = 5, delta = 15, R = D: every partition of the 32 points into three sets
//                                             of size <= 15, the smallest set over orbit representatives of AGL(5, 2)
//   ./26_search dense2 u part parts [kmin kmax seed]   N = 5, u unused points, delta = (32 - u)/2 - 1: every configuration
//                                             of 32 - u points, (unused set, smallest set) over orbit representatives
//   ./26_search small delta N [seed]          every configuration of 2 delta + 2 points that affinely spans F_2^N
//                                             (frame 0, e_1..e_N plus extra points), every colouring with sizes <= delta
//   ./26_search mult N delta [seed]           patterns with multiplicities (sum 2 delta + 2): the statement P_mult,
//                                             sum of multiplicities <= 2 deg + q |Pi| with q the inseparability degree
//   ./26_search sym N mode seed poly...       colourings invariant under g = block companion matrix of the given
//                                             polynomials (bit masks, e.g. 0x25 = x^5+x^2+1); mode 0: g fixes the colours,
//                                             mode 1: g rotates them. All delta at once.
//
// D is the span of N random elements of GF(2^64). A configuration (R0, R1, R2), |Ri| <= delta, sum = 2 delta + 2, has a
// solution u0 + u1 + u2 = 0, deg <= delta, Z_{Ri} | ui iff a Hankel determinant vanishes: with R2 the smallest set and
// R0 the largest, t = delta - |R0| + 1, c_y = Z_{R0}(y) / (Z_{R1}(y) Z_{R2}'(y)) for y in R2, S_m = sum_y c_y y^m,
// the t x t matrix (S_{i+j}) is singular. (h0 Z0 + h1 Z1 vanishes on R2 iff h1 interpolates -h0 Z0/Z1 there, iff the
// divided differences of order > deg h1 vanish.) Nonsingular for the random basis implies nonsingular for the generic one.
#include "02_gf.h"
#define MAXP 256
#define MAXD 48
static int NN, n;
static u64 pts[MAXP];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void init_pts(int N, u64 seed) {
  NN = N; n = 1 << N; if (seed) rs = seed * 0x9E3779B97F4A7C15ull + 12345;
  for (int i = 0; i < 20; i++) rnd();
  u64 b[8]; for (int i = 0; i < N; i++) b[i] = rnd();
  for (int x = 0; x < n; x++) { u64 v = 0; for (int i = 0; i < N; i++) if (x >> i & 1) v ^= b[i]; pts[x] = v; }
}

// division-free determinant test, t x t
static int det_zero(u64 M[][MAXD], int t) {
  for (int c = 0; c < t; c++) {
    int p = -1; for (int i = c; i < t; i++) if (M[i][c]) { p = i; break; }
    if (p < 0) return 1;
    if (p != c) for (int j = c; j < t; j++) { u64 x = M[p][j]; M[p][j] = M[c][j]; M[c][j] = x; }
    u64 piv = M[c][c];
    for (int i = c + 1; i < t; i++) { u64 f = M[i][c]; for (int j = c + 1; j < t; j++) M[i][j] = gmul(M[i][j], piv) ^ gmul(f, M[c][j]); }
  }
  return 0;
}
static int hankel_zero(const u64 *c, const u64 *y, int k, int t) {
  u64 S[2 * MAXD], pw[MAXP]; static u64 M[MAXD][MAXD];
  for (int i = 0; i < k; i++) pw[i] = c[i];
  for (int m = 0; m <= 2 * (t - 1); m++) { u64 s = 0; for (int i = 0; i < k; i++) { s ^= pw[i]; pw[i] = gmul(pw[i], y[i]); } S[m] = s; }
  if (t == 1) return S[0] == 0;
  for (int i = 0; i < t; i++) for (int j = 0; j < t; j++) M[i][j] = S[i + j];
  return det_zero(M, t);
}

// generic test: three lists of point indices
static int singular3(const int *A[3], const int r[3], int delta) {
  int o[3] = {0, 1, 2};
  for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) if (r[o[j]] > r[o[i]]) { int x = o[i]; o[i] = o[j]; o[j] = x; }
  const int *R0 = A[o[0]], *R1 = A[o[1]], *R2 = A[o[2]]; int r0 = r[o[0]], r1 = r[o[1]], k = r[o[2]];
  int t = delta - r0 + 1;
  u64 num[MAXP], den[MAXP], y[MAXP], c[MAXP], pre[MAXP];
  for (int i = 0; i < k; i++) {
    u64 yy = pts[R2[i]], a = 1, b = 1; y[i] = yy;
    for (int j = 0; j < r0; j++) a = gmul(a, yy ^ pts[R0[j]]);
    for (int j = 0; j < r1; j++) b = gmul(b, yy ^ pts[R1[j]]);
    for (int j = 0; j < k; j++) if (j != i) b = gmul(b, yy ^ pts[R2[j]]);
    num[i] = a; den[i] = b;
  }
  u64 acc = 1; for (int i = 0; i < k; i++) { pre[i] = acc; acc = gmul(acc, den[i]); }
  u64 inv = ginv(acc);
  for (int i = k - 1; i >= 0; i--) { c[i] = gmul(num[i], gmul(inv, pre[i])); inv = gmul(inv, den[i]); }
  return hankel_zero(c, y, k, t);
}

// ---- analysis of a singular configuration: a generic solution, reduced xi, deg, nu, |Pi| ----
static int pdeg(const u64 *a, int d) { while (d >= 0 && !a[d]) d--; return d; }
static u64 peval(const u64 *a, int d, u64 x) { u64 v = 0; for (int i = d; i >= 0; i--) v = gmul(v, x) ^ a[i]; return v; }
static int pmod(u64 *a, int da, const u64 *b, int db) {
  u64 inv = ginv(b[db]);
  for (int i = da; i >= db; i--) if (a[i]) { u64 f = gmul(a[i], inv); for (int j = 0; j <= db; j++) a[i - db + j] ^= gmul(f, b[j]); }
  return pdeg(a, db - 1);
}
static int pgcd(const u64 *a, int da, const u64 *b, int db, u64 *g) {
  u64 x[MAXD + 2], y[MAXD + 2], tmp[MAXD + 2]; memcpy(x, a, (da + 1) * 8); memcpy(y, b, (db + 1) * 8);
  while (db >= 0) { int dr = pmod(x, da, y, db); memcpy(tmp, x, (dr + 1) * 8); memcpy(x, y, (db + 1) * 8); da = db; memcpy(y, tmp, (dr + 1) * 8); db = dr; }
  memcpy(g, x, (da + 1) * 8); return da;
}
static int pdivexact(const u64 *a, int da, const u64 *b, int db, u64 *q) {
  u64 x[MAXD + 2]; memcpy(x, a, (da + 1) * 8); u64 inv = ginv(b[db]);
  for (int i = da; i >= db; i--) { u64 f = gmul(x[i], inv); q[i - db] = f; if (f) for (int j = 0; j <= db; j++) x[i - db + j] ^= gmul(f, b[j]); }
  return da - db;
}
typedef struct { int deg, nu, npi, dimV, degenerate, msum, q; } Info;
static int pmult(const u64 *a, int da, u64 x) { u64 t[MAXD + 2]; memcpy(t, a, (da + 1) * 8); int m = 0; while (da >= 0) { u64 v = 0; for (int i = da; i >= 0; i--) v = gmul(v, x) ^ t[i]; if (v) break; u64 carry = 0; for (int i = da; i >= 0; i--) { u64 cur = t[i] ^ gmul(carry, x); t[i] = carry; carry = cur; } da--; m++; } return m; }
static Info analyse(const int *A[3], const int r[3], int delta) {
  Info inf = {0, 0, 0, 0, 0, 0, 1};
  int rows = 0, own[MAXD + 4], sh[MAXD + 4]; static u64 M[MAXD + 4][MAXD + 2], C[MAXD + 4][MAXD + 4];
  u64 Z[3][MAXD + 2];
  for (int i = 0; i < 3; i++) {
    memset(Z[i], 0, sizeof Z[i]); Z[i][0] = 1; int d = 0;
    for (int p = 0; p < r[i]; p++) { u64 v = pts[A[i][p]]; for (int j = d + 1; j >= 1; j--) Z[i][j] = Z[i][j - 1] ^ gmul(Z[i][j], v); Z[i][0] = gmul(Z[i][0], v); d++; }
    for (int j = 0; j <= delta - r[i]; j++) { own[rows] = i; sh[rows] = j; for (int c = 0; c <= delta; c++) M[rows][c] = (c >= j && c - j <= r[i]) ? Z[i][c - j] : 0; rows++; }
  }
  for (int i = 0; i < rows; i++) for (int j = 0; j < rows; j++) C[i][j] = (i == j);
  int used[MAXD + 4] = {0}, piv_of_col[MAXD + 2];
  for (int c = 0; c <= delta; c++) {
    int p = -1; for (int i = 0; i < rows; i++) if (!used[i] && M[i][c]) { p = i; break; }
    piv_of_col[c] = p; if (p < 0) continue; used[p] = 1; u64 inv = ginv(M[p][c]);
    for (int i = 0; i < rows; i++) if (i != p && M[i][c]) { u64 f = gmul(M[i][c], inv); for (int j = 0; j <= delta; j++) M[i][j] ^= gmul(f, M[p][j]); for (int j = 0; j < rows; j++) C[i][j] ^= gmul(f, C[p][j]); }
  }
  u64 h[3][MAXD + 2]; memset(h, 0, sizeof h);
  for (int i = 0; i < rows; i++) if (!used[i]) { inf.dimV++; u64 w = rnd() | 1; for (int j = 0; j < rows; j++) h[own[j]][sh[j]] ^= gmul(w, C[i][j]); }
  if (!inf.dimV) return inf;
  u64 u[3][MAXD + 2]; int du[3];
  for (int i = 0; i < 3; i++) { memset(u[i], 0, sizeof u[i]); for (int a = 0; a <= delta - r[i]; a++) if (h[i][a]) for (int b = 0; b <= r[i]; b++) u[i][a + b] ^= gmul(h[i][a], Z[i][b]); du[i] = pdeg(u[i], delta); }
  if (du[0] < 0 || du[1] < 0 || du[2] < 0) { inf.degenerate = 1; return inf; }
  u64 g[MAXD + 2], a[MAXD + 2], b[MAXD + 2], c[MAXD + 2]; int dg = pgcd(u[0], du[0], u[1], du[1], g);
  int da = pdivexact(u[0], du[0], g, dg, a), db = pdivexact(u[1], du[1], g, dg, b); int dm = da > db ? da : db;
  for (int i = 0; i <= dm; i++) c[i] = (i <= da ? a[i] : 0) ^ (i <= db ? b[i] : 0);
  int dc = pdeg(c, dm); inf.deg = dm;
  for (int p = 0; p < n; p++) if (!peval(a, da, pts[p]) || !peval(b, db, pts[p]) || !peval(c, dc, pts[p])) inf.nu++;
  for (int p = 0; p < n; p++) inf.msum += pmult(a, da, pts[p]) + pmult(b, db, pts[p]) + pmult(c, dc, pts[p]);
  for (;;) { int ok = 1, q2 = 2 * inf.q; for (int i = 0; i <= da; i++) if (a[i] && i % q2) ok = 0; for (int i = 0; i <= db; i++) if (b[i] && i % q2) ok = 0; if (!ok || q2 > dm) break; inf.q = q2; }
  for (int s = 0; s < n; s++) { int ok = 1; for (int tr = 0; tr < 2 * dm + 3 && ok; tr++) { u64 yv = rnd(); if (gmul(peval(a, da, yv ^ pts[s]), peval(b, db, yv)) != gmul(peval(a, da, yv), peval(b, db, yv ^ pts[s]))) ok = 0; } inf.npi += ok; }
  return inf;
}
#define HN 64
static long hist[HN][3 * HN][HN]; static long nviol, nsing, ntot, ndegen;
static void record(const int *A[3], const int r[3], int delta, int verbose) {
  Info f = analyse(A, r, delta); nsing++;
  if (f.degenerate || !f.dimV) { ndegen++; return; }
  if (f.deg < HN && f.npi < HN) hist[f.deg][f.nu][f.npi]++;
  int bad = f.nu > 2 * f.deg + f.npi;
  if (bad) nviol++;
  if (bad || verbose) {
    printf("%s delta=%d dimV=%d deg=%d nu=%d |Pi|=%d sets:", bad ? "VIOLATION" : "singular", delta, f.dimV, f.deg, f.nu, f.npi);
    for (int i = 0; i < 3; i++) { printf(" {"); for (int j = 0; j < r[i]; j++) printf("%d%s", A[i][j], j + 1 < r[i] ? "," : ""); printf("}"); }
    printf("\n"); fflush(stdout);
  }
}
static void report(void) {
  printf("configurations %ld, singular %ld (degenerate %ld), violations of P %ld\n", ntot, nsing, ndegen, nviol);
  for (int d = 0; d < HN; d++) for (int v = 0; v < 3 * HN; v++) for (int p = 0; p < HN; p++) if (hist[d][v][p]) printf("  (deg, nu, |Pi|) = (%d, %d, %d): %ld\n", d, v, p, hist[d][v][p]);
}

// ---- mode all: N <= 4, every unordered triple ----
static void mode_all(int delta) {
  int nu = 2 * delta + 2; if (nu > n) { printf("2 delta + 2 > n\n"); return; }
  double tot = 0, sing = 0;
  for (unsigned R2 = 0; R2 < (1u << n); R2++) {
    int k = __builtin_popcount(R2); if (k < 2 || 3 * k > nu) continue;
    for (unsigned R1 = 0; R1 < (1u << n); R1++) {
      if (R1 & R2) continue; int r1 = __builtin_popcount(R1); int r0 = nu - k - r1;
      if (r1 < k || r0 < r1 || r0 > delta) continue;
      // R0: subsets of the rest of size r0
      unsigned rest = ((1u << n) - 1) & ~(R1 | R2);
      for (unsigned R0 = rest;; R0 = (R0 - 1) & rest) {
        if (__builtin_popcount(R0) == r0) {
          int l[3][16]; int r[3] = {0, 0, 0}; unsigned mk[3] = {R0, R1, R2};
          for (int i = 0; i < 3; i++) for (int p = 0; p < n; p++) if (mk[i] >> p & 1) l[i][r[i]++] = p;
          const int *A[3] = {l[0], l[1], l[2]};
          double wgt = (r0 == r1 && r1 == k) ? 1.0 / 6 : (r0 == r1 || r1 == k) ? 0.5 : 1.0;
          tot += wgt; ntot++;
          if (singular3(A, r, delta)) { sing += wgt; record(A, r, delta, 0); }
        }
        if (!R0) break;
      }
    }
  }
  printf("N=%d delta=%d: unordered configurations %.0f, singular %.0f\n", NN, delta, tot, sing); report();
}

// ---- orbit representatives of k-subsets of AG(5,2) ----
static unsigned canon5(unsigned S) {
  int p[32], k = 0; for (int x = 0; x < 32; x++) if (S >> x & 1) p[k++] = x;
  // affine dimension
  int d = 0; { unsigned basis[5]; for (int i = 1; i < k; i++) { unsigned v = p[i] ^ p[0]; for (int j = 0; j < d; j++) if ((v ^ basis[j]) < v) v ^= basis[j]; if (v) { basis[d++] = v; } } }
  static const int perm5[120][5] = {{0}}; static int perms[6][120][5], np[6], init = 0;
  (void)perm5;
  if (!init) { init = 1; for (int dd = 1; dd <= 5; dd++) { int a[5]; for (int i = 0; i < dd; i++) a[i] = i; np[dd] = 0;
      for (;;) { memcpy(perms[dd][np[dd]++], a, sizeof a); int i = dd - 2; while (i >= 0 && a[i] > a[i + 1]) i--; if (i < 0) break; int j = dd - 1; while (a[j] < a[i]) j--; int x = a[i]; a[i] = a[j]; a[j] = x; for (int l = i + 1, rr = dd - 1; l < rr; l++, rr--) { x = a[l]; a[l] = a[rr]; a[rr] = x; } } } }
  unsigned best = ~0u;
  int idx[5];
  for (int i0 = 0; i0 < k; i0++) {
    // choose d-subsets of the other points
    int others[32], m = 0; for (int i = 0; i < k; i++) if (i != i0) others[m++] = p[i] ^ p[i0];
    for (int i = 0; i < d; i++) idx[i] = i;
    for (;;) {
      signed char inv[32]; memset(inv, -1, sizeof inv); int ok = 1;
      for (int cc = 0; cc < (1 << d) && ok; cc++) { int v = 0; for (int j = 0; j < d; j++) if (cc >> j & 1) v ^= others[idx[j]]; if (inv[v] >= 0) ok = 0; else inv[v] = (signed char)cc; }
      if (ok) {
        int co[32]; for (int i = 0; i < k; i++) co[i] = inv[p[i] ^ p[i0]];
        for (int q = 0; q < np[d]; q++) {
          unsigned im = 0; const int *pp = perms[d][q];
          for (int i = 0; i < k; i++) { int cv = co[i], w = 0; for (int j = 0; j < d; j++) if (cv >> j & 1) w |= 1 << pp[j]; im |= 1u << w; }
          if (im < best) best = im;
        }
      }
      int i = d - 1; while (i >= 0 && idx[i] == m - d + i) i--; if (i < 0) break; idx[i]++; for (int j = i + 1; j < d; j++) idx[j] = idx[j - 1] + 1;
    }
  }
  return best;
}
static int cmpu(const void *a, const void *b) { unsigned x = *(const unsigned *)a, y = *(const unsigned *)b; return x < y ? -1 : x > y; }
static int orbit_reps(int k, unsigned *out) {
  int cnt = 0; static unsigned buf[20000];
  for (int d = 1; d <= 5; d++) {
    int extra = k - d - 1; if (extra < 0) continue;
    unsigned frame = 1u; for (int i = 0; i < d; i++) frame |= 1u << (1 << i);
    int cand[32], m = 0; for (int x = 0; x < (1 << d); x++) if (!(frame >> x & 1)) cand[m++] = x;
    if (extra > m) continue;
    int idx[32]; for (int i = 0; i < extra; i++) idx[i] = i;
    for (;;) {
      unsigned S = frame; for (int i = 0; i < extra; i++) S |= 1u << cand[idx[i]];
      buf[cnt++] = canon5(S);
      int i = extra - 1; while (i >= 0 && idx[i] == m - extra + i) i--; if (i < 0) break; idx[i]++; for (int j = i + 1; j < extra; j++) idx[j] = idx[j - 1] + 1;
    }
  }
  qsort(buf, cnt, sizeof(unsigned), cmpu); int o = 0;
  for (int i = 0; i < cnt; i++) if (!i || buf[i] != buf[i - 1]) out[o++] = buf[i];
  return o;
}

// ---- mode dense: N = 5, delta = 15, R = D ----
static u64 d_inv[16][32], d_c0[16], d_y[16], d_zi[33][16];
static int d_k, d_m, d_xs[32], d_r1, d_t, d_force0; static unsigned d_R2;
static void d_leaf(unsigned R1) {
  u64 c[10]; const u64 *z = d_zi[d_r1];
  for (int i = 0; i < d_k; i++) c[i] = gmul(d_c0[i], gmul(z[i], z[i]));
  ntot++;
  if (hankel_zero(c, d_y, d_k, d_t)) {
    int l[3][32]; int r[3] = {0, 0, 0}; unsigned mk[3] = {~(R1 | d_R2), R1, d_R2};
    for (int i = 0; i < 3; i++) for (int p = 0; p < 32; p++) if (mk[i] >> p & 1) l[i][r[i]++] = p;
    const int *A[3] = {l[0], l[1], l[2]}; record(A, r, 15, 1);
  }
}
static void d_dfs(int pos, int chosen, unsigned R1) {
  if (chosen == d_r1) { d_leaf(R1); return; }
  if (d_m - pos < d_r1 - chosen) return;
  // take xs[pos]
  if (!(pos == 0 && d_force0)) { for (int i = 0; i < d_k; i++) d_zi[chosen + 1][i] = gmul(d_zi[chosen][i], d_inv[i][pos]); d_dfs(pos + 1, chosen + 1, R1 | 1u << d_xs[pos]); }
  d_dfs(pos + 1, chosen, R1);
}
static void mode_dense(int part, int parts) {
  const int delta = 15; long job = 0;
  for (int k = 2; k <= 10; k++) {
    static unsigned reps[20000]; int nr = orbit_reps(k, reps);
    long before = ntot;
    for (int ri = 0; ri < nr; ri++) {
      for (int r1 = k; 2 * r1 <= 32 - k; r1++) {
        int r0 = 32 - k - r1; if (r0 > delta) continue;
        if (job++ % parts != part) continue;
        d_R2 = reps[ri]; d_k = k; d_m = 0; d_r1 = r1; d_t = delta - r0 + 1; d_force0 = (r0 == r1);
        int ys[10], q = 0; for (int x = 0; x < 32; x++) { if (d_R2 >> x & 1) ys[q++] = x; else d_xs[d_m++] = x; }
        for (int i = 0; i < k; i++) {
          u64 yy = pts[ys[i]], a = 1, b = 1; d_y[i] = yy;
          for (int j = 0; j < d_m; j++) { a = gmul(a, yy ^ pts[d_xs[j]]); d_inv[i][j] = ginv(yy ^ pts[d_xs[j]]); }
          for (int j = 0; j < k; j++) if (j != i) b = gmul(b, yy ^ pts[ys[j]]);
          d_c0[i] = gmul(a, ginv(b)); d_zi[0][i] = 1;
        }
        d_dfs(0, 0, 0);
      }
    }
    printf("smallest set %d: %d orbit representatives, %ld configurations in this part\n", k, nr, ntot - before); fflush(stdout);
  }
  report();
}

// ---- mode small: 2 delta + 2 points spanning F_2^N, all colourings ----
static void mode_small(int delta) {
  int nu = 2 * delta + 2, extra = nu - NN - 1; if (extra < 0 || nu > n) { printf("no such configuration\n"); return; }
  int P[MAXP]; P[0] = 0; for (int i = 0; i < NN; i++) P[1 + i] = 1 << i;
  int cand[MAXP], m = 0; for (int x = 1; x < n; x++) if (x & (x - 1)) cand[m++] = x;
  if (extra > m) { printf("no such configuration\n"); return; }
  int idx[MAXP]; for (int i = 0; i < extra; i++) idx[i] = i;
  long nsets = 0; int col[MAXP];
  for (;;) {
    for (int i = 0; i < extra; i++) P[NN + 1 + i] = cand[idx[i]];
    nsets++;
    // colourings: col[0] = 0, first colour different from 0 is 1
    long total = 1; for (int i = 1; i < nu; i++) total *= 3;
    for (long code = 0; code < total; code++) {
      long cc = code; int r[3] = {1, 0, 0}, l[3][MAXP], seen1 = 0, ok = 1; l[0][0] = P[0]; col[0] = 0;
      for (int i = 1; i < nu && ok; i++) { int c = cc % 3; cc /= 3; if (c == 2 && !seen1) ok = 0; if (c == 1) seen1 = 1; l[c][r[c]++] = P[i]; if (r[c] > delta) ok = 0; }
      if (!ok || r[1] < 2 || r[2] < 2 || r[0] < 2) continue;
      const int *A[3] = {l[0], l[1], l[2]}; ntot++;
      if (singular3(A, r, delta)) record(A, r, delta, 0);
    }
    int i = extra - 1; while (i >= 0 && idx[i] == m - extra + i) i--; if (i < 0) break; idx[i]++; for (int j = i + 1; j < extra; j++) idx[j] = idx[j - 1] + 1;
  }
  printf("N=%d delta=%d: %ld point sets with the frame, ", NN, delta, nsets); report();
}

// ---- mode sym ----
static void mode_sym(int mode, int npoly, char **polys) {
  // block companion matrix acting on column vectors: image of e_j
  int img[8], off = 0;
  for (int q = 0; q < npoly; q++) {
    unsigned f = (unsigned)strtoul(polys[q], 0, 0); int d = 31 - __builtin_clz(f);
    for (int j = 0; j < d; j++) { if (j + 1 < d) img[off + j] = 1 << (off + j + 1); else { int v = 0; for (int i = 0; i < d; i++) if (f >> i & 1) v |= 1 << (off + i); img[off + j] = v; } }
    off += d;
  }
  if (off != NN) { printf("degrees sum to %d, not N\n", off); return; }
  int g[MAXP]; for (int x = 0; x < n; x++) { int v = 0; for (int j = 0; j < NN; j++) if (x >> j & 1) v ^= img[j]; g[x] = v; }
  int orb[MAXP], norb = 0, start[MAXP], len[MAXP]; memset(orb, -1, sizeof orb);
  for (int x = 0; x < n; x++) if (orb[x] < 0) { int y = x, l = 0; do { orb[y] = norb; y = g[y]; l++; } while (y != x); start[norb] = x; len[norb] = l; norb++; }
  int use[MAXP], nuse = 0; for (int o = 0; o < norb; o++) if (mode == 0 || len[o] % 3 == 0) use[nuse++] = o;
  printf("N=%d, %d orbits (", NN, norb); for (int o = 0; o < norb; o++) printf("%d%s", len[o], o + 1 < norb ? "," : ""); printf("), %d usable, mode %d\n", nuse, mode);
  double total = 1; for (int i = 0; i < nuse; i++) total *= 4;
  long lim = total > 3e8 ? 300000000L : (long)total; int sample = total > 3e8;
  if (sample) printf("too many colourings (%.3g): sampling %ld at random\n", total, lim);
  for (long it = 0; it < lim; it++) {
    u64 code = sample ? rnd() : (u64)it; int r[3] = {0, 0, 0}; static int l[3][MAXP]; int first = 1, okc = 1;
    for (int i = 0; i < nuse && okc; i++) {
      int c = (int)(code >> (2 * i) & 3); if (c == 3) continue; // 3 = unused
      if (!sample && first && c != 0) { okc = 0; break; }
      first = 0; int y = start[use[i]];
      for (int j = 0; j < len[use[i]]; j++) { int cj = mode ? (c + j) % 3 : c; l[cj][r[cj]++] = y; y = g[y]; }
    }
    if (!okc) continue;
    int nu = r[0] + r[1] + r[2]; if (nu < 6 || (nu & 1)) continue; int delta = nu / 2 - 1;
    if (r[0] > delta || r[1] > delta || r[2] > delta || r[0] < 1 || r[1] < 1 || r[2] < 1 || delta >= MAXD - 2) continue;
    const int *A[3] = {l[0], l[1], l[2]}; ntot++;
    if (singular3(A, r, delta)) record(A, r, delta, 0);
  }
  report();
}

// ---- mode dense2: N = 5, u unused points, delta = (32 - u)/2 - 1, every configuration of 32 - u points ----
// Orbit representatives of pairs (U, S) under AGL(5,2): the minimum, over affine frames made of a frame of U (from U)
// completed by points of S, of the image pair.
static int q_U[32], q_nu, q_S[32], q_ns, q_dU, q_d; static u64 q_best;
static void q_rec(int depth, int p0, unsigned span, int *vec) {
  if (depth == q_d) {
    signed char inv[32]; for (int c = 0; c < (1 << q_d); c++) inv[vec[c]] = (signed char)c;
    unsigned iu = 0, is = 0;
    for (int i = 0; i < q_nu; i++) iu |= 1u << inv[q_U[i] ^ p0];
    for (int i = 0; i < q_ns; i++) is |= 1u << inv[q_S[i] ^ p0];
    u64 v = (u64)iu << 32 | is; if (v < q_best) q_best = v; return;
  }
  const int *src = depth < q_dU ? q_U : q_S; int cnt = depth < q_dU ? q_nu : q_ns;
  for (int i = 0; i < cnt; i++) {
    int v = src[i] ^ p0; if (span >> v & 1) continue;
    unsigned sp = span; for (int c = 0; c < (1 << depth); c++) { vec[c | 1 << depth] = vec[c] ^ v; sp |= 1u << (vec[c] ^ v); }
    q_rec(depth + 1, p0, sp, vec);
  }
}
static int affdim(const int *p, int k) { int d = 0; unsigned basis[5]; for (int i = 1; i < k; i++) { unsigned v = p[i] ^ p[0]; for (int j = 0; j < d; j++) if ((v ^ basis[j]) < v) v ^= basis[j]; if (v) basis[d++] = v; } return d; }
static u64 canon_pair(unsigned U, unsigned S) {
  q_nu = q_ns = 0; int all[32], na = 0;
  for (int x = 0; x < 32; x++) { if (U >> x & 1) { q_U[q_nu++] = x; all[na++] = x; } }
  for (int x = 0; x < 32; x++) if (S >> x & 1) { q_S[q_ns++] = x; all[na++] = x; }
  q_dU = q_nu ? affdim(q_U, q_nu) : 0; q_d = affdim(all, na); q_best = ~0ull;
  int vec[32];
  if (q_nu) { for (int i = 0; i < q_nu; i++) { vec[0] = 0; q_rec(0, q_U[i], 1u, vec); } }
  else { for (int i = 0; i < q_ns; i++) { vec[0] = 0; q_rec(0, q_S[i], 1u, vec); } }
  return q_best;
}
static int cmpu64(const void *a, const void *b) { u64 x = *(const u64 *)a, y = *(const u64 *)b; return x < y ? -1 : x > y; }
// representatives S (k-subsets of the complement of U) under the stabiliser of U; U is a canon5 representative
static long pair_reps(unsigned U, int k, unsigned **out) {
  int pu[32], nu_ = 0; for (int x = 0; x < 32; x++) if (U >> x & 1) pu[nu_++] = x;
  int dU = nu_ ? affdim(pu, nu_) : 0; long cap = 1 << 16, cnt = 0; u64 *buf = malloc(cap * sizeof(u64));
  for (int d = dU; d <= 5; d++) {
    if (nu_ == 0 && d == 0) continue;
    unsigned forced = 0; for (int i = dU; i < d; i++) forced |= 1u << (1 << i);
    if (nu_ == 0) forced |= 1u; // no U: the frame is 0, e_1..e_d inside S
    if (forced & U) continue;
    int extra = k - __builtin_popcount(forced); if (extra < 0) continue;
    int cand[32], m = 0; for (int x = 0; x < (1 << d); x++) if (!((U | forced) >> x & 1)) cand[m++] = x;
    if (extra > m) continue;
    int idx[32]; for (int i = 0; i < extra; i++) idx[i] = i;
    for (;;) {
      unsigned S = forced; for (int i = 0; i < extra; i++) S |= 1u << cand[idx[i]];
      if (cnt == cap) { cap *= 2; buf = realloc(buf, cap * sizeof(u64)); }
      buf[cnt++] = canon_pair(U, S);
      int i = extra - 1; while (i >= 0 && idx[i] == m - extra + i) i--; if (i < 0) break; idx[i]++; for (int j = i + 1; j < extra; j++) idx[j] = idx[j - 1] + 1;
    }
  }
  qsort(buf, cnt, sizeof(u64), cmpu64); long o = 0; unsigned *res = malloc((cnt + 1) * sizeof(unsigned));
  for (long i = 0; i < cnt; i++) if (!i || buf[i] != buf[i - 1]) { if ((unsigned)(buf[i] >> 32) != U && nu_) { fprintf(stderr, "canonical U mismatch\n"); exit(1); } res[o++] = (unsigned)buf[i]; }
  free(buf); *out = res; return o;
}
static int d_delta;
static void d_leaf2(unsigned R1, unsigned U) {
  u64 c[16]; const u64 *z = d_zi[d_r1];
  for (int i = 0; i < d_k; i++) c[i] = gmul(d_c0[i], gmul(z[i], z[i]));
  ntot++;
  if (hankel_zero(c, d_y, d_k, d_t)) {
    int l[3][32]; int r[3] = {0, 0, 0}; unsigned mk[3] = {~(R1 | d_R2 | U), R1, d_R2};
    for (int i = 0; i < 3; i++) for (int p = 0; p < 32; p++) if (mk[i] >> p & 1) l[i][r[i]++] = p;
    const int *A[3] = {l[0], l[1], l[2]}; record(A, r, d_delta, 1);
  }
}
static unsigned d_U;
static void d_dfs2(int pos, int chosen, unsigned R1) {
  if (chosen == d_r1) { d_leaf2(R1, d_U); return; }
  if (d_m - pos < d_r1 - chosen) return;
  if (!(pos == 0 && d_force0)) { for (int i = 0; i < d_k; i++) d_zi[chosen + 1][i] = gmul(d_zi[chosen][i], d_inv[i][pos]); d_dfs2(pos + 1, chosen + 1, R1 | 1u << d_xs[pos]); }
  d_dfs2(pos + 1, chosen, R1);
}
static void mode_dense2(int u, int part, int parts, int kmin, int kmax) {
  int nu = 32 - u, delta = nu / 2 - 1; d_delta = delta; long job = 0;
  static unsigned ureps[20000]; int nur = 1; ureps[0] = 0; if (u) nur = orbit_reps(u, ureps);
  printf("u=%d delta=%d: %d orbits of unused sets\n", u, delta, nur);
  for (int k = kmin; k <= kmax && 3 * k <= nu; k++) {
    long before = ntot, nreps = 0;
    for (int ui = 0; ui < nur; ui++) {
      unsigned U = ureps[ui], *reps; long nr = pair_reps(U, k, &reps); nreps += nr; d_U = U;
      for (long ri = 0; ri < nr; ri++) {
        for (int r1 = k; 2 * r1 <= nu - k; r1++) {
          int r0 = nu - k - r1; if (r0 > delta) continue;
          if (job++ % parts != part) continue;
          d_R2 = reps[ri]; d_k = k; d_m = 0; d_r1 = r1; d_t = delta - r0 + 1; d_force0 = (r0 == r1);
          int ys[16], q = 0; for (int x = 0; x < 32; x++) { if (d_R2 >> x & 1) ys[q++] = x; else if (!(U >> x & 1)) d_xs[d_m++] = x; }
          for (int i = 0; i < k; i++) {
            u64 yy = pts[ys[i]], a = 1, b = 1; d_y[i] = yy;
            for (int j = 0; j < d_m; j++) { a = gmul(a, yy ^ pts[d_xs[j]]); d_inv[i][j] = ginv(yy ^ pts[d_xs[j]]); }
            for (int j = 0; j < k; j++) if (j != i) b = gmul(b, yy ^ pts[ys[j]]);
            d_c0[i] = gmul(a, ginv(b)); d_zi[0][i] = 1;
          }
          d_dfs2(0, 0, 0);
        }
      }
      free(reps);
    }
    printf("smallest set %d: %ld orbit representatives (U, R2), %ld configurations in this part\n", k, nreps, ntot - before); fflush(stdout);
  }
  report();
}

// ---- mode mult: patterns with multiplicities, sum = 2 delta + 2, each colour at most delta ----
static int m_delta, m_cnt[3], m_list[3][MAXD + 2]; static long m_tot, m_sing, m_viol, m_h[HN][2 * HN][HN][9];
static void m_rec(int p, int left) {
  if (left == 0) {
    if (m_cnt[0] < 1 || m_cnt[1] < 1 || m_cnt[2] < 1) return;
    // canonical colour order: skip relabelled copies
    if (m_list[0][0] > m_list[1][0] || m_list[1][0] > m_list[2][0]) return;
    const int *A[3] = {m_list[0], m_list[1], m_list[2]}; m_tot++;
    Info f = analyse(A, m_cnt, m_delta); if (!f.dimV) return;
    m_sing++; if (f.degenerate) return;
    int ql = 0; while ((1 << ql) < f.q) ql++;
    if (f.deg < HN && f.msum < 2 * HN && f.npi < HN) m_h[f.deg][f.msum][f.npi][ql]++;
    if (f.msum > 2 * f.deg + f.q * f.npi) { m_viol++; printf("VIOLATION of P_mult: delta=%d deg=%d msum=%d |Pi|=%d q=%d\n", m_delta, f.deg, f.msum, f.npi, f.q); }
    return;
  }
  if (p == n) return;
  m_rec(p + 1, left);
  for (int c = 0; c < 3; c++) for (int m = 1; m <= left && m_cnt[c] + m <= m_delta; m++) {
    for (int j = 0; j < m; j++) m_list[c][m_cnt[c] + j] = p;
    m_cnt[c] += m; m_rec(p + 1, left - m); m_cnt[c] -= m;
  }
}
static void mode_mult(int delta) {
  m_delta = delta; m_rec(0, 2 * delta + 2);
  printf("N=%d delta=%d: multiplicity patterns %ld, with a solution %ld, violations of sum mult <= 2 deg + q |Pi|: %ld\n", NN, delta, m_tot, m_sing, m_viol);
  for (int d = 0; d < HN; d++) for (int v = 0; v < 2 * HN; v++) for (int p = 0; p < HN; p++) for (int q = 0; q < 9; q++) if (m_h[d][v][p][q]) printf("  (deg, sum mult, |Pi|, q) = (%d, %d, %d, %d): %ld\n", d, v, p, 1 << q, m_h[d][v][p][q]);
}

int main(int argc, char **argv) {
  if (argc < 2) return 1;
  gf_init(64, 0x1b);
  if (!strcmp(argv[1], "all")) { init_pts(atoi(argv[2]), argc > 4 ? strtoull(argv[4], 0, 0) : 0); mode_all(atoi(argv[3])); }
  else if (!strcmp(argv[1], "dense")) { init_pts(5, argc > 4 ? strtoull(argv[4], 0, 0) : 0); mode_dense(atoi(argv[2]), atoi(argv[3])); }
  else if (!strcmp(argv[1], "small")) { init_pts(atoi(argv[3]), argc > 4 ? strtoull(argv[4], 0, 0) : 0); mode_small(atoi(argv[2])); }
  else if (!strcmp(argv[1], "sym")) { init_pts(atoi(argv[2]), strtoull(argv[4], 0, 0)); mode_sym(atoi(argv[3]), argc - 5, argv + 5); }
  else if (!strcmp(argv[1], "dense2")) { init_pts(5, argc > 7 ? strtoull(argv[7], 0, 0) : 0); mode_dense2(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), argc > 5 ? atoi(argv[5]) : 2, argc > 6 ? atoi(argv[6]) : 10); }
  else if (!strcmp(argv[1], "densetest")) { // positive control for the incremental path: three cosets of an 8-element subspace, delta = 11
    init_pts(5, 0); d_delta = 11; d_U = 0xFFu; d_R2 = 0xFF00u; d_k = 8; d_m = 0; d_r1 = 8; d_t = 11 - 8 + 1; d_force0 = 1;
    int ys[16], q = 0; for (int x = 0; x < 32; x++) { if (d_R2 >> x & 1) ys[q++] = x; else if (!(d_U >> x & 1)) d_xs[d_m++] = x; }
    for (int i = 0; i < 8; i++) { u64 yy = pts[ys[i]], a = 1, b = 1; d_y[i] = yy;
      for (int j = 0; j < d_m; j++) { a = gmul(a, yy ^ pts[d_xs[j]]); d_inv[i][j] = ginv(yy ^ pts[d_xs[j]]); }
      for (int j = 0; j < 8; j++) if (j != i) b = gmul(b, yy ^ pts[ys[j]]);
      d_c0[i] = gmul(a, ginv(b)); d_zi[0][i] = 1; }
    d_dfs2(0, 0, 0); report(); }
  else if (!strcmp(argv[1], "pairreps")) { int u = atoi(argv[2]); static unsigned ur[20000]; int nur = 1; ur[0] = 0; if (u) nur = orbit_reps(u, ur); for (int k = 2; 3 * k <= 32 - u; k++) { long t = 0; for (int i = 0; i < nur; i++) { unsigned *r; t += pair_reps(ur[i], k, &r); free(r); } printf("u=%d k=%d: %ld orbits\n", u, k, t); fflush(stdout); } }
  else if (!strcmp(argv[1], "mult")) { init_pts(atoi(argv[2]), argc > 4 ? strtoull(argv[4], 0, 0) : 0); mode_mult(atoi(argv[3])); }
  else if (!strcmp(argv[1], "reps")) { for (int k = 2; k <= 10; k++) { static unsigned reps[20000]; printf("k=%d: %d orbits\n", k, orbit_reps(k, reps)); } }
  return 0;
}
