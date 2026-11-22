// 17_fibers: the three-fibre problem on a 16-point (or 8-point) generic subspace domain, exhaustively.
//
//   cc -O2 -o 17_fibers 17_fibers.c
//   ./17_fibers N delta [seed] [dump]        N = 3 or 4
//
// For a rational function xi over a field containing the domain D (a random N-dimensional F_2-subspace of GF(2^64)),
// nu(xi) = #{x in D : xi(x) in {0, 1, infinity}} and Pi(xi) = {a in D : xi(X + a) = xi(X)}. On generic POINTS
// nu <= 2 deg(xi) + 1 by counting. The program enumerates all triples (R0, R1, R2) of pairwise disjoint subsets of D
// with |Ri| <= delta and |R0| + |R1| + |R2| = 2 delta + 2, decides by rank whether there are polynomials
// u0 + u1 + u2 = 0, deg <= delta, Z_{Ri} | ui, not all zero, and for each solution computes the reduced xi = u0/u1,
// its degree, nu(xi) and |Pi(xi)|. Every xi of degree <= delta with nu(xi) >= 2 delta + 2 arises this way.
// Output: a histogram over (deg xi, nu, |Pi|) and the number of violations of nu <= 2 deg + |Pi|.
#include "02_gf.h"
#define MAXN 32
static int NN, n, delta;
static u64 pts[MAXN];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int pc(unsigned x) { return __builtin_popcount(x); }

static int pdeg(const u64 *a, int d) { while (d >= 0 && !a[d]) d--; return d; }
static u64 peval(const u64 *a, int d, u64 x) { u64 v = 0; for (int i = d; i >= 0; i--) v = gmul(v, x) ^ a[i]; return v; }
// remainder of a mod b in place, returns degree
static int pmod(u64 *a, int da, const u64 *b, int db) {
  u64 inv = ginv(b[db]);
  for (int i = da; i >= db; i--) if (a[i]) { u64 f = gmul(a[i], inv); for (int j = 0; j <= db; j++) a[i - db + j] ^= gmul(f, b[j]); }
  return pdeg(a, db - 1);
}
static int pgcd(const u64 *a, int da, const u64 *b, int db, u64 *g) {
  u64 x[40], y[40]; memcpy(x, a, (da + 1) * sizeof(u64)); memcpy(y, b, (db + 1) * sizeof(u64));
  while (db >= 0) { int dr = pmod(x, da, y, db); u64 tmp[40]; memcpy(tmp, x, (dr + 1) * sizeof(u64)); memcpy(x, y, (db + 1) * sizeof(u64)); da = db; memcpy(y, tmp, (dr + 1) * sizeof(u64)); db = dr; }
  memcpy(g, x, (da + 1) * sizeof(u64)); return da;
}
static int pdivexact(u64 *a, int da, const u64 *b, int db, u64 *q) { // q = a / b
  u64 x[40]; memcpy(x, a, (da + 1) * sizeof(u64)); u64 inv = ginv(b[db]);
  for (int i = da; i >= db; i--) { u64 f = gmul(x[i], inv); q[i - db] = f; if (f) for (int j = 0; j <= db; j++) x[i - db + j] ^= gmul(f, b[j]); }
  return da - db;
}
static void locator(unsigned R, u64 *z, int *dz) { z[0] = 1; int d = 0; for (int p = 0; p < n; p++) if (R >> p & 1) { z[d + 1] = 0; for (int j = d + 1; j >= 1; j--) z[j] = z[j - 1] ^ gmul(z[j], pts[p]); z[0] = gmul(z[0], pts[p]); d++; } *dz = d; }

static long hist[20][36][36]; // deg, nu, |Pi|
static long viol = 0, nsing = 0, ntot = 0, nbig = 0;
static int dump;

static void analyse(const u64 *u0, const u64 *u1, unsigned R0, unsigned R1, unsigned R2, int kd) {
  int d0 = pdeg(u0, delta), d1 = pdeg(u1, delta);
  if (d0 < 0 || d1 < 0) return; // degenerate: one of the three vanishes
  u64 u2[40]; for (int i = 0; i <= delta; i++) u2[i] = u0[i] ^ u1[i];
  if (pdeg(u2, delta) < 0) return;
  u64 g[40], a[40], b[40]; int dg = pgcd(u0, d0, u1, d1, g);
  int da = pdivexact((u64 *)u0, d0, g, dg, a), db = pdivexact((u64 *)u1, d1, g, dg, b);
  u64 c[40]; int dmax = da > db ? da : db; for (int i = 0; i <= dmax; i++) c[i] = (i <= da ? a[i] : 0) ^ (i <= db ? b[i] : 0);
  int dc = pdeg(c, dmax); int deg = dmax; // degree of xi = max(da, db) (dc <= that)
  int nu = 0; for (int p = 0; p < n; p++) { if (!peval(a, da, pts[p]) || !peval(b, db, pts[p]) || !peval(c, dc, pts[p])) nu++; }
  int npi = 0;
  for (int s = 0; s < n; s++) {
    int ok = 1;
    for (int trial = 0; trial < 2 * deg + 3 && ok; trial++) { u64 y = rnd(); if (gmul(peval(a, da, y ^ pts[s]), peval(b, db, y)) != gmul(peval(a, da, y), peval(b, db, y ^ pts[s]))) ok = 0; }
    npi += ok;
  }
  hist[deg][nu][npi]++;
  if (nu > 2 * deg + npi) { viol++; printf("VIOLATION deg=%d nu=%d pi=%d R=%04x %04x %04x ker=%d\n", deg, nu, npi, R0, R1, R2, kd); }
  if (dump) printf("  R=%04x %04x %04x ker=%d deg=%d nu=%d pi=%d common=%d\n", R0, R1, R2, kd, deg, nu, npi, dg);
}

static u64 A[20][60];
static u64 zc[3][40]; static int dzc[3]; static unsigned zcR[3] = {~0u, ~0u, ~0u};
// division-free test: is the square system singular? (only used when the number of unknowns equals delta + 1)
static int quick_nonsingular(unsigned R0, unsigned R1, unsigned R2) {
  unsigned Rs[3] = {R0, R1, R2}; int off[4]; off[0] = 0;
  for (int i = 0; i < 3; i++) { if (zcR[i] != Rs[i]) { locator(Rs[i], zc[i], &dzc[i]); zcR[i] = Rs[i]; } off[i + 1] = off[i] + (delta - dzc[i] + 1); }
  int m = delta + 1; if (off[3] != m) return 0;
  static u64 B[20][20];
  for (int r = 0; r < m; r++) for (int cc = 0; cc < m; cc++) B[r][cc] = 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j <= delta - dzc[i]; j++) for (int l = 0; l <= dzc[i]; l++) B[j + l][off[i] + j] = zc[i][l];
  for (int cc = 0; cc < m; cc++) {
    int r = cc; while (r < m && !B[r][cc]) r++;
    if (r == m) return 0;
    if (r != cc) for (int c2 = cc; c2 < m; c2++) { u64 tmp = B[r][c2]; B[r][c2] = B[cc][c2]; B[cc][c2] = tmp; }
    u64 P = B[cc][cc];
    for (int rr = cc + 1; rr < m; rr++) if (B[rr][cc]) { u64 f = B[rr][cc]; for (int c2 = cc + 1; c2 < m; c2++) B[rr][c2] = gmul(P, B[rr][c2]) ^ gmul(f, B[cc][c2]); B[rr][cc] = 0; }
  }
  return 1;
}
static void test(unsigned R0, unsigned R1, unsigned R2) {
  ntot++;
  if (quick_nonsingular(R0, R1, R2)) return;
  unsigned Rs[3] = {R0, R1, R2}; u64 z[3][40]; int dz[3], off[4]; off[0] = 0;
  for (int i = 0; i < 3; i++) { locator(Rs[i], z[i], &dz[i]); off[i + 1] = off[i] + (delta - dz[i] + 1); }
  int nc = off[3], nr = delta + 1; // unknowns: coefficients of h_i, deg h_i <= delta - |R_i|; equations: coefficients of sum h_i Z_i
  for (int r = 0; r < nr; r++) for (int cc = 0; cc < nc; cc++) A[r][cc] = 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j <= delta - dz[i]; j++) for (int l = 0; l <= dz[i]; l++) A[j + l][off[i] + j] = z[i][l];
  int piv[60], isp[60], rank = 0; memset(isp, 0, sizeof isp);
  for (int cc = 0; cc < nc && rank < nr; cc++) {
    int r = rank; while (r < nr && !A[r][cc]) r++;
    if (r == nr) continue;
    if (r != rank) for (int c2 = cc; c2 < nc; c2++) { u64 tmp = A[r][c2]; A[r][c2] = A[rank][c2]; A[rank][c2] = tmp; }
    u64 inv = ginv(A[rank][cc]);
    for (int c2 = cc; c2 < nc; c2++) A[rank][c2] = gmul(A[rank][c2], inv);
    for (int rr = 0; rr < nr; rr++) if (rr != rank && A[rr][cc]) { u64 f = A[rr][cc]; for (int c2 = cc; c2 < nc; c2++) A[rr][c2] ^= gmul(f, A[rank][c2]); }
    piv[rank] = cc; isp[cc] = 1; rank++;
  }
  int kd = nc - rank;
  if (kd == 0) return;
  nsing++; if (kd > 1) nbig++;
  int reps = kd == 1 ? 1 : 4;
  for (int rep = 0; rep < reps; rep++) {
    u64 x[60]; memset(x, 0, sizeof x);
    for (int cc = 0; cc < nc; cc++) if (!isp[cc]) x[cc] = rnd() | 1;
    for (int r = 0; r < rank; r++) { u64 s = 0; for (int cc = 0; cc < nc; cc++) if (!isp[cc] && A[r][cc]) s ^= gmul(A[r][cc], x[cc]); x[piv[r]] = s; }
    u64 u[2][40]; memset(u, 0, sizeof u);
    for (int i = 0; i < 2; i++) for (int j = 0; j <= delta - dz[i]; j++) for (int l = 0; l <= dz[i]; l++) u[i][j + l] ^= gmul(x[off[i] + j], z[i][l]);
    analyse(u[0], u[1], R0, R1, R2, kd);
  }
}

// enumerate R1 subset of avail with size r1 and min element constraints, then R2
static void subsets(unsigned avail, int r, unsigned minmask, void (*f)(unsigned, void *), void *ctx) {
  // iterate over all r-subsets of avail (as bitmask), using Gosper on compressed indices
  int idx[MAXN], m = 0; for (int p = 0; p < n; p++) if (avail >> p & 1) idx[m++] = p;
  if (r > m) return;
  if (r == 0) { f(0, ctx); return; }
  u64 c = (1ull << r) - 1, lim = 1ull << m;
  while (c < lim) { unsigned S = 0; for (int i = 0; i < m; i++) if (c >> i & 1) S |= 1u << idx[i]; f(S, ctx); u64 t = c | (c - 1); c = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzll(c) + 1)); }
  (void)minmask;
}
typedef struct { unsigned R0, R1; int r0, r1, r2; } ctx_t;
static void got_R2(unsigned R2, void *v) { ctx_t *c = v; if (c->r1 == c->r2 && R2 < c->R1) return; test(c->R0, c->R1, R2); }
static int useorb;
static void got_R1(unsigned R1, void *v) { ctx_t *c = v; if (!useorb && c->r0 == c->r1 && R1 < c->R0) return; c->R1 = R1; subsets((n == 32 ? ~0u : ((1u << n) - 1)) & ~c->R0 & ~R1, c->r2, 0, got_R2, c); }
static void got_R0(unsigned R0, void *v) { ctx_t *c = v; c->R0 = R0; subsets((n == 32 ? ~0u : ((1u << n) - 1)) & ~R0, c->r1, 0, got_R1, c); }

// orbit representatives of the r-subsets of F_2^NN under the affine group (generators: translations, transvections)
static unsigned *orep; static long norep;
static unsigned img(unsigned S, const int *perm) { unsigned r = 0; while (S) { int p = __builtin_ctz(S); S &= S - 1; r |= 1u << perm[p]; } return r; }
static void orbit_reps(int r) {
  int gens[40][MAXN], ng = 0;
  for (int i = 0; i < NN; i++) { for (int p = 0; p < n; p++) gens[ng][p] = p ^ (1 << i); ng++; }
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) if (i != j) { for (int p = 0; p < n; p++) gens[ng][p] = (p >> j & 1) ? p ^ (1 << i) : p; ng++; }
  size_t cap = 1; while (cap < 16000000) cap <<= 1; unsigned *tab = calloc(cap, sizeof(unsigned)); // 0 = empty (the empty set is never stored for r > 0)
  unsigned *stack = malloc(8000000 * sizeof(unsigned)); orep = malloc(4096 * sizeof(unsigned)); norep = 0;
  if (r == 0) { orep[norep++] = 0; return; }
  u64 c = (1ull << r) - 1, lim = 1ull << n;
  while (c < lim) {
    unsigned S = (unsigned)c; size_t h = (S * 2654435761u) & (cap - 1); int found = 0;
    while (tab[h]) { if (tab[h] == S) { found = 1; break; } h = (h + 1) & (cap - 1); }
    if (!found) {
      orep[norep++] = S; long sp = 0; stack[sp++] = S; tab[h] = S;
      while (sp) { unsigned U = stack[--sp]; for (int g = 0; g < ng; g++) { unsigned V = img(U, gens[g]); size_t hh = (V * 2654435761u) & (cap - 1); int f2 = 0; while (tab[hh]) { if (tab[hh] == V) { f2 = 1; break; } hh = (hh + 1) & (cap - 1); } if (!f2) { tab[hh] = V; stack[sp++] = V; } } }
    }
    u64 t = c | (c - 1); c = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzll(c) + 1));
  }
  free(tab); free(stack);
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 17_fibers N delta [seed] [dump | orb [part parts [r0 r1]]]\n"); return 1; }
  NN = atoi(argv[1]); n = 1 << NN; delta = atoi(argv[2]); if (argc > 3) rs ^= strtoull(argv[3], 0, 10) * 0x9e3779b97f4a7c15ull;
  dump = argc > 4 && !strcmp(argv[4], "dump"); useorb = argc > 4 && !strcmp(argv[4], "orb");
  int part = argc > 6 ? atoi(argv[5]) : 0, parts = argc > 6 ? atoi(argv[6]) : 1, only0 = argc > 8 ? atoi(argv[7]) : -1, only1 = argc > 8 ? atoi(argv[8]) : -1;
  gf_init(64, 0x1b);
  u64 b[8]; for (int i = 0; i < NN; i++) { for (int j = 0; j < 20; j++) rnd(); b[i] = rnd(); }
  for (int p = 0; p < n; p++) { pts[p] = 0; for (int i = 0; i < NN; i++) if (p >> i & 1) pts[p] ^= b[i]; }
  int nu = 2 * delta + 2; unsigned full = n == 32 ? ~0u : ((1u << n) - 1);
  printf("n=%d delta=%d: triples of disjoint sets with sizes <= delta and total %d%s\n", n, delta, nu, useorb ? " (R0 over orbit representatives of the affine group)" : "");
  if (nu > n) { printf("2 delta + 2 > n: nothing to test\n"); return 0; }
  for (int r0 = delta; r0 >= 0; r0--) for (int r1 = r0; r1 >= 0; r1--) { int r2 = nu - r0 - r1; if (r2 > r1 || r2 < 0) continue;
    if (only0 >= 0 && (r0 != only0 || r1 != only1)) continue;
    long s0 = nsing, t0 = ntot; ctx_t c = {0, 0, r0, r1, r2};
    if (!useorb) subsets(full, r0, 0, got_R0, &c);
    else { orbit_reps(r0); for (long o = 0; o < norep; o++) if (o % parts == part) got_R0(orep[o], &c); printf("  %ld orbits of %d-sets\n", norep, r0); free(orep); }
    printf("sizes (%d,%d,%d): %ld triples, %ld with a solution\n", r0, r1, r2, ntot - t0, nsing - s0); fflush(stdout); }
  printf("total %ld triples, %ld with a solution (%ld with solution space of dimension > 1), violations of nu <= 2 deg + |Pi|: %ld\n", ntot, nsing, nbig, viol);
  printf("histogram  deg  nu  |Pi|  count  (nu - 2 deg - 1):\n");
  for (int d = 0; d < 20; d++) for (int v = 0; v < 36; v++) for (int q = 0; q < 36; q++) if (hist[d][v][q]) printf("  %2d %3d %3d %10ld   excess %d\n", d, v, q, hist[d][v][q], v - 2 * d - 1);
  return 0;
}
