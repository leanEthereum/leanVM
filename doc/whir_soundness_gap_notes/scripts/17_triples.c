// 17_triples: all list triples of a Reed-Solomon code on a 16-point subspace domain, in the syndrome form.
//
//   cc -O2 -o 17_triples 17_triples.c
//   ./17_triples k T [seed] [dump]
//
// Domain: a random 4-dimensional F_2-subspace of GF(2^64) (the generic model of notes 02, 04, 12), n = 16.
// A member of a list at agreement T is an error vector supported on a set E of t = n - T points, and members of
// one list have the same syndrome (power sums p_0..p_{n-k-1}). The program enumerates all triples (E0, E1, E2) of
// t-sets with pairwise intersections <= d - 1, d = n + k - 2T, E0 over representatives of the AGL(4,2)-orbits,
// and decides by rank whether three vectors with supports in E0, E1, E2, not all supported on E0 & E1 & E2,
// have the same syndrome. For each such triple it prints: orbit data, the pairwise intersections, whether the triple
// is a strict common top (locators differ in degree < d), and for each pair the number of roots of c_i - c_j that are
// not in D (the "outside roots", with multiplicity).
#include "02_gf.h"
#define N 16
static int k, T, t, d, R; // R = n - k
static u64 pts[N], mom[N][N];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int pc(unsigned x) { return __builtin_popcount(x); }

// kernel of the system: sum_{x in E0} e0(x) x^j = sum_{x in Ei} ei(x) x^j, i = 1, 2, j < R. Returns its dimension,
// and one kernel vector (as three functions on D) with a nonzero component outside the trivial part if any.
static u64 A[2 * N][3 * N + 1];
static int solve(unsigned E0, unsigned E1, unsigned E2, u64 e[3][N], int want) {
  int col[3 * N], who[3 * N], nc = 0;
  unsigned Es[3] = {E0, E1, E2};
  for (int i = 0; i < 3; i++) for (int p = 0; p < N; p++) if (Es[i] >> p & 1) { col[nc] = p; who[nc] = i; nc++; }
  int nr = 2 * R;
  for (int r = 0; r < nr; r++) for (int c = 0; c < nc; c++) {
    int blk = r / R, j = r % R; u64 v = 0;
    if (who[c] == 0) v = mom[col[c]][j];
    else if (who[c] == blk + 1) v = mom[col[c]][j];
    A[r][c] = v;
  }
  int piv[3 * N], rank = 0, isp[3 * N];
  memset(isp, 0, sizeof isp);
  for (int c = 0; c < nc && rank < nr; c++) {
    int r = rank; while (r < nr && !A[r][c]) r++;
    if (r == nr) continue;
    if (r != rank) for (int cc = c; cc < nc; cc++) { u64 tmp = A[r][cc]; A[r][cc] = A[rank][cc]; A[rank][cc] = tmp; }
    u64 inv = ginv(A[rank][c]);
    for (int cc = c; cc < nc; cc++) A[rank][cc] = gmul(A[rank][cc], inv);
    for (int rr = 0; rr < nr; rr++) if (rr != rank && A[rr][c]) {
      u64 f = A[rr][c];
      for (int cc = c; cc < nc; cc++) A[rr][cc] ^= gmul(f, A[rank][cc]);
    }
    piv[rank] = c; isp[c] = 1; rank++;
  }
  int kd = nc - rank;
  if (want && kd > 0) {
    // random combination of the kernel basis vectors
    u64 x[3 * N]; memset(x, 0, sizeof x);
    for (int c = 0; c < nc; c++) if (!isp[c]) x[c] = rnd() | 1;
    for (int r = 0; r < rank; r++) { u64 s = 0; for (int c = 0; c < nc; c++) if (!isp[c] && A[r][c]) s ^= gmul(A[r][c], x[c]); x[piv[r]] = s; }
    memset(e, 0, 3 * N * sizeof(u64));
    for (int c = 0; c < nc; c++) e[who[c]][col[c]] = x[c];
  }
  return kd;
}

// coefficients of the interpolant on D of the values v (degree < 16), by Newton interpolation
static void interp(const u64 *v, u64 *cf) {
  u64 dd[N]; memcpy(dd, v, sizeof dd);
  for (int j = 1; j < N; j++) for (int i = N - 1; i >= j; i--) dd[i] = gmul(dd[i] ^ dd[i - 1], ginv(pts[i] ^ pts[i - j]));
  // Newton to monomial
  u64 c[N]; memset(c, 0, sizeof c);
  for (int j = N - 1; j >= 0; j--) { // c = c * (X - pts[j]) + dd[j]
    for (int i = N - 1; i >= 1; i--) c[i] = c[i - 1] ^ gmul(c[i], pts[j]);
    c[0] = gmul(c[0], pts[j]) ^ dd[j];
  }
  memcpy(cf, c, sizeof c);
}
// number of roots of the polynomial cf (degree deg) that are not in D, with multiplicity; -1 if zero polynomial
static int outside_roots(u64 *cf, int *degout, int *inD) {
  int deg = N - 1; while (deg >= 0 && !cf[deg]) deg--;
  *degout = deg; *inD = 0;
  if (deg < 0) return -1;
  u64 c[N]; memcpy(c, cf, sizeof c);
  int rem = deg;
  for (int p = 0; p < N; p++) for (;;) {
    u64 v = 0; for (int i = rem; i >= 0; i--) v = gmul(v, pts[p]) ^ c[i];
    if (v || rem == 0) break;
    // divide by (X - pts[p])
    u64 carry = 0; for (int i = rem; i >= 0; i--) { u64 cur = c[i] ^ gmul(carry, pts[p]); c[i] = carry; carry = cur; }
    rem--; (*inD)++;
  }
  return rem;
}


// ---- invariant of a triple: xi = (c1 - c2)/(c2 - c0) reduced, its degree, nu = #{x in D: xi(x) in {0,1,inf}}, |Pi|
static int pdeg(const u64 *a, int d) { while (d >= 0 && !a[d]) d--; return d; }
static u64 peval(const u64 *a, int d, u64 x) { u64 v = 0; for (int i = d; i >= 0; i--) v = gmul(v, x) ^ a[i]; return v; }
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
static int pdivexact(const u64 *a, int da, const u64 *b, int db, u64 *q) {
  u64 x[40]; memcpy(x, a, (da + 1) * sizeof(u64)); u64 inv = ginv(b[db]);
  for (int i = da; i >= db; i--) { u64 f = gmul(x[i], inv); q[i - db] = f; if (f) for (int j = 0; j <= db; j++) x[i - db + j] ^= gmul(f, b[j]); }
  return da - db;
}
static int wronskian_degree(u64 e[3][N]) { // degree of (c0-c1)'(c1-c2) + (c0-c1)(c1-c2)', -1 if zero
  u64 v[N], p[N], q[N], w[2 * N]; memset(w, 0, sizeof w);
  for (int x = 0; x < N; x++) v[x] = e[0][x] ^ e[1][x]; interp(v, p);
  for (int x = 0; x < N; x++) v[x] = e[1][x] ^ e[2][x]; interp(v, q);
  for (int i = 1; i < N; i += 2) for (int j = 0; j < N; j++) { w[i - 1 + j] ^= gmul(p[i], q[j]); w[i - 1 + j] ^= gmul(q[i], p[j]); }
  int d = 2 * N - 1; while (d >= 0 && !w[d]) d--; return d;
}
static void xi_invariant(u64 e[3][N], int *deg, int *nu, int *npi) {
  u64 v[N], u0[N], u1[N]; // u0 = c1 - c2 = e2 - e1 (as words: c_i = w - e_i), u1 = c2 - c0 = e0 - e2
  for (int p = 0; p < N; p++) v[p] = e[1][p] ^ e[2][p]; interp(v, u0);
  for (int p = 0; p < N; p++) v[p] = e[2][p] ^ e[0][p]; interp(v, u1);
  int d0 = pdeg(u0, N - 1), d1 = pdeg(u1, N - 1); u64 g[40], a[40], b[40], c[40];
  int dg = pgcd(u0, d0, u1, d1, g); int da = pdivexact(u0, d0, g, dg, a), db = pdivexact(u1, d1, g, dg, b);
  int dm = da > db ? da : db; for (int i = 0; i <= dm; i++) c[i] = (i <= da ? a[i] : 0) ^ (i <= db ? b[i] : 0);
  int dc = pdeg(c, dm); *deg = dm; *nu = 0; *npi = 0;
  for (int p = 0; p < N; p++) if (!peval(a, da, pts[p]) || !peval(b, db, pts[p]) || !peval(c, dc, pts[p])) (*nu)++;
  for (int s = 0; s < N; s++) { int ok = 1; for (int trial = 0; trial < 2 * dm + 3 && ok; trial++) { u64 y = rnd(); if (gmul(peval(a, da, y ^ pts[s]), peval(b, db, y)) != gmul(peval(a, da, y), peval(b, db, y ^ pts[s]))) ok = 0; } *npi += ok; }
}

static unsigned img(unsigned S, const int *perm) { unsigned r = 0; for (int p = 0; p < N; p++) if (S >> p & 1) r |= 1u << perm[p]; return r; }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 17_triples k T [seed] [dump]\n"); return 1; }
  k = atoi(argv[1]); T = atoi(argv[2]); if (argc > 3) rs ^= strtoull(argv[3], 0, 10) * 0x9e3779b97f4a7c15ull;
  int dump = argc > 4;
  t = N - T; d = N + k - 2 * T; R = N - k;
  gf_init(64, 0x1b);
  u64 b[4]; for (int i = 0; i < 4; i++) { for (int j = 0; j < 20; j++) rnd(); b[i] = rnd(); }
  for (int p = 0; p < N; p++) { pts[p] = 0; for (int i = 0; i < 4; i++) if (p >> i & 1) pts[p] ^= b[i]; }
  for (int p = 0; p < N; p++) { mom[p][0] = 1; for (int j = 1; j < N; j++) mom[p][j] = gmul(mom[p][j - 1], pts[p]); }
  printf("n=16 k=%d T=%d t=%d d=%d m=%d  (regime m >= d: %s)\n", k, T, t, d, T - k, T - k >= d ? "yes" : "no");
  // orbits of t-sets under AGL(4,2): generators = 4 translations, 12 transvections
  int gens[16][N], ng = 0;
  for (int i = 0; i < 4; i++) { for (int p = 0; p < N; p++) gens[ng][p] = p ^ (1 << i); ng++; }
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) { for (int p = 0; p < N; p++) gens[ng][p] = (p >> j & 1) ? p ^ (1 << i) : p; ng++; }
  static int orb[1 << N]; memset(orb, -1, sizeof orb);
  static unsigned stack[1 << N]; unsigned reps[4096]; long osize[4096]; int nrep = 0;
  for (unsigned S = 0; S < (1u << N); S++) if (pc(S) == t && orb[S] < 0) {
    int sp = 0; stack[sp++] = S; orb[S] = nrep; long sz = 0;
    while (sp) { unsigned U = stack[--sp]; sz++; for (int g = 0; g < ng; g++) { unsigned V = img(U, gens[g]); if (orb[V] < 0) { orb[V] = nrep; stack[sp++] = V; } } }
    reps[nrep] = S; osize[nrep] = sz; nrep++;
  }
  printf("%d orbits of %d-sets\n", nrep, t);
  static unsigned sets[1 << N]; int ns = 0;
  for (unsigned S = 0; S < (1u << N); S++) if (pc(S) == t) sets[ns++] = S;
  long total_rooted = 0, sing_rooted = 0; double total_w = 0, sing_w = 0;
  long hist_out[64]; memset(hist_out, 0, sizeof hist_out);
  long n_strict = 0, n_allin = 0, n_someout = 0, n_mtop = 0, n_bigker = 0, hist_M[N + 1]; memset(hist_M, 0, sizeof hist_M);
  static long hist_xi[N][N + 1][N + 1]; long bad_period = 0, bad_w = 0; int wmax = -1, wbound = 0;
  for (int r = 0; r < nrep; r++) {
    unsigned E0 = reps[r]; long cnt = 0, sing = 0;
    static unsigned cand[1 << N]; int ncand = 0;
    for (int a = 0; a < ns; a++) if (sets[a] != E0 && pc(sets[a] & E0) <= d - 1) cand[ncand++] = sets[a];
    for (int a = 0; a < ncand; a++) for (int c = a + 1; c < ncand; c++) {
      unsigned E1 = cand[a], E2 = cand[c];
      if (pc(E1 & E2) > d - 1) continue;
      cnt++;
      u64 e[3][N];
      int g = pc(E0 & E1 & E2);
      int kd = solve(E0, E1, E2, e, 0);
      if (kd <= g) continue;
      sing++;
      solve(E0, E1, E2, e, 1);
      // strict top: locators of E_i agree above degree d - 1  <=>  e_1..e_{t-d} equal; test through power sums of the sets is
      // not valid in char 2, so compare elementary symmetric functions directly
      u64 es[3][N + 1]; unsigned Es[3] = {E0, E1, E2};
      for (int i = 0; i < 3; i++) { memset(es[i], 0, sizeof es[i]); es[i][0] = 1; int deg = 0; for (int p = 0; p < N; p++) if (Es[i] >> p & 1) { deg++; for (int j = deg; j >= 1; j--) es[i][j] ^= gmul(es[i][j - 1], pts[p]); } }
      int strict = 1; for (int j = 1; j <= t - d; j++) if (es[0][j] != es[1][j] || es[0][j] != es[2][j]) strict = 0;
      int outs[3], degs[3], ins[3], anyout = 0;
      for (int a2 = 0; a2 < 3; a2++) {
        int i = a2, j = (a2 + 1) % 3; u64 v[N], cf[N];
        for (int p = 0; p < N; p++) v[p] = e[i][p] ^ e[j][p];
        interp(v, cf); outs[a2] = outside_roots(cf, &degs[a2], &ins[a2]);
        if (degs[a2] >= k) { fprintf(stderr, "degree check failed\n"); return 1; }
        if (outs[a2] > 0) anyout = 1;
        if (outs[a2] >= 0) hist_out[outs[a2]]++;
      }
      if (strict) n_strict++; else if (!anyout) n_allin++; else n_someout++;
      // the canonical representative of the word (degree < n): w - c_i is the interpolant of e_i. Multiset top with
      // mass < n  <=>  the three interpolants have the same degree and all their roots in D.
      int wdeg[3], win[3], wout[3], mtop = 1;
      for (int i = 0; i < 3; i++) { u64 cf[N]; interp(e[i], cf); wout[i] = outside_roots(cf, &wdeg[i], &win[i]); if (wout[i] != 0) mtop = 0; }
      if (mtop) n_mtop++; hist_M[wdeg[0]]++; if (kd - g > 1) n_bigker++;
      int xdeg, xnu, xpi; xi_invariant(e, &xdeg, &xnu, &xpi); hist_xi[xdeg][xnu][xpi]++;
      if (xpi < 3 * T - N - 2 * k + 2 || xnu > 2 * xdeg + xpi) bad_period++;
      { int ex = 3 * T - N - 2 * k + 1, J = 0; while (ex >= 1 && (1 << J) <= ex) J++; // 2^J > ex >= 2^(J-1)
        int wd = wronskian_degree(e), bound = 2 * k - 2 - (ex >= 1 ? (1 << J) : 2); if (wd > wmax) wmax = wd; if (wd > bound) bad_w++; wbound = bound; }
      if (dump) printf("  E=%04x %04x %04x g=%d ker=%d inter=%d,%d,%d strict=%d deg(c_i-c_j)=%d,%d,%d rootsInD=%d,%d,%d outside=%d,%d,%d\n", E0, E1, E2, g, kd,
                       pc(E0 & E1), pc(E1 & E2), pc(E2 & E0), strict, degs[0], degs[1], degs[2], ins[0], ins[1], ins[2], outs[0], outs[1], outs[2]), printf("      deg(w-c_i)=%d,%d,%d outside=%d,%d,%d\n", wdeg[0], wdeg[1], wdeg[2], wout[0], wout[1], wout[2]);
    }
    printf("orbit %d rep %04x size %ld: rooted triples %ld, list triples %ld\n", r, E0, osize[r], cnt, sing);
    total_rooted += cnt; sing_rooted += sing; total_w += (double)cnt * osize[r] / 3; sing_w += (double)sing * osize[r] / 3;
    fflush(stdout);
  }
  printf("total unordered triples with pairwise intersections <= d-1: %.0f, list triples: %.0f\n", total_w, sing_w);
  printf("rooted list triples: %ld  strict tops: %ld  not strict, every c_i - c_j splits over D: %ld  some root outside D: %ld\n", sing_rooted, n_strict, n_allin, n_someout);
  printf("multiset tops for the canonical representative (all roots of all w - c_i in D): %ld of %ld rooted list triples; solution space of dimension > 1: %ld\n", n_mtop, sing_rooted, n_bigker);
  printf("degree of the canonical representative:"); for (int i = 0; i <= N; i++) if (hist_M[i]) printf(" %d:%ld", i, hist_M[i]); printf("\n");
  printf("invariant xi = (c1-c2)/(c2-c0) of the rooted list triples, (deg, nu, |Pi|): count:");
  for (int a = 0; a < N; a++) for (int b2 = 0; b2 <= N; b2++) for (int c2 = 0; c2 <= N; c2++) if (hist_xi[a][b2][c2]) printf(" (%d,%d,%d):%ld", a, b2, c2, hist_xi[a][b2][c2]);
  printf("\ntriples with |Pi| < 3T - n - 2k + 2 = %d or nu > 2 deg + |Pi|: %ld\n", 3 * T - N - 2 * k + 2, bad_period);
  printf("largest degree of the Wronskian of (c0-c1, c1-c2): %d, bound of Theorem 3.3: %d, violations: %ld\n", wmax, wbound, bad_w);
  printf("outside-root histogram over pairs:"); for (int i = 0; i < 64; i++) if (hist_out[i]) printf(" %d:%ld", i, hist_out[i]); printf("\n");
  return 0;
}
