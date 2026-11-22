// Researcher 39: numerical test of Theorem S2 of note 39 (phantom roots outside D are common to all members).
//
//   39_split_pairs N T k r seed [real]
//
// Domain: a random N-dimensional F_2-subspace of GF(2^64) (basis from xorshift(seed)), or with "real" the span of
// 1, x, .., x^{N-1}. n = 2^N <= 16 in practice. For every unordered pair of T-subsets S1 != S2 the program solves
//     Z_S1 h1 = Z_S2 h2  modulo polynomials of degree < k,      h1, h2 monic of degree r,
// which is the statement "S1 and S2 are agreement sets of two members of the list of one word of degree T + r".
// The system is linear in the 2r coefficients, with m' - 1 = T + r - k equations. For a solvable pair the reduced
// fraction A/B = h1/h2 is computed (it is unique as soon as m' >= 2r + 1) and the roots of A and B are located:
// in D, or not. Theorem S2 says that for m' = T + r - k + 1 >= 2(deg A + deg B) all of them are in D on a generic
// domain. Output: the number of solvable pairs, by (deg A, deg B), and the number with a root outside D.
#include "02_gf.h"
#define MAXN 16
#define MAXR 4
static int N, n, T, k, r, mp;
static u64 pts[MAXN];
static u64 rs;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

// polynomials: low coefficient first, degree given
static int pdeg(const u64 *a, int d) { while (d >= 0 && !a[d]) d--; return d; }
static int pgcd(const u64 *a, int da, const u64 *b, int db, u64 *g) { // monic gcd, returns degree
  u64 x[2 * MAXR + 2], y[2 * MAXR + 2]; int dx = da, dy = db;
  memcpy(x, a, (da + 1) * sizeof(u64)); if (db >= 0) memcpy(y, b, (db + 1) * sizeof(u64));
  dx = pdeg(x, dx); dy = pdeg(y, dy);
  while (dy >= 0) {
    while (dx >= dy) { u64 f = gmul(x[dx], ginv(y[dy])); for (int i = 0; i <= dy; i++) x[dx - dy + i] ^= gmul(f, y[i]); dx = pdeg(x, dx); }
    u64 t[2 * MAXR + 2]; memcpy(t, x, sizeof t); memcpy(x, y, sizeof t); memcpy(y, t, sizeof t); int td = dx; dx = dy; dy = td;
  }
  u64 iv = ginv(x[dx]); for (int i = 0; i <= dx; i++) g[i] = gmul(x[i], iv);
  return dx;
}
static int pdivexact(const u64 *a, int da, const u64 *b, int db, u64 *q) { // a / b, returns degree of q
  u64 x[2 * MAXR + 2]; memcpy(x, a, (da + 1) * sizeof(u64)); u64 iv = ginv(b[db]);
  for (int i = da - db; i >= 0; i--) { u64 f = gmul(x[i + db], iv); q[i] = f; for (int j = 0; j <= db; j++) x[i + j] ^= gmul(f, b[j]); }
  return da - db;
}
static u64 peval(const u64 *a, int d, u64 x) { u64 v = 0; for (int i = d; i >= 0; i--) v = gmul(v, x) ^ a[i]; return v; }
static int roots_outside(const u64 *a, int d) { // number of roots (with multiplicity) not in D
  u64 x[2 * MAXR + 2]; memcpy(x, a, (d + 1) * sizeof(u64)); int left = d;
  for (int p = 0; p < n; p++) while (left > 0 && peval(x, left, pts[p]) == 0) { // divide by (X - pts[p])
    u64 q[2 * MAXR + 2]; u64 lin[2] = {pts[p], 1}; pdivexact(x, left, lin, 1, q); left--; memcpy(x, q, (left + 1) * sizeof(u64));
  }
  return left;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: 39_split_pairs N T k r seed [real]\n"); return 1; }
  gf_init(64, 0x1b);
  N = atoi(argv[1]); n = 1 << N; T = atoi(argv[2]); k = atoi(argv[3]); r = atoi(argv[4]);
  rs = 88172645463325252ull ^ (strtoull(argv[5], 0, 10) * 0x9E3779B97F4A7C15ull); for (int i = 0; i < 20; i++) rnd();
  u64 basis[8]; for (int i = 0; i < N; i++) basis[i] = rnd();
  if (argc > 6 && !strcmp(argv[6], "real")) for (int i = 0; i < N; i++) basis[i] = 1ull << i;
  for (int p = 0; p < n; p++) { pts[p] = 0; for (int i = 0; i < N; i++) if (p >> i & 1) pts[p] ^= basis[i]; }
  mp = T + r - k + 1; int neq = mp - 1, nun = 2 * r;
  if (r > MAXR || neq > 14) { fprintf(stderr, "r <= %d and T + r - k <= 14\n", MAXR); return 1; }
  // all T-subsets with e_0..e_neq
  size_t cap = 1 << 16, ns = 0; u32 *msk = malloc(cap * sizeof(u32)); u64 *E = malloc(cap * 16 * sizeof(u64));
  for (u32 m = 0; m < (1u << n); m++) {
    if (__builtin_popcount(m) != T) continue;
    if (ns == cap) { cap *= 2; msk = realloc(msk, cap * sizeof(u32)); E = realloc(E, cap * 16 * sizeof(u64)); }
    u64 *e = E + ns * 16; memset(e, 0, 16 * sizeof(u64)); e[0] = 1;
    for (int p = 0; p < n; p++) if (m >> p & 1) for (int j = neq; j >= 1; j--) e[j] ^= gmul(e[j - 1], pts[p]);
    msk[ns++] = m;
  }
  long solv = 0, bad = 0, nonuniq = 0, hist[MAXR + 1][MAXR + 1]; memset(hist, 0, sizeof hist); long badh[MAXR + 1][MAXR + 1]; memset(badh, 0, sizeof badh);
  for (size_t i = 0; i < ns; i++) for (size_t j = i + 1; j < ns; j++) {
    const u64 *e1 = E + i * 16, *e2 = E + j * 16;
    // equations q = 1..neq: sum_{t=1..r} a_t e1[q-t] + sum_t b_t e2[q-t] = e1[q] + e2[q]
    u64 M[14][2 * MAXR + 1];
    for (int q = 1; q <= neq; q++) {
      for (int t = 1; t <= r; t++) { M[q - 1][t - 1] = q - t >= 0 ? e1[q - t] : 0; M[q - 1][r + t - 1] = q - t >= 0 ? e2[q - t] : 0; }
      M[q - 1][nun] = e1[q] ^ e2[q];
    }
    int piv[2 * MAXR], rank = 0, isp[2 * MAXR]; memset(isp, 0, sizeof isp);
    for (int c = 0; c < nun && rank < neq; c++) {
      int p = -1; for (int q = rank; q < neq; q++) if (M[q][c]) { p = q; break; }
      if (p < 0) continue;
      if (p != rank) for (int cc = 0; cc <= nun; cc++) { u64 t = M[p][cc]; M[p][cc] = M[rank][cc]; M[rank][cc] = t; }
      u64 iv = ginv(M[rank][c]); for (int cc = 0; cc <= nun; cc++) M[rank][cc] = gmul(M[rank][cc], iv);
      for (int q = 0; q < neq; q++) if (q != rank && M[q][c]) { u64 f = M[q][c]; for (int cc = 0; cc <= nun; cc++) M[q][cc] ^= gmul(f, M[rank][cc]); }
      piv[rank] = c; isp[c] = 1; rank++;
    }
    int ok = 1; for (int q = rank; q < neq; q++) if (M[q][nun]) { ok = 0; break; }
    if (!ok) continue;
    solv++; if (rank < nun) nonuniq++;
    u64 h1[MAXR + 1], h2[MAXR + 1], sol[2 * MAXR]; memset(sol, 0, sizeof sol);
    for (int q = 0; q < rank; q++) sol[piv[q]] = M[q][nun]; // free unknowns = 0
    h1[r] = h2[r] = 1; for (int t = 1; t <= r; t++) { h1[r - t] = sol[t - 1]; h2[r - t] = sol[r + t - 1]; }
    u64 g[2 * MAXR + 2], A[2 * MAXR + 2], B[2 * MAXR + 2]; int dg = pgcd(h1, r, h2, r, g);
    int dA = pdivexact(h1, r, g, dg, A), dB = pdivexact(h2, r, g, dg, B);
    hist[dA][dB]++;
    if (roots_outside(A, dA) + roots_outside(B, dB) > 0) { bad++; badh[dA][dB]++; }
  }
  printf("N=%d n=%d T=%d k=%d r=%d: m' = %d, threshold 4r = %d; %zu sets, %ld solvable pairs (%ld with a non-unique (h1, h2)), %ld with a root of the reduced fraction outside D\n", N, n, T, k, r, mp, 4 * r, ns, solv, nonuniq, bad);
  for (int a = 0; a <= r; a++) for (int b = 0; b <= r; b++) if (hist[a][b]) printf("  reduced degrees (%d, %d): %ld pairs, %ld with a root outside D (m' >= 2(deg A + deg B): %s)\n", a, b, hist[a][b], badh[a][b], mp >= 2 * (a + b) ? "yes" : "no");
  return 0;
}
