// Referee 41: independent numerical test of 35-large-characteristic-transfer.md over GF(2^16).
//
// For an evaluation set D (n points), a word y, a degree bound Delta, an agreement A and a certificate (m, B):
//   1. builds the contact conditions Q in c_m(alpha, y_alpha) for the support {X^x Y0^a Y1^c : c <= B,
//      x + Delta (a + c) < m A}, checks the local rank against R(m, B), and solves for the explainer space;
//   2. enumerates the list of y at agreement A by exhaustive interpolation (independent of the theory), or
//      takes the hyperplane flats when the enumeration is out of reach;
//   3. for random explainers Q: checks Q(X, P, P') = 0 on every list member and != 0 on a random polynomial,
//      splits Q = Q0(tau, u, v) + X Q1(tau, u, v) (tau = X^2, u = Y0 + X Y1, v = Y1), checks Proposition 2
//      (orders of Q0 + alpha Q1 and Q1 along the lines), computes deg gcd(Q0, Q1) at random tau by linear
//      algebra, decides for each list member whether its section lies on the common component, and compares the
//      number of members off the component with the Bezout bound (deg Q0 - t)(deg Q1 - t) of Theorem 4;
//      with nexp >= 2 also the Wronskian Q1 Q0' - Q0 Q1' of two explainers and its order along the lines;
//   4. for the flat word: builds the flat cubic G of Proposition 5, checks that the sections of the flats and of
//      every list member with at least 3n/8 - 1 agreements off 0 lie on it, its contact orders, whether the
//      common component is a power of it, and the two local ranks used in the proof of Lemma C.
//
// usage: 41_theory N dom seed word Delta A m B [nexp]
//   dom : 0 = span(1, x, .., x^(N-1)) in GF(2^16);  1 = random F2-subspace;  2 = n random points (no structure);
//         3 = span(1, z, .., z^(N-1)) in the subfield GF(2^8), z^8 + z^4 + z^3 + z^2 + 1 = 0 (the domain of 35_flat_list.c)
//   m = 0: only the list and the flat cubic checks (no explainer)
//   word: flat (alpha^(n/2-1)) | flat1 (alpha^(n/2)) | rand | plantL (L = 2..9 planted polynomials) |
//         sidon (tangent lines y = aX + a^2, Delta = 1) | five8 (L_U^5, |U| = n/8) | code:e (a codeword with e errors) | pad:e:c (X^e Z_C, |C| = c)
// build: cc -O2 -o 41_theory 41_theory.c
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint16_t fe;
static fe EXP[2 * 65535 + 2];
static int LOG[65536];
static inline fe mul(fe a, fe b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static inline fe inv(fe a) { return EXP[65535 - LOG[a]]; }
static fe fpow(fe a, long e) {
  if (e == 0) return 1;
  if (!a) return 0;
  return EXP[(int)(((long)LOG[a] * (e % 65535)) % 65535)];
}
static void gf_init(void) {
  unsigned v = 1;
  for (int i = 0; i < 65535; i++) {
    EXP[i] = (fe)v; LOG[v] = i;
    v <<= 1; if (v >> 16) v ^= 0x1100B;
    if (i < 65534 && v == 1) { fprintf(stderr, "modulus not primitive\n"); exit(1); }
  }
  if (v != 1) { fprintf(stderr, "modulus not primitive\n"); exit(1); }
  for (int i = 65535; i < 2 * 65535 + 2; i++) EXP[i] = EXP[i - 65535];
}
static uint64_t rs = 88172645463325252ull;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline fe rfe(void) { return (fe)(rnd() >> 20); }
static inline fe rfe_nz(void) { fe r; do r = rfe(); while (!r); return r; }
static inline int odd_binom(int nn, int kk) { return kk >= 0 && kk <= nn && ((nn & kk) == kk); }

#define MAXN 64
static int NN, n, Delta, A, m, B, Z, Bjet;
static fe D[MAXN], y[MAXN];

// ---------------------------------------------------------------- formulas of the note
static long Rloc(int mm, int BB) {
  if (mm <= 0 || BB < 0) return 0;
  long r = 0;
  for (int s = 0; s < mm; s++) {
    long k1 = 2 * s - mm + 1, k2 = s + BB - mm + 1;
    r += (long)(s + 1) * (BB + 1) - (k1 > 0 ? k1 : 0) * (k2 > 0 ? k2 : 0);
  }
  return r;
}

// ---------------------------------------------------------------- support
static int NM;                 // number of monomials
static int *mx, *ma, *mc;
static int *idxmap;            // [(c * (Bjet+1) + a) * Z + x]
static inline int midx(int x, int a, int c) {
  if (c > B || x < 0 || a < 0 || a + c > Bjet || x + Delta * (a + c) >= Z) return -1;
  return idxmap[(c * (Bjet + 1) + a) * Z + x];
}
static void build_support(void) {
  Z = m * A; Bjet = (Z - 1) / Delta;
  int cnt = 0;
  for (int c = 0; c <= B; c++) for (int a = 0; Delta * (a + c) < Z; a++) cnt += Z - Delta * (a + c);
  NM = cnt;
  mx = malloc(sizeof(int) * NM); ma = malloc(sizeof(int) * NM); mc = malloc(sizeof(int) * NM);
  idxmap = malloc(sizeof(int) * (size_t)(B + 1) * (Bjet + 1) * Z);
  memset(idxmap, 0xff, sizeof(int) * (size_t)(B + 1) * (Bjet + 1) * Z);
  cnt = 0;
  for (int c = 0; c <= B; c++) for (int a = 0; Delta * (a + c) < Z; a++) for (int x = 0; x + Delta * (a + c) < Z; x++) {
    mx[cnt] = x; ma[cnt] = a; mc[cnt] = c; idxmap[(c * (Bjet + 1) + a) * Z + x] = cnt; cnt++;
  }
}

// ---------------------------------------------------------------- contact conditions at one point
// rows (l, i, e): coefficient of T^i w^l Y1^e, i + 2l < mm, e <= B + i, after X = alpha + T, Y0 = b + w + T Y1
static int rows_pp;
static int rowid[40][80][160];
static void build_rowids(int mm) {
  rows_pp = 0;
  for (int l = 0; 2 * l < mm; l++) for (int i = 0; i + 2 * l < mm; i++) for (int e = 0; e <= B + i; e++) rowid[l][i][e] = rows_pp++;
}
static void build_block(int p, int mm, fe *blk) { // blk: rows_pp x NM
  memset(blk, 0, sizeof(fe) * (size_t)rows_pp * NM);
  fe al = D[p], b = y[p];
  for (int j = 0; j < NM; j++) {
    int x = mx[j], a = ma[j], c = mc[j];
    for (int l = 0; l <= a && 2 * l < mm; l++) {
      if (!odd_binom(a, l)) continue;
      for (int pp = 0; pp <= a - l; pp++) {
        if (!odd_binom(a - l, pp)) continue;
        fe cb = fpow(b, a - l - pp);
        if (!cb) continue;
        int e = c + pp;
        for (int i = pp; i + 2 * l < mm; i++) {
          int ip = i - pp;
          if (ip > x || !odd_binom(x, ip)) continue;
          fe v = mul(cb, fpow(al, x - ip));
          if (v) blk[(size_t)rowid[l][i][e] * NM + j] ^= v;
        }
      }
    }
  }
}

// ---------------------------------------------------------------- dense linear algebra
// rank of a rows x cols matrix (destroyed)
static int rank_inplace(fe *M, int rows, int cols) {
  int r = 0;
  for (int c = 0; c < cols && r < rows; c++) {
    int piv = -1;
    for (int i = r; i < rows; i++) if (M[(size_t)i * cols + c]) { piv = i; break; }
    if (piv < 0) continue;
    if (piv != r) for (int j = 0; j < cols; j++) { fe t = M[(size_t)r * cols + j]; M[(size_t)r * cols + j] = M[(size_t)piv * cols + j]; M[(size_t)piv * cols + j] = t; }
    fe *pr = M + (size_t)r * cols;
    fe iv = inv(pr[c]);
    for (int j = c; j < cols; j++) pr[j] = mul(pr[j], iv);
    for (int i = r + 1; i < rows; i++) {
      fe *ri = M + (size_t)i * cols; fe f = ri[c];
      if (!f) continue;
      int lf = LOG[f];
      for (int j = c; j < cols; j++) if (pr[j]) ri[j] ^= EXP[lf + LOG[pr[j]]];
    }
    r++;
  }
  return r;
}
// nullspace of a rows x cols matrix (destroyed). Returns nullity; basis (nullity x cols) malloc'ed in *basis.
static int nullspace(fe *M, int rows, int cols, fe **basis) {
  int *pivcol = malloc(sizeof(int) * (rows + 1)), *ispiv = calloc(cols, sizeof(int));
  int r = 0;
  for (int c = 0; c < cols && r < rows; c++) {
    int piv = -1;
    for (int i = r; i < rows; i++) if (M[(size_t)i * cols + c]) { piv = i; break; }
    if (piv < 0) continue;
    if (piv != r) for (int j = 0; j < cols; j++) { fe t = M[(size_t)r * cols + j]; M[(size_t)r * cols + j] = M[(size_t)piv * cols + j]; M[(size_t)piv * cols + j] = t; }
    fe *pr = M + (size_t)r * cols;
    fe iv = inv(pr[c]);
    for (int j = c; j < cols; j++) pr[j] = mul(pr[j], iv);
    for (int i = 0; i < rows; i++) {
      if (i == r) continue;
      fe *ri = M + (size_t)i * cols; fe f = ri[c];
      if (!f) continue;
      int lf = LOG[f];
      for (int j = c; j < cols; j++) if (pr[j]) ri[j] ^= EXP[lf + LOG[pr[j]]];
    }
    pivcol[r] = c; ispiv[c] = 1; r++;
  }
  int nul = cols - r;
  fe *bs = calloc((size_t)(nul ? nul : 1) * cols, sizeof(fe));
  int k = 0;
  for (int f = 0; f < cols; f++) {
    if (ispiv[f]) continue;
    bs[(size_t)k * cols + f] = 1;
    for (int i = 0; i < r; i++) bs[(size_t)k * cols + pivcol[i]] = M[(size_t)i * cols + f];
    k++;
  }
  free(pivcol); free(ispiv);
  *basis = bs;
  return nul;
}

// ---------------------------------------------------------------- global echelon form (explainer system)
static fe **pivrow;   // pivrow[c]: row with leading 1 in column c
static int grank;
static void ech_insert(fe *row) { // consumes a copy
  for (int c = 0; c < NM; c++) {
    fe f = row[c];
    if (!f) continue;
    if (pivrow[c]) {
      fe *pr = pivrow[c]; int lf = LOG[f];
      for (int j = c; j < NM; j++) if (pr[j]) row[j] ^= EXP[lf + LOG[pr[j]]];
    } else {
      fe iv = inv(f);
      fe *nr = malloc(sizeof(fe) * NM);
      for (int j = 0; j < NM; j++) nr[j] = mul(row[j], iv);
      pivrow[c] = nr; grank++;
      return;
    }
  }
}
static void random_null_vector(fe *x) {
  for (int c = NM - 1; c >= 0; c--) {
    if (!pivrow[c]) { x[c] = rfe(); continue; }
    fe *pr = pivrow[c]; fe s = 0;
    for (int j = c + 1; j < NM; j++) if (pr[j] && x[j]) s ^= EXP[LOG[pr[j]] + LOG[x[j]]];
    x[c] = s;
  }
}

// ---------------------------------------------------------------- polynomials in one variable, list oracle
#define MAXK 40
static int nmem, capmem;
static fe (*mem)[MAXK];   // coefficients, degree <= Delta
static int *memagree;
static void add_member(const fe *cf, int agree) {
  if (nmem == capmem) { capmem = capmem ? 2 * capmem : 64; mem = realloc(mem, sizeof(*mem) * capmem); memagree = realloc(memagree, sizeof(int) * capmem); }
  memset(mem[nmem], 0, sizeof(mem[nmem]));
  memcpy(mem[nmem], cf, sizeof(fe) * (Delta + 1));
  memagree[nmem] = agree; nmem++;
}
static fe peval(const fe *cf, int deg, fe x) { fe r = 0; for (int i = deg; i >= 0; i--) r = mul(r, x) ^ cf[i]; return r; }
static int agreement(const fe *cf) { int a = 0; for (int p = 0; p < n; p++) if (peval(cf, Delta, D[p]) == y[p]) a++; return a; }
// every polynomial of degree <= Delta with >= A agreements, once (from its first Delta + 1 agreement positions)
static long hist[MAXN + 1];
static void list_exhaustive(void) {
  int kk = Delta + 1, lim = n - A + kk; // the first kk agreements lie in positions < lim
  int idx[MAXK];
  for (int i = 0; i < kk; i++) idx[i] = i;
  for (;;) {
    fe c[MAXK], xs[MAXK];
    for (int i = 0; i < kk; i++) { xs[i] = D[idx[i]]; c[i] = y[idx[i]]; }
    for (int j = 1; j < kk; j++) for (int i = kk - 1; i >= j; i--) c[i] = mul(c[i] ^ c[i - 1], inv(xs[i] ^ xs[i - j]));
    int agree = 0, ok = 1, pos = 0;
    for (int t = 0; t < n && ok; t++) {
      fe r = c[kk - 1];
      for (int i = kk - 2; i >= 0; i--) r = mul(r, D[t] ^ xs[i]) ^ c[i];
      if (r == y[t]) { if (pos < kk) { if (idx[pos] != t) ok = 0; pos++; } agree++; }
      else if (agree + (n - 1 - t) < A) ok = 0;
    }
    if (ok && agree >= A) {
      fe p[MAXK]; memset(p, 0, sizeof p);
      p[0] = c[kk - 1]; int deg = 0;
      for (int i = kk - 2; i >= 0; i--) {
        for (int d = deg + 1; d >= 1; d--) p[d] = p[d - 1] ^ mul(p[d], xs[i]);
        p[0] = mul(p[0], xs[i]) ^ c[i]; deg++;
      }
      add_member(p, agree); hist[agree]++;
    }
    int i = kk - 1;
    while (i >= 0 && idx[i] == lim - kk + i) i--;
    if (i < 0) break;
    idx[i]++;
    for (int j = i + 1; j < kk; j++) idx[j] = idx[j - 1] + 1;
  }
}
static double binom_d(int a, int b) { double r = 1; for (int i = 0; i < b; i++) r = r * (a - i) / (i + 1); return r; }

// subspace polynomial of the points with index in mask-set (indices i with par(i & phi) == 0), or of all of D
static void locator(const int *sel, int cnt, fe *out) { // out: degree cnt, monic
  memset(out, 0, sizeof(fe) * (cnt + 1)); out[0] = 1;
  for (int t = 0; t < cnt; t++) { fe r = D[sel[t]]; for (int d = t + 1; d >= 1; d--) out[d] = out[d - 1] ^ mul(out[d], r); out[0] = mul(out[0], r); }
}

// ---------------------------------------------------------------- trivariate polynomials in (tau, u, v)
typedef struct { int TD, UD; fe *c; } tri;   // c[(t * UD + i) * UD + j] : tau^t u^i v^j
static tri tri_new(int TD, int UD) { tri g; g.TD = TD; g.UD = UD; g.c = calloc((size_t)TD * UD * UD, sizeof(fe)); return g; }
static inline fe *tri_at(tri *g, int t, int i, int j) { return &g->c[((size_t)t * g->UD + i) * g->UD + j]; }
static int tri_is_zero(tri *g) { size_t s = (size_t)g->TD * g->UD * g->UD; for (size_t i = 0; i < s; i++) if (g->c[i]) return 0; return 1; }
static fe tri_eval(tri *g, fe t0, fe u0, fe v0) {
  fe acc = 0;
  for (int t = g->TD - 1; t >= 0; t--) {
    fe gu = 0;
    for (int i = g->UD - 1; i >= 0; i--) {
      fe gv = 0; fe *row = tri_at(g, t, i, 0);
      for (int j = g->UD - 1; j >= 0; j--) gv = mul(gv, v0) ^ row[j];
      gu = mul(gu, u0) ^ gv;
    }
    acc = mul(acc, t0) ^ gu;
  }
  return acc;
}
// specialise tau = t0: bivariate q[i * UD + j]
static void tri_spec(tri *g, fe t0, fe *q) {
  int UD = g->UD;
  memset(q, 0, sizeof(fe) * UD * UD);
  for (int t = g->TD - 1; t >= 0; t--) for (int i = 0; i < UD * UD; i++) q[i] = mul(q[i], t0) ^ g->c[(size_t)t * UD * UD + i];
}
// order (capped at J) of G along a random line transversal to l_alpha at a random point of it
#define JMAX 12
static int ord_line_once(tri *g, fe al, fe yal, int J) {
  fe v0 = rfe(), u0 = yal ^ mul(al, v0), t0 = mul(al, al);
  fe a1 = rfe_nz(), a2 = rfe_nz(), a3 = rfe_nz();
  fe acc[JMAX] = {0};
  for (int t = g->TD - 1; t >= 0; t--) {
    fe gu[JMAX] = {0};
    for (int i = g->UD - 1; i >= 0; i--) {
      fe gv[JMAX] = {0}; fe *row = tri_at(g, t, i, 0);
      for (int j = g->UD - 1; j >= 0; j--) { // gv = gv * (v0 + a3 s) + row[j]
        for (int d = J - 1; d >= 1; d--) gv[d] = mul(gv[d], v0) ^ mul(gv[d - 1], a3);
        gv[0] = mul(gv[0], v0) ^ row[j];
      }
      for (int d = J - 1; d >= 1; d--) gu[d] = mul(gu[d], u0) ^ mul(gu[d - 1], a2) ^ gv[d];
      gu[0] = mul(gu[0], u0) ^ gv[0];
    }
    for (int d = J - 1; d >= 1; d--) acc[d] = mul(acc[d], t0) ^ mul(acc[d - 1], a1) ^ gu[d];
    acc[0] = mul(acc[0], t0) ^ gu[0];
  }
  for (int d = 0; d < J; d++) if (acc[d]) return d;
  return J;
}
static int ord_line(tri *g, fe al, fe yal, int J) { int o = J; for (int r = 0; r < 3; r++) { int t = ord_line_once(g, al, yal, J); if (t < o) o = t; } return o; }

// ---------------------------------------------------------------- bivariate gcd by linear algebra
static int bdeg(const fe *q, int UD) { int d = -1; for (int i = 0; i < UD; i++) for (int j = 0; j < UD; j++) if (q[i * UD + j] && i + j > d) d = i + j; return d; }
static inline int tri_cnt(int d) { return d < 0 ? 0 : (d + 1) * (d + 2) / 2; }
static inline int tpos(int i, int j) { int d = i + j; return d * (d + 1) / 2 + j; } // position of u^i v^j among monomials ordered by degree
// cofactor system: a (deg <= da), b (deg <= db) with a q1 + b q0 = 0; returns nullity and basis (unknowns: a then b)
static int cofactors(const fe *q0, int d0, const fe *q1, int d1, int da, int db, int UD, fe **basis) {
  int na = tri_cnt(da), nb = tri_cnt(db), cols = na + nb;
  int de = (da + d1 > db + d0 ? da + d1 : db + d0), rows = tri_cnt(de);
  fe *M = calloc((size_t)rows * cols, sizeof(fe));
  for (int i = 0; i + 0 <= da; i++) for (int j = 0; i + j <= da; j++) {
    int col = tpos(i, j);
    for (int I = 0; I <= d1; I++) for (int J = 0; I + J <= d1; J++) { fe v = q1[I * UD + J]; if (v) M[(size_t)tpos(i + I, j + J) * cols + col] ^= v; }
  }
  for (int i = 0; i <= db; i++) for (int j = 0; i + j <= db; j++) {
    int col = na + tpos(i, j);
    for (int I = 0; I <= d0; I++) for (int J = 0; I + J <= d0; J++) { fe v = q0[I * UD + J]; if (v) M[(size_t)tpos(i + I, j + J) * cols + col] ^= v; }
  }
  int nul = nullspace(M, rows, cols, basis);
  free(M);
  return nul;
}
// gcd of two bivariate polynomials (arrays UD x UD). Returns its total degree t and writes it to h (UD x UD), normalised
// so that its first nonzero coefficient (in tpos order from the top degree) is 1. h may be NULL.
static int bigcd(const fe *q0, const fe *q1, int UD, fe *h) {
  int d0 = bdeg(q0, UD), d1 = bdeg(q1, UD);
  if (h) memset(h, 0, sizeof(fe) * UD * UD);
  if (d0 < 0 && d1 < 0) return -1;
  const fe *single = NULL; int ds = 0;
  if (d1 < 0) { single = q0; ds = d0; }
  if (d0 < 0) { single = q1; ds = d1; }
  int t;
  fe *hh = calloc(UD * UD, sizeof(fe));
  if (single) { memcpy(hh, single, sizeof(fe) * UD * UD); t = ds; }
  else if (d0 == 0 || d1 == 0) { hh[0] = 1; t = 0; }
  else {
    fe *bs; int nul = cofactors(q0, d0, q1, d1, d0 - 1, d1 - 1, UD, &bs); free(bs);
    t = 0; while ((t + 1) * (t + 2) / 2 <= nul) t++;
    if (t * (t + 1) / 2 != nul) { fprintf(stderr, "bigcd: nullity %d is not triangular\n", nul); exit(1); }
    if (t == 0) hh[0] = 1;
    else {
      nul = cofactors(q0, d0, q1, d1, d0 - t, d1 - t, UD, &bs);
      if (nul != 1) { fprintf(stderr, "bigcd: cofactor nullity %d\n", nul); exit(1); }
      int da = d0 - t; // a = q0 / h up to a scalar
      fe *a = calloc(UD * UD, sizeof(fe));
      for (int i = 0; i <= da; i++) for (int j = 0; i + j <= da; j++) a[i * UD + j] = bs[tpos(i, j)];
      free(bs);
      // solve h a = lambda q0
      int cols = tri_cnt(t) + 1, rows = tri_cnt(d0);
      fe *M = calloc((size_t)rows * cols, sizeof(fe));
      for (int i = 0; i <= t; i++) for (int j = 0; i + j <= t; j++)
        for (int I = 0; I <= da; I++) for (int J = 0; I + J <= da; J++) { fe v = a[I * UD + J]; if (v) M[(size_t)tpos(i + I, j + J) * cols + tpos(i, j)] ^= v; }
      for (int I = 0; I <= d0; I++) for (int J = 0; I + J <= d0; J++) M[(size_t)tpos(I, J) * cols + cols - 1] ^= q0[I * UD + J];
      nul = nullspace(M, rows, cols, &bs);
      if (nul != 1 || !bs[cols - 1]) { fprintf(stderr, "bigcd: division failed (%d)\n", nul); exit(1); }
      for (int i = 0; i <= t; i++) for (int j = 0; i + j <= t; j++) hh[i * UD + j] = bs[tpos(i, j)];
      free(bs); free(M); free(a);
    }
  }
  // normalise
  fe lead = 0;
  for (int d = t; d >= 0 && !lead; d--) for (int j = 0; j <= d && !lead; j++) if (hh[(d - j) * UD + j]) lead = hh[(d - j) * UD + j];
  fe iv = inv(lead);
  for (int i = 0; i < UD * UD; i++) hh[i] = mul(hh[i], iv);
  if (h) memcpy(h, hh, sizeof(fe) * UD * UD);
  free(hh);
  return t;
}
static fe beval(const fe *q, int UD, fe u0, fe v0) {
  fe gu = 0;
  for (int i = UD - 1; i >= 0; i--) { fe gv = 0; for (int j = UD - 1; j >= 0; j--) gv = mul(gv, v0) ^ q[i * UD + j]; gu = mul(gu, u0) ^ gv; }
  return gu;
}
static void bmul(const fe *p, const fe *q, int UD, fe *out) {
  fe *r = calloc(UD * UD, sizeof(fe));
  for (int i = 0; i < UD; i++) for (int j = 0; j < UD; j++) { fe a = p[i * UD + j]; if (!a) continue;
    for (int I = 0; i + I < UD; I++) for (int J = 0; j + J < UD; J++) { fe b = q[I * UD + J]; if (b) r[(i + I) * UD + j + J] ^= mul(a, b); } }
  memcpy(out, r, sizeof(fe) * UD * UD); free(r);
}

// ---------------------------------------------------------------- explainers
static fe eval_Q(const fe *q, fe x0, fe y0, fe y1) {
  static fe *px = NULL, *py = NULL, *pz = NULL;
  if (!px) { px = malloc(sizeof(fe) * (Z + 1)); py = malloc(sizeof(fe) * (Bjet + 2)); pz = malloc(sizeof(fe) * (B + 2)); }
  px[0] = 1; for (int i = 1; i <= Z; i++) px[i] = mul(px[i - 1], x0);
  py[0] = 1; for (int i = 1; i <= Bjet + 1; i++) py[i] = mul(py[i - 1], y0);
  pz[0] = 1; for (int i = 1; i <= B + 1; i++) pz[i] = mul(pz[i - 1], y1);
  fe s = 0;
  for (int j = 0; j < NM; j++) if (q[j]) s ^= mul(q[j], mul(px[mx[j]], mul(py[ma[j]], pz[mc[j]])));
  return s;
}
static int kills(const fe *q, const fe *P, int deg) { // Q(X, P, P') == 0 ? (12 random points; deg Q(X,P,P') < Z < 2^16)
  fe dP[MAXK + 2]; memset(dP, 0, sizeof dP);
  for (int i = 1; i <= deg; i += 2) dP[i - 1] = P[i];
  for (int r = 0; r < 12; r++) { fe x0 = rfe(); if (eval_Q(q, x0, peval(P, deg, x0), peval(dP, deg, x0))) return 0; }
  return 1;
}
static void split_Q(const fe *q, tri *Q0, tri *Q1) {
  for (int j = 0; j < NM; j++) {
    fe v = q[j]; if (!v) continue;
    int x = mx[j], a = ma[j], c = mc[j];
    for (int jj = 0; jj <= a; jj++) {
      if (!odd_binom(a, jj)) continue;
      int e = x + jj; tri *g = (e & 1) ? Q1 : Q0;
      *tri_at(g, e >> 1, a - jj, c + jj) ^= v;
    }
  }
}
static int tri_uvdeg(tri *g) { int d = -1; for (int t = 0; t < g->TD; t++) for (int i = 0; i < g->UD; i++) for (int j = 0; j < g->UD; j++) if (*tri_at(g, t, i, j) && i + j > d) d = i + j; return d; }

// ---------------------------------------------------------------- univariate irreducibility over GF(2^16) (Rabin)
#define UMAX 130
static void umulmod(const fe *a, const fe *b, const fe *f, int d, fe *out) { // a, b of degree < d, f monic of degree d
  fe t[2 * UMAX]; memset(t, 0, sizeof(fe) * 2 * d);
  for (int i = 0; i < d; i++) if (a[i]) for (int j = 0; j < d; j++) if (b[j]) t[i + j] ^= mul(a[i], b[j]);
  for (int i = 2 * d - 2; i >= d; i--) if (t[i]) { fe c = t[i]; for (int j = 0; j < d; j++) if (f[j]) t[i - d + j] ^= mul(c, f[j]); t[i] = 0; }
  memcpy(out, t, sizeof(fe) * d);
}
static int ugcd_deg(const fe *a, int da, const fe *b, int db) { // degree of gcd; a, b not both zero
  fe x[UMAX + 1], y2[UMAX + 1]; memset(x, 0, sizeof x); memset(y2, 0, sizeof y2);
  memcpy(x, a, sizeof(fe) * (da + 1)); memcpy(y2, b, sizeof(fe) * (db + 1));
  int dx = da, dy = db;
  while (dx >= 0 && !x[dx]) dx--;
  while (dy >= 0 && !y2[dy]) dy--;
  while (dy >= 0) {
    while (dx >= dy) { fe cq = mul(x[dx], inv(y2[dy])); for (int j = 0; j <= dy; j++) x[dx - dy + j] ^= mul(cq, y2[j]); while (dx >= 0 && !x[dx]) dx--; }
    fe tmp[UMAX + 1]; memcpy(tmp, x, sizeof tmp); memcpy(x, y2, sizeof x); memcpy(y2, tmp, sizeof y2);
    int t = dx; dx = dy; dy = t;
  }
  return dx;
}
static int uirreducible(const fe *fin, int d) { // fin of exact degree d
  if (d <= 0 || d >= UMAX) return 0;
  if (d == 1) return 1;
  fe f[UMAX + 1]; fe iv = inv(fin[d]); for (int i = 0; i <= d; i++) f[i] = mul(fin[i], iv);
  fe h[UMAX]; memset(h, 0, sizeof h); h[1] = 1; // x
  fe hs[UMAX][UMAX];
  for (int i = 1; i <= d; i++) { for (int s = 0; s < 16; s++) umulmod(h, h, f, d, h); memcpy(hs[i], h, sizeof(fe) * d); }
  fe t[UMAX]; memcpy(t, hs[d], sizeof(fe) * d); t[1] ^= 1;
  for (int i = 0; i < d; i++) if (t[i]) return 0;
  for (int p = 2; p <= d; p++) {
    if (d % p) continue;
    int isp = 1; for (int r = 2; r * r <= p; r++) if (p % r == 0) isp = 0;
    if (!isp) continue;
    memcpy(t, hs[d / p], sizeof(fe) * d); t[1] ^= 1;
    int dt = d - 1; while (dt >= 0 && !t[dt]) dt--;
    if (dt < 0) return 0;
    if (ugcd_deg(f, d, t, dt) != 0) return 0;
  }
  return 1;
}
// restriction of a bivariate polynomial (UD x UD, total degree d) to the line (u0 + a s, v0 + b s); returns the degree
static int line_restrict(const fe *w, int UD, int d, fe u0, fe a, fe v0, fe b, fe *f) {
  fe acc[UMAX + 1]; memset(acc, 0, sizeof acc);
  for (int i = (d < UD - 1 ? d : UD - 1); i >= 0; i--) {
    fe in[UMAX + 1]; memset(in, 0, sizeof in);
    for (int j = (d - i < UD - 1 ? d - i : UD - 1); j >= 0; j--) { for (int e = d; e >= 1; e--) in[e] = mul(in[e], v0) ^ mul(in[e - 1], b); in[0] = mul(in[0], v0) ^ w[i * UD + j]; }
    for (int e = d; e >= 1; e--) acc[e] = mul(acc[e], u0) ^ mul(acc[e - 1], a) ^ in[e];
    acc[0] = mul(acc[0], u0) ^ in[0];
  }
  memcpy(f, acc, sizeof(fe) * (d + 1));
  int df = d; while (df >= 0 && !f[df]) df--;
  return df;
}

// ---------------------------------------------------------------- main
int main(int argc, char **argv) {
  if (argc < 9) { fprintf(stderr, "usage: 41_theory N dom seed word Delta A m B [nexp]\n"); return 1; }
  gf_init();
  NN = atoi(argv[1]); n = 1 << NN;
  int dom = atoi(argv[2]); long seed = atol(argv[3]); const char *word = argv[4];
  Delta = atoi(argv[5]); A = atoi(argv[6]); m = atoi(argv[7]); B = atoi(argv[8]);
  int nexp = argc > 9 ? atoi(argv[9]) : 2;
  rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ull; for (int i = 0; i < 20; i++) rnd();
  // ----- domain
  fe basis[16];
  if (dom == 0) for (int b = 0; b < NN; b++) basis[b] = EXP[b];
  if (dom == 1) {
    for (int b = 0; b < NN;) { // random independent vectors over F2
      fe c = rfe_nz(); int dep = 0;
      for (int mask = 1; mask < (1 << b) && !dep; mask++) { fe s = 0; for (int t = 0; t < b; t++) if (mask >> t & 1) s ^= basis[t]; if (s == c) dep = 1; }
      if (!dep) basis[b++] = c;
    }
  }
  if (dom == 3) { // span(1, z, .., z^(N-1)) with z a root of x^8 + x^4 + x^3 + x^2 + 1 (the GF(2^8) of 35_flat_list.c)
    fe z = 0;
    for (int e = 1; e < 255 && !z; e++) { fe c = EXP[257 * e]; fe c2 = mul(c, c), c3 = mul(c2, c), c4 = mul(c2, c2), c8 = mul(c4, c4); if ((c8 ^ c4 ^ c3 ^ c2 ^ 1) == 0) z = c; }
    if (!z) { fprintf(stderr, "no root\n"); return 1; }
    basis[0] = 1; for (int b = 1; b < NN; b++) basis[b] = mul(basis[b - 1], z);
  }
  if (dom == 0 || dom == 1 || dom == 3) for (int i = 0; i < n; i++) { fe e = 0; for (int b = 0; b < NN; b++) if (i >> b & 1) e ^= basis[b]; D[i] = e; }
  if (dom == 2) for (int i = 0; i < n;) { fe c = rfe(); int dup = 0; for (int j = 0; j < i; j++) if (D[j] == c) dup = 1; if (!dup) D[i++] = c; }
  int is_sub = dom != 2;
  // ----- word
  int isflat = !strcmp(word, "flat"), isflat1 = !strcmp(word, "flat1");
  if (isflat || isflat1) { if (!is_sub) { fprintf(stderr, "flat words need a subspace\n"); return 1; } for (int i = 0; i < n; i++) y[i] = fpow(D[i], isflat ? n / 2 - 1 : n / 2); if (isflat) y[0] = D[0] ? y[0] : 0; }
  else if (!strcmp(word, "rand")) for (int i = 0; i < n; i++) y[i] = rfe();
  else if (!strncmp(word, "plant", 5)) {
    int L = atoi(word + 5); fe P[16][MAXK];
    for (int l = 0; l < L; l++) for (int i = 0; i <= Delta; i++) P[l][i] = rfe();
    int perm[MAXN]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < n; i++) y[perm[i]] = peval(P[i % L], Delta, D[perm[i]]);
  } else if (!strcmp(word, "sidon")) {
    // greedy Sidon set S in D (sums a + a' pairwise distinct, nonzero); y(a + a') = a a'; other points random
    int S[MAXN], ns = 0; char used[65536]; memset(used, 0, sizeof used);
    int order[MAXN]; for (int i = 0; i < n; i++) order[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = order[i]; order[i] = order[j]; order[j] = t; }
    int best[MAXN], nbest = 0;
    for (int tries = 0; tries < 4000; tries++) {
      ns = 0; memset(used, 0, sizeof used);
      for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = order[i]; order[i] = order[j]; order[j] = t; }
      for (int oi = 0; oi < n; oi++) {
        int c = order[oi], ok = 1;
        for (int t = 0; t < ns && ok; t++) if (used[D[c] ^ D[S[t]]]) ok = 0;
        if (!ok) continue;
        for (int t = 0; t < ns; t++) used[D[c] ^ D[S[t]]] = 1;
        S[ns++] = c;
      }
      if (ns > nbest) { nbest = ns; memcpy(best, S, sizeof(int) * ns); }
    }
    ns = nbest; memcpy(S, best, sizeof(int) * ns);
    for (int i = 0; i < n; i++) y[i] = rfe();
    int inD = 0;
    for (int s = 0; s < ns; s++) for (int t = s + 1; t < ns; t++) {
      fe sum = D[S[s]] ^ D[S[t]];
      for (int i = 0; i < n; i++) if (D[i] == sum) { y[i] = mul(D[S[s]], D[S[t]]); inD++; }
    }
    printf("sidon: |S| = %d, %d of %d pairwise sums in D\n", ns, inD, ns * (ns - 1) / 2);
  } else if (!strncmp(word, "code:", 5)) {
    int e = atoi(word + 5); fe P[MAXK]; for (int i = 0; i <= Delta; i++) P[i] = rfe();
    for (int i = 0; i < n; i++) y[i] = peval(P, Delta, D[i]);
    for (int t = 0; t < e; t++) y[rnd() % n] ^= rfe_nz();
  } else if (!strcmp(word, "five8")) { // L_U^5, U the span of the first N - 3 basis vectors (note 21, section 2.2); use Delta = n/2, A = 5n/8
    if (!is_sub) { fprintf(stderr, "five8 needs a subspace\n"); return 1; }
    for (int i = 0; i < n; i++) { fe v = 1; for (int u = 0; u < n / 8; u++) v = mul(v, D[i] ^ D[u]); y[i] = fpow(v, 5); }
  } else if (!strncmp(word, "pad:", 4)) {
    int e, c; sscanf(word + 4, "%d:%d", &e, &c);
    for (int i = 0; i < n; i++) { fe v = fpow(D[i], e); for (int t = 1; t <= c; t++) v = mul(v, D[i] ^ D[t]); y[i] = v; }
  } else { fprintf(stderr, "unknown word\n"); return 1; }

  int only_list = (m == 0);
  if (only_list) { m = 1; B = 0; }
  build_support();
  printf("n = %d, domain %s, word %s, Delta = %d, A = %d, (m, B) = (%d, %d): %d monomials, n R(m, B) = %ld, B_jet = %d\n",
         n, dom == 0 ? "span(1..x^(N-1))" : dom == 1 ? "random subspace" : dom == 3 ? "span(1..z^(N-1)) in GF(2^8)" : "random points", word, Delta, A, m, B, NM, n * Rloc(m, B), Bjet);

  // ----- flat cubic data (subspace domains)
  fe LD[MAXN + 1], ecoef[8]; tri Gc; int have_cubic = 0;
  if (is_sub) {
    int all[MAXN]; for (int i = 0; i < n; i++) all[i] = i;
    locator(all, n, LD);
    int lin = 1; for (int d = 0; d <= n; d++) if (LD[d] && (d & (d - 1) || d == 0)) lin = 0;
    for (int j = 0; j <= NN; j++) ecoef[j] = LD[1 << j];
    if (!lin) { fprintf(stderr, "L_D is not linearised\n"); return 1; }
    if (isflat) {
      // G = u^3 + tau u v^2 + e0 v + u gamma(tau) + e0 tau^(n/4-1), gamma(tau) = sum_{1<=j<N} e_j tau^(2^(j-1)-1)
      Gc = tri_new(n / 4 + 1, 4); have_cubic = 1;
      *tri_at(&Gc, 0, 3, 0) ^= 1; *tri_at(&Gc, 1, 1, 2) ^= 1; *tri_at(&Gc, 0, 0, 1) ^= ecoef[0];
      for (int j = 1; j < NN; j++) *tri_at(&Gc, (1 << (j - 1)) - 1, 1, 0) ^= ecoef[j];
      *tri_at(&Gc, n / 4 - 1, 0, 0) ^= ecoef[0];
    }
    if (isflat1) {
      // slack 1 (referee): G' = tau v^3 + u^2 v + e0 u + tau gamma(tau) v + e0 tau^(n/4), hat G' = d/dX of
      // E' = Y0^3 + (L_D(X) - X^n) Y0 + e0 X^(n/2+1); it should contain all n lines and all 2(n - 1) affine flats
      Gc = tri_new(n / 4 + 2, 4); have_cubic = 2;
      *tri_at(&Gc, 1, 0, 3) ^= 1; *tri_at(&Gc, 0, 2, 1) ^= 1; *tri_at(&Gc, 0, 1, 0) ^= ecoef[0];
      for (int j = 1; j < NN; j++) *tri_at(&Gc, 1 << (j - 1), 0, 1) ^= ecoef[j];
      *tri_at(&Gc, n / 4, 0, 0) ^= ecoef[0];
    }
  }

  // ----- list
  double cost = binom_d(n - A + Delta + 1, Delta + 1);
  if (cost < 1.2e8) { list_exhaustive(); printf("list (exhaustive, %.0f interpolations): %d members;", cost, nmem); for (int a = A; a <= n; a++) if (hist[a]) printf(" [%d: %ld]", a, hist[a]); printf("\n"); }
  else if (isflat || isflat1) {
    for (int phi = 1; phi < n; phi++) {
      int sel[MAXN], cnt = 0; for (int i = 0; i < n; i++) if (!__builtin_parity(i & phi)) sel[cnt++] = i;
      fe LV[MAXN + 1]; locator(sel, cnt, LV);
      fe P[MAXK]; memset(P, 0, sizeof P);
      if (isflat) { for (int d = 1; d < n / 2; d++) P[d - 1] = LV[d]; if (agreement(P) >= A) add_member(P, agreement(P)); }
      else {
        for (int d = 0; d < n / 2; d++) P[d] = LV[d];
        if (agreement(P) >= A) add_member(P, agreement(P));
        int o = 0; while (__builtin_parity(o & phi) == 0) o++;
        P[0] ^= peval(LV, n / 2, D[o]);
        if (agreement(P) >= A) add_member(P, agreement(P));
      }
    }
    printf("list (hyperplane flats only, exhaustive search out of reach: %.2e interpolations): %d members\n", cost, nmem);
  } else printf("list: not computed (%.2e interpolations)\n", cost);

  // ----- flat cubic checks
  if (have_cubic) {
    int ncont = 0, bad = 0;
    for (int p = 0; p < n; p++) { int o = ord_line(&Gc, D[p], y[p], 4); if (o >= 1) ncont++; if (D[p] && o != 1) bad++; if (!D[p] && o != (have_cubic == 1 ? 0 : 1)) bad++; }
    printf("flat cubic%s: contains %d lines; lines whose order differs from 1 (from %d at alpha = 0): %d\n", have_cubic == 2 ? " (slack 1 version)" : "", ncont, have_cubic == 1 ? 0 : 1, bad);
    int on = 0, off = 0, need = 0, needoff = 0;
    for (int i = 0; i < nmem; i++) {
      int ag0 = 0; for (int p = 0; p < n; p++) if (D[p] && peval(mem[i], Delta, D[p]) == y[p]) ag0++;
      int ok = 1;
      for (int r = 0; r < 8 && ok; r++) {
        fe t0 = rfe(), g = 0, h = 0;
        for (int d = Delta; d >= 0; d--) { if (d & 1) h = mul(h, t0) ^ mem[i][d]; else g = mul(g, t0) ^ mem[i][d]; }
        if (tri_eval(&Gc, t0, g, h)) ok = 0;
      }
      if (ok) on++; else off++;
      if (have_cubic == 1 && 2 * ag0 > 3 * (Delta + 1) - 3) { need++; if (!ok) needoff++; }
      if (have_cubic == 2 && 2 * memagree[i] > 3 * Delta - 1) { need++; if (!ok) needoff++; }
    }
    if (have_cubic == 1) printf("flat cubic: %d list members are sections, %d are not; members with 2 * (agreements off 0) > 3k - 3: %d, of which NOT sections: %d\n", on, off, need, needoff);
    else printf("flat cubic (slack 1 version): %d list members are sections, %d are not; members with 2 * agreements > 3 Delta - 1: %d, of which NOT sections: %d\n", on, off, need, needoff);
  }

  if (only_list) return 0;
  // ----- contact conditions
  build_rowids(m);
  fe *blk = malloc(sizeof(fe) * (size_t)rows_pp * NM);
  pivrow = calloc(NM, sizeof(fe *));
  int rect_in = Delta * (m - 1 + B) < Z;
  for (int p = 0; p < n; p++) {
    build_block(p, m, blk);
    if (p < 3) {
      fe *cp = malloc(sizeof(fe) * (size_t)rows_pp * NM); memcpy(cp, blk, sizeof(fe) * (size_t)rows_pp * NM);
      int r = rank_inplace(cp, rows_pp, NM); free(cp);
      printf("local rank at point %d: %d (R(m, B) = %ld, full rectangle %s the support)\n", p, r, Rloc(m, B), rect_in ? "inside" : "NOT inside");
    }
    for (int r = 0; r < rows_pp; r++) ech_insert(blk + (size_t)r * NM);
  }
  printf("explainer space: rank %d, dimension %d (count predicts >= %ld)\n", grank, NM - grank, NM - n * Rloc(m, B));
  if (NM == grank) { printf("no explainer\n"); return 0; }

  // ----- Lemma C local ranks for the flat cubic: rank(S -> /c_m) and rank(G S' -> /c_m) = rank(S' -> /c_(m-o))
  if (have_cubic == 1) {
    int W = 3 * (Delta + 1) - 2, Zp = Z - W, np = 0;
    // sparse form of hat G in (X, Y0, Y1): list of (x, a, c, coef)
    int gx[32], ga[32], gc[32], ng = 0; fe gv[32];
    gx[ng] = 0; ga[ng] = 3; gc[ng] = 0; gv[ng++] = 1;
    gx[ng] = 1; ga[ng] = 2; gc[ng] = 1; gv[ng++] = 1;
    gx[ng] = 0; ga[ng] = 0; gc[ng] = 1; gv[ng++] = ecoef[0];
    for (int j = 1; j < NN; j++) if (ecoef[j]) { gx[ng] = (1 << j) - 2; ga[ng] = 1; gc[ng] = 0; gv[ng++] = ecoef[j]; gx[ng] = (1 << j) - 1; ga[ng] = 0; gc[ng] = 1; gv[ng++] = ecoef[j]; }
    gx[ng] = n / 2 - 2; ga[ng] = 0; gc[ng] = 0; gv[ng++] = ecoef[0];
    for (int j = 0; j < NM; j++) if (mc[j] <= B - 1 && mx[j] + Delta * (ma[j] + mc[j]) < Zp) np++;
    for (int pt = 0; pt < 2; pt++) {
      int p = pt == 0 ? 0 : 1 + (int)(rnd() % (n - 1));
      build_block(p, m, blk);
      fe *img = calloc((size_t)np * rows_pp, sizeof(fe)); int k = 0, miss = 0;
      for (int j = 0; j < NM; j++) {
        if (!(mc[j] <= B - 1 && mx[j] + Delta * (ma[j] + mc[j]) < Zp)) continue;
        for (int t = 0; t < ng; t++) {
          int id = midx(mx[j] + gx[t], ma[j] + ga[t], mc[j] + gc[t]);
          if (id < 0) { miss++; continue; }
          for (int r = 0; r < rows_pp; r++) { fe v = blk[(size_t)r * NM + id]; if (v) img[(size_t)k * rows_pp + r] ^= mul(v, gv[t]); }
        }
        k++;
      }
      int r2 = rank_inplace(img, np, rows_pp); free(img);
      int o = D[p] ? 2 : 0;
      printf("Lemma C local ranks at alpha %s: rank(G S') = %d, R(m - o, B - 1) = %ld (o = %d); products outside S: %d; side condition Delta (m + B) <= Z - W: %s\n",
             D[p] ? "!= 0" : "= 0", r2, Rloc(m - o, B - 1), o, miss, Delta * (m + B) <= Zp ? "holds" : "fails");
    }
  }

  // ----- random explainers
  fe *q = malloc(sizeof(fe) * NM);
  int TD = (Z + Bjet) / 2 + 2, UD = Bjet + 2;
  tri keep0[2], keep1[2];
  for (int ex = 0; ex < nexp; ex++) {
    random_null_vector(q);
    int nz = 0; for (int j = 0; j < NM; j++) if (q[j]) nz++;
    // residual check on two points
    int resid = 0;
    for (int p = 0; p < n; p += n / 2 + 1) { build_block(p, m, blk); for (int r = 0; r < rows_pp; r++) { fe s = 0; for (int j = 0; j < NM; j++) if (q[j] && blk[(size_t)r * NM + j]) s ^= mul(q[j], blk[(size_t)r * NM + j]); if (s) resid++; } }
    int killed = 0; for (int i = 0; i < nmem; i++) if (kills(q, mem[i], Delta)) killed++;
    fe Rp[MAXK]; for (int i = 0; i <= Delta; i++) Rp[i] = rfe();
    int krand = kills(q, Rp, Delta);
    printf("explainer %d: %d nonzero coefficients, residual %d; kills %d of %d list members; kills a random polynomial: %s\n", ex, nz, resid, killed, nmem, krand ? "YES" : "no");
    tri Q0 = tri_new(TD, UD), Q1 = tri_new(TD, UD);
    split_Q(q, &Q0, &Q1);
    int d0 = tri_uvdeg(&Q0), d1 = tri_uvdeg(&Q1);
    // Proposition 2
    int J = m / 2 + 2 < JMAX ? m / 2 + 2 : JMAX, bad2 = 0;
    tri Qa = tri_new(TD, UD);
    for (int p = 0; p < n; p++) {
      for (size_t i = 0; i < (size_t)TD * UD * UD; i++) Qa.c[i] = Q0.c[i] ^ mul(D[p], Q1.c[i]);
      int oa = ord_line(&Qa, D[p], y[p], J), o1 = ord_line(&Q1, D[p], y[p], J);
      if (oa < (m + 1) / 2 || o1 < m / 2) bad2++;
      if (p == 1 && ex == 0) printf("   orders along the line of point 1: Q0 + alpha Q1: %d (needs >= %d), Q1: %d (needs >= %d)\n", oa, (m + 1) / 2, o1, m / 2);
    }
    printf("   Proposition 2: %d of %d lines violate the two order conditions\n", bad2, n);
    // sections of the members
    int secbad = 0;
    for (int i = 0; i < nmem; i++) for (int r = 0; r < 2; r++) {
      fe t0 = rfe(), g = 0, h = 0;
      for (int d = Delta; d >= 0; d--) { if (d & 1) h = mul(h, t0) ^ mem[i][d]; else g = mul(g, t0) ^ mem[i][d]; }
      if (tri_eval(&Q0, t0, g, h) || tri_eval(&Q1, t0, g, h)) secbad++;
    }
    printf("   Proposition 3: Q0 and Q1 vanish separately on the sections of the members: %s; (u, v)-degrees %d, %d%s\n", secbad ? "NO" : "yes", d0, d1, tri_is_zero(&Q1) ? " (Q1 = 0: Q is a first integral)" : "");
    // gcd at three random tau
    fe *q0 = malloc(sizeof(fe) * UD * UD), *q1 = malloc(sizeof(fe) * UD * UD), *h = malloc(sizeof(fe) * UD * UD);
    int tt[3]; int *onc = calloc(nmem ? nmem : 1, sizeof(int));
    for (int r = 0; r < 3; r++) {
      fe t0 = rfe_nz();
      tri_spec(&Q0, t0, q0); tri_spec(&Q1, t0, q1);
      tt[r] = bigcd(q0, q1, UD, h);
      for (int i = 0; i < nmem; i++) {
        fe g = 0, hh = 0;
        for (int d = Delta; d >= 0; d--) { if (d & 1) hh = mul(hh, t0) ^ mem[i][d]; else g = mul(g, t0) ^ mem[i][d]; }
        if (tt[r] > 0 && beval(h, UD, g, hh) == 0) onc[i]++;
      }
      if (r == 0) {
        int du = -1, dv = -1; for (int i = 0; i < UD; i++) for (int j = 0; j < UD; j++) if (h[i * UD + j]) { if (i > du) du = i; if (j > dv) dv = j; }
        printf("   common component at a random tau: total degree %d, deg_u %d, deg_v %d\n", tt[r], du, dv);
        if (have_cubic && tt[r] > 0) {
          fe *gc0 = calloc(UD * UD, sizeof(fe)), *pw = calloc(UD * UD, sizeof(fe)), *g4 = malloc(sizeof(fe) * 16);
          tri_spec(&Gc, t0, g4);
          for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) gc0[i * UD + j] = g4[i * 4 + j];
          int e = 0; pw[0] = 1;
          fe *cur = malloc(sizeof(fe) * UD * UD); memcpy(cur, h, sizeof(fe) * UD * UD);
          // multiplicity of the cubic in h: divide while gcd(cur, cubic) has degree 3
          for (;;) {
            fe *gg = malloc(sizeof(fe) * UD * UD);
            int tg = bigcd(cur, gc0, UD, gg); free(gg);
            if (tg != 3) break;
            e++; bmul(pw, gc0, UD, pw);
            // cur := h / pw via cofactor: a pw = lambda h
            int dh = tt[r], dp = 3 * e, da = dh - dp;
            if (da < 0) break;
            int cols = tri_cnt(da) + 1, rows = tri_cnt(dh);
            fe *M = calloc((size_t)rows * cols, sizeof(fe)), *bs;
            for (int i = 0; i <= da; i++) for (int j = 0; i + j <= da; j++)
              for (int I = 0; I <= dp; I++) for (int Jj = 0; I + Jj <= dp; Jj++) { fe v = pw[I * UD + Jj]; if (v) M[(size_t)tpos(i + I, j + Jj) * cols + tpos(i, j)] ^= v; }
            for (int I = 0; I <= dh; I++) for (int Jj = 0; I + Jj <= dh; Jj++) M[(size_t)tpos(I, Jj) * cols + cols - 1] ^= h[I * UD + Jj];
            int nul = nullspace(M, rows, cols, &bs); free(M);
            if (nul != 1 || !bs[cols - 1]) { free(bs); e--; break; }
            memset(cur, 0, sizeof(fe) * UD * UD);
            for (int i = 0; i <= da; i++) for (int j = 0; i + j <= da; j++) cur[i * UD + j] = bs[tpos(i, j)];
            free(bs);
            if (da == 0) break;
          }
          printf("   the flat cubic divides the common component exactly %d times (component degree %d)\n", e, tt[r]);
          free(gc0); free(pw); free(g4); free(cur);
        }
        if (tt[r] >= 2 && nmem <= 200) { // squares (Y0 - P)^2 = (u - g)^2 + tau (v - h)^2 of list members dividing the component
          int nsq = 0; fe *s2 = calloc(UD * UD, sizeof(fe)), *gg = malloc(sizeof(fe) * UD * UD);
          for (int i = 0; i < nmem; i++) {
            fe g = 0, hh = 0;
            for (int d = Delta; d >= 0; d--) { if (d & 1) hh = mul(hh, t0) ^ mem[i][d]; else g = mul(g, t0) ^ mem[i][d]; }
            memset(s2, 0, sizeof(fe) * UD * UD);
            s2[2 * UD] = 1; s2[2] = t0; s2[0] = mul(g, g) ^ mul(t0, mul(hh, hh));
            if (bigcd(h, s2, UD, gg) == 2) nsq++;
          }
          printf("   members P whose square (Y0 - P)^2, a first integral with b = 0, divides the common component: %d (total degree %d of %d)\n", nsq, 2 * nsq, tt[r]);
          free(s2); free(gg);
        }
      }
    }
    int non = 0, nmixed = 0; for (int i = 0; i < nmem; i++) { if (onc[i] == 3) non++; else if (onc[i] != 0) nmixed++; }
    int t = tt[0] < tt[1] ? tt[0] : tt[1]; if (tt[2] < t) t = tt[2];
    long bez = (long)(d0 - t) * (d1 - t);
    printf("   gcd degree at three random tau: %d %d %d; members on the common component: %d, off it: %d (ambiguous %d); Bezout bound for the rest (d0 - t)(d1 - t) = %ld: %s\n",
           tt[0], tt[1], tt[2], non, nmem - non - nmixed, nmixed, bez, (tri_is_zero(&Q1) || nmem - non <= bez) ? "ok" : "VIOLATED");
    free(q0); free(q1); free(h); free(onc); free(Qa.c);
    if (ex < 2) { keep0[ex] = Q0; keep1[ex] = Q1; } else { free(Q0.c); free(Q1.c); }
  }
  // ----- Wronskian of two explainers: Q' dQ - Q dQ' = Q1 Q0' - Q0 Q1' in (tau, u, v), a first integral;
  //       referee's claim: its order along every line is >= m (contact order >= 2m)
  if (nexp >= 2 && (double)TD * UD * UD < 3e4 && m + 2 <= JMAX) {
    tri Wr = tri_new(2 * TD, 2 * UD);
    for (int s = 0; s < 2; s++) {
      tri *P = s == 0 ? &keep1[0] : &keep0[0], *R2 = s == 0 ? &keep0[1] : &keep1[1];
      for (int t = 0; t < TD; t++) for (int i = 0; i < UD; i++) for (int j = 0; j < UD; j++) {
        fe a = *tri_at(P, t, i, j); if (!a) continue; int la = LOG[a];
        for (int t2 = 0; t2 < TD; t2++) for (int i2 = 0; i2 < UD; i2++) { fe *row = tri_at(R2, t2, i2, 0); fe *dst = tri_at(&Wr, t + t2, i + i2, j);
          for (int j2 = 0; j2 < UD; j2++) if (row[j2]) dst[j2] ^= EXP[la + LOG[row[j2]]]; }
      }
    }
    int omin = JMAX, omax = 0;
    for (int p = 0; p < n; p++) { int o = ord_line(&Wr, D[p], y[p], m + 2); if (o < omin) omin = o; if (o > omax) omax = o; }
    int secbad = 0;
    for (int i = 0; i < nmem; i++) { fe t0 = rfe(), g = 0, h = 0; for (int d = Delta; d >= 0; d--) { if (d & 1) h = mul(h, t0) ^ mem[i][d]; else g = mul(g, t0) ^ mem[i][d]; } if (tri_eval(&Wr, t0, g, h)) secbad++; }
    int dW = tri_uvdeg(&Wr);
    printf("Wronskian of explainers 0 and 1: %s, (u, v)-degree %d; order along the lines between %d and %d%s (claim: >= m = %d); vanishes on the sections of all members: %s\n",
           tri_is_zero(&Wr) ? "ZERO" : "nonzero", dW, omin, omax, omax >= m + 2 ? "+" : "", m, secbad ? "NO" : "yes");
    if (dW > 0 && dW < UMAX - 2) {
      // jet coordinates: weighted degree, b = deg_Y1, does the leading Y1-coefficient involve Y0
      int UW = Wr.UD, XD = 2 * Wr.TD + UW + 1, AD = 2 * UW;
      fe *jet = calloc((size_t)XD * AD * AD, sizeof(fe)); // [x][a][c]
      for (int t = 0; t < Wr.TD; t++) for (int i = 0; i < UW; i++) for (int j = 0; j < UW; j++) {
        fe v = *tri_at(&Wr, t, i, j); if (!v) continue;
        for (int p = 0; p <= i; p++) if (odd_binom(i, p)) jet[((size_t)(2 * t + p) * AD + (i - p)) * AD + (j + p)] ^= v;
      }
      long Wt = -1; int bb = -1, lcY0 = 0;
      for (int x = 0; x < XD; x++) for (int a = 0; a < AD; a++) for (int cc = 0; cc < AD; cc++) if (jet[((size_t)x * AD + a) * AD + cc]) { long w = x + (long)Delta * (a + cc); if (w > Wt) Wt = w; if (cc > bb) bb = cc; }
      for (int x = 0; x < XD; x++) for (int a = 1; a < AD; a++) if (jet[((size_t)x * AD + a) * AD + bb]) lcY0 = 1;
      long so = 0; for (int p = 0; p < n; p++) so += 2 * ord_line(&Wr, D[p], y[p], m + 2);
      printf("   in jet coordinates: weighted degree W = %ld (2mA = %d), b = %d, leading Y1-coefficient %s; total contact %ld = %.2f n, efficiency W / total contact = %.4f (A/n = %.4f)\n",
             Wt, 2 * Z, bb, lcY0 ? "involves Y0" : "is in F[X]", so, (double)so / n, (double)Wt / so, (double)A / n);
      free(jet);
      // irreducibility at a random tau: an irreducible line restriction of full degree, and a nonsingular rational point
      int irr = 0, tries = 0, nonsing = 0, UW2 = Wr.UD;
      fe *w = malloc(sizeof(fe) * UW2 * UW2);
      fe t0 = rfe_nz(); tri_spec(&Wr, t0, w);
      int dw = bdeg(w, UW2);
      for (tries = 0; tries < 60 * dw && !irr; tries++) {
        fe f[UMAX + 1]; int df = line_restrict(w, UW2, dw, rfe(), rfe_nz(), rfe(), rfe_nz(), f);
        if (df == dw && uirreducible(f, df)) irr = 1;
      }
      for (int tr = 0; tr < 40 && !nonsing; tr++) {
        fe u0 = rfe(), cf[UMAX + 1], cu[UMAX + 1]; // cf[j] = sum_i w[i][j] u0^i ; cu[j] = sum_i i w[i][j] u0^(i-1)
        for (int j = 0; j <= dw; j++) { fe s = 0, su = 0; for (int i = (dw - j < UW2 - 1 ? dw - j : UW2 - 1); i >= 0; i--) { su = mul(su, u0); if ((i + 1) < UW2 && ((i + 1) & 1) && j < UW2) su ^= w[(i + 1) * UW2 + j]; s = mul(s, u0) ^ (j < UW2 ? w[i * UW2 + j] : 0); } cf[j] = s; cu[j] = su; }
        for (int v0 = 0; v0 < 65536 && !nonsing; v0++) {
          fe s = 0; for (int j = dw; j >= 0; j--) s = mul(s, (fe)v0) ^ cf[j];
          if (s) continue;
          fe dv = 0, du = 0; for (int j = dw; j >= 0; j--) { du = mul(du, (fe)v0) ^ cu[j]; }
          for (int j = dw; j >= 1; j--) { dv = mul(dv, (fe)v0); if (j & 1) dv ^= cf[j]; }
          // dv computed as sum_{j odd} cf[j] v0^(j-1): redo exactly
          dv = 0; { fe pw = 1; for (int j = 1; j <= dw; j++) { if (j & 1) dv ^= mul(cf[j], pw); pw = mul(pw, (fe)v0); } }
          if (dv || du) nonsing = 1;
        }
      }
      printf("   at a random tau (degree %d): irreducible restriction to a line found: %s (%d lines tried); nonsingular GF(2^16)-point found: %s => %s\n",
             dw, irr ? "yes" : "no", tries, nonsing ? "yes" : "no", (irr && nonsing && dw == dW) ? "the Wronskian is absolutely irreducible over F(tau)" : "no conclusion");
      free(w);
    }
  }
  return 0;
}
