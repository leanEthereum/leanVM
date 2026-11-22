// Referee 52. Null space of the contact conditions of order m on a monomial support, over GF(2^kf).
//
// Support: X^x Y0^a Y1^c, c in a given list, x + Delta*(a + c) < Z.
// Conditions at a received point (alpha, y), from the definition of the contact ideal c_m(alpha, y):
// write Q(alpha + T, y + S, Y1) in the basis T^i' w^l Y1^e (S = w + T*Y1); every coefficient with i' + 2l < m is 0.
//   X^x Y0^a Y1^c  ->  sum_{i,j,p} C(x,i) C(a,j) C(j,p) alpha^(x-i) y^(a-j) T^(i+p) w^(j-p) Y1^(c+p).
// No rank formula is used. Output: number of unknowns, rank, nullity, the local rank at the first three points,
// a Lemma 0 test on supplied polynomials, and a basis of the null space.
//
// stdin:  kf modpoly / n Delta m Z / ncs c_1 .. c_ncs / n lines "alpha y" / ntest dP / ntest lines of dP+1 coefficients
// stdout: "U .. RANK .. NULL .. LOCAL r0 r1 r2" / "KILL killed ntest control" / NULL lines of U hex values
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint16_t fe;
static int kf, ord;
static fe *EXP;
static int *LOG;
static inline fe mul(fe a, fe b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static inline fe inv(fe a) { return EXP[ord - LOG[a]]; }
static void gf_init(unsigned modp) {
  ord = (1 << kf) - 1;
  EXP = malloc(sizeof(fe) * (2 * ord + 2));
  LOG = malloc(sizeof(int) * (ord + 1));
  unsigned v = 1;
  for (int i = 0; i < ord; i++) {
    EXP[i] = (fe)v; LOG[v] = i;
    v <<= 1; if (v >> kf) v ^= modp;
  }
  if (v != 1) { fprintf(stderr, "modulus not primitive\n"); exit(1); }
  for (int i = ord; i < 2 * ord + 2; i++) EXP[i] = EXP[i - ord];
}
static uint64_t rs = 0x9E3779B97F4A7C15ull;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int U;
// r ^= f * p on columns [from, U)
static inline void axpy(fe *r, const fe *p, fe f, int from) {
  int lf = LOG[f];
  for (int c = from; c < U; c++) if (p[c]) r[c] ^= EXP[lf + LOG[p[c]]];
}
// insert r into an echelon set (piv[col] = normalized row with leading column col); returns 1 if independent
static int insert(fe **piv, fe *r, int copy) {
  for (int c = 0; c < U; c++) {
    if (!r[c]) continue;
    if (piv[c]) { axpy(r, piv[c], r[c], c); continue; }
    fe iv = inv(r[c]);
    fe *s = r;
    if (copy) { s = malloc(sizeof(fe) * U); memcpy(s, r, sizeof(fe) * U); }
    for (int k = c; k < U; k++) s[k] = mul(s[k], iv);
    piv[c] = s;
    return 1;
  }
  return 0;
}

int main(void) {
  unsigned modp;
  int n, Delta, m, Z, ncs, cs[8];
  if (scanf("%d %u", &kf, &modp) != 2) return 1;
  gf_init(modp);
  if (scanf("%d %d %d %d", &n, &Delta, &m, &Z) != 4) return 1;
  if (scanf("%d", &ncs) != 1) return 1;
  int cmax = 0;
  for (int i = 0; i < ncs; i++) { if (scanf("%d", &cs[i]) != 1) return 1; if (cs[i] > cmax) cmax = cs[i]; }
  fe *al = malloc(sizeof(fe) * n), *yy = malloc(sizeof(fe) * n);
  for (int i = 0; i < n; i++) { unsigned a, b; if (scanf("%u %u", &a, &b) != 2) return 1; al[i] = (fe)a; yy[i] = (fe)b; }
  // monomials
  int cap = 1 << 16; U = 0;
  int *mx = malloc(sizeof(int) * cap), *ma = malloc(sizeof(int) * cap), *mc = malloc(sizeof(int) * cap);
  int xmax = 0, amax = 0;
  for (int ic = 0; ic < ncs; ic++)
    for (int a = 0; Delta * (a + cs[ic]) < Z; a++)
      for (int x = 0; x + Delta * (a + cs[ic]) < Z; x++) {
        if (U == cap) { cap *= 2; mx = realloc(mx, sizeof(int) * cap); ma = realloc(ma, sizeof(int) * cap); mc = realloc(mc, sizeof(int) * cap); }
        mx[U] = x; ma[U] = a; mc[U] = cs[ic]; U++;
        if (x > xmax) xmax = x;
        if (a > amax) amax = a;
      }
  int L = (m + 1) / 2, E = cmax + m, nloc = m * L * E;
  fe *blk = malloc(sizeof(fe) * (size_t)nloc * U);
  fe **gpiv = calloc(U, sizeof(fe *)), **lpiv = calloc(U, sizeof(fe *));
  fe *apow = malloc(sizeof(fe) * (xmax + 1)), *ypow = malloc(sizeof(fe) * (amax + 1));
  int locrank[3] = {-1, -1, -1}, rank = 0;
  for (int pt = 0; pt < n; pt++) {
    memset(blk, 0, sizeof(fe) * (size_t)nloc * U);
    apow[0] = 1; for (int e = 1; e <= xmax; e++) apow[e] = mul(apow[e - 1], al[pt]);
    ypow[0] = 1; for (int e = 1; e <= amax; e++) ypow[e] = mul(ypow[e - 1], yy[pt]);
    for (int u = 0; u < U; u++) {
      int x = mx[u], a = ma[u], c = mc[u];
      for (int j = 0; j <= a && j < m; j++) {
        if (j & ~a) continue;
        for (int p = 0; p <= j; p++) {
          if (p & ~j) continue;
          for (int i = 0; i <= x && i + 2 * j - p < m; i++) {
            if (i & ~x) continue;
            fe v = mul(apow[x - i], ypow[a - j]);
            if (!v) continue;
            int row = ((i + p) * L + (j - p)) * E + (c + p);
            blk[(size_t)row * U + u] ^= v;
          }
        }
      }
    }
    memset(lpiv, 0, sizeof(fe *) * U);
    int lr = 0;
    for (int r = 0; r < nloc; r++) lr += insert(lpiv, blk + (size_t)r * U, 0);
    if (pt < 3) locrank[pt] = lr;
    for (int c = 0; c < U; c++) if (lpiv[c]) rank += insert(gpiv, lpiv[c], 1);
  }
  // reduced echelon form
  for (int c = U - 1; c >= 0; c--) {
    if (!gpiv[c]) continue;
    for (int c2 = 0; c2 < c; c2++) if (gpiv[c2] && gpiv[c2][c]) axpy(gpiv[c2], gpiv[c], gpiv[c2][c], c);
  }
  int nul = U - rank;
  printf("U %d RANK %d NULL %d LOCAL %d %d %d\n", U, rank, nul, locrank[0], locrank[1], locrank[2]);
  fe **basis = malloc(sizeof(fe *) * (nul > 0 ? nul : 1));
  int nb = 0;
  for (int f = 0; f < U; f++) {
    if (gpiv[f]) continue;
    fe *v = calloc(U, sizeof(fe));
    v[f] = 1;
    for (int c = 0; c < f; c++) if (gpiv[c]) v[c] = gpiv[c][f];
    basis[nb++] = v;
  }
  // Lemma 0 test: a random combination R of the basis, evaluated on the jets (x, P(x), P'(x)) at min(Z, 2^kf) points
  int ntest = 0, dP = 0;
  if (scanf("%d %d", &ntest, &dP) != 2) ntest = 0;
  fe *R = calloc(U, sizeof(fe));
  for (int b = 0; b < nb; b++) { fe f = (fe)(1 + rnd() % ord); axpy(R, basis[b], f, 0); }
  int npts = Z < (1 << kf) ? Z : (1 << kf);
  fe *P = malloc(sizeof(fe) * (dP + 1));
  int killed = 0, control = 0;
  for (int t = 0; t <= ntest; t++) {
    if (t < ntest) { for (int i = 0; i <= dP; i++) { unsigned v; if (scanf("%u", &v) != 1) return 1; P[i] = (fe)v; } }
    else { for (int i = 0; i <= dP; i++) P[i] = (fe)(i <= Delta ? rnd() % (ord + 1) : 0); }
    int zero = 1;
    for (int e = 0; e < npts && zero; e++) {
      fe x = (fe)e, p = 0, dp = 0;
      for (int i = dP; i >= 0; i--) p = mul(p, x) ^ P[i];
      for (int i = dP; i >= 1; i--) dp = mul(dp, x) ^ ((i & 1) ? P[i] : 0);
      // R(x, p, dp): monomials are grouped by c, then a, then x ascending
      fe tot = 0;
      int u = 0;
      while (u < U) {
        int c = mc[u];
        fe accA = 0, ppow = 1;
        while (u < U && mc[u] == c) {
          int a = ma[u], u0 = u;
          while (u < U && mc[u] == c && ma[u] == a) u++;
          fe h = 0;
          for (int k = u - 1; k >= u0; k--) h = mul(h, x) ^ R[k];
          accA ^= mul(h, ppow);
          ppow = mul(ppow, p);
        }
        fe dpc = 1;
        for (int k = 0; k < c; k++) dpc = mul(dpc, dp);
        tot ^= mul(accA, dpc);
      }
      if (tot) zero = 0;
    }
    if (t < ntest) killed += zero; else control = zero;
  }
  printf("KILL %d %d %d\n", nb ? killed : -1, ntest, control);
  for (int b = 0; b < nb; b++) {
    for (int u = 0; u < U; u++) printf("%x ", basis[b][u]);
    printf("\n");
  }
  return 0;
}
