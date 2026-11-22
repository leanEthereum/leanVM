// Referee 52. Exhaustive list oracle: all polynomials of degree <= Delta over GF(2^kf) that agree with a word on
// at least A of n points. Independent of the explainer theory: every such polynomial is the interpolant of its
// first Delta+1 agreement positions, and these lie among the first n - A + Delta + 1 positions. The DFS keeps the
// Newton form of the interpolant of the chosen positions.
// stdin:  kf modpoly / n Delta A / n lines "alpha y"
// stdout: one line per list member: agreement, then the Delta+1 monomial coefficients (low to high), decimal
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
static int n, Delta, A, K;
static fe al[256], yy[256];
static int idx[256];
static fe nw[256];  // Newton coefficients on the chosen nodes
static long count = 0;

static void leaf(void) {
  int agree = 0, firstK = 1, seen = 0;
  for (int p = 0; p < n; p++) {
    fe v = nw[K - 1];
    for (int i = K - 2; i >= 0; i--) v = mul(v, al[p] ^ al[idx[i]]) ^ nw[i];
    if (v == yy[p]) {
      if (seen < K && idx[seen] != p) { firstK = 0; break; }
      seen++; agree++;
    } else if (n - p - 1 + agree < A) return;
  }
  if (!firstK || agree < A) return;
  // monomial coefficients from the Newton form
  fe co[256]; memset(co, 0, sizeof co);
  for (int i = K - 1; i >= 0; i--) {
    // co = co * (X - al[idx[i]]) + nw[i]
    for (int d = K - 1; d >= 1; d--) co[d] = co[d - 1] ^ mul(co[d], al[idx[i]]);
    co[0] = mul(co[0], al[idx[i]]) ^ nw[i];
  }
  printf("%d", agree);
  for (int d = 0; d < K; d++) printf(" %u", co[d]);
  printf("\n");
  count++;
}
static void dfs(int j, int start) {
  if (j == K) { leaf(); return; }
  int lim = n - A + j;
  for (int p = start; p <= lim && p < n; p++) {
    fe v = 0, den = 1;
    if (j > 0) { v = nw[j - 1]; for (int i = j - 2; i >= 0; i--) v = mul(v, al[p] ^ al[idx[i]]) ^ nw[i]; }
    for (int i = 0; i < j; i++) den = mul(den, al[p] ^ al[idx[i]]);
    nw[j] = mul(v ^ yy[p], inv(den));
    idx[j] = p;
    dfs(j + 1, p + 1);
  }
}
int main(void) {
  unsigned modp;
  if (scanf("%d %u", &kf, &modp) != 2) return 1;
  ord = (1 << kf) - 1;
  EXP = malloc(sizeof(fe) * (2 * ord + 2));
  LOG = malloc(sizeof(int) * (ord + 1));
  unsigned v = 1;
  for (int i = 0; i < ord; i++) { EXP[i] = (fe)v; LOG[v] = i; v <<= 1; if (v >> kf) v ^= modp; }
  for (int i = ord; i < 2 * ord + 2; i++) EXP[i] = EXP[i - ord];
  if (scanf("%d %d %d", &n, &Delta, &A) != 3) return 1;
  for (int i = 0; i < n; i++) { unsigned a, b; if (scanf("%u %u", &a, &b) != 2) return 1; al[i] = (fe)a; yy[i] = (fe)b; }
  K = Delta + 1;
  dfs(0, 0);
  fprintf(stderr, "members %ld\n", count);
  return 0;
}
