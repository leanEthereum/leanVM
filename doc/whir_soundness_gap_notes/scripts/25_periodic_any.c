// Researcher 25. Members of periodic words on one generic label domain, all agreement sets (note 25, section 2.7).
//
// Lambda is a random nu-dimensional subspace of GF(2^64) (n = 2^nu labels), Ubar the span of its first j basis
// vectors, M = n / 2^j, and pi = L_Ubar : Lambda -> Lambda_U (M labels). A periodic word is w = f o pi.
// The program enumerates every subset S of Lambda with |S| = T and decides whether there are a polynomial c of
// degree <= kdeg and a function f with c = f o pi on S, other than the trivial ones (c = g o L_Ubar). This is a
// rank computation in the unknowns (coefficients of c, values of f on pi(S)): a solution that is not trivial
// exists iff the null space has dimension > t0 = floor(kdeg / 2^j) + 1.
// When the count of conditions |S| - kdeg - 1 exceeds the dimension M - t0 of the space of periodic words modulo
// codewords, a hit at a random Lambda is necessary for a family that exists for generic (Lambda, Ubar).
//
// cc -O2 -o 25_periodic_any 25_periodic_any.c ;  ./25_periodic_any nu j T kdeg [seed] [part parts]
#include "25_gf.h"
#define MAXN 32
#define MAXC 64

static int nu, jj, n, M, T, kdeg, K1, t0, ncol;
static u64 pts[MAXN];
static int lab[MAXN];
static u64 rows[MAXN][MAXC]; // row of each point: powers of y, then the indicator of its label
static long n_leaf, n_hit, n_prim;
static int primitive(void);
static int part, parts;

// echelon basis: piv[c] = index of the basis row with pivot c, or -1
typedef struct { u64 b[MAXN + 2][MAXC]; int pivcol[MAXN + 2]; int rk; } ech;

static int reduce_add(ech *e, const u64 *row) { // returns 1 if independent (added), 0 if dependent
  u64 v[MAXC];
  memcpy(v, row, sizeof(u64) * ncol);
  for (int i = 0; i < e->rk; i++) {
    int c = e->pivcol[i];
    u64 f = v[c];
    if (!f) continue;
    for (int t = c; t < ncol; t++) v[t] ^= gmul(f, e->b[i][t]);
  }
  int c = 0;
  while (c < ncol && !v[c]) c++;
  if (c == ncol) return 0;
  u64 iv = ginv(v[c]);
  for (int t = c; t < ncol; t++) e->b[e->rk][t] = gmul(v[t], iv);
  for (int t = 0; t < c; t++) e->b[e->rk][t] = 0;
  e->pivcol[e->rk] = c;
  e->rk++;
  return 1;
}

static int sel[MAXN];
// Is there a solution (c, f) on S = sel[0..T) with c not periodic under any nonzero element of Ubar?
// The null space is a vector space, so it is enough that for each nonzero eta in Ubar some null vector has
// c(z + eta) != c(z) at some point of Lambda (deg c < n, so periodicity on Lambda is periodicity).
static int primitive(void) {
  int labidx[MAXN], nl = 0, seen[MAXN];
  memset(seen, -1, sizeof seen);
  for (int i = 0; i < T; i++) if (seen[lab[sel[i]]] < 0) seen[lab[sel[i]]] = nl++;
  (void)labidx;
  int nc = K1 + nl;
  static u64 a[MAXN * MAXC], nlv[MAXC * MAXC];
  // null space of the T x nc system = left null space of its transpose
  for (int c = 0; c < nc; c++)
    for (int i = 0; i < T; i++) {
      u64 v;
      if (c < K1) v = rows[sel[i]][c];
      else v = (seen[lab[sel[i]]] == c - K1);
      a[c * T + i] = v;
    }
  int d = left_null(a, nc, T, nlv);
  int U = 1 << jj, ok = 1;
  for (int eta = 1; eta < U && ok; eta++) {
    int nonper = 0;
    for (int t = 0; t < d && !nonper; t++) {
      u64 val[MAXN];
      for (int x = 0; x < n; x++) { u64 v = 0; for (int c = K1 - 1; c >= 0; c--) v = gmul(v, pts[x]) ^ nlv[t * nc + c]; val[x] = v; }
      for (int x = 0; x < n; x++) if (val[x] != val[x ^ eta]) { nonper = 1; break; }
    }
    if (!nonper) ok = 0;
  }
  return ok;
}
static void dfs(ech *e, int depth, int start, unsigned labmask, int nlab) {
  if (depth == T) {
    n_leaf++;
    int nullity = K1 + nlab - e->rk;
    if (nullity > t0) {
      n_hit++;
      int prim = primitive();
      n_prim += prim;
      if (prim && n_prim <= 40) {
        printf("  HIT S =");
        for (int i = 0; i < T; i++) printf(" %d", sel[i]);
        printf("   pattern a_u:");
        int a[MAXN] = {0};
        for (int i = 0; i < T; i++) a[lab[sel[i]]]++;
        for (int u = 0; u < M; u++) printf(" %d", a[u]);
        printf("   nullity %d (trivial %d)\n", nullity, t0);
      }
    }
    return;
  }
  for (int p = start; p <= n - (T - depth); p++) {
    if (depth == 1 && parts > 1 && ((sel[0] * 7 + p) % parts) != part) continue;
    int save = e->rk;
    int newlab = !(labmask >> lab[p] & 1);
    int ind = reduce_add(e, rows[p]);
    // nullity now: K1 + nlab' - rk. It can only decrease later by one per added point, and the final value
    // must exceed t0. A new label keeps it, a dependent row keeps it, an independent old label lowers it.
    int nl2 = nlab + newlab;
    int nullity = K1 + nl2 - e->rk;
    sel[depth] = p;
    // remaining points: T - depth - 1. Best case they are all new labels or dependent.
    if (nullity > t0) dfs(e, depth + 1, p + 1, labmask | 1u << lab[p], nl2);
    e->rk = save;
    (void)ind;
  }
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: %s nu j T kdeg [seed] [part parts]\n", argv[0]); return 1; }
  nu = atoi(argv[1]); jj = atoi(argv[2]); T = atoi(argv[3]); kdeg = atoi(argv[4]);
  if (argc > 5) { rng_s = strtoull(argv[5], 0, 0); for (int i = 0; i < 20; i++) rnd(); }
  part = argc > 7 ? atoi(argv[6]) : 0; parts = argc > 7 ? atoi(argv[7]) : 1;
  n = 1 << nu; M = n >> jj; K1 = kdeg + 1; t0 = (kdeg >> jj) + 1; ncol = K1 + M;
  u64 bas[6];
  for (int i = 0; i < nu; i++) bas[i] = rnd();
  for (int x = 0; x < n; x++) { pts[x] = 0; for (int i = 0; i < nu; i++) if (x >> i & 1) pts[x] ^= bas[i]; lab[x] = x >> jj; }
  // check that the label is L_Ubar: points with equal x >> jj differ by an element of Ubar = span(bas[0..j-1]). True by construction.
  for (int x = 0; x < n; x++) {
    u64 pw = 1;
    for (int c = 0; c < K1; c++) { rows[x][c] = pw; pw = gmul(pw, pts[x]); }
    for (int u = 0; u < M; u++) rows[x][K1 + u] = (u == lab[x]);
  }
  printf("nu=%d (n=%d labels), j=%d (M'=%d), |S|=%d (%.4f), degree <= %d, trivial dimension %d, part %d/%d\n", nu, n, jj, M, T, (double)T / n, kdeg, t0, part, parts);
  printf("conditions %d against %d dimensions of periodic words modulo codewords\n", T - K1, M - t0);
  static ech e;
  e.rk = 0;
  dfs(&e, 0, 0, 0, 0);
  printf("subsets with a nontrivial solution: %ld, of which with a solution periodic under no element of Ubar: %ld\n", n_hit, n_prim);
  return 0;
}
