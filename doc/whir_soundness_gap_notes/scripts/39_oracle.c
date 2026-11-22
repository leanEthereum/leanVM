// Researcher 39: exhaustive list of a top-type word (every polynomial of degree < k, by interpolation as in
// 02_lists.c, in parallel), and for every member the location of the roots of w - c: in D or outside ("phantom").
//
//   39_oracle N k T seed dom word [args] [twist g] [threads t] [dump file] [analyse P R]
//
// dom:  rand (random N-dimensional subspace of GF(2^64), basis from xorshift(seed)) | real (span of 1, x, .., x^(N-1))
// word: xl j e    w = X^e L_W(X), W = span of the first j basis vectors
//       pow e     w = X^e
//       tw j e g  w = (X^e L_W(X)) * g(X), g a random monic polynomial of degree g (a twisted top word)
//       xb e mask w = X^e Z_B(X), B the set of points whose indices are the bits of the hex mask
//       any of these may be followed by "twist g": the word is multiplied by a random monic polynomial of degree g
// n = 2^N <= 64. The cost is C(n - T + k, k) interpolations. Use T > k: with T = k every interpolant is a member and
// all C(n, k) of them are kept in memory. For every member c with agreement set S the program
// computes h = (w - c)/Z_S and the number of roots of h outside D (with multiplicity). Output: a histogram of
// (|S|, deg h, roots of h outside D) with, per line, whether note 39 Theorem S applies
// (deg w - k + 1 >= 2 deg h; for "tw" the phantom part g is common and is removed first).
// "dump file" writes the agreement sets as hex masks, one per line.
// "analyse P R" adds: the period groups of the triple functions xi_l = (c_l - c_i)/(c_j - c_i) (two random
// evaluation points), with the exact minimum over all pairs of B(i, j) = number of l without a nonzero period if
// the list has at most 700 members and over P random pairs otherwise; R greedy runs for a primitive sublist (no
// triple with a nonzero period); and the affine rank of the list over GF(2^64).
#include "02_gf.h"
#include <pthread.h>
#include <stdatomic.h>
#define MAXN 64
#define MAXK 40
static int N, n, k, T, NTH = 4, M, GD;
static u64 pts[MAXN], invd[MAXN][MAXN], W[MAXN], wpoly[2 * MAXN + 8], gpoly[MAXN];
static u64 rs;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { u64 mask; int agree, hdeg, out; u64 *poly; } member;
typedef struct { member *mem; size_t nmem, cap; int idx[MAXN]; u64 cf[MAXN]; } ctx;
static atomic_int next_first;

static void analyse(ctx *c, u64 mask, int agree) {
  // monomial coefficients of the member from its Newton form
  u64 P[2 * MAXN + 8]; memset(P, 0, sizeof P);
  u64 nb[MAXK + 1]; memset(nb, 0, sizeof nb); nb[0] = 1; int nd = 0; // newton basis polynomial prod_{i<j}(X - x_i)
  for (int j = 0; j < k; j++) {
    for (int i = 0; i <= nd; i++) P[i] ^= gmul(c->cf[j], nb[i]);
    u64 x = pts[c->idx[j]]; for (int i = nd + 1; i >= 1; i--) nb[i] = nb[i - 1] ^ gmul(nb[i], x); nb[0] = gmul(nb[0], x); nd++;
  }
  u64 *keep = malloc(k * sizeof(u64)); memcpy(keep, P, k * sizeof(u64));
  for (int i = 0; i <= M; i++) P[i] ^= wpoly[i]; // P = w - c, monic of degree M
  int d = M;
  // remove the common phantom part g (twisted words)
  if (GD) { u64 q[2 * MAXN + 8]; u64 x[2 * MAXN + 8]; memcpy(x, P, sizeof x);
    for (int i = d - GD; i >= 0; i--) { u64 f = x[i + GD]; q[i] = f; for (int j = 0; j <= GD; j++) x[i + j] ^= gmul(f, gpoly[j]); }
    int rem = 0; for (int i = 0; i < GD; i++) if (x[i]) rem = 1;
    if (!rem) { d -= GD; memcpy(P, q, (d + 1) * sizeof(u64)); } }
  // divide by (X - s) for s in S, then by (X - x) for the remaining roots in D
  int hdeg = d - agree;
  for (int p = 0; p < n; p++) if (mask >> p & 1) { u64 x = pts[p], carry = 0; for (int i = d; i >= 0; i--) { u64 t = P[i]; P[i] = carry; carry = t ^ gmul(carry, x); } d--; /* synthetic division, remainder in carry */ }
  int left = d;
  for (int p = 0; p < n; p++) for (;;) {
    if (left == 0) break;
    u64 x = pts[p], v = 0; for (int i = left; i >= 0; i--) v = gmul(v, x) ^ P[i];
    if (v) break;
    u64 carry = 0; for (int i = left; i >= 0; i--) { u64 t = P[i]; P[i] = carry; carry = t ^ gmul(carry, x); } left--;
  }
  if (c->nmem == c->cap) { c->cap = c->cap * 2 + 1024; c->mem = realloc(c->mem, c->cap * sizeof(member)); }
  member *m = &c->mem[c->nmem++]; m->mask = mask; m->agree = agree; m->hdeg = hdeg; m->out = left; m->poly = keep;
}
static void leaf(ctx *c) {
  u64 mask = 0; int agree = 0, last = c->idx[k - 1];
  for (int p = 0; p < n; p++) {
    u64 x = pts[p], v = c->cf[k - 1];
    for (int i = k - 2; i >= 0; i--) v = gmul(v, x ^ pts[c->idx[i]]) ^ c->cf[i];
    if (v == W[p]) { mask |= 1ull << p; agree++; }
    else if (n - p - 1 + agree < T) return;
  }
  u64 chosen = 0; for (int i = 0; i < k; i++) chosen |= 1ull << c->idx[i];
  u64 below = mask & ((last == 63) ? ~0ull : ((1ull << (last + 1)) - 1));
  if (below != chosen || agree < T) return;
  analyse(c, mask, agree);
}
static void dfs(ctx *c, int j, int start) {
  if (j == k) { leaf(c); return; }
  int lim = n - T + j;
  for (int p = start; p <= lim && p < n; p++) {
    u64 x = pts[p], v = 0, nb = 1;
    if (j > 0) { v = c->cf[j - 1]; for (int i = j - 2; i >= 0; i--) v = gmul(v, x ^ pts[c->idx[i]]) ^ c->cf[i]; }
    for (int i = 0; i < j; i++) nb = gmul(nb, invd[p][c->idx[i]]);
    c->cf[j] = gmul(v ^ W[p], nb); c->idx[j] = p;
    dfs(c, j + 1, p + 1);
  }
}
static void *worker(void *arg) {
  ctx *c = arg;
  for (;;) {
    int code = atomic_fetch_add(&next_first, 1); // the first two points (p0 < p1) encoded as p0 * n + p1
    if (code >= n * n) break;
    int p0 = code / n, p1 = code % n;
    if (p1 <= p0 || p0 > n - T || p1 > n - T + 1) continue;
    c->cf[0] = W[p0]; c->idx[0] = p0;
    if (k == 1) { if (p1 == p0 + 1) leaf(c); continue; }
    { u64 x = pts[p1]; c->cf[1] = gmul(c->cf[0] ^ W[p1], invd[p1][p0]); (void)x; c->idx[1] = p1; }
    dfs(c, 2, p1 + 1);
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 39_oracle N k T seed dom word [args] [twist g] [threads t] [dump file] [analyse P R]\n"); return 1; }
  gf_init(64, 0x1b);
  N = atoi(argv[1]); n = 1 << N; k = atoi(argv[2]); T = atoi(argv[3]);
  if (n > MAXN || k > MAXK || k < 2) { fprintf(stderr, "n <= 64, 2 <= k <= %d\n", MAXK); return 1; }
  rs = 88172645463325252ull ^ (strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ull); for (int i = 0; i < 20; i++) rnd();
  u64 basis[8]; for (int i = 0; i < N; i++) basis[i] = rnd();
  if (!strcmp(argv[5], "real")) for (int i = 0; i < N; i++) basis[i] = 1ull << i;
  for (int p = 0; p < n; p++) { pts[p] = 0; for (int i = 0; i < N; i++) if (p >> i & 1) pts[p] ^= basis[i]; }
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) invd[i][j] = ginv(pts[i] ^ pts[j]);
  int ai = 7; memset(wpoly, 0, sizeof wpoly);
  if (!strcmp(argv[6], "xl") || !strcmp(argv[6], "tw")) {
    int j = atoi(argv[ai++]), e = atoi(argv[ai++]);
    wpoly[0] = 1; M = 0;
    for (int u = 0; u < (1 << j); u++) { for (int i = M + 1; i >= 1; i--) wpoly[i] = wpoly[i - 1] ^ gmul(wpoly[i], pts[u]); wpoly[0] = gmul(wpoly[0], pts[u]); M++; }
    for (int i = M; i >= 0; i--) { wpoly[i + e] = wpoly[i]; } for (int i = 0; i < e; i++) wpoly[i] = 0; M += e;
    if (!strcmp(argv[6], "tw")) {
      GD = atoi(argv[ai++]); for (int i = 0; i < GD; i++) gpoly[i] = rnd(); gpoly[GD] = 1;
      u64 t[2 * MAXN + 8]; memset(t, 0, sizeof t); for (int i = 0; i <= M; i++) for (int g = 0; g <= GD; g++) t[i + g] ^= gmul(wpoly[i], gpoly[g]);
      M += GD; memcpy(wpoly, t, sizeof t);
    }
  } else if (!strcmp(argv[6], "pow")) { M = atoi(argv[ai++]); wpoly[M] = 1; }
  else if (!strcmp(argv[6], "xb")) {
    int e = atoi(argv[ai++]); u64 bm = strtoull(argv[ai++], 0, 16); wpoly[0] = 1; M = 0;
    for (int u = 0; u < n; u++) if (bm >> u & 1) { for (int i = M + 1; i >= 1; i--) wpoly[i] = wpoly[i - 1] ^ gmul(wpoly[i], pts[u]); wpoly[0] = gmul(wpoly[0], pts[u]); M++; }
    for (int i = M; i >= 0; i--) { wpoly[i + e] = wpoly[i]; } for (int i = 0; i < e; i++) wpoly[i] = 0; M += e;
  }
  else { fprintf(stderr, "unknown word\n"); return 1; }
  if (ai + 1 < argc && !strcmp(argv[ai], "twist")) { // multiply the word by a random monic g of the given degree
    GD = atoi(argv[ai + 1]); ai += 2; for (int i = 0; i < GD; i++) gpoly[i] = rnd(); gpoly[GD] = 1;
    u64 t[2 * MAXN + 8]; memset(t, 0, sizeof t); for (int i = 0; i <= M; i++) for (int g = 0; g <= GD; g++) t[i + g] ^= gmul(wpoly[i], gpoly[g]);
    M += GD; memcpy(wpoly, t, sizeof t);
  }
  const char *dump = 0; int an_pairs = -1, an_runs = 0;
  for (; ai < argc; ai++) { if (!strcmp(argv[ai], "threads")) NTH = atoi(argv[++ai]); else if (!strcmp(argv[ai], "dump")) dump = argv[++ai]; else if (!strcmp(argv[ai], "analyse")) { an_pairs = atoi(argv[++ai]); an_runs = atoi(argv[++ai]); } }
  for (int p = 0; p < n; p++) { u64 v = 0; for (int i = M; i >= 0; i--) v = gmul(v, pts[p]) ^ wpoly[i]; W[p] = v; }
  pthread_t th[64]; ctx *cs = calloc(NTH, sizeof(ctx));
  for (int t = 0; t < NTH; t++) pthread_create(&th[t], 0, worker, &cs[t]);
  for (int t = 0; t < NTH; t++) pthread_join(th[t], 0);
  size_t tot = 0; static long hist[MAXN + 1][MAXN + 1][MAXN + 1];
  FILE *f = dump ? fopen(dump, "w") : 0;
  for (int t = 0; t < NTH; t++) for (size_t i = 0; i < cs[t].nmem; i++) { member *m = &cs[t].mem[i]; tot++; hist[m->agree][m->hdeg][m->out]++; if (f) fprintf(f, "%llx\n", (unsigned long long)m->mask); }
  if (f) fclose(f);
  printf("N=%d n=%d k=%d T=%d dom=%s word=%s deg w = %d%s: list size %zu\n", N, n, k, T, argv[5], argv[6], M, GD ? " (twisted)" : "", tot);
  int Mtop = M - GD, ktop = k - GD; // after removing the common phantom part: a top word of mass Mtop in degree < ktop
  printf("  (|S|, deg h, roots of h outside D) : count   [Theorem S applies iff %d - %d + 1 >= 2 deg h]\n", Mtop, ktop);
  long viol = 0;
  for (int a = 0; a <= n; a++) for (int h = 0; h <= MAXN; h++) for (int o = 0; o <= MAXN; o++) if (hist[a][h][o]) {
    int applies = Mtop - ktop + 1 >= 2 * h;
    printf("  (%d, %d, %d) : %ld%s\n", a, h, o, hist[a][h][o], applies ? (o ? "   VIOLATION" : "   covered") : (o ? "   not covered, phantom roots" : "   not covered"));
    if (applies && o) viol += hist[a][h][o];
  }
  printf("  members covered by Theorem S with a root outside D: %ld\n", viol);
  if (an_pairs < 0 || tot < 3) return 0;
  // ---------- analysis of the list ----------
  member **L = malloc(tot * sizeof(member *)); size_t nm = 0;
  for (int t = 0; t < NTH; t++) for (size_t i = 0; i < cs[t].nmem; i++) L[nm++] = &cs[t].mem[i];
  u64 tq[2] = {rnd(), rnd()}; u64 *val = malloc(nm * 2 * (size_t)n * sizeof(u64));
  #define VAL(m, q, a) val[((m) * 2 + (q)) * (size_t)n + (a)]
  for (size_t m = 0; m < nm; m++) for (int q = 0; q < 2; q++) for (int a = 0; a < n; a++) { u64 x = tq[q] ^ pts[a], v = 0; for (int i = k - 1; i >= 0; i--) v = gmul(v, x) ^ L[m]->poly[i]; VAL(m, q, a) = v; }
  #define PERIODS(i, j, l, per) do { per = 0; u64 A0 = VAL(l, 0, 0) ^ VAL(i, 0, 0), B0 = VAL(j, 0, 0) ^ VAL(i, 0, 0), A1 = VAL(l, 1, 0) ^ VAL(i, 1, 0), B1 = VAL(j, 1, 0) ^ VAL(i, 1, 0); \
    for (int a = 0; a < n; a++) { if (gmul(VAL(l, 0, a) ^ VAL(i, 0, a), B0) != gmul(A0, VAL(j, 0, a) ^ VAL(i, 0, a))) continue; if (gmul(VAL(l, 1, a) ^ VAL(i, 1, a), B1) != gmul(A1, VAL(j, 1, a) ^ VAL(i, 1, a))) continue; per++; } } while (0)
  long ph[MAXN + 1]; memset(ph, 0, sizeof ph); long bmin = -1, bmax = -1; size_t bi = 0, bj = 0; int exact = nm <= 700;
  long npr = exact ? (long)(nm * (nm - 1) / 2) : an_pairs;
  for (long pr = 0; pr < npr; pr++) {
    size_t i, j;
    if (exact) { static size_t ci = 0, cj = 0; if (pr == 0) { ci = 0; cj = 1; } i = ci; j = cj; if (++cj == nm) { ci++; cj = ci + 1; } }
    else { i = rnd() % nm; j = rnd() % nm; if (i == j) { pr--; continue; } }
    long b = 0; for (size_t l = 0; l < nm; l++) { if (l == i || l == j) continue; int per; PERIODS(i, j, l, per); ph[per]++; b += per == 1; }
    if (bmin < 0 || b < bmin) { bmin = b; bi = i; bj = j; } if (b > bmax) bmax = b;
  }
  printf("triple functions over %s %ld pairs: |Pi(xi_l)| : count =", exact ? "all" : "random", npr); for (int p = 1; p <= n; p++) if (ph[p]) printf(" %d:%ld", p, ph[p]);
  printf(" (%d means collinear)\n  B(i, j) = thirds without a nonzero period: min %ld, max %ld of %zu%s\n", n, bmin, bmax, nm - 2, exact ? " (exact minimum over all pairs)" : " (sampled)");
  (void)bi; (void)bj;
  size_t bestsz = 0;
  for (int run = 0; run < an_runs; run++) {
    size_t *perm = malloc(nm * sizeof(size_t)), *ch = malloc(nm * sizeof(size_t)), nc = 0;
    for (size_t i = 0; i < nm; i++) perm[i] = i;
    for (size_t i = nm - 1; i > 0; i--) { size_t j = rnd() % (i + 1); size_t t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (size_t p = 0; p < nm; p++) { size_t l = perm[p]; int ok = 1;
      for (size_t ia = 0; ia < nc && ok; ia++) for (size_t ib = ia + 1; ib < nc && ok; ib++) { int per; size_t mi = ch[ia], mj = ch[ib]; PERIODS(mi, mj, l, per); if (per > 1) ok = 0; }
      if (ok) ch[nc++] = l; }
    if (nc > bestsz) bestsz = nc;
    free(perm); free(ch);
  }
  if (an_runs) printf("  largest primitive sublist found by %d greedy runs: %zu; generalized Singleton bound: %d\n", an_runs, bestsz, T > k ? (n - k - 1) / (T - k) : -1);
  { u64 (*bas)[MAXK] = malloc(k * sizeof *bas); int *pv = malloc(k * sizeof(int)), rank = 0;
    for (size_t m = 1; m < nm && rank < k; m++) {
      u64 v[MAXK]; for (int i = 0; i < k; i++) v[i] = L[m]->poly[i] ^ L[0]->poly[i];
      for (int b = 0; b < rank; b++) if (v[pv[b]]) { u64 f = v[pv[b]]; for (int i = 0; i <= pv[b]; i++) v[i] ^= gmul(f, bas[b][i]); }
      int top = k - 1; while (top >= 0 && !v[top]) top--;
      if (top < 0) continue;
      u64 iv = ginv(v[top]); for (int i = 0; i < k; i++) bas[rank][i] = i <= top ? gmul(v[i], iv) : 0; pv[rank++] = top;
    }
    printf("  affine rank over GF(2^64): %d (codewords of degree < %d: at most %d)\n", rank, k, k); }
  return 0;
}
