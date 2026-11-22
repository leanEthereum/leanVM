// Researcher 37: translation profile of the members of a list, and periods of the triple functions.
//
//   37_profile N k T seed word [args] [pert m]
//
// Domain: a random N-dimensional subspace of GF(2^64) (leanVM modulus), basis from xorshift(seed), n = 2^N <= 32
// in practice (the enumeration costs C(n - T + k, k) interpolations). Point p is sum of basis[i] over the bits of p.
// Words:
//   xl j e   w = X^e L_W(X), W = span of the first j basis vectors (the 5n/8 family of notes 02 and 05 at rate 1/2:
//            j = N - 3, e = n/2, k = n/2 + 1 (degree <= n/2), T = 5n/8; with k = n/2 the strict tops only)
//   pow e    w = X^e (flats at rate 1/4: e = 2k - 1, T = 2k - 1)
//   rand     random word
// "pert m" replaces w at m random points by random values (the perturbation of note 37, Proposition 2.1).
//
// Output:
//   1. the list size at agreement >= T and the histogram of |S|;
//   2. per member: |Stab(S)| (the a with S + a = S, including 0) and sigma = max over a != 0 of |S n (S + a)|,
//      as a histogram of (|S|, |Stab|, sigma);
//   3. per direction a != 0: the number of members with S + a = S and with |S n (S + a)| >= T (a multiple of 2);
//   4. for NPAIRS (environment, default 24) random pairs (i, j) of members: over all l, the histogram of |Pi(xi_l)|, xi_l = (c_l - c_i)/(c_j - c_i)
//      (periods tested at 3 random points of GF(2^64)); "collinear" counts constant xi_l. With STABMIN=s in the
//      environment the pairs are drawn among the members with |Stab(S)| >= s.
#include "02_gf.h"
#define MAXN 64
#define MAXK 32
static int N, n, k, T;
static u64 pts[MAXN], invd[MAXN][MAXN], W[MAXN];
static u64 rs;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { u64 mask; int agree; u64 cf[MAXK]; unsigned char idx[MAXK]; } member;
static member *mem; static size_t nmem, capmem;
static int idx[MAXN]; static u64 cf[MAXN];

static void leaf(void) {
  u64 mask = 0; int agree = 0, last = idx[k - 1];
  for (int p = 0; p < n; p++) {
    u64 x = pts[p], v = cf[k - 1];
    for (int i = k - 2; i >= 0; i--) v = gmul(v, x ^ pts[idx[i]]) ^ cf[i];
    if (v == W[p]) { mask |= 1ull << p; agree++; }
    else if (n - p - 1 + agree < T) return;
  }
  u64 chosen = 0; for (int i = 0; i < k; i++) chosen |= 1ull << idx[i];
  u64 below = mask & ((last == 63) ? ~0ull : ((1ull << (last + 1)) - 1));
  if (below != chosen || agree < T) return;
  if (nmem == capmem) { capmem = capmem * 2 + 1024; mem = realloc(mem, capmem * sizeof(member)); }
  member *m = &mem[nmem++]; m->mask = mask; m->agree = agree;
  for (int i = 0; i < k; i++) { m->cf[i] = cf[i]; m->idx[i] = (unsigned char)idx[i]; }
}
static void dfs(int j, int start) {
  if (j == k) { leaf(); return; }
  int lim = n - T + j;
  for (int p = start; p <= lim && p < n; p++) {
    u64 x = pts[p], v = 0, nb = 1;
    if (j > 0) { v = cf[j - 1]; for (int i = j - 2; i >= 0; i--) v = gmul(v, x ^ pts[idx[i]]) ^ cf[i]; }
    for (int i = 0; i < j; i++) nb = gmul(nb, invd[p][idx[i]]);
    cf[j] = gmul(v ^ W[p], nb); idx[j] = p;
    dfs(j + 1, p + 1);
  }
}
static u64 eval(const member *m, u64 x) {
  u64 v = m->cf[k - 1];
  for (int i = k - 2; i >= 0; i--) v = gmul(v, x ^ pts[m->idx[i]]) ^ m->cf[i];
  return v;
}
static u64 shift_mask(u64 mask, int a) { // S + a: point p goes to p ^ a
  u64 r = 0; for (int p = 0; p < n; p++) if (mask >> p & 1) r |= 1ull << (p ^ a); return r;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: 37_profile N k T seed word [args] [pert m]\n"); return 1; }
  gf_init(64, 0x1b);
  N = atoi(argv[1]); n = 1 << N; k = atoi(argv[2]); T = atoi(argv[3]);
  rs = 88172645463325252ull ^ (strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ull); for (int i = 0; i < 20; i++) rnd();
  u64 basis[8]; for (int i = 0; i < N; i++) basis[i] = rnd();
  for (int p = 0; p < n; p++) { pts[p] = 0; for (int i = 0; i < N; i++) if (p >> i & 1) pts[p] ^= basis[i]; }
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) invd[i][j] = ginv(pts[i] ^ pts[j]);
  int ai = 6;
  if (!strcmp(argv[5], "xl")) {
    int j = atoi(argv[ai++]), e = atoi(argv[ai++]);
    for (int p = 0; p < n; p++) { u64 x = pts[p], v = gpow(x, e); for (int u = 0; u < (1 << j); u++) v = gmul(v, x ^ pts[u]); W[p] = v; }
  } else if (!strcmp(argv[5], "pow")) {
    int e = atoi(argv[ai++]); for (int p = 0; p < n; p++) W[p] = gpow(pts[p], e);
  } else for (int p = 0; p < n; p++) W[p] = rnd();
  if (ai + 1 < argc && !strcmp(argv[ai], "pert")) {
    int m = atoi(argv[ai + 1]); u64 used = 0;
    printf("perturbed points:");
    while (m > 0) { int p = rnd() % n; if (used >> p & 1) continue; used |= 1ull << p; W[p] = rnd(); m--; printf(" %d", p); }
    printf("\n");
  }
  dfs(0, 0);
  printf("N=%d n=%d k=%d T=%d: list size %zu\n", N, n, k, T, nmem);
  long hist[MAXN + 1] = {0}; for (size_t i = 0; i < nmem; i++) hist[mem[i].agree]++;
  printf("agreement histogram:"); for (int a = T; a <= n; a++) if (hist[a]) printf(" %d:%ld", a, hist[a]); printf("\n");
  // 2. per member
  static long prof[MAXN + 1][MAXN + 1][MAXN + 1];
  int *stabs = malloc((nmem + 1) * sizeof(int));
  long *inv_a = calloc(n, sizeof(long)), *near_a = calloc(n, sizeof(long)); long any_inv = 0, any_near = 0;
  for (size_t i = 0; i < nmem; i++) {
    int stab = 1, sig = 0, nr = 0;
    for (int a = 1; a < n; a++) {
      int c = __builtin_popcountll(mem[i].mask & shift_mask(mem[i].mask, a));
      if (c == mem[i].agree) { stab++; inv_a[a]++; }
      if (c >= T) { near_a[a]++; nr = 1; }
      if (c > sig) sig = c;
    }
    prof[mem[i].agree][stab][sig]++; any_inv += stab > 1; any_near += nr; stabs[i] = stab;
  }
  printf("members (|S|, |Stab(S)|, sigma = max_a |S n (S+a)|) : count\n");
  for (int a = T; a <= n; a++) for (int s = 1; s <= n; s++) for (int g = 0; g <= n; g++) if (prof[a][s][g]) printf("  (%d, %d, %d) : %ld\n", a, s, g, prof[a][s][g]);
  printf("members with a nonzero exact period: %ld of %zu; with some a such that |S n (S+a)| >= T: %ld\n", any_inv, nmem, any_near);
  long mx = 0, sum = 0; for (int a = 1; a < n; a++) { if (inv_a[a] > mx) mx = inv_a[a]; sum += inv_a[a]; }
  printf("per direction: max number of a-invariant members %ld, sum over a %ld\n", mx, sum);
  // 4. periods of triple functions
  if (nmem >= 3) {
    u64 tp[3]; for (int q = 0; q < 3; q++) tp[q] = rnd();
    u64 *val = malloc(nmem * 3 * n * sizeof(u64)); // val[m][q][a] = c_m(tp[q] + pts[a])
    for (size_t m = 0; m < nmem; m++) for (int q = 0; q < 3; q++) for (int a = 0; a < n; a++) val[(m * 3 + q) * n + a] = eval(&mem[m], tp[q] ^ pts[a]);
    long tot[MAXN + 2] = {0}, totc = 0, best_periodic = 0; int want = getenv("NPAIRS") ? atoi(getenv("NPAIRS")) : 24; int npairs = nmem * (nmem - 1) / 2 < (size_t)want ? (int)(nmem * (nmem - 1) / 2) : want; long pairs_with = 0;
    int stabmin = getenv("STABMIN") ? atoi(getenv("STABMIN")) : 1; size_t *pool = malloc(nmem * sizeof(size_t)), npool = 0;
    for (size_t i = 0; i < nmem; i++) if (stabs[i] >= stabmin) pool[npool++] = i;
    if (npool < 2) { printf("fewer than two members with |Stab| >= %d\n", stabmin); return 0; }
    if ((size_t)npairs > npool * (npool - 1) / 2) npairs = (int)(npool * (npool - 1) / 2);
    for (int pr = 0; pr < npairs; pr++) {
      size_t i = pool[rnd() % npool], j = pool[rnd() % npool]; if (i == j) { pr--; continue; }
      long h[MAXN + 2] = {0}, hc = 0, periodic = 0;
      for (size_t l = 0; l < nmem; l++) {
        if (l == i || l == j) continue;
        // constant: (c_l - c_i)(t_q) (c_j - c_i)(t_q') = (c_l - c_i)(t_q') (c_j - c_i)(t_q) for q != q'
        u64 A[3], B[3];
        for (int q = 0; q < 3; q++) { A[q] = val[(l * 3 + q) * n] ^ val[(i * 3 + q) * n]; B[q] = val[(j * 3 + q) * n] ^ val[(i * 3 + q) * n]; }
        if (gmul(A[0], B[1]) == gmul(A[1], B[0]) && gmul(A[0], B[2]) == gmul(A[2], B[0])) { hc++; continue; }
        int per = 1;
        for (int a = 1; a < n; a++) {
          int ok = 1;
          for (int q = 0; q < 3 && ok; q++) {
            u64 Aa = val[(l * 3 + q) * n + a] ^ val[(i * 3 + q) * n + a], Ba = val[(j * 3 + q) * n + a] ^ val[(i * 3 + q) * n + a];
            ok = gmul(A[q], Ba) == gmul(Aa, B[q]);
          }
          per += ok;
        }
        h[per]++; periodic += per > 1;
      }
      for (int s = 0; s <= n; s++) tot[s] += h[s]; totc += hc; if (periodic > best_periodic) best_periodic = periodic; pairs_with += periodic > 0;
    }
    printf("triple functions over %d random pairs (i, j) among the %zu members with |Stab| >= %d, all l: collinear %ld;", npairs, npool, stabmin, totc);
    for (int s = 1; s <= n; s++) if (tot[s]) printf(" |Pi|=%d: %ld;", s, tot[s]);
    printf("\n  largest number of l with a nonzero period for one pair: %ld of %zu; pairs with at least one such l: %ld of %d\n", best_periodic, nmem - 2, pairs_with, npairs);
  }
  return 0;
}
