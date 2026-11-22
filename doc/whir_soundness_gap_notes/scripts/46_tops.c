// Referee 46: exhaustive list of a top-type word by enumeration of ALL T-subsets of the domain (n <= 32 in practice).
//
// Word w = X^a Z_B (mass M = a + |B|), codewords of degree < k, agreement >= T. A member is P = w - c, monic of
// degree M, whose coefficients of X^M .. X^k are those of w, with at least T distinct roots in D. For a T-set S
// of roots write P = Z_S h, deg h = r = M - T. With rev(P)(Z) = Z^M P(1/Z): rev(h) = rev(w) / Psi_S mod Z^m',
// m' = M - k + 1, Psi_S = prod (1 + sZ). So S is the set of T roots of a member iff the coefficients of
// Z^(r+1) .. Z^(m'-1) of rev(w)/Psi_S vanish, and then h is determined. No theory of the notes is used: h may
// have roots anywhere. Each member is reported once, from the T-subset of its roots in D with smallest indices.
//
// cc -O2 -o 46_tops 46_tops.c -lpthread
// ./46_tops N seed k T pow M | xlw a j | xb a hexmask   [dump file] [threads t]
//   seed 0: the real shape span(1, x, .., x^(N-1)); xlw: W = span of the first j basis vectors.
#include "46_gf.h"
#include <pthread.h>
#include <stdatomic.h>
#define MAXM 20
static int N, n, K, T, M, mp, r, nthreads = 4;
static u64 pts[64], basis[8], tser[MAXM];
typedef struct { u64 supp, dbl; int out, maxmult; } member;
typedef struct { member *a; size_t len, cap; long leaves, pass; } tctx;
static int ntask; static int (*tasks)[2]; static atomic_int next_task;

static void leaf(tctx *c, u64 mask, const u64 *Q) {
  c->leaves++;
  for (int j = r + 1; j < mp; j++) if (Q[j]) return;
  c->pass++;
  // h = sum_j Q_j X^(r-j), monic of degree r
  u64 h[MAXM]; int deg = r;
  for (int j = 0; j <= r; j++) h[r - j] = Q[j];
  int extra[MAXM], ne = 0;
  for (int i = 0; i < n && deg > 0; i++) {
    for (;;) {
      u64 v = 0; for (int e = deg; e >= 0; e--) v = gmul(v, pts[i]) ^ h[e];
      if (v) break;
      // divide by (X - pts[i])
      u64 q[MAXM];
      q[deg - 1] = h[deg];
      for (int e = deg - 1; e >= 1; e--) q[e - 1] = h[e] ^ gmul(pts[i], q[e]);
      for (int e = 0; e < deg; e++) h[e] = q[e];
      deg--; extra[ne++] = i;
      if (deg == 0) break;
    }
  }
  int top = 63 - __builtin_clzll(mask);
  int mult[64]; for (int i = 0; i < n; i++) mult[i] = (mask >> i) & 1;
  for (int e = 0; e < ne; e++) {
    if (!((mask >> extra[e]) & 1) && extra[e] < top) return; // found from a smaller T-subset
    mult[extra[e]]++;
  }
  member m; m.supp = 0; m.dbl = 0; m.out = deg; m.maxmult = 0;
  for (int i = 0; i < n; i++) {
    if (mult[i]) m.supp |= 1ULL << i;
    if (mult[i] >= 2) m.dbl |= 1ULL << i;
    if (mult[i] > m.maxmult) m.maxmult = mult[i];
  }
  if (c->len == c->cap) { c->cap = c->cap ? 2 * c->cap : 1024; c->a = realloc(c->a, c->cap * sizeof(member)); }
  c->a[c->len++] = m;
}

static void dfs(tctx *c, int start, int depth, u64 mask, const u64 *Q) {
  if (depth == T) { leaf(c, mask, Q); return; }
  int need = T - depth;
  for (int i = start; i <= n - need; i++) {
    u64 Q2[MAXM], x = pts[i];
    Q2[0] = 1;
    for (int j = 1; j < mp; j++) Q2[j] = Q[j] ^ gmul(x, Q2[j - 1]);
    dfs(c, i + 1, depth + 1, mask | (1ULL << i), Q2);
  }
}

static void *worker(void *arg) {
  tctx *c = arg;
  for (;;) {
    int t = atomic_fetch_add(&next_task, 1);
    if (t >= ntask) break;
    int i1 = tasks[t][0], i2 = tasks[t][1];
    u64 Q1[MAXM], Q2[MAXM];
    Q1[0] = 1; for (int j = 1; j < mp; j++) Q1[j] = tser[j] ^ gmul(pts[i1], Q1[j - 1]);
    Q2[0] = 1; for (int j = 1; j < mp; j++) Q2[j] = Q1[j] ^ gmul(pts[i2], Q2[j - 1]);
    dfs(c, i2 + 1, 2, (1ULL << i1) | (1ULL << i2), Q2);
  }
  return NULL;
}

static int cmpm(const void *a, const void *b) {
  const member *x = a, *y = b;
  if (x->supp != y->supp) return x->supp < y->supp ? -1 : 1;
  if (x->dbl != y->dbl) return x->dbl < y->dbl ? -1 : 1;
  return x->out - y->out;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 46_tops N seed k T pow M | xlw a j | xb a hexmask [dump file] [threads t]\n"); return 1; }
  N = atoi(argv[1]); n = 1 << N; u64 seed = strtoull(argv[2], 0, 10); K = atoi(argv[3]); T = atoi(argv[4]);
  make_domain(N, seed, basis, pts);
  int ai = 5; int a = 0; u64 B = 0;
  if (!strcmp(argv[ai], "pow")) { a = atoi(argv[ai + 1]); ai += 2; }
  else if (!strcmp(argv[ai], "xlw")) { a = atoi(argv[ai + 1]); int j = atoi(argv[ai + 2]); B = (j == 6) ? ~0ULL : ((1ULL << (1 << j)) - 1); ai += 3; }
  else if (!strcmp(argv[ai], "xb")) { a = atoi(argv[ai + 1]); B = strtoull(argv[ai + 2], 0, 16); ai += 3; }
  else { fprintf(stderr, "bad word\n"); return 1; }
  const char *dump = NULL;
  for (; ai < argc; ai++) {
    if (!strcmp(argv[ai], "dump")) dump = argv[++ai];
    else if (!strcmp(argv[ai], "threads")) nthreads = atoi(argv[++ai]);
  }
  M = a + __builtin_popcountll(B); mp = M - K + 1; r = M - T;
  if (mp > MAXM || mp < 2 || r < 0 || r > mp - 1 || T < 2) { fprintf(stderr, "parameters out of range: M=%d m'=%d r=%d\n", M, mp, r); return 1; }
  memset(tser, 0, sizeof tser); tser[0] = 1;
  for (int i = 0; i < n; i++) if ((B >> i) & 1) for (int j = mp - 1; j >= 1; j--) tser[j] ^= gmul(pts[i], tser[j - 1]);
  printf("N=%d seed=%llu k=%d T=%d M=%d m'=%d r=%d conditions=%d\n", N, (unsigned long long)seed, K, T, M, mp, r, mp - 1 - r);
  ntask = 0; tasks = malloc(sizeof(int[2]) * n * n);
  for (int i1 = 0; i1 <= n - T; i1++) for (int i2 = i1 + 1; i2 <= n - T + 1; i2++) { tasks[ntask][0] = i1; tasks[ntask][1] = i2; ntask++; }
  pthread_t th[64]; tctx ctx[64]; memset(ctx, 0, sizeof ctx);
  for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, &ctx[t]);
  size_t tot = 0; long leaves = 0, pass = 0;
  for (int t = 0; t < nthreads; t++) { pthread_join(th[t], NULL); tot += ctx[t].len; leaves += ctx[t].leaves; pass += ctx[t].pass; }
  member *all = malloc((tot + 1) * sizeof(member)); size_t p = 0;
  for (int t = 0; t < nthreads; t++) { memcpy(all + p, ctx[t].a, ctx[t].len * sizeof(member)); p += ctx[t].len; }
  qsort(all, tot, sizeof(member), cmpm);
  size_t dup = 0; for (size_t i = 1; i < tot; i++) if (!cmpm(&all[i - 1], &all[i])) dup++;
  printf("T-subsets examined %ld, passing %ld, members %zu (duplicates %zu)\n", leaves, pass, tot, dup);
  // table: (support, number of points of multiplicity >= 2, largest multiplicity, roots outside D) : count
  long tab[65][8][8]; memset(tab, 0, sizeof tab); int tabmm[65][8][8]; memset(tabmm, 0, sizeof tabmm);
  for (size_t i = 0; i < tot; i++) {
    int s = __builtin_popcountll(all[i].supp), d = __builtin_popcountll(all[i].dbl), o = all[i].out;
    if (d > 7) d = 7; if (o > 7) o = 7;
    tab[s][d][o]++; if (all[i].maxmult > tabmm[s][d][o]) tabmm[s][d][o] = all[i].maxmult;
  }
  for (int s = 0; s <= 64; s++) for (int d = 0; d < 8; d++) for (int o = 0; o < 8; o++) if (tab[s][d][o])
    printf("  agreement %d, multiple points %d (largest multiplicity %d), roots outside D %d : %ld\n", s, d, tabmm[s][d][o], o, tab[s][d][o]);
  if (dump) {
    FILE *f = fopen(dump, "w");
    for (size_t i = 0; i < tot; i++) fprintf(f, "%016llx %016llx %d\n", (unsigned long long)all[i].supp, (unsigned long long)all[i].dbl, all[i].out);
    fclose(f);
  }
  return 0;
}
