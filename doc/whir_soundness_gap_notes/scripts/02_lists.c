// General list sizes on a subspace domain (n <= 64), by exhaustive interpolation.
//
// profile mode:  02_lists profile m modlow n k Tmin  < "pts... then words, one per line (n hex values)"
//   For each word prints hist[a] = number of polynomials of degree < k that agree with it on exactly a points,
//   for a >= Tmin (Tmin > k - 1). Every polynomial is counted once, from the k-subset of its first k agreements,
//   so the cost is C(n - Tmin + k, k) interpolations of n k multiplications each.
// members mode: as profile, but prints the agreement set (hex mask over the points) of every such polynomial.
// climb mode:    02_lists climb m modlow n k T steps seed  < "pts"  (optionally followed by one starting word)
//   Simulated annealing over words: a move sets w(x) to the value at x of the interpolant of a random k-subset
//   (biased to subsets of the agreement set of a current near-list member). Score favours polynomials whose
//   agreement is close to T. Prints the best list size found at agreement >= T and the word.
#include "02_gf.h"
#include <math.h>
#define MAXN 64
static int n, k;
static u64 pts[MAXN], invd[MAXN][MAXN];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

typedef struct { u64 mask; int agree; } member;
static member *mem; static size_t nmem, capmem;
static long hist[MAXN + 1];
static int Tmin;
static u64 *W;
static int idx[MAXN]; static u64 cf[MAXN];

static void leaf(void) {
  u64 mask = 0; int agree = 0, last = idx[k - 1];
  for (int p = 0; p < n; p++) {
    u64 x = pts[p], v = cf[k - 1];
    for (int i = k - 2; i >= 0; i--) v = gmul(v, x ^ pts[idx[i]]) ^ cf[i];
    if (v == W[p]) { mask |= 1ull << p; agree++; }
    else if (n - p - 1 + agree < Tmin) return;
  }
  // first-k property: the chosen subset is exactly the first k agreement points
  u64 chosen = 0; for (int i = 0; i < k; i++) chosen |= 1ull << idx[i];
  u64 below = mask & ((last == 63) ? ~0ull : ((1ull << (last + 1)) - 1));
  if (below != chosen) return;
  if (agree < Tmin) return;
  hist[agree]++;
  if (mem) { if (nmem == capmem) { capmem = capmem * 2 + 1024; mem = realloc(mem, capmem * sizeof(member)); } mem[nmem].mask = mask; mem[nmem].agree = agree; nmem++; }
}
static void dfs(int j, int start) {
  if (j == k) { leaf(); return; }
  int lim = n - Tmin + j; // index of the j-th agreement point is at most this
  for (int p = start; p <= lim && p < n; p++) {
    u64 x = pts[p], v = 0, nb = 1;
    if (j > 0) { v = cf[j - 1]; for (int i = j - 2; i >= 0; i--) v = gmul(v, x ^ pts[idx[i]]) ^ cf[i]; }
    for (int i = 0; i < j; i++) nb = gmul(nb, invd[p][idx[i]]);
    cf[j] = gmul(v ^ W[p], nb); idx[j] = p;
    dfs(j + 1, p + 1);
  }
}
static void oracle(u64 *w) { W = w; memset(hist, 0, sizeof hist); nmem = 0; dfs(0, 0); }

static u64 interp_at(u64 *w, int *I, int target) { // value at pts[target] of the interpolant of w on I (|I| = k)
  u64 r = 0, x = pts[target];
  for (int a = 0; a < k; a++) {
    u64 num = w[I[a]];
    for (int b = 0; b < k; b++) if (b != a) num = gmul(gmul(num, x ^ pts[I[b]]), invd[I[a]][I[b]]);
    r ^= num;
  }
  return r;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "see header\n"); return 1; }
  int climb = !strcmp(argv[1], "climb"), members = !strcmp(argv[1], "members");
  gf_init(atoi(argv[2]), strtoull(argv[3], 0, 16));
  n = atoi(argv[4]); k = atoi(argv[5]);
  for (int i = 0; i < n; i++) if (scanf("%llx", (unsigned long long *)&pts[i]) != 1) return 1;
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) invd[i][j] = ginv(pts[i] ^ pts[j]);
  u64 w[MAXN];
  if (!climb) {
    Tmin = atoi(argv[6]);
    for (;;) {
      for (int i = 0; i < n; i++) if (scanf("%llx", (unsigned long long *)&w[i]) != 1) return 0;
      if (members && !mem) { mem = malloc(sizeof(member)); capmem = 1; }
      oracle(w);
      if (members) for (size_t i = 0; i < nmem; i++) printf("%llx ", (unsigned long long)mem[i].mask);
      else for (int a = Tmin; a <= n; a++) if (hist[a]) printf("%d:%ld ", a, hist[a]);
      printf("\n"); fflush(stdout);
    }
  }
  int T = atoi(argv[6]); long steps = atol(argv[7]); rs ^= strtoull(argv[8], 0, 10) * 0x9E3779B97F4A7C15ull; for (int i = 0; i < 20; i++) rnd();
  Tmin = T - 2 > k ? T - 2 : k + 1; if (Tmin > T) Tmin = T;
  mem = malloc(sizeof(member)); capmem = 1;
  int have = 1;
  for (int i = 0; i < n; i++) if (scanf("%llx", (unsigned long long *)&w[i]) != 1) { have = 0; break; }
  u64 mask_m = GF_M == 64 ? ~0ull : ((1ull << GF_M) - 1);
  if (!have) for (int i = 0; i < n; i++) w[i] = rnd() & mask_m;
  #define SCORE() ({ double s = 0; for (int a = Tmin; a <= n; a++) s += hist[a] * (a >= T ? 100.0 : (a == T - 1 ? 6.0 : 1.0)); s; })
  oracle(w); double cur = SCORE(); long best = 0; for (int a = T; a <= n; a++) best += hist[a];
  u64 bestw[MAXN]; memcpy(bestw, w, sizeof w);
  for (long st = 0; st < steps; st++) {
    double temp = 30.0 * (1.0 - (double)st / steps) + 0.5;
    int I[MAXN], x;
    u64 pool = ~0ull >> (64 - n);
    if (nmem && (rnd() & 3)) pool = mem[rnd() % nmem].mask; // subset of a near-list member's agreement set
    int cnt = __builtin_popcountll(pool), sel[MAXN], c = 0;
    for (int p = 0; p < n; p++) if (pool >> p & 1) sel[c++] = p;
    for (int i = 0; i < k; i++) { int j = i + rnd() % (cnt - i); int t = sel[i]; sel[i] = sel[j]; sel[j] = t; I[i] = sel[i]; }
    u64 used = 0; for (int i = 0; i < k; i++) used |= 1ull << I[i];
    do x = rnd() % n; while (pool >> x & 1 && cnt > k ? 0 : (used >> x & 1));
    if (used >> x & 1) continue;
    u64 old = w[x], nv = interp_at(w, I, x);
    if (nv == old) continue;
    w[x] = nv; oracle(w); double s = SCORE();
    if (s >= cur || exp((s - cur) / temp) * 18446744073709551615.0 > (double)rnd()) {
      cur = s; long L = 0; for (int a = T; a <= n; a++) L += hist[a];
      if (L > best) { best = L; memcpy(bestw, w, sizeof w); }
    } else { w[x] = old; oracle(w); }
  }
  printf("best %ld :", best); for (int i = 0; i < n; i++) printf(" %llx", (unsigned long long)bestw[i]); printf("\n");
  return 0;
}
