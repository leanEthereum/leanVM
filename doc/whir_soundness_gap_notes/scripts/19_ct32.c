// Researcher 19. Exhaustive check of note 19, Theorems 2 and 3, at n = 32 in small fields, where non-formal
// coincidences and deep accidents abound. All s-subsets of a 5-dimensional F_2-subspace D of GF(2^m) are keyed
// on (e_1..e_g) (the real class) and on (n_phi mod 4) (the formal class of the previous level, u = 2).
// For every pair inside (real class) x (previous-level class) it checks: the odd Walsh support Omega is empty or
// has at least 6 points (8 if g >= 6), P_1(Omega) = 0 (and P_3 if g >= 6), the distance is at least 12 (16),
// and it reports the largest such cell against the bound of Theorem 3, the largest real class and the largest
// number of previous-level classes met by one real class (deep accidents).
// usage: 19_ct32 s g m r seed      (seed 0: power shape; m <= 9, g <= 7)
// build: cc -O2 -mcpu=native -o 19_ct32 19_ct32.c
#include "13_gf.h"
#include <math.h>
typedef struct { u64 key, prev; u32 mask; } rec;
static gf_t F; static int S, G; static u64 pts[32], idel[32], idel3[32]; static u32 hm[32];
static rec *buf; static size_t len, cap;
static void dfs(int next, int size, u32 mask, u64 *e) {
  if (size == S) {
    u64 k = 0, p = 0;
    for (int j = 1; j <= G; j++) k = (k << F.m) | e[j];
    for (int phi = 1; phi < 32; phi++) p = (p << 2) | (__builtin_popcount(mask & hm[phi]) & 3);
    if (len == cap) { cap = cap ? 2 * cap : 1 << 22; buf = realloc(buf, cap * sizeof(rec)); if (!buf) exit(1); }
    buf[len++] = (rec){k, p, mask};
    return;
  }
  if (32 - next < S - size) return;
  for (int i = next; i < 32; i++) {
    u64 f[9]; f[0] = 1;
    for (int j = 1; j <= G; j++) f[j] = e[j] ^ gf_mul(&F, e[j - 1], pts[i]);
    dfs(i + 1, size + 1, mask | (1u << i), f);
  }
}
static int cmp(const void *a, const void *b) {
  const rec *x = a, *y = b;
  if (x->key != y->key) return x->key < y->key ? -1 : 1;
  if (x->prev != y->prev) return x->prev < y->prev ? -1 : 1;
  return 0;
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: 19_ct32 s g m r seed\n"); return 1; }
  S = atoi(argv[1]); G = atoi(argv[2]); int m = atoi(argv[3]); u64 r = strtoull(argv[4], 0, 0); int seed = atoi(argv[5]);
  if (G * m > 63 || G > 7) { fprintf(stderr, "key too long\n"); return 1; }
  gf_init(&F, m, r);
  u64 basis[5];
  if (!seed) for (int i = 0; i < 5; i++) basis[i] = 1ull << i;
  else {
    rng_state += 0x1234567ull * seed;
    for (;;) {
      for (int i = 0; i < 5; i++) basis[i] = rnd64() & F.mask;
      int ok = 1; u64 seen[32];
      for (int x = 0; x < 32 && ok; x++) { u64 v = 0; for (int i = 0; i < 5; i++) if (x >> i & 1) v ^= basis[i]; seen[x] = v; for (int y = 0; y < x; y++) if (seen[y] == v) ok = 0; }
      if (ok) break;
    }
  }
  for (int x = 0; x < 32; x++) { pts[x] = 0; for (int i = 0; i < 5; i++) if (x >> i & 1) pts[x] ^= basis[i]; }
  for (int phi = 1; phi < 32; phi++) {
    hm[phi] = 0; u64 d = 1;
    for (int x = 0; x < 32; x++) if (__builtin_popcount(phi & x) & 1) { hm[phi] |= 1u << x; d = gf_mul(&F, d, pts[x]); }
    idel[phi] = d; idel3[phi] = gf_mul(&F, d, gf_sqr(&F, d));   // 1/a_phi and 1/a_phi^3
  }
  u64 e[9]; memset(e, 0, sizeof e); e[0] = 1;
  dfs(0, 0, 0, e);
  qsort(buf, len, sizeof(rec), cmp);
  int zone2 = G >= 6, sm = S <= 16 ? S : 32 - S;
  double rho2 = S * (32.0 - S) / 64.0, bound = zone2 ? (sm == 16 ? 1e30 : 1.0 / ((1 - sm / 16.0) * (1 - sm / 16.0))) : (rho2 < 3 ? 3 / (3 - rho2) : 1e30);
  size_t bestcell = 0, bestreal = 0, bestprev = 0, pairs = 0, viol = 0, whist[40] = {0}, mind = 99, nreal = 0;
  for (size_t a = 0; a < len;) {
    size_t t = a + 1, nprev = 1;
    while (t < len && buf[t].key == buf[a].key) { if (buf[t].prev != buf[t - 1].prev) nprev++; t++; }
    if (t - a > bestreal) bestreal = t - a;
    if (nprev > bestprev) bestprev = nprev;
    if (t - a >= 2) nreal++;
    for (size_t b = a; b < t;) {
      size_t c = b + 1; while (c < t && buf[c].prev == buf[b].prev) c++;
      if (c - b > bestcell) bestcell = c - b;
      for (size_t i = b; i < c; i++) for (size_t j = b; j < i; j++) {
        u32 A = buf[i].mask, B = buf[j].mask; int w = 0; u64 p1 = 0, p3 = 0;
        for (int phi = 1; phi < 32; phi++) {
          int d = __builtin_popcount(A & hm[phi]) - __builtin_popcount(B & hm[phi]);
          if (d & 3) { viol++; continue; }
          if (d & 4) { w++; p1 ^= idel[phi]; p3 ^= idel3[phi]; }
        }
        size_t dist = __builtin_popcount(A ^ B);
        pairs++; whist[w]++; if (dist < mind) mind = dist;
        if (p1 || (zone2 && p3)) viol++;
        if (w && w < (zone2 ? 8 : 6)) viol++;
        if (dist < (zone2 ? 16 : 12)) viol++;
      }
      b = c;
    }
    a = t;
  }
  printf("s=%d g=%d m=%d seed=%d sets=%zu real classes>=2: %zu largest real class %zu, most previous-level classes in one real class %zu, largest cell %zu (bound %s%.2f), pairs in cells %zu, min distance %zu, violations %zu, |Omega| histogram:", S, G, m, seed, len, nreal, bestreal, bestprev, bestcell, bound > 1e29 ? "none " : "", bound > 1e29 ? 0 : bound, pairs, mind == 99 ? 0 : mind, viol);
  for (int w = 0; w < 40; w++) if (whist[w]) printf(" %d:%zu", w, whist[w]);
  printf("\n");
  if (viol || (bound < 1e29 && bestcell > (size_t)floor(bound + 1e-9))) { printf("FAILED\n"); return 2; }
  return 0;
}
