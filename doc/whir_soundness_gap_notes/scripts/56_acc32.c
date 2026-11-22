// Researcher 56. Exhaustive test of the all-digit stratum count (56-witt-real-field.md, Theorem 3) at n = 32.
// All p-subsets S of a 5-dimensional F_2-subspace D of GF(2^m) are keyed on (e_1..e_G) and on the hyperplane
// counts n_phi(S) modulo 4 and modulo 8. A pair (S, S') has Walsh level r when n_phi(S) = n_phi(S') modulo
// 2^(r-1) for all phi and not modulo 2^r. For every level r = 2, 3, 4 and every depth g <= G the program counts
// the pairs of level exactly r that share e_1..e_g and prints the count against
//     (pairs of level r) * 2^(-m C_g(r)),   C_g(r) = #{0 <= i < g : wt(i) >= r - 1},
// and against the count that ignores the strata of the later blocks, 2^(-m (g - 2^(r-1) + 1)).
// It also prints one pair of level 3 with the longest common top found, for a direct check of deg(Z_S - Z_S').
// usage: 56_acc32 p G m r seed      (modulus x^m + r; seed 0: D = span(1, x, .., x^4); G m <= 128)
// build: cc -O2 -mcpu=native -o 56_acc32 56_acc32.c
#include "13_gf.h"
#include <math.h>
typedef struct { u64 k0, k1, l3; u32 c2, mask; } rec;
static gf_t F; static int P, G; static u64 pts[32]; static u32 hm[32];
static rec *buf; static size_t len, cap;

static void emit(u32 mask, const u64 *e, u32 c0, u32 c1, u32 c2) {
  // e_1 in the top bits of the 128-bit key (k1 high, k0 low)
  unsigned __int128 k = 0;
  for (int j = 1; j <= G; j++) k = (k << F.m) | e[j];
  k <<= 128 - G * F.m;
  if (len == cap) { cap = cap ? 2 * cap : 1 << 22; buf = realloc(buf, cap * sizeof(rec)); if (!buf) exit(1); }
  buf[len++] = (rec){(u64)k, (u64)(k >> 64), (u64)c0 | (u64)c1 << 32, c2, mask};
}
static void dfs(int next, int size, u32 mask, const u64 *e, u32 c0, u32 c1, u32 c2) {
  if (size == P) { emit(mask, e, c0, c1, c2); return; }
  if (32 - next < P - size) return;
  for (int i = next; i < 32; i++) {
    u64 f[17]; f[0] = 1;
    for (int j = 1; j <= G; j++) f[j] = e[j] ^ gf_mul(&F, e[j - 1], pts[i]);
    u32 M = hm[i], carry = c0 & M, carry2 = c1 & carry;
    dfs(i + 1, size + 1, mask | (1u << i), f, c0 ^ M, c1 ^ carry, c2 ^ carry2);
  }
}
static int cmp_l(const void *a, const void *b) {
  const rec *x = a, *y = b;
  if (x->l3 != y->l3) return x->l3 < y->l3 ? -1 : 1;
  if (x->c2 != y->c2) return x->c2 < y->c2 ? -1 : 1;
  return 0;
}
static int cmp_k(const void *a, const void *b) {
  const rec *x = a, *y = b;
  if (x->k1 != y->k1) return x->k1 < y->k1 ? -1 : 1;
  if (x->k0 != y->k0) return x->k0 < y->k0 ? -1 : 1;
  return 0;
}
// number of leading coefficients e_1.. on which two records agree (G if all)
static inline int common(const rec *x, const rec *y) {
  u64 d1 = x->k1 ^ y->k1, d0 = x->k0 ^ y->k0;
  int lz = d1 ? __builtin_clzll(d1) : d0 ? 64 + __builtin_clzll(d0) : 128;
  int c = lz / F.m;
  return c > G ? G : c;
}
static int Ccount(int g, int r) { int c = 0; for (int i = 0; i < g; i++) if (__builtin_popcount(i) >= r - 1) c++; return c; }

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: 56_acc32 p G m r seed\n"); return 1; }
  P = atoi(argv[1]); G = atoi(argv[2]); int m = atoi(argv[3]); u64 r = strtoull(argv[4], 0, 0); int seed = atoi(argv[5]);
  if (G * m > 128 || G > 16 || G >= P + 1) { fprintf(stderr, "bad parameters\n"); return 1; }
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
  for (int x = 0; x < 32; x++) { u64 v = 0; for (int i = 0; i < 5; i++) if (x >> i & 1) v ^= basis[i]; pts[x] = v; }
  for (int x = 0; x < 32; x++) { u32 M = 0; for (int phi = 1; phi < 32; phi++) if (__builtin_popcount(phi & x) & 1) M |= 1u << phi; hm[x] = M; }
  u64 e0[17] = {1};
  dfs(0, 0, 0, e0, 0, 0, 0);
  printf("n=32 p=%d G=%d GF(2^%d) modulus x^%d+0x%llx %s basis:", P, G, m, m, (unsigned long long)r, seed ? "random" : "power");
  for (int i = 0; i < 5; i++) printf(" %llx", (unsigned long long)basis[i]);
  printf("\n  %zu sets\n", len);

  // levels 3 and 4: pairs inside the classes modulo 4
  qsort(buf, len, sizeof(rec), cmp_l);
  double P3 = 0, P4 = 0; double A3[18] = {0}, A4[18] = {0};   // A[g] = pairs sharing exactly e_1..e_g (g = G: at least)
  int bestc = -1; u32 bm1 = 0, bm2 = 0; size_t maxcls = 0;
  for (size_t i = 0; i < len;) {
    size_t j = i; while (j < len && buf[j].l3 == buf[i].l3) j++;
    if (j - i > maxcls) maxcls = j - i;
    for (size_t a = i; a < j; a++) for (size_t b = a + 1; b < j; b++) {
      int c = common(&buf[a], &buf[b]);
      if (buf[a].c2 == buf[b].c2) { P4++; A4[c]++; if (c < 7) { fprintf(stderr, "Theorem W violated (level 4)\n"); return 1; } }
      else { P3++; A3[c]++; if (c < 3) { fprintf(stderr, "Theorem W violated (level 3)\n"); return 1; }
             if (c > bestc) { bestc = c; bm1 = buf[a].mask; bm2 = buf[b].mask; } }
    }
    i = j;
  }
  // level 2: all pairs sharing e_1..e_g, by prefix groups
  qsort(buf, len, sizeof(rec), cmp_k);
  double T[18] = {0};                     // T[g] = pairs sharing at least e_1..e_g
  for (int g = 1; g <= G; g++) {
    size_t run = 1;
    for (size_t i = 1; i <= len; i++) {
      if (i < len && common(&buf[i - 1], &buf[i]) >= g) run++;
      else { T[g] += (double)run * (run - 1) / 2; run = 1; }
    }
  }
  double P2 = T[1] - P3 - P4;
  printf("  pairs with equal sum: %.0f; level 2: %.0f, level 3: %.0f, level 4: %.0f; largest class modulo 4: %zu\n", T[1], P2, P3, P4, maxcls);
  printf("  depth g | level | pairs sharing e_1..e_g | C_g(r) | predicted pairs 2^(-m C) | ratio | naive exponent g-2^(r-1)+1 | naive prediction\n");
  for (int g = 2; g <= G; g++) {
    double a3 = 0, a4 = 0;
    for (int c = g; c <= G; c++) { a3 += A3[c]; a4 += A4[c]; }
    double a2 = T[g] - a3 - a4;
    double obs[5] = {0, 0, a2, a3, a4}, tot[5] = {0, 0, P2, P3, P4};
    for (int lev = 2; lev <= 4; lev++) {
      int C = Ccount(g, lev), naive = g - (1 << (lev - 1)) + 1; if (naive < 0) naive = 0;
      if (C == 0 && lev > 2) continue;
      double pred = tot[lev] * pow(2.0, -(double)m * C), npred = tot[lev] * pow(2.0, -(double)m * naive);
      printf("  %7d | %5d | %22.0f | %6d | %24.4g | %5.3f | %26d | %.4g\n", g, lev, obs[lev], C, pred, pred > 0 ? obs[lev] / pred : 0, naive, npred);
    }
  }
  if (bestc >= 0) printf("  example: level-3 pair sharing e_1..e_%d: masks %08x %08x\n", bestc, bm1, bm2);
  return 0;
}
