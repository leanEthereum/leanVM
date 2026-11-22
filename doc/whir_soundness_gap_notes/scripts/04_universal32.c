// Researcher 04. Common-top classes for n = 32 in an (almost) generic model: T-subsets of a 5-dimensional
// F_2-subspace D of K = GF(2^64) are keyed on (e_1..e_m) computed in TWO independent random embeddings of D
// (two random bases), so that the key is injective on Sym^j(D) for j <= 4 (70 monomials, 128 bits).
// With basis mode "poly" it uses the single real embedding D = span(1, x, .., x^4) instead.
// For every class with at least two members it checks the conclusions of Corollary 2.5 of the report
// (04-list-bounds-beyond-johnson.md, tables of sections 2.7 and 3.3):
//   n_phi(S) = n_phi(S') mod 2^(a+1) for all 31 nonzero functionals phi (2^a <= m < 2^(a+1)),
//   and, when a = N - 3 and T != 16, that |S ^ S'| = 16 and S ^ S' is an affine hyperplane.
// usage: 04_universal32 T m mode seed     (mode: 0 = two random bases, 1 = poly basis)
// build: cc -O2 -o 04_universal32 04_universal32.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;

#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
#include <arm_neon.h>
static inline u64 mul64(u64 a, u64 b) {
  poly128_t p = vmull_p64(a, b);
  u64 lo = (u64)p, hi = (u64)(p >> 64);
  poly128_t q = vmull_p64(hi, 0x1b);
  lo ^= (u64)q;
  lo ^= (u64)vmull_p64((u64)(q >> 64), 0x1b);
  return lo;
}
#else
static inline u64 mul64(u64 a, u64 b) {
  u64 r = 0;
  for (int i = 0; i < 64; i++) { if (b & 1) r ^= a; b >>= 1; a = (a << 1) ^ ((a >> 63) ? 0x1b : 0); }
  return r;
}
#endif

#define MMAX 8
static int T, M, nemb;
static u64 pts[2][32];
typedef struct { u64 key; u32 mask; } rec;
static rec *buf; static size_t len, cap;
static int sigma;
static u64 seedstate;
static u32 hmask[32];
static u64 rnd(void) { seedstate ^= seedstate << 13; seedstate ^= seedstate >> 7; seedstate ^= seedstate << 17; return seedstate; }

static void dfs(int next, int size, u32 mask, int x, u64 e[2][MMAX + 1]) {
  if (size == T) {
    if (x != sigma) return;
    u64 h = 0x9e3779b97f4a7c15ull;
    for (int b = 0; b < nemb; b++) for (int j = 1; j <= M; j++) { h ^= e[b][j]; h *= 0xff51afd7ed558ccdull; h ^= h >> 29; }
    if (len == cap) { cap = cap ? 2 * cap : 1 << 20; buf = realloc(buf, cap * sizeof(rec)); }
    buf[len].key = h; buf[len].mask = mask; len++;
    return;
  }
  if (32 - next < T - size) return;
  for (int i = next; i < 32; i++) {
    u64 f[2][MMAX + 1];
    for (int b = 0; b < nemb; b++) {
      f[b][0] = 1;
      for (int j = 1; j <= M; j++) f[b][j] = e[b][j] ^ mul64(e[b][j - 1], pts[b][i]);
    }
    dfs(i + 1, size + 1, mask | (1u << i), x ^ i, f);
  }
}
static int cmp(const void *a, const void *b) { u64 x = ((const rec *)a)->key, y = ((const rec *)b)->key; return x < y ? -1 : x > y; }

int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: T m mode seed\n"); return 1; }
  T = atoi(argv[1]); M = atoi(argv[2]); int mode = atoi(argv[3]); seedstate = strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1Dull + 1;
  nemb = mode ? 1 : 2;
  for (int b = 0; b < nemb; b++) {
    u64 basis[5];
    for (int i = 0; i < 5; i++) basis[i] = mode ? (1ull << i) : rnd();
    for (int i = 0; i < 32; i++) { pts[b][i] = 0; for (int j = 0; j < 5; j++) if (i >> j & 1) pts[b][i] ^= basis[j]; }
  }
  for (int phi = 0; phi < 32; phi++) { hmask[phi] = 0; for (int x = 0; x < 32; x++) if (__builtin_parity(x & phi)) hmask[phi] |= 1u << x; }
  int a = 0; while ((2 << a) <= M) a++;          // 2^a <= M < 2^(a+1)
  int modulus = 2 << a;
  size_t best = 0, nbest = 0, nclasses = 0, pairs = 0, badcong = 0, badhyp = 0;
  size_t hist[40]; memset(hist, 0, sizeof hist);
  u32 bestmask[64]; int nb = 0;
  for (sigma = 0; sigma < 32; sigma++) {
    len = 0;
    u64 e[2][MMAX + 1]; memset(e, 0, sizeof e); e[0][0] = e[1][0] = 1;
    dfs(0, 0, 0, 0, e);
    qsort(buf, len, sizeof(rec), cmp);
    size_t s = 0;
    while (s < len) {
      size_t t = s + 1;
      while (t < len && buf[t].key == buf[s].key) t++;
      size_t c = t - s;
      if (c >= 2) {
        nclasses++;
        if (c < 40) hist[c]++;
        if (c > best) { best = c; nbest = 1; nb = c < 64 ? (int)c : 64; for (int i = 0; i < nb; i++) bestmask[i] = buf[s + i].mask; }
        else if (c == best) nbest++;
        // congruence: all pairs of the class agree iff the residue vector (n_phi mod modulus)_phi is constant on it
        {
          u64 *rv = malloc(c * sizeof(u64));
          for (size_t i = 0; i < c; i++) {
            u32 A = buf[s + i].mask; u64 h = 0;
            for (int phi = 1; phi < 32; phi++) h = h * 1000003ull + (u64)(__builtin_popcount(A & hmask[phi]) % modulus);
            rv[i] = h;
          }
          size_t same = 0;
          // count pairs with equal residue vectors (sort the hashes)
          for (size_t i = 1; i < c; i++) { u64 v = rv[i]; size_t j = i; while (j > 0 && rv[j - 1] > v) { rv[j] = rv[j - 1]; j--; } rv[j] = v; }
          for (size_t i = 0; i < c;) { size_t j = i; while (j < c && rv[j] == rv[i]) j++; same += (j - i) * (j - i - 1) / 2; i = j; }
          pairs += c * (c - 1) / 2; badcong += c * (c - 1) / 2 - same;
          free(rv);
        }
        if (a == 2 && T != 16 && c <= 4096) for (size_t i = s; i < t; i++) for (size_t j = i + 1; j < t; j++) {
          u32 d = buf[i].mask ^ buf[j].mask; int hyp = 0;
          for (int phi = 1; phi < 32 && !hyp; phi++) if (d == hmask[phi] || d == ~hmask[phi]) hyp = 1;
          if (!hyp) badhyp++;
        }
      }
      s = t;
    }
  }
  printf("T=%d m=%d (k=%d) mode=%s: classes with >= 2 members: %zu, largest %zu (%zu of them), pairs checked %zu, "
         "congruence mod %d violated by %zu pairs", T, M, T - M, mode ? "poly" : "two random embeddings", nclasses, best, nbest, pairs, modulus, badcong);
  if (a == 2 && T != 16) printf(", pairs whose difference is not an affine hyperplane: %zu", badhyp);
  printf("\n  class-size histogram:");
  for (int c = 2; c < 40; c++) if (hist[c]) printf(" %d:%zu", c, hist[c]);
  printf("\n");
  return 0;
}
