// Researcher 12. Exact multiset-top lists on a generic domain with n = 16, multiplicities <= 2.
// A multiset m on F_2^4 of mass M gives the word-minus-codeword Z_m. By Theorem W of note 02 and its converse,
// multisets of mass M share e_1..e_{M-k} formally iff n_phi(m) agree mod 2^(a+1) for all phi, 2^a <= M-k < 2^(a+1).
// For each (k, T) prints, per mass M, the largest number of such multisets with support >= T (a list of genuine
// codewords of degree < k at agreement T), and checks the parity statement of note 12, Lemma 2.1:
// odd-multiplicity sets of two members differ by an affine function when M-k >= n/8 (and by a constant when >= n/4).
// usage: 12_multiset16 k T      build: cc -O2 -o 12_multiset16 12_multiset16.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef uint64_t u64;
static u64 addm[16];
typedef struct { u64 key; uint32_t m; } rec;
static rec *R; static size_t len;
static int K, T;
static int cmp(const void *a, const void *b) { u64 x = ((const rec *)a)->key, y = ((const rec *)b)->key; return x < y ? -1 : x > y; }
static int affine(int v) { // is the 16-bit truth table v an affine function (including constants)?
  int c = v & 1; if (c) v ^= 0xffff;
  int l = 0; for (int i = 0; i < 4; i++) if ((v >> (1 << i)) & 1) l |= 1 << i;
  for (int x = 0; x < 16; x++) if (((v >> x) & 1) != (__builtin_popcount(x & l) & 1)) return 0;
  return 1;
}
int main(int argc, char **argv) {
  K = atoi(argv[1]); T = atoi(argv[2]);
  for (int x = 0; x < 16; x++) { addm[x] = 0; for (int p = 1; p < 16; p++) if (__builtin_popcount(p & x) & 1) addm[x] |= 1ull << (4 * (p - 1)); }
  R = malloc(sizeof(rec) * 43046721ull);
  for (int M = T; M <= 32; M++) {
    int g = M - K; if (g < 1) continue;
    int a = 0; while ((2 << a) <= g) a++;
    int mod = 2 << a; u64 fm = 0; for (int p = 0; p < 15; p++) fm |= (u64)((mod - 1) & 15) << (4 * p);
    if (mod >= 16) fm = ~0ull >> 4;
    len = 0;
    for (uint32_t c = 0; c < 43046721u; c++) {
      uint32_t t = c, m = 0; int mass = 0, supp = 0; u64 key = 0;
      for (int x = 0; x < 16 && t; x++) { int d = t % 3; t /= 3; if (d) { m |= (uint32_t)d << (2 * x); mass += d; supp++; key += d * addm[x]; } }
      if (mass != M || supp < T) continue;
      // fields are 4 bits and hold n_phi <= 32: reduce each field mod 16 is automatic only if no carry; n_phi <= 16 here
      // (at most 8 points with phi = 1, multiplicity <= 2), and 16 would carry into the next field, so recompute safely:
      u64 kk = 0; for (int p = 1; p < 16; p++) { int s = 0; for (int x = 0; x < 16; x++) if (__builtin_popcount(p & x) & 1) s += (m >> (2 * x)) & 3; kk |= (u64)(s & (mod - 1) & 15) << (4 * (p - 1)); }
      (void)key; (void)fm;
      R[len].key = kk; R[len].m = m; len++;
    }
    qsort(R, len, sizeof(rec), cmp);
    size_t best = 0, bi = 0; long bad = 0;
    for (size_t i = 0; i < len;) {
      size_t j = i; while (j < len && R[j].key == R[i].key) j++;
      if (j - i > best) { best = j - i; bi = i; }
      if (g >= 2 && j - i <= 2000) for (size_t x = i; x < j; x++) for (size_t y = x + 1; y < j; y++) {
        int ox = 0, oy = 0; for (int p = 0; p < 16; p++) { ox |= ((R[x].m >> (2 * p)) & 1) << p; oy |= ((R[y].m >> (2 * p)) & 1) << p; }
        int d = ox ^ oy; if (g >= 4 ? !(d == 0 || d == 0xffff) : !affine(d)) bad++;
      }
      i = j;
    }
    printf("k=%d T=%d M=%d modulus %d: multisets %zu, largest list %zu, parity violations %ld", K, T, M, mod, len, best, bad);
    if (best > 1) { printf("  e.g."); for (size_t x = bi; x < bi + (best < 3 ? best : 3); x++) printf(" %08x", R[x].m); }
    printf("\n");
  }
  return 0;
}
