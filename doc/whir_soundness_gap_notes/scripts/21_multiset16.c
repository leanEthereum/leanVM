// Researcher 21 (referee). Multiset tops in the formal model at n = 16 (note 12, Theorems A and A').
// For (k, T) and every mass M in [T, Mmax]: all multisets on F_2^4 of mass M with support >= T (any multiplicities),
// grouped by the Walsh key (n_phi mod 2^(a+1))_phi, a = floor(log2(M - k)); prints the largest class for each mass.
// By Theorem W and its converse a class is exactly a multiset top list of mass M in degree < k on a generic domain.
// Usage: 21_multiset16 k T Mmax        Build: cc -O2 -o 21_multiset16 21_multiset16.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef uint64_t u64;
typedef unsigned __int128 u128;

static int T_, M_, bits_, mod_;
static u128 *keys;
static size_t cnt, cap;
static int mu[16];

static void rec(int x, int mass, int supp) {
  if (supp + (16 - x) < T_) return;
  if (x == 16) {
    if (mass != M_) return;
    u128 k = 0;
    for (int phi = 1; phi < 16; phi++) {
      int c = 0;
      for (int y = 1; y < 16; y++) if (__builtin_popcount(y & phi) & 1) c += mu[y];
      k = (k << bits_) | (unsigned)(c % mod_);
    }
    if (cnt == cap) { cap *= 2; keys = realloc(keys, cap * sizeof(u128)); }
    keys[cnt++] = k;
    return;
  }
  int rest = 16 - x - 1; // points after x; each needed support point costs at least 1
  for (int m = 0; mass + m <= M_; m++) {
    int need = T_ - (supp + (m > 0)) ;
    if (need < 0) need = 0;
    if (need > rest) continue;
    if (mass + m + need > M_) break;
    mu[x] = m;
    rec(x + 1, mass + m, supp + (m > 0));
  }
}
static int cmp(const void *a, const void *b) { u128 x = *(const u128 *)a, y = *(const u128 *)b; return x < y ? -1 : x > y; }

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: 21_multiset16 k T Mmax\n"); return 1; }
  int k = atoi(argv[1]); T_ = atoi(argv[2]); int Mmax = atoi(argv[3]);
  cap = 1 << 20; keys = malloc(cap * sizeof(u128));
  for (M_ = T_; M_ <= Mmax; M_++) {
    int g = M_ - k, a = 0;
    while ((2 << a) <= g) a++;
    mod_ = 2 << a; bits_ = a + 1;
    cnt = 0;
    rec(0, 0, 0);
    qsort(keys, cnt, sizeof(u128), cmp);
    size_t best = 0, nbest = 0;
    for (size_t i = 0; i < cnt;) {
      size_t j = i;
      while (j < cnt && keys[j] == keys[i]) j++;
      if (j - i > best) { best = j - i; nbest = 1; } else if (j - i == best) nbest++;
      i = j;
    }
    printf("k=%d T=%d mass M=%d (g=%d, modulus %d): %zu multisets with support >= T, largest class %zu (x%zu)\n", k, T_, M_, g, mod_, cnt, best, nbest);
    fflush(stdout);
  }
  return 0;
}
