// Researcher 12. Class of a seed at n = 128 in the second dyadic range (n_phi mod 16), by enumerating S0 + RM(2,7),
// which contains the class (note 12, Lemma 1.2). Seeds are lifts of subsets of F_2^5: the argument is a 32-bit mask
// and the seed is its preimage under x -> x mod 32. Checks Theorem 5.2 of note 12 at n = 128:
// the lift of cff3c000 (seven cosets of a codimension-4 subspace) must give 105*128 - 965 = 12475,
// and the lift of 58851331 must give 56*128 - 392 = 6776.
// build: cc -O3 -o 12_class128 12_class128.c     usage: 12_class128 hexmask32
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
typedef uint64_t u64;
static inline int pc(u128 v) { return __builtin_popcountll((u64)v) + __builtin_popcountll((u64)(v >> 64)); }
int main(int argc, char **argv) {
  uint32_t m = (uint32_t)strtoul(argv[1], 0, 16);
  u128 s0 = 0; for (int x = 0; x < 128; x++) if ((m >> (x & 31)) & 1) s0 |= (u128)1 << x;
  static u128 H[128]; for (int p = 0; p < 128; p++) { H[p] = 0; for (int x = 0; x < 128; x++) if (__builtin_popcount(p & x) & 1) H[p] |= (u128)1 << x; }
  u128 basis[29]; int nb = 0; basis[nb++] = ~(u128)0;
  for (int i = 0; i < 7; i++) basis[nb++] = H[1 << i];
  for (int i = 0; i < 7; i++) for (int j = i + 1; j < 7; j++) basis[nb++] = H[1 << i] & H[1 << j];
  int t = pc(s0), r0[128]; for (int p = 1; p < 128; p++) r0[p] = pc(s0 & H[p]) & 15;
  // test the functionals in an order that rejects early: single bits first
  int order[127], no = 0; for (int w = 1; w <= 7; w++) for (int p = 1; p < 128; p++) if (__builtin_popcount(p) == w) order[no++] = p;
  u128 q = 0; u64 count = 0;
  for (u64 g = 0; g < (1ull << 29); g++) {
    if (g) q ^= basis[__builtin_ctzll(g)];
    u128 s = s0 ^ q; if (pc(s) != t) continue;
    int ok = 1; for (int i = 0; i < 127 && ok; i++) { int p = order[i]; ok = (pc(s & H[p]) & 15) == r0[p]; }
    count += ok;
  }
  printf("seed lift of %08x, |S| = %d of 128, class size %llu\n", m, t, (unsigned long long)count);
  return 0;
}
