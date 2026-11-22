// Researcher 12. Common-top classes in the formal model, by Walsh keys (Theorem W of note 02 and its converse):
// two T-subsets of F_2^N share e_1..e_t formally, 2^a <= t < 2^(a+1), iff n_phi(S) = n_phi(S') mod 2^(a+1) for all phi.
// mode "ex32 T s":   n = 32, modulus 4 (depths 2 and 3). Enumerates all T-subsets with XOR-sum s (0 or 1),
//                    prints the largest classes and one representative each.
// mode "seed64 hexmask": n = 64, modulus 8 (depths 4..7). Enumerates S0 + RM(2,6), which contains the class of S0,
//                    and prints the class size. Optional third argument: file to dump the members.
// mode "lift hexmask32": prints the lift of a subset of F_2^5 to F_2^6 (preimage under dropping the top bit).
// build: cc -O2 -o 12_class 12_class.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;
#define LO 0x5555555555555555ull
#define HI 0xAAAAAAAAAAAAAAAAull
static u64 addm[32];
static u64 *keys; static u32 *masks; static size_t len, cap;
static int T, S0;
static inline u64 add4(u64 a, u64 b) { return ((a & LO) + (b & LO)) ^ ((a ^ b) & HI); }
static void dfs(int next, int size, u32 mask, int x, u64 key) {
  if (size == T) {
    if (x != S0) return;
    if (len == cap) { cap = cap ? 2 * cap : 1 << 22; keys = realloc(keys, cap * 8); masks = realloc(masks, cap * 4); }
    keys[len] = key; masks[len] = mask; len++; return;
  }
  if (32 - next < T - size) return;
  for (int i = next; i < 32; i++) dfs(i + 1, size + 1, mask | (1u << i), x ^ i, add4(key, addm[i]));
}
static size_t *idx;
static int cmp(const void *a, const void *b) { u64 x = keys[*(const size_t *)a], y = keys[*(const size_t *)b]; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  if (argc >= 4 && !strcmp(argv[1], "ex32")) {
    T = atoi(argv[2]); S0 = atoi(argv[3]);
    for (int x = 0; x < 32; x++) { addm[x] = 0; for (int p = 1; p < 32; p++) if (__builtin_popcount(p & x) & 1) addm[x] |= 1ull << (2 * (p - 1)); }
    dfs(0, 0, 0, 0, 0);
    idx = malloc(len * sizeof(size_t)); for (size_t i = 0; i < len; i++) idx[i] = i;
    qsort(idx, len, sizeof(size_t), cmp);
    size_t best[6] = {0}, rep[6] = {0}, ncl = 0, hist1 = 0;
    for (size_t i = 0; i < len;) {
      size_t j = i; while (j < len && keys[idx[j]] == keys[idx[i]]) j++;
      size_t c = j - i; ncl++; if (c == 1) hist1++;
      for (int b = 0; b < 6; b++) if (c > best[b]) { for (int e = 5; e > b; e--) { best[e] = best[e - 1]; rep[e] = rep[e - 1]; } best[b] = c; rep[b] = idx[i]; break; } else if (c == best[b]) break;
      i = j;
    }
    printf("T=%d sum=%d sets=%zu classes=%zu singletons=%zu\n", T, S0, len, ncl, hist1);
    for (int b = 0; b < 6 && best[b]; b++) printf("  class size %zu rep %08x\n", best[b], masks[rep[b]]);
    return 0;
  }
  if (argc >= 3 && !strcmp(argv[1], "lift")) { u32 m = (u32)strtoul(argv[2], 0, 16); printf("%016llx\n", (unsigned long long)(((u64)m << 32) | m)); return 0; }
  if (argc >= 3 && !strcmp(argv[1], "seed64")) {
    u64 s0 = strtoull(argv[2], 0, 16); FILE *out = argc >= 4 ? fopen(argv[3], "w") : 0;
    u64 H[64]; for (int p = 0; p < 64; p++) { H[p] = 0; for (int x = 0; x < 64; x++) if (__builtin_popcount(p & x) & 1) H[p] |= 1ull << x; }
    u64 basis[22]; int nb = 0; basis[nb++] = ~0ull;
    for (int i = 0; i < 6; i++) basis[nb++] = H[1 << i];
    for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) basis[nb++] = H[1 << i] & H[1 << j];
    int t = __builtin_popcountll(s0), r0[64]; for (int p = 1; p < 64; p++) r0[p] = __builtin_popcountll(s0 & H[p]) & 7;
    u64 q = 0, count = 0;
    for (u64 g = 0; g < (1ull << 22); g++) {
      if (g) q ^= basis[__builtin_ctzll(g)];
      u64 s = s0 ^ q; if (__builtin_popcountll(s) != t) continue;
      int ok = 1; for (int p = 1; p < 64 && ok; p++) ok = (__builtin_popcountll(s & H[p]) & 7) == r0[p];
      if (ok) { count++; if (out) fprintf(out, "%016llx\n", (unsigned long long)s); }
    }
    printf("seed %016llx T=%d class size %llu\n", (unsigned long long)s0, t, (unsigned long long)count);
    return 0;
  }
  fprintf(stderr, "usage: see header\n"); return 1;
}
