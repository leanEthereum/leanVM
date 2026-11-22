// Researcher 21 (referee). Formal-model class enumerations, by the Walsh criterion only (no field arithmetic).
// A class at modulus M is a set of equal-size subsets of F_2^N with n_phi(S) = |{x in S : phi(x) = 1}| congruent mod M for all phi.
//   classes32 s M        : all s-subsets of F_2^5 (sum 0, and sum 1 if s is even: enough by symmetry), class-size statistics
//   rm2 N M seed c [file]: the class of a seed in F_2^N, N = 5, 6, 7, searched inside seed + RM(2, N); counts the members
//                          invariant under the bottom c bits; optionally dumps the members (hex bit masks)
//                          seed = "cosets:<c>:<l1,l2,...>[+x1,x2,...]" : union of the cosets of the bottom-c-bit subspace with the
//                          given labels, plus optional single points
// Build: cc -O2 -o 21_walsh 21_walsh.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;

static int par(u32 x) { return __builtin_popcount(x) & 1; }

typedef struct { u64 a, b; } key_t;
static int kcmp(const void *x, const void *y) {
  const key_t *p = x, *q = y;
  if (p->a != q->a) return p->a < q->a ? -1 : 1;
  if (p->b != q->b) return p->b < q->b ? -1 : 1;
  return 0;
}

static void classes32(int s, int M) {
  u32 fm[32];
  for (int phi = 1; phi < 32; phi++) {
    fm[phi] = 0;
    for (int x = 0; x < 32; x++) if (par(x & phi)) fm[phi] |= 1u << x;
  }
  u32 col[5];
  for (int j = 0; j < 5; j++) { col[j] = 0; for (int x = 0; x < 32; x++) if (x >> j & 1) col[j] |= 1u << x; }
  int bits = M <= 2 ? 1 : M <= 4 ? 2 : M <= 8 ? 3 : 4;
  for (int target = 0; target <= ((s & 1) ? 0 : 1); target++) {
    size_t cap = 1 << 20, cnt = 0;
    key_t *keys = malloc(cap * sizeof(key_t));
    // (s-1)-subsets A of 32 points, completed by the point x = target ^ xor(A) if x > max(A)
    u64 A = (1ull << (s - 1)) - 1;
    while (A < (1ull << 32)) {
      u32 a = (u32)A;
      int x = target;
      for (int j = 0; j < 5; j++) if (__builtin_popcount(a & col[j]) & 1) x ^= 1 << j;
      int mx = a ? 31 - __builtin_clz(a) : -1;
      if (x > mx) {
        u32 S = a | (1u << x);
        unsigned __int128 k = 0;
        for (int phi = 1; phi < 32; phi++) k = (k << bits) | (unsigned)(__builtin_popcount(S & fm[phi]) % M);
        if (cnt == cap) { cap *= 2; keys = realloc(keys, cap * sizeof(key_t)); }
        keys[cnt].a = (u64)(k >> 64); keys[cnt].b = (u64)k; cnt++;
      }
      if (s == 1) break;
      u64 c = A & -A, r = A + c;
      A = (((r ^ A) >> 2) / c) | r;
    }
    qsort(keys, cnt, sizeof(key_t), kcmp);
    size_t best = 0, nbest = 0, nclass = 0, nmulti = 0, second = 0;
    for (size_t i = 0; i < cnt;) {
      size_t j = i;
      while (j < cnt && kcmp(&keys[i], &keys[j]) == 0) j++;
      size_t sz = j - i;
      nclass++;
      if (sz >= 2) nmulti++;
      if (sz > best) { second = best; best = sz; nbest = 1; }
      else if (sz == best) nbest++;
      else if (sz > second) second = sz;
      i = j;
    }
    printf("classes32 s=%d (T=%d by complement) mod=%d sum=%d: sets=%zu classes=%zu with>=2=%zu largest=%zu (x%zu) next=%zu\n",
           s, 32 - s, M, target, cnt, nclass, nmulti, best, nbest, second);
    free(keys);
  }
}

static u128 parse_seed(const char *spec, int N) {
  u128 S = 0;
  if (!strncmp(spec, "cosets:", 7)) {
    int c = atoi(spec + 7);
    const char *p = strchr(spec + 7, ':') + 1;
    while (*p) {
      int l = (int)strtol(p, (char **)&p, 10);
      for (int y = 0; y < (1 << c); y++) S |= (u128)1 << ((l << c) | y);
      if (*p == ',') p++;
      if (*p == '+') { // extra single points: +x1,x2,...
        p++;
        while (*p) { int x = (int)strtol(p, (char **)&p, 10); S |= (u128)1 << x; if (*p == ',') p++; }
      }
    }
  } else { fprintf(stderr, "bad seed\n"); exit(1); }
  (void)N;
  return S;
}
static int pc128(u128 x) { return __builtin_popcountll((u64)x) + __builtin_popcountll((u64)(x >> 64)); }

static void rm2(int N, int M, const char *spec, int inv_c, const char *dump) {
  FILE *df = dump ? fopen(dump, "w") : NULL;
  int n = 1 << N;
  u128 S0 = parse_seed(spec, N);
  int sz = pc128(S0);
  static u128 fm[128];
  static int n0[128];
  for (int phi = 1; phi < n; phi++) {
    fm[phi] = 0;
    for (int x = 0; x < n; x++) if (par(x & phi)) fm[phi] |= (u128)1 << x;
    n0[phi] = pc128(S0 & fm[phi]) % M;
  }
  // monomials: constant, x_i, x_i x_j
  int nm = 0;
  static u128 mono[64];
  mono[nm++] = n == 128 ? ~(u128)0 : (((u128)1 << n) - 1);
  for (int i = 0; i < N; i++) { u128 m = 0; for (int x = 0; x < n; x++) if (x >> i & 1) m |= (u128)1 << x; mono[nm++] = m; }
  for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) {
    u128 m = 0; for (int x = 0; x < n; x++) if ((x >> i & 1) && (x >> j & 1)) m |= (u128)1 << x; mono[nm++] = m; }
  // translation masks for invariance under the bottom inv_c bits (a subspace Y) and each of its hyperplanes
  u64 total = 0, invY = 0;
  u128 mask = 0;
  u64 lim = 1ull << nm;
  // order functionals so that early exit is fast: plain order
  for (u64 g = 0;; g++) {
    u128 S = S0 ^ mask;
    if (pc128(S) == sz) {
      int ok = 1;
      for (int phi = 1; phi < n; phi++) if (pc128(S & fm[phi]) % M != n0[phi]) { ok = 0; break; }
      if (ok) {
        total++;
        if (df) fprintf(df, "%016llx%016llx\n", (unsigned long long)(u64)(S >> 64), (unsigned long long)(u64)S);
        // invariant under Y = bottom inv_c bits?
        int inv = 1;
        for (int b = 0; b < inv_c && inv; b++) {
          u128 Tm = 0; // translate by e_b
          for (int x = 0; x < n; x++) if (S >> x & 1) Tm |= (u128)1 << (x ^ (1 << b));
          if (Tm != S) inv = 0;
        }
        invY += inv;
      }
    }
    if (g + 1 == lim) break;
    int t = __builtin_ctzll(g + 1);
    mask ^= mono[t];
  }
  if (df) fclose(df);
  printf("rm2 N=%d mod=%d seed=%s size=%d: class members in seed+RM(2,N): %llu, invariant under the bottom %d bits: %llu\n",
         N, M, spec, sz, (unsigned long long)total, inv_c, (unsigned long long)invY);
}

int main(int argc, char **argv) {
  if (argc >= 4 && !strcmp(argv[1], "classes32")) classes32(atoi(argv[2]), atoi(argv[3]));
  else if (argc >= 6 && !strcmp(argv[1], "rm2")) rm2(atoi(argv[2]), atoi(argv[3]), argv[4], atoi(argv[5]), argc >= 7 ? argv[6] : NULL);
  else { fprintf(stderr, "usage: see header\n"); return 1; }
  return 0;
}
