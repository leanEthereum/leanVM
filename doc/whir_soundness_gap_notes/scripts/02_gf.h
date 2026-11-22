// GF(2^m) for the 02_*.c programs: m = 64 (leanVM's K, x^64+x^4+x^3+x+1) by carry-less multiply,
// m <= 16 by log tables. Portable fallback when NEON's pmull is absent.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint16_t u16;

static int GF_M = 64;
static u64 GF_MOD = 0x1b; // low part of the modulus
static u16 *GF_LOG, *GF_EXP;

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
  for (int i = 0; i < 64; i++) {
    if (b & 1) r ^= a;
    b >>= 1;
    a = (a << 1) ^ ((a >> 63) ? 0x1b : 0);
  }
  return r;
}
#endif

static u64 mul_slow(u64 a, u64 b) { // m <= 32
  u64 r = 0;
  while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; }
  for (int i = 63; i >= GF_M; i--) if ((r >> i) & 1) r ^= ((1ull << GF_M) | GF_MOD) << (i - GF_M);
  return r;
}

static void gf_init(int m, u64 modlow) {
  GF_M = m; GF_MOD = modlow;
  if (m == 64) { if (modlow != 0x1b) { fprintf(stderr, "m=64 needs modulus 0x1b\n"); exit(1); } return; }
  if (m > 16) { fprintf(stderr, "m must be 64 or <= 16\n"); exit(1); }
  u32 q = 1u << m;
  GF_LOG = malloc(q * sizeof(u16)); GF_EXP = malloc(2 * q * sizeof(u16));
  for (u64 g = 2; g < q; g++) {
    u64 x = 1; int ok = 1;
    for (u32 i = 0; i < q - 1; i++) { GF_EXP[i] = (u16)x; x = mul_slow(x, g); if (x == 1 && i + 1 < q - 1) { ok = 0; break; } }
    if (ok) break;
  }
  for (u32 i = 0; i < q - 1; i++) { GF_LOG[GF_EXP[i]] = (u16)i; GF_EXP[i + q - 1] = GF_EXP[i]; }
}

static inline u64 gmul(u64 a, u64 b) {
  if (GF_M == 64) return mul64(a, b);
  if (!a || !b) return 0;
  return GF_EXP[(u32)GF_LOG[a] + GF_LOG[b]];
}
static inline u64 gpow(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = gmul(r, a); a = gmul(a, a); e >>= 1; } return r; }
static inline u64 ginv(u64 a) {
  if (GF_M == 64) return gpow(a, ~0ull - 1);
  return GF_EXP[((1u << GF_M) - 1 - GF_LOG[a]) % ((1u << GF_M) - 1)];
}
