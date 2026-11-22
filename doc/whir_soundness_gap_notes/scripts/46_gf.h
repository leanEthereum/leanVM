// Referee 46: own GF(2^64) arithmetic (x^64 + x^4 + x^3 + x + 1), subspace domains and small polynomial helpers.
// Nothing here is shared with the 02_/39_ programs.
#ifndef GF46_H
#define GF46_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;

#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
#include <arm_neon.h>
static inline u64 gmul(u64 a, u64 b) {
  poly128_t p = vmull_p64(a, b);
  u64 lo = (u64)p, hi = (u64)(p >> 64);
  poly128_t q = vmull_p64(hi, 0x1bULL);
  lo ^= (u64)q;
  hi = (u64)(q >> 64); // at most 4 bits
  return lo ^ hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4);
}
#else
static inline u64 gmul(u64 a, u64 b) {
  u64 r = 0;
  for (int i = 0; i < 64; i++) {
    if (b & 1) r ^= a;
    b >>= 1;
    a = (a << 1) ^ ((a >> 63) ? 0x1bULL : 0);
  }
  return r;
}
#endif
static inline u64 gsq(u64 a) { return gmul(a, a); }
static u64 ginv(u64 a) { // a^(2^64 - 2)
  u64 r = 1, s = gsq(a);
  for (int i = 1; i < 64; i++) { r = gmul(r, s); s = gsq(s); }
  return r;
}
static u64 gsqrt(u64 a) { // a^(2^63)
  for (int i = 0; i < 63; i++) a = gsq(a);
  return a;
}
static u64 gpow(u64 a, unsigned e) {
  u64 r = 1;
  while (e) { if (e & 1) r = gmul(r, a); a = gsq(a); e >>= 1; }
  return r;
}

static u64 sm_state;
static u64 splitmix(void) {
  u64 z = (sm_state += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

// Basis of an N-dimensional F_2-subspace: seed 0 is the real shape 1, x, ..., x^(N-1); otherwise random and
// checked independent. pts[i] is the sum of the basis vectors selected by the bits of i, so translation by
// pts[a] is XOR of indices and the functional "bit j" is the j-th coordinate.
static void make_domain(int N, u64 seed, u64 *basis, u64 *pts) {
  if (seed == 0) {
    for (int i = 0; i < N; i++) basis[i] = 1ULL << i;
  } else {
    sm_state = seed * 0x1234567ULL + 99;
    for (;;) {
      for (int i = 0; i < N; i++) basis[i] = splitmix();
      u64 red[64]; int rank = 0;
      memset(red, 0, sizeof red);
      for (int i = 0; i < N; i++) {
        u64 v = basis[i];
        for (int b = 63; b >= 0 && v; b--) {
          if (!((v >> b) & 1)) continue;
          if (red[b]) v ^= red[b]; else { red[b] = v; rank++; v = 0; }
        }
      }
      if (rank == N) break;
    }
  }
  int n = 1 << N;
  for (int i = 0; i < n; i++) {
    u64 v = 0;
    for (int j = 0; j < N; j++) if ((i >> j) & 1) v ^= basis[j];
    pts[i] = v;
  }
}

// Polynomials: coefficient arrays, low degree first, degree stored separately (-1 for the zero polynomial).
#define PMAX 100
typedef struct { int deg; u64 c[PMAX]; } poly;
static void pnorm(poly *p) { while (p->deg >= 0 && p->c[p->deg] == 0) p->deg--; }
static void pzero(poly *p) { p->deg = -1; memset(p->c, 0, sizeof p->c); }
static void pone(poly *p) { pzero(p); p->deg = 0; p->c[0] = 1; }
static void padd(poly *r, const poly *a, const poly *b) {
  poly t; pzero(&t);
  int d = a->deg > b->deg ? a->deg : b->deg;
  for (int i = 0; i <= d; i++) t.c[i] = (i <= a->deg ? a->c[i] : 0) ^ (i <= b->deg ? b->c[i] : 0);
  t.deg = d; pnorm(&t); *r = t;
}
static void pmul(poly *r, const poly *a, const poly *b) {
  poly t; pzero(&t);
  if (a->deg < 0 || b->deg < 0) { *r = t; return; }
  if (a->deg + b->deg >= PMAX) { fprintf(stderr, "pmul overflow\n"); exit(1); }
  for (int i = 0; i <= a->deg; i++) if (a->c[i])
    for (int j = 0; j <= b->deg; j++) t.c[i + j] ^= gmul(a->c[i], b->c[j]);
  t.deg = a->deg + b->deg; pnorm(&t); *r = t;
}
static void pdivrem(poly *q, poly *r, const poly *a, const poly *b) { // b nonzero
  poly rem = *a, quo; pzero(&quo);
  u64 il = ginv(b->c[b->deg]);
  while (rem.deg >= b->deg) {
    int s = rem.deg - b->deg;
    u64 f = gmul(rem.c[rem.deg], il);
    quo.c[s] = f; if (s > quo.deg) quo.deg = s;
    for (int i = 0; i <= b->deg; i++) rem.c[i + s] ^= gmul(f, b->c[i]);
    rem.c[rem.deg] = 0;
    pnorm(&rem);
  }
  if (q) *q = quo;
  if (r) *r = rem;
}
static void pmonic(poly *p) {
  if (p->deg < 0) return;
  u64 il = ginv(p->c[p->deg]);
  for (int i = 0; i <= p->deg; i++) p->c[i] = gmul(p->c[i], il);
}
static void pgcd(poly *g, const poly *a, const poly *b) {
  poly x = *a, y = *b, r;
  while (y.deg >= 0) { pdivrem(NULL, &r, &x, &y); x = y; y = r; }
  pmonic(&x); *g = x;
}
static u64 peval(const poly *p, u64 x) {
  u64 v = 0;
  for (int i = p->deg; i >= 0; i--) v = gmul(v, x) ^ p->c[i];
  return v;
}
static int peq(const poly *a, const poly *b) {
  if (a->deg != b->deg) return 0;
  for (int i = 0; i <= a->deg; i++) if (a->c[i] != b->c[i]) return 0;
  return 1;
}
// p(X) = A(q) + X B(q) with q = X^2 + a X: fills A and B.
static void psplit(poly *A, poly *B, const poly *p, u64 a) {
  poly q; pzero(&q); q.deg = 2; q.c[2] = 1; q.c[1] = a;
  poly cur = *p, quo, rem;
  pzero(A); pzero(B);
  int k = 0;
  while (cur.deg >= 0) {
    pdivrem(&quo, &rem, &cur, &q);
    A->c[k] = rem.deg >= 0 ? rem.c[0] : 0;
    B->c[k] = rem.deg >= 1 ? rem.c[1] : 0;
    k++; cur = quo;
  }
  A->deg = k - 1; B->deg = k - 1; pnorm(A); pnorm(B);
}
// A(q(X)) for q = X^2 + a X.
static void pcompose_q(poly *r, const poly *A, u64 a) {
  poly q; pzero(&q); q.deg = 2; q.c[2] = 1; q.c[1] = a;
  poly acc; pzero(&acc);
  for (int i = A->deg; i >= 0; i--) {
    pmul(&acc, &acc, &q);
    poly c; pzero(&c); if (A->c[i]) { c.deg = 0; c.c[0] = A->c[i]; }
    padd(&acc, &acc, &c);
  }
  *r = acc;
}
#endif
