// Researcher 21 (referee). n = 32, exhaustive inside sum buckets, in a small field GF(2^m): note 19, Theorems 1 to 3.
// For all s-subsets S of a 5-dimensional subspace D with a given e_1 (the sum), compute the previous-level class
// (n_phi mod 4 for all phi), the bit vector B(S) = (bit 2 of n_phi), e_2..e_7 by multiplying out, and the dual sums
// P_m(B) = sum over phi in B of delta_phi^(2^m - 1), delta_phi = product of the points x with phi(x) = 1.
// Checks: (Theorem 1 / Corollary 1.3) inside a previous-level class the partition by e_4 (and by (e_4,e_5)) equals the
// partition by P_1, the partition by (e_4..e_6) equals that by (P_1,P_2), the partition by (e_4..e_7) that by (P_1,P_2,P_3);
// (Theorem 2) pairs in a cell (class, e_4..e_g) have |Omega| = popcount(B ^ B') in {0} u [6, ..) (u [8, ..) for g >= 6) and
// distance >= 12, resp. 16; (Theorems 3a, 3c) cell sizes against the bounds.
// Usage: 21_dual32 m r seed s g ntargets      (r: low part of the modulus x^m + r; seed 0: basis 1, x, .., x^4)
// Build: cc -O2 -o 21_dual32 21_dual32.c
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint16_t u16;

static int M_;
static u32 R_;
static u16 *EXP, *LOG;
static u32 slow_mul(u32 a, u32 b) {
  u32 p = 0;
  for (int i = 0; i < M_; i++) if (b >> i & 1) p ^= a << i;
  for (int i = 2 * M_ - 2; i >= M_; i--) if (p >> i & 1) p ^= ((1u << M_) | R_) << (i - M_);
  return p;
}
static inline u32 mul(u32 a, u32 b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static void init_field(int m, u32 r) {
  M_ = m; R_ = r;
  u32 q = 1u << m;
  EXP = malloc(2 * q * sizeof(u16)); LOG = malloc(q * sizeof(u16));
  // find a generator
  for (u32 g = 2; g < q; g++) {
    u32 x = 1; u32 ord = 0;
    do { x = slow_mul(x, g); ord++; } while (x != 1);
    if (ord == q - 1) {
      x = 1;
      for (u32 i = 0; i < q - 1; i++) { EXP[i] = x; EXP[i + q - 1] = x; LOG[x] = i; x = slow_mul(x, g); }
      return;
    }
  }
  fprintf(stderr, "no generator: modulus reducible?\n"); exit(1);
}

typedef struct { u64 key; u32 S, B; u16 e[6], P[3]; } rec_t; // e[0..5] = e_2..e_7
static int g_;
static int cmp_class(const void *a, const void *b) { // by class, then e_4..e_g
  const rec_t *p = a, *q = b;
  if (p->key != q->key) return p->key < q->key ? -1 : 1;
  for (int j = 2; j <= g_ - 2; j++) if (p->e[j] != q->e[j]) return p->e[j] < q->e[j] ? -1 : 1;
  return 0;
}
static int cmp_real(const void *a, const void *b) { // by e_2..e_g, then class
  const rec_t *p = a, *q = b;
  for (int j = 0; j <= g_ - 2; j++) if (p->e[j] != q->e[j]) return p->e[j] < q->e[j] ? -1 : 1;
  if (p->key != q->key) return p->key < q->key ? -1 : 1;
  return 0;
}
typedef struct { u64 a, b; } pr_t;
static int cmp_pa(const void *x, const void *y) { const pr_t *p = x, *q = y; return p->a != q->a ? (p->a < q->a ? -1 : 1) : (p->b != q->b ? (p->b < q->b ? -1 : 1) : 0); }
static int cmp_pb(const void *x, const void *y) { const pr_t *p = x, *q = y; return p->b != q->b ? (p->b < q->b ? -1 : 1) : 0; }
// is the relation {(a_i, b_i)} a bijection between the distinct a and the distinct b ?
static int bijection(pr_t *v, size_t n) {
  qsort(v, n, sizeof(pr_t), cmp_pa);
  size_t u = 0;
  for (size_t i = 0; i < n; i++) if (!u || v[u - 1].a != v[i].a || v[u - 1].b != v[i].b) v[u++] = v[i];
  for (size_t i = 1; i < u; i++) if (v[i].a == v[i - 1].a) return 0;
  qsort(v, u, sizeof(pr_t), cmp_pb);
  for (size_t i = 1; i < u; i++) if (v[i].b == v[i - 1].b) return 0;
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 21_dual32 m r seed s g ntargets\n"); return 1; }
  int m = atoi(argv[1]); u32 r = (u32)strtoul(argv[2], 0, 0); int seed = atoi(argv[3]);
  int s = atoi(argv[4]); g_ = atoi(argv[5]); int ntarget = atoi(argv[6]);
  init_field(m, r);
  u32 q = 1u << m;
  u32 D[32];
  srand(seed);
  for (;;) {
    u32 b[5];
    for (int i = 0; i < 5; i++) b[i] = seed ? (u32)(rand() % (q - 1)) + 1 : (1u << i);
    int ok = 1;
    for (int x = 0; x < 32; x++) { D[x] = 0; for (int i = 0; i < 5; i++) if (x >> i & 1) D[x] ^= b[i]; if (x && !D[x]) ok = 0; }
    for (int x = 0; x < 32 && ok; x++) for (int y = 0; y < x; y++) if (D[x] == D[y]) ok = 0;
    if (ok) break;
  }
  u32 fm[32]; u16 dl[32][3];
  for (int phi = 1; phi < 32; phi++) {
    fm[phi] = 0; u32 d = 1;
    for (int x = 0; x < 32; x++) if (__builtin_popcount(x & phi) & 1) { fm[phi] |= 1u << x; d = mul(d, D[x]); }
    u32 d3 = mul(d, mul(d, d)), d7 = mul(d3, mul(d3, d));
    dl[phi][0] = d; dl[phi][1] = d3; dl[phi][2] = d7;
  }
  u32 col[5];
  for (int j = 0; j < 5; j++) { col[j] = 0; for (int x = 0; x < 32; x++) if (x >> j & 1) col[j] |= 1u << x; }
  int sp = s <= 16 ? s : 32 - s;
  double rho2 = sp * (32.0 - sp) / 64.0; // s(n-s)/(16 u^2), u = 2
  long bound = -1; // -1: no bound claimed for cells
  if (g_ >= 6) { if (sp < 8) bound = 1; else if (sp < 16) bound = (long)floor(1.0 / ((1 - sp / 16.0) * (1 - sp / 16.0)) + 1e-9); }
  else if (g_ >= 4) { if (sp < 6) bound = 1; else if (sp < 8) bound = (long)floor(3.0 / (3.0 - rho2) + 1e-9); }
  size_t maxcell = 0, maxreal = 0, maxprev = 0, maxclasses_in_real = 0, nsets = 0, viol = 0, crit_fail = 0, pairs_checked = 0;
  u64 omega_seen = 0; int mindist0 = 99, mindist = 99;
  int targets[32], nt = 0;
  if (s & 1) targets[nt++] = 0; else for (int t = 0; t < 32 && nt < ntarget; t++) targets[nt++] = (t * 11) % 32;
  for (int ti = 0; ti < nt; ti++) {
    int target = targets[ti];
    size_t cap = 1 << 20, cnt = 0;
    rec_t *R = malloc(cap * sizeof(rec_t));
    u64 A = (1ull << (s - 1)) - 1;
    while (A < (1ull << 32)) {
      u32 a = (u32)A;
      int x = target;
      for (int j = 0; j < 5; j++) if (__builtin_popcount(a & col[j]) & 1) x ^= 1 << j;
      int mx = 31 - __builtin_clz(a);
      if (x > mx) {
        u32 S = a | (1u << x);
        if (cnt == cap) { cap *= 2; R = realloc(R, cap * sizeof(rec_t)); }
        rec_t *p = &R[cnt++];
        p->S = S; p->key = 0; p->B = 0; p->P[0] = p->P[1] = p->P[2] = 0;
        for (int phi = 1; phi < 32; phi++) {
          int np = __builtin_popcount(S & fm[phi]);
          p->key = (p->key << 2) | (np & 3);
          if (np & 4) { p->B |= 1u << phi; p->P[0] ^= dl[phi][0]; p->P[1] ^= dl[phi][1]; p->P[2] ^= dl[phi][2]; }
        }
        u32 e[8] = {1, 0, 0, 0, 0, 0, 0, 0};
        for (u32 t = S; t; t &= t - 1) {
          u32 pt = D[__builtin_ctz(t)];
          if (pt) for (int j = 7; j >= 1; j--) e[j] ^= mul(pt, e[j - 1]);
        }
        for (int j = 2; j <= 7; j++) p->e[j - 2] = (u16)e[j];
      }
      u64 c = A & -A, rr = A + c;
      A = (((rr ^ A) >> 2) / c) | rr;
    }
    nsets += cnt;
    // real classes: same e_2..e_g
    qsort(R, cnt, sizeof(rec_t), cmp_real);
    for (size_t i = 0; i < cnt;) {
      size_t j = i, ncl = 0;
      while (j < cnt) {
        int same = 1;
        for (int t = 0; t <= g_ - 2; t++) if (R[i].e[t] != R[j].e[t]) same = 0;
        if (!same) break;
        if (j == i || R[j].key != R[j - 1].key) ncl++;
        j++;
      }
      if (j - i > maxreal) maxreal = j - i;
      if (ncl > maxclasses_in_real) maxclasses_in_real = ncl;
      i = j;
    }
    // previous-level classes
    qsort(R, cnt, sizeof(rec_t), cmp_class);
    for (size_t i = 0; i < cnt;) {
      size_t j = i;
      while (j < cnt && R[j].key == R[i].key) j++;
      size_t sz = j - i;
      if (sz > maxprev) maxprev = sz;
      if (sz >= 2) {
        pr_t *v = malloc(sz * sizeof(pr_t));
        for (int lev = 0; lev < 4; lev++) {
          for (size_t t = 0; t < sz; t++) {
            rec_t *p = &R[i + t];
            u64 a = p->e[2], b = p->P[0];
            if (lev >= 1) a = (a << 16) | p->e[3];
            if (lev >= 2) { a = (a << 16) | p->e[4]; b = (b << 16) | p->P[1]; }
            if (lev >= 3) { a = (a << 16) | p->e[5]; b = (b << 16) | p->P[2]; }
            v[t].a = a; v[t].b = b;
          }
          if (!bijection(v, sz)) crit_fail++;
        }
        free(v);
        // cells
        for (size_t c0 = i; c0 < j;) {
          size_t c1 = c0;
          while (c1 < j && cmp_class(&R[c0], &R[c1]) == 0) c1++;
          size_t cs = c1 - c0;
          if (cs > maxcell) maxcell = cs;
          if (bound >= 0 && (long)cs > bound) viol++;
          for (size_t a = c0; a < c1; a++) for (size_t b = a + 1; b < c1; b++) {
            int w = __builtin_popcount(R[a].B ^ R[b].B), d = __builtin_popcount(R[a].S ^ R[b].S);
            pairs_checked++;
            omega_seen |= 1ull << w;
            if (w == 0) { if (d < mindist0) mindist0 = d; } else if (d < mindist) mindist = d;
            if (w != 0 && w < (g_ >= 6 ? 8 : 6)) viol++;
            if (d < (g_ >= 6 ? 16 : 12) || (w == 0 && d < 16)) viol++;
            if (g_ < 6 && sp >= 6 && sp < 8 && d != 12) viol++;
          }
          c0 = c1;
        }
      }
      i = j;
    }
    free(R);
  }
  printf("GF(2^%d) seed=%d s=%d g=%d sums=%d: sets=%zu largest previous-level class=%zu largest real class=%zu (meets up to %zu previous-level classes) "
         "largest cell=%zu bound=%ld criterion failures=%zu violations=%zu pairs in cells=%zu min distance (Omega empty)=%d (Omega nonempty)=%d |Omega| seen:",
         m, seed, s, g_, nt, nsets, maxprev, maxreal, maxclasses_in_real, maxcell, bound, crit_fail, viol, pairs_checked, mindist0, mindist);
  for (int w = 0; w < 32; w++) if (omega_seen >> w & 1) printf(" %d", w);
  printf("\n");
  return 0;
}
