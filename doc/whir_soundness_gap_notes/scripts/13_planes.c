// Researcher 13. Collision statistics of the invariants that govern the non-formal ("pigeonhole") lists on a
// subspace domain D of GF(2^m), all computed on the dual space Dstar = {0} u {1/delta_H}, delta_H = prod of D \ H,
// which is an N-dimensional F_2-space indexed by the functionals of D (note 05, Proposition 4.1; note 02, section 7):
//   iota2: sum of 1/a over the nonzero a of a plane A of Dstar. Two codimension-2 subspaces V, V' of D have the
//          same second coefficient c(V) = c(V') iff iota2 agrees on their planes.
//   pi2:   product of the nonzero a of a plane. Two planes with the same product and trivial intersection are one
//          decomposition of a rank-4 solution of the Gold moment equation (10 decompositions per solution).
//   iota3: sum of 1/a over a 3-dimensional subspace: the fibres of c on codimension-3 subspaces.
//   aff2:  sum of 1/a over an affine plane of Dstar off the origin: c(V1)^4 + c(V2)^4 for two codimension-2
//          subspaces through a common codimension-3 subspace (two free flats of size n/4).
// With a second field (m2 r2) the key is the pair of invariants in both fields, on the "same" domain
// (power shape: the polynomials of degree < N reduced modulo both moduli), so what collides is an identity of
// F_2(x) up to an error of 2^-(m+m2) per pair. With shape random and two fields the two bases are independent.
// usage: 13_planes N stat shape m r [m2 r2] [-p passes] [-v]      shape: power | random:<seed>
// build: cc -O2 -mcpu=native -o 13_planes 13_planes.c
#include "13_gf.h"
#include <math.h>

static int N, nf;
static gf_t F[2];
static u64 *elt[2], *inv[2];

static void dual_basis(const gf_t *G, const u64 *basis, u64 *a) {
  for (int k = 0; k < N; k++) {
    u64 h[64], z = basis[k]; int d = 0;
    for (int j = 0; j < N; j++) if (j != k) h[d++] = basis[j];
    gf_subspace_eval(G, h, d, &z, 1);
    a[k] = gf_inv(G, z);
  }
}
static inline u64 mix(u64 a, u64 b) {
  u64 h = a * 0x9e3779b97f4a7c15ull;
  h ^= h >> 32;
  h += b * 0xc2b2ae3d27d4eb4full;
  h ^= h >> 29;
  return h * 0xff51afd7ed558ccdull;
}
typedef void (*emit_fn)(u64 key, u32 a, u32 b, u32 c);
static int stat; // 0 iota2, 1 pi2, 2 iota3, 3 aff2
static inline u64 keyof(u32 a, u32 b, u32 c) {
  u64 k[2] = {0, 0};
  for (int f = 0; f < nf; f++) {
    if (stat == 0) k[f] = inv[f][a] ^ inv[f][b] ^ inv[f][a ^ b];
    else if (stat == 1) k[f] = gf_mul(&F[f], gf_mul(&F[f], elt[f][a], elt[f][b]), elt[f][a ^ b]);
    else if (stat == 2) k[f] = inv[f][a] ^ inv[f][b] ^ inv[f][a ^ b] ^ inv[f][c] ^ inv[f][c ^ a] ^ inv[f][c ^ b] ^ inv[f][c ^ a ^ b];
    else k[f] = inv[f][c] ^ inv[f][c ^ a] ^ inv[f][c ^ b] ^ inv[f][c ^ a ^ b];
  }
  return nf == 2 ? mix(k[0], k[1]) : k[0];
}
// subsets of the bits below p, skipping the positions in the mask skip
static inline u32 spread(u32 i, u32 below, u32 skip) {
  u32 r = 0, m = below & ~skip; // deposit the bits of i into the positions of m
  while (m) { u32 low = m & -m; if (i & 1) r |= low; i >>= 1; m ^= low; }
  return r;
}
static void enumerate(emit_fn emit) {
  if (stat == 0 || stat == 1) {
    for (int p1 = 1; p1 < N; p1++) for (int p2 = 0; p2 < p1; p2++)
      for (u32 i = 0; i < (1u << (p1 - 1)); i++) {
        u32 a = (1u << p1) | spread(i, (1u << p1) - 1, 1u << p2);
        for (u32 j = 0; j < (1u << p2); j++) { u32 b = (1u << p2) | j; emit(keyof(a, b, 0), a, b, 0); }
      }
  } else if (stat == 2) {
    for (int p1 = 2; p1 < N; p1++) for (int p2 = 1; p2 < p1; p2++) for (int p3 = 0; p3 < p2; p3++)
      for (u32 i = 0; i < (1u << (p1 - 2)); i++) {
        u32 a = (1u << p1) | spread(i, (1u << p1) - 1, (1u << p2) | (1u << p3));
        for (u32 j = 0; j < (1u << (p2 - 1)); j++) {
          u32 b = (1u << p2) | spread(j, (1u << p2) - 1, 1u << p3);
          for (u32 l = 0; l < (1u << p3); l++) { u32 c = (1u << p3) | l; emit(keyof(a, b, c), a, b, c); }
        }
      }
  } else {
    // affine planes c + <a, b> off the origin: plane <a, b> in RREF, c a coset representative with zero pivot bits
    for (int p1 = 1; p1 < N; p1++) for (int p2 = 0; p2 < p1; p2++)
      for (u32 i = 0; i < (1u << (p1 - 1)); i++) {
        u32 a = (1u << p1) | spread(i, (1u << p1) - 1, 1u << p2);
        for (u32 j = 0; j < (1u << p2); j++) {
          u32 b = (1u << p2) | j;
          for (u32 l = 1; l < (1u << (N - 2)); l++) {
            u32 c = spread(l, (1u << N) - 1, (1u << p1) | (1u << p2));
            emit(keyof(a, b, c), a, b, c);
          }
        }
      }
  }
}
static u64 *keys; static size_t nkeys, cap; static int passes = 1, pass;
static void emit_store(u64 key, u32 a, u32 b, u32 c) {
  (void)a; (void)b; (void)c;
  if (passes > 1 && (int)((key * 0x9e3779b97f4a7c15ull) >> 40) % passes != pass) return;
  if (nkeys == cap) { cap = cap ? cap * 2 : 1 << 20; keys = realloc(keys, cap * sizeof(u64)); if (!keys) { fprintf(stderr, "oom\n"); exit(1); } }
  keys[nkeys++] = key;
}
static u64 *dup; static size_t ndup; static unsigned char *bloom;
static void emit_find(u64 key, u32 a, u32 b, u32 c) {
  u64 h = (key * 0x9e3779b97f4a7c15ull) >> 40;
  if (!(bloom[h >> 3] >> (h & 7) & 1)) return;
  size_t lo = 0, hi = ndup;
  while (lo < hi) { size_t mid = (lo + hi) / 2; if (dup[mid] < key) lo = mid + 1; else hi = mid; }
  if (lo < ndup && dup[lo] == key) printf("  hit key=%016llx a=%x b=%x c=%x\n", (unsigned long long)key, a, b, c);
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: N stat shape m r [m2 r2] [-p passes] [-v]\n"); return 1; }
  N = atoi(argv[1]);
  const char *sn[] = {"iota2", "pi2", "iota3", "aff2"};
  stat = -1; for (int i = 0; i < 4; i++) if (!strcmp(argv[2], sn[i])) stat = i;
  if (stat < 0) { fprintf(stderr, "unknown stat\n"); return 1; }
  const char *shape = argv[3];
  int verbose = 0; nf = 1;
  gf_init(&F[0], atoi(argv[4]), strtoull(argv[5], 0, 0));
  int ai = 6;
  if (ai + 1 < argc && argv[ai][0] != '-') { gf_init(&F[1], atoi(argv[ai]), strtoull(argv[ai + 1], 0, 0)); nf = 2; ai += 2; }
  for (; ai < argc; ai++) { if (!strcmp(argv[ai], "-p")) passes = atoi(argv[++ai]); else if (!strcmp(argv[ai], "-v")) verbose = 1; }
  for (int f = 0; f < nf; f++) {
    u64 basis[64], a[64];
    if (!strncmp(shape, "random", 6)) {
      rng_state = strtoull(shape + 7, 0, 10) * 0x2545F4914F6CDD1Dull + 77 * f + 1;
      for (;;) { // a random independent family
        for (int i = 0; i < N; i++) basis[i] = rnd64() & F[f].mask;
        u64 e[64]; int rk = 0; memset(e, 0, sizeof e);
        for (int i = 0; i < N; i++) { u64 v = basis[i]; for (int b = 63; b >= 0 && v; b--) if (v >> b & 1) { if (e[b]) v ^= e[b]; else { e[b] = v; rk++; break; } } }
        if (rk == N) break;
      }
    } else for (int i = 0; i < N; i++) basis[i] = 1ull << i;
    if (N > F[f].m) { fprintf(stderr, "N > m\n"); return 1; }
    dual_basis(&F[f], basis, a);
    elt[f] = malloc(sizeof(u64) << N); inv[f] = malloc(sizeof(u64) << N);
    elt[f][0] = inv[f][0] = 0;
    for (u32 v = 1; v < (1u << N); v++) { int b = __builtin_ctz(v); elt[f][v] = elt[f][v & (v - 1)] ^ a[b]; }
    for (u32 v = 1; v < (1u << N); v++) { if (!elt[f][v]) { fprintf(stderr, "dual space degenerate\n"); return 1; } inv[f][v] = gf_inv(&F[f], elt[f][v]); }
    // sanity: additivity of functional -> 1/delta_H, on the hyperplane ker(e_0 + e_1)
    { u64 h[64], z = basis[0]; int d = 0; h[d++] = basis[0] ^ basis[1]; for (int j = 2; j < N; j++) h[d++] = basis[j];
      gf_subspace_eval(&F[f], h, d, &z, 1);
      if (gf_inv(&F[f], z) != (a[0] ^ a[1])) { fprintf(stderr, "additivity check failed\n"); return 1; } }
  }
  double P = 0; size_t hist[64]; memset(hist, 0, sizeof hist); size_t maxmult = 0; double pairs = 0;
  u64 *alldup = 0; size_t nall = 0;
  for (pass = 0; pass < passes; pass++) {
    nkeys = 0; enumerate(emit_store);
    P += (double)nkeys;
    radix_sort(keys, nkeys);
    for (size_t s = 0; s < nkeys;) {
      size_t t = s + 1; while (t < nkeys && keys[t] == keys[s]) t++;
      size_t c = t - s; if (c < 64) hist[c]++; if (c > maxmult) maxmult = c;
      if (c >= 2) { pairs += (double)c * (c - 1) / 2; alldup = realloc(alldup, (nall + 1) * sizeof(u64)); alldup[nall++] = keys[s]; }
      s = t;
    }
  }
  double bits = nf == 2 ? (double)(F[0].m + F[1].m) : (double)F[0].m;
  double mu = P / pow(2.0, bits);
  // planes that share a line never collide (b^2 + ab is injective up to b -> a + b): they are not candidates
  double cand = P * (P - 1) / 2;
  if (stat == 0 || stat == 1) cand = P * (P - 1 - 3 * (pow(2.0, N - 1) - 2)) / 2;
  printf("N=%d stat=%s shape=%s m=%d r=0x%llx", N, sn[stat], shape, F[0].m, (unsigned long long)F[0].r);
  if (nf == 2) printf(" m2=%d r2=0x%llx", F[1].m, (unsigned long long)F[1].r);
  printf("\n  objects %.0f (2^%.2f), colliding pairs %.0f, random model %.4g (ratio %.4f), largest fibre %zu\n", P, log2(P), pairs,
         cand / pow(2.0, bits), pairs / (cand / pow(2.0, bits)), maxmult);
  printf("  fibre sizes (observed / Poisson with mean %.4g):", mu);
  if (mu < 20) for (int c = 1; c < 64; c++) if (hist[c] || (c <= (int)maxmult + 1)) {
    double pois = pow(2.0, bits) * exp(-mu); for (int i = 1; i <= c; i++) pois *= mu / i;
    printf(" %d:%zu/%.4g", c, hist[c], pois);
  }
  // the expected maximum of 2^bits Poisson variables: the largest c with 2^bits P(X >= c) >= 1
  { double lt = bits * log(2.0) - mu, best = 0; for (int c = 1; c < 100000; c++) { lt += log(mu / c); if (lt >= 0) best = c; if (c > mu && lt < -40) break; }
    printf("  [Poisson: largest fibre size expected at least once: %.0f]", best); }
  printf("\n");
  if (verbose && nall && nall <= 200000) {
    passes = 1; dup = alldup; ndup = nall; radix_sort(dup, ndup);
    bloom = calloc(1 << 21, 1);
    for (size_t i = 0; i < ndup; i++) { u64 h = (dup[i] * 0x9e3779b97f4a7c15ull) >> 40; bloom[h >> 3] |= 1 << (h & 7); }
    enumerate(emit_find);
  }
  return 0;
}
