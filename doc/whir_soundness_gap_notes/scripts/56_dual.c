// Researcher 56. Non-formal pairs inside a previous-level class at toy sizes, as a function of the field degree m
// (56-witt-real-field.md, Section 5). D is an N-dimensional F_2-subspace of GF(2^m); for a functional phi != 0,
// delta_phi = prod of the points off ker(phi) and a_phi = 1 / delta_phi (additive in phi, note 19 Lemma 1.1).
//  six:   all 6-subsets Omega of functionals with sum 0 and sum of delta = 0. Each gives 16 pairs of disjoint
//         sets A, B of 3n/16 points with Z_A - Z_B constant (note 19, Remark 2.2): depth 3n/16 - 1.
//  eight: all pairs of disjoint zero-sum 4-sets F1, F2 of functionals with sum of delta = sum of delta^3 = 0.
//         Each gives pairs of disjoint sets A, B of n/4 points with deg(Z_A - Z_B) <= n/32: depth 7n/32 - 1,
//         above the second position 3n/16, where the formal model has only hyperplane swaps.
// The counts are printed against the random model (zero-sum configurations) * 2^(-m) resp. 2^(-2m), and the
// first configuration found is verified by multiplying out Z_A and Z_B.
// usage: 56_dual N m r seed [six|eight|both|list]   (modulus x^m + r; seed 0: D = span(1, x, .., x^(N-1));
//        list: the six-point words themselves, when there are fewer than 400)
// build: cc -O2 -mcpu=native -o 56_dual 56_dual.c
#include "13_gf.h"
#include <math.h>
static gf_t F; static int N, n; static u64 *pts, *del, *del3;
typedef struct { u64 k1, k2; u32 id[4]; } rec4;
static int cmp4(const void *a, const void *b) {
  const rec4 *x = a, *y = b;
  if (x->k1 != y->k1) return x->k1 < y->k1 ? -1 : 1;
  if (x->k2 != y->k2) return x->k2 < y->k2 ? -1 : 1;
  return 0;
}
typedef struct { u64 k; u32 a, b; } rec3;
static int cmp3(const void *a, const void *b) { const rec3 *x = a, *y = b; return x->k < y->k ? -1 : x->k > y->k; }

// c(x) = (1/4) sum_i eps_i (-1)^(phi_i(x)); returns 0 if some value is not in {0, 1, -1}
static int build_sets(const u32 *phi, int w, u32 signs, int *A, int *na, int *B, int *nb) {
  *na = *nb = 0;
  for (int x = 0; x < n; x++) {
    int s = 0;
    for (int i = 0; i < w; i++) s += ((signs >> i & 1) ^ (__builtin_popcount(phi[i] & x) & 1)) ? -1 : 1;
    if (s == 4) A[(*na)++] = x; else if (s == -4) B[(*nb)++] = x; else if (s != 0) return 0;
  }
  return 1;
}
static void locator(const int *S, int k, u64 *z) { // z[0..k], low degree first
  z[0] = 1; for (int j = 1; j <= k; j++) z[j] = 0;
  for (int t = 0; t < k; t++) { u64 s = pts[S[t]]; for (int j = t + 1; j >= 1; j--) z[j] = z[j - 1] ^ gf_mul(&F, s, z[j]); z[0] = gf_mul(&F, s, z[0]); }
}
static void verify(const u32 *phi, int w, const char *name) {
  int *A = malloc(n * sizeof(int)), *B = malloc(n * sizeof(int)), na, nb, valid = 0; u32 first = 0;
  for (u32 s = 0; s < (1u << w); s++) if (build_sets(phi, w, s, A, &na, B, &nb) && na) { if (!valid) first = s; valid++; }
  if (!valid) { printf("  %s: no sign pattern gives a difference of two sets\n", name); free(A); free(B); return; }
  build_sets(phi, w, first, A, &na, B, &nb);
  u64 *za = malloc((n + 1) * sizeof(u64)), *zb = malloc((n + 1) * sizeof(u64));
  locator(A, na, za); locator(B, nb, zb);
  int deg = -1; for (int j = 0; j <= na; j++) if (za[j] != zb[j]) deg = j;
  // Walsh level: the hyperplane counts of 1_A - 1_B, modulo n/4 (formal at depth >= n/8) and modulo n/8
  int formal = 1, prev = 1;
  for (int f = 1; f < n; f++) {
    int d = 0;
    for (int i = 0; i < na; i++) d += __builtin_popcount(f & A[i]) & 1;
    for (int i = 0; i < nb; i++) d -= __builtin_popcount(f & B[i]) & 1;
    if (d % (n / 4)) formal = 0;
    if (d % (n / 8)) prev = 0;
  }
  printf("  %s: functionals", name); for (int i = 0; i < w; i++) printf(" %x", phi[i]);
  printf(", signs %x (%d valid sign patterns)\n", first, valid);
  printf("     |A| = %d, |B| = %d, disjoint, deg(Z_A - Z_B) = %d: common top to depth %d = %.4f n; "
         "same previous-level class: %s; formal at this depth: %s\n", na, nb, deg, na - deg - 1, (double)(na - deg - 1) / n,
         prev ? "yes" : "NO", formal ? "YES" : "no");
  printf("     A = {"); for (int i = 0; i < na && i < 12; i++) printf("%d,", A[i]); printf("...}  B = {"); for (int i = 0; i < nb && i < 12; i++) printf("%d,", B[i]); printf("...}  (points as bit masks of coordinates)\n");
  free(A); free(B); free(za); free(zb);
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: 56_dual N m r seed [six|eight|both|list]\n"); return 1; }
  N = atoi(argv[1]); int m = atoi(argv[2]); u64 r = strtoull(argv[3], 0, 0); int seed = atoi(argv[4]);
  const char *mode = argc > 5 ? argv[5] : "both";
  n = 1 << N; gf_init(&F, m, r);
  u64 basis[32];
  if (!seed) for (int i = 0; i < N; i++) basis[i] = 1ull << i;
  else {
    rng_state += 0x1234567ull * seed;
    for (;;) { // random independent basis
      for (int i = 0; i < N; i++) basis[i] = rnd64() & F.mask;
      u64 e[64] = {0}; int ok = 1;
      for (int i = 0; i < N && ok; i++) { u64 v = basis[i]; for (int b = m - 1; b >= 0 && v; b--) if (v >> b & 1) { if (e[b]) v ^= e[b]; else { e[b] = v; break; } } if (!v) ok = 0; }
      if (ok) break;
    }
  }
  pts = malloc(n * sizeof(u64)); del = malloc(n * sizeof(u64)); del3 = malloc(n * sizeof(u64));
  for (int x = 0; x < n; x++) { u64 v = 0; for (int i = 0; i < N; i++) if (x >> i & 1) v ^= basis[i]; pts[x] = v; }
  // a for the dual basis functionals phi_i (phi_i(b_j) = [i = j]): 1 / L_{H_i}(b_i)
  u64 a[32];
  for (int i = 0; i < N; i++) {
    u64 hb[32]; int k = 0; for (int j = 0; j < N; j++) if (j != i) hb[k++] = basis[j];
    u64 z = basis[i]; gf_subspace_eval(&F, hb, N - 1, &z, 1); a[i] = gf_inv(&F, z);
  }
  del[0] = 0;
  for (int f = 1; f < n; f++) { u64 v = 0; for (int i = 0; i < N; i++) if (f >> i & 1) v ^= a[i]; del[f] = gf_inv(&F, v); del3[f] = gf_mul(&F, del[f], gf_sqr(&F, del[f])); }
  // self check of the additivity: delta_phi = product of the points off ker(phi), for a few phi
  for (int t = 0; t < 5; t++) { int f = 1 + (int)(rnd64() % (n - 1)); u64 p = 1; for (int x = 1; x < n; x++) if (__builtin_popcount(f & x) & 1) p = gf_mul(&F, p, pts[x]); if (p != del[f]) { fprintf(stderr, "additivity check failed\n"); return 1; } }
  printf("N=%d n=%d GF(2^%d) modulus x^%d+0x%llx %s basis\n", N, n, m, m, (unsigned long long)r, seed ? "random" : "power");
  double nn = n - 1;
  if (strcmp(mode, "eight")) {
    // six-point words: two triples with equal xor and equal sum of delta
    double found = 0, cand = 0; u32 ex[6]; int have = 0;
    static u32 all[4096][6]; int nall = 0;   // every pair of triples, when there are few (mode "list")
    size_t cap = (size_t)n * n / 4 + 16; rec3 *buf = malloc(cap * sizeof(rec3));
    for (int sig = 0; sig < n; sig++) {
      size_t len = 0;
      for (int p1 = 1; p1 < n; p1++) for (int p2 = p1 + 1; p2 < n; p2++) { int p3 = sig ^ p1 ^ p2; if (p3 > p2) buf[len++] = (rec3){del[p1] ^ del[p2] ^ del[p3], p1, p2}; }
      qsort(buf, len, sizeof(rec3), cmp3);
      for (size_t i = 0; i < len;) {
        size_t j = i; while (j < len && buf[j].k == buf[i].k) j++;
        found += (double)(j - i) * (j - i - 1) / 2;
        if (j - i > 1 && !have) { have = 1; ex[0] = buf[i].a; ex[1] = buf[i].b; ex[2] = sig ^ ex[0] ^ ex[1]; ex[3] = buf[i + 1].a; ex[4] = buf[i + 1].b; ex[5] = sig ^ ex[3] ^ ex[4]; }
        for (size_t x = i; x < j; x++) for (size_t y = x + 1; y < j; y++) if (nall < 4096) {
          u32 *w = all[nall++]; w[0] = buf[x].a; w[1] = buf[x].b; w[2] = sig ^ w[0] ^ w[1]; w[3] = buf[y].a; w[4] = buf[y].b; w[5] = sig ^ w[3] ^ w[4];
        }
        i = j;
      }
    }
    free(buf);
    found /= 10;   // a 6-set splits into two complementary triples in 10 ways
    cand = (nn * (nn - 1) * (nn - 2) * (nn - 3) * (nn - 4) * (nn - 5) / 720 - nn * ((nn - 1) / 2) * ((nn - 1) / 2 - 1) * ((nn - 1) / 2 - 2) / 6) / n;
    printf("  six-point words (sum phi = 0, sum delta = 0): %.0f; zero-sum 6-sets: %.4g; random model %.4g; ratio %.3f\n", found, cand, cand * pow(2, -m), found / (cand * pow(2, -m)));
    if (have) verify(ex, 6, "example (depth 3n/16 - 1)");
    if (!strcmp(mode, "list") && nall < 4096) {
      // distinct 6-sets, sorted
      int cnt = 0;
      for (int i = 0; i < nall; i++) {
        u32 *w = all[i];
        for (int x = 0; x < 6; x++) for (int y = x + 1; y < 6; y++) if (w[y] < w[x]) { u32 t = w[x]; w[x] = w[y]; w[y] = t; }
        int dup = 0; for (int j = 0; j < i && !dup; j++) if (!memcmp(all[j], w, 24)) dup = 1;
        if (dup) continue;
        printf("  word %2d:", ++cnt); for (int x = 0; x < 6; x++) printf(" %x", w[x]); printf("\n");
      }
    }
  }
  if (strcmp(mode, "six") && strcmp(mode, "list")) {
    // eight-point words: two zero-sum 4-sets with equal (sum delta, sum delta^3)
    size_t cap = (size_t)((double)n * n * n / 24 + 1024), len = 0; rec4 *buf = malloc(cap * sizeof(rec4));
    for (int p1 = 1; p1 < n; p1++) for (int p2 = p1 + 1; p2 < n; p2++) for (int p3 = p2 + 1; p3 < n; p3++) {
      int p4 = p1 ^ p2 ^ p3; if (p4 <= p3) continue;
      buf[len++] = (rec4){del[p1] ^ del[p2] ^ del[p3] ^ del[p4], del3[p1] ^ del3[p2] ^ del3[p3] ^ del3[p4], {p1, p2, p3, p4}};
    }
    qsort(buf, len, sizeof(rec4), cmp4);
    double found = 0; u32 ex[8]; int have = 0;
    for (size_t i = 0; i < len;) {
      size_t j = i; while (j < len && buf[j].k1 == buf[i].k1 && buf[j].k2 == buf[i].k2) j++;
      for (size_t x = i; x < j; x++) for (size_t y = x + 1; y < j; y++) {
        for (int s = 0; s < 4; s++) for (int t = 0; t < 4; t++) if (buf[x].id[s] == buf[y].id[t]) { fprintf(stderr, "overlapping flats with equal keys: contradicts the dual BCH bound\n"); return 1; }
        found++;
        if (!have) { have = 1; memcpy(ex, buf[x].id, 16); memcpy(ex + 4, buf[y].id, 16); }
      }
      i = j;
    }
    double pairs = (double)len * (len - 1) / 2;
    printf("  eight-point words (two zero-sum 4-sets, sum delta = sum delta^3 = 0): %.0f; zero-sum 4-sets: %zu; random model %.4g; ratio %.3f\n", found, len, pairs * pow(2, -2.0 * m), found / (pairs * pow(2, -2.0 * m)));
    if (have) verify(ex, 8, "example (depth 7n/32 - 1)");
    free(buf);
  }
  return 0;
}
