// Researcher 56. The structural six-point words of the power shape D = span(1, x, .., x^(N-1)) in GF(2^m), at any
// N <= 30 (56-witt-real-field.md, Section 5.2). A functional is a mask phi: f = sum f_i x^i -> sum_{i in phi} f_i.
// The search is restricted to the space Phi of functionals spanned by
//    f_0, f_1, f_2, f_(N-1), f_(N-2), f_(N-3), sum of all f_i, sum over even i, sum over i = 0, 1 mod 4,
//    sum over i = 0 mod 3, sum over i = 1 mod 3
// (the functionals that factor through f mod x^3, the three top coefficients, f mod (x+1)^4 and f mod x^2+x+1,
// partly), which contains every six-point word that the exhaustive search 56_dual finds in a large field at
// N = 8 and N = 9. It lists all 6-subsets Omega of Phi \ 0 with sum of phi = 0 and sum of delta_phi = 0,
// delta_phi = prod of the points off ker(phi) = L_{ker phi}(t). By note 19 (Corollary 1.3, Remark 2.2) each word
// gives 16 pairs of disjoint sets A, B of 3n/16 points with Z_A - Z_B constant. For N <= 13 one pair per word is
// multiplied out.
// usage: 56_struct N m r        (modulus x^m + r)
// build: cc -O2 -mcpu=native -o 56_struct 56_struct.c
#include "13_gf.h"
static gf_t F; static int N;
typedef struct { u64 k; u32 a, b; } rec3;
static int cmp3(const void *a, const void *b) { const rec3 *x = a, *y = b; return x->k < y->k ? -1 : x->k > y->k; }

static u64 delta_of(u32 phi) { // L_{ker phi}(x^p), p the lowest bit of phi
  int p = __builtin_ctz(phi); u64 hb[32]; int k = 0;
  for (int i = 0; i < N; i++) if (i != p) hb[k++] = (phi >> i & 1) ? (1ull << i) ^ (1ull << p) : 1ull << i;
  u64 z = 1ull << p; gf_subspace_eval(&F, hb, N - 1, &z, 1); return z;
}
static int verify(const u32 *phi) { // signs: one minus sign on the first functional; returns deg(Z_A - Z_B)
  int n = 1 << N, na = 0, nb = 0; int *A = malloc(n * sizeof(int)), *B = malloc(n * sizeof(int));
  for (int x = 0; x < n; x++) {
    int s = 0;
    for (int i = 0; i < 6; i++) s += ((i == 0) ^ (__builtin_popcount(phi[i] & x) & 1)) ? -1 : 1;
    if (s == 4) A[na++] = x; else if (s == -4) B[nb++] = x; else if (s) { fprintf(stderr, "not a difference of sets\n"); exit(1); }
  }
  if (na != 3 * n / 16 || nb != na) { fprintf(stderr, "wrong sizes\n"); exit(1); }
  u64 *za = malloc((na + 1) * sizeof(u64)), *zb = malloc((na + 1) * sizeof(u64));
  for (int pass = 0; pass < 2; pass++) {
    u64 *z = pass ? zb : za; int *S = pass ? B : A;
    z[0] = 1; for (int j = 1; j <= na; j++) z[j] = 0;
    for (int t = 0; t < na; t++) { u64 s = (u64)S[t]; for (int j = t + 1; j >= 1; j--) z[j] = z[j - 1] ^ gf_mul(&F, s, z[j]); z[0] = gf_mul(&F, s, z[0]); }
  }
  int deg = -1; for (int j = 0; j <= na; j++) if (za[j] != zb[j]) deg = j;
  free(A); free(B); free(za); free(zb);
  return deg;
}
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: 56_struct N m r\n"); return 1; }
  N = atoi(argv[1]); int m = atoi(argv[2]); u64 r = strtoull(argv[3], 0, 0);
  gf_init(&F, m, r);
  u32 all = (N == 32) ? ~0u : (1u << N) - 1, gen[16]; int ng = 0;
  u32 even = 0, q4 = 0, p30 = 0, p31 = 0;
  for (int i = 0; i < N; i++) { if (i % 2 == 0) even |= 1u << i; if (i % 4 < 2) q4 |= 1u << i; if (i % 3 == 0) p30 |= 1u << i; if (i % 3 == 1) p31 |= 1u << i; }
  u32 cand[11] = {1, 2, 4, 1u << (N - 1), 1u << (N - 2), 1u << (N - 3), all, even, q4, p30, p31};
  u32 ech[32] = {0};
  for (int i = 0; i < 11; i++) { // keep an independent subfamily
    u32 v = cand[i];
    for (int b = N - 1; b >= 0 && v; b--) if (v >> b & 1) { if (ech[b]) v ^= ech[b]; else { ech[b] = v; gen[ng++] = cand[i]; break; } }
  }
  int I = 1 << ng;
  u32 *mask = malloc(I * sizeof(u32)); u64 *del = malloc(I * sizeof(u64));
  for (int idx = 1; idx < I; idx++) { u32 v = 0; for (int i = 0; i < ng; i++) if (idx >> i & 1) v ^= gen[i]; mask[idx] = v; del[idx] = delta_of(v); }
  printf("N=%d GF(2^%d) modulus x^%d+0x%llx power basis; Phi has dimension %d (%d functionals)\n", N, m, m, (unsigned long long)r, ng, I - 1);
  rec3 *buf = malloc(((size_t)I * I / 4 + 16) * sizeof(rec3));
  static u32 words[4096][6]; int nw = 0;
  for (int sig = 0; sig < I; sig++) {
    size_t len = 0;
    for (int p1 = 1; p1 < I; p1++) for (int p2 = p1 + 1; p2 < I; p2++) { int p3 = sig ^ p1 ^ p2; if (p3 > p2) buf[len++] = (rec3){del[p1] ^ del[p2] ^ del[p3], p1, p2}; }
    qsort(buf, len, sizeof(rec3), cmp3);
    for (size_t i = 0; i + 1 < len; i++) if (buf[i].k == buf[i + 1].k) {
      for (size_t y = i + 1; y < len && buf[y].k == buf[i].k; y++) if (nw < 4096) {
        u32 *w = words[nw]; w[0] = mask[buf[i].a]; w[1] = mask[buf[i].b]; w[2] = mask[sig ^ buf[i].a ^ buf[i].b];
        w[3] = mask[buf[y].a]; w[4] = mask[buf[y].b]; w[5] = mask[sig ^ buf[y].a ^ buf[y].b];
        for (int x = 0; x < 6; x++) for (int z = x + 1; z < 6; z++) if (w[z] < w[x]) { u32 t = w[x]; w[x] = w[z]; w[z] = t; }
        int dup = 0; for (int j = 0; j < nw && !dup; j++) if (!memcmp(words[j], w, 24)) dup = 1;
        if (!dup) nw++;
      }
    }
  }
  printf("  %d six-point words with sum phi = 0 and sum delta = 0 in Phi\n", nw);
  for (int i = 0; i < nw; i++) {
    u32 *w = words[i]; u64 s = 0; u32 x = 0;
    for (int j = 0; j < 6; j++) { s ^= delta_of(w[j]); x ^= w[j]; }
    if (s || x) { fprintf(stderr, "recheck failed\n"); return 1; }
    // two planes? the six points are the nonzero points of two 2-dimensional subspaces iff some 3 of them sum to 0
    int planes = 0; for (int a = 0; a < 6; a++) for (int b = a + 1; b < 6; b++) for (int c = b + 1; c < 6; c++) if ((w[a] ^ w[b] ^ w[c]) == 0) planes = 1;
    printf("  word %2d:", i + 1); for (int j = 0; j < 6; j++) printf(" %x", w[j]);
    printf("  [%s]", planes ? "two planes" : "not two planes");
    if (N <= 13) printf("  deg(Z_A - Z_B) = %d with |A| = |B| = %d", verify(w), 3 * (1 << N) / 16);
    printf("\n");
  }
  return 0;
}
