// Researcher 13. Exhaustive common-top classes for n = 32 in GF(2^m), m and the modulus free: all T-subsets of a
// 5-dimensional F_2-subspace D, keyed on (e_1, .., e_g). Generalizes 04_universal32.c (m = 64 only) so that the
// same table can be computed where the coefficients wrap (m about 13 is the leanVM ratio m/N = 2.56 at N = 5).
// Shapes: power (D = span(1, x, .., x^4)), random:<seed>. With a second field the key is the pair of keys in both
// fields: for the power shape that is the F_2[x] model (no wrap at all), for a random shape the formal model.
// For every class with >= 2 members it also counts the pairs that violate the formal congruence
// n_phi(S) = n_phi(S') mod 2^(a+1), 2^a <= g < 2^(a+1) (the non-formal pairs).
// usage: 13_ct32 T g shape m r [m2 r2]         4 threads
// build: cc -O2 -mcpu=native -o 13_ct32 13_ct32.c -lpthread
#include "13_gf.h"
#include <pthread.h>

#define GMAX 8
static int T, G, nemb, modulus;
static gf_t F[2];
static u64 pts[2][32];
static u32 hmask[32];
typedef struct { u64 key; u32 mask; } rec;
typedef struct { rec *buf; size_t len, cap; int sigma; size_t nclasses, pairs, badcong, best, hist[64]; } job;

static void dfs(job *J, int next, int size, u32 mask, int x, u64 e[2][GMAX + 1]) {
  if (size == T) {
    if (x != J->sigma) return;
    u64 h = 0x9e3779b97f4a7c15ull;
    for (int b = 0; b < nemb; b++) for (int j = 1; j <= G; j++) { h ^= e[b][j]; h *= 0xff51afd7ed558ccdull; h ^= h >> 29; }
    if (J->len == J->cap) { J->cap = J->cap ? 2 * J->cap : 1 << 20; J->buf = realloc(J->buf, J->cap * sizeof(rec)); }
    J->buf[J->len].key = h; J->buf[J->len].mask = mask; J->len++;
    return;
  }
  if (32 - next < T - size) return;
  for (int i = next; i < 32; i++) {
    u64 f[2][GMAX + 1];
    for (int b = 0; b < nemb; b++) {
      f[b][0] = 1;
      for (int j = 1; j <= G; j++) f[b][j] = e[b][j] ^ gf_mul(&F[b], e[b][j - 1], pts[b][i]);
    }
    dfs(J, i + 1, size + 1, mask | (1u << i), x ^ i, f);
  }
}
static int cmp(const void *a, const void *b) { u64 x = ((const rec *)a)->key, y = ((const rec *)b)->key; return x < y ? -1 : x > y; }
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER; static int nextsigma;
static job jobs[32];
static void *worker(void *arg) {
  (void)arg;
  for (;;) {
    pthread_mutex_lock(&mu); int s = nextsigma++; pthread_mutex_unlock(&mu);
    if (s >= 32) return 0;
    job *J = &jobs[s]; J->sigma = s;
    u64 e[2][GMAX + 1]; memset(e, 0, sizeof e); e[0][0] = e[1][0] = 1;
    dfs(J, 0, 0, 0, 0, e);
    qsort(J->buf, J->len, sizeof(rec), cmp);
    for (size_t a = 0; a < J->len;) {
      size_t t = a + 1; while (t < J->len && J->buf[t].key == J->buf[a].key) t++;
      size_t c = t - a;
      if (c >= 2) {
        J->nclasses++; if (c < 64) J->hist[c]++; if (c > J->best) J->best = c;
        u64 *rv = malloc(c * sizeof(u64));
        for (size_t i = 0; i < c; i++) {
          u32 A = J->buf[a + i].mask; u64 h = 0;
          for (int phi = 1; phi < 32; phi++) h = h * 1000003ull + (u64)(__builtin_popcount(A & hmask[phi]) % modulus);
          rv[i] = h;
        }
        if (c > 4096) radix_sort(rv, c);
        else for (size_t i = 1; i < c; i++) { u64 v = rv[i]; size_t j = i; while (j > 0 && rv[j - 1] > v) { rv[j] = rv[j - 1]; j--; } rv[j] = v; }
        size_t same = 0;
        for (size_t i = 0; i < c;) { size_t j = i; while (j < c && rv[j] == rv[i]) j++; same += (j - i) * (j - i - 1) / 2; i = j; }
        J->pairs += c * (c - 1) / 2; J->badcong += c * (c - 1) / 2 - same;
        free(rv);
      }
      a = t;
    }
    free(J->buf); J->buf = 0;
  }
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: T g shape m r [m2 r2]\n"); return 1; }
  T = atoi(argv[1]); G = atoi(argv[2]); const char *shape = argv[3];
  if (G > GMAX) return 1;
  gf_init(&F[0], atoi(argv[4]), strtoull(argv[5], 0, 0)); nemb = 1;
  if (argc >= 8) { gf_init(&F[1], atoi(argv[6]), strtoull(argv[7], 0, 0)); nemb = 2; }
  for (int b = 0; b < nemb; b++) {
    u64 basis[5];
    if (!strncmp(shape, "random", 6)) {
      rng_state = strtoull(shape + 7, 0, 10) * 0x2545F4914F6CDD1Dull + 77 * b + 1;
      for (;;) {
        for (int i = 0; i < 5; i++) basis[i] = rnd64() & F[b].mask;
        int ok = 1; for (int x = 1; x < 32 && ok; x++) { u64 z = 0; for (int j = 0; j < 5; j++) if (x >> j & 1) z ^= basis[j]; if (!z) ok = 0; }
        if (ok) break;
      }
    } else for (int i = 0; i < 5; i++) basis[i] = 1ull << i;
    for (int i = 0; i < 32; i++) { pts[b][i] = 0; for (int j = 0; j < 5; j++) if (i >> j & 1) pts[b][i] ^= basis[j]; }
  }
  for (int phi = 0; phi < 32; phi++) { hmask[phi] = 0; for (int x = 0; x < 32; x++) if (__builtin_parity(x & phi)) hmask[phi] |= 1u << x; }
  int a = 0; while ((2 << a) <= G) a++;
  modulus = 2 << a;
  pthread_t th[4]; for (int i = 0; i < 4; i++) pthread_create(&th[i], 0, worker, 0);
  for (int i = 0; i < 4; i++) pthread_join(th[i], 0);
  size_t nclasses = 0, pairs = 0, bad = 0, best = 0, hist[64]; memset(hist, 0, sizeof hist);
  for (int s = 0; s < 32; s++) { nclasses += jobs[s].nclasses; pairs += jobs[s].pairs; bad += jobs[s].badcong; if (jobs[s].best > best) best = jobs[s].best; for (int c = 0; c < 64; c++) hist[c] += jobs[s].hist[c]; }
  printf("T=%d g=%d shape=%s m=%d", T, G, shape, F[0].m); if (nemb == 2) printf("+%d", F[1].m);
  printf(": classes>=2 %zu, largest %zu, pairs %zu, non-formal pairs (congruence mod %d fails) %zu\n  sizes:", nclasses, best, pairs, modulus, bad);
  for (int c = 2; c < 64; c++) if (hist[c]) printf(" %d:%zu", c, hist[c]);
  printf("\n");
  return 0;
}
