// Researcher 27. All four-member lists on a 16-point generic subspace domain, in the syndrome form.
//
//   cc -O2 -o 27_lists 27_lists.c -lpthread
//   ./27_lists k T [seed] [threads] [real] [pairlo pairhi]     (only the rooted pairs with index in [pairlo, pairhi))
//
// Members of a list at agreement T = n - t are t-sets E (error supports) with the syndrome s in U_E = span{(a^i)_{i<M}:
// a in E}, M = n - k, that is: s kills x^l Z_E for l < m = T - k. The program takes E_0 over the orbits of AGL(4,2),
// E_1 over the orbits of Stab(E_0), every E_2, computes the syndrome space of the triple (dimension d - m when the
// triple is generic, d = M - 2m), and scans every E_3 after E_2 for a common nonzero syndrome. Each hit is turned into
// codewords and analysed (27_common.h). Counts are weighted so that the first column is the exact number of unordered
// quadruples of error sets {E_0, .., E_3} carrying a list of four distinct codewords.
// With real = 1 the domain is span(1, x, x^2, x^3) and only translations are used as symmetries.
// The "flag bound" reported in the output is the formula exc_I <= (max over the five cross-ratio functions of
// |Pi| - 1) + (|Pi(Xi)| - 1), with exc_I = I - 3 delta - 2. It is the natural guess and it is false (note 27, 3.2).
// 27_summary.py computes J = pair + 2 trip + dbl, excJ = J - 3 delta - 2 and the check of Conjecture Q from the classes.
#include "27_common.h"
#include <pthread.h>
static int K, T, tt, M, mm, dd, NTH = 4;
static int ns; static uint16_t *smask; static int *sidx; static u64 *loc; // loc[s][0..tt]
#define LOC(s) (loc + (size_t)(s) * (tt + 1))
static int ng; static uint8_t (*grp)[16];
static inline unsigned ap(const uint8_t *p, unsigned mask) { unsigned r = 0; while (mask) { int b = __builtin_ctz(mask); mask &= mask - 1; r |= 1u << p[b]; } return r; }
static inline int pc(unsigned x) { return __builtin_popcount(x); }

static void build_group(int full) {
  if (!full) { ng = 16; grp = malloc(16 * 16); for (int t = 0; t < 16; t++) for (int x = 0; x < 16; x++) grp[t][x] = x ^ t; return; }
  grp = malloc((size_t)322560 * 16); ng = 0;
  for (int c0 = 1; c0 < 16; c0++) for (int c1 = 1; c1 < 16; c1++) { if (c1 == c0) continue;
    for (int c2 = 1; c2 < 16; c2++) { if (c2 == c0 || c2 == c1 || c2 == (c0 ^ c1)) continue;
      for (int c3 = 1; c3 < 16; c3++) { int sp[8] = {0, c0, c1, c0 ^ c1, c2, c2 ^ c0, c2 ^ c1, c2 ^ c0 ^ c1}; int bad = 0; for (int i = 0; i < 8; i++) if (sp[i] == c3) bad = 1; if (bad) continue;
        int c[4] = {c0, c1, c2, c3};
        for (int t = 0; t < 16; t++) { for (int x = 0; x < 16; x++) { int v = t; for (int i = 0; i < 4; i++) if (x >> i & 1) v ^= c[i]; grp[ng][x] = v; } ng++; } } } }
}

static void locator(unsigned R, u64 *z) { z[0] = 1; int d = 0; for (int p = 0; p < 16; p++) if (R >> p & 1) { z[d + 1] = 0; for (int j = d + 1; j >= 1; j--) z[j] = z[j - 1] ^ mul(z[j], pts[p]); z[0] = mul(z[0], pts[p]); d++; } }

static inline u64 dot(const u64 *a, const u64 *b, int len) { // lazy reduction
#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
  poly128_t acc = 0; for (int i = 0; i < len; i++) acc ^= vmull_p64(a[i], b[i]);
  u64 lo = (u64)acc, hi = (u64)(acc >> 64); poly128_t q = vmull_p64(hi, 0x1b); lo ^= (u64)q; lo ^= (u64)vmull_p64((u64)(q >> 64), 0x1b); return lo;
#else
  u64 s = 0; for (int i = 0; i < len; i++) s ^= mul(a[i], b[i]); return s;
#endif
}

// kernel of an r x c matrix (row-major, destroyed); returns dimension, basis in Kb (each of length c)
static int kernel(u64 *A, int r, int c, u64 *Kb) {
  int piv[64], isp[64], rank = 0; memset(isp, 0, sizeof isp);
  for (int cc = 0; cc < c && rank < r; cc++) {
    int p = rank; while (p < r && !A[p * c + cc]) p++;
    if (p == r) continue;
    if (p != rank) for (int j = 0; j < c; j++) { u64 x = A[p * c + j]; A[p * c + j] = A[rank * c + j]; A[rank * c + j] = x; }
    u64 iv = inv(A[rank * c + cc]);
    for (int j = cc; j < c; j++) A[rank * c + j] = mul(A[rank * c + j], iv);
    for (int i = 0; i < r; i++) if (i != rank && A[i * c + cc]) { u64 f = A[i * c + cc]; for (int j = cc; j < c; j++) A[i * c + j] ^= mul(f, A[rank * c + j]); }
    piv[rank] = cc; isp[cc] = 1; rank++;
  }
  int kd = 0;
  for (int cc = 0; cc < c; cc++) if (!isp[cc]) { u64 *v = Kb + kd * c; memset(v, 0, c * sizeof(u64)); v[cc] = 1; for (int i = 0; i < rank; i++) v[piv[i]] = A[i * c + cc]; kd++; }
  return kd;
}

static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static double total = 0, nviol = 0; static long nhit = 0, ndegen = 0;
static u64 Vinv[16][16];
static char exkey[MAXKEY][120];

static void handle(const unsigned E[4], const u64 *y, double w, int kap) {
  // errors e_i on E_i from the syndrome
  u64 ev[4][16]; memset(ev, 0, sizeof ev);
  for (int i = 0; i < 4; i++) {
    int ix[16], c = 0; for (int p = 0; p < 16; p++) if (E[i] >> p & 1) ix[c++] = p;
    u64 A[16 * 17];
    u64 pw[16]; for (int a = 0; a < tt; a++) pw[a] = 1;
    for (int j = 0; j < tt; j++) { for (int a = 0; a < tt; a++) { A[j * (tt + 1) + a] = pw[a]; pw[a] = mul(pw[a], pts[ix[a]]); } A[j * (tt + 1) + tt] = y[j]; }
    for (int cc = 0; cc < tt; cc++) { int p = cc; while (!A[p * (tt + 1) + cc]) p++;
      if (p != cc) for (int j = 0; j <= tt; j++) { u64 x = A[p * (tt + 1) + j]; A[p * (tt + 1) + j] = A[cc * (tt + 1) + j]; A[cc * (tt + 1) + j] = x; }
      u64 iv = inv(A[cc * (tt + 1) + cc]); for (int j = cc; j <= tt; j++) A[cc * (tt + 1) + j] = mul(A[cc * (tt + 1) + j], iv);
      for (int r = 0; r < tt; r++) if (r != cc && A[r * (tt + 1) + cc]) { u64 f = A[r * (tt + 1) + cc]; for (int j = cc; j <= tt; j++) A[r * (tt + 1) + j] ^= mul(f, A[cc * (tt + 1) + j]); } }
    for (int a = 0; a < tt; a++) ev[i][ix[a]] = A[a * (tt + 1) + tt];
  }
  poly u[3];
  for (int i = 1; i < 4; i++) {
    u64 val[16]; for (int p = 0; p < 16; p++) val[p] = ev[0][p] ^ ev[i][p];
    poly *q = &u[i - 1]; q->d = K - 1;
    for (int j = 0; j < K; j++) q->c[j] = dot(Vinv[j], val, K);
    pnorm(q);
    for (int p = 0; p < 16; p++) if (peval(q, pts[p]) != val[p]) { fprintf(stderr, "not a codeword difference: bug\n"); exit(1); }
  }
  info4 o; analyse4(u, &o);
  char key[300];
  if (!o.degenerate) { int p = sprintf(key, "kap=%d gamD=%d | ", kap, o.gamD); key4(&o, key + p); }
  pthread_mutex_lock(&mu);
  nhit++;
  if (o.degenerate) { ndegen++; pthread_mutex_unlock(&mu); return; }
  total += w;
  if (o.npair + 2 * o.ntrip + o.ndbl + 3 * o.gamD < 4 * T - 16) { fprintf(stderr, "count bug\n"); exit(1); }
  int before = nkey; hadd(key, w);
  if (nkey > before) sprintf(exkey[nkey - 1], "E = %04x %04x %04x %04x", E[0], E[1], E[2], E[3]);
  if (o.exc > o.flag) nviol += w;
  pthread_mutex_unlock(&mu);
}

// two equal members: the syndrome lies in U of the intersection F of two error sets (it kills x^l Z_F, l < M - |F|)
static int degenerate_y(const unsigned E[4], const u64 *y) {
  for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) {
    unsigned F = E[i] & E[j]; u64 z[17]; z[0] = 1; int d = 0;
    for (int p = 0; p < 16; p++) if (F >> p & 1) { z[d + 1] = 0; for (int q = d + 1; q >= 1; q--) z[q] = z[q - 1] ^ mul(z[q], pts[p]); z[0] = mul(z[0], pts[p]); d++; }
    int ok = 1; for (int l = 0; l < M - d && ok; l++) if (dot(z, y + l, d + 1)) ok = 0;
    if (ok) return 1;
  }
  return 0;
}
static long ndeg_fast = 0;
static unsigned gE0, gE1; static double gw; static int gthread_n;
static void *worker(void *arg) {
  int th = (int)(long)arg;
  u64 *A = malloc(sizeof(u64) * 3 * mm * M), *Kb = malloc(sizeof(u64) * M * M), W[16 * 16], Wk[16 * 16], y[32];
  for (int s2 = th; s2 < ns; s2 += gthread_n) {
    unsigned E2 = smask[s2];
    if (E2 == gE0 || E2 == gE1 || pc(E2 & gE0) > dd - 1 || pc(E2 & gE1) > dd - 1) continue;
    memset(A, 0, sizeof(u64) * 3 * mm * M);
    const u64 *z[3] = {LOC(sidx[gE0]), LOC(sidx[gE1]), LOC(s2)};
    for (int i = 0; i < 3; i++) for (int l = 0; l < mm; l++) for (int j = 0; j <= tt; j++) A[(i * mm + l) * M + l + j] = z[i][j];
    int kap = kernel(A, 3 * mm, M, Kb);
    if (kap == 0) continue;
    if (kap == 1) { // degenerate triple: the syndrome is supported on the intersection of two error sets (two equal members)
      unsigned prs[3] = {gE0 & gE1, gE0 & E2, gE1 & E2}; int bad = 0;
      for (int q = 0; q < 3 && !bad; q++) { u64 B[16 * 17]; int ix[16], c = 0; for (int p = 0; p < 16; p++) if (prs[q] >> p & 1) ix[c++] = p;
        // is y in the span of the columns of the points of prs[q]? rank test of the M x (c+1) matrix
        for (int j = 0; j < M; j++) { for (int a = 0; a < c; a++) B[j * (c + 1) + a] = j == 0 ? 1 : mul(B[(j - 1) * (c + 1) + a], pts[ix[a]]); B[j * (c + 1) + c] = Kb[j]; }
        u64 Kt[17 * 17]; if (kernel(B, M, c + 1, Kt) > 0) bad = 1; }
      if (bad) continue; }
    for (int s3 = s2 + 1; s3 < ns; s3++) {
      unsigned E3 = smask[s3];
      if (pc(E3 & E2) > dd - 1 || pc(E3 & gE0) > dd - 1 || pc(E3 & gE1) > dd - 1 || E3 == gE0 || E3 == gE1) continue;
      const u64 *z3 = LOC(s3);
      if (kap == 1) {
        int ok = 1; for (int l = 0; l < mm && ok; l++) if (dot(z3, Kb + l, tt + 1)) ok = 0;
        if (!ok) continue;
        unsigned E[4] = {gE0, gE1, E2, E3}; handle(E, Kb, gw, kap);
      } else {
        for (int l = 0; l < mm; l++) for (int j = 0; j < kap; j++) W[l * kap + j] = dot(z3, Kb + j * M + l, tt + 1);
        if (kap == 2 && mm >= 2) { if (mul(W[0], W[3]) != mul(W[1], W[2])) continue; }
        int kd = kernel(W, mm, kap, Wk);
        if (kd == 0) continue;
        u64 lam[16]; memset(lam, 0, sizeof lam);
        for (int a = 0; a < kd; a++) { u64 r = kd == 1 ? 1 : (rnd() | 1); for (int j = 0; j < kap; j++) lam[j] ^= mul(r, Wk[a * kap + j]); }
        for (int j = 0; j < M; j++) { y[j] = 0; for (int a = 0; a < kap; a++) y[j] ^= mul(lam[a], Kb[a * M + j]); }
        unsigned E[4] = {gE0, gE1, E2, E3};
        if (degenerate_y(E, y)) { __sync_fetch_and_add(&ndeg_fast, 1); continue; }
        handle(E, y, gw, kap * 10 + kd);
      }
    }
  }
  free(A); free(Kb); return NULL;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 27_lists k T [seed] [threads] [real] [pairlo pairhi]\n"); return 1; }
  K = atoi(argv[1]); T = atoi(argv[2]); u64 seed = argc > 3 ? strtoull(argv[3], 0, 10) : 1; NTH = argc > 4 ? atoi(argv[4]) : 4;
  int real = argc > 5 ? atoi(argv[5]) : 0; long pairlo = argc > 6 ? atol(argv[6]) : 0, pairhi = argc > 7 ? atol(argv[7]) : -1;
  domain_init(4, seed, real);
  tt = 16 - T; M = 16 - K; mm = T - K; dd = M - 2 * mm;
  printf("n=16 k=%d T=%d t=%d M=%d m=%d d=%d ; generic points allow %d members ; e4 = 4T-n-3k+1 = %d ; e3 = 3T-n-2k+1 = %d\n", K, T, tt, M, mm, dd, (M - 1) / mm, 4 * T - 16 - 3 * K + 1, 3 * T - 16 - 2 * K + 1);
  // inverse Vandermonde on the first K points
  { u64 A[16][32]; u64 pw; for (int i = 0; i < K; i++) { pw = 1; for (int j = 0; j < K; j++) { A[i][j] = pw; pw = mul(pw, pts[i]); A[i][K + j] = i == j; } }
    for (int c = 0; c < K; c++) { int p = c; while (!A[p][c]) p++; if (p != c) for (int j = 0; j < 2 * K; j++) { u64 x = A[p][j]; A[p][j] = A[c][j]; A[c][j] = x; }
      u64 iv = inv(A[c][c]); for (int j = 0; j < 2 * K; j++) A[c][j] = mul(A[c][j], iv);
      for (int r = 0; r < K; r++) if (r != c && A[r][c]) { u64 f = A[r][c]; for (int j = 0; j < 2 * K; j++) A[r][j] ^= mul(f, A[c][j]); } }
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) Vinv[i][j] = A[i][K + j]; }
  smask = malloc(65536 * sizeof(uint16_t)); sidx = malloc(65536 * sizeof(int)); ns = 0;
  for (unsigned s = 0; s < 65536; s++) { sidx[s] = -1; if (pc(s) == tt) { sidx[s] = ns; smask[ns++] = s; } }
  loc = malloc((size_t)ns * (tt + 1) * sizeof(u64)); for (int s = 0; s < ns; s++) locator(smask[s], LOC(s));
  build_group(!real);
  char *seen = calloc(ns, 1), *seen1 = malloc(ns); int *stab = malloc(ng * sizeof(int));
  long npairs = 0; int norb = 0;
  for (int s0 = 0; s0 < ns; s0++) {
    if (seen[s0]) continue;
    unsigned E0 = smask[s0]; int nst = 0, osz = 0;
    for (int g = 0; g < ng; g++) { unsigned im = ap(grp[g], E0); if (!seen[sidx[im]]) { seen[sidx[im]] = 1; osz++; } if (im == E0) stab[nst++] = g; }
    norb++;
    memset(seen1, 0, ns);
    for (int s1 = 0; s1 < ns; s1++) {
      if (seen1[s1]) continue;
      unsigned E1 = smask[s1]; int o1 = 0;
      for (int g = 0; g < nst; g++) { unsigned im = ap(grp[stab[g]], E1); if (!seen1[sidx[im]]) { seen1[sidx[im]] = 1; o1++; } }
      if (E1 == E0 || pc(E1 & E0) > dd - 1) continue;
      npairs++;
      if (npairs - 1 < pairlo || (pairhi >= 0 && npairs - 1 >= pairhi)) continue;
      gE0 = E0; gE1 = E1; gw = (double)osz * o1 / 12.0; gthread_n = NTH;
      pthread_t th[16]; for (int i = 0; i < NTH; i++) pthread_create(&th[i], NULL, worker, (void *)(long)i);
      for (int i = 0; i < NTH; i++) pthread_join(th[i], NULL);
    }
  }
  printf("orbits of E0: %d, rooted pairs (E0,E1): %ld (processed [%ld, %ld)), hits %ld (degenerate %ld, and %ld rejected before analysis)\n", norb, npairs, pairlo, pairhi < 0 ? npairs : pairhi, nhit, ndegen, ndeg_fast);
  printf("four-member lists (unordered quadruples of error sets): %.1f ; violations of the flag bound (weighted): %.1f\n", total, nviol);
  printf("    weighted      raw  class\n");
  int *ord = malloc(nkey * sizeof(int)); for (int i = 0; i < nkey; i++) ord[i] = i;
  qsort(ord, nkey, sizeof(int), cmpkey);
  for (int i = 0; i < nkey; i++) printf("%12.1f %9ld  %s   [%s]\n", hcnt[ord[i]], hraw[ord[i]], hkey[ord[i]], exkey[ord[i]]);
  return 0;
}
