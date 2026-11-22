// Researcher 39: affine rank over GF(2^64) of the list of X^(n/2) L_W (|W| = n/8, degree <= n/2) on a generic
// subspace, as a function of N, for the members at agreement 5n/8 (the 56n - 392 simple ones) and for the whole
// list at agreement 19n/32.
//
//   39_rank N seed [stall]
//
// By note 39 Proposition 4.1 every member is the lift, along a subspace Pi of W of index 4, of one of the 15736
// members of the 32-point problem on D/Pi. The program enumerates those 15736 multisets on F_2^5 (as 39_family.c),
// then draws random pairs (Pi, member), builds the locator V(L_Pi(X)) on a random N-dimensional subspace of GF(2^64)
// and reduces its difference with a fixed member against an echelon basis, until "stall" (default 400) consecutive
// samples add nothing. The rank found is a lower bound of the true rank that is exact with overwhelming probability;
// for N = 5, 6, 7 it is compared in note 39 with the exact rank computed by 39_family.c on the whole list.
#include "02_gf.h"
#define N0 5
#define n0 32
static u64 rs;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { unsigned char c[n0]; } mset;
static mset *mem; static size_t nmem, capmem;
static int G[8];
static void try_spectrum(int nout, const int *psi, const int *sg) {
  unsigned char c[n0]; int supp = 0;
  for (int x = 0; x < n0; x++) {
    int s = 0; for (int i = 0; i < nout; i++) s += (__builtin_parity(psi[i] & x) ? -sg[i] : sg[i]);
    int v = G[x >> 2] + 2 * s;
    if (v < 0 || (v & 7)) return;
    c[x] = (unsigned char)(v >> 3); supp += c[x] > 0;
  }
  if (supp < 19) return;
  if (nmem == capmem) { capmem = capmem * 2 + 4096; mem = realloc(mem, capmem * sizeof(mset)); }
  memcpy(mem[nmem++].c, c, n0);
}
static void outside(int maxout) {
  int psi[3], sg[3];
  try_spectrum(0, psi, sg);
  for (int a = 1; a < n0; a++) { if (!(a & 3)) continue; psi[0] = a;
    for (int s0 = -1; s0 <= 1; s0 += 2) { sg[0] = s0; try_spectrum(1, psi, sg); }
    if (maxout < 2) continue;
    for (int b = a + 1; b < n0; b++) { if (!(b & 3)) continue; psi[1] = b;
      for (int s = 0; s < 4; s++) { sg[0] = s & 1 ? -1 : 1; sg[1] = s & 2 ? -1 : 1; try_spectrum(2, psi, sg); }
      for (int c = b + 1; c < n0; c++) { if (!(c & 3)) continue; psi[2] = c;
        for (int s = 0; s < 8; s++) { sg[0] = s & 1 ? -1 : 1; sg[1] = s & 2 ? -1 : 1; sg[2] = s & 4 ? -1 : 1; try_spectrum(3, psi, sg); } }
    }
  }
}
static void enumerate(void) {
  int a[8];
  for (int s = 0; s < 128; s++) { for (int t = 1; t < 8; t++) a[t] = (s >> (t - 1) & 1) ? -1 : 1; for (int y = 0; y < 8; y++) { G[y] = 5; for (int t = 1; t < 8; t++) G[y] += __builtin_parity(t & y) ? -a[t] : a[t]; } outside(3); }
  for (int p = 1; p < 8; p++) for (int s = 0; s < 128; s++) { for (int t = 1; t < 8; t++) a[t] = (s >> (t - 1) & 1) ? -1 : 1; a[p] *= 3; for (int y = 0; y < 8; y++) { G[y] = 5; for (int t = 1; t < 8; t++) G[y] += __builtin_parity(t & y) ? -a[t] : a[t]; } outside(1); }
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 39_rank N seed [stall]\n"); return 1; }
  gf_init(64, 0x1b);
  int N = atoi(argv[1]), n = 1 << N, NW = N - 3, stall = argc > 3 ? atoi(argv[3]) : 400;
  if (N < 5 || N > 14) { fprintf(stderr, "5 <= N <= 14\n"); return 1; }
  rs = 88172645463325252ull ^ (strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ull); for (int i = 0; i < 20; i++) rnd();
  u64 basis[16]; for (int i = 0; i < N; i++) basis[i] = rnd();
  enumerate();
  size_t nsimple = 0; size_t *simple = malloc(nmem * sizeof(size_t));
  for (size_t m = 0; m < nmem; m++) { int mx = 0; for (int x = 0; x < n0; x++) if (mem[m].c[x] > mx) mx = mem[m].c[x]; if (mx == 1) simple[nsimple++] = m; }
  int len = n / 2 + 1, mass = 5 * n / 8;
  u64 *P0 = 0, *P = malloc((mass + 1) * sizeof(u64)), *pw = malloc((mass + 1) * sizeof(u64)), *tmp = malloc((mass + 1) * sizeof(u64));
  u64 **bas = malloc(len * sizeof(u64 *)); int *pv = malloc(len * sizeof(int)); int rank = 0, rank_simple = 0; long samples_tot = 0;
  for (int pass = 0; pass < 2; pass++) {
    int idle = 0; long samples = 0;
    while (idle < stall && rank < len) {
      // random Pi: kernel in W of two independent functionals r1, r2 on W
      int r1, r2;
      if (NW == 2) { r1 = 1; r2 = 2; } else do { r1 = 1 + rnd() % ((1 << NW) - 1); r2 = 1 + rnd() % ((1 << NW) - 1); } while (r1 == r2);
      // basis of Pi and preimages of the 5 coordinates of the quotient
      int pb[16], np = 0, pre[5] = {-1, -1, 0, 0, 0};
      { // gaussian elimination on the two functionals: find pivots
        int p1 = __builtin_ctz(r1), rr2 = (r2 >> p1 & 1) ? r2 ^ r1 : r2, p2 = __builtin_ctz(rr2); int rr1 = (r1 >> p2 & 1) ? r1 ^ rr2 : r1;
        // now rr1 has bit p1, not p2; rr2 has bit p2, not p1
        for (int i = 0; i < NW; i++) { if (i == p1 || i == p2) continue; int v = 1 << i; if (rr1 >> i & 1) v |= 1 << p1; if (rr2 >> i & 1) v |= 1 << p2; pb[np++] = v; }
        // preimage of (1,0): x with r1.x = 1, r2.x = 0; of (0,1): r1.x = 0, r2.x = 1 (in terms of rr1, rr2 then transformed back)
        int e1 = 1 << p1, e2 = 1 << p2; // rr1.e1 = 1, rr2.e1 = 0; rr1.e2 = 0, rr2.e2 = 1
        // r1 = rr1 or rr1 ^ rr2..., solve by trying the four combinations
        int cand[4] = {0, e1, e2, e1 ^ e2};
        for (int q = 0; q < 4; q++) { int a = __builtin_parity(r1 & cand[q]), b = __builtin_parity(r2 & cand[q]); if (a == 1 && b == 0) pre[0] = cand[q]; if (a == 0 && b == 1) pre[1] = cand[q]; }
        for (int t = 0; t < 3; t++) pre[2 + t] = 1 << (NW + t);
      }
      // L_Pi as a linearized polynomial: coefficients lc[i] of X^(2^i)
      u64 lc[16]; memset(lc, 0, sizeof lc); lc[0] = 1; int ld = 0;
      for (int j = 0; j < np; j++) {
        u64 v = 0; for (int i = 0; i < N; i++) if (pb[j] >> i & 1) v ^= basis[i];
        u64 lv = 0, xp = v; for (int i = 0; i <= ld; i++) { lv ^= gmul(lc[i], xp); xp = gmul(xp, xp); }
        u64 nc[16]; memset(nc, 0, sizeof nc);
        for (int i = 0; i <= ld; i++) { nc[i + 1] ^= gmul(lc[i], lc[i]); nc[i] ^= gmul(lv, lc[i]); }
        ld++; memcpy(lc, nc, sizeof lc);
      }
      u64 lam5[5];
      for (int t = 0; t < 5; t++) { u64 v = 0; for (int i = 0; i < N; i++) if (pre[t] >> i & 1) v ^= basis[i]; u64 lv = 0, xp = v; for (int i = 0; i <= ld; i++) { lv ^= gmul(lc[i], xp); xp = gmul(xp, xp); } lam5[t] = lv; }
      size_t m = pass == 0 ? simple[rnd() % nsimple] : rnd() % nmem;
      // V(Y) = prod (Y - lam_y)^c(y), degree 20
      u64 V[21]; memset(V, 0, sizeof V); V[0] = 1; int vd = 0;
      for (int y = 0; y < n0; y++) { u64 lam = 0; for (int t = 0; t < 5; t++) if (y >> t & 1) lam ^= lam5[t];
        for (int e = 0; e < mem[m].c[y]; e++) { for (int j = vd + 1; j >= 1; j--) V[j] = V[j - 1] ^ gmul(V[j], lam); V[0] = gmul(V[0], lam); vd++; } }
      // P = V(L_Pi(X)): Horner with sparse multiplication by L_Pi
      int unit = 1 << ld; memset(P, 0, (mass + 1) * sizeof(u64)); P[0] = V[20]; int pd = 0;
      for (int j = 19; j >= 0; j--) {
        memset(tmp, 0, (mass + 1) * sizeof(u64));
        for (int i = 0; i <= ld; i++) { u64 cf = lc[i]; if (!cf) continue; int sh = 1 << i; for (int d = 0; d <= pd; d++) if (P[d]) tmp[d + sh] ^= gmul(cf, P[d]); }
        pd += unit; memcpy(P, tmp, (mass + 1) * sizeof(u64)); P[0] ^= V[j];
      }
      samples++;
      if (!P0) { P0 = malloc((mass + 1) * sizeof(u64)); memcpy(P0, P, (mass + 1) * sizeof(u64)); continue; }
      for (int j = 0; j <= mass; j++) P[j] ^= P0[j];
      for (int j = len; j <= mass; j++) if (P[j]) { printf("a difference has degree > n/2!\n"); return 1; }
      for (int b = 0; b < rank; b++) if (P[pv[b]]) { u64 f = P[pv[b]]; u64 *bb = bas[b]; for (int j = 0; j <= pv[b]; j++) P[j] ^= gmul(f, bb[j]); }
      int top = len - 1; while (top >= 0 && !P[top]) top--;
      if (top < 0) { idle++; continue; }
      idle = 0; u64 iv = ginv(P[top]); bas[rank] = malloc(len * sizeof(u64)); for (int j = 0; j < len; j++) bas[rank][j] = j <= top ? gmul(P[j], iv) : 0; pv[rank++] = top;
    }
    if (pass == 0) rank_simple = rank;
    samples_tot += samples;
  }
  (void)pw;
  printf("N=%d n=%d: affine rank of the members at agreement 5n/8: %d (4N - 7 = %d); of the whole list at 19n/32: %d (N^2 - 3N + 5 = %d); polynomials of degree <= n/2: %d; %ld samples\n", N, n, rank_simple, 4 * N - 7, rank, N * N - 3 * N + 5, len, samples_tot);
  return 0;
}
