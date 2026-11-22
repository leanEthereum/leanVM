// Referee 46: note 37 Proposition 2.1 at sizes where it says something (n = 2^12 .. 2^16).
// Samples members of the 19n/32 family of note 39 Proposition 4.1 (type (b), agreement sets invariant under a
// subspace of size n/32) and of the 5n/8 family (type (a2), invariant under n/16), by their coordinate
// description, removes a random set P of density lambda from every agreement set (the word is changed on P to a
// value no codeword takes, so the codewords stay and agree exactly on S \ P), and measures the self-intersections
// |S' & (S' + a)| for every a != 0 by a Walsh-Hadamard autocorrelation.
// cc -O2 -o 46_perturb 46_perturb.c -lm ; ./46_perturb N lambda count seed
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
static u64 rs;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int par(unsigned v) { return __builtin_popcount(v) & 1; }
static void wht(int64_t *a, int n) {
  for (int h = 1; h < n; h <<= 1)
    for (int i = 0; i < n; i += 2 * h)
      for (int j = i; j < i + h; j++) { int64_t x = a[j], y = a[j + h]; a[j] = x + y; a[j + h] = x - y; }
}
// self-intersections: out[a] = |S & (S + a)|; returns |S|
static int autocorr(const unsigned char *S, int n, int64_t *buf) {
  int sz = 0;
  for (int i = 0; i < n; i++) { buf[i] = S[i]; sz += S[i]; }
  wht(buf, n);
  for (int i = 0; i < n; i++) buf[i] = buf[i] * buf[i];
  wht(buf, n);
  for (int i = 0; i < n; i++) buf[i] /= n;
  return sz;
}
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: 46_perturb N lambda count seed\n"); return 1; }
  int N = atoi(argv[1]); double lam = atof(argv[2]); int count = atoi(argv[3]); rs = 88172645463325252ULL ^ (strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL);
  int n = 1 << N, sh = N - 3, wn = n / 8;
  unsigned char *S = malloc(n), *S2 = malloc(n), *P = malloc(n);
  int64_t *buf = malloc(n * sizeof(int64_t));
  int np = 0; for (int i = 0; i < n; i++) { P[i] = ((double)(rnd() >> 11) / 9007199254740992.0) < lam; np += P[i]; }
  double t = sqrt(n * log(2.0 * count * n));
  printf("N=%d n=%d lambda=%.3f |P|=%d, %d members, t = sqrt(n ln(2Ln)) = %.1f\n", N, n, lam, np, count, t);
  long inv_before = 0, inv_after = 0, viol_size = 0, viol_auto = 0; double worst_ratio = 0, mean_before = 0, mean_after = 0, mean_size = 0, worst_margin = -1e18;
  for (int c = 0; c < count; c++) {
    unsigned h = (unsigned)(1 + rnd() % 7) << sh; int s = rnd() & 1;
    int type = c & 1;
    if (type == 0) { // (b)
      unsigned p1, p2;
      for (;;) {
        p1 = rnd() % n; p2 = rnd() % n;
        int ok = 1;
        for (int cc = 1; cc < 8 && ok; cc++) { unsigned e = ((cc & 1) ? h : 0) ^ ((cc & 2) ? p1 : 0) ^ ((cc & 4) ? p2 : 0); if (e == 0) ok = 0; if ((e & (wn - 1)) == 0 && e != h) ok = 0; }
        if (ok) break;
      }
      int ca = rnd() & 3, cb = rnd() & 3, y0;
      do { y0 = rnd() & 7; } while (par(((unsigned)y0 << sh) & h) == s);
      for (int i = 0; i < n; i++) {
        int code = par(i & p1) | (par(i & p2) << 1);
        if (par(i & h) == s) S[i] = (code != ca); else S[i] = ((i >> sh) == y0) || (code == cb);
      }
    } else { // (a2)
      unsigned psi; do { psi = rnd() % n; } while ((psi & (wn - 1)) == 0);
      int cc = rnd() & 1, y0;
      do { y0 = rnd() & 7; } while (par(((unsigned)y0 << sh) & h) == s);
      for (int i = 0; i < n; i++) { if (par(i & h) == s) S[i] = (par(i & psi) == cc); else S[i] = ((i >> sh) != y0); }
    }
    int sz = autocorr(S, n, buf);
    int64_t mb = 0; long stab = 0; for (int a = 1; a < n; a++) { if (buf[a] > mb) mb = buf[a]; if (buf[a] == sz) stab++; }
    if (stab) inv_before++;
    mean_before += (double)mb / sz;
    for (int i = 0; i < n; i++) S2[i] = S[i] && !P[i];
    int sz2 = autocorr(S2, n, buf);
    int64_t ma = 0; long stab2 = 0; for (int a = 1; a < n; a++) { if (buf[a] > ma) ma = buf[a]; if (buf[a] == sz2) stab2++; }
    if (stab2) inv_after++;
    mean_after += (double)ma / sz2; mean_size += (double)sz2 / sz;
    if (fabs(sz2 - (1 - lam) * sz) > t) viol_size++;
    double bound = (1 - lam) * (1 - lam) * sz + t;
    if (ma > bound) viol_auto++;
    if ((double)ma / sz2 > worst_ratio) worst_ratio = (double)ma / sz2;
    if (ma - (1 - lam) * (1 - lam) * sz > worst_margin) worst_margin = ma - (1 - lam) * (1 - lam) * sz;
  }
  printf("before: members with an exact nonzero period of S: %ld of %d; mean of max_a |S&(S+a)|/|S| = %.4f\n", inv_before, count, mean_before / count);
  printf("after : members with an exact nonzero period of S': %ld; mean |S'|/|S| = %.4f (1 - lambda = %.4f); mean of max_a |S'&(S'+a)|/|S'| = %.4f, worst %.4f (a former period gives about 1 - lambda = %.4f, an exact period would give 1)\n",
         inv_after, mean_size / count, 1 - lam, mean_after / count, worst_ratio, 1 - lam);
  printf("        largest max_a |S'&(S'+a)| - (1-lambda)^2 |S| = %.1f (Proposition 2.1 allows t = %.1f); violations of the two inequalities of Proposition 2.1: %ld and %ld\n", worst_margin, t, viol_size, viol_auto);
  return 0;
}
