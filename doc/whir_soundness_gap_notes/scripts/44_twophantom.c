// 44_twophantom: data for note 44 section 3.5 (two poles outside D), n = 16.
//
//   cc -O2 -o 44_twophantom 44_twophantom.c
//   ./44_twophantom [seed]
//
// D = span of 4 random elements of GF(2^64). The points 1, 2, 3 (labels in F_2^4) are put in a fibre. Every
// m : D \ {1,2,3} -> {-1,0,1} is enumerated, P_y = prod_x (y + x)^m(x) for the points y with m(y) = 0, and q is the
// polynomial of degree <= 2 with q(y_i) = P_{y_i}, i = 1, 2, 3. Then xi = prod (X + x)^m(x) / q(X) takes the value 1
// at the three points, and its fibre over 1 in D is {y : m(y) = 0, P_y = q(y)}. Reported: the distribution of the
// fibre size, split by the number of roots of q outside D (2: two poles outside D; the cases deg q < 2 or a root in D
// are counted apart), and for the fibres of at least 4 points with two poles outside D: how many functions have a
// period, the range of |deg num - deg den| for those without, and the check nu <= 2 deg + 1 for those without.
#include "02_gf.h"
static u64 pts[16];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
  u64 seed = argc > 1 ? strtoull(argv[1], 0, 0) : 1; const int n = 16;
  gf_init(64, 0x1b); rs = seed * 0x9E3779B97F4A7C15ull + 12345; for (int i = 0; i < 20; i++) rnd();
  u64 b[4]; for (int i = 0; i < 4; i++) b[i] = rnd();
  for (int x = 0; x < n; x++) { u64 v = 0; for (int i = 0; i < 4; i++) if (x >> i & 1) v ^= b[i]; pts[x] = v; }
  static u64 inv[16][16]; for (int y = 0; y < n; y++) for (int x = 0; x < n; x++) if (x != y) inv[y][x] = ginv(pts[y] ^ pts[x]);
  int fr[13], nf = 0; for (int x = 0; x < n; x++) if (x < 1 || x > 3) fr[nf++] = x;
  long total = 1; for (int i = 0; i < nf; i++) total *= 3;
  // hist[class][fibre size], class 0: deg q < 2, 1: a root of q in D, 2: both roots outside D
  long hist[3][17] = {{0}}; int imb_min[17], imb_max[17]; long per[17] = {0}, viol = 0; for (int i = 0; i < 17; i++) { imb_min[i] = 99; imb_max[i] = -1; }
  u64 y1 = pts[1], y2 = pts[2], y3 = pts[3];
  u64 d12 = ginv(y1 ^ y2), d13 = ginv(y1 ^ y3), d23 = ginv(y2 ^ y3);
  for (long code = 0; code < total; code++) {
    int m[16] = {0}; long c = code; int mp = 0, mn = 0;
    for (int i = 0; i < nf; i++) { int e = (int)(c % 3) - 1; c /= 3; m[fr[i]] = e; if (e > 0) mp++; if (e < 0) mn++; }
    u64 P[16];
    for (int y = 0; y < n; y++) { if (m[y]) continue; u64 v = 1; for (int x = 0; x < n; x++) { if (m[x] > 0) v = gmul(v, pts[y] ^ pts[x]); else if (m[x] < 0) v = gmul(v, inv[y][x]); } P[y] = v; }
    // Newton form of q through (y1,P1), (y2,P2), (y3,P3)
    u64 f12 = gmul(P[1] ^ P[2], d12), f23 = gmul(P[2] ^ P[3], d23), f123 = gmul(f12 ^ f23, d13);
    int fib = 0, rootD = 0;
    for (int y = 0; y < n; y++) {
      u64 q = P[1] ^ gmul(pts[y] ^ y1, f12 ^ gmul(pts[y] ^ y2, f123));
      if (!q) rootD = 1;
      if (!m[y] && q == P[y]) fib++;
    }
    int cls = !f123 ? 0 : rootD ? 1 : 2;
    hist[cls][fib]++;
    if (cls == 2 && fib >= 4) {
      int imb = mp - (mn + 2); if (imb < 0) imb = -imb;
      // xi has the period a iff m(x + a) = m(x) for all x and the two poles outside D differ by a, that is
      // q(X + a) = q(X): with q = f123 X^2 + (f12 + f123 (y1 + y2)) X + ..., iff f123 a = f12 + f123 (y1 + y2)
      int np = 0; for (int a = 1; a < n; a++) { int ok = 1; for (int x = 0; x < n; x++) if (m[x] != m[x ^ a]) { ok = 0; break; }
        if (ok && gmul(f123, pts[a]) == (f12 ^ gmul(f123, y1 ^ y2))) np++; }
      if (np) per[fib]++;
      else { if (imb < imb_min[fib]) imb_min[fib] = imb; if (imb > imb_max[fib]) imb_max[fib] = imb;
        int delta = mp > mn + 2 ? mp : mn + 2; if (mp + mn + fib > 2 * delta + 1) { viol++; printf("VIOLATION of P: code %ld\n", code); } }
    }
  }
  const char *nm[3] = {"deg q < 2", "a root of q in D", "both roots of q outside D"};
  for (int cl = 0; cl < 3; cl++) { printf("%s: fibre sizes", nm[cl]); for (int f = 0; f <= 16; f++) if (hist[cl][f]) printf(" %d:%ld", f, hist[cl][f]); printf("\n"); }
  for (int f = 4; f <= 16; f++) if (hist[2][f]) printf("  two poles outside D, fibre %d: %ld functions, %ld with a period; without period: |deg num - deg den| from %d to %d\n", f, hist[2][f], per[f], imb_min[f], imb_max[f]);
  printf("violations of P among the functions with two poles outside D and a fibre of at least 4 points: %ld\n", viol);
  return 0;
}
