// Referee 46: the family CLAIMED by note 39 Proposition 4.1 for w = X^(n/2) L_W, |W| = n/8, degree <= n/2,
// agreement >= 19n/32, generated from its combinatorial description only, each member then verified by direct
// evaluation in GF(2^64): the coefficients of Z^1 .. Z^(n/8-1) of Psi_mu = prod (1 + xZ)^mu(x) must be those of
// rev(L_W), which says deg(w - Z_mu) <= n/2.
//
// Coordinates: point i of D is the F_2-combination of the basis selected by the bits of i, W = {i < n/8},
// functionals are N-bit masks (parity of the AND).
//  (a1) unions of five cosets of W;
//  (a2) half of a coset H' of a hyperplane H > W cut by a functional psi not in W-perp, plus three of the four
//       cosets of W on the other side;
//  (b)  mu = 1_H' - 1_A + 1_C + 1_A', V = ker(h, psi1, psi2) with V + W = H, A in H' and A' off H' cosets of V,
//       C off H' a coset of W.
// cc -O2 -o 46_family 46_family.c ; ./46_family N seed [dump file]   (dump for N <= 6: "support double" in hex)
#include "46_gf.h"
typedef unsigned __int128 u128;
static int N, n, mp;
static u64 pts[128], basis[8], tser[40];
typedef struct { u128 supp, dbl; int type; } mem;
static mem *all; static size_t cnt, cap;
static long bad = 0;
static int par(unsigned v) { return __builtin_popcount(v) & 1; }

static void add(const int *mult, int type) {
  u64 P[40]; memset(P, 0, sizeof P); P[0] = 1;
  mem m; m.supp = 0; m.dbl = 0; m.type = type;
  for (int i = 0; i < n; i++) {
    if (mult[i] < 0 || mult[i] > 2) { fprintf(stderr, "multiplicity out of range\n"); exit(1); }
    for (int e = 0; e < mult[i]; e++) for (int j = mp - 1; j >= 1; j--) P[j] ^= gmul(pts[i], P[j - 1]);
    if (mult[i]) m.supp |= (u128)1 << i;
    if (mult[i] == 2) m.dbl |= (u128)1 << i;
  }
  for (int j = 1; j < mp; j++) if (P[j] != tser[j]) { bad++; break; }
  if (cnt == cap) { cap = cap ? 2 * cap : 4096; all = realloc(all, cap * sizeof(mem)); }
  all[cnt++] = m;
}
static int cmpm(const void *a, const void *b) {
  const mem *x = a, *y = b;
  if (x->supp != y->supp) return x->supp < y->supp ? -1 : 1;
  if (x->dbl != y->dbl) return x->dbl < y->dbl ? -1 : 1;
  return 0;
}
static u128 shiftmask(u128 m, int a) { u128 r = 0; for (int i = 0; i < n; i++) if ((m >> i) & 1) r |= (u128)1 << (i ^ a); return r; }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: 46_family N seed [dump file]\n"); return 1; }
  N = atoi(argv[1]); n = 1 << N; u64 seed = strtoull(argv[2], 0, 10);
  if (N < 5 || N > 7) { fprintf(stderr, "N in 5..7\n"); return 1; }
  make_domain(N, seed, basis, pts);
  mp = n / 8; int wn = n / 8, sh = N - 3;
  memset(tser, 0, sizeof tser); tser[0] = 1;
  for (int i = 0; i < wn; i++) for (int j = mp - 1; j >= 1; j--) tser[j] ^= gmul(pts[i], tser[j - 1]);
  int mult[128];
  // (a1)
  for (int cs = 0; cs < 256; cs++) if (__builtin_popcount(cs) == 5) {
    for (int i = 0; i < n; i++) mult[i] = (cs >> (i >> sh)) & 1;
    add(mult, 0);
  }
  size_t c_a1 = cnt;
  // (a2)
  for (int hc = 1; hc < 8; hc++) for (int s = 0; s < 2; s++) {
    unsigned h = (unsigned)hc << sh;
    for (unsigned psi = 0; psi < (unsigned)n; psi++) {
      if ((psi & (wn - 1)) == 0) continue; // psi in W-perp
      if ((psi ^ h) < psi) continue;       // psi and psi + h cut H' the same way
      for (int c = 0; c < 2; c++) for (int y0 = 0; y0 < 8; y0++) {
        if (par(((unsigned)y0 << sh) & h) == s) continue; // the empty coset is off H'
        for (int i = 0; i < n; i++) {
          if (par(i & h) == s) mult[i] = (par(i & psi) == c);
          else mult[i] = ((i >> sh) != y0);
        }
        add(mult, 1);
      }
    }
  }
  size_t c_a2 = cnt - c_a1;
  // (b)
  long nV = 0;
  for (int hc = 1; hc < 8; hc++) {
    unsigned h = (unsigned)hc << sh;
    for (unsigned p1 = 1; p1 < (unsigned)n; p1++) for (unsigned p2 = p1 + 1; p2 < (unsigned)n; p2++) {
      // span(h, p1, p2) must be 3-dimensional and meet W-perp in {0, h} only
      unsigned el[8]; int ok = 1;
      for (int c = 0; c < 8; c++) el[c] = ((c & 1) ? h : 0) ^ ((c & 2) ? p1 : 0) ^ ((c & 4) ? p2 : 0);
      for (int c = 1; c < 8 && ok; c++) {
        if (el[c] == 0) ok = 0;
        if ((el[c] & (wn - 1)) == 0 && el[c] != h) ok = 0;
      }
      if (!ok) continue;
      // canonical generators: p1 the least element outside {0, h}, p2 the least outside {0, h, p1, p1 + h}
      unsigned m1 = ~0u, m2 = ~0u;
      for (int c = 2; c < 8; c++) if (el[c] < m1) m1 = el[c];
      for (int c = 2; c < 8; c++) if (el[c] != m1 && el[c] != (m1 ^ h) && el[c] < m2) m2 = el[c];
      if (m1 != p1 || m2 != p2) continue;
      nV++;
      for (int s = 0; s < 2; s++)
        for (int ca = 0; ca < 4; ca++) for (int cb = 0; cb < 4; cb++) for (int y0 = 0; y0 < 8; y0++) {
          if (par(((unsigned)y0 << sh) & h) == s) continue; // C is off H'
          for (int i = 0; i < n; i++) {
            int code = par(i & p1) | (par(i & p2) << 1);
            if (par(i & h) == s) mult[i] = (code != ca);                       // H' minus A
            else mult[i] = ((i >> sh) == y0) + (code == cb);                    // C plus A'
          }
          add(mult, 2);
        }
    }
  }
  size_t c_b = cnt - c_a1 - c_a2;
  printf("N=%d seed=%llu: (a1) %zu, (a2) %zu, (b) %zu [subspaces V per hyperplane: %ld], total %zu\n", N, (unsigned long long)seed, c_a1, c_a2, c_b, nV / 7, cnt);
  long gb = 1; { long num = 1, den = 1; for (int i = 0; i < 2; i++) { num *= (1L << (N - 3 - i)) - 1; den *= (1L << (i + 1)) - 1; } gb = num / den; }
  printf("formula: 56n - 392 = %d, 14336 * binom(N-3,2)_2 = %ld, total %ld\n", 56 * n - 392, 14336 * gb, 56 * n - 392 + 14336 * gb);
  printf("members failing the evaluation in GF(2^64): %ld\n", bad);
  qsort(all, cnt, sizeof(mem), cmpm);
  size_t dup = 0; for (size_t i = 1; i < cnt; i++) if (!cmpm(&all[i - 1], &all[i])) dup++;
  printf("duplicates: %zu\n", dup);
  // profile: (support, largest multiplicity, order of the period group of mu, order of the stabilizer of the support)
  long prof[129][3][5][5]; memset(prof, 0, sizeof prof);
  int lg[129]; for (int i = 0; i <= 128; i++) lg[i] = -1; for (int i = 0; i <= 7; i++) lg[1 << i] = i;
  long minper = n;
  for (size_t i = 0; i < cnt; i++) {
    int s = 0; for (int j = 0; j < n; j++) s += (int)((all[i].supp >> j) & 1);
    int per = 0, st = 0;
    for (int a = 0; a < n; a++) {
      u128 sa = shiftmask(all[i].supp, a);
      if (sa == all[i].supp) { st++; if (shiftmask(all[i].dbl, a) == all[i].dbl) per++; }
    }
    if (per < minper) minper = per;
    int lp = lg[per], ls = lg[st];
    if (lp > 4 || ls > 4 || lp < 0 || ls < 0) { fprintf(stderr, "unexpected period order %d %d\n", per, st); exit(1); }
    prof[s][all[i].dbl ? 2 : 1][lp][ls]++;
  }
  for (int s = 0; s <= n; s++) for (int m = 1; m <= 2; m++) for (int lp = 0; lp < 5; lp++) for (int ls = 0; ls < 5; ls++) if (prof[s][m][lp][ls])
    printf("  (support %d, largest multiplicity %d, period group of mu %d, stabilizer of the support %d) : %ld\n", s, m, 1 << lp, 1 << ls, prof[s][m][lp][ls]);
  printf("smallest period group: %ld (n/32 = %d)\n", minper, n / 32);
  if (argc >= 5 && !strcmp(argv[3], "dump") && N <= 6) {
    FILE *f = fopen(argv[4], "w");
    for (size_t i = 0; i < cnt; i++) fprintf(f, "%016llx %016llx 0\n", (unsigned long long)all[i].supp, (unsigned long long)all[i].dbl);
    fclose(f);
  }
  return 0;
}
