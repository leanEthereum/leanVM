// Researcher 27. Four-member curves of degree 2 (conics) on a 32-point generic subspace with more incidences than
// the count for independent points (J >= 3 delta + 3 = 9).
//
//   cc -O2 -o 27_conics 27_conics.c
//   ./27_conics [seed] [part parts] [Jmin]
//
// A conic Xi = (v_1 : v_2 : v_3), deg v_i <= 2, is fixed by 8 pair incidences in general. The program takes the six
// affinely independent points 0, b1, .., b5 with every labelling by the six pair types (the first label is 01, by the
// symmetry of the four members; at most two points per type), two more points with labels, solves for the conic when
// it is unique, and counts its incidences with all 32 points. Every conic with J >= Jmin (default 10) is analysed
// (27_common.h). So every conic that has at least 8 pair points, six of them affinely independent and eight of them
// determining it, is found. Conics whose special points span less than the whole space are those of 27_lists (n = 16).
#include "27_common.h"
static const int PA[6] = {0, 0, 0, 1, 1, 2}, PB[6] = {1, 2, 3, 2, 3, 3};
static long nconf = 0, nuniq = 0, nmulti = 0, nbig = 0, viol = 0;
static u64 pw2[32];

// rank-8 test and kernel of an 8 x 9 system by fraction-free elimination; returns kernel dimension, ker gets one vector
static int solve(u64 A[8][9], u64 *ker) {
  int piv[8], r = 0, isp[9] = {0};
  for (int c = 0; c < 9 && r < 8; c++) {
    int p = r; while (p < 8 && !A[p][c]) p++;
    if (p == 8) continue;
    if (p != r) for (int j = 0; j < 9; j++) { u64 t = A[p][j]; A[p][j] = A[r][j]; A[r][j] = t; }
    u64 pv = A[r][c];
    for (int i = 0; i < 8; i++) if (i != r && A[i][c]) { u64 f = A[i][c]; for (int j = 0; j < 9; j++) A[i][j] = mul(A[i][j], pv) ^ mul(A[r][j], f); }
    piv[r] = c; isp[c] = 1; r++;
  }
  if (r < 8) return 9 - r;
  int fc = 0; while (isp[fc]) fc++;
  // x_fc = 1; x_piv[i] = A[i][fc] / A[i][piv[i]]; clear denominators
  u64 den = 1; for (int i = 0; i < 8; i++) den = mul(den, A[i][piv[i]]);
  ker[fc] = den;
  for (int i = 0; i < 8; i++) { u64 t = A[i][fc]; for (int j = 0; j < 8; j++) if (j != i) t = mul(t, A[j][piv[j]]); ker[piv[i]] = t; }
  return 1;
}

int main(int argc, char **argv) {
  u64 seed = argc > 1 ? strtoull(argv[1], 0, 10) : 1; int part = argc > 3 ? atoi(argv[2]) : 0, parts = argc > 3 ? atoi(argv[3]) : 1, Jmin = argc > 4 ? atoi(argv[4]) : 10;
  domain_init(5, seed, 0);
  for (int x = 0; x < 32; x++) pw2[x] = mul(pts[x], pts[x]);
  static const int base[6] = {0, 1, 2, 4, 8, 16};
  int other[26], no = 0; for (int x = 0; x < 32; x++) { int isb = 0; for (int i = 0; i < 6; i++) if (base[i] == x) isb = 1; if (!isb) other[no++] = x; }
  int lab[8];
  for (long code = 0; code < 7776; code++) { // labels of base points 1..5 (base point 0 has label 0 = pair 01)
    if (code % parts != part) continue;
    lab[0] = 0; long c = code; int cnt[6] = {1, 0, 0, 0, 0, 0}, ok = 1;
    for (int i = 1; i < 6; i++) { lab[i] = c % 6; c /= 6; if (++cnt[lab[i]] > 2) ok = 0; }
    if (!ok) continue;
    for (int a = 0; a < no; a++) for (int b = a + 1; b < no; b++) for (int la = 0; la < 6; la++) for (int lb = 0; lb < 6; lb++) {
      if (cnt[la] + 1 + (lb == la) > 2 || cnt[lb] + 1 > 2) continue;
      lab[6] = la; lab[7] = lb; int px[8]; for (int i = 0; i < 6; i++) px[i] = base[i]; px[6] = other[a]; px[7] = other[b];
      u64 A[8][9]; memset(A, 0, sizeof A);
      for (int i = 0; i < 8; i++) { int ma = PA[lab[i]], mb = PB[lab[i]]; u64 x = pts[px[i]], x2 = pw2[px[i]];
        if (ma > 0) { A[i][(ma - 1) * 3] ^= 1; A[i][(ma - 1) * 3 + 1] ^= x; A[i][(ma - 1) * 3 + 2] ^= x2; }
        A[i][(mb - 1) * 3] ^= 1; A[i][(mb - 1) * 3 + 1] ^= x; A[i][(mb - 1) * 3 + 2] ^= x2; }
      nconf++;
      u64 ker[9]; int kd = solve(A, ker);
      if (kd != 1) { nmulti++; continue; }
      nuniq++;
      int J = 0;
      for (int x = 0; x < 32; x++) { u64 v[4]; v[0] = 0; for (int m = 0; m < 3; m++) v[m + 1] = ker[m * 3] ^ mul(ker[m * 3 + 1], pts[x]) ^ mul(ker[m * 3 + 2], pw2[x]);
        int eq = (v[0] == v[1]) + (v[0] == v[2]) + (v[0] == v[3]) + (v[1] == v[2]) + (v[1] == v[3]) + (v[2] == v[3]);
        J += eq == 1 ? 1 : eq == 2 ? 1 : eq == 3 ? 2 : eq == 6 ? 3 : 0; }
      if (J < Jmin) continue;
      poly u[3]; for (int m = 0; m < 3; m++) { u[m].d = 2; for (int j = 0; j < 3; j++) u[m].c[j] = ker[m * 3 + j]; pnorm(&u[m]); }
      info4 o; analyse4(u, &o); if (o.degenerate) continue;
      nbig++;
      int Jc = o.npair + 2 * o.ntrip + o.ndbl, excJ = Jc - 3 * o.delta - 2, mx = 0;
      for (int q = 0; q < 5; q++) if (o.f[q].npi > mx) mx = o.f[q].npi;
      for (int q = 0; q < 3; q++) if (o.z[q].npi > mx) mx = o.z[q].npi;
      char key[400]; int p = sprintf(key, "J=%d excJ=%d maxPi=%d Q:%s | ", Jc, excJ, mx, excJ <= mx + 3 * o.npiXi - 2 ? "ok" : "VIOLATED"); key4(&o, key + p);
      if (excJ > mx + 3 * o.npiXi - 2) viol++;
      hadd(key, 1);
    }
  }
  printf("n=32 conics: configurations %ld, unique conic %ld, larger solution space %ld, with J >= %d: %ld, violations of Conjecture Q: %ld\n", nconf, nuniq, nmulti, Jmin, nbig, viol);
  hprint();
  return 0;
}
