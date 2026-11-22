// Researcher 27. Which F_2-linear relations between the special points of a four-member configuration are needed?
//
//   cc -O2 -o 27_generalize 27_generalize.c
//   ./27_generalize k T E0 E1 E2 E3 [seed] [tries]      (error sets as hex masks of the 16 points, from 27_lists)
//
// A list on a generic subspace is a configuration of labelled points x_j = l_j(b), l_j linear forms over F_2, for
// which the incidence system has a solution identically in b. Equivalently the F_2-rational linear space
// Lambda = {(l_j(b))_j} lies in the variety of solvable configurations. The program recomputes the list of the four
// error sets, reduces it to its curve Xi of degree delta, records the type (partition of the four members into equal
// values) of every special point, and then looks for a smallest space Rel' of F_2-relations between the points (a
// largest Lambda) for which a configuration of the same types, with points generic subject to Rel' only, still has a
// curve of degree <= delta without common factor and with four distinct members. It prints the relations kept.
#include "27_common.h"
#define MAXP 16
static int npt, ptype[MAXP][4]; // class id of each member at the point
static int delta;
static int label[MAXP];

static int kernel(u64 *A, int r, int c, u64 *Kb) {
  int piv[80], isp[80], rank = 0; memset(isp, 0, sizeof isp);
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

// does the configuration with points xs (field elements) have a solution of degree <= delta, primitive, nondegenerate?
static int solvable(const u64 *xs, int *kd_out) {
  static u64 A[64 * 64], Kb[64 * 64]; int c = 3 * (delta + 1), r = 0;
  for (int j = 0; j < npt; j++) {
    u64 pw[32]; pw[0] = 1; for (int i = 1; i <= delta; i++) pw[i] = mul(pw[i - 1], xs[j]);
    for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++) {
      if (ptype[j][a] != ptype[j][b]) continue;
      int first = 1; for (int a2 = 0; a2 < a; a2++) if (ptype[j][a2] == ptype[j][a]) first = 0;
      if (!first) continue; // rows: member a (first of its class) against each later member b of the class
      memset(A + r * c, 0, c * sizeof(u64));
      if (a > 0) for (int i = 0; i <= delta; i++) A[r * c + (a - 1) * (delta + 1) + i] ^= pw[i];
      for (int i = 0; i <= delta; i++) A[r * c + (b - 1) * (delta + 1) + i] ^= pw[i];
      r++;
    }
  }
  int kd = kernel(A, r, c, Kb); if (kd_out) *kd_out = kd;
  if (kd == 0) return 0;
  poly u[3];
  for (int a = 0; a < 3; a++) { u[a].d = delta; for (int i = 0; i <= delta; i++) { u64 s = 0; for (int q = 0; q < kd; q++) s ^= mul(Kb[q * c + a * (delta + 1) + i], q == 0 && kd == 1 ? 1 : (rnd() | 1)); u[a].c[i] = s; } pnorm(&u[a]); }
  if (u[0].d < 0 || u[1].d < 0 || u[2].d < 0) return 0;
  poly t, g, d; padd(&d, &u[0], &u[1]); if (d.d < 0) return 0; padd(&d, &u[0], &u[2]); if (d.d < 0) return 0; padd(&d, &u[1], &u[2]); if (d.d < 0) return 0;
  pgcd(&t, &u[0], &u[1]); pgcd(&g, &t, &u[2]);
  return g.d == 0;
}

// relations: bitmasks over the npt points. Realize the configuration whose relation space is spanned by rel[0..nr-1].
static void realize(const unsigned *rel, int nr, u64 *xs) {
  // quotient of F_2^npt by the span: reduce each unit vector modulo an echelon basis, then map the free coordinates
  unsigned ech[MAXP]; int lead[MAXP], ne = 0;
  for (int i = 0; i < nr; i++) { unsigned v = rel[i]; for (int j = 0; j < ne; j++) if (v >> lead[j] & 1) v ^= ech[j]; if (v) { lead[ne] = 31 - __builtin_clz(v); for (int j = 0; j < ne; j++) if (ech[j] >> lead[ne] & 1) ech[j] ^= v; ech[ne++] = v; } }
  u64 base[MAXP]; for (int j = 0; j < npt; j++) base[j] = rnd();
  for (int j = 0; j < npt; j++) {
    // point j is the unit vector e_j reduced: if j is a leading position, e_j = sum of the other terms of its row
    int row = -1; for (int q = 0; q < ne; q++) if (lead[q] == j) row = q;
    if (row < 0) xs[j] = base[j];
    else { u64 v = 0; unsigned m = ech[row] ^ (1u << j); for (int p = 0; p < npt; p++) if (m >> p & 1) v ^= base[p]; xs[j] = v; }
  }
}
static int spandim(const unsigned *rel, int nr) { unsigned ech[32]; int ne = 0; for (int i = 0; i < nr; i++) { unsigned v = rel[i]; for (int j = 0; j < ne; j++) { unsigned t = v ^ ech[j]; if (t < v) v = t; } if (v) ech[ne++] = v; } return ne; }

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 27_generalize k T E0 E1 E2 E3 [seed] [tries]\n"); return 1; }
  int K = atoi(argv[1]), T = atoi(argv[2]); unsigned E[4]; for (int i = 0; i < 4; i++) E[i] = strtoul(argv[3 + i], 0, 16);
  u64 seed = argc > 7 ? strtoull(argv[7], 0, 10) : 1; int tries = argc > 8 ? atoi(argv[8]) : 20;
  domain_init(4, seed, 0);
  int tt = 16 - T, M = 16 - K, mm = T - K;
  // syndrome: kernel of the 4m x M matrix of shifted locators
  static u64 A[64 * 64], Kb[64 * 64]; memset(A, 0, sizeof A);
  for (int i = 0; i < 4; i++) { u64 z[20]; z[0] = 1; int d = 0; for (int p = 0; p < 16; p++) if (E[i] >> p & 1) { z[d + 1] = 0; for (int j = d + 1; j >= 1; j--) z[j] = z[j - 1] ^ mul(z[j], pts[p]); z[0] = mul(z[0], pts[p]); d++; }
    for (int l = 0; l < mm; l++) for (int j = 0; j <= tt; j++) A[(i * mm + l) * M + l + j] = z[j]; }
  int kd = kernel(A, 4 * mm, M, Kb); if (kd == 0) { printf("no list on these error sets\n"); return 0; }
  u64 y[32]; for (int j = 0; j < M; j++) { y[j] = 0; for (int q = 0; q < kd; q++) y[j] ^= mul(Kb[q * M + j], kd == 1 ? 1 : (rnd() | 1)); }
  u64 ev[4][16]; memset(ev, 0, sizeof ev);
  for (int i = 0; i < 4; i++) { int ix[16], c = 0; for (int p = 0; p < 16; p++) if (E[i] >> p & 1) ix[c++] = p;
    static u64 B[32 * 32], Kt[32 * 32]; for (int j = 0; j < M; j++) { for (int a = 0; a < c; a++) B[j * (c + 1) + a] = j == 0 ? 1 : mul(B[(j - 1) * (c + 1) + a], pts[ix[a]]); B[j * (c + 1) + c] = y[j]; }
    if (kernel(B, M, c + 1, Kt) != 1 || !Kt[c]) { fprintf(stderr, "syndrome not in U_E\n"); return 1; }
    u64 iv = inv(Kt[c]); for (int a = 0; a < c; a++) ev[i][ix[a]] = mul(Kt[a], iv); }
  poly u[3];
  for (int i = 1; i < 4; i++) { static u64 B[32 * 32], Kt[32 * 32]; // interpolate e_0 - e_i by a polynomial of degree < K
    for (int p = 0; p < 16; p++) { for (int j = 0; j < K; j++) B[p * (K + 1) + j] = j == 0 ? 1 : mul(B[p * (K + 1) + j - 1], pts[p]); B[p * (K + 1) + K] = ev[0][p] ^ ev[i][p]; }
    if (kernel(B, 16, K + 1, Kt) != 1) { fprintf(stderr, "interpolation failed\n"); return 1; }
    u64 iv = inv(Kt[K]); u[i - 1].d = K - 1; for (int j = 0; j < K; j++) u[i - 1].c[j] = mul(Kt[j], iv); pnorm(&u[i - 1]); }
  info4 o; analyse4(u, &o); if (o.degenerate) { printf("degenerate\n"); return 0; }
  char key[400]; key4(&o, key); printf("%s\n", key);
  delta = o.delta; npt = 0; u64 xs0[MAXP];
  poly G, t; pgcd(&t, &u[0], &u[1]); pgcd(&G, &t, &u[2]);
  for (int x = 0; x < 16; x++) { if (!peval(&G, pts[x])) continue; u64 val[4]; for (int i = 0; i < 4; i++) val[i] = i ? peval(&o.v[i], pts[x]) : 0;
    int cls[4], nc = 0; for (int i = 0; i < 4; i++) { cls[i] = -1; for (int j = 0; j < i; j++) if (val[j] == val[i]) { cls[i] = cls[j]; break; } if (cls[i] < 0) cls[i] = nc++; }
    if (nc == 4) continue;
    for (int i = 0; i < 4; i++) ptype[npt][i] = cls[i]; label[npt] = x; xs0[npt] = pts[x]; npt++; }
  printf("special points (label: classes of members 0123):"); for (int j = 0; j < npt; j++) printf(" %x:%d%d%d%d", label[j], ptype[j][0], ptype[j][1], ptype[j][2], ptype[j][3]); printf("\n");
  if (!solvable(xs0, &kd)) { printf("original configuration not reproduced (kd=%d)\n", kd); return 1; }
  // relation space of the affine points (1, x_j)
  unsigned rel[1 << 12]; int nr = 0;
  { unsigned vec[MAXP], comb[MAXP]; int nb = 0; unsigned bv[MAXP], bc[MAXP];
    for (int j = 0; j < npt; j++) { vec[j] = (label[j] << 1) | 1; comb[j] = 1u << j; unsigned v = vec[j], c = comb[j];
      for (int q = 0; q < nb; q++) { if ((v ^ bv[q]) < v) { v ^= bv[q]; c ^= bc[q]; } }
      if (v) { bv[nb] = v; bc[nb] = c; nb++; } else rel[nr++] = c; } }
  printf("points %d, relations %d (dimension of the relation space)\n", npt, nr);
  int best = nr; unsigned bestrel[32]; memcpy(bestrel, rel, nr * sizeof(unsigned));
  for (int tr = 0; tr < tries; tr++) {
    unsigned cur[32]; int nc = nr; memcpy(cur, rel, nr * sizeof(unsigned));
    for (;;) { // try to drop to a hyperplane of the current relation space
      int found = 0; int nh = (1 << nc) - 1; int start = rnd() % nh;
      for (int hh = 0; hh < nh && !found; hh++) { unsigned h = 1 + (start + hh) % nh; // functional h on the coordinates of cur
        unsigned sub[32]; int ns = 0; int pivot = __builtin_ctz(h);
        for (int i = 0; i < nc; i++) { if (i == pivot) continue; sub[ns++] = (h >> i & 1) ? cur[i] ^ cur[pivot] : cur[i]; }
        u64 xs[MAXP]; int ok = 1;
        for (int rep = 0; rep < 2 && ok; rep++) { realize(sub, ns, xs); int dis = 1; for (int a = 0; a < npt; a++) for (int b = a + 1; b < npt; b++) if (xs[a] == xs[b]) dis = 0; if (!dis || !solvable(xs, NULL)) ok = 0; }
        if (ok) { memcpy(cur, sub, ns * sizeof(unsigned)); nc = ns; found = 1; }
      }
      if (!found || nc == 0) break;
    }
    if (nc < best || tr == 0) { best = nc; memcpy(bestrel, cur, nc * sizeof(unsigned)); }
    printf("try %d: minimal relation space of dimension %d:", tr, nc);
    for (int i = 0; i < nc; i++) { printf(" {"); for (int j = 0; j < npt; j++) if (cur[i] >> j & 1) printf("%x", label[j]); printf("}"); } printf("\n");
  }
  (void)spandim;
  return 0;
}
