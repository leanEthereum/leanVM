// Researcher 27. Lift a four-member list from a 16-point domain to n = 16 |U| points through L_U and verify it.
//
//   cc -O2 -o 27_lift 27_lift.c
//   ./27_lift k0 T0 E0 E1 E2 E3 [logu] [seed]      (error sets on 16 points as hex masks; |U| = 2^logu, default 2)
//
// D is a random subspace of dimension 4 + logu, U the span of the last logu basis vectors, D_0 = L_U(D) (16 points).
// The list of the four error sets is computed on D_0, its differences u_i^0 are composed with L_U, and the common
// factor is cut down so that the degree is < n/2 (roots of the common factor are kept inside D as far as possible).
// Output: the degree bound k, and the agreements of the four members with the word that takes at each point a value
// shared by the most members. This is a direct check of the "if" direction (lifting) and of the count
// sum |S_i| = n + J + 3 gamma_D.
#include "27_common.h"
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
#define BIGN 256
typedef struct { int d; u64 c[BIGN + 2]; } bpoly;
static u64 bev(const bpoly *a, u64 x) { u64 v = 0; for (int i = a->d; i >= 0; i--) v = mul(v, x) ^ a->c[i]; return v; }
int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 27_lift k0 T0 E0 E1 E2 E3 [logu] [seed]\n"); return 1; }
  int K = atoi(argv[1]), T = atoi(argv[2]); unsigned E[4]; for (int i = 0; i < 4; i++) E[i] = strtoul(argv[3 + i], 0, 16);
  int logu = argc > 7 ? atoi(argv[7]) : 1; u64 seed = argc > 8 ? strtoull(argv[8], 0, 10) : 1;
  int N = 4 + logu, nb = 1 << N, u = 1 << logu;
  rs = seed * 0x9e3779b97f4a7c15ull + 12345; for (int i = 0; i < 20; i++) rnd();
  u64 b[8], big[BIGN]; for (int i = 0; i < N; i++) b[i] = rnd();
  for (int x = 0; x < nb; x++) { u64 v = 0; for (int i = 0; i < N; i++) if (x >> i & 1) v ^= b[i]; big[x] = v; }
  // L_U as a polynomial, U = span of b[4..N-1] = points x with low four bits zero
  bpoly LU; LU.d = 0; LU.c[0] = 1;
  for (int x = 0; x < nb; x += 16) { LU.c[LU.d + 1] = 0; for (int j = LU.d + 1; j >= 1; j--) LU.c[j] = LU.c[j - 1] ^ mul(LU.c[j], big[x]); LU.c[0] = mul(LU.c[0], big[x]); LU.d++; }
  NN = 4; n = 16; for (int x = 0; x < 16; x++) pts[x] = bev(&LU, big[x]);
  int tt = 16 - T, M = 16 - K, mm = T - K; (void)tt;
  static u64 A[64 * 64], Kb[64 * 64]; memset(A, 0, sizeof A);
  for (int i = 0; i < 4; i++) { u64 z[20]; z[0] = 1; int d = 0; for (int p = 0; p < 16; p++) if (E[i] >> p & 1) { z[d + 1] = 0; for (int j = d + 1; j >= 1; j--) z[j] = z[j - 1] ^ mul(z[j], pts[p]); z[0] = mul(z[0], pts[p]); d++; }
    for (int l = 0; l < mm; l++) for (int j = 0; j <= d; j++) A[(i * mm + l) * M + l + j] = z[j]; }
  int kd = kernel(A, 4 * mm, M, Kb); if (kd == 0) { printf("no list on these error sets\n"); return 0; }
  u64 y[32]; for (int j = 0; j < M; j++) { y[j] = 0; for (int q = 0; q < kd; q++) y[j] ^= mul(Kb[q * M + j], kd == 1 ? 1 : (rnd() | 1)); }
  u64 ev[4][16]; memset(ev, 0, sizeof ev);
  for (int i = 0; i < 4; i++) { int ix[16], c = 0; for (int p = 0; p < 16; p++) if (E[i] >> p & 1) ix[c++] = p;
    static u64 B[32 * 32], Kt[32 * 32]; for (int j = 0; j < M; j++) { for (int a = 0; a < c; a++) B[j * (c + 1) + a] = j == 0 ? 1 : mul(B[(j - 1) * (c + 1) + a], pts[ix[a]]); B[j * (c + 1) + c] = y[j]; }
    if (kernel(B, M, c + 1, Kt) != 1 || !Kt[c]) { fprintf(stderr, "syndrome not in U_E\n"); return 1; }
    u64 iv = inv(Kt[c]); for (int a = 0; a < c; a++) ev[i][ix[a]] = mul(Kt[a], iv); }
  poly u0[3];
  for (int i = 1; i < 4; i++) { static u64 B[32 * 32], Kt[32 * 32];
    for (int p = 0; p < 16; p++) { for (int j = 0; j < K; j++) B[p * (K + 1) + j] = j == 0 ? 1 : mul(B[p * (K + 1) + j - 1], pts[p]); B[p * (K + 1) + K] = ev[0][p] ^ ev[i][p]; }
    if (kernel(B, 16, K + 1, Kt) != 1) { fprintf(stderr, "interpolation failed\n"); return 1; }
    u64 iv = inv(Kt[K]); u0[i - 1].d = K - 1; for (int j = 0; j < K; j++) u0[i - 1].c[j] = mul(Kt[j], iv); pnorm(&u0[i - 1]); }
  info4 o; analyse4(u0, &o); if (o.degenerate) { printf("degenerate\n"); return 0; }
  char key[400]; key4(&o, key); printf("on 16 points: %s\n", key);
  int J0 = o.npair + 2 * o.ntrip + o.ndbl;
  // lifted curve: v_i(L_U(X)); values at the points of D
  u64 val[BIGN][4]; int special = 0, J = 0, freept[BIGN], nfree = 0;
  for (int x = 0; x < nb; x++) { u64 yv = bev(&LU, big[x]); val[x][0] = 0; for (int i = 1; i < 4; i++) val[x][i] = peval(&o.v[i], yv);
    int best = 1; for (int i = 0; i < 4; i++) { int c = 0; for (int j = 0; j < 4; j++) c += val[x][i] == val[x][j]; if (c > best) best = c; }
    if (best > 1) { special++; J += best - 1; } else freept[nfree++] = x; }
  int delta = o.delta * u, kk = nb / 2, gam = kk - 1 - delta; // common factor of degree gam with roots at free points
  if (gam < 0) { printf("lifted degree %d exceeds n/2 - 1\n", delta); return 0; }
  int gD = gam < nfree ? gam : nfree;
  printf("n=%d |U|=%d: delta=%d J=%d (16-point J=%d, excess %d), special points %d, free %d, common factor of degree %d with %d roots in D\n", nb, u, delta, J, J0, J0 - 3 * o.delta - 2, special, nfree, gam, gD);
  // agreements: at a root of G all four agree; elsewhere the members of a largest class agree with the word
  int ag[4] = {0, 0, 0, 0}; char isroot[BIGN]; memset(isroot, 0, sizeof isroot); for (int i = 0; i < gD; i++) isroot[freept[i]] = 1;
  for (int x = 0; x < nb; x++) {
    if (isroot[x]) { for (int i = 0; i < 4; i++) ag[i]++; continue; }
    int best = 0, bi = 0; for (int i = 0; i < 4; i++) { int c = 0; for (int j = 0; j < 4; j++) c += val[x][i] == val[x][j]; if (c > best || (c == best && ag[i] < ag[bi])) { best = c; bi = i; } }
    for (int j = 0; j < 4; j++) if (val[x][j] == val[x][bi]) ag[j]++;
  }
  int mn = ag[0]; for (int i = 1; i < 4; i++) if (ag[i] < mn) mn = ag[i];
  printf("degree < k = %d, agreements %d %d %d %d (sum %d = n + J + 3 gamma_D = %d), min %d, T/n = %.4f, generic four-member bound T <= %d\n", kk, ag[0], ag[1], ag[2], ag[3], ag[0] + ag[1] + ag[2] + ag[3], nb + J + 3 * gD, mn, (double)mn / nb, (nb - kk - 1) / 4 + kk);
  return 0;
}
