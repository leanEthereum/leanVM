// 81_k2_exact.c: exact K_2 = q^{-2k} sum_{rank M = 2} prod_x q^{2 - rank[delta_x, delta_pi(x)]}
// at (k, n) = (4, 8) for the plain T2 tree code over GF(2^m), m in {4, 6, 8}, d = 1 partner map pi.
// Enumerates Gr(2, 4)(F_q) by reduced echelon forms. Output: histogram N[n1][n0] of subspaces by
// (number of windows of rank 1, number of windows of rank 0), and K_2.
// usage: k2 <m> <twiddle seed> <map type c|u|s|x> <map seed> [quiet]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static int m, q; static uint8_t *MUL; // MUL[a*q+b]
static uint64_t rs;
static uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void field(int mm){ static const int poly[9] = {0,0,0,0,0x13,0,0x43,0,0x11d}; m = mm; q = 1 << m;
  int *ex = malloc(2*q*sizeof(int)), *lg = malloc(q*sizeof(int)); int x = 1;
  for (int i = 0; i < q-1; i++){ ex[i] = x; lg[x] = i; x <<= 1; if (x & q) x ^= poly[m]; }
  for (int i = q-1; i < 2*q; i++) ex[i] = ex[i-(q-1)];
  MUL = malloc((size_t)q*q);
  for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) MUL[a*q+b] = (a && b) ? ex[lg[a]+lg[b]] : 0; }
#define mul(a,b) MUL[(a)*q+(b)]
enum { V = 2, K = 4, N = 8 };
static uint8_t G[K][N]; // G[e][y] = prod_i x_i(y)^{e_i}
static int pi[N];
static int rank4(uint8_t A[4][4]){ // rank over GF(q) of 4x4, destructive
  int r = 0; for (int c = 0; c < 4 && r < 4; c++){ int p = -1; for (int i = r; i < 4; i++) if (A[i][c]) { p = i; break; }
    if (p < 0) continue; for (int j = 0; j < 4; j++){ uint8_t t = A[r][j]; A[r][j] = A[p][j]; A[p][j] = t; }
    // inverse of pivot
    uint8_t inv = 1; for (int z = 1; z < q; z++) if (mul(A[r][c], z) == 1) { inv = z; break; }
    for (int i = 0; i < 4; i++) if (i != r && A[i][c]){ uint8_t f = mul(A[i][c], inv); for (int j = 0; j < 4; j++) A[i][j] ^= mul(f, A[r][j]); }
    r++; } return r; }
int main(int argc, char **argv){
  if (argc < 5){ fprintf(stderr, "usage: k2 m twseed maptype mapseed\n"); return 1; }
  field(atoi(argv[1])); uint64_t tws = strtoull(argv[2],0,10); char mt = argv[3][0]; uint64_t ms = strtoull(argv[4],0,10);
  int quiet = argc > 5;
  // twiddles: node at level j has prefix p of j+1 bits; tw[j][p][b]
  rs = 0x9E3779B97F4A7C15ULL ^ (tws * 0xD1B54A32D192ED03ULL); for (int i = 0; i < 20; i++) rnd();
  uint8_t tw[V][N][2];
  for (int j = 0; j < V; j++) for (int p = 0; p < (2 << j); p++){ int a = rnd() % q, b; do b = rnd() % q; while (b == a); tw[j][p][0] = a; tw[j][p][1] = b; }
  for (int y = 0; y < N; y++){ // bits of y: tree, then j_{v-1}..j_0; layer i = v-1 is the top variable (level 0 node)
    uint8_t x[V]; for (int lev = 0; lev < V; lev++){ int p = y >> (V - lev); int b = (y >> (V - lev - 1)) & 1; x[V-1-lev] = tw[lev][p][b]; }
    for (int e = 0; e < K; e++){ uint8_t g = 1; for (int i = 0; i < V; i++) if ((e >> i) & 1) g = mul(g, x[i]); G[e][y] = g; } }
  // MDS check
  int nonmds = 0; for (int s = 0; s < 256; s++) if (__builtin_popcount(s) == 4){ uint8_t A[4][4]; int c = 0; for (int y = 0; y < N; y++) if ((s >> y) & 1){ for (int e = 0; e < 4; e++) A[e][c] = G[e][y]; c++; } if (rank4(A) < 4) nonmds++; }
  // map
  rs = 0xA24BAED4963EE407ULL ^ (ms * 0x9FB21C651E98DF25ULL); for (int i = 0; i < 20; i++) rnd();
  if (mt == 's') for (int y = 0; y < N; y++) pi[y] = y ^ 1;
  else if (mt == 'x') for (int y = 0; y < N; y++) pi[y] = y ^ K;
  else if (mt == 'u'){ int o[N]; for (int i = 0; i < N; i++) o[i] = i; for (int i = N-1; i > 0; i--){ int j = rnd() % (i+1); int t = o[i]; o[i] = o[j]; o[j] = t; } for (int i = 0; i < N; i++) pi[o[i]] = o[(i+1)%N]; }
  else { int a[K], b[K]; for (int i = 0; i < K; i++){ a[i] = i; b[i] = K + i; }
    for (int i = K-1; i > 0; i--){ int j = rnd() % (i+1); int t = a[i]; a[i] = a[j]; a[j] = t; j = rnd() % (i+1); t = b[i]; b[i] = b[j]; b[j] = t; }
    for (int i = 0; i < K; i++){ pi[a[i]] = b[i]; pi[b[i]] = a[(i+1)%K]; } }
  static uint64_t H[N+1][N+1]; memset(H, 0, sizeof H);
  // echelon forms: pivots i<j; row1 has 1 at i, 0 at j, free at columns >i other than j; row2 has 1 at j, free at columns > j
  for (int i = 0; i < K; i++) for (int j = i+1; j < K; j++){
    int f1[K], n1f = 0, f2[K], n2f = 0; for (int c = i+1; c < K; c++) if (c != j) f1[n1f++] = c; for (int c = j+1; c < K; c++) f2[n2f++] = c;
    long c1max = 1; for (int t = 0; t < n1f; t++) c1max *= q; long c2max = 1; for (int t = 0; t < n2f; t++) c2max *= q;
    for (long c1 = 0; c1 < c1max; c1++){ uint8_t d1[N]; memcpy(d1, G[i], N); long z = c1; for (int t = 0; t < n1f; t++){ int a = z % q; z /= q; if (a) for (int y = 0; y < N; y++) d1[y] ^= mul(a, G[f1[t]][y]); }
      for (long c2 = 0; c2 < c2max; c2++){ uint8_t d2[N]; memcpy(d2, G[j], N); long z2 = c2; for (int t = 0; t < n2f; t++){ int a = z2 % q; z2 /= q; if (a) for (int y = 0; y < N; y++) d2[y] ^= mul(a, G[f2[t]][y]); }
        int r1 = 0, r0 = 0; for (int x = 0; x < N; x++){ int y = pi[x]; if (mul(d1[x], d2[y]) != mul(d1[y], d2[x])) continue; if ((d1[x] | d2[x] | d1[y] | d2[y]) == 0) r0++; else r1++; }
        H[r1][r0]++; } } }
  double gl2 = ((double)q*q - 1) * ((double)q*q - q), K2 = 0; double lq = log2((double)q);
  double Sw[2*N+1]; for (int w = 0; w <= 2*N; w++) Sw[w] = 0;
  for (int a = 0; a <= N; a++) for (int b = 0; b <= N; b++) if (H[a][b]){ double t = gl2 * (double)H[a][b] * pow(q, a + 2*b - 2*K); K2 += t; Sw[a+2*b] += t;
    if (!quiet) printf("  n1=%d n0=%d count=%llu log_q(count)=%.3f term=%.4g\n", a, b, (unsigned long long)H[a][b], log2((double)H[a][b])/lq, t); }
  printf("m=%d tw=%llu map=%c%llu pi=", m, (unsigned long long)tws, mt, (unsigned long long)ms); for (int y = 0; y < N; y++) printf("%d", pi[y]);
  printf(" nonMDSsets=%d K2=%.6g log2K2/n=%.4f  by w:", nonmds, K2, log2(K2)/N); for (int w = 0; w <= 2*N; w++) if (Sw[w] > 0) printf(" %d:%.4g", w, Sw[w]); printf("\n");
  return 0; }
