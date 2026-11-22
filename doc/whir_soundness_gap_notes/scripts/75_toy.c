// Referee 75: toy check of note 73, Theorem 5.1, over GF(2^8). The top J levels are a random tree code conditioned on being MDS
// (rejection, all k_J-subsets checked); the levels below are random (T1 or T2). For each code, every subset Z of the n leaves is
// visited (DFS with an incremental echelon basis) and E = max { |Z| - rk(Z) : rk(Z) < k } is recorded, with the largest number of
// zeros of a nonzero codeword. Output: the histogram of E, to be compared with eps_0 n computed by 75_eps0.py with 64 -> 8.
// usage: 75_toy r v J variant trials seed
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static uint8_t gexp[512], glog[256];
static inline uint8_t mul(uint8_t a, uint8_t b) { return (a && b) ? gexp[glog[a] + glog[b]] : 0; }
static inline uint8_t inv(uint8_t a) { return gexp[255 - glog[a]]; }
static uint64_t s0 = 88172645463325252ull, s1 = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; a ^= a >> 17; a ^= b ^ (b >> 26); s1 = a; return a + b; }
static int r, v, J, variant, n, k;
static uint8_t G[64][16];           // leaf rows
static uint8_t tw[8][64];           // tw[j][node of level j], j = 1..v (node count 2^(j+r))
static void rows_at(int lev, uint8_t out[][16]) { // rows of T_lev
    int cnt = 1 << (lev + r);
    for (int p = 0; p < cnt; p++) { out[p][0] = 1; for (int j = 1; j <= lev; j++) { uint8_t t = tw[j][p >> (lev - j)]; int h = 1 << (j - 1); for (int e = 0; e < h; e++) out[p][e + h] = mul(out[p][e], t); } }
}
static int rank_of(uint8_t M[][16], int R, int C) { int rk = 0; for (int c = 0; c < C && rk < R; c++) { int p = -1; for (int i = rk; i < R; i++) if (M[i][c]) { p = i; break; } if (p < 0) continue;
        if (p != rk) { uint8_t t[16]; memcpy(t, M[p], 16); memcpy(M[p], M[rk], 16); memcpy(M[rk], t, 16); } uint8_t iv = inv(M[rk][c]);
        for (int i = rk + 1; i < R; i++) if (M[i][c]) { uint8_t f = mul(M[i][c], iv); for (int j = c; j < C; j++) M[i][j] ^= mul(f, M[rk][j]); } rk++; } return rk; }
static int top_is_mds(void) { if (J == 0) return 1; static uint8_t T[64][16]; rows_at(J, T); int nJ = 1 << (J + r), kJ = 1 << J; int idx[16]; for (int i = 0; i < kJ; i++) idx[i] = i;
    for (;;) { uint8_t M[16][16]; for (int i = 0; i < kJ; i++) memcpy(M[i], T[idx[i]], 16); if (rank_of(M, kJ, kJ) < kJ) return 0;
        int i = kJ - 1; while (i >= 0 && idx[i] == nJ - kJ + i) i--; if (i < 0) return 1; idx[i]++; for (int j = i + 1; j < kJ; j++) idx[j] = idx[j - 1] + 1; } }
static void draw_level(int j) { int cnt = 1 << (j + r); for (int p = 0; p < cnt; p += 2) { uint8_t a = (uint8_t)rnd(), b; if (variant == 1) b = a ^ 1; else do b = (uint8_t)rnd(); while (b == a); tw[j][p] = a; tw[j][p + 1] = b; } }
static int bestE, bestZeros;
static void dfs(int x, uint8_t basis[][16], int *pivcol, int rk, int size) {
    if (x == n) { if (rk < k) { if (size - rk > bestE) bestE = size - rk; if (size > bestZeros) bestZeros = size; } return; }
    dfs(x + 1, basis, pivcol, rk, size);
    uint8_t row[16]; memcpy(row, G[x], 16);
    for (int i = 0; i < rk; i++) { uint8_t f = row[pivcol[i]]; if (f) for (int c = 0; c < k; c++) row[c] ^= mul(f, basis[i][c]); }
    int pc = -1; for (int c = 0; c < k; c++) if (row[c]) { pc = c; break; }
    if (pc < 0) { dfs(x + 1, basis, pivcol, rk, size + 1); return; }
    if (rk + 1 == k && 0) return;
    uint8_t nb[16][16]; int np[16]; memcpy(nb, basis, sizeof(nb)); memcpy(np, pivcol, sizeof(np));
    uint8_t iv = inv(row[pc]); for (int c = 0; c < k; c++) row[c] = mul(row[c], iv);
    for (int i = 0; i < rk; i++) { uint8_t f = nb[i][pc]; if (f) for (int c = 0; c < k; c++) nb[i][c] ^= mul(f, row[c]); }
    memcpy(nb[rk], row, 16); np[rk] = pc;
    if (rk + 1 < k) dfs(x + 1, nb, np, rk + 1, size + 1);   // a set of full rank has no nonzero codeword vanishing on it
}
int main(int argc, char **argv) {
    r = atoi(argv[1]); v = atoi(argv[2]); J = atoi(argv[3]); variant = atoi(argv[4]); long trials = atol(argv[5]); s0 ^= strtoull(argv[6], 0, 10) * 0x2545F4914F6CDD1Dull; for (int i = 0; i < 30; i++) rnd();
    n = 1 << (v + r); k = 1 << v; if (n > 32 || k > 16) { printf("too large\n"); return 1; }
    int x = 1; for (int i = 0; i < 255; i++) { gexp[i] = x; glog[x] = i; x ^= (x << 1) ^ ((x & 0x80) ? 0x11b : 0); x &= 0xff; } for (int i = 255; i < 512; i++) gexp[i] = gexp[i - 255];
    long histE[40] = {0}, histZ[40] = {0};
    for (long tr = 0; tr < trials; tr++) {
        do { for (int j = 1; j <= J; j++) draw_level(j); } while (!top_is_mds());
        for (int j = J + 1; j <= v; j++) draw_level(j);
        rows_at(v, G);
        uint8_t basis[16][16]; int piv[16]; memset(basis, 0, sizeof(basis)); bestE = 0; bestZeros = 0; dfs(0, basis, piv, 0, 0);
        histE[bestE]++; histZ[bestZeros]++;
    }
    printf("GF(2^8) T%d r=%d v=%d (k=%d, n=%d) J=%d trials=%ld\n  histogram of E = max excess |Z| - rk(Z) over Z with rk < k:", variant, r, v, k, n, J, trials);
    for (int e = 0; e < 40; e++) if (histE[e]) printf(" E=%d:%ld", e, histE[e]);
    printf("\n  histogram of the largest number of zeros of a nonzero codeword:"); for (int e = 0; e < 40; e++) if (histZ[e]) printf(" %d:%ld", e, histZ[e]); printf("\n");
    return 0;
}
