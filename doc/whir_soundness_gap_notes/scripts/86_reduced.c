// Note 86: three members. Certified check of (C*) on (a) every pattern of the upper levels and (b) every REDUCED pattern of
// the bottom level (an upper pattern Q with every node doubled, plus one triple leaf in some of the pairs where Q is empty).
// By Corollary 1.4 of note 86, (C*) for all reduced patterns at a size gives (C*) for all three-member patterns at that size.
// Certification: ranks at the top level (k = 1) have no twiddle. At every other level the rank at the draw is a lower bound on the
// generic rank and B(P;Q) with generic upper ranks is an upper bound; so rank = B on every pattern of a level certifies that the
// drawn ranks of that level are the generic ones, which the next level down uses.
// Build: cc -O2 -o 86_bin/86_reduced 86_reduced.c      Run: 86_reduced v r seed [list]     (k = 2^v, n = 2^(v+r))
#define FB 64
#include "69_gf.h"
#define MAXN 64
#define MAXV 6
static const int NB[5] = {0, 1, 1, 1, 2};
static const int BAS[5][2] = {{0, 0}, {1, 0}, {2, 0}, {3, 0}, {1, 2}};
static int JOIN[5][5];
static int V, RR;
static int NN[MAXV + 1], KK[MAXV + 1];
static fe G[MAXV + 1][MAXN][MAXN];
static void make_codes(void) {
    static fe tw[MAXV][MAXN];
    int n = 1 << (V + RR);
    for (int i = 0; i < V; i++) for (int q = 0; q < (n >> i); q++) tw[i][q] = gf_rand();
    for (int h = 0; h <= V; h++) { NN[h] = n >> h; KK[h] = 1 << (V - h);
        for (int u = 0; u < NN[h]; u++) { G[h][u][0] = 1; for (int i = h; i < V; i++) { fe x = tw[i][u >> (i - h)]; for (int e = 0; e < (1 << (i - h)); e++) G[h][u][e | (1 << (i - h))] = gf_mul(G[h][u][e], x); } } }
}
static fe M[2 * MAXN][2 * MAXN]; static int pivcol[2 * MAXN];
static int rank_pattern(int h, const int *pid, int reduce) {
    int K = KK[h], cols = 2 * K, rows = 0;
    for (int x = 0; x < NN[h]; x++) for (int b = 0; b < NB[pid[x]]; b++) { fe *row = M[rows++]; memset(row, 0, sizeof(fe) * cols); int vec = BAS[pid[x]][b]; for (int a = 0; a < 2; a++) if ((vec >> a) & 1) memcpy(row + a * K, G[h][x], sizeof(fe) * K); }
    int rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1; for (int i = rk; i < rows; i++) if (M[i][c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = 0; j < cols; j++) { fe t = M[p][j]; M[p][j] = M[rk][j]; M[rk][j] = t; }
        fe inv = gf_inv(M[rk][c]);
        if (reduce) for (int j = 0; j < cols; j++) M[rk][j] = gf_mul(M[rk][j], inv);
        for (int i = reduce ? 0 : rk + 1; i < rows; i++) { fe f = M[i][c]; if (!f || i == rk) continue; if (!reduce) f = gf_mul(f, inv); for (int j = c; j < cols; j++) M[i][j] ^= gf_mul(f, M[rk][j]); }
        pivcol[rk++] = c;
    }
    return rk;
}
// rank tables per level (base-5 index), filled on demand; only for levels with at most 12 nodes
static signed char *tab[MAXV + 1];
static long idx_of(int h, const int *pid) { long s = 0; for (int x = 0; x < NN[h]; x++) s = s * 5 + pid[x]; return s; }
static int rk_level(int h, const int *pid) {
    if (NN[h] > 12) return rank_pattern(h, pid, 0);
    if (!tab[h]) { long sz = 1; for (int x = 0; x < NN[h]; x++) sz *= 5; tab[h] = malloc(sz); memset(tab[h], -1, sz); }
    long i = idx_of(h, pid); if (tab[h][i] < 0) tab[h][i] = (signed char)rank_pattern(h, pid, 0); return tab[h][i];
}
static void full_part(int h, const int *pid, int rk, int *q) { // binary full part: theta (x) g_p (x) e_b in R for b = 0, 1
    int K = KK[h], cols = 2 * K; fe vec[2 * MAXN];
    rank_pattern(h, pid, 1);
    for (int p = 0; p < NN[h + 1]; p++) { int in[4] = {0, 1, 1, 1};
        for (int th = 1; th <= 3; th++) for (int b = 0; b < 2 && in[th]; b++) {
            memset(vec, 0, sizeof(fe) * cols);
            for (int a = 0; a < 2; a++) if ((th >> a) & 1) for (int e = 0; e < K / 2; e++) vec[a * K + 2 * e + b] = G[h + 1][p][e];
            for (int i = 0; i < rk; i++) { fe f = vec[pivcol[i]]; if (f) for (int j = 0; j < cols; j++) vec[j] ^= gf_mul(f, M[i][j]); }
            for (int j = 0; j < cols; j++) if (vec[j]) { in[th] = 0; break; } }
        int cnt = in[1] + in[2] + in[3];
        q[p] = cnt == 3 ? 4 : in[1] ? 1 : in[2] ? 2 : in[3] ? 3 : 0;
        if (cnt == 2) { fprintf(stderr, "full part not a subspace\n"); exit(1); } }
}
static int bound(int h, const int *pid, int *q) {
    int base = rk_level(h + 1, q), s = 2 * base;
    for (int x = 0; x < NN[h]; x++) { int p = x >> 1, d = q[p], nd = JOIN[d][pid[x]]; if (nd != d) { q[p] = nd; s += rk_level(h + 1, q) - base; q[p] = d; } }
    return s;
}
static const char *NAME[5] = {".", "01", "02", "12", "012"};
static long c_tot, c_dep, c_ok, c_fail; static int do_list;
static void test_one(int h, const int *pid) {
    int w = 0, q[MAXN]; for (int x = 0; x < NN[h]; x++) w += NB[pid[x]];
    int rk = rk_level(h, pid); c_tot++; c_dep += rk < w;
    full_part(h, pid, rk, q); int b = bound(h, pid, q);
    if (b == rk) { c_ok++; return; }
    c_fail++;
    if (c_fail <= 40 || do_list) { printf("  FAIL level %d: w %d rank %d B(P;Q*) %d: ", h, w, rk, b); for (int x = 0; x < NN[h]; x++) printf("%s ", NAME[pid[x]]); printf("| Q* = "); for (int p = 0; p < NN[h + 1]; p++) printf("%s ", NAME[q[p]]); printf("\n"); fflush(stdout); }
}
int main(int argc, char **argv) {
    V = atoi(argv[1]); RR = atoi(argv[2]); rng_seed(atol(argv[3])); do_list = argc > 4;
    for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) JOIN[a][b] = a == 0 ? b : b == 0 ? a : a == b ? a : 4;
    make_codes(); int pid[MAXN];
    printf("three members, k = %d, n = %d, seed %s\n", 1 << V, 1 << (V + RR), argv[3]);
    if (argc > 4 && !strcmp(argv[4], "struct")) { // random patterns built from a random pattern Q2 two levels up (not certified)
        long count = atol(argv[5]); int n2 = NN[2], q2[MAXN]; do_list = argc > 6; long shown = 0;
        for (long it = 0; it < count; it++) {
            int dens = 2 + rng_below(6);
            for (int u = 0; u < n2; u++) q2[u] = rng_below(10) < (uint64_t)dens ? 1 + rng_below(4) : 0;
            for (int u = 0; u < n2; u++) for (int j = 0; j < 4; j++) {
                int c = q2[u];
                if (c == 0) c = rng_below(2) ? 4 : 0;            // empty node: any subset of its four leaves is a triple
                else if (c < 4 && rng_below(8) == 0) c = 4;        // pair node: a few leaves raised to triples
                pid[4 * u + j] = c; }
            long before = c_fail; test_one(0, pid); (void)before; (void)shown;
        }
        printf("structured random patterns: %ld, rows dependent %ld, rank = B(P;Q*) %ld, failures of (C*) %ld\n", c_tot, c_dep, c_ok, c_fail);
        return 0;
    }
    if (argc > 4 && !strcmp(argv[4], "redrand")) { // random reduced patterns (not certified): Q random at level 1, random lonely triples
        long count = atol(argv[5]); int n1 = NN[1], q1[MAXN]; do_list = argc > 6;
        for (long it = 0; it < count; it++) {
            int kind = rng_below(3), dens = 2 + rng_below(7);
            for (int p = 0; p < n1; p++) q1[p] = rng_below(10) < (uint64_t)dens ? 1 + rng_below(4) : 0;
            if (kind == 1) for (int p = 0; p < n1; p += 2) q1[p + 1] = q1[p];                               // doubled from level 2
            if (kind == 2) for (int p = 0; p < n1; p += 2) if (rng_below(3)) q1[p + 1] = q1[p];             // mostly doubled
            for (int p = 0; p < n1; p++) { pid[2 * p] = pid[2 * p + 1] = q1[p]; if (!q1[p] && rng_below(2)) pid[2 * p + 1] = 4; }
            test_one(0, pid);
        }
        printf("random reduced patterns: %ld, rows dependent %ld, rank = B(P;Q*) %ld, failures of (C*) %ld\n", c_tot, c_dep, c_ok, c_fail);
        return 0;
    }
    // levels V-1 down to 1: every pattern
    for (int h = V - 1; h >= 1; h--) {
        if (NN[h] > 8) { printf("level %d (k = %d, n = %d): too many patterns for the exhaustive pass, stopping the certified chain here\n", h, KK[h], NN[h]); return 1; }
        long tot = 1; for (int x = 0; x < NN[h]; x++) tot *= 5; c_tot = c_dep = c_ok = c_fail = 0;
        for (long i = 0; i < tot; i++) { long s = i; for (int x = NN[h] - 1; x >= 0; x--) { pid[x] = s % 5; s /= 5; } test_one(h, pid); }
        printf("level %d (k = %d, n = %d): all %ld patterns, rows dependent %ld, rank = B(P;Q*) %ld, failures %ld\n", h, KK[h], NN[h], c_tot, c_dep, c_ok, c_fail); fflush(stdout);
        if (c_fail) return 1;
    }
    // level 0: every reduced pattern
    int n1 = NN[1], q1[MAXN], zero[MAXN]; long tot = 1; for (int x = 0; x < n1; x++) tot *= 5; c_tot = c_dep = c_ok = c_fail = 0;
    for (long i = 0; i < tot; i++) { long s = i; int nz = 0; for (int x = n1 - 1; x >= 0; x--) { q1[x] = s % 5; s /= 5; } for (int x = 0; x < n1; x++) if (!q1[x]) zero[nz++] = x;
        for (int mask = 0; mask < (1 << nz); mask++) {
            for (int p = 0; p < n1; p++) pid[2 * p] = pid[2 * p + 1] = q1[p];
            for (int j = 0; j < nz; j++) if ((mask >> j) & 1) pid[2 * zero[j] + 1] = 4;
            test_one(0, pid); } }
    printf("level 0 (k = %d, n = %d): all %ld reduced patterns, rows dependent %ld, rank = B(P;Q*) %ld, failures %ld\n", KK[0], NN[0], c_tot, c_dep, c_ok, c_fail);
    return 0;
}
