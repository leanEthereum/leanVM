// Note 86: m members (binary patterns: a node carries any subspace of F_2^(m-1)). Certified check of (C*) on every binary pattern
// of the upper levels and on every REDUCED binary pattern of the bottom level: in every bottom pair (A, B), with M = A cap B,
// each of A, B is M or has dimension at least dim M + 2. By Lemma 1.6 of note 86 this gives (C*) for all binary patterns.
// Certification as in 86_reduced.c (the top level has no twiddle).
// Build: cc -O2 -o 86_bin/86_reduced_m 86_reduced_m.c      Run: 86_reduced_m m v r seed
#define FB 64
#include "69_gf.h"
#define MAXM 5
#define MAXB 70
#define MAXN 32
#define MAXV 4
static int m, L, NBS;
static uint32_t smask[MAXB];
static int jointab[MAXB][MAXB], meettab[MAXB][MAXB], pdim[MAXB], nbas[MAXB], basV[MAXB][MAXM];
static uint32_t span_add(uint32_t s, int v) { uint32_t out = s; for (int u = 0; u < (1 << L); u++) if ((s >> u) & 1) out |= 1u << (u ^ v); return out; }
static int find_mask(uint32_t s) { for (int i = 0; i < NBS; i++) if (smask[i] == s) return i; return -1; }
static void gen_subspaces(void) {
    NBS = 0; smask[NBS++] = 1u;
    for (int i = 0; i < NBS; i++) for (int v = 1; v < (1 << L); v++) { if ((smask[i] >> v) & 1) continue; uint32_t s = span_add(smask[i], v); if (find_mask(s) < 0) smask[NBS++] = s; }
    for (int i = 0; i < NBS; i++) { uint32_t cur = 1u; nbas[i] = 0; for (int v = 1; v < (1 << L); v++) if (((smask[i] >> v) & 1) && !((cur >> v) & 1)) { basV[i][nbas[i]++] = v; cur = span_add(cur, v); } pdim[i] = nbas[i]; }
    for (int a = 0; a < NBS; a++) for (int b = 0; b < NBS; b++) { uint32_t s = smask[a]; for (int j = 0; j < nbas[b]; j++) s = span_add(s, basV[b][j]); jointab[a][b] = find_mask(s); meettab[a][b] = find_mask(smask[a] & smask[b]); }
}
static int V, RR, NN[MAXV + 1], KK[MAXV + 1];
static fe G[MAXV + 1][MAXN][MAXN];
static void make_codes(void) {
    static fe tw[MAXV][MAXN]; int n = 1 << (V + RR);
    for (int i = 0; i < V; i++) for (int q = 0; q < (n >> i); q++) tw[i][q] = gf_rand();
    for (int h = 0; h <= V; h++) { NN[h] = n >> h; KK[h] = 1 << (V - h);
        for (int u = 0; u < NN[h]; u++) { G[h][u][0] = 1; for (int i = h; i < V; i++) { fe x = tw[i][u >> (i - h)]; for (int e = 0; e < (1 << (i - h)); e++) G[h][u][e | (1 << (i - h))] = gf_mul(G[h][u][e], x); } } }
}
static fe M[MAXN * MAXM][MAXN * MAXM]; static int pivcol[MAXN * MAXM];
static int rank_pattern(int h, const int *pid, int reduce) {
    int K = KK[h], cols = L * K, rows = 0;
    for (int x = 0; x < NN[h]; x++) for (int b = 0; b < nbas[pid[x]]; b++) { fe *row = M[rows++]; memset(row, 0, sizeof(fe) * cols); int vec = basV[pid[x]][b]; for (int a = 0; a < L; a++) if ((vec >> a) & 1) memcpy(row + a * K, G[h][x], sizeof(fe) * K); }
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
static signed char *tab[MAXV + 1];
static int rk_level(int h, const int *pid) {
    double sz = 1; for (int x = 0; x < NN[h]; x++) sz *= NBS;
    if (sz > 3e8) return rank_pattern(h, pid, 0);
    if (!tab[h]) { tab[h] = malloc((size_t)sz); memset(tab[h], -1, (size_t)sz); }
    long i = 0; for (int x = 0; x < NN[h]; x++) i = i * NBS + pid[x];
    if (tab[h][i] < 0) tab[h][i] = (signed char)rank_pattern(h, pid, 0); return tab[h][i];
}
static void full_part(int h, const int *pid, int rk, int *q) {
    int K = KK[h], cols = L * K; fe vec[MAXN * MAXM];
    rank_pattern(h, pid, 1);
    for (int p = 0; p < NN[h + 1]; p++) { uint32_t s = 1u;
        for (int th = 1; th < (1 << L); th++) { int ok = 1;
            for (int b = 0; b < 2 && ok; b++) {
                memset(vec, 0, sizeof(fe) * cols);
                for (int a = 0; a < L; a++) if ((th >> a) & 1) for (int e = 0; e < K / 2; e++) vec[a * K + 2 * e + b] = G[h + 1][p][e];
                for (int i = 0; i < rk; i++) { fe f = vec[pivcol[i]]; if (f) for (int j = 0; j < cols; j++) vec[j] ^= gf_mul(f, M[i][j]); }
                for (int j = 0; j < cols; j++) if (vec[j]) { ok = 0; break; } }
            if (ok) s |= 1u << th; }
        q[p] = find_mask(s); if (q[p] < 0) { fprintf(stderr, "full part not a subspace\n"); exit(1); } }
}
static int bound(int h, const int *pid, int *q) {
    int base = rk_level(h + 1, q), s = 2 * base;
    for (int x = 0; x < NN[h]; x++) { int p = x >> 1, d = q[p], nd = jointab[d][pid[x]]; if (nd != d) { q[p] = nd; s += rk_level(h + 1, q) - base; q[p] = d; } }
    return s;
}
static long c_tot, c_dep, c_ok, c_fail;
static void print_pat(const int *pid, int n) {
    for (int x = 0; x < n; x++) { int id = pid[x]; if (!nbas[id]) printf(".");
        for (int b = 0; b < nbas[id]; b++) { int v = basV[id][b]; if (b) printf("+"); if (__builtin_popcount(v) & 1) printf("0"); for (int a = 1; a < m; a++) if ((v >> (a - 1)) & 1) printf("%d", a); }
        printf(" "); }
}
static void test_one(int h, const int *pid) {
    int w = 0, q[MAXN]; for (int x = 0; x < NN[h]; x++) w += pdim[pid[x]];
    int rk = rk_level(h, pid); c_tot++; c_dep += rk < w;
    full_part(h, pid, rk, q); int b = bound(h, pid, q);
    if (b == rk) { c_ok++; return; }
    c_fail++; if (c_fail <= 30) { printf("  FAIL level %d: w %d rank %d B(P;Q*) %d: ", h, w, rk, b); print_pat(pid, NN[h]); printf("| Q* = "); print_pat(q, NN[h + 1]); printf("\n"); fflush(stdout); }
}
int main(int argc, char **argv) {
    if (argc < 5) return 1;
    m = atoi(argv[1]); L = m - 1; V = atoi(argv[2]); RR = atoi(argv[3]); rng_seed(atol(argv[4]));
    gen_subspaces(); make_codes(); int pid[MAXN];
    printf("%d members (%d binary subspaces), k = %d, n = %d, seed %s\n", m, NBS, 1 << V, 1 << (V + RR), argv[4]);
    for (int h = V - 1; h >= 1; h--) {
        double tot = 1; for (int x = 0; x < NN[h]; x++) tot *= NBS; if (tot > 2e7) { printf("level %d: too many patterns\n", h); return 1; }
        c_tot = c_dep = c_ok = c_fail = 0;
        for (long i = 0; i < (long)tot; i++) { long s = i; for (int x = NN[h] - 1; x >= 0; x--) { pid[x] = s % NBS; s /= NBS; } test_one(h, pid); }
        printf("level %d (k = %d, n = %d): all %ld binary patterns, rows dependent %ld, rank = B(P;Q*) %ld, failures %ld\n", h, KK[h], NN[h], c_tot, c_dep, c_ok, c_fail); fflush(stdout);
        if (c_fail) return 1;
    }
    static int pa[MAXB * MAXB], pb[MAXB * MAXB]; int np = 0;
    for (int a = 0; a < NBS; a++) for (int b = a; b < NBS; b++) { int mt = meettab[a][b];
        if ((a == mt || pdim[a] - pdim[mt] >= 2) && (b == mt || pdim[b] - pdim[mt] >= 2)) { pa[np] = a; pb[np] = b; np++; } }
    int n1 = NN[1]; double tot = 1; for (int x = 0; x < n1; x++) tot *= np;
    printf("reduced pairs: %d, reduced patterns: %.0f\n", np, tot); if (tot > 4e9) return 1;
    c_tot = c_dep = c_ok = c_fail = 0;
    for (long i = 0; i < (long)tot; i++) { long s = i; for (int p = n1 - 1; p >= 0; p--) { int j = s % np; s /= np; pid[2 * p] = pa[j]; pid[2 * p + 1] = pb[j]; } test_one(0, pid); }
    printf("level 0 (k = %d, n = %d): all %ld reduced binary patterns, rows dependent %ld, rank = B(P;Q*) %ld, failures %ld\n", KK[0], NN[0], c_tot, c_dep, c_ok, c_fail);
    return 0;
}
