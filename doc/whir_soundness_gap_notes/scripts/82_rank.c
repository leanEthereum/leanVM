// Note 82: exact generic ranks of partition patterns in the tree code T2 over GF(2^64), and the graphic bound
// B(P;Q) = 2 r_up(Q) + sum_x (r_up(Q v pi_x@p(x)) - r_up(Q)) of Lemma 1.1, minimized over all upper partition patterns Q.
// Build: cc -O2 -o 82_bin/82_rank 82_rank.c
// Modes:
//   table v r m out.bin              ranks of all B_m^n partition patterns at (v, r), one byte each (v = 0 allowed)
//   all   v r m up.bin               every pattern at (v, r): exact rank against min_Q B (up.bin = table at (v-1, r))
//   rand  v r m up.bin count seed minw [classonly]   random patterns of weight >= minw
//   file  v r m up.bin patterns.txt  patterns "... | c c c" with classes as digit strings
// A pattern code is sum_x id(pi_x) * B^x, leaf 0 the lowest digit; pair p = leaves 2p, 2p+1.
#define FB 64
#include "69_gf.h"
#define MAXM 6
#define MAXB 203
#define MAXN 64
static int m, L, NB;                 // members, m - 1, Bell number
static int rgs[MAXB][MAXM], nblk[MAXB], jointab[MAXB][MAXB], pdim[MAXB];
static int nbas[MAXB], basA[MAXB][MAXM], basB[MAXB][MAXM];
static void gen_partitions(void) {
    int a[MAXM] = {0}; NB = 0;
    for (;;) {
        int mx = 0; for (int i = 0; i < m; i++) { rgs[NB][i] = a[i]; if (a[i] > mx) mx = a[i]; }
        nblk[NB] = mx + 1; pdim[NB] = m - nblk[NB];
        int first[MAXM]; for (int b = 0; b < m; b++) first[b] = -1;
        nbas[NB] = 0;
        for (int i = 0; i < m; i++) { if (first[a[i]] < 0) first[a[i]] = i; else { basA[NB][nbas[NB]] = first[a[i]]; basB[NB][nbas[NB]] = i; nbas[NB]++; } }
        NB++;
        int i = m - 1;
        for (; i > 0; i--) { int pm = 0; for (int j = 0; j < i; j++) if (a[j] > pm) pm = a[j]; if (a[i] <= pm) { a[i]++; for (int j = i + 1; j < m; j++) a[j] = 0; break; } }
        if (i == 0) break;
    }
}
static int find_id(const int *lab) { // canonicalize labels to an rgs and look it up
    int map[MAXM], c[MAXM], nx = 0; for (int i = 0; i < m; i++) map[i] = -1;
    for (int i = 0; i < m; i++) { if (map[lab[i]] < 0) map[lab[i]] = nx++; c[i] = map[lab[i]]; }
    for (int id = 0; id < NB; id++) { int ok = 1; for (int i = 0; i < m; i++) if (rgs[id][i] != c[i]) { ok = 0; break; } if (ok) return id; }
    return -1;
}
static void gen_join(void) {
    for (int a = 0; a < NB; a++) for (int b = 0; b < NB; b++) {
        int par[MAXM]; for (int i = 0; i < m; i++) par[i] = i;
        for (int pass = 0; pass < 2; pass++) { const int *g = pass ? rgs[b] : rgs[a];
            for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (g[i] == g[j]) { int x = i, y = j; while (par[x] != x) x = par[x]; while (par[y] != y) y = par[y]; if (x != y) par[y] = x; } }
        int lab[MAXM]; for (int i = 0; i < m; i++) { int x = i; while (par[x] != x) x = par[x]; lab[i] = x; }
        jointab[a][b] = find_id(lab);
    }
}
static int class_id(const char *tok) { // "." or digits: one class, everything else singletons
    int lab[MAXM]; for (int i = 0; i < m; i++) lab[i] = i;
    if (tok[0] != '.') { int f = tok[0] - '0'; for (const char *c = tok; *c; c++) lab[*c - '0'] = f; }
    return find_id(lab);
}
// ---- tree code
static int V, RR, N, K;
static fe tw[16][MAXN], G[MAXN][MAXN];
static void make_code(int v, int r) {
    V = v; RR = r; N = 1 << (v + r); K = 1 << v;
    for (int i = 0; i < v; i++) for (int q = 0; q < (N >> i); q++) tw[i][q] = gf_rand();
    for (int j = 0; j < N; j++) { G[j][0] = 1; for (int i = 0; i < v; i++) { fe x = tw[i][j >> i]; for (int e = 0; e < (1 << i); e++) G[j][e | (1 << i)] = gf_mul(G[j][e], x); } }
}
static fe M[MAXN * MAXM][MAXN * MAXM];
static int rank_pattern(const int *pid) {
    int cols = L * K, rows = 0;
    for (int x = 0; x < N; x++) for (int b = 0; b < nbas[pid[x]]; b++) {
        fe *row = M[rows++]; memset(row, 0, sizeof(fe) * cols);
        int A = basA[pid[x]][b], B = basB[pid[x]][b];
        if (A > 0) memcpy(row + (A - 1) * K, G[x], sizeof(fe) * K);
        if (B > 0) memcpy(row + (B - 1) * K, G[x], sizeof(fe) * K);
    }
    int rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1; for (int i = rk; i < rows; i++) if (M[i][c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = c; j < cols; j++) { fe t = M[p][j]; M[p][j] = M[rk][j]; M[rk][j] = t; }
        fe inv = gf_inv(M[rk][c]);
        for (int i = rk + 1; i < rows; i++) { fe f = M[i][c]; if (!f) continue; f = gf_mul(f, inv); for (int j = c; j < cols; j++) M[i][j] ^= gf_mul(f, M[rk][j]); }
        rk++;
    }
    return rk;
}
static unsigned char *up; static uint64_t upsize, powB[MAXN + 1];
static void load_up(const char *fn, int nup) {
    powB[0] = 1; for (int i = 1; i <= MAXN && powB[i - 1] < (1ull << 58) / NB; i++) powB[i] = powB[i - 1] * NB;
    upsize = powB[nup]; up = (unsigned char *)malloc(upsize);
    FILE *f = fopen(fn, "rb"); if (!f || fread(up, 1, upsize, f) != upsize) { fprintf(stderr, "bad table %s\n", fn); exit(1); } fclose(f);
}
// min over Q of B(P;Q); restricted = 1: only Q_p refining pi_{p0} v pi_{p1}. argmin returned in *best.
static int min_bound(const int *pid, int restricted, uint64_t *best) {
    int np = N / 2, bestv = 1 << 30, cap[MAXN];
    for (int p = 0; p < np; p++) cap[p] = jointab[pid[2 * p]][pid[2 * p + 1]];
    for (uint64_t q = 0; q < upsize; q++) {
        int d[MAXN]; uint64_t t = q; int ok = 1;
        for (int p = 0; p < np; p++) { d[p] = t % NB; t /= NB; if (restricted && jointab[d[p]][cap[p]] != cap[p]) { ok = 0; break; } }
        if (!ok) continue;
        int base = up[q], s = 2 * base;
        for (int x = 0; x < N && s < bestv; x++) { int p = x >> 1, nd = jointab[d[p]][pid[x]]; if (nd != d[p]) s += up[q + (uint64_t)(nd - d[p]) * powB[p]] - base; }
        if (s < bestv) { bestv = s; *best = q; }
    }
    return bestv;
}
static void print_pat(const int *pid, int n) {
    for (int x = 0; x < n; x++) { const int *g = rgs[pid[x]]; int any = 0;
        for (int b = 0; b < m; b++) { int cnt = 0; for (int i = 0; i < m; i++) cnt += g[i] == b; if (cnt >= 2) { if (any) printf("/"); for (int i = 0; i < m; i++) if (g[i] == b) printf("%d", i); any = 1; } }
        if (!any) printf("."); printf(" "); }
}
static long cnt_tot, cnt_dep, cnt_ok_restricted, cnt_ok_full, cnt_fail, cnt_below;
static void test_one(const int *pid) {
    int w = 0; for (int x = 0; x < N; x++) w += pdim[pid[x]];
    int rk = rank_pattern(pid); uint64_t bq = 0;
    cnt_tot++; cnt_dep += rk < w;
    int b = min_bound(pid, 1, &bq);
    if (b == rk) { cnt_ok_restricted++; return; }
    if (b < rk) { cnt_below++; printf("BELOW (bug) rank %d bound %d: ", rk, b); print_pat(pid, N); printf("\n"); return; }
    b = min_bound(pid, 0, &bq);
    if (b == rk) { cnt_ok_full++; if (cnt_ok_full <= 5) { printf("needs unrestricted Q: rank %d w %d: ", rk, w); print_pat(pid, N); printf("\n"); } return; }
    if (b < rk) { cnt_below++; return; }
    cnt_fail++;
    if (cnt_fail <= 40) { printf("FAIL rank %d min_Q B %d w %d: ", rk, b, w); print_pat(pid, N); printf("\n"); fflush(stdout); }
}
static void summary(const char *what) {
    printf("%s: patterns %ld, rows dependent %ld, min_Q B = rank with Q below the sibling join %ld, only with other Q %ld, min_Q B > rank (C fails) %ld, below rank (bug) %ld\n", what, cnt_tot, cnt_dep, cnt_ok_restricted, cnt_ok_full, cnt_fail, cnt_below);
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: see header\n"); return 1; }
    const char *mode = argv[1]; int v = atoi(argv[2]), r = atoi(argv[3]); m = atoi(argv[4]); L = m - 1;
    gen_partitions(); gen_join(); rng_seed(82);
    make_code(v, r);
    int pid[MAXN];
    if (!strcmp(mode, "table")) {
        uint64_t tot = 1; for (int i = 0; i < N; i++) tot *= NB;
        unsigned char *tab = (unsigned char *)malloc(tot);
        for (uint64_t q = 0; q < tot; q++) { uint64_t t = q; for (int x = 0; x < N; x++) { pid[x] = t % NB; t /= NB; } tab[q] = (unsigned char)rank_pattern(pid); }
        FILE *f = fopen(argv[5], "wb"); fwrite(tab, 1, tot, f); fclose(f);
        printf("table (v=%d, r=%d, members %d): %llu patterns written to %s\n", v, r, m, (unsigned long long)tot, argv[5]);
        return 0;
    }
    load_up(argv[5], N / 2);
    char what[256];
    if (!strcmp(mode, "all")) {
        uint64_t tot = 1; for (int i = 0; i < N; i++) tot *= NB;
        for (uint64_t q = 0; q < tot; q++) { uint64_t t = q; for (int x = 0; x < N; x++) { pid[x] = t % NB; t /= NB; } test_one(pid); }
        snprintf(what, sizeof what, "all patterns (k=%d, n=%d, members %d)", K, N, m);
    } else if (!strcmp(mode, "rand")) {
        long count = atol(argv[6]); rng_seed(atol(argv[7])); make_code(v, r); int minw = atoi(argv[8]), classonly = argc > 9;
        int cls[MAXB], ncls = 0; for (int id = 0; id < NB; id++) { int big = 0; for (int b = 0; b < m; b++) { int c = 0; for (int i = 0; i < m; i++) c += rgs[id][i] == b; big += c >= 2; } if (!classonly || big <= 1) cls[ncls++] = id; }
        for (long it = 0; it < count;) { int w = 0; for (int x = 0; x < N; x++) { pid[x] = cls[rng_below(ncls)]; w += pdim[pid[x]]; } if (w < minw) continue; it++; test_one(pid); }
        snprintf(what, sizeof what, "random patterns (k=%d, n=%d, members %d, weight >= %d, %s, seed %s)", K, N, m, minw, classonly ? "classes" : "partitions", argv[7]);
    } else if (!strcmp(mode, "file")) {
        FILE *f = fopen(argv[6], "r"); char line[4096];
        while (fgets(line, sizeof line, f)) { char *s = strchr(line, '|'); s = s ? s + 1 : line; int x = 0; for (char *tok = strtok(s, " \n"); tok && x < N; tok = strtok(NULL, " \n")) pid[x++] = class_id(tok); if (x == N) test_one(pid); }
        fclose(f); snprintf(what, sizeof what, "file %s (k=%d, n=%d, members %d)", argv[6], K, N, m);
    }
    summary(what);
    return 0;
}
