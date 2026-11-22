// Note 82 (binary patterns: every leaf carries a subspace of the even-weight code of length m over F_2; generated from 82_rank.c).
// Note 82: exact generic ranks of partition patterns in the tree code T2 over GF(2^64), and the graphic bound
// B(P;Q) = 2 r_up(Q) + sum_x (r_up(Q v pi_x@p(x)) - r_up(Q)) of Lemma 1.1, minimized over all upper partition patterns Q.
// Build: cc -O2 -o 82_bin/82_bin 82_binary.c
// Modes:
//   table v r m out.bin              ranks of all B_m^n partition patterns at (v, r), one byte each (v = 0 allowed)
//   all   v r m up.bin               every pattern at (v, r): exact rank against min_Q B (up.bin = table at (v-1, r))
//   rand  v r m up.bin count seed minw [binary|graphic|class]   random patterns of weight >= minw
//   file  v r m up.bin patterns.txt  patterns "... | c c c" with classes as digit strings
// A pattern code is sum_x id(pi_x) * B^x, leaf 0 the lowest digit; pair p = leaves 2p, 2p+1.
#define FB 64
#include "69_gf.h"
#define MAXM 6
#define MAXB 400
#define MAXN 64
static int m, L, NB;                 // members, m - 1, number of subspaces of F_2^L (the even-weight code of length m)
static uint32_t smask[MAXB];         // a subspace as the set of its vectors (bit v set iff v in it), v in 0..2^L-1, member a >= 1 is bit a-1
static int jointab[MAXB][MAXB], pdim[MAXB], nbas[MAXB], basV[MAXB][MAXM];
static uint32_t span_add(uint32_t s, int v) { uint32_t out = s; for (int u = 0; u < (1 << L); u++) if ((s >> u) & 1) out |= 1u << (u ^ v); return out; }
static int find_mask(uint32_t s) { for (int i = 0; i < NB; i++) if (smask[i] == s) return i; return -1; }
static void gen_partitions(void) {
    NB = 0; smask[NB++] = 1u;
    for (int i = 0; i < NB; i++) for (int v = 1; v < (1 << L); v++) { if ((smask[i] >> v) & 1) continue; uint32_t s = span_add(smask[i], v); if (find_mask(s) < 0) { if (NB >= MAXB) { fprintf(stderr, "too many subspaces\n"); exit(1); } smask[NB++] = s; } }
    for (int i = 0; i < NB; i++) { uint32_t cur = 1u; nbas[i] = 0; for (int v = 1; v < (1 << L); v++) if (((smask[i] >> v) & 1) && !((cur >> v) & 1)) { basV[i][nbas[i]++] = v; cur = span_add(cur, v); } pdim[i] = nbas[i]; }
}
static void gen_join(void) {
    for (int a = 0; a < NB; a++) for (int b = 0; b < NB; b++) { uint32_t s = smask[a]; for (int j = 0; j < nbas[b]; j++) s = span_add(s, basV[b][j]); jointab[a][b] = find_mask(s); }
}
static int memvec(int a) { return a ? 1 << (a - 1) : 0; }
static int class_id(const char *tok) { // "." or blocks of digits separated by '/': the span of the differences inside each block
    uint32_t s = 1u; if (tok[0] == '.') return find_mask(s);
    int first = -1;
    for (const char *c = tok; *c; c++) { if (*c == '/') { first = -1; continue; } int a = *c - '0'; if (first < 0) first = a; else s = span_add(s, memvec(first) ^ memvec(a)); }
    return find_mask(s);
}
static int is_graphic[MAXB], is_class[MAXB];
static void mark_kinds(void) { // graphic: spanned by differences of two members; class: all of them inside one block
    for (int i = 0; i < NB; i++) {
        uint32_t s = 1u; int par[MAXM]; for (int a = 0; a < m; a++) par[a] = a;
        for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) { int v = memvec(a) ^ memvec(b); if ((smask[i] >> v) & 1) { s = span_add(s, v); int x = a, y = b; while (par[x] != x) x = par[x]; while (par[y] != y) y = par[y]; if (x != y) par[y] = x; } }
        is_graphic[i] = s == smask[i];
        int big = 0; for (int a = 0; a < m; a++) { int c = 0; for (int b = 0; b < m; b++) { int y = b; while (par[y] != y) y = par[y]; c += y == a; } big += c >= 2; }
        is_class[i] = is_graphic[i] && big <= 1;
    }
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
        int vec = basV[pid[x]][b];
        for (int a = 0; a < L; a++) if ((vec >> a) & 1) memcpy(row + a * K, G[x], sizeof(fe) * K);
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
static void print_pat(const int *pid, int n) { // every basis vector as the even set of members it is the indicator of, vectors of a leaf joined by '+'
    for (int x = 0; x < n; x++) { int id = pid[x];
        if (!nbas[id]) printf(".");
        for (int b = 0; b < nbas[id]; b++) { int v = basV[id][b]; if (b) printf("+"); if (__builtin_popcount(v) & 1) printf("0"); for (int a = 1; a < m; a++) if ((v >> (a - 1)) & 1) printf("%d", a); }
        printf(" "); }
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
    gen_partitions(); gen_join(); mark_kinds(); rng_seed(82);
    make_code(v, r);
    int pid[MAXN];
    if (!strcmp(mode, "table")) {
        uint64_t tot = 1; for (int i = 0; i < N; i++) tot *= NB;
        unsigned char *tab = (unsigned char *)malloc(tot);
        for (uint64_t q = 0; q < tot; q++) { uint64_t t = q; for (int x = 0; x < N; x++) { pid[x] = t % NB; t /= NB; } tab[q] = (unsigned char)rank_pattern(pid); }
        FILE *f = fopen(argv[5], "wb"); fwrite(tab, 1, tot, f); fclose(f);
        printf("table of binary patterns (v=%d, r=%d, members %d): %llu patterns written to %s\n", v, r, m, (unsigned long long)tot, argv[5]);
        return 0;
    }
    load_up(argv[5], N / 2);
    char what[256];
    if (!strcmp(mode, "all")) {
        uint64_t tot = 1; for (int i = 0; i < N; i++) tot *= NB;
        for (uint64_t q = 0; q < tot; q++) { uint64_t t = q; for (int x = 0; x < N; x++) { pid[x] = t % NB; t /= NB; } test_one(pid); }
        snprintf(what, sizeof what, "all patterns (k=%d, n=%d, members %d)", K, N, m);
    } else if (!strcmp(mode, "rand")) {
        long count = atol(argv[6]); rng_seed(atol(argv[7])); make_code(v, r); int minw = atoi(argv[8]);
        const char *kind = argc > 9 ? argv[9] : "binary"; int cls[MAXB], ncls = 0, classonly = 0; (void)classonly;
        for (int id = 0; id < NB; id++) if (!strcmp(kind, "binary") || (!strcmp(kind, "graphic") && is_graphic[id]) || (!strcmp(kind, "class") && is_class[id])) cls[ncls++] = id;
        for (long it = 0; it < count;) { int w = 0; for (int x = 0; x < N; x++) { pid[x] = cls[rng_below(ncls)]; w += pdim[pid[x]]; } if (w < minw) continue; it++; test_one(pid); }
        snprintf(what, sizeof what, "random patterns (k=%d, n=%d, members %d, weight >= %d, %s, seed %s)", K, N, m, minw, kind, argv[7]);
    } else if (!strcmp(mode, "file")) {
        FILE *f = fopen(argv[6], "r"); char line[4096];
        while (fgets(line, sizeof line, f)) { char *s = strchr(line, '|'); s = s ? s + 1 : line; int x = 0; for (char *tok = strtok(s, " \n"); tok && x < N; tok = strtok(NULL, " \n")) pid[x++] = class_id(tok); if (x == N) test_one(pid); }
        fclose(f); snprintf(what, sizeof what, "file %s (k=%d, n=%d, members %d)", argv[6], K, N, m);
    }
    summary(what);
    return 0;
}
