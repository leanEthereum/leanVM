// Note 82: (C') at sizes where the table of upper ranks is too large. Upper ranks are computed on demand (cached),
// and the upper pattern Q is found (a) as the binary full part Q*: Q*_p = all binary theta with theta (x) g_p (x) F^2 inside R,
// read off the kernel of the system; (b) by coordinate descent on B(P;Q) from Q*, from the sibling join and from 0.
// B >= rank always, so B = rank certifies (C') on the instance; B > rank after the search is only a failed search.
// Build: cc -O2 -o 82_bin/82_big 82_big.c
//   rand v r m count seed minw kind(class|graphic|binary)
//   pert v r m count seed minw kind nflip
//   file v r m patterns.txt [lift]     lift: every leaf of the file's pattern becomes a bottom pair with the same class (v is the lifted depth)
#define FB 64
#include "69_gf.h"
#define MAXM 6
#define MAXB 400
#define MAXN 64
static int m, L, NB;
static uint32_t smask[MAXB];
static int jointab[MAXB][MAXB], pdim[MAXB], nbas[MAXB], basV[MAXB][MAXM], is_graphic[MAXB], is_class[MAXB];
static uint32_t span_add(uint32_t s, int v) { uint32_t out = s; for (int u = 0; u < (1 << L); u++) if ((s >> u) & 1) out |= 1u << (u ^ v); return out; }
static int find_mask(uint32_t s) { for (int i = 0; i < NB; i++) if (smask[i] == s) return i; return -1; }
static int memvec(int a) { return a ? 1 << (a - 1) : 0; }
static void gen_subspaces(void) {
    NB = 0; smask[NB++] = 1u;
    for (int i = 0; i < NB; i++) for (int v = 1; v < (1 << L); v++) { if ((smask[i] >> v) & 1) continue; uint32_t s = span_add(smask[i], v); if (find_mask(s) < 0) smask[NB++] = s; }
    for (int i = 0; i < NB; i++) { uint32_t cur = 1u; nbas[i] = 0; for (int v = 1; v < (1 << L); v++) if (((smask[i] >> v) & 1) && !((cur >> v) & 1)) { basV[i][nbas[i]++] = v; cur = span_add(cur, v); } pdim[i] = nbas[i]; }
    for (int a = 0; a < NB; a++) for (int b = 0; b < NB; b++) { uint32_t s = smask[a]; for (int j = 0; j < nbas[b]; j++) s = span_add(s, basV[b][j]); jointab[a][b] = find_mask(s); }
    for (int i = 0; i < NB; i++) {
        uint32_t s = 1u; int par[MAXM]; for (int a = 0; a < m; a++) par[a] = a;
        for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) { int v = memvec(a) ^ memvec(b); if ((smask[i] >> v) & 1) { s = span_add(s, v); int x = a, y = b; while (par[x] != x) x = par[x]; while (par[y] != y) y = par[y]; if (x != y) par[y] = x; } }
        is_graphic[i] = s == smask[i];
        int big = 0; for (int a = 0; a < m; a++) { int c = 0; for (int b = 0; b < m; b++) { int y = b; while (par[y] != y) y = par[y]; c += y == a; } big += c >= 2; }
        is_class[i] = is_graphic[i] && big <= 1;
    }
}
static int class_id(const char *tok) {
    uint32_t s = 1u; if (tok[0] == '.') return 0; int first = -1;
    for (const char *c = tok; *c; c++) { if (*c == '/') { first = -1; continue; } int a = *c - '0'; if (first < 0) first = a; else s = span_add(s, memvec(first) ^ memvec(a)); }
    return find_mask(s);
}
typedef struct { int N, K; fe G[MAXN][MAXN]; } code_t;
static code_t lo, hi; // the code and the code one layer up (the same upper twiddles)
static void make_codes(int v, int r) {
    static fe tw[16][MAXN];
    lo.N = 1 << (v + r); lo.K = 1 << v; hi.N = lo.N / 2; hi.K = lo.K / 2;
    for (int i = 0; i < v; i++) for (int q = 0; q < (lo.N >> i); q++) tw[i][q] = gf_rand();
    for (int j = 0; j < lo.N; j++) { lo.G[j][0] = 1; for (int i = 0; i < v; i++) { fe x = tw[i][j >> i]; for (int e = 0; e < (1 << i); e++) lo.G[j][e | (1 << i)] = gf_mul(lo.G[j][e], x); } }
    for (int p = 0; p < hi.N; p++) for (int e = 0; e < hi.K; e++) hi.G[p][e] = lo.G[2 * p][2 * e];
}
static fe M[MAXN * MAXM][MAXN * MAXM]; static int pivcol[MAXN * MAXM];
static int rank_pattern(const code_t *C, const int *pid, int reduce) { // reduce = 1: reduced row echelon form, pivots in pivcol
    int cols = L * C->K, rows = 0, K = C->K;
    for (int x = 0; x < C->N; x++) for (int b = 0; b < nbas[pid[x]]; b++) { fe *row = M[rows++]; memset(row, 0, sizeof(fe) * cols); int vec = basV[pid[x]][b]; for (int a = 0; a < L; a++) if ((vec >> a) & 1) memcpy(row + a * K, C->G[x], sizeof(fe) * K); }
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
// ---- cache of upper ranks
#define HSIZE (1u << 22)
typedef unsigned __int128 u128;
static u128 hkey[HSIZE]; static signed char hval[HSIZE]; static int digbits; static long nup;
static int uprank(const int *q) {
    u128 key = 0;
    if (digbits * hi.N <= 127) { for (int p = 0; p < hi.N; p++) key = (key << digbits) | (u128)q[p]; key += 1; }
    else { const u128 mul = ((u128)0x9E3779B97F4A7C15ull << 64) | 0xF39CC0605CEDC835ull; for (int p = 0; p < hi.N; p++) key = (key + (u128)(q[p] + 1)) * mul; key |= 1; } // 128-bit fingerprint for long patterns
    uint64_t kk = (uint64_t)key ^ ((uint64_t)(key >> 64) * 0xD6E8FEB86659FD93ull);
    uint32_t h = (uint32_t)((kk * 0x9E3779B97F4A7C15ull) >> 42);
    while (hkey[h] && hkey[h] != key) h = (h + 1) & (HSIZE - 1);
    if (hkey[h] == key) return hval[h];
    if (nup > (long)(HSIZE * 0.7)) { memset(hkey, 0, sizeof hkey); nup = 0; h = (uint32_t)((kk * 0x9E3779B97F4A7C15ull) >> 42); }
    int rk = rank_pattern(&hi, q, 0); hkey[h] = key; hval[h] = (signed char)rk; nup++; return rk;
}
static int bound(const int *pid, int *q) {
    int base = uprank(q), s = 2 * base;
    for (int x = 0; x < lo.N; x++) { int p = x >> 1, d = q[p], nd = jointab[d][pid[x]]; if (nd != d) { q[p] = nd; s += uprank(q) - base; q[p] = d; } }
    return s;
}
static int descend(const int *pid, int *q, int target) {
    int cur = bound(pid, q), improved = 1;
    while (improved && cur > target) { improved = 0;
        for (int p = 0; p < hi.N && cur > target; p++) { int keep = q[p], bestd = keep;
            for (int d = 0; d < NB; d++) { if (d == keep) continue; q[p] = d; int b = bound(pid, q); if (b < cur) { cur = b; bestd = d; improved = 1; } }
            q[p] = bestd; } }
    return cur;
}
static void full_part(const int *pid, int rk, int *q) { // Q*: needs the reduced echelon form of the system
    int cols = L * lo.K, K = lo.K, d = cols - rk;
    static fe ker[MAXN * MAXM][MAXN * MAXM]; int ispiv[MAXN * MAXM] = {0};
    rank_pattern(&lo, pid, 1); for (int i = 0; i < rk; i++) ispiv[pivcol[i]] = 1;
    int kd = 0; for (int c = 0; c < cols; c++) { if (ispiv[c]) continue; memset(ker[kd], 0, sizeof(fe) * cols); ker[kd][c] = 1; for (int i = 0; i < rk; i++) ker[kd][pivcol[i]] = M[i][c]; kd++; }
    (void)d;
    for (int p = 0; p < hi.N; p++) { uint32_t s = 1u;
        for (int v = 1; v < (1 << L); v++) { int ok = 1;
            for (int i = 0; i < kd && ok; i++) for (int b = 0; b < 2 && ok; b++) { fe acc = 0; for (int a = 0; a < L; a++) if ((v >> a) & 1) for (int e = 0; e < K / 2; e++) acc ^= gf_mul(ker[i][a * K + 2 * e + b], hi.G[p][e]); if (acc) ok = 0; }
            if (ok) s |= 1u << v; }
        q[p] = find_mask(s); }
}
static void print_pat(const int *pid, int n) {
    for (int x = 0; x < n; x++) { int id = pid[x]; if (!nbas[id]) printf(".");
        for (int b = 0; b < nbas[id]; b++) { int v = basV[id][b]; if (b) printf("+"); if (__builtin_popcount(v) & 1) printf("0"); for (int a = 1; a < m; a++) if ((v >> (a - 1)) & 1) printf("%d", a); }
        printf(" "); }
}
static long c_tot, c_dep, c_star, c_desc, c_open, c_below;
static void test_one(const int *pid) {
    int w = 0, q[MAXN]; for (int x = 0; x < lo.N; x++) w += pdim[pid[x]];
    int rk = rank_pattern(&lo, pid, 0); c_tot++; c_dep += rk < w;
    full_part(pid, rk, q); int b = bound(pid, q), best = b;
    if (getenv("VERBOSE")) { int wq = 0; for (int p = 0; p < hi.N; p++) wq += pdim[q[p]]; printf("w %d, L*k %d, rank %d, B(P;Q*) %d, weight of Q* %d, rank of Q* %d; Q* = ", w, L * lo.K, rk, b, wq, uprank(q)); print_pat(q, hi.N); printf("\n"); }
    if (b == rk) { c_star++; return; }
    if (b < rk) { c_below++; printf("BELOW (bug): rank %d B %d\n", rk, b); return; }
    for (int start = 0; start < 3 && best > rk; start++) {
        if (start == 0) full_part(pid, rk, q); else for (int p = 0; p < hi.N; p++) q[p] = start == 1 ? jointab[pid[2 * p]][pid[2 * p + 1]] : 0;
        int d = descend(pid, q, rk); if (d < best) best = d; }
    if (best == rk) { c_desc++; return; }
    if (best < rk) { c_below++; return; }
    c_open++; if (c_open <= 20) { printf("OPEN rank %d w %d best B found %d (B at Q* %d): ", rk, w, best, b); print_pat(pid, lo.N); printf("\n"); fflush(stdout); }
}
int main(int argc, char **argv) {
    const char *mode = argv[1]; int v = atoi(argv[2]), r = atoi(argv[3]); m = atoi(argv[4]); L = m - 1;
    gen_subspaces(); digbits = 1; while ((1 << digbits) < NB) digbits++;
    
    int pid[MAXN]; char what[300];
    if (!strcmp(mode, "rand")) {
        long count = atol(argv[5]); rng_seed(atol(argv[6])); make_codes(v, r); int minw = atoi(argv[7]); const char *kind = argv[8]; int cls[MAXB], ncls = 0;
        for (int id = 0; id < NB; id++) if (!strcmp(kind, "binary") || (!strcmp(kind, "graphic") && is_graphic[id]) || (!strcmp(kind, "class") && is_class[id])) cls[ncls++] = id;
        for (long it = 0; it < count;) { int w = 0; for (int x = 0; x < lo.N; x++) { pid[x] = cls[rng_below(ncls)]; w += pdim[pid[x]]; } if (w < minw) continue; it++; test_one(pid); }
        snprintf(what, sizeof what, "random %s patterns (k=%d, n=%d, members %d, weight >= %d, seed %s)", kind, lo.K, lo.N, m, minw, argv[6]);
    } else if (!strcmp(mode, "pert")) { // a random pattern one layer up, every leaf doubled, then nflip leaves redrawn
        long count = atol(argv[5]); rng_seed(atol(argv[6])); make_codes(v, r); int minw = atoi(argv[7]); const char *kind = argv[8]; int nflip = atoi(argv[9]), cls[MAXB], ncls = 0;
        for (int id = 0; id < NB; id++) if (!strcmp(kind, "binary") || (!strcmp(kind, "graphic") && is_graphic[id]) || (!strcmp(kind, "class") && is_class[id])) cls[ncls++] = id;
        for (long it = 0; it < count;) { int w = 0; for (int p = 0; p < hi.N; p++) pid[2 * p] = pid[2 * p + 1] = cls[rng_below(ncls)];
            for (int f = 0; f < nflip; f++) pid[rng_below(lo.N)] = cls[rng_below(ncls)];
            for (int x = 0; x < lo.N; x++) w += pdim[pid[x]]; if (w < minw) continue; it++; test_one(pid); }
        snprintf(what, sizeof what, "doubled random %s patterns with %d leaves redrawn (k=%d, n=%d, members %d, weight >= %d, seed %s)", kind, nflip, lo.K, lo.N, m, minw, argv[6]);
    } else {
        rng_seed(82); make_codes(v, r); int lift = argc > 6; FILE *f = fopen(argv[5], "r"); char line[4096]; int n0 = lift ? lo.N / 2 : lo.N, tmp[MAXN];
        while (fgets(line, sizeof line, f)) { char *s = strchr(line, '|'); s = s ? s + 1 : line; int x = 0; for (char *tok = strtok(s, " \n"); tok && x < n0; tok = strtok(NULL, " \n")) tmp[x++] = class_id(tok); if (x != n0) continue;
            for (int y = 0; y < lo.N; y++) pid[y] = lift ? tmp[y / 2] : tmp[y]; test_one(pid); }
        fclose(f); snprintf(what, sizeof what, "file %s%s (k=%d, n=%d, members %d)", argv[5], lift ? ", every leaf doubled" : "", lo.K, lo.N, m);
    }
    printf("%s: patterns %ld, rows dependent %ld, B(P;Q*) = rank %ld, B = rank after descent %ld, not certified %ld, below (bug) %ld\n", what, c_tot, c_dep, c_star, c_desc, c_open, c_below);
    return 0;
}
