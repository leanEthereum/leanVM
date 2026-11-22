// Note 78, experiment 3: rank of the incidence system of patterns for several codes over GF(2^64); spec[0] is the reference (U).
// usage: 78_e3_scan mode v r L part nparts seed deficient_out spec0 spec1 ...
// mode: full        every pattern, one per orbit of the relabelings of the members (valid for every code); counts are
//                   reported both in orbits and in patterns
//       trees       one pattern per orbit of the child swaps inside each tree, every ordered tuple of trees (valid for U, T2, V2)
//       sample:N    N random patterns per generator (generators 0..5, see gen()); the partner maps of the first V1 spec are used
//       file:PATH   the patterns of a file (lines "... | c c c" or "c c c")
#include "69_pat.h"
#include "78_var.h"
#define MAXK 16
static int v, r, L, n, k, nk; static char **specs; static var_t V[MAXK]; static fe *M;
static long hist[MAXK][8], horb[MAXK][8], nfeas[MAXK], nviol[MAXK], ndeflist[MAXK], total, totorb; static int maxw[MAXK], maxa[MAXK], maxdw[MAXK];
static uint8_t bestw[MAXK][MAXN], besta[MAXK][MAXN];
static FILE *fout; static long nout; static int tgt = -1;
static void eval(const uint8_t *cls, long mult) {
    int rk[MAXK], w = pat_weight(cls, n), a = pat_balanced(cls, n, L);
    total += mult; totorb++;
    int anydef = 0;
    for (int c = 0; c < nk; c++) {
        rk[c] = inc_rank(V[c].G, n, k, L, cls, -1, -1, M);
        int def = rk[0] - rk[c]; if (def < 0) def = 7; if (def > 6) def = 6 + (def == 7);
        hist[c][def] += mult; horb[c][def]++;
        int isdef = rk[c] < rk[0]; anydef |= isdef;
        if (!isdef && w <= maxw[c] && a <= maxa[c] && w < L * k) continue;
        if (pat_feasible(V[c].G, n, k, L, cls, rk[c], M)) {
            nfeas[c]++; if (w >= L * k) nviol[c] += mult;
            if (isdef) { ndeflist[c] += mult; if (w > maxdw[c]) maxdw[c] = w; }
            if (w > maxw[c]) { maxw[c] = w; memcpy(bestw[c], cls, n); }
            if (a > maxa[c]) { maxa[c] = a; memcpy(besta[c], cls, n); }
        }
    }
    if (anydef && nout < 200000) {
        nout++; fprintf(fout, "w=%d a=%d mult=%ld ranks", w, a, mult);
        for (int c = 0; c < nk; c++) fprintf(fout, " %s=%d", specs[c], rk[c]);
        fprintf(fout, " | "); pat_print(fout, cls, n, L);
    }
}
static uint8_t randclass(int minsz) { uint8_t c = 0; int sz = minsz + (int)rng_below((uint64_t)(L + 2 - minsz)); while (__builtin_popcount(c) < sz) c |= (uint8_t)(1 << rng_below(L + 1)); return c; }
static void trim_to(uint8_t *cls, int wmax) { // drop random memberships until the weight is at most wmax
    while (pat_weight(cls, n) > wmax) { int x; do x = (int)rng_below(n); while (!cls[x]); int l; do l = (int)rng_below(L + 1); while (!((cls[x] >> l) & 1)); cls[x] &= (uint8_t)~(1 << l); if (__builtin_popcount(cls[x]) < 2) cls[x] = 0; }
}
static void gen(int g, uint8_t *cls) {
    memset(cls, 0, n);
    int target = L * k - 2 + (int)rng_below(5);
    if (g == 0) { // random leaves, random classes, weight within 2 of Lk
        while (pat_weight(cls, n) < target) { int x = (int)rng_below(n); cls[x] = randclass(2); }
        trim_to(cls, target);
    } else if (g == 1 || g == 2) { // unions of blocks at one level (g=1) or mixed levels (g=2), then up to 3 edited leaves
        int lev = 1 + (int)rng_below(v + r - 1);
        for (int x = 0; x < n;) { int lv = g == 1 ? lev : (int)rng_below(v + r); int bs = 1 << lv; while (x % bs) bs >>= 1; uint8_t c = rng_below(4) ? randclass(2) : 0; for (int y = 0; y < bs && x < n; y++) cls[x++] = c; }
        int ed = (int)rng_below(4); for (int e = 0; e < ed; e++) { int x = (int)rng_below(n); cls[x] = rng_below(2) ? randclass(2) : 0; }
        if (rng_below(2)) trim_to(cls, target);
    } else if (g == 3) { // tree 0 in blocks, the other trees scattered
        int bs = 1 << (1 + (int)rng_below(v - 1));
        for (int b = 0; b < k / bs; b++) { uint8_t c = rng_below(4) ? randclass(2) : 0; for (int y = 0; y < bs; y++) cls[b * bs + y] = c; }
        int cap = pat_weight(cls, n) + (n - k) * L; if (target > cap) target = cap; // the scattered trees can add at most L per leaf
        for (int guard = 0; pat_weight(cls, n) < target && guard < 100000; guard++) { int x = k + (int)rng_below(n - k); cls[x] = randclass(2); }
        trim_to(cls, target);
    } else if (g == 4 && tgt >= 0) { // classes constant along runs of the first partner map
        while (pat_weight(cls, n) < target) { int x = (int)rng_below(n), len = 1 + (int)rng_below(6); uint8_t c = randclass(2); for (int i = 0; i < len; i++) { cls[x] = c; x = V[tgt].pi[0][x]; } }
        trim_to(cls, target + 2);
    } else if (g == 5 && tgt >= 0) { // the V1 image of a block pattern: class(x) = intersection of the block classes at x and its partners
        uint8_t blk[MAXN]; int lev = 1 + (int)rng_below(v + r - 1), bs = 1 << lev;
        for (int b = 0; b < n / bs; b++) { uint8_t c = rng_below(5) ? randclass(2) : 0; for (int y = 0; y < bs; y++) blk[b * bs + y] = c; }
        int nz = (int)rng_below(bs); for (int e = 0; e < nz; e++) blk[rng_below(n)] = (uint8_t)((1 << (L + 1)) - 1);
        for (int x = 0; x < n; x++) { uint8_t c = blk[x]; for (int a = 0; a < V[tgt].d; a++) c &= blk[V[tgt].pi[a][x]]; cls[x] = __builtin_popcount(c) >= 2 ? c : 0; }
    } else gen(0, cls);
}
static int parse_pattern(const char *line, uint8_t *cls) {
    const char *p = strstr(line, " | "); p = p ? p + 3 : line; int x = 0;
    while (*p && x < n) { while (*p == ' ') p++; if (!*p || *p == '\n') break; uint8_t c = 0;
        while (*p && *p != ' ' && *p != '\n') { if (*p >= '0' && *p <= '9') c |= (uint8_t)(1 << (*p - '0')); p++; } cls[x++] = c; }
    return x == n;
}
static void report(const char *tag) {
    printf("%s v=%d r=%d k=%d n=%d members=%d patterns=%ld (evaluated %ld) Lk-1=%d\n", tag, v, r, k, n, L + 1, total, totorb, L * k - 1);
    for (int c = 0; c < nk; c++) {
        long def = 0, deforb = 0; int maxdef = 0; for (int d = 1; d < 7; d++) if (hist[c][d]) { def += hist[c][d]; deforb += horb[c][d]; maxdef = d; }
        printf("  %-16s deficient patterns %ld (evaluated %ld), largest deficiency %d, rank above U %ld | deficient and carrying a list %ld (largest weight %d) | lists with weight >= Lk: %ld | largest weight of a list %d, largest balanced agreement %d\n",
               specs[c], def, deforb, maxdef, hist[c][7], ndeflist[c], maxdw[c], nviol[c], maxw[c], maxa[c]);
        if (c && (def || maxw[c] > L * k - 1)) { printf("     max-weight list: "); pat_print(stdout, bestw[c], n, L); }
    }
    memset(hist, 0, sizeof hist); memset(horb, 0, sizeof horb); memset(nfeas, 0, sizeof nfeas); memset(nviol, 0, sizeof nviol); memset(ndeflist, 0, sizeof ndeflist);
    memset(maxw, 0, sizeof maxw); memset(maxa, 0, sizeof maxa); memset(maxdw, 0, sizeof maxdw); total = totorb = 0;
}
int main(int argc, char **argv) {
    const char *mode = argv[1]; v = atoi(argv[2]); r = atoi(argv[3]); L = atoi(argv[4]);
    long part = atol(argv[5]), nparts = atol(argv[6]); uint64_t seed = strtoull(argv[7], 0, 10);
    fout = fopen(argv[8], "w"); specs = argv + 9; nk = argc - 9; gf_init(); n = 1 << (v + r); k = 1 << v;
    rng_seed(seed); // the codes depend on the seed only, not on the part
    for (int c = 0; c < nk; c++) { if (!var_make(&V[c], specs[c], v, r)) { printf("bad spec %s\n", specs[c]); return 1; } if (tgt < 0 && V[c].d) tgt = c; }
    for (int c = 0; c < nk; c++) if (V[c].d) { printf("# %s partner map 1:", specs[c]); for (int x = 0; x < n && n <= 32; x++) printf(" %d", V[c].pi[0][x]); printf("\n"); }
    M = malloc(sizeof(fe) * (size_t)(L * n + k) * L * k);
    uint8_t classes[64]; int C = 0; classes[C++] = 0;
    for (int s = 1; s < (1 << (L + 1)); s++) if (__builtin_popcount(s) >= 2) classes[C++] = (uint8_t)s;
    uint8_t cls[MAXN];
    if (!strcmp(mode, "full")) {
        int nperm = 1; for (int i = 2; i <= L + 1; i++) nperm *= i;
        int (*sig)[64] = malloc(sizeof(int[64]) * nperm), idxof[256]; for (int c = 0; c < C; c++) idxof[classes[c]] = c;
        int p[8]; for (int i = 0; i <= L; i++) p[i] = i;
        for (int t = 0; t < nperm; t++) { // all permutations of the members (Heap-free: next_permutation)
            for (int c = 0; c < C; c++) { uint8_t m = 0; for (int l = 0; l <= L; l++) if ((classes[c] >> l) & 1) m |= (uint8_t)(1 << p[l]); sig[t][c] = idxof[m]; }
            int i = L - 1; while (i >= 0 && p[i] > p[i + 1]) i--; if (i < 0) break; int j = L; while (p[j] < p[i]) j--; int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            for (int a = i + 1, b = L; a < b; a++, b--) { tmp = p[a]; p[a] = p[b]; p[b] = tmp; }
        }
        int dig[MAXN] = {0}; long hi = 0;
        for (;;) {
            if (hi % nparts == part) {
                int canon = 1, stab = 0;
                for (int t = 0; t < nperm && canon; t++) { int cmp = 0; for (int x = n - 1; x >= 0 && !cmp; x--) cmp = sig[t][dig[x]] - dig[x]; if (cmp < 0) canon = 0; stab += (cmp == 0); }
                if (canon) { for (int x = 0; x < n; x++) cls[x] = classes[dig[x]]; eval(cls, nperm / stab); }
            }
            int x = 0; while (x < n && ++dig[x] == C) dig[x++] = 0;
            if (x == n) break;
            if (x >= n - 2) hi++;
        }
    } else if (!strcmp(mode, "trees")) {
        uint8_t *canon = malloc(C); long cnt = C; memcpy(canon, classes, C);
        for (int s = 1; s < k; s *= 2) {
            long ncnt = cnt * (cnt + 1) / 2, o = 0; uint8_t *nc = malloc((size_t)ncnt * 2 * s);
            for (long a = 0; a < cnt; a++) for (long b = a; b < cnt; b++, o++) { memcpy(nc + o * 2 * s, canon + a * s, s); memcpy(nc + o * 2 * s + s, canon + b * s, s); }
            free(canon); canon = nc; cnt = ncnt;
        }
        int nt = 1 << r; long idx[16] = {0};
        for (idx[0] = part; idx[0] < cnt; idx[0] += nparts) {
            for (int t = 1; t < nt; t++) idx[t] = 0;
            for (;;) {
                for (int t = 0; t < nt; t++) memcpy(cls + t * k, canon + idx[t] * k, k);
                eval(cls, 1);
                int t = nt - 1; while (t >= 1 && ++idx[t] == cnt) idx[t--] = 0;
                if (t < 1) break;
            }
        }
    } else if (!strncmp(mode, "sample:", 7)) {
        long N = atol(mode + 7); rng_seed(seed * 1000 + 17 + (uint64_t)part);
        static const char *gname[6] = {"g0 random leaves, weight within 2 of Lk", "g1 unions of blocks at one level, up to 3 edits", "g2 blocks of mixed levels", "g3 tree 0 in blocks, the rest scattered", "g4 classes constant along runs of the first partner map", "g5 V1 image of a block pattern with zeros"};
        for (int g = 0; g < 6; g++) { if (g >= 4 && tgt < 0) break; for (long s = 0; s < N; s++) { gen(g, cls); eval(cls, 1); } report(gname[g]); }
        fclose(fout); return 0;
    } else if (!strncmp(mode, "file:", 5)) {
        FILE *f = fopen(mode + 5, "r"); char line[8192];
        while (f && fgets(line, sizeof line, f)) if (parse_pattern(line, cls)) eval(cls, 1);
    }
    char tag[64]; sprintf(tag, "%s part %ld/%ld", mode, part, nparts); report(tag);
    fclose(fout);
    return 0;
}
