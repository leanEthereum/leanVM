// Task 2, exhaustive: rank of the incidence system of every pattern, for several codes over GF(2^64).
// usage: t2_exh v r L full|canon part nparts seed kinds deficient_out
// kinds: string over {U,2,1,R,S}; kinds[0] is the reference (use U). canon = one pattern per orbit of the tree automorphisms.
#include "69_pat.h"
#define MAXK 6
static int v, r, L, n, k, nk; static const char *kinds;
static fe *G[MAXK], *M;
static long hist[MAXK][64], nfeas[MAXK], nviol[MAXK], total; static int maxw[MAXK], maxa[MAXK];
static uint8_t bestw[MAXK][MAXN], besta[MAXK][MAXN];
static FILE *fout; static long nout; static int scan_all;

static void eval(const uint8_t *cls) {
    int rk[MAXK], w = pat_weight(cls, n), a = pat_balanced(cls, n, L);
    total++;
    for (int c = 0; c < nk; c++) {
        rk[c] = inc_rank(G[c], n, k, L, cls, -1, -1, M);
        int def = rk[0] - rk[c]; hist[c][def < 0 ? 63 : def]++;
        if (!scan_all && w <= maxw[c] && a <= maxa[c] && w < L * k) continue; // feasibility only where it can change a statistic
        if (pat_feasible(G[c], n, k, L, cls, rk[c], M)) {
            nfeas[c]++; if (w >= L * k) nviol[c]++;
            if (w > maxw[c]) { maxw[c] = w; memcpy(bestw[c], cls, n); }
            if (a > maxa[c]) { maxa[c] = a; memcpy(besta[c], cls, n); }
        }
    }
    int anydef = 0; for (int c = 1; c < nk; c++) anydef |= (rk[c] < rk[0]);
    if (anydef && nout < 300000) {
        nout++; fprintf(fout, "w=%d a=%d ranks", w, a);
        for (int c = 0; c < nk; c++) fprintf(fout, " %c=%d", kinds[c], rk[c]);
        fprintf(fout, " feas");
        for (int c = 0; c < nk; c++) fprintf(fout, " %c=%d", kinds[c], pat_feasible(G[c], n, k, L, cls, rk[c], M));
        fprintf(fout, " | "); pat_print(fout, cls, n, L);
    }
}
int main(int argc, char **argv) {
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); int full = !strcmp(argv[4], "full"); scan_all = full;
    long part = atol(argv[5]), nparts = atol(argv[6]); rng_seed(strtoull(argv[7], 0, 10)); kinds = argv[8]; nk = (int)strlen(kinds);
    fout = fopen(argv[9], "w"); gf_init(); n = 1 << (v + r); k = 1 << v;
    for (int c = 0; c < nk; c++) { G[c] = malloc(sizeof(fe) * n * k); code_gen(kinds[c], v, r, G[c]); }
    M = malloc(sizeof(fe) * (size_t)(L * n + k) * L * k);
    uint8_t classes[64]; int C = 0; classes[C++] = 0;
    for (int s = 1; s < (1 << (L + 1)); s++) if (__builtin_popcount(s) >= 2) classes[C++] = (uint8_t)s;
    uint8_t cls[MAXN];
    if (full) {
        int dig[MAXN] = {0};
        for (;;) {
            for (int x = 0; x < n; x++) cls[x] = classes[dig[x]];
            eval(cls);
            int x = 0; while (x < n && ++dig[x] == C) dig[x++] = 0;
            if (x == n) break;
        }
    } else {
        uint8_t *canon = malloc(C); long cnt = C; memcpy(canon, classes, C);
        for (int s = 1; s < n / 2; s *= 2) { // canon: cnt patterns of s leaves -> cnt(cnt+1)/2 patterns of 2s leaves
            long ncnt = cnt * (cnt + 1) / 2, o = 0; uint8_t *nc = malloc((size_t)ncnt * 2 * s);
            for (long a = 0; a < cnt; a++) for (long b = a; b < cnt; b++, o++) { memcpy(nc + o * 2 * s, canon + a * s, s); memcpy(nc + o * 2 * s + s, canon + b * s, s); }
            free(canon); canon = nc; cnt = ncnt;
        }
        int h = n / 2;
        for (long a = part; a < cnt; a += nparts) for (long b = a; b < cnt; b++) { memcpy(cls, canon + a * h, h); memcpy(cls + h, canon + b * h, h); eval(cls); }
    }
    printf("v=%d r=%d k=%d n=%d members=%d mode=%s part=%ld/%ld patterns=%ld  Lk=%d\n", v, r, k, n, L + 1, argv[4], part, nparts, total, L * k);
    for (int c = 0; c < nk; c++) {
        printf("code %c: feasible=%ld feasible_with_weight>=Lk=%ld max_weight=%d max_balanced=%d  deficiency_hist:", kinds[c], nfeas[c], nviol[c], maxw[c], maxa[c]);
        for (int d = 0; d < 64; d++) if (hist[c][d]) printf(" %d:%ld", d == 63 ? -1 : d, hist[c][d]);
        printf("\n  max-weight example: "); pat_print(stdout, bestw[c], n, L);
        printf("  max-balanced example: "); pat_print(stdout, besta[c], n, L);
    }
    fclose(fout);
    return 0;
}
