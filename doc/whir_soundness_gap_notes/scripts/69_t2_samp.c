// Task 2, sampled: random and structured patterns at sizes beyond exhaustive reach, GF(2^64).
// usage: t2_samp v r L samples seed kinds deficient_out     (kinds[0] = U is the reference)
// Generators: 0 random leaves; 1..v-? unions of blocks at one level (level = generator index), with noise;
// 'P' sibling pairs split between classes; 'A' tree 0 in blocks, the other trees scattered; 'M' blocks of mixed levels.
#include "69_pat.h"
static int L, n, k, v, r, nclass; static uint8_t classes[64];
static uint8_t rclass(void) { return classes[1 + rng_below(nclass - 1)]; }
static void trim(uint8_t *cls, int target) { // drop or add single memberships until the weight is target
    for (int it = 0; it < 100000; it++) {
        int w = pat_weight(cls, n); if (w == target) return;
        int x = (int)rng_below(n);
        if (w > target && cls[x]) { int l; do l = (int)rng_below(L + 1); while (!((cls[x] >> l) & 1)); cls[x] &= (uint8_t)~(1 << l); if (__builtin_popcount(cls[x]) < 2) cls[x] = 0; }
        else if (w < target) { if (!cls[x]) cls[x] = rclass(); else cls[x] |= (uint8_t)(1 << rng_below(L + 1)); }
    }
}
static void gen(int g, uint8_t *cls) {
    memset(cls, 0, n);
    int target = L * k - 2 + (int)rng_below(5);
    if (g == 0) { trim(cls, target); return; }
    if (g >= 1 && g < 10) { // blocks at level g, a class or nothing per block, then at most 3 single-leaf edits
        int bs = 1 << g;
        for (int b = 0; b < n / bs; b++) { uint8_t c = rng_below(3) ? rclass() : 0; for (int x = 0; x < bs; x++) cls[b * bs + x] = c; }
        for (int e = (int)rng_below(4); e > 0; e--) { int x = (int)rng_below(n); cls[x] = rng_below(2) ? rclass() : 0; }
        if (rng_below(2)) trim(cls, target);
        return;
    }
    if (g == 'P') { for (int x = 0; x < n; x += 2) { if (rng_below(4) == 0) continue; cls[x] = rclass(); do cls[x + 1] = rclass(); while (cls[x + 1] == cls[x]); } if (rng_below(2)) trim(cls, target); return; }
    if (g == 'A') { // tree 0: blocks at a random level; other trees: scattered leaves
        int lev = 1 + (int)rng_below(v - 1), bs = 1 << lev;
        for (int b = 0; b < k / bs; b++) { uint8_t c = rng_below(4) ? rclass() : 0; for (int x = 0; x < bs; x++) cls[b * bs + x] = c; }
        trim(cls, target); // trim edits random leaves of all trees; tree 0 keeps most of its blocks
        return;
    }
    // 'M': recursive, each block either takes one class, nothing, or splits
    int stack[512], sp = 0; stack[sp++] = 0; stack[sp++] = n;
    while (sp) { int len = stack[--sp], o = stack[--sp];
        if (len > 1 && (len > k || rng_below(2))) { stack[sp++] = o; stack[sp++] = len / 2; stack[sp++] = o + len / 2; stack[sp++] = len / 2; continue; }
        uint8_t c = rng_below(3) ? rclass() : 0; for (int x = 0; x < len; x++) cls[o + x] = c; }
    if (rng_below(2)) trim(cls, target);
}
int main(int argc, char **argv) {
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); long samples = atol(argv[4]); rng_seed(strtoull(argv[5], 0, 10));
    const char *kinds = argv[6]; int nk = (int)strlen(kinds); FILE *fout = fopen(argv[7], "w"); gf_init(); n = 1 << (v + r); k = 1 << v;
    fe *G[8]; for (int c = 0; c < nk; c++) { G[c] = malloc(sizeof(fe) * n * k); code_gen(kinds[c], v, r, G[c]); }
    fe *M = malloc(sizeof(fe) * (size_t)(L * n + k) * L * k);
    classes[0] = 0; nclass = 1; for (int s = 1; s < (1 << (L + 1)); s++) if (__builtin_popcount(s) >= 2) classes[nclass++] = (uint8_t)s;
    int gens[16], ng = 0; gens[ng++] = 0; for (int i = 1; i < v; i++) gens[ng++] = i; gens[ng++] = 'P'; gens[ng++] = 'A'; gens[ng++] = 'M';
    uint8_t cls[MAXN];
    printf("v=%d r=%d k=%d n=%d members=%d samples per generator=%ld, weights near Lk=%d\n", v, r, k, n, L + 1, samples, L * k);
    for (int gi = 0; gi < ng; gi++) {
        long def[8] = {0}, feasnew[8] = {0}; int maxdef[8] = {0};
        for (long s = 0; s < samples; s++) {
            gen(gens[gi], cls);
            int rk[8], any = 0;
            for (int c = 0; c < nk; c++) { rk[c] = inc_rank(G[c], n, k, L, cls, -1, -1, M); int d = rk[0] - rk[c]; if (d > 0) { def[c]++; any = 1; if (d > maxdef[c]) maxdef[c] = d; } }
            if (!any) continue;
            int f0 = pat_feasible(G[0], n, k, L, cls, rk[0], M);
            for (int c = 1; c < nk; c++) if (rk[c] < rk[0] && !f0 && pat_feasible(G[c], n, k, L, cls, rk[c], M)) feasnew[c]++;
            fprintf(fout, "g=%d | ", gens[gi]); pat_print(fout, cls, n, L);
        }
        if (gens[gi] < 10) printf("generator %s%d:", gens[gi] ? "blocks at level " : "random leaves ", gens[gi]); else printf("generator %c:", gens[gi]);
        for (int c = 1; c < nk; c++) printf("  %c: deficient %ld (max %d), new lists %ld;", kinds[c], def[c], maxdef[c], feasnew[c]);
        printf("\n");
    }
    fclose(fout);
    return 0;
}
