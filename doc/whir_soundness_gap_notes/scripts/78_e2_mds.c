// Note 78, experiment 2: singular k x k minors of the variants over GF(2^64).
// usage: 78_e2_mds all  v r ndraws spec...          all C(n,k) minors, ndraws independent draws of each spec
//        78_e2_mds rand v r ndraws nsamp spec...    nsamp random minors per draw
//        78_e2_mds gl   v part nparts [list]        rate 1/2, every M in GL_v(F_2): all minors up to the child swaps of both
//                                                    trees; a singular minor is re-tested on 2 more twiddle draws
//        78_e2_mds canon v spec [part nparts]       rate 1/2, one V2 spec: all minors up to child swaps (3 draws for singular ones)
#include "78_var.h"
static int minor_singular(const fe *G, int k, const int *rows, fe *W) {
    for (int a = 0; a < k; a++) memcpy(W + (size_t)a * k, G + (size_t)rows[a] * k, sizeof(fe) * k);
    return gf_rank(W, k, k) < k;
}
static uint32_t *canon_sets(int v, long *cnt_out) { // subsets of a tree of 2^v leaves up to child swaps, as bitmasks
    long cnt = 2; uint32_t *c = malloc(sizeof(uint32_t) * 2); c[0] = 0; c[1] = 1;
    for (int s = 1; s < (1 << v); s *= 2) {
        long nc = cnt * (cnt + 1) / 2, o = 0; uint32_t *d = malloc(sizeof(uint32_t) * nc);
        for (long a = 0; a < cnt; a++) for (long b = a; b < cnt; b++) d[o++] = c[a] | (c[b] << s);
        free(c); c = d; cnt = nc;
    }
    *cnt_out = cnt; return c;
}
static void describe(const uint32_t *M, int v, char *out) { // structural flags of M
    uint32_t Inv[MAXV]; f2_inv(M, v, Inv);
    int perm = 1, lowpres = 0, highpres = 0, blockdiag = 0, upper = 1, lower = 1;
    for (int l = 0; l < v; l++) { perm &= (__builtin_popcount(M[l]) == 1); for (int j = 0; j < v; j++) if ((M[l] >> j) & 1) { if (j < l) upper = 0; if (j > l) lower = 0; } }
    for (int i = 1; i < v; i++) { // split at level i: low bits 0..i-1
        uint32_t lowmask = (1u << i) - 1; int lp = 1, hp = 1;
        for (int l = i; l < v; l++) if (M[l] & lowmask) lp = 0;           // M maps low bits to low bits
        for (int l = 0; l < i; l++) if (M[l] & ~lowmask) hp = 0;           // M maps high bits to high bits
        lowpres += lp; highpres += hp; blockdiag += (lp && hp);
    }
    sprintf(out, "top=(%d,%d) perm=%d tri=%s lowpres=%d highpres=%d blockdiag=%d", (int)((M[v - 1] >> (v - 1)) & 1), (int)((Inv[v - 1] >> (v - 1)) & 1), perm, upper && lower ? "id" : upper ? "U" : lower ? "L" : "-", lowpres, highpres, blockdiag);
}
int main(int argc, char **argv) {
    gf_init(); rng_seed(78002);
    if (!strcmp(argv[1], "all") || !strcmp(argv[1], "rand")) {
        int isall = !strcmp(argv[1], "all"), v = atoi(argv[2]), r = atoi(argv[3]), nd = atoi(argv[4]); long ns = isall ? 0 : atol(argv[5]);
        int n = 1 << (v + r), k = 1 << v; fe *W = malloc(sizeof(fe) * k * k);
        for (int a = isall ? 5 : 6; a < argc; a++) {
            long sing = 0, tot = 0, drawswith = 0;
            for (int dr = 0; dr < nd; dr++) {
                var_t V; if (!var_make(&V, argv[a], v, r)) { printf("bad spec %s\n", argv[a]); return 1; }
                int rows[64]; long s0 = sing;
                if (isall) {
                    for (int i = 0; i < k; i++) rows[i] = i;
                    for (;;) { sing += minor_singular(V.G, k, rows, W); tot++;
                        int i = k - 1; while (i >= 0 && rows[i] == n - k + i) i--; if (i < 0) break; rows[i]++; for (int j = i + 1; j < k; j++) rows[j] = rows[j - 1] + 1; }
                } else for (long s = 0; s < ns; s++) {
                    uint64_t used = 0; int c = 0; while (c < k) { int x = (int)rng_below((uint64_t)n); if ((used >> x) & 1) continue; used |= 1ull << x; rows[c++] = x; }
                    sing += minor_singular(V.G, k, rows, W); tot++;
                }
                drawswith += (sing > s0); var_free(&V);
            }
            printf("(k,n)=(%d,%d) %-14s %s minors: %ld singular of %ld (%d draws, %ld draws with a singular minor)\n", k, n, argv[a], isall ? "all" : "random", sing, tot, nd, drawswith);
            fflush(stdout);
        }
        return 0;
    }
    int isgl = !strcmp(argv[1], "gl"), v = atoi(argv[2]), k = 1 << v, n = 2 * k;
    long part = 0, nparts = 1; int list = 0; const char *onespec = 0;
    if (isgl) { part = atol(argv[3]); nparts = atol(argv[4]); list = argc > 5; } else { onespec = argv[3]; if (argc > 5) { part = atol(argv[4]); nparts = atol(argv[5]); } }
    long cnt; uint32_t *cs = canon_sets(v, &cnt); fe *W = malloc(sizeof(fe) * k * k);
    long npairs = 0; for (long a = 0; a < cnt; a++) for (long b = 0; b < cnt; b++) npairs += (__builtin_popcount(cs[a]) + __builtin_popcount(cs[b]) == k);
    long nM = 0, nMDS = 0, idx = 0; char spec[64], desc[160];
    long agg[2][2][2] = {{{0}}}, aggmds[2][2][2] = {{{0}}}; // by top flags and perm
    uint64_t lim = isgl ? (1ull << (v * v)) : 1;
    for (uint64_t code = 0; code < lim; code++) {
        uint32_t M[MAXV];
        if (isgl) { f2_unpack(code, v, M); if (!f2_inv(M, v, 0)) continue; if ((idx++ % nparts) != part) continue; sprintf(spec, "T2:M#%llu", (unsigned long long)code); }
        else strcpy(spec, onespec);
        var_t V[3]; for (int d = 0; d < 3; d++) if (!var_make(&V[d], spec, v, 1)) { printf("bad spec\n"); return 1; }
        memcpy(M, V[0].M[1], sizeof M);
        long sing = 0, ident = 0, done = 0; uint32_t ex0 = 0, ex1 = 0; int rows[64];
        for (long a = 0; a < cnt; a++) for (long b = 0; b < cnt; b++) {
            if (__builtin_popcount(cs[a]) + __builtin_popcount(cs[b]) != k) continue;
            if (!isgl && (done++ % nparts) != part) continue;
            int c = 0; for (int x = 0; x < k; x++) if ((cs[a] >> x) & 1) rows[c++] = x; for (int x = 0; x < k; x++) if ((cs[b] >> x) & 1) rows[c++] = k + x;
            if (!minor_singular(V[0].G, k, rows, W)) continue;
            sing++;
            if (minor_singular(V[1].G, k, rows, W) && minor_singular(V[2].G, k, rows, W)) { if (!ident) { ex0 = cs[a]; ex1 = cs[b]; } ident++; }
        }
        describe(M, v, desc); nM++; nMDS += (ident == 0);
        int f0 = (M[v - 1] >> (v - 1)) & 1, isperm = strstr(desc, "perm=1") != 0, f1 = strstr(desc, "top=(0,1)") || strstr(desc, "top=(1,1)");
        agg[f0][f1][isperm]++; if (!ident) aggmds[f0][f1][isperm]++;
        if (!isgl || list || ident == 0) {
            printf("M#%llu rows", (unsigned long long)f2_pack(M, v)); for (int l = 0; l < v; l++) { printf(" "); for (int j = v - 1; j >= 0; j--) printf("%d", (M[l] >> j) & 1); }
            printf(" | %s | canonical minors %ld, singular (draw 1) %ld, identically zero (3 draws) %ld", desc, isgl ? npairs : done, sing, ident);
            if (ident) printf(" e.g. tree0=%x tree1=%x", ex0, ex1);
            printf("\n"); fflush(stdout);
        }
        for (int d = 0; d < 3; d++) var_free(&V[d]);
    }
    if (isgl) {
        printf("# v=%d part %ld/%ld: matrices %ld, MDS on all canonical minors %ld; canonical minors per matrix %ld\n", v, part, nparts, nM, nMDS, npairs);
        for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++) for (int c = 0; c < 2; c++) if (agg[a][b][c]) printf("#   M[top,top]=%d Minv[top,top]=%d perm=%d: %ld matrices, %ld MDS\n", a, b, c, agg[a][b][c], aggmds[a][b][c]);
    }
    return 0;
}
