// Referee 80: independent checks of note 76's exact list sizes (generic T2 tree code, rate 1/2, GF(2^64)).
//   80_lists n8 <seed>            exhaustive, by incidence systems (not the secant form): every family of four or five 5-subsets
//                                 of the 8 leaves with pairwise intersections <= 3; which of them carry a list of distinct codewords
//   80_lists n16 <seed> <file>    for every five-member pattern of 76_tmp/n16_orbits5.txt: the incidence system has a list; a word
//                                 is rebuilt from a kernel point and ALL codewords at agreement >= 10 with it are enumerated by
//                                 interpolation through every 8-subset (12870 of them): are there exactly five
#include "80_gf.h"
static tree_t T;
static int n, k;
static int has_list(const fe *Kb, int dim, int L) {
    if (dim == 0) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) {
        int ok = 0;
        for (int d = 0; d < dim && !ok; d++) for (int e = 0; e < k && !ok; e++) {
            fe val = Kb[(size_t)d * L * k + (size_t)(b - 1) * k + e];
            if (a >= 1) val ^= Kb[(size_t)d * L * k + (size_t)(a - 1) * k + e];
            if (val) ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}
static int carries(const unsigned *sets, int m, fe *M, fe *Kb, int *dimout) { // sets[l] = agreement set of member l (bitmask of leaves)
    unsigned cls[32];
    for (int x = 0; x < n; x++) { cls[x] = 0; for (int l = 0; l < m; l++) if ((sets[l] >> x) & 1) cls[x] |= 1u << l; }
    int L = m - 1, w = pat_matrix(&T, cls, L, M);
    int dim = fe_kernel(M, w, L * k, Kb);
    if (dimout) *dimout = dim;
    return has_list(Kb, dim, L);
}
static int main_n8(uint64_t seed) {
    rnd_seed(seed); fe_selftest(); tree_init(&T, 2, 2, 2); n = T.n; k = T.k;
    unsigned S5[56]; int ns = 0;
    for (unsigned m = 0; m < 256; m++) if (popc(m) == 5) S5[ns++] = m;
    fe *M = malloc(sizeof(fe) * 64 * 16), *Kb = malloc(sizeof(fe) * 16 * 16);
    long n3 = 0, l3 = 0, n4 = 0, l4 = 0, n5 = 0, l5 = 0; unsigned st[5];
    for (int a = 0; a < ns; a++) for (int b = a + 1; b < ns; b++) {
        if (popc(S5[a] & S5[b]) > 3) continue;
        for (int c = b + 1; c < ns; c++) {
            if (popc(S5[a] & S5[c]) > 3 || popc(S5[b] & S5[c]) > 3) continue;
            st[0] = S5[a]; st[1] = S5[b]; st[2] = S5[c]; n3++;
            if (!carries(st, 3, M, Kb, NULL)) continue;
            l3++;
            for (int d = c + 1; d < ns; d++) {
                if (popc(S5[a] & S5[d]) > 3 || popc(S5[b] & S5[d]) > 3 || popc(S5[c] & S5[d]) > 3) continue;
                st[3] = S5[d]; n4++;
                if (!carries(st, 4, M, Kb, NULL)) continue;
                l4++;
                if (l4 == 1) printf("  first four-member list: agreement sets %02x %02x %02x %02x\n", st[0], st[1], st[2], st[3]);
                for (int e = d + 1; e < ns; e++) {
                    if (popc(S5[a] & S5[e]) > 3 || popc(S5[b] & S5[e]) > 3 || popc(S5[c] & S5[e]) > 3 || popc(S5[d] & S5[e]) > 3) continue;
                    st[4] = S5[e]; n5++;
                    if (carries(st, 5, M, Kb, NULL)) { l5++; if (l5 <= 3) printf("  FIVE-member list: %02x %02x %02x %02x %02x\n", st[0], st[1], st[2], st[3], st[4]); }
                }
            }
        }
    }
    printf("n = 8, agreement 5, seed %llu: triples of 5-sets tested %ld (with a list %ld); quadruples extending them %ld (with a list %ld); quintuples extending those %ld (with a list %ld)\n",
           (unsigned long long)seed, n3, l3, n4, l4, n5, l5);
    return 0;
}
static int main_n16(uint64_t seed, const char *file) {
    rnd_seed(seed); fe_selftest(); tree_init(&T, 3, 2, 2); n = T.n; k = T.k;
    FILE *f = fopen(file, "r"); if (!f) { printf("cannot open %s\n", file); return 1; }
    char line[4096]; int L = 4, npat = 0, ok5 = 0, bad = 0, dimhist[8] = {0};
    fe *M = malloc(sizeof(fe) * 80 * 32), *Kb = malloc(sizeof(fe) * 32 * 32), *c[5], *u = malloc(sizeof(fe) * 16), *cand = malloc(sizeof(fe) * 16);
    for (int l = 0; l < 5; l++) c[l] = calloc(16, sizeof(fe));
    fe Sys[8 * 9], msg[8]; int pc[9];
    while (fgets(line, sizeof line, f)) {
        char *p = strstr(line, "classes per leaf:"); if (!p) continue;
        p += strlen("classes per leaf:");
        unsigned cls[16]; int x = 0;
        for (char *tok = strtok(p, " \n"); tok && x < 16; tok = strtok(NULL, " \n")) {
            if (tok[0] == '|') continue;
            unsigned C = 0; for (char *q = tok; *q; q++) if (*q >= '0' && *q <= '4') C |= 1u << (*q - '0');
            cls[x++] = C;
        }
        if (x != 16) { printf("parse error\n"); return 1; }
        npat++;
        int w = pat_matrix(&T, cls, L, M), dim = fe_kernel(M, w, L * k, Kb);
        dimhist[dim < 7 ? dim : 7]++;
        if (!has_list(Kb, dim, L)) { bad++; printf("  pattern %d: no list (kernel dim %d)\n", npat, dim); continue; }
        // random kernel point -> messages (member 0 is the zero codeword), codewords, word
        fe mm[4 * 8]; memset(mm, 0, sizeof mm);
        for (int d = 0; d < dim; d++) { fe co = rnd_nz(); for (int e = 0; e < L * k; e++) mm[e] ^= fe_mul(co, Kb[(size_t)d * L * k + e]); }
        for (int l = 1; l <= 4; l++) tree_encode(&T, mm + (l - 1) * 8, c[l]);
        int consistent = 1;
        for (int y = 0; y < 16; y++) {
            int l0 = __builtin_ctz(cls[y]); u[y] = c[l0][y];
            for (int l = 0; l < 5; l++) if (((cls[y] >> l) & 1) && c[l][y] != u[y]) consistent = 0;
        }
        // all codewords at agreement >= 10: interpolate through every 8-subset on which the word is taken
        fe found[64][16]; int nf = 0, over = 0;
        for (unsigned I = 0; I < 65536; I++) {
            if (popc(I) != 8) continue;
            int r = 0;
            for (int y = 0; y < 16; y++) if ((I >> y) & 1) { memcpy(Sys + r * 9, T.G + (size_t)y * 8, sizeof(fe) * 8); Sys[r * 9 + 8] = u[y]; r++; }
            if (fe_rref(Sys, 8, 9, pc) != 8 || pc[7] != 7) { printf("singular information set\n"); return 1; }
            for (int e = 0; e < 8; e++) msg[e] = Sys[e * 9 + 8];
            tree_encode(&T, msg, cand);
            int agr = 0; for (int y = 0; y < 16; y++) agr += cand[y] == u[y];
            if (agr < 10) continue;
            int known = 0; for (int j = 0; j < nf && !known; j++) if (!memcmp(found[j], cand, sizeof(fe) * 16)) known = 1;
            if (!known) { if (nf < 64) memcpy(found[nf++], cand, sizeof(fe) * 16); else over = 1; }
        }
        if (consistent && nf == 5 && !over) ok5++; else { bad++; printf("  pattern %d: consistent %d, codewords at agreement >= 10: %d%s (kernel dim %d)\n", npat, consistent, nf, over ? "+" : "", dim); }
    }
    printf("n = 16, seed %llu: %d five-member patterns read; list of five distinct codewords and exactly five codewords at agreement >= 10 with the rebuilt word: %d; others: %d; kernel dimensions:", (unsigned long long)seed, npat, ok5, bad);
    for (int d = 0; d < 8; d++) if (dimhist[d]) printf(" %d x dim %d,", dimhist[d], d);
    printf("\n");
    return 0;
}
int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "n8")) return main_n8(strtoull(argv[2], 0, 10));
    if (argc >= 4 && !strcmp(argv[1], "n16")) return main_n16(strtoull(argv[2], 0, 10), argv[3]);
    printf("usage: 80_lists n8 seed | n16 seed file\n"); return 1;
}
