// Note 76: exact lists of the generic tree code at small size by the secant form.
// Usage: 76_n8 v e seed [verbose]. Enumerates every flat of dimension >= 1 that is the meet of two or three
// spans span(g_E), |E| = e, takes its generic point (or its only point) s and computes the full list of s
// (all minimal supports of size <= e). Complete for lists of at least three members whenever any three
// members have a meet of dimension <= 2 containing the list's point as the generic point of a pair meet
// or as the point of a triple meet: at (v, e) = (2, 3) every list of >= 2 members is found (planes of P^3).
// cc -O2 -o 76_bin/76_n8 76_n8.c
#include "76_sec.h"
#define MAXL 4096
static int cmp_u32(const void *a, const void *b) { uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? -1 : x > y; }

int main(int argc, char **argv) {
    int v = argc > 1 ? atoi(argv[1]) : 2, e = argc > 2 ? atoi(argv[2]) : 3; uint64_t seed = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
    int verbose = argc > 4 ? atoi(argv[4]) : 0;
    sec_t S; sec_init(&S, v, e, seed);
    int k = S.k, n = S.n;
    printf("# v=%d k=%d n=%d error weight <= %d (agreement >= %d), sets %d, seed %llu\n", v, k, n, e, n - e, S.nset, (unsigned long long)seed);
    long hist[MAXL] = {0}; int best = 0; uint32_t bestsup[MAXL]; long nbest = 0;
    fe B2[SMAXK * SMAXK], B3[SMAXK * SMAXK], s[SMAXK]; uint32_t sup[MAXL];
    // distinct maximal lists are counted through a hash of the sorted support list
    uint64_t *seen = (uint64_t *)calloc(1 << 22, sizeof(uint64_t)); long nseen = 0;
    for (int i = 0; i < S.nset; i++) for (int j = i + 1; j < S.nset; j++) {
        int id[3] = {i, j, 0};
        int d2 = sec_meet(&S, id, 2, B2);
        if (d2 == 0) continue;
        for (int l = j; l < S.nset; l++) { // l == j: the generic point of the pair meet
            int d3;
            if (l == j) { d3 = d2; memcpy(B3, B2, sizeof(fe) * d2 * k); }
            else { id[2] = l; d3 = sec_meet(&S, id, 3, B3); if (d3 == 0 || d3 == d2) continue; }
            memset(s, 0, sizeof(s));
            for (int a = 0; a < d3; a++) { fe c = d3 == 1 ? 1 : gf_rand_nz(); for (int t = 0; t < k; t++) s[t] ^= gf_mul(c, B3[a * k + t]); }
            int cnt = sec_list(&S, s, sup, MAXL);
            qsort(sup, cnt, sizeof(uint32_t), cmp_u32);
            uint64_t h = 1469598103934665603ull; for (int a = 0; a < cnt; a++) { h ^= sup[a]; h *= 1099511628211ull; } if (!h) h = 1;
            uint64_t slot = h & ((1 << 22) - 1); int dup = 0;
            while (seen[slot]) { if (seen[slot] == h) { dup = 1; break; } slot = (slot + 1) & ((1 << 22) - 1); }
            if (dup) continue;
            seen[slot] = h; nseen++;
            hist[cnt]++;
            if (cnt > best) { best = cnt; nbest = 0; memcpy(bestsup, sup, sizeof(uint32_t) * cnt); }
            if (cnt == best) nbest++;
            if (verbose && cnt >= verbose) {
                printf("list of %d (flat dim %d): agreement classes per leaf:", cnt, d3);
                for (int x = 0; x < n; x++) { printf(" "); int any = 0; for (int a = 0; a < cnt; a++) if (!((sup[a] >> x) & 1)) { printf("%c", a < 10 ? '0' + a : 'a' + a - 10); any = 1; } if (!any) printf("."); if ((x & 1) && x + 1 < n) printf(" |"); }
                printf("   sizes:"); for (int a = 0; a < cnt; a++) printf(" %d", n - __builtin_popcount(sup[a])); printf("\n");
            }
        }
    }
    printf("distinct lists found: %ld\n", nseen);
    for (int c = 1; c < MAXL; c++) if (hist[c]) printf("  lists with %d members: %ld\n", c, hist[c]);
    printf("largest list: %d members (%ld lists). One of them, error supports:\n", best, nbest);
    for (int a = 0; a < best; a++) { printf("  "); sec_print_set(stdout, bestsup[a], n); printf("  agreement %d\n", n - __builtin_popcount(bestsup[a])); }
    return 0;
}
