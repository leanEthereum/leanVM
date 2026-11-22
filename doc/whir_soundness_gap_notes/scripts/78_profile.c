// Note 78: tensor profile of the kernel of a pattern's incidence system for a V2 code, in the variables of each tree.
// usage: 78_profile v r seed spec patternfile [maxlines]
// Per pattern: rank, kernel dimension, and for a random kernel point (d_1..d_L), per tree t and split level i = 1..v-1, the rank
// of the (L k/2^i) x 2^i matrix of the upper slices of all d_l written in tree t's index (table f -> d(M_t^-1 f)).
// Rank 1 at (t, i) = the differences are A_l (x) B with a common lower factor for tree t at level i.
// "two-sided" = some level has rank 1 in every tree (not necessarily the same level).
#include "69_pat.h"
#include "78_var.h"
static int parse_pattern(const char *line, uint8_t *cls, int n, int *Lout) {
    const char *p = strstr(line, " | "); p = p ? p + 3 : line; int x = 0, mx = 0;
    while (*p && x < n) { while (*p == ' ') p++; if (!*p || *p == '\n') break; uint8_t c = 0;
        while (*p && *p != ' ' && *p != '\n') { if (*p >= '0' && *p <= '9') { c |= (uint8_t)(1 << (*p - '0')); if (*p - '0' > mx) mx = *p - '0'; } p++; } cls[x++] = c; }
    *Lout = mx; return x == n;
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]); rng_seed(strtoull(argv[3], 0, 10)); gf_init();
    var_t V; if (!var_make(&V, argv[4], v, r)) { printf("bad spec\n"); return 1; }
    FILE *fp = fopen(argv[5], "r"); long maxl = argc > 6 ? atol(argv[6]) : 1000000, cnt = 0, two = 0, withker = 0, anyprod = 0;
    int n = V.n, k = V.k, L; char line[8192]; uint8_t cls[MAXN];
    long hist[64] = {0};
    while (fgets(line, sizeof line, fp) && cnt < maxl) {
        if (!parse_pattern(line, cls, n, &L)) continue;
        cnt++; int cols = L * k, rows = 0;
        fe *M = malloc(sizeof(fe) * (size_t)(L * n + 1) * cols), *K = malloc(sizeof(fe) * (size_t)cols * cols), *d = calloc(cols, sizeof(fe)), *R = malloc(sizeof(fe) * cols);
        for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
            fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * k, V.G + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, V.G + (size_t)x * k, sizeof(fe) * k); rows++; } }
        int dim = gf_kernel(M, rows, cols, K);
        for (int b = 0; b < dim; b++) { fe s = gf_rand(); for (int j = 0; j < cols; j++) d[j] ^= gf_mul(s, K[(size_t)b * cols + j]); }
        printf("w=%d rank=%d ker=%d prof", pat_weight(cls, n), cols - dim, dim);
        int alltrees = 1, some = 0;
        for (int t = 0; t < (1 << r) && dim; t++) {
            int has1 = 0; printf(" t%d=", t);
            for (int i = 1; i < v; i++) {
                int kl = 1 << i; // R[(l, f_up), f_low] = d_l[e] with f = M_t e
                for (int l = 0; l < L; l++) for (int e = 0; e < k; e++) { int f = (V.hasM && t) ? V.perm[t][e] : e; R[(size_t)(l * (k >> i) + (f >> i)) * kl + (f & (kl - 1))] = d[l * k + e]; }
                int tr = gf_rank(R, cols / kl, kl); printf("%d%s", tr, i + 1 < v ? "," : ""); has1 |= (tr == 1);
            }
            alltrees &= has1; some |= has1;
        }
        if (dim) { withker++; two += alltrees; anyprod += some; if (dim < 64) hist[dim]++; }
        printf(" | "); pat_print(stdout, cls, n, L);
        free(M); free(K); free(d); free(R);
    }
    printf("# %s: patterns %ld, with a kernel %ld, a common lower factor in some tree %ld, in every tree (two-sided product) %ld\n", argv[4], cnt, withker, anyprod, two);
    return 0;
}
