// Task 2: re-evaluate listed patterns on fresh codes: rank, kernel dimension, feasibility, tensor profile of the kernel.
// usage: t2_file v r L kinds seed patternfile [maxlines]
// Tensor profile of a random kernel point (d_1..d_L): for each split level i (1 <= i < v) the rank of the
// (L k/2^i) x 2^i matrix whose rows are the upper slices of all d_l. Rank 1 = common lower factor (A_l (x) B).
// sub=: size of the largest sub-list (>= 3 members) whose differences share a lower factor at some level.
// up=: rank of the (k/2^i) x (L 2^i) matrix in the other direction. Rank 1 = common upper factor (A (x) B_l).
#include "69_pat.h"
#include "69_lin.h"
static int parse_pattern(const char *line, uint8_t *cls, int n) {
    const char *p = strstr(line, " | "); p = p ? p + 3 : line;
    int x = 0;
    while (*p && x < n) {
        while (*p == ' ') p++;
        if (!*p || *p == '\n') break;
        uint8_t c = 0;
        while (*p && *p != ' ' && *p != '\n') { if (*p >= '0' && *p <= '9') c |= (uint8_t)(1 << (*p - '0')); p++; }
        cls[x++] = c;
    }
    return x == n;
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), L = atoi(argv[3]); const char *kinds = argv[4];
    rng_seed(strtoull(argv[5], 0, 10)); FILE *f = fopen(argv[6], "r"); long maxlines = argc > 7 ? atol(argv[7]) : 1000000000;
    gf_init(); int n = 1 << (v + r), k = 1 << v, nk = (int)strlen(kinds), cols = L * k;
    fe *G[8]; for (int c = 0; c < nk; c++) { G[c] = malloc(sizeof(fe) * n * k); code_gen(kinds[c], v, r, G[c]); }
    fe *M = malloc(sizeof(fe) * (size_t)(L * n + k) * cols), *K = malloc(sizeof(fe) * (size_t)cols * cols), *d = malloc(sizeof(fe) * cols), *R = malloc(sizeof(fe) * cols);
    char line[4096]; uint8_t cls[MAXN]; long cnt = 0;
    long agg[8][5] = {{0}}; // per kind: deficient, feasible, feasible with a product profile (some level of rank 1)
    while (fgets(line, sizeof line, f) && cnt < maxlines) {
        if (!parse_pattern(line, cls, n)) continue;
        cnt++;
        int rk0 = 0;
        printf("w=%d a=%d", pat_weight(cls, n), pat_balanced(cls, n, L));
        for (int c = 0; c < nk; c++) {
            int rk = inc_rank(G[c], n, k, L, cls, -1, -1, M); if (c == 0) rk0 = rk;
            int feas = pat_feasible(G[c], n, k, L, cls, rk, M);
            // kernel point: rebuild the system (inc_rank destroys M) and take a random combination of a kernel basis
            int rows = 0;
            for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
                fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
                memcpy(row + (l - 1) * k, G[c] + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, G[c] + (size_t)x * k, sizeof(fe) * k); rows++; } }
            int dim = gf_kernel(M, rows, cols, K);
            memset(d, 0, sizeof(fe) * cols);
            for (int b = 0; b < dim; b++) { fe s = gf_rand(); for (int j = 0; j < cols; j++) d[j] ^= gf_mul(s, K[(size_t)b * cols + j]); }
            // direct check of the sampled kernel point: codewords G d_l, agreement inside every class, and each member's true agreement count
            int bad = 0, minag = n;
            if (dim) {
                fe *cw = M; // reuse: (L+1) x n codeword values, member 0 is the zero codeword
                for (int l = 0; l <= L; l++) for (int x = 0; x < n; x++) { fe sacc = 0; if (l) for (int e = 0; e < k; e++) sacc ^= gf_mul(G[c][(size_t)x * k + e], d[(l - 1) * k + e]); cw[(size_t)l * n + x] = sacc; }
                int ag[16] = {0};
                for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = 0; l <= L; l++) if ((cls[x] >> l) & 1) { ag[l]++; bad += (cw[(size_t)l * n + x] != cw[(size_t)l0 * n + x]); } }
                for (int l = 0; l <= L; l++) if (ag[l] < minag) minag = ag[l];
            }
            printf(" | %c rank=%d ker=%d feas=%d direct(bad=%d,minclass=%d) prof=", kinds[c], rk, dim, feas, bad, dim ? minag : 0);
            int prod = 0, upc = 0;
            for (int i = 1; i < v; i++) {
                int kl = 1 << i; // rows: (l, e_up), cols: f ; d[(l-1)k + (e_up << i | f)] is already in that layout
                memcpy(R, d, sizeof(fe) * cols);
                int tr = dim ? gf_rank(R, cols / kl, kl) : 0;
                printf("%d%s", tr, i + 1 < v ? "," : ""); prod |= (tr == 1);
            }
            printf(" up=");
            for (int i = 1; i < v; i++) { // upper factor: rows e_up, columns (l, f)
                int kl = 1 << i, ku = k >> i;
                for (int e = 0; e < ku; e++) for (int l = 0; l < L; l++) for (int ff = 0; ff < kl; ff++) R[(size_t)e * L * kl + l * kl + ff] = d[l * k + ((e << i) | ff)];
                int tr = dim ? gf_rank(R, ku, L * kl) : 0;
                printf("%d%s", tr, i + 1 < v ? "," : ""); upc |= (tr == 1);
            }
            // largest subset of members (>= 3) whose differences to its first member share a lower factor at some level
            int best = 0;
            for (int T = 0; dim && T < (1 << (L + 1)); T++) {
                int sz = __builtin_popcount(T); if (sz < 3 || sz <= best) continue;
                int l0 = __builtin_ctz(T), ok = 0;
                for (int i = 1; i < v && !ok; i++) {
                    int kl = 1 << i, rows2 = 0;
                    for (int l = l0 + 1; l <= L; l++) if ((T >> l) & 1) {
                        for (int e = 0; e < k; e++) R[(size_t)rows2 * k + e] = d[(l - 1) * k + e] ^ (l0 ? d[(l0 - 1) * k + e] : 0);
                        rows2++;
                    }
                    ok = (gf_rank(R, rows2 * (k / kl), kl) == 1);
                }
                if (ok) best = sz;
            }
            printf(" sub=%d", best);
            if (feas && best >= 3) agg[c][4]++;
            if (feas && upc && !prod) agg[c][3]++;
            if (rk < rk0) agg[c][0]++;
            if (feas) { agg[c][1]++; if (prod) agg[c][2]++; }
        }
        printf(" | "); pat_print(stdout, cls, n, L);
    }
    for (int c = 0; c < nk; c++) printf("# kind %c: patterns %ld, rank below kind %c: %ld, feasible: %ld, feasible with a common lower factor: %ld, feasible with a common upper factor only: %ld, feasible with three or more members sharing a lower factor: %ld\n", kinds[c], cnt, kinds[0], agg[c][0], agg[c][1], agg[c][2], agg[c][3], agg[c][4]);
    return 0;
}
