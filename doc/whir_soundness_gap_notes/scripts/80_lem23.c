// Referee 80: note 76, Lemma 2.3 (top-down derivative lemma) and Lemma 2.1 (monotonicity by lifting), exact checks.
//   80_lem23 deriv <v> <members> <variant> <patterns> <seed>
//       for random dependent patterns: a random relation nu among the incidence rows, its block parts rho_q at the four top blocks;
//       are (1,0) (x) rho_q and (0,1) (x) rho_q in the row space (Lemma 2.3)? For T1 also the sums over the two children of a root.
//   80_lem23 lift <seed> <file>
//       every five-member pattern of the file (n = 16) lifted by one layer (each class copied to two sibling leaves) carries a list
//       at (16,32): five codewords at agreement >= 20 = 5n/8 (Lemma 2.1 at this size).
#include "80_gf.h"
static int in_rowspace(const fe *A, int w, int C, const fe *vec, int rk, fe *buf) {
    memcpy(buf, A, sizeof(fe) * (size_t)w * C); memcpy(buf + (size_t)w * C, vec, sizeof(fe) * C);
    return fe_rank(buf, w + 1, C) == rk;
}
int main(int argc, char **argv) {
    if (argc >= 7 && !strcmp(argv[1], "deriv")) {
        int v = atoi(argv[2]), members = atoi(argv[3]), variant = atoi(argv[4]), npat = atoi(argv[5]); rnd_seed(strtoull(argv[6], 0, 10)); fe_selftest();
        tree_t T; tree_init(&T, v, 2, variant); int k = T.k, n = T.n, L = members - 1, C = L * k, hb = k / 2;
        fe *A = malloc(sizeof(fe) * (size_t)(n * L + 2) * C), *At = malloc(sizeof(fe) * (size_t)C * n * L), *Kb = malloc(sizeof(fe) * (size_t)n * L * n * L), *buf = malloc(sizeof(fe) * (size_t)(n * L + 2) * C);
        fe *nu = malloc(sizeof(fe) * n * L), *rho = malloc(sizeof(fe) * 4 * C), *vec = malloc(sizeof(fe) * C);
        unsigned *cls = malloc(sizeof(unsigned) * n); int *rowleaf = malloc(sizeof(int) * n * L);
        long tested = 0, fail_single = 0, fail_pair = 0, nonzero_parts = 0;
        for (int it = 0; it < npat; it++) {
            int th = 40 + rnd_below(45);
            int b = (it & 1) ? 1 << (1 + rnd_below(v - 1)) : 1; // half of the patterns are constant on blocks, with a block of common zeros
            for (int x = 0; x < n; x++) { if (x % b) { cls[x] = cls[x - 1]; continue; } cls[x] = 0; for (int l = 0; l < members; l++) if ((int)rnd_below(100) < th) cls[x] |= 1u << l; }
            if (b > 1) { int q = rnd_below(n / b), keep = rnd_below(b); for (int j = 0; j < b; j++) cls[q * b + j] = j == keep ? 0 : (1u << members) - 1; }
            int w = 0; for (int x = 0; x < n; x++) { int r = cls_rows(cls[x], L, T.G + (size_t)x * k, k, A + (size_t)w * C); for (int j = 0; j < r; j++) rowleaf[w + j] = x; w += r; }
            if (!w) continue;
            int rk = fe_rank(A, w, C); if (rk == w || rk == C) continue; // no relation, or the row space is everything (nothing to test)
            for (int i = 0; i < w; i++) for (int j = 0; j < C; j++) At[(size_t)j * w + i] = A[(size_t)i * C + j];
            int d = fe_kernel(At, C, w, Kb); if (d != w - rk) { printf("kernel dimension mismatch\n"); return 1; }
            for (int i = 0; i < w; i++) { nu[i] = 0; } for (int j = 0; j < d; j++) { fe co = rnd_nz(); for (int i = 0; i < w; i++) nu[i] ^= fe_mul(co, Kb[(size_t)j * w + i]); }
            tested++;
            // rho_q in K^L (x) K^(k/2): the e_top = 0 slice of sum_{rows of block q} nu_r row_r
            memset(rho, 0, sizeof(fe) * 4 * C);
            for (int i = 0; i < w; i++) { int q = rowleaf[i] / hb; for (int l = 0; l < L; l++) for (int e = 0; e < hb; e++) rho[(size_t)q * C + l * k + e] ^= fe_mul(nu[i], A[(size_t)i * C + l * k + e]); }
            for (int q = 0; q < 4; q++) {
                int nz = 0; for (int j = 0; j < C; j++) nz |= rho[(size_t)q * C + j] != 0; if (!nz) continue; nonzero_parts++;
                for (int side = 0; side < 2; side++) {
                    memset(vec, 0, sizeof(fe) * C);
                    for (int l = 0; l < L; l++) for (int e = 0; e < hb; e++) vec[l * k + side * hb + e] = rho[(size_t)q * C + l * k + e];
                    if (!in_rowspace(A, w, C, vec, rk, buf)) fail_single++;
                }
            }
            for (int root = 0; root < 2; root++) for (int side = 0; side < 2; side++) { // sums over the two children of a root
                memset(vec, 0, sizeof(fe) * C);
                for (int l = 0; l < L; l++) for (int e = 0; e < hb; e++) vec[l * k + side * hb + e] = rho[(size_t)(2 * root) * C + l * k + e] ^ rho[(size_t)(2 * root + 1) * C + l * k + e];
                if (!in_rowspace(A, w, C, vec, rk, buf)) fail_pair++;
            }
        }
        printf("(k,n)=(%d,%d) T%d, %d members: %ld dependent patterns of rank below Lk, %ld nonzero block parts; (1,0)(x)rho_q or (0,1)(x)rho_q outside the row space: %ld; the same for rho_q + rho_q' (two children of a root): %ld\n",
               k, n, variant, members, tested, nonzero_parts, fail_single, fail_pair);
        return 0;
    }
    if (argc >= 4 && !strcmp(argv[1], "lift")) {
        rnd_seed(strtoull(argv[2], 0, 10)); fe_selftest(); tree_t T; tree_init(&T, 4, 2, 2); int k = T.k, n = T.n, L = 4;
        FILE *f = fopen(argv[3], "r"); if (!f) return 1; char line[4096]; int npat = 0, ok = 0, minagr = 99;
        fe *M = malloc(sizeof(fe) * (size_t)(n * L) * L * k), *Kb = malloc(sizeof(fe) * (size_t)L * k * L * k);
        while (fgets(line, sizeof line, f)) {
            char *p = strstr(line, "classes per leaf:"); if (!p) continue; p += strlen("classes per leaf:");
            unsigned cls[32]; int x = 0;
            for (char *tok = strtok(p, " \n"); tok && x < 16; tok = strtok(NULL, " \n")) { if (tok[0] == '|') continue; unsigned Cc = 0; for (char *q = tok; *q; q++) if (*q >= '0' && *q <= '4') Cc |= 1u << (*q - '0'); cls[2 * x] = cls[2 * x + 1] = Cc; x++; }
            npat++;
            for (int l = 0; l < 5; l++) { int a = 0; for (int y = 0; y < 32; y++) a += (cls[y] >> l) & 1; if (a < minagr) minagr = a; }
            int w = pat_matrix(&T, cls, L, M), dim = fe_kernel(M, w, L * k, Kb), good = dim > 0;
            for (int a = 0; a <= L && good; a++) for (int b = a + 1; b <= L && good; b++) {
                int nzf = 0;
                for (int d = 0; d < dim && !nzf; d++) for (int e = 0; e < k && !nzf; e++) { fe val = Kb[(size_t)d * L * k + (size_t)(b - 1) * k + e]; if (a >= 1) val ^= Kb[(size_t)d * L * k + (size_t)(a - 1) * k + e]; if (val) nzf = 1; }
                if (!nzf) good = 0;
            }
            ok += good;
        }
        printf("lifts to (16,32) of %d five-member patterns of n = 16: %d carry five distinct codewords; least agreement of a member %d (5n/8 = 20)\n", npat, ok, minagr);
        return 0;
    }
    printf("usage: see header\n"); return 1;
}
