// Note 74, task 2: is the kernel of a pattern spanned by lifted solutions A (x) B (Lemma 3.1)?
// For every split level i = 1..v and every zero set Z of 2^i - 1 leaves: B_Z, the kernel A_i(Z) of the top system, the products.
// Output per pattern: kernel dimension for T2 and for a uniform matrix, dim of the span of lifts at each level, of all levels < v,
// of all levels, and the verdict. usage: 74_classify v r L seed patternfile [v]
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
static int v, r, L, n, k, cols;
static fe *G, *GU;
// span accumulator: rows of length cols, reduced when the buffer fills
typedef struct { fe *buf; int rows, cap; } span_t;
static void span_add(span_t *s, const fe *vec) {
    memcpy(s->buf + (size_t)s->rows * cols, vec, sizeof(fe) * cols); s->rows++;
    if (s->rows == s->cap) s->rows = gf_rank(s->buf, s->rows, cols);
}
static int span_dim(span_t *s) { s->rows = s->rows ? gf_rank(s->buf, s->rows, cols) : 0; return s->rows; }
int main(int argc, char **argv) {
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); rng_seed(strtoull(argv[4], 0, 10)); FILE *f = fopen(argv[5], "r"); int verbose = argc > 6;
    gf_init(); n = 1 << (v + r); k = 1 << v; cols = L * k;
    G = malloc(sizeof(fe) * n * k); GU = malloc(sizeof(fe) * n * k); code_gen('2', v, r, G); code_gen('U', v, r, GU);
    fe *M = malloc(sizeof(fe) * (size_t)(L * n + k) * cols), *S = malloc(sizeof(fe) * (size_t)cols * cols), *Bm = malloc(sizeof(fe) * k * k), *Bk = malloc(sizeof(fe) * k * k);
    fe *Tm = malloc(sizeof(fe) * (size_t)(L * n) * cols), *Ak = malloc(sizeof(fe) * (size_t)cols * cols), *vec = malloc(sizeof(fe) * cols), *chk = malloc(sizeof(fe) * (size_t)(2 * cols + 8) * cols);
    span_t lev[MAXV + 1], below, all; int cap = 4 * cols + 8;
    for (int i = 0; i <= v; i++) lev[i].buf = malloc(sizeof(fe) * (size_t)cap * cols), lev[i].cap = cap;
    below.buf = malloc(sizeof(fe) * (size_t)cap * cols); below.cap = cap; all.buf = malloc(sizeof(fe) * (size_t)cap * cols); all.cap = cap;
    char line[8192]; uint8_t cls[MAXN]; long cnt = 0, nfull = 0, nacc = 0, nnot = 0, nbelow = 0, notin = 0; long hist[64][8]; memset(hist, 0, sizeof hist);
    while (fgets(line, sizeof line, f)) {
        if (!parse_pattern(line, cls, n)) continue;
        cnt++;
        int rkU = inc_rank(GU, n, k, L, cls, -1, -1, M), dU = cols - rkU;
        int rows = 0;
        for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
            fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * k, G + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, G + (size_t)x * k, sizeof(fe) * k); rows++; } }
        int dT = gf_kernel(M, rows, cols, S);
        for (int i = 0; i <= v; i++) lev[i].rows = 0; below.rows = 0; all.rows = 0;
        int ldim[MAXV + 1] = {0};
        for (int i = 1; i <= v; i++) {
            int kl = 1 << i, ku = k >> i, z = kl - 1, tc = L * ku, Z[64];
            for (int a = 0; a < z; a++) Z[a] = a;
            for (;;) {
                uint64_t inZ[4] = {0}; for (int a = 0; a < z; a++) inZ[Z[a] >> 6] |= 1ull << (Z[a] & 63);
                // top system
                int tr = 0;
                for (int x = 0; x < n; x++) if (cls[x] && !((inZ[x >> 6] >> (x & 63)) & 1)) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
                    fe *row = Tm + (size_t)tr * tc; memset(row, 0, sizeof(fe) * tc);
                    for (int e = 0; e < ku; e++) { fe gq = G[(size_t)x * k + ((size_t)e << i)]; row[(l - 1) * ku + e] = gq; if (l0 >= 1) row[(l0 - 1) * ku + e] = gq; }
                    tr++; } }
                int da = tr ? gf_kernel(Tm, tr, tc, Ak) : tc;
                if (!tr) { memset(Ak, 0, sizeof(fe) * tc * tc); for (int a = 0; a < tc; a++) Ak[(size_t)a * tc + a] = 1; }
                if (da) {
                    for (int a = 0; a < z; a++) memcpy(Bm + (size_t)a * kl, G + (size_t)Z[a] * k, sizeof(fe) * kl);
                    int db = z ? gf_kernel(Bm, z, kl, Bk) : 1; if (!z) Bk[0] = 1;
                    for (int b = 0; b < db; b++) for (int a = 0; a < da; a++) {
                        for (int l = 0; l < L; l++) for (int e = 0; e < ku; e++) for (int ff = 0; ff < kl; ff++) vec[l * k + ((e << i) | ff)] = gf_mul(Ak[(size_t)a * tc + l * ku + e], Bk[(size_t)b * kl + ff]);
                        span_add(&lev[i], vec); span_add(&all, vec); if (i < v) span_add(&below, vec);
                    }
                }
                int a = z - 1; while (a >= 0 && Z[a] == n - z + a) a--;
                if (a < 0) break;
                Z[a]++; for (int b = a + 1; b < z; b++) Z[b] = Z[b - 1] + 1;
            }
            ldim[i] = span_dim(&lev[i]);
        }
        int dbel = span_dim(&below), dall = span_dim(&all);
        // sanity: the lifts lie in the kernel
        memcpy(chk, S, sizeof(fe) * (size_t)dT * cols); memcpy(chk + (size_t)dT * cols, all.buf, sizeof(fe) * (size_t)dall * cols);
        if ((dT + dall ? gf_rank(chk, dT + dall, cols) : 0) != dT) notin++;
        int verdict = dall == dT ? 0 : (dT - dall <= dU ? 1 : 2);
        if (verdict == 0) nfull++; else if (verdict == 1) nacc++; else nnot++;
        if (dbel == dT) nbelow++;
        if (verbose || verdict == 2) { printf("%s dT=%d dU=%d lifts:", verdict == 0 ? "SPANNED" : verdict == 1 ? "REMAINDER<=dU" : "NOT-A-LIFT", dT, dU); for (int i = 1; i <= v; i++) printf(" L%d=%d", i, ldim[i]); printf(" below_v=%d all=%d | ", dbel, dall); pat_print(stdout, cls, n, L); }
    }
    printf("# v=%d r=%d L=%d: patterns %ld; kernel spanned by lifts (all levels): %ld, of which by levels < v alone: %ld; remainder at most the uniform kernel dimension: %ld; NOT explained: %ld; lifts outside the kernel (must be 0): %ld\n", v, r, L, cnt, nfull, nbelow, nacc, nnot, notin);
    return 0;
}
