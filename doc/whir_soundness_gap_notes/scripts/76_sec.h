// Note 76: secant form of list decoding for the rate-1/2 tree code (Lemma 1.2).
// Points g_x in K^k (rows of the generator of the dual tree code up to scalars; by Lemma 1.1 a generic tree code).
// A list around the syndrome s at error weight <= e is the set of minimal supports E, |E| <= e, with s in span(g_E).
// Needs 69_tree.h, 69_lin.h. Field GF(2^64).
#ifndef SEC76_H
#define SEC76_H
#include "69_tree.h"
#include "69_lin.h"
#define SMAXN 32
#define SMAXK 16
typedef struct {
    int v, n, k, e, nset, codim;
    fe G[SMAXN * SMAXK];
    uint32_t *mask;   // nset masks of size e
    fe *nrm;          // nset * codim * k normals of span(g_E)
} sec_t;

static fe dot(const fe *a, const fe *b, int k) { fe s = 0; for (int i = 0; i < k; i++) s ^= gf_mul(a[i], b[i]); return s; }

static void sec_init(sec_t *S, int v, int e, uint64_t seed) {
    S->v = v; S->k = 1 << v; S->n = 2 << v; S->e = e; S->codim = S->k - e;
    rng_seed(seed);
    char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = '2'; modes[v] = 0;
    tree_t T; tree_make(&T, v, 1, modes); tree_gen(&T, S->G); tree_free(&T);
    int n = S->n, k = S->k, cnt = 0;
    for (uint32_t m = 0; m < (1u << n); m++) if (__builtin_popcount(m) == e) cnt++;
    S->nset = cnt; S->mask = (uint32_t *)malloc(sizeof(uint32_t) * cnt);
    S->nrm = (fe *)malloc(sizeof(fe) * (size_t)cnt * S->codim * k);
    fe M[SMAXK * SMAXK], Kb[SMAXK * SMAXK];
    cnt = 0;
    for (uint32_t m = 0; m < (1u << n); m++) if (__builtin_popcount(m) == e) {
        S->mask[cnt] = m; int r = 0;
        for (int x = 0; x < n; x++) if ((m >> x) & 1) memcpy(M + (r++) * k, S->G + x * k, sizeof(fe) * k);
        int d = gf_kernel(M, e, k, Kb);
        if (d != S->codim) { fprintf(stderr, "not MDS on a set\n"); exit(1); }
        memcpy(S->nrm + (size_t)cnt * S->codim * k, Kb, sizeof(fe) * S->codim * k);
        cnt++;
    }
}
static inline int sec_in(const sec_t *S, int idx, const fe *s) {
    const fe *nu = S->nrm + (size_t)idx * S->codim * S->k;
    for (int c = 0; c < S->codim; c++) if (dot(nu + c * S->k, s, S->k)) return 0;
    return 1;
}
// minimal support of s inside the set mask m (s must lie in span(g_m)); returns the mask of nonzero coefficients
static uint32_t sec_support(const sec_t *S, uint32_t m, const fe *s) {
    int k = S->k, n = S->n, e = __builtin_popcount(m), pos[SMAXN], r = 0;
    // solve sum_x c_x g_x = s: kernel of the k x (e+1) matrix [g_x .. | s]
    fe M[SMAXK * (SMAXN + 1)], Kb[(SMAXN + 1) * (SMAXN + 1)];
    for (int x = 0; x < n; x++) if ((m >> x) & 1) pos[r++] = x;
    for (int i = 0; i < k; i++) { for (int j = 0; j < e; j++) M[i * (e + 1) + j] = S->G[pos[j] * k + i]; M[i * (e + 1) + e] = s[i]; }
    int d = gf_kernel(M, k, e + 1, Kb);
    if (d != 1 || !Kb[e]) { fprintf(stderr, "support: unexpected kernel %d\n", d); exit(1); }
    uint32_t out = 0;
    for (int j = 0; j < e; j++) if (Kb[j]) out |= 1u << pos[j];
    return out;
}
// the list of s: distinct minimal supports of size <= e. Returns the count; sup[] receives them.
static int sec_list(const sec_t *S, const fe *s, uint32_t *sup, int maxsup) {
    int cnt = 0;
    for (int i = 0; i < S->nset; i++) if (sec_in(S, i, s)) {
        uint32_t m = sec_support(S, S->mask[i], s); int dup = 0;
        for (int j = 0; j < cnt; j++) if (sup[j] == m) { dup = 1; break; }
        if (!dup) { if (cnt >= maxsup) { fprintf(stderr, "list overflow\n"); exit(1); } sup[cnt++] = m; }
    }
    return cnt;
}
// basis of the intersection of span(g_E) over the given set indices: kernel of the stacked normals. Returns the dimension.
static int sec_meet(const sec_t *S, const int *idx, int cnt, fe *basis) {
    int k = S->k, rows = cnt * S->codim;
    fe *M = (fe *)malloc(sizeof(fe) * (size_t)(rows + 1) * k);
    for (int i = 0; i < cnt; i++) memcpy(M + (size_t)i * S->codim * k, S->nrm + (size_t)idx[i] * S->codim * k, sizeof(fe) * S->codim * k);
    int d = gf_kernel(M, rows, k, basis);
    free(M);
    return d;
}
static void sec_print_set(FILE *f, uint32_t m, int n) { for (int x = 0; x < n; x++) fputc(((m >> x) & 1) ? 'x' : '.', f); }
#endif
