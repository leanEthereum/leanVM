// Note 78: the variants V1 (leaf mixing) and V2 (index change) of the tree code of note 68 Section 13.
// Needs note 69's headers. A code is given by a spec string, tokens separated by ':':
//   U            uniform generator matrix
//   T2           plain tree code (independent twiddles at every node)
//   T2:d<D><p>   V1 with D partners per leaf; p = a (uniform permutations of all leaves), x (partner in another tree),
//                s (partner = the sibling leaf), b (uniform permutation inside each half tree), c (one n-cycle),
//                f (as x, redrawn until it has no 2-cycle)
//   T2:M<list>   V2; list = names separated by '/', one per tree 1, 2, ..; if fewer names than trees, tree t uses M^t.
//                names: id, rev, rot, up, dn, ud (= up*dn), du (= dn*up), cr (bit 0 := top bit, top bit := top + bit 0), sw<i>, #<integer> (rows packed v bits each, row l = bits l*v..l*v+v-1,
//                (M e)_l = parity(row_l & e))
//   T2:M..:d..   V1 on top of V2
#ifndef VAR78_H
#define VAR78_H
#include "69_tree.h"
#include "69_lin.h"
#define V78_MAXD 3
#define V78_MAXT 8
typedef struct {
    int v, r, n, k, uniform;
    tree_t T;
    int d; char ptype;
    int *pi[V78_MAXD]; fe *mu[V78_MAXD];
    int hasM; uint32_t M[V78_MAXT][MAXV];
    int *perm[V78_MAXT]; // perm[t][e] = M_t e
    fe *G;
} var_t;

static inline int f2_apply(const uint32_t *rows, int v, int e) { int o = 0; for (int l = 0; l < v; l++) o |= (__builtin_parity(rows[l] & (uint32_t)e)) << l; return o; }
static void f2_mul(const uint32_t *A, const uint32_t *B, int v, uint32_t *C) { // C = A B
    uint32_t out[MAXV];
    for (int l = 0; l < v; l++) { uint32_t row = 0; for (int j = 0; j < v; j++) if ((A[l] >> j) & 1) row ^= B[j]; out[l] = row; }
    memcpy(C, out, sizeof(uint32_t) * v);
}
static int f2_inv(const uint32_t *A, int v, uint32_t *Inv) { // returns 0 if singular
    uint32_t a[MAXV], b[MAXV];
    for (int l = 0; l < v; l++) { a[l] = A[l]; b[l] = 1u << l; }
    for (int c = 0; c < v; c++) {
        int p = -1; for (int l = c; l < v; l++) if ((a[l] >> c) & 1) { p = l; break; }
        if (p < 0) return 0;
        uint32_t t = a[p]; a[p] = a[c]; a[c] = t; t = b[p]; b[p] = b[c]; b[c] = t;
        for (int l = 0; l < v; l++) if (l != c && ((a[l] >> c) & 1)) { a[l] ^= a[c]; b[l] ^= b[c]; }
    }
    if (Inv) memcpy(Inv, b, sizeof(uint32_t) * v);
    return 1;
}
static uint64_t f2_pack(const uint32_t *A, int v) { uint64_t c = 0; for (int l = 0; l < v; l++) c |= (uint64_t)A[l] << (l * v); return c; }
static void f2_unpack(uint64_t c, int v, uint32_t *A) { for (int l = 0; l < v; l++) A[l] = (uint32_t)((c >> (l * v)) & ((1u << v) - 1)); }
static void f2_mul(const uint32_t *A, const uint32_t *B, int v, uint32_t *C);
static int f2_named(const char *name, int v, uint32_t *A) { // returns 1 on success
    for (int l = 0; l < v; l++) A[l] = 1u << l;
    if (!strcmp(name, "id")) return 1;
    if (!strcmp(name, "rev")) { for (int l = 0; l < v; l++) A[l] = 1u << (v - 1 - l); return 1; }
    if (!strcmp(name, "rot")) { for (int l = 0; l < v; l++) A[l] = 1u << ((l + v - 1) % v); return 1; }
    if (!strcmp(name, "up")) { for (int l = 0; l + 1 < v; l++) A[l] |= 1u << (l + 1); return 1; }
    if (!strcmp(name, "dn")) { for (int l = 1; l < v; l++) A[l] |= 1u << (l - 1); return 1; }
    if (!strcmp(name, "ud") || !strcmp(name, "du")) { // up*dn and dn*up
        uint32_t U[MAXV], D[MAXV]; f2_named("up", v, U); f2_named("dn", v, D);
        if (name[0] == 'u') f2_mul(U, D, v, A); else f2_mul(D, U, v, A);
        return 1;
    }
    if (!strcmp(name, "cr")) { A[0] = 1u << (v - 1); A[v - 1] = (1u << (v - 1)) | 1u; return v >= 2; } // (Me)_0 = e_top, (Me)_top = e_top + e_0
    if (name[0] == 's' && name[1] == 'w') { int i = atoi(name + 2); if (i + 1 >= v) return 0; A[i] = 1u << (i + 1); A[i + 1] = 1u << i; return 1; }
    if (name[0] == '#') { f2_unpack(strtoull(name + 1, 0, 0), v, A); return f2_inv(A, v, 0); }
    return 0;
}
static void rand_perm(int *p, int m) { for (int i = 0; i < m; i++) p[i] = i; for (int i = m - 1; i > 0; i--) { int j = (int)rng_below((uint64_t)i + 1), t = p[i]; p[i] = p[j]; p[j] = t; } }
static void var_partner(var_t *V, int a) {
    int n = V->n, k = V->k, *pi = V->pi[a], *tmp = (int *)malloc(sizeof(int) * n);
    char p = V->ptype;
    if (p == 'a') rand_perm(pi, n);
    else if (p == 's') { for (int x = 0; x < n; x++) pi[x] = x ^ 1; }
    else if (p == 'c') { rand_perm(tmp, n); for (int i = 0; i < n; i++) pi[tmp[i]] = tmp[(i + 1) % n]; }
    else if (p == 'b') { int h = k / 2; for (int b = 0; b < n / h; b++) { rand_perm(tmp, h); for (int i = 0; i < h; i++) pi[b * h + i] = b * h + tmp[i]; } }
    else { // 'x' and 'f': tree t goes to tree t ^ s by a uniform bijection
        for (;;) {
            int s = 1 + (int)rng_below((uint64_t)(1 << V->r) - 1);
            for (int t = 0; t < (1 << V->r); t++) { rand_perm(tmp, k); for (int i = 0; i < k; i++) pi[t * k + i] = (t ^ s) * k + tmp[i]; }
            if (p == 'x') break;
            int two = 0; for (int x = 0; x < n; x++) two |= (pi[pi[x]] == x);
            if (!two) break;
        }
    }
    for (int x = 0; x < n; x++) V->mu[a][x] = gf_rand_nz();
    free(tmp);
}
static void tree_butterfly(const tree_t *T, fe *c) {
    for (int i = T->v - 1; i >= 0; i--) {
        int h = 1 << i;
        for (int o = 0; o < T->n; o += 2 * h) {
            fe t0 = T->tw[i][o >> i], t1 = T->tw[i][(o >> i) + 1];
            for (int f = 0; f < h; f++) { fe u = c[o + f], w = c[o + h + f]; c[o + f] = u ^ gf_mul(t0, w); c[o + h + f] = u ^ gf_mul(t1, w); }
        }
    }
}
// (re)compute the generator from the twiddles, the index maps and the partners
static void var_build(var_t *V) {
    int n = V->n, k = V->k;
    if (V->uniform) return;
    fe *R = (fe *)malloc(sizeof(fe) * (size_t)n * k), *row = (fe *)malloc(sizeof(fe) * k);
    for (int j = 0; j < n; j++) {
        tree_row(&V->T, j, row);
        int t = j >> V->v;
        if (V->hasM && t) for (int e = 0; e < k; e++) R[(size_t)j * k + e] = row[V->perm[t][e]];
        else memcpy(R + (size_t)j * k, row, sizeof(fe) * k);
    }
    memcpy(V->G, R, sizeof(fe) * (size_t)n * k);
    for (int a = 0; a < V->d; a++) for (int x = 0; x < n; x++) {
        fe m = V->mu[a][x]; const fe *src = R + (size_t)V->pi[a][x] * k; fe *dst = V->G + (size_t)x * k;
        for (int e = 0; e < k; e++) dst[e] ^= gf_mul(m, src[e]);
    }
    free(R); free(row);
}
static int var_make(var_t *V, const char *spec, int v, int r) {
    memset(V, 0, sizeof *V); V->v = v; V->r = r; V->n = 1 << (v + r); V->k = 1 << v;
    int n = V->n, k = V->k;
    V->G = (fe *)malloc(sizeof(fe) * (size_t)n * k);
    char buf[256]; strncpy(buf, spec, 255); buf[255] = 0;
    char *save = 0, *tok = strtok_r(buf, ":", &save);
    if (!tok) return 0;
    if (!strcmp(tok, "U")) { V->uniform = 1; for (size_t a = 0; a < (size_t)n * k; a++) V->G[a] = gf_rand(); return 1; }
    if (strcmp(tok, "T2")) return 0;
    char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = '2'; modes[v] = 0;
    tree_make(&V->T, v, r, modes);
    while ((tok = strtok_r(0, ":", &save))) {
        if (tok[0] == 'd') {
            V->d = tok[1] - '0'; V->ptype = tok[2] ? tok[2] : 'a';
            if (V->d < 1 || V->d > V78_MAXD) return 0;
            for (int a = 0; a < V->d; a++) { V->pi[a] = (int *)malloc(sizeof(int) * n); V->mu[a] = (fe *)malloc(sizeof(fe) * n); var_partner(V, a); }
        } else if (tok[0] == 'M') {
            V->hasM = 1; int cnt = 0; char *s2 = 0, *nm = strtok_r(tok + 1, "/", &s2);
            for (int l = 0; l < v; l++) V->M[0][l] = 1u << l;
            while (nm && cnt + 1 < (1 << r)) { if (!f2_named(nm, v, V->M[cnt + 1])) return 0; cnt++; nm = strtok_r(0, "/", &s2); }
            if (!cnt) return 0;
            for (int t = cnt + 1; t < (1 << r); t++) f2_mul(V->M[t - 1], V->M[1], v, V->M[t]);
            for (int t = 0; t < (1 << r); t++) { V->perm[t] = (int *)malloc(sizeof(int) * k); for (int e = 0; e < k; e++) V->perm[t][e] = f2_apply(V->M[t], v, e); }
        } else return 0;
    }
    var_build(V);
    return 1;
}
// encoder: index change per tree, butterflies, mixing. For U: G m.
static void var_encode(const var_t *V, const fe *m, fe *c) {
    int n = V->n, k = V->k;
    if (V->uniform) { for (int x = 0; x < n; x++) { fe s = 0; for (int e = 0; e < k; e++) s ^= gf_mul(V->G[(size_t)x * k + e], m[e]); c[x] = s; } return; }
    fe *c0 = (fe *)malloc(sizeof(fe) * n);
    for (int t = 0; t < (1 << V->r); t++) for (int e = 0; e < k; e++) c0[t * k + ((V->hasM && t) ? V->perm[t][e] : e)] = m[e];
    tree_butterfly(&V->T, c0);
    memcpy(c, c0, sizeof(fe) * n);
    for (int a = 0; a < V->d; a++) for (int x = 0; x < n; x++) c[x] ^= gf_mul(V->mu[a][x], c0[V->pi[a][x]]);
    free(c0);
}
static void var_free(var_t *V) {
    free(V->G); if (V->uniform) return; tree_free(&V->T);
    for (int a = 0; a < V->d; a++) { free(V->pi[a]); free(V->mu[a]); }
    if (V->hasM) for (int t = 0; t < (1 << V->r); t++) free(V->perm[t]);
}
#endif
