// Tree codes: twiddles, generator matrix, butterfly encoder, rank. Needs 69_gf.h.
// A code is (v, r, modes): modes[i] in {'1','2','S'} for layer i (layer 0 = bottom).
// '2': t(p,0) != t(p,1) uniform (T2). '1': t(p,1) = t(p,0) + 1 (T1). 'S': subspace specialization.
#ifndef TREE69_H
#define TREE69_H
#include "69_gf.h"
#define MAXV 12
typedef struct { int v, r, n, k; fe *tw[MAXV]; fe beta[64]; } tree_t;

static int f2_independent(const fe *b, int cnt) { // rank over F_2 of the bit vectors
    fe piv[64]; int np = 0;
    for (int i = 0; i < cnt; i++) {
        fe x = b[i];
        for (int j = 0; j < np; j++) { fe y = x ^ piv[j]; if (y < x) x = y; }
        if (!x) return 0;
        piv[np++] = x;
    }
    return 1;
}
// what[i][l] = normalized subspace polynomial of span(beta_0..beta_{i-1}) at beta_l, l >= i
static void subspace_values(const fe *beta, int d, int v, fe *what) {
    fe cur[64];
    fe inv0 = gf_inv(beta[0]);
    for (int l = 0; l < d; l++) cur[l] = gf_mul(beta[l], inv0);
    for (int i = 0; i < v; i++) {
        for (int l = i; l < d; l++) what[i * 64 + l] = cur[l];
        if (i + 1 < v) {
            fe den = gf_inv(gf_mul(cur[i + 1], cur[i + 1] ^ 1));
            for (int l = i + 1; l < d; l++) cur[l] = gf_mul(gf_mul(cur[l], cur[l] ^ 1), den);
        }
    }
}
static void tree_make(tree_t *T, int v, int r, const char *modes) {
    T->v = v; T->r = r; T->n = 1 << (v + r); T->k = 1 << v;
    int d = v + r;
    do { for (int l = 0; l < d; l++) T->beta[l] = gf_rand(); } while (!f2_independent(T->beta, d));
    fe *what = (fe *)calloc((size_t)v * 64, sizeof(fe));
    subspace_values(T->beta, d, v, what);
    for (int i = 0; i < v; i++) {
        int cnt = T->n >> i;
        T->tw[i] = (fe *)malloc(sizeof(fe) * cnt);
        for (int q = 0; q < cnt; q += 2) {
            if (modes[i] == 'S') {
                fe s = 0;
                for (int u = 1; u < d - i; u++) if ((q >> u) & 1) s ^= what[i * 64 + i + u];
                T->tw[i][q] = s; T->tw[i][q + 1] = s ^ what[i * 64 + i]; // what[i][i] = 1
            } else if (modes[i] == '1') {
                T->tw[i][q] = gf_rand(); T->tw[i][q + 1] = T->tw[i][q] ^ 1;
            } else {
                T->tw[i][q] = gf_rand();
                do T->tw[i][q + 1] = gf_rand(); while (T->tw[i][q + 1] == T->tw[i][q]);
            }
        }
    }
    free(what);
}
static void tree_free(tree_t *T) { for (int i = 0; i < T->v; i++) free(T->tw[i]); }
static void tree_row(const tree_t *T, int j, fe *row) { // row[e] = prod_{i: e_i=1} x_i(j)
    row[0] = 1;
    for (int i = 0; i < T->v; i++) {
        fe x = T->tw[i][j >> i]; int h = 1 << i;
        for (int e = 0; e < h; e++) row[h + e] = gf_mul(row[e], x);
    }
}
static void tree_gen(const tree_t *T, fe *G) { for (int j = 0; j < T->n; j++) tree_row(T, j, G + (size_t)j * T->k); }
static void tree_encode(const tree_t *T, const fe *m, fe *c) { // butterflies, top layer first
    for (int t = 0; t < (1 << T->r); t++) memcpy(c + (size_t)t * T->k, m, sizeof(fe) * T->k);
    for (int i = T->v - 1; i >= 0; i--) {
        int h = 1 << i;
        for (int o = 0; o < T->n; o += 2 * h) {
            fe t0 = T->tw[i][o >> i], t1 = T->tw[i][(o >> i) + 1];
            for (int f = 0; f < h; f++) {
                fe u = c[o + f], w = c[o + h + f];
                c[o + f] = u ^ gf_mul(t0, w); c[o + h + f] = u ^ gf_mul(t1, w);
            }
        }
    }
}
static int gf_rank(fe *M, int rows, int cols) { // destructive, row-major
    int rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1;
        for (int i = rk; i < rows; i++) if (M[(size_t)i * cols + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = c; j < cols; j++) { fe t = M[(size_t)p * cols + j]; M[(size_t)p * cols + j] = M[(size_t)rk * cols + j]; M[(size_t)rk * cols + j] = t; }
        fe inv = gf_inv(M[(size_t)rk * cols + c]);
        for (int i = rk + 1; i < rows; i++) {
            fe f = M[(size_t)i * cols + c];
            if (!f) continue;
            f = gf_mul(f, inv);
            for (int j = c; j < cols; j++) M[(size_t)i * cols + j] ^= gf_mul(f, M[(size_t)rk * cols + j]);
        }
        rk++;
    }
    return rk;
}
#endif
