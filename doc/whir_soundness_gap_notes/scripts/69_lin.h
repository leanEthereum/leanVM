// Kernel of a matrix over the field of 69_gf.h (reduced row echelon form). Needs 69_gf.h.
#ifndef LIN69_H
#define LIN69_H
#include "69_gf.h"
// M: rows x cols, row-major, destroyed. K: receives a basis of {x : M x = 0}, one vector per row. Returns the dimension.
static int gf_kernel(fe *M, int rows, int cols, fe *K) {
    int *pivcol = (int *)malloc(sizeof(int) * (rows + 1)), *ispiv = (int *)calloc(cols, sizeof(int)), rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1;
        for (int i = rk; i < rows; i++) if (M[(size_t)i * cols + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = 0; j < cols; j++) { fe t = M[(size_t)p * cols + j]; M[(size_t)p * cols + j] = M[(size_t)rk * cols + j]; M[(size_t)rk * cols + j] = t; }
        fe inv = gf_inv(M[(size_t)rk * cols + c]);
        for (int j = 0; j < cols; j++) M[(size_t)rk * cols + j] = gf_mul(M[(size_t)rk * cols + j], inv);
        for (int i = 0; i < rows; i++) {
            fe f = M[(size_t)i * cols + c];
            if (i == rk || !f) continue;
            for (int j = 0; j < cols; j++) M[(size_t)i * cols + j] ^= gf_mul(f, M[(size_t)rk * cols + j]);
        }
        pivcol[rk++] = c; ispiv[c] = 1;
    }
    int d = 0;
    for (int c = 0; c < cols; c++) {
        if (ispiv[c]) continue;
        fe *x = K + (size_t)d * cols; memset(x, 0, sizeof(fe) * cols);
        x[c] = 1;
        for (int i = 0; i < rk; i++) x[pivcol[i]] = M[(size_t)i * cols + c]; // characteristic 2: no sign
        d++;
    }
    free(pivcol); free(ispiv);
    return d;
}
// Solve A x = b for square nonsingular A (k x k). Returns 0 if singular.
static int gf_solve(const fe *A, const fe *b, int k, fe *x) {
    fe *M = (fe *)malloc(sizeof(fe) * k * (k + 1)), *K = (fe *)malloc(sizeof(fe) * (k + 1) * (k + 1));
    for (int i = 0; i < k; i++) { memcpy(M + (size_t)i * (k + 1), A + (size_t)i * k, sizeof(fe) * k); M[(size_t)i * (k + 1) + k] = b[i]; }
    int d = gf_kernel(M, k, k + 1, K), ok = (d == 1 && K[k] != 0);
    if (ok) { fe inv = gf_inv(K[k]); for (int i = 0; i < k; i++) x[i] = gf_mul(K[i], inv); }
    free(M); free(K);
    return ok;
}
#endif
