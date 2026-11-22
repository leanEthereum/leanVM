// Note 83: GF(2^64) linear algebra as a shared library for the Python scripts (field of 69_gf.h).
// cc -O2 -shared -fPIC -o 83_bin/libgf83.dylib 83_gflib.c
#include "69_gf.h"
#include "69_lin.h"
uint64_t g83_mul(uint64_t a, uint64_t b) { return gf_mul(a, b); }
uint64_t g83_inv(uint64_t a) { return gf_inv(a); }
// rank of rows x cols (copy made)
int g83_rank(const uint64_t *M, int rows, int cols) {
    fe *A = (fe *)malloc(sizeof(fe) * (size_t)rows * cols + 8); memcpy(A, M, sizeof(fe) * (size_t)rows * cols);
    int rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1;
        for (int i = rk; i < rows; i++) if (A[(size_t)i * cols + c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = c; j < cols; j++) { fe t = A[(size_t)p * cols + j]; A[(size_t)p * cols + j] = A[(size_t)rk * cols + j]; A[(size_t)rk * cols + j] = t; }
        fe inv = gf_inv(A[(size_t)rk * cols + c]);
        for (int i = rk + 1; i < rows; i++) {
            fe f = A[(size_t)i * cols + c]; if (!f) continue; f = gf_mul(f, inv);
            for (int j = c; j < cols; j++) A[(size_t)i * cols + j] ^= gf_mul(f, A[(size_t)rk * cols + j]);
        }
        rk++;
    }
    free(A); return rk;
}
// kernel basis of {x : M x = 0}; K must hold cols*cols entries; returns the dimension
int g83_kernel(const uint64_t *M, int rows, int cols, uint64_t *K) {
    fe *A = (fe *)malloc(sizeof(fe) * (size_t)(rows + 1) * cols + 8); memcpy(A, M, sizeof(fe) * (size_t)rows * cols);
    int d = gf_kernel(A, rows, cols, K); free(A); return d;
}
// C = A (r x m) times B (m x c)
void g83_matmul(const uint64_t *A, const uint64_t *B, int r, int m, int c, uint64_t *C) {
    for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { fe s = 0; for (int l = 0; l < m; l++) s ^= gf_mul(A[(size_t)i * m + l], B[(size_t)l * c + j]); C[(size_t)i * c + j] = s; }
}
