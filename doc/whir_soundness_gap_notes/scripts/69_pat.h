// Agreement patterns and their incidence systems. Needs 69_tree.h.
// A pattern gives each leaf x a class cls[x]: a bitmask of members (subset of {0..L}), empty or of size >= 2.
// Unknowns: d_1..d_L in F^k (d_0 = 0). Leaf x with class C: g_x (d_l - d_l0) = 0 for l in C, l0 = min C.
#ifndef PAT69_H
#define PAT69_H
#include "69_tree.h"
#define MAXN 256
// kinds: '2' tree T2, '1' tree T1, 'S' Reed-Solomon on an F_2-subspace, 'R' Reed-Solomon at random points, 'U' uniform matrix,
// 'A' and 'B' the mixed variants of Task 5
static void code_gen(char kind, int v, int r, fe *G) {
    int n = 1 << (v + r), k = 1 << v;
    if (kind == '2' || kind == '1' || kind == 'S' || (kind >= 'A' && kind <= 'D')) {
        // 'A': bottom ceil(v/2) layers T2, upper layers subspace. 'B': bottom floor(v/2) layers subspace, upper layers T2.
        // 'C': bottom floor(v/2) layers T2, upper layers subspace. 'D': bottom ceil(v/2) layers subspace, upper layers T2.
        char modes[MAXV + 1];
        for (int i = 0; i < v; i++) modes[i] = kind == 'A' ? (i < (v + 1) / 2 ? '2' : 'S') : kind == 'B' ? (i < v / 2 ? 'S' : '2') : kind == 'C' ? (i < v / 2 ? '2' : 'S') : kind == 'D' ? (i < (v + 1) / 2 ? 'S' : '2') : kind;
        modes[v] = 0;
        tree_t T; tree_make(&T, v, r, modes); tree_gen(&T, G); tree_free(&T);
    } else if (kind == 'R') {
        fe y[MAXN];
        for (int j = 0; j < n; j++) { int ok; do { y[j] = gf_rand(); ok = 1; for (int a = 0; a < j; a++) ok &= (y[a] != y[j]); } while (!ok); }
        for (int j = 0; j < n; j++) { fe p = 1; for (int e = 0; e < k; e++) { G[j * k + e] = p; p = gf_mul(p, y[j]); } }
    } else {
        for (int a = 0; a < n * k; a++) G[a] = gf_rand();
    }
}
static int pat_weight(const uint8_t *cls, int n) { int w = 0; for (int x = 0; x < n; x++) if (cls[x]) w += __builtin_popcount(cls[x]) - 1; return w; }
// largest achievable minimum agreement: leaves with an empty class go to one member each
static int pat_balanced(const uint8_t *cls, int n, int L) {
    int cnt[16] = {0}, freeleaves = 0;
    for (int x = 0; x < n; x++) { if (!cls[x]) freeleaves++; for (int l = 0; l <= L; l++) cnt[l] += (cls[x] >> l) & 1; }
    while (freeleaves--) { int b = 0; for (int l = 1; l <= L; l++) if (cnt[l] < cnt[b]) b = l; cnt[b]++; }
    int mn = cnt[0]; for (int l = 1; l <= L; l++) if (cnt[l] < mn) mn = cnt[l];
    return mn;
}
// rank of the incidence system; if ca < cb are given (ca >= 0), k more equations d_ca = d_cb are added
static int inc_rank(const fe *G, int n, int k, int L, const uint8_t *cls, int ca, int cb, fe *M) {
    int cols = L * k, rows = 0;
    for (int x = 0; x < n; x++) {
        if (!cls[x]) continue;
        int l0 = __builtin_ctz(cls[x]);
        for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
            fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * k, G + (size_t)x * k, sizeof(fe) * k);
            if (l0 >= 1) memcpy(row + (l0 - 1) * k, G + (size_t)x * k, sizeof(fe) * k);
            rows++;
        }
    }
    if (ca >= 0) for (int e = 0; e < k; e++) {
        fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
        row[(cb - 1) * k + e] = 1; if (ca >= 1) row[(ca - 1) * k + e] = 1;
        rows++;
    }
    return gf_rank(M, rows, cols);
}
// 1 iff the kernel has a point with d_0 = 0, d_1, .., d_L pairwise distinct (large field: iff no pair collapses on the whole kernel)
static int pat_feasible(const fe *G, int n, int k, int L, const uint8_t *cls, int rank0, fe *M) {
    if (rank0 == L * k) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++)
        if (inc_rank(G, n, k, L, cls, a, b, M) == rank0) return 0;
    return 1;
}
static void pat_print(FILE *f, const uint8_t *cls, int n, int L) {
    for (int x = 0; x < n; x++) {
        if (!cls[x]) fputc('.', f); else for (int l = 0; l <= L; l++) if ((cls[x] >> l) & 1) fputc('0' + l, f);
        fputc(x + 1 < n ? ' ' : '\n', f);
    }
}
#endif
