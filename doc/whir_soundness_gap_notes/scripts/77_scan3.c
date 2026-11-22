// Note 77: exhaustive test of Q_3 for Reed-Solomon codes on an F_2-subspace D of GF(2^64).
// Q_3 fails iff there are disjoint A, B, C in D, |A|+|B|+|C| = 2k, each of size <= k-1, and polynomials f, g of degree < k,
// f = 0 on A, g = 0 on B, f + g = 0 on C, (f, g) != 0: a singular 2k x 2k system. All labelings of D by {-, A, B, C} with
// exactly 2k labelled points are enumerated, up to the symmetry "the smallest labelled point is in A".
// usage: 77_scan3 N k kind seed [odd]     with 'odd': 2k + 1 labelled points and the same degree bound (an unbalanced triple with an odd number of points)
// kind P: D = <1, x, .., x^(N-1)> (today's code); G: random subspace; H: <1, r, r^2, ..> for a random r
// prints one line per singular labeling: the labels in the order of the points (index j = sum of the basis elements of the bits of j),
// the kernel dimension, and the true pattern of the first kernel vector (A: only f = 0, B: only g = 0, C: only f + g = 0, T: all, -: none).
#include "69_gf.h"
#include "69_lin.h"
static int N, n, k, K2, NL; // NL labelled points: 2k, or 2k + 1 with the option 'odd'
static fe pts[64], pw[64][16];
static char lab[65];
static long long tested = 0, found = 0;
static fe M[33][32];
static int singular(void) {
    int r = 0;
    for (int j = 0; j < n; j++) {
        if (lab[j] == '-') continue;
        for (int e = 0; e < k; e++) {
            M[r][e] = (lab[j] == 'A' || lab[j] == 'C') ? pw[j][e] : 0;
            M[r][k + e] = (lab[j] == 'B' || lab[j] == 'C') ? pw[j][e] : 0;
        }
        r++;
    }
    for (int c = 0; c < K2; c++) {
        int p = -1;
        for (int i = c; i < NL; i++) if (M[i][c]) { p = i; break; }
        if (p < 0) return 1;
        if (p != c) for (int j = c; j < K2; j++) { fe t = M[p][j]; M[p][j] = M[c][j]; M[c][j] = t; }
        fe inv = gf_inv(M[c][c]);
        for (int i = c + 1; i < NL; i++) {
            if (!M[i][c]) continue;
            fe f = gf_mul(M[i][c], inv);
            for (int j = c + 1; j < K2; j++) M[i][j] ^= gf_mul(f, M[c][j]);
        }
    }
    return 0;
}
static void describe(void) {
    static fe Mk[64 * 32], Kk[33 * 32];
    int r = 0;
    for (int j = 0; j < n; j++) {
        if (lab[j] == '-') continue;
        for (int e = 0; e < k; e++) {
            Mk[r * K2 + e] = (lab[j] == 'A' || lab[j] == 'C') ? pw[j][e] : 0;
            Mk[r * K2 + k + e] = (lab[j] == 'B' || lab[j] == 'C') ? pw[j][e] : 0;
        }
        r++;
    }
    int d = gf_kernel(Mk, r, K2, Kk);
    char tr[65];
    for (int j = 0; j < n; j++) {
        fe f = 0, g = 0;
        for (int e = 0; e < k; e++) { f ^= gf_mul(Kk[e], pw[j][e]); g ^= gf_mul(Kk[k + e], pw[j][e]); }
        tr[j] = (!f && !g) ? 'T' : !f ? 'A' : !g ? 'B' : (f == g) ? 'C' : '-';
    }
    tr[n] = 0;
    int df = -1, dg = -1;
    for (int e = 0; e < k; e++) { if (Kk[e]) df = e; if (Kk[k + e]) dg = e; }
    printf("%s %d %s %d %d\n", lab, d, tr, df, dg);
}
static void rec(int j, int used, int a, int b, int c) {
    if (n - j < NL - used) return;
    if (j == n) {
        tested++;
        if (singular()) { found++; lab[n] = 0; describe(); }
        return;
    }
    if (used < NL) {
        if (a < k - 1) { lab[j] = 'A'; rec(j + 1, used + 1, a + 1, b, c); }
        if (used > 0) {
            if (b < k - 1) { lab[j] = 'B'; rec(j + 1, used + 1, a, b + 1, c); }
            if (c < k - 1 && b > 0) { lab[j] = 'C'; rec(j + 1, used + 1, a, b, c + 1); }
        }
    }
    lab[j] = '-'; rec(j + 1, used, a, b, c);
}
int main(int argc, char **argv) {
    N = atoi(argv[1]); k = atoi(argv[2]); char kind = argv[3][0]; rng_seed(argc > 4 ? strtoull(argv[4], 0, 10) : 1);
    n = 1 << N; K2 = 2 * k; NL = K2 + (argc > 5 && argv[5][0] == 'o');
    fe basis[8];
    if (kind == 'P') for (int i = 0; i < N; i++) basis[i] = 1ull << i;
    else if (kind == 'H') { fe r = gf_rand(); basis[0] = 1; for (int i = 1; i < N; i++) basis[i] = gf_mul(basis[i - 1], r); }
    else for (int i = 0; i < N; i++) basis[i] = gf_rand();
    for (int j = 0; j < n; j++) { pts[j] = 0; for (int i = 0; i < N; i++) if ((j >> i) & 1) pts[j] ^= basis[i]; }
    for (int j = 0; j < n; j++) { pw[j][0] = 1; for (int e = 1; e < k; e++) pw[j][e] = gf_mul(pw[j][e - 1], pts[j]); }
    rec(0, 0, 0, 0, 0);
    fprintf(stderr, "N=%d k=%d labelled=%d kind=%c: labelings tested %lld (smallest labelled point in A, first of B before first of C), singular %lld\n", N, k, NL, kind, tested, found);
    return 0;
}
