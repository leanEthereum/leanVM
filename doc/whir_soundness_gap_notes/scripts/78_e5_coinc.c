// Note 78, experiment 5(c): planted coincidences in the top twiddles (note 69 Section 8) and what they waste in a variant.
// usage: 78_e5_coinc v r depth seed spec...
// depth 1: two equal top twiddles in trees 0 and 1 (blocks = half trees 0 and 2). depth j >= 2: 2^j random blocks of
// k/2^j leaves, one twiddle of layer v-j solved so that the minor of the top code on them vanishes. The top code is the one of
// the code WITHOUT the mixing: for V2 the rows of tree t are read through the action of M_t on the top bits, which exists
// when M_t preserves the low bits at that level (otherwise the tree-code minor is used and the line says so).
// Reported: the nullity of the unmixed code on the k planted leaves (the family F), the leaves Z' on which all of F vanishes
// in the full variant, the waste min(|Z'|, k) - rank on Z', the waste after adding to Z' the largest groups of leaves whose
// functionals on F are proportional (for V1: a leaf of the planted blocks and its partner outside them whose own partner is
// inside), and the largest waste over 40000 random leaf sets.
#include "78_var.h"
static fe det(const fe *A, int m) {
    fe *M = malloc(sizeof(fe) * m * m), d = 1; memcpy(M, A, sizeof(fe) * m * m);
    for (int c = 0; c < m; c++) {
        int p = -1; for (int i = c; i < m; i++) if (M[i * m + c]) { p = i; break; }
        if (p < 0) { free(M); return 0; }
        if (p != c) for (int j = 0; j < m; j++) { fe t = M[p * m + j]; M[p * m + j] = M[c * m + j]; M[c * m + j] = t; }
        d = gf_mul(d, M[c * m + c]); fe inv = gf_inv(M[c * m + c]);
        for (int i = c + 1; i < m; i++) { fe f = gf_mul(M[i * m + c], inv); if (f) for (int j = c; j < m; j++) M[i * m + j] ^= gf_mul(f, M[c * m + j]); }
    }
    free(M); return d;
}
static int quotient_ok;
static void top_rows(const var_t *V, int lo, const int *P, int ku, fe *A) {
    fe row[1 << MAXV]; int v = V->v;
    for (int a = 0; a < ku; a++) {
        tree_row(&V->T, P[a] << lo, row); int t = (P[a] << lo) >> v;
        for (int e = 0; e < ku; e++) { int idx = e << lo; if (V->hasM && t && quotient_ok) idx = (f2_apply(V->M[t], v, e << lo) >> lo) << lo; A[a * ku + e] = row[idx]; }
    }
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), j = atoi(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10); gf_init();
    for (int a = 5; a < argc; a++) {
        rng_seed(seed); var_t V; if (!var_make(&V, argv[a], v, r)) { printf("bad spec\n"); return 1; }
        int n = V.n, k = V.k, lo = v - j, ku = 1 << j, N = n >> lo, bs = 1 << lo, P[64];
        quotient_ok = 1;
        if (V.hasM) for (int t = 1; t < (1 << r); t++) for (int l = lo; l < v; l++) if (V.M[t][l] & ((1u << lo) - 1)) quotient_ok = 0;
        fe *A = malloc(sizeof(fe) * ku * ku);
        if (j == 1) { P[0] = 0; P[1] = 2; V.T.tw[v - 1][2] = V.T.tw[v - 1][0]; }
        else for (;;) {
            int used[1024] = {0}; for (int b = 0; b < ku; b++) { int p; do p = (int)rng_below(N); while (used[p]); used[p] = 1; P[b] = p; }
            int q = P[ku - 1]; fe *slot = &V.T.tw[lo][q], saved = *slot;
            *slot = 0; top_rows(&V, lo, P, ku, A); fe d0 = det(A, ku);
            *slot = 1; top_rows(&V, lo, P, ku, A); fe d1 = det(A, ku);
            if (d0 == d1) { *slot = saved; continue; }
            *slot = gf_mul(d0, gf_inv(d0 ^ d1));
            if (*slot == V.T.tw[lo][q ^ 1]) { *slot = saved; continue; }
            top_rows(&V, lo, P, ku, A); if (det(A, ku)) { printf("planting failed\n"); return 1; }
            break;
        }
        int dsave = V.d; V.d = 0; var_build(&V);                         // the unmixed code
        fe *M = malloc(sizeof(fe) * (size_t)n * k), *Kb = malloc(sizeof(fe) * (size_t)k * k);
        uint8_t inB[1024] = {0}; int rows = 0; for (int b = 0; b < ku; b++) for (int x = 0; x < bs; x++) inB[(P[b] << lo) + x] = 1;
        for (int x = 0; x < n; x++) if (inB[x]) memcpy(M + (size_t)rows++ * k, V.G + (size_t)x * k, sizeof(fe) * k);
        int f = gf_kernel(M, rows, k, Kb);
        V.d = dsave; var_build(&V);                                      // the full variant
        uint8_t inZ[1024] = {0}; int zc = 0; rows = 0;
        for (int x = 0; x < n; x++) { int all = (f > 0); for (int b = 0; b < f && all; b++) { fe s = 0; for (int e = 0; e < k; e++) s ^= gf_mul(V.G[(size_t)x * k + e], Kb[(size_t)b * k + e]); all = (s == 0); } inZ[x] = (uint8_t)all; zc += all; }
        for (int x = 0; x < n; x++) if (inZ[x]) memcpy(M + (size_t)rows++ * k, V.G + (size_t)x * k, sizeof(fe) * k);
        int rkZ = rows ? gf_rank(M, rows, k) : 0, wasteZ = (zc < k ? zc : k) - rkZ;
        // leaves whose functionals on F are proportional cost F one condition together: add the largest groups to Z' up to k leaves
        int wasteG = 0, ngroups = 0, zg = zc;
        if (f > 0) {
            fe *H = calloc((size_t)n * f, sizeof(fe)); int *ord = malloc(sizeof(int) * n), no = 0; uint8_t inG[1024]; memcpy(inG, inZ, n);
            for (int x = 0; x < n; x++) { if (inZ[x]) continue; fe *h = H + (size_t)x * f;
                for (int b = 0; b < f; b++) { fe sa = 0; for (int e = 0; e < k; e++) sa ^= gf_mul(V.G[(size_t)x * k + e], Kb[(size_t)b * k + e]); h[b] = sa; }
                int b0 = 0; while (!h[b0]) b0++; fe inv = gf_inv(h[b0]); for (int b = 0; b < f; b++) h[b] = gf_mul(h[b], inv);
                ord[no++] = x; }
            int *grp = malloc(sizeof(int) * n), *gsz = calloc(n, sizeof(int)); // group id = first leaf with the same normalized functional
            for (int a = 0; a < no; a++) { int g = ord[a]; for (int b = 0; b < a; b++) if (!memcmp(H + (size_t)ord[b] * f, H + (size_t)ord[a] * f, sizeof(fe) * f)) { g = grp[ord[b]]; break; } grp[ord[a]] = g; gsz[g]++; }
            for (;;) { int bg = -1; for (int a = 0; a < no; a++) { int g = ord[a]; if (grp[g] == g && gsz[g] >= 2 && (bg < 0 || gsz[g] > gsz[bg])) bg = g; }
                if (bg < 0 || zg >= k) break;
                for (int a = 0; a < no && zg < k; a++) if (grp[ord[a]] == bg) { inG[ord[a]] = 1; zg++; }
                gsz[bg] = 0; ngroups++; }
            rows = 0; for (int x = 0; x < n; x++) if (inG[x]) memcpy(M + (size_t)rows++ * k, V.G + (size_t)x * k, sizeof(fe) * k);
            wasteG = rows ? (zg < k ? zg : k) - gf_rank(M, rows, k) : 0;
            free(H); free(ord); free(grp); free(gsz);
        }
        long tests = 0; int maxw = 0;
        for (int t = 0; t < 40000; t++) {
            uint8_t sel[1024] = {0}; rows = 0;
            int kind = t % 4;
            if (kind == 3) { for (int x = 0; x < n; x++) sel[x] = inZ[x] && rng_below(8) != 0; }
            else for (int c = (int)rng_below(2 * ku); c > 0; c--) { int lev = (int)rng_below(v), b = (int)rng_below(n >> lev); if ((kind == 1) && !inB[b << lev]) continue; for (int x = 0; x < (1 << lev); x++) sel[(b << lev) + x] = 1; }
            if (kind == 2 && V.d) { for (int x = 0; x < n; x++) if (sel[x]) sel[V.pi[0][x]] = 1; }
            for (int c = (int)rng_below(k); c > 0; c--) sel[rng_below(n)] = 1;
            for (int x = 0; x < n; x++) if (sel[x]) memcpy(M + (size_t)rows++ * k, V.G + (size_t)x * k, sizeof(fe) * k);
            int sz = rows, rk = gf_rank(M, rows, k), w = (sz < k ? sz : k) - rk; tests++; if (w > maxw) maxw = w;
        }
        printf("(k,n)=(%d,%d) depth %d (one block = %d leaves) %-12s%s: unmixed code: nullity %d on the %d planted leaves | full variant: the family vanishes on %d leaves, waste there %d | with %d groups of leaves that F sees proportionally (%d leaves in all): waste %d | largest waste over %ld random leaf sets: %d\n",
               k, n, j, bs, argv[a], (V.hasM && !quotient_ok) ? " [tree-code minor]" : "", f, k, zc, wasteZ, ngroups, zg, wasteG, tests, maxw > wasteZ ? maxw : wasteZ);
        free(A); free(M); free(Kb); var_free(&V);
    }
    return 0;
}
