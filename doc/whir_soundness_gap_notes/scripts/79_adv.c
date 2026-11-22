// Note 79, Section 3 check (ii): V1 with d = 1 and an n-cycle that walks through the blocks of the three-member
// lift at N = 4 (rate 1/2) carries a list of weight 5k/2 - 5 = 2k - 1 + (k/2 - 4); a uniformly random n-cycle does not.
// usage: 79_adv v seed
#include "75_gf.h"
#define MAXN 128
#define MAXK 64
static int v, n, k;
static fe g[MAXN][MAXK], h[MAXN][MAXK];
static int solve(const int *cls, int *list) {
    static fe A[2 * MAXN * 2 * MAXK], Kb[2 * MAXK * 2 * MAXK]; int piv[2 * MAXK]; int C = 2 * k, R = 0;
    for (int x = 0; x < n; x++) { int c = cls[x]; if (!c) continue;
        if (c == 1 || c == 4) { for (int e = 0; e < k; e++) { A[R * C + e] = h[x][e]; A[R * C + k + e] = 0; } R++; }
        if (c == 2 || c == 4) { for (int e = 0; e < k; e++) { A[R * C + e] = 0; A[R * C + k + e] = h[x][e]; } R++; }
        if (c == 3) { for (int e = 0; e < k; e++) { A[R * C + e] = h[x][e]; A[R * C + k + e] = h[x][e]; } R++; } }
    gf_rref(A, R, C, piv); int dim = gf_kernel_from_rref(A, C, piv, Kb), n1 = 0, n2 = 0, n3 = 0;
    for (int b = 0; b < dim; b++) for (int e = 0; e < k; e++) { fe a = Kb[b * C + e], c2 = Kb[b * C + k + e]; if (a) n1 = 1; if (c2) n2 = 1; if (a ^ c2) n3 = 1; }
    *list = n1 && n2 && n3; return dim;
}
static void mix(const int *pi, const fe *mu) { for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) h[x][e] = g[x][e] ^ gf_mul(mu[x], g[pi[x]][e]); }
int main(int argc, char **argv) {
    if (argc < 3) { printf("usage: v seed\n"); return 1; }
    v = atoi(argv[1]); rng_seed(strtoull(argv[2], 0, 0)); n = 2 << v; k = 1 << v; gf_selftest();
    static fe tw[8][MAXN]; for (int l = 0; l < v; l++) for (int p = 0; p < (n >> l); p++) tw[l][p] = rnd();
    for (int y = 0; y < n; y++) for (int e = 0; e < k; e++) { fe a = 1; for (int l = 0; l < v; l++) if ((e >> l) & 1) a = gf_mul(a, tw[l][y >> l]); g[y][e] = a; }
    int bs = k / 2, J = bs - 1, order[MAXN], m = 0, cls[MAXN], plain[MAXN], pi[MAXN]; fe mu[MAXN];
    for (int t = 0; t < bs; t++) order[m++] = t;                 // block 0
    for (int t = 0; t < J; t++) order[m++] = 3 * bs + t;         // zeros of B, in block 3
    for (int t = 0; t < bs; t++) order[m++] = bs + t;            // block 1
    order[m++] = 3 * bs + J;                                     // leftover leaf of block 3
    for (int t = 0; t < bs; t++) order[m++] = 2 * bs + t;        // block 2
    for (int x = 0; x < n; x++) { plain[x] = 0; cls[x] = 0; mu[x] = rnd() | 1; }
    for (int t = 0; t < bs; t++) { plain[t] = 1; plain[bs + t] = 2; plain[2 * bs + t] = 3; }
    for (int t = 0; t < J; t++) plain[3 * bs + t] = 4;
    // plain tree code: the lift pattern
    for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) h[x][e] = g[x][e];
    int list, dim = solve(plain, &list), w = 0; for (int x = 0; x < n; x++) w += plain[x] == 4 ? 2 : plain[x] ? 1 : 0;
    printf("(k,n)=(%d,%d): plain lift pattern weight %d (2k-1 = %d), kernel dim %d, list %d\n", k, n, w, 2 * k - 1, dim, list);
    // adversarial cycle: class at x = the part of the plain class at x that also holds at pi(x)
    for (int j = 0; j < n; j++) pi[order[j]] = order[(j + 1) % n];
    for (int x = 0; x < n; x++) { int a = plain[x], b = plain[pi[x]]; cls[x] = (a == b) ? a : (a == 4 ? b : (b == 4 ? a : 0)); }
    mix(pi, mu); dim = solve(cls, &list); w = 0; for (int x = 0; x < n; x++) w += cls[x] == 4 ? 2 : cls[x] ? 1 : 0;
    printf("  V1, d = 1, cycle through the blocks: interior pattern weight %d = 2k - 1 + %d, kernel dim %d, list %d\n", w, w - 2 * k + 1, dim, list);
    // uniformly random n-cycle, same recipe
    int o[MAXN]; for (int i = 0; i < n; i++) o[i] = i; for (int i = n - 1; i > 0; i--) { int j = (int)rnd_below(i + 1), t = o[i]; o[i] = o[j]; o[j] = t; }
    for (int j = 0; j < n; j++) pi[o[j]] = o[(j + 1) % n];
    for (int x = 0; x < n; x++) { int a = plain[x], b = plain[pi[x]]; cls[x] = (a == b) ? a : (a == 4 ? b : (b == 4 ? a : 0)); }
    mix(pi, mu); dim = solve(cls, &list); w = 0; for (int x = 0; x < n; x++) w += cls[x] == 4 ? 2 : cls[x] ? 1 : 0;
    printf("  V1, d = 1, random n-cycle: interior pattern weight %d, kernel dim %d (2k - weight = %d), list %d\n", w, dim, 2 * k - w, list);
    return 0;
}
