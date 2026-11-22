// Referee 75: independent test of note 74, Theorem 4.2 and Corollary 4.3 (the properties Q_t), over GF(2^64) with random twiddles.
// usage: 75_qt v r L variant(1|2) mode(E|S|F) trials seed
//   E: exhaustive over all patterns with |X| = L k leaves, one pair per leaf, every pair used at most k - 1 times (one draw of the code)
//   S: sampled patterns (random, recursive block structure, sibling copies), |X| in [Lk - 2, Lk + 1]; a list is built from every genuine kernel
//   F: lifted lists A (x) B at every split level; the codewords are encoded by butterflies and their coincidences counted
// A "violation" is: (thm) kernel genuine for every pair used and rows dependent; (cor) t distinct codewords with more than (s-1)k - 1
// coincidence leaves on some sub-list of s members.
#include "75_gf.h"
#define MAXN 256
#define MAXC 96
static int v, r, n, k, L, variant, P, cols;
static fe *tw[10], *G;
static int pa[64], pb[64];
static void gen_code(void) {
    for (int i = 0; i < v; i++) for (int q = 0; q < (n >> i); q++) {
        if (variant == 1 && (q & 1)) tw[i][q] = tw[i][q - 1] ^ 1;
        else do tw[i][q] = rnd(); while ((q & 1) && tw[i][q] == tw[i][q - 1]);
    }
    for (int j = 0; j < n; j++) { fe *g = G + (size_t)j * k; g[0] = 1;
        for (int i = 0; i < v; i++) { fe x = tw[i][j >> i]; for (int e = 0; e < (1 << i); e++) g[e + (1 << i)] = gf_mul(g[e], x); } }
}
// butterfly encoder, independent of G: node q at level i holds the partial evaluation, a table of 2^i coefficients
static void encode(const fe *m, fe *c) {
    static fe A[2][MAXN]; int cur = 0;
    for (int T = 0; T < (n >> v); T++) memcpy(A[0] + (size_t)T * k, m, sizeof(fe) * k);
    for (int i = v; i >= 1; i--) { int h = 1 << (i - 1);
        for (int q = 0; q < (n >> i); q++) for (int b = 0; b < 2; b++) { int qq = 2 * q + b; fe t = tw[i - 1][qq];
            for (int e = 0; e < h; e++) A[cur ^ 1][qq * h + e] = A[cur][(q << i) + e] ^ gf_mul(t, A[cur][(q << i) + e + h]); }
        cur ^= 1; }
    memcpy(c, A[cur], sizeof(fe) * n);
}
static int st_maxw; static long st_trials, st_dep, st_gen_used, st_viol_thm, st_gen_all, st_lists, st_viol_cor, st_tight, st_square_def; static int st_maxco;
static fe Mx[(MAXN + 4) * MAXC], Kb[MAXC * MAXC], cw[8][MAXN];
static void build_row(fe *row, int x, int p) { memset(row, 0, sizeof(fe) * cols);
    if (pa[p]) memcpy(row + (pa[p] - 1) * k, G + (size_t)x * k, sizeof(fe) * k);
    if (pb[p]) memcpy(row + (pb[p] - 1) * k, G + (size_t)x * k, sizeof(fe) * k); }
static int pair_genuine(const fe *w, int p) { // d_a != d_b on the vector w
    for (int e = 0; e < k; e++) { fe s = 0; if (pa[p]) s ^= w[(pa[p] - 1) * k + e]; if (pb[p]) s ^= w[(pb[p] - 1) * k + e]; if (s) return 1; }
    return 0; }
// counts coincidence leaves of the list 0, d_1..d_L (rows of w) on every sub-list; returns 1 on a violation of Corollary 4.3
static int check_list(const fe *w, int *co_all) {
    static fe zero[MAXN]; memcpy(cw[0], zero, sizeof(fe) * n);
    for (int l = 1; l <= L; l++) encode(w + (l - 1) * k, cw[l]);
    for (int j = 0; j < n; j++) { fe s = 0; for (int l = 1; l <= L; l++) { const fe *d = w + (l - 1) * k; fe a = 0; for (int e = 0; e < k; e++) a ^= gf_mul(d[e], G[(size_t)j * k + e]); if (a != cw[l][j]) { printf("encoder mismatch\n"); exit(1); } s ^= a; } (void)s; }
    int bad = 0; *co_all = 0;
    for (int T = 3; T < (1 << (L + 1)); T++) { int s = __builtin_popcount(T); if (s < 2) continue; int co = 0;
        for (int j = 0; j < n; j++) { int hit = 0; for (int a = 0; a <= L && !hit; a++) if ((T >> a) & 1) for (int b = a + 1; b <= L; b++) if (((T >> b) & 1) && cw[a][j] == cw[b][j]) { hit = 1; break; } co += hit; }
        if (co > (s - 1) * k - 1) bad = 1; if (T == (1 << (L + 1)) - 1) *co_all = co; }
    return bad; }
static void analyze(const int *pat) {
    int X[MAXN], nx = 0, used[64] = {0}; for (int x = 0; x < n; x++) if (pat[x] >= 0) { X[nx++] = x; used[pat[x]] = 1; }
    if (!nx) return; st_trials++;
    for (int a = 0; a < nx; a++) build_row(Mx + (size_t)a * cols, X[a], pat[X[a]]);
    int piv[MAXC]; int rk = gf_rref(Mx, nx, cols, piv); int dim = gf_kernel_from_rref(Mx, cols, piv, Kb);
    int gen_used = dim > 0, gen_all = dim > 0;
    for (int p = 0; p < P; p++) { int g = 0; for (int t = 0; t < dim && !g; t++) g = pair_genuine(Kb + (size_t)t * cols, p); if (!g) { gen_all = 0; if (used[p]) gen_used = 0; } }
    if (rk < nx) st_dep++;
    if (gen_used) { st_gen_used++; if (rk < nx) { st_viol_thm++; if (st_viol_thm <= 3) printf("THEOREM VIOLATION: |X|=%d rank=%d pattern:", nx, rk); if (st_viol_thm <= 3) for (int x = 0; x < n; x++) if (pat[x] >= 0) printf(" %d:%d%d", x, pa[pat[x]], pb[pat[x]]); if (st_viol_thm <= 3) printf("\n"); } }
    if (gen_all) { st_gen_all++; fe w[MAXC]; memset(w, 0, sizeof(w));
        for (int t = 0; t < dim; t++) { fe c = rnd() | 1; for (int j = 0; j < cols; j++) w[j] ^= gf_mul(c, Kb[(size_t)t * cols + j]); }
        int distinct = 1; for (int p = 0; p < P; p++) if (!pair_genuine(w, p)) distinct = 0;
        if (distinct) { int co; st_lists++; if (check_list(w, &co)) { st_viol_cor++; if (st_viol_cor <= 2) { printf("COROLLARY VIOLATION: %d coincidence leaves > Lk-1 = %d (or a sub-list), |X|=%d rank=%d pattern:", co, cols - 1, nx, rk); for (int x = 0; x < n; x++) if (pat[x] >= 0) printf(" %d:%d%d", x, pa[pat[x]], pb[pat[x]]); printf("\n"); } }
            if (co > st_maxco) st_maxco = co; if (co == cols - 1) st_tight++; } }
}
// exhaustive: DFS over leaves, |X| = Lk exactly, pair counts <= k - 1
static int epat[MAXN], ecnt[64]; static long e_total;
static void edfs(int x, int placed) {
    if (placed == cols) { for (int y = x; y < n; y++) epat[y] = -1; e_total++;
        static fe Sq[MAXC * MAXC]; int a = 0; for (int y = 0; y < n; y++) if (epat[y] >= 0) build_row(Sq + (size_t)(a++) * cols, y, epat[y]);
        if (gf_rank(Sq, cols, cols) < cols) { st_square_def++; analyze(epat); } return; }
    if (n - x < cols - placed) return;
    epat[x] = -1; edfs(x + 1, placed);
    for (int p = 0; p < P; p++) if (ecnt[p] < k - 1) { epat[x] = p; ecnt[p]++; edfs(x + 1, placed + 1); ecnt[p]--; }
    epat[x] = -1;
}
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void rec_fill(int *pat, int i, int q, double pc, double dens) {
    if (i == 0) { pat[q] = urand() < dens ? (int)rnd_below(P) : -1; return; }
    if (urand() < pc) { int p = urand() < dens ? (int)rnd_below(P) : -1; for (int x = q << i; x < ((q + 1) << i); x++) pat[x] = p; return; }
    rec_fill(pat, i - 1, 2 * q, pc, dens); rec_fill(pat, i - 1, 2 * q + 1, pc, dens);
}
static void gen_pattern(int *pat, int target, int style, int repair) {
    for (int x = 0; x < n; x++) pat[x] = -1;
    if (style == 1) { double pc = 0.15 + 0.5 * urand(); for (int T = 0; T < (n >> v); T++) rec_fill(pat, v, T, pc, (double)target / n); }
    else if (style == 2) { int blk = 1 << rnd_below(v + 1); for (int x = 0; x < n; x++) { if ((int)rnd_below(n) >= target) continue; pat[x] = ((x % blk) && pat[x - 1] >= 0 && rnd_below(4) < 3) ? pat[x - 1] : (int)rnd_below(P); } }
    int cnt = 0; for (int x = 0; x < n; x++) cnt += pat[x] >= 0;
    while (cnt > target) { int x = rnd_below(n); if (pat[x] >= 0) { pat[x] = -1; cnt--; } }
    while (cnt < target) { int x = rnd_below(n); if (pat[x] < 0) { int s = x ^ 1; pat[x] = (style && pat[s] >= 0 && rnd_below(2)) ? pat[s] : (int)rnd_below(P); cnt++; } }
    if (repair) for (int it = 0; it < 4 * n; it++) { int c[64] = {0}, worst = -1; for (int x = 0; x < n; x++) if (pat[x] >= 0) c[pat[x]]++;
        for (int p = 0; p < P; p++) if (c[p] > k - 1) worst = p; if (worst < 0) break;
        int x; do x = rnd_below(n); while (pat[x] != worst); int low = 0; for (int p = 1; p < P; p++) if (c[p] < c[low]) low = p; pat[x] = low; }
}
// lifted list at split level i: top list from a top pattern of L*kup - 1 block coincidences, B with 2^i - 1 zeros
static void lifted(int i, int zeros_outside) {
    int kup = k >> i, N = n >> i, cu = L * kup, lo = 1 << i; if (cu - 1 > N && kup > 1) return;
    fe A[MAXC]; memset(A, 0, sizeof(A)); int blockhit[MAXN] = {0};
    if (kup == 1) { for (int l = 0; l < L; l++) A[l] = rnd() | 1; }
    else { int bp[MAXN], c[64] = {0}, tries = 0;
        for (int q = 0; q < N; q++) bp[q] = -1;
        for (int placed = 0; placed < cu - 1 && tries < 100000; tries++) { int q = rnd_below(N), p = rnd_below(P); if (bp[q] >= 0 || c[p] >= kup - 1) continue; bp[q] = p; c[p]++; placed++; }
        static fe Tm[MAXN * MAXC], Tk[MAXC * MAXC]; int nr = 0;
        for (int q = 0; q < N; q++) if (bp[q] >= 0) { fe *row = Tm + (size_t)nr * cu; memset(row, 0, sizeof(fe) * cu); blockhit[q] = 1;
            for (int s = 0; s < 2; s++) { int m = s ? pb[bp[q]] : pa[bp[q]]; if (m) for (int e = 0; e < kup; e++) row[(m - 1) * kup + e] = G[(size_t)(q << i) * k + (e << i)]; } nr++; }
        int piv[MAXC]; gf_rref(Tm, nr, cu, piv); int dim = gf_kernel_from_rref(Tm, cu, piv, Tk); if (!dim) return;
        for (int t = 0; t < dim; t++) { fe cc = rnd() | 1; for (int j = 0; j < cu; j++) A[j] ^= gf_mul(cc, Tk[(size_t)t * cu + j]); } }
    // B: 2^i - 1 zeros at random leaves (outside the coincidence blocks if asked and possible)
    static fe Bm[MAXN * MAXC], Bk[MAXC * MAXC]; fe B[MAXC]; int nz = 0, guard = 0;
    while (nz < lo - 1 && guard++ < 100000) { int x = rnd_below(n); if (zeros_outside && blockhit[x >> i]) continue; memcpy(Bm + (size_t)nz * lo, G + (size_t)x * k, sizeof(fe) * lo); nz++; }
    int piv[MAXC]; gf_rref(Bm, nz, lo, piv); int dim = gf_kernel_from_rref(Bm, lo, piv, Bk); memset(B, 0, sizeof(B));
    for (int t = 0; t < dim; t++) { fe cc = rnd() | 1; for (int j = 0; j < lo; j++) B[j] ^= gf_mul(cc, Bk[(size_t)t * lo + j]); }
    fe w[MAXC]; for (int l = 0; l < L; l++) for (int e = 0; e < k; e++) w[l * k + e] = gf_mul(A[l * kup + (e >> i)], B[e & (lo - 1)]);
    int distinct = 1; for (int p = 0; p < P; p++) if (!pair_genuine(w, p)) distinct = 0; if (!distinct) return;
    int co; st_lists++; if (check_list(w, &co)) { st_viol_cor++; if (st_viol_cor <= 2) printf("COROLLARY VIOLATION (lift at level %d): %d coincidence leaves > %d\n", i, co, cols - 1); }
    if (co > st_maxco) st_maxco = co; if (co == cols - 1) st_tight++;
    int wt = 0; for (int j = 0; j < n; j++) { int best = 1; for (int a = 0; a <= L; a++) { int c = 0; for (int b = 0; b <= L; b++) c += cw[a][j] == cw[b][j]; if (c > best) best = c; } wt += best - 1; }
    if (wt > st_maxw) st_maxw = wt;
}
// one-sided staircase of note 74, Proposition 6.1, at split level i: all members A_S (x) B, S a kup-subset of the blocks other than q0
static void staircase(int i, long maxmem, int sub_t, long sub_trials) {
    int kup = k >> i, N = n >> i, lo = 1 << i, q0 = (int)rnd_below(N); if (kup < 1 || kup > N - 1) { printf("no staircase at this level\n"); return; }
    static fe Bm[MAXN * MAXC], Bk[MAXC * MAXC]; fe B[MAXC], beta[MAXN], y[MAXN];
    for (int z = 0; z < lo - 1; z++) memcpy(Bm + (size_t)z * lo, G + (size_t)((q0 << i) + z) * k, sizeof(fe) * lo);
    int piv[MAXC]; gf_rref(Bm, lo - 1, lo, piv); int dim = gf_kernel_from_rref(Bm, lo, piv, Bk); if (dim != 1) { printf("unexpected kernel of B: %d\n", dim); return; } memcpy(B, Bk, sizeof(fe) * lo);
    for (int q = 0; q < N; q++) beta[q] = rnd();
    for (int j = 0; j < n; j++) { fe bj = 0; for (int e = 0; e < lo; e++) bj ^= gf_mul(B[e], G[(size_t)j * k + e]); y[j] = (j >> i) == q0 ? 0 : gf_mul(beta[j >> i], bj); }
    fe *cws = malloc(sizeof(fe) * (size_t)maxmem * n); long mem = 0; int idx[MAXC], others[MAXN], no = 0, minag = n + 1, maxag = 0; long singular = 0;
    for (int q = 0; q < N; q++) if (q != q0) others[no++] = q;
    for (int a = 0; a < kup; a++) idx[a] = a;
    for (;;) {
        fe Tm[MAXC * (MAXC + 1)]; int tp[MAXC + 1];
        for (int a = 0; a < kup; a++) { int q = others[idx[a]]; for (int e = 0; e < kup; e++) Tm[a * (kup + 1) + e] = G[(size_t)(q << i) * k + (e << i)]; Tm[a * (kup + 1) + kup] = beta[q]; }
        int rk = gf_rref(Tm, kup, kup + 1, tp);
        if (rk < kup || tp[kup] >= 0) singular++;
        else { fe m[MAXC]; for (int e = 0; e < k; e++) m[e] = gf_mul(Tm[tp[e >> i] * (kup + 1) + kup], B[e & (lo - 1)]);
            encode(m, cws + (size_t)mem * n); int ag = 0; for (int j = 0; j < n; j++) ag += cws[(size_t)mem * n + j] == y[j]; if (ag < minag) minag = ag; if (ag > maxag) maxag = ag; mem++; }
        if (mem >= maxmem) break;
        int a = kup - 1; while (a >= 0 && idx[a] == no - kup + a) a--; if (a < 0) break; idx[a]++; for (int b = a + 1; b < kup; b++) idx[b] = idx[b - 1] + 1;
    }
    long dup = 0; for (long a = 1; a < mem && a < 3000; a++) for (long b = 0; b < a; b++) if (!memcmp(cws + (size_t)a * n, cws + (size_t)b * n, sizeof(fe) * n)) dup++;
    int maxco = 0; long viol = 0;
    for (long tr = 0; tr < sub_trials && mem >= sub_t; tr++) { long pick[8]; for (int a = 0; a < sub_t; a++) { int ok; do { pick[a] = (long)rnd_below(mem); ok = 1; for (int b = 0; b < a; b++) if (pick[b] == pick[a]) ok = 0; } while (!ok); }
        int co = 0; for (int j = 0; j < n; j++) { int hit = 0; for (int a = 0; a < sub_t && !hit; a++) for (int b = a + 1; b < sub_t; b++) if (cws[(size_t)pick[a] * n + j] == cws[(size_t)pick[b] * n + j]) { hit = 1; break; } co += hit; }
        if (co > maxco) maxco = co; if (co > (sub_t - 1) * k - 1) viol++; }
    printf("T%d (k,n)=(%d,%d) one-sided staircase, split level %d (N=%d blocks, kup=%d): %ld members (singular interpolations %ld, duplicates among the first 3000: %ld), agreement with the word min %d max %d (k + n/N - 1 = %d); %ld random sub-lists of %d members: largest number of coincidence leaves %d against (t-1)k - 1 = %d, violations %ld\n",
        variant, k, n, i, N, kup, mem, singular, dup, minag, maxag, k + lo - 1, sub_trials, sub_t, maxco, (sub_t - 1) * k - 1, viol);
    free(cws);
}
int main(int argc, char **argv) {
    if (argc < 8) { printf("usage: 75_qt v r L variant mode trials seed\n"); return 1; }
    v = atoi(argv[1]); r = atoi(argv[2]); L = atoi(argv[3]); variant = atoi(argv[4]); char mode = argv[5][0]; long trials = atol(argv[6]); rng_seed(strtoull(argv[7], 0, 10));
    gf_selftest(); n = 1 << (v + r); k = 1 << v; cols = L * k; P = 0;
    if (n > MAXN || cols > MAXC) { printf("too large\n"); return 1; }
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) { pa[P] = a; pb[P] = b; P++; }
    for (int i = 0; i < v; i++) tw[i] = malloc(sizeof(fe) * (n >> i)); G = malloc(sizeof(fe) * (size_t)n * k); gen_code();
    if (mode == 'E') { edfs(0, 0); printf("T%d (k,n)=(%d,%d) members=%d EXHAUSTIVE square patterns (pair counts <= k-1): %ld patterns, rank deficient %ld, genuine for used pairs %ld, THEOREM VIOLATIONS %ld, lists of distinct codewords %ld, COROLLARY VIOLATIONS %ld\n", variant, k, n, L + 1, e_total, st_square_def, st_gen_used, st_viol_thm, st_lists, st_viol_cor); }
    else if (mode == 'S') { int pat[MAXN];
        for (long tr = 0; tr < trials; tr++) { if (tr % 5000 == 0) gen_code(); int target = cols - 2 + (int)rnd_below(4); if (target > n) target = n; gen_pattern(pat, target, (int)rnd_below(3), (int)rnd_below(4) != 0); analyze(pat); }
        printf("T%d (k,n)=(%d,%d) members=%d SAMPLED: %ld patterns, rows dependent %ld, genuine for used pairs %ld, THEOREM VIOLATIONS %ld, genuine for all pairs %ld, lists built %ld, largest number of coincidence leaves %d (Lk-1 = %d, reached by %ld lists), COROLLARY VIOLATIONS %ld\n", variant, k, n, L + 1, st_trials, st_dep, st_gen_used, st_viol_thm, st_gen_all, st_lists, st_maxco, cols - 1, st_tight, st_viol_cor); }
    else if (mode == 'O') { for (int i = 1; i < v; i++) for (int t = 3; t <= 5; t++) staircase(i, 40000, t, trials); }
    else { for (long tr = 0; tr < trials; tr++) { if (tr % 2000 == 0) gen_code(); for (int i = 1; i <= v; i++) lifted(i, (int)rnd_below(2)); }
        printf("T%d (k,n)=(%d,%d) members=%d LIFTED lists, all split levels: lists %ld, largest number of coincidence leaves %d (Lk-1 = %d, reached by %ld), largest pattern weight %d (5k/2 - 2 = %d for three members), COROLLARY VIOLATIONS %ld\n", variant, k, n, L + 1, st_lists, st_maxco, cols - 1, st_tight, st_maxw, 5 * k / 2 - 2, st_viol_cor); }
    return 0;
}
