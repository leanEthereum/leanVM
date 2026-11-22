// Referee 80: the mixed tree code V1 with d = 1 (row h_x = g_x + mu_x g_pi(x)), rate 1/2, T2, GF(2^64).
//   80_v1 scan <seed> <part> <parts> [mode]   exhaustive three-member scan at (4,8); mode: cross (all 576 cross-tree
//                                             permutations, split in parts), plain, sibling, mask
//   80_v1 adv <v> <seed>                      the N = 4 lift under the block-walking n-cycle, random n-cycles, cross-tree maps
//   80_v1 xor <v> <i> <seed>                  the staircase under the mask x ^ (tree bit), by encoding
//   80_v1 sub <v> <i> <seed>                  sub-lists of 3, 4, 5 members of the masked staircase (GS(2), GS(3), GS(4))
#include "80_gf.h"

static tree_t T;
static int n, k, v;

static void mixed_rows(const int *pi, const fe *mu, fe *H) { // H[x] = g_x + mu_x g_pi(x)
    for (int x = 0; x < n; x++) for (int e = 0; e < k; e++) H[(size_t)x * k + e] = T.G[(size_t)x * k + e] ^ fe_mul(mu[x], T.G[(size_t)pi[x] * k + e]);
}
static void mix_word(const int *pi, const fe *mu, const fe *c, fe *out) { for (int x = 0; x < n; x++) out[x] = c[x] ^ fe_mul(mu[x], c[pi[x]]); }
// incidence matrix of a pattern on rows R (n x k); returns weight
static int inc_matrix(const fe *R, const unsigned *cls, int L, fe *M) {
    int w = 0;
    for (int x = 0; x < n; x++) w += cls_rows(cls[x], L, R + (size_t)x * k, k, M + (size_t)w * L * k);
    return w;
}
// does the kernel (dim x L*k) contain a list: every e_l and every e_l - e_l' nonzero on some basis vector
static int kernel_has_list(const fe *Kb, int dim, int L) {
    if (dim == 0) return 0;
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) {
        int ok = 0;
        for (int d = 0; d < dim && !ok; d++) for (int e = 0; e < k && !ok; e++) {
            fe val = Kb[(size_t)d * L * k + (size_t)(b - 1) * k + e];
            if (a >= 1) val ^= Kb[(size_t)d * L * k + (size_t)(a - 1) * k + e];
            if (val) ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}
static void random_cycle(int *pi) { // uniformly random n-cycle
    int *ord = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) ord[x] = x;
    for (int x = n - 1; x > 0; x--) { int y = rnd_below(x + 1), t = ord[x]; ord[x] = ord[y]; ord[y] = t; }
    for (int x = 0; x < n; x++) pi[ord[x]] = ord[(x + 1) % n];
    free(ord);
}
static void random_perm(int *pi) {
    for (int x = 0; x < n; x++) pi[x] = x;
    for (int x = n - 1; x > 0; x--) { int y = rnd_below(x + 1), t = pi[x]; pi[x] = pi[y]; pi[y] = t; }
}
static void random_cross(int *pi) { // uniformly random permutation exchanging the two trees
    int *a = malloc(sizeof(int) * k);
    for (int h = 0; h < 2; h++) {
        for (int x = 0; x < k; x++) a[x] = x;
        for (int x = k - 1; x > 0; x--) { int y = rnd_below(x + 1), t = a[x]; a[x] = a[y]; a[y] = t; }
        for (int x = 0; x < k; x++) pi[h * k + x] = (1 - h) * k + a[x];
    }
    free(a);
}
static void agreement_classes(fe **c, int members, const fe *u, unsigned *cls) {
    for (int x = 0; x < n; x++) { cls[x] = 0; for (int l = 0; l < members; l++) if (c[l][x] == u[x]) cls[x] |= 1u << l; }
}

// ---------- scan ----------
static const unsigned C3[5] = {0, 3, 5, 6, 7};
static long scan_one(const int *pi, const fe *mu, long *maxw_list) {
    static fe H[8 * 4], M[16 * 8], Kb[8 * 8];
    unsigned cls[8];
    mixed_rows(pi, mu, H);
    long viol = 0; *maxw_list = 0;
    for (int code = 0; code < 390625; code++) {
        int c = code, w = 0;
        for (int x = 0; x < 8; x++) { cls[x] = C3[c % 5]; c /= 5; w += cls_dim(cls[x]); }
        if (w < 7) continue;
        inc_matrix(H, cls, 2, M);
        int dim = fe_kernel(M, w, 8, Kb);
        if (kernel_has_list(Kb, dim, 2)) { if (w > *maxw_list) *maxw_list = w; if (w >= 8) viol++; }
    }
    return viol;
}
static int next_perm4(int *a) {
    int i = 2; while (i >= 0 && a[i] > a[i + 1]) i--;
    if (i < 0) return 0;
    int j = 3; while (a[j] < a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = 3; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}
static int main_scan(int argc, char **argv) {
    rnd_seed(strtoull(argv[2], 0, 10)); fe_selftest();
    int part = atoi(argv[3]), parts = atoi(argv[4]);
    const char *mode = argc > 5 ? argv[5] : "cross";
    v = 2; tree_init(&T, v, 2, 2); n = T.n; k = T.k;
    int pi[8]; fe mu[8]; long mw;
    for (int x = 0; x < 8; x++) mu[x] = rnd_nz();
    if (!strcmp(mode, "plain")) { for (int x = 0; x < 8; x++) { mu[x] = 0; pi[x] = x; } long vl = scan_one(pi, mu, &mw); printf("plain code: %ld violations of GS(2), largest weight of a list %ld\n", vl, mw); return 0; }
    if (!strcmp(mode, "sibling")) { for (int x = 0; x < 8; x++) pi[x] = x ^ 1; long vl = scan_one(pi, mu, &mw); printf("V1 sibling map: %ld violations, largest weight %ld\n", vl, mw); return 0; }
    if (!strcmp(mode, "mask")) { for (int x = 0; x < 8; x++) pi[x] = x ^ 4; long vl = scan_one(pi, mu, &mw); printf("V1 mask x^4: %ld violations, largest weight %ld\n", vl, mw); return 0; }
    int s[4] = {0, 1, 2, 3}, idx = 0; long tot = 0, nperm = 0, worst = 0;
    do {
        int t[4] = {0, 1, 2, 3};
        do {
            if (idx++ % parts != part) continue;
            for (int x = 0; x < 4; x++) { pi[x] = 4 + s[x]; pi[4 + x] = t[x]; }
            for (int x = 0; x < 8; x++) mu[x] = rnd_nz();
            long vl = scan_one(pi, mu, &mw);
            tot += vl; nperm++; if (mw > worst) worst = mw;
            if (vl) { printf("cross-tree pi ="); for (int x = 0; x < 8; x++) printf(" %d", pi[x]); printf(": %ld violations\n", vl); }
        } while (next_perm4(t));
    } while (next_perm4(s));
    printf("part %d/%d: %ld cross-tree permutations scanned, %ld violations of GS(2) in all, largest weight of a list %ld (2k - 1 = 7)\n", part, parts, nperm, tot, worst);
    return 0;
}

// ---------- the N = 4 lift ----------
static void lower_rows(int i, int x, fe *g) { // lower part of the row of leaf x: layers below i
    g[0] = 1;
    for (int l = 0; l < i; l++) { fe t = T.tw[l][x >> l]; for (int e = 0; e < (1 << l); e++) g[e | (1 << l)] = fe_mul(g[e], t); }
}
static void upper_row(int i, int q, fe *g) { // top-code row of block q (layers i .. v-1), length k >> i
    g[0] = 1;
    for (int l = i; l < v; l++) { fe t = T.tw[l][q >> (l - i)]; for (int e = 0; e < (1 << (l - i)); e++) g[e | (1 << (l - i))] = fe_mul(g[e], t); }
}
static void product_codeword(int i, const fe *A, const fe *B, fe *c) { // message A (x) B, split level i
    int b = 1 << i; fe *m = malloc(sizeof(fe) * k);
    for (int e = 0; e < k; e++) m[e] = fe_mul(A[e >> i], B[e & (b - 1)]);
    tree_encode(&T, m, c); free(m);
}
// a lower factor B vanishing at the given leaves (cnt <= b - 1 of them, in any blocks); random in the kernel
static void lower_factor(int i, const int *zeros, int cnt, fe *B) {
    int b = 1 << i; fe *R = malloc(sizeof(fe) * (size_t)(cnt + 1) * b), *Kb = malloc(sizeof(fe) * (size_t)b * b);
    for (int z = 0; z < cnt; z++) lower_rows(i, zeros[z], R + (size_t)z * b);
    int d = fe_kernel(R, cnt, b, Kb);
    for (int e = 0; e < b; e++) B[e] = 0;
    for (int j = 0; j < d; j++) { fe co = j ? rnd_nz() : 1; for (int e = 0; e < b; e++) B[e] ^= fe_mul(co, Kb[(size_t)j * b + e]); }
    free(R); free(Kb);
}
static int interior_weight(const unsigned *cls, const int *pi, int *wint_classes) {
    int w = 0; for (int x = 0; x < n; x++) w += cls_dim(cls[x] & cls[pi[x]]);
    return w;
}
static int main_adv(int argc, char **argv) {
    v = atoi(argv[2]); rnd_seed(strtoull(argv[3], 0, 10)); fe_selftest();
    tree_init(&T, v, 2, 2); n = T.n; k = T.k;
    int i = v - 1, b = 1 << i, L = 2;
    fe z[4][2]; for (int q = 0; q < 4; q++) upper_row(i, q, z[q]);
    // top codeword vanishing at block q: (T_q, 1)
    fe vq[3][2]; for (int q = 0; q < 3; q++) { vq[q][0] = z[q][1]; vq[q][1] = 1; }
    // alpha v2 + beta v1 = v0
    fe det = fe_mul(vq[2][0], vq[1][1]) ^ fe_mul(vq[2][1], vq[1][0]), di = fe_inv(det);
    fe alpha = fe_mul(di, fe_mul(vq[0][0], vq[1][1]) ^ fe_mul(vq[0][1], vq[1][0]));
    fe beta = fe_mul(di, fe_mul(vq[2][0], vq[0][1]) ^ fe_mul(vq[2][1], vq[0][0]));
    fe A[3][2] = {{0, 0}, {fe_mul(alpha, vq[2][0]), fe_mul(alpha, vq[2][1])}, {fe_mul(beta, vq[1][0]), fe_mul(beta, vq[1][1])}};
    int *zeros = malloc(sizeof(int) * b), keep = 3 * b + (int)rnd_below(b), cnt = 0;
    for (int x = 3 * b; x < 4 * b; x++) if (x != keep) zeros[cnt++] = x;
    fe *B = malloc(sizeof(fe) * b); lower_factor(i, zeros, cnt, B);
    fe *c[3], *cm[3], *u = calloc(n, sizeof(fe)), *um = malloc(sizeof(fe) * n);
    for (int l = 0; l < 3; l++) { c[l] = malloc(sizeof(fe) * n); cm[l] = malloc(sizeof(fe) * n); product_codeword(i, A[l], B, c[l]); }
    for (int x = 0; x < b; x++) u[x] = c[1][x]; // block 0: members 1, 2; blocks 1, 2 and block 3: member 0 = 0
    unsigned *cls = malloc(sizeof(unsigned) * n), *clm = malloc(sizeof(unsigned) * n);
    agreement_classes(c, 3, u, cls);
    int wplain = pat_weight(cls, n);
    fe *M = malloc(sizeof(fe) * (size_t)(2 * n + 1) * L * k), *Kb = malloc(sizeof(fe) * (size_t)L * k * L * k), *H = malloc(sizeof(fe) * (size_t)n * k), *mu = malloc(sizeof(fe) * n);
    int w = inc_matrix(T.G, cls, L, M), dim = fe_kernel(M, w, L * k, Kb);
    printf("(k,n)=(%d,%d): N = 4 lift, plain weight %d (5k/2 - 2 = %d), plain kernel dimension %d, list %d\n", k, n, wplain, 5 * k / 2 - 2, dim, kernel_has_list(Kb, dim, L));
    int *pi = malloc(sizeof(int) * n), *ord = malloc(sizeof(int) * n), o = 0;
    for (int x = 0; x < b; x++) ord[o++] = x;
    for (int zz = 0; zz < cnt; zz++) ord[o++] = zeros[zz];
    for (int x = b; x < 2 * b; x++) ord[o++] = x;
    ord[o++] = keep;
    for (int x = 2 * b; x < 3 * b; x++) ord[o++] = x;
    for (int x = 0; x < n; x++) pi[ord[x]] = ord[(x + 1) % n];
    for (int trial = 0; trial < 8; trial++) {
        const char *name = trial == 0 ? "block-walking n-cycle" : trial < 4 ? "random n-cycle" : trial < 7 ? "random cross-tree permutation" : "mask x ^ (tree bit)";
        if (trial >= 1 && trial < 4) random_cycle(pi);
        if (trial >= 4 && trial < 7) random_cross(pi);
        if (trial == 7) for (int x = 0; x < n; x++) pi[x] = x ^ k;
        for (int x = 0; x < n; x++) mu[x] = rnd_nz();
        for (int l = 0; l < 3; l++) mix_word(pi, mu, c[l], cm[l]);
        mix_word(pi, mu, u, um);
        agreement_classes(cm, 3, um, clm);
        int distinct = memcmp(cm[0], cm[1], sizeof(fe) * n) && memcmp(cm[0], cm[2], sizeof(fe) * n) && memcmp(cm[1], cm[2], sizeof(fe) * n);
        int wm = pat_weight(clm, n), wi = interior_weight(cls, pi, NULL);
        mixed_rows(pi, mu, H);
        w = inc_matrix(H, clm, L, M); dim = fe_kernel(M, w, L * k, Kb);
        printf("  %-30s: V1 weight of the three encoded codewords %d (interior weight %d), distinct %d, 2k - 1 = %d, mixed kernel dim %d (2k - w = %d), list %d%s\n",
               name, wm, wi, distinct, 2 * k - 1, dim, 2 * k - wm, kernel_has_list(Kb, dim, L), wm > 2 * k - 1 ? "  ** GS(2) VIOLATED" : "");
    }
    // best possible interior weight over cross-tree permutations: 2 * max overlap of a bijection (greedy bound printed by 80_r3.py); here a direct count
    return 0;
}

// ---------- the staircase under the mask ----------
static int main_xor(int argc, char **argv, int sub) {
    v = atoi(argv[2]); int i = atoi(argv[3]); rnd_seed(strtoull(argv[4], 0, 10)); fe_selftest();
    tree_init(&T, v, 2, 2); n = T.n; k = T.k;
    int b = 1 << i, N = n / b, kup = N / 2, half = N / 2, ncos = half - 1, pick = kup / 2;
    if (b < 4) { printf("need block size >= 4\n"); return 1; }
    // zeros of B: positions 1 .. (b-2)/2 of block 0 and the same positions of block N/2 (closed under x -> x ^ k)
    int j0 = (b - 2) / 2, *zeros = malloc(sizeof(int) * b), cnt = 0;
    for (int p = 1; p <= j0; p++) { zeros[cnt++] = p; zeros[cnt++] = p ^ k; }
    fe *B = malloc(sizeof(fe) * b); lower_factor(i, zeros, cnt, B);
    fe *uup = malloc(sizeof(fe) * N); for (int q = 0; q < N; q++) uup[q] = rnd_nz();
    fe *Z = malloc(sizeof(fe) * (size_t)N * kup); for (int q = 0; q < N; q++) upper_row(i, q, Z + (size_t)q * kup);
    fe *low = malloc(sizeof(fe) * b), *u = malloc(sizeof(fe) * n);
    for (int x = 0; x < n; x++) { lower_rows(i, x, low); fe s = 0; for (int e = 0; e < b; e++) s ^= fe_mul(low[e], B[e]); u[x] = fe_mul(uup[x >> i], s); }
    // members: unions S of `pick` cosets {q, q + N/2}, q = 1 .. N/2 - 1 (coset 0 is reserved for the zeros of B)
    int maxm = sub ? 5 : 100000, members = 0;
    fe **c = malloc(sizeof(fe *) * 200000);
    fe *Sys = malloc(sizeof(fe) * (size_t)kup * (kup + 1)), *A = malloc(sizeof(fe) * kup);
    int *pc = malloc(sizeof(int) * (kup + 1));
    int limit_cosets = sub ? pick + 1 : ncos; // sub-lists: all members inside pick + 1 cosets
    for (unsigned mask = 0; mask < (1u << limit_cosets) && members < maxm; mask++) {
        if (popc(mask) != pick) continue;
        int r = 0;
        for (int q = 1; q < half; q++) if ((mask >> (q - 1)) & 1) for (int hh = 0; hh < 2; hh++) {
            int blk = q + hh * half;
            memcpy(Sys + (size_t)r * (kup + 1), Z + (size_t)blk * kup, sizeof(fe) * kup); Sys[(size_t)r * (kup + 1) + kup] = uup[blk]; r++;
        }
        int rk = fe_rref(Sys, kup, kup + 1, pc);
        if (rk != kup || pc[kup - 1] != kup - 1) { printf("interpolation singular\n"); return 1; }
        for (int e = 0; e < kup; e++) A[e] = Sys[(size_t)e * (kup + 1) + kup];
        c[members] = malloc(sizeof(fe) * n); product_codeword(i, A, B, c[members]); members++;
    }
    int *pi = malloc(sizeof(int) * n); fe *mu = malloc(sizeof(fe) * n), *um = malloc(sizeof(fe) * n);
    fe **cm = malloc(sizeof(fe *) * members); for (int l = 0; l < members; l++) cm[l] = malloc(sizeof(fe) * n);
    printf("(k,n)=(%d,%d), N = %d blocks of %d, %d zeros of B, %d members\n", k, n, N, b, cnt, members);
    for (int trial = 0; trial < 6; trial++) {
        const char *name = trial == 0 ? "plain code (mu = 0)" : trial == 1 ? "mask x ^ (tree bit)" : trial < 4 ? "random permutation" : "random cross-tree permutation";
        if (trial <= 1) for (int x = 0; x < n; x++) pi[x] = x ^ k;
        else if (trial < 4) random_perm(pi); else random_cross(pi);
        for (int x = 0; x < n; x++) mu[x] = trial == 0 ? 0 : rnd_nz();
        for (int l = 0; l < members; l++) mix_word(pi, mu, c[l], cm[l]);
        mix_word(pi, mu, u, um);
        int amin = n, amax = 0; long sum = 0; int distinct = 1;
        for (int l = 0; l < members; l++) { int a = 0; for (int x = 0; x < n; x++) a += cm[l][x] == um[x]; if (a < amin) amin = a; if (a > amax) amax = a; sum += a; }
        for (int l = 1; l < members && distinct; l++) if (!memcmp(cm[l], cm[l - 1], sizeof(fe) * n)) distinct = 0;
        if (!sub) {
            printf("  %-30s: agreement min %d max %d, sum %ld, GS bound n + (M-1)k - 1 = %ld, consecutive members distinct %d%s\n", name, amin, amax, sum, (long)n + (long)(members - 1) * k - 1, distinct, sum > (long)n + (long)(members - 1) * k - 1 ? "  ** GS VIOLATED" : "");
        } else {
            for (int m = 3; m <= members; m++) { // sub-list of the first m members
                int w = 0; for (int x = 0; x < n; x++) { int cx = 0; for (int l = 0; l < m; l++) cx += cm[l][x] == um[x]; if (cx > 1) w += cx - 1; }
                printf("  %-30s: first %d members: weight %d, Lk - 1 = %d%s\n", name, m, w, (m - 1) * k - 1, w > (m - 1) * k - 1 ? "  ** GS VIOLATED" : "");
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 5 && !strcmp(argv[1], "scan")) return main_scan(argc, argv);
    if (argc >= 4 && !strcmp(argv[1], "adv")) return main_adv(argc, argv);
    if (argc >= 5 && !strcmp(argv[1], "xor")) return main_xor(argc, argv, 0);
    if (argc >= 5 && !strcmp(argv[1], "sub")) return main_xor(argc, argv, 1);
    printf("usage: see the header of 80_v1.c\n");
    return 1;
}
