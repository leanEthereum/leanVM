// Note 82: the case k = 2 (generic 2 x n matrix, rows Lambda_x (x) (1, t_x)) for binary patterns with m members.
// Compares the exact rank over GF(2^64) with min over F_2-subspaces Theta of 2 dim Theta + sum_x dim(Lambda_x + Theta)/Theta
// (the one-level identity of note 74; for k = 2 only the sum Theta of the chosen subspaces matters).
// Build: cc -O2 -o 82_bin/82_k2 82_k2.c   (ONLY_GRAPHIC_THETA=1 in the environment restricts Theta to partitions of the members)
//   rand  m nleaves count seed kind(class|graphic|binary) minw
//   multi m n         every multiset of n proper nonzero binary subspaces on n leaves
//   planes m          every 5-subset of the graphic planes (m = 6: 20 triangles and 45 double pairs), n = 5
#define FB 64
#include "69_gf.h"
#define MAXM 8
#define MAXB 3000
#define MAXN 32
static int m, L, NB, NV;
static uint64_t smask[MAXB]; static int sdim[MAXB];
static uint64_t span_add(uint64_t s, int v) { uint64_t out = s; for (int u = 0; u < NV; u++) if ((s >> u) & 1) out |= 1ull << (u ^ v); return out; }
static uint64_t span_sum(uint64_t a, uint64_t b) { uint64_t s = a; for (int v = 1; v < NV; v++) if (((b >> v) & 1) && !((s >> v) & 1)) s = span_add(s, v); return s; }
static int dimof(uint64_t s) { return __builtin_ctzll((uint64_t)__builtin_popcountll(s)); }
static int find_mask(uint64_t s) { for (int i = 0; i < NB; i++) if (smask[i] == s) return i; return -1; }
static int memvec(int a) { return a ? 1 << (a - 1) : 0; }
static void gen_subspaces(void) {
    NB = 0; smask[NB++] = 1ull;
    for (int i = 0; i < NB; i++) for (int v = 1; v < NV; v++) { if ((smask[i] >> v) & 1) continue; uint64_t s = span_add(smask[i], v); if (find_mask(s) < 0) { if (NB >= MAXB) { fprintf(stderr, "too many\n"); exit(1); } smask[NB++] = s; } }
    for (int i = 0; i < NB; i++) sdim[i] = dimof(smask[i]);
}
static int graphic(uint64_t sm, int *isclass) {
    uint64_t s = 1ull; int par[MAXM]; for (int a = 0; a < m; a++) par[a] = a;
    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) { int v = memvec(a) ^ memvec(b); if ((sm >> v) & 1) { s = span_add(s, v); int x = a, y = b; while (par[x] != x) x = par[x]; while (par[y] != y) y = par[y]; if (x != y) par[y] = x; } }
    int big = 0; for (int a = 0; a < m; a++) { int c = 0; for (int b = 0; b < m; b++) { int y = b; while (par[y] != y) y = par[y]; c += y == a; } big += c >= 2; }
    *isclass = s == sm && big <= 1; return s == sm;
}
static fe M[MAXN * MAXM][2 * MAXM];
static int rank_k2(const uint64_t *lam, int n) {
    int cols = 2 * L, rows = 0;
    for (int x = 0; x < n; x++) { fe t = gf_rand(); uint64_t cur = 1ull;
        for (int v = 1; v < NV; v++) if (((lam[x] >> v) & 1) && !((cur >> v) & 1)) { cur = span_add(cur, v); fe *row = M[rows++]; for (int a = 0; a < L; a++) { row[2 * a] = (v >> a) & 1; row[2 * a + 1] = ((v >> a) & 1) ? t : 0; } } }
    int rk = 0;
    for (int c = 0; c < cols && rk < rows; c++) {
        int p = -1; for (int i = rk; i < rows; i++) if (M[i][c]) { p = i; break; }
        if (p < 0) continue;
        if (p != rk) for (int j = c; j < cols; j++) { fe t = M[p][j]; M[p][j] = M[rk][j]; M[rk][j] = t; }
        fe inv = gf_inv(M[rk][c]);
        for (int i = rk + 1; i < rows; i++) { fe f = M[i][c]; if (!f) continue; f = gf_mul(f, inv); for (int j = c; j < cols; j++) M[i][j] ^= gf_mul(f, M[rk][j]); }
        rk++;
    }
    return rk;
}
static int only_graphic, sgraphic[MAXB];
static int min_theta(const uint64_t *lam, int n, int *arg) {
    int best = 1 << 30;
    for (int i = 0; i < NB; i++) { if (only_graphic && !sgraphic[i]) continue; int s = 2 * sdim[i]; for (int x = 0; x < n && s < best; x++) s += dimof(span_sum(smask[i], lam[x])) - sdim[i]; if (s < best) { best = s; *arg = i; } }
    return best;
}
static void print_sub(uint64_t sm) { uint64_t cur = 1ull; int any = 0;
    for (int v = 1; v < NV; v++) if (((sm >> v) & 1) && !((cur >> v) & 1)) { cur = span_add(cur, v); if (any) printf("+"); any = 1; if (__builtin_popcount(v) & 1) printf("0"); for (int a = 1; a < m; a++) if ((v >> (a - 1)) & 1) printf("%d", a); }
    if (!any) printf("."); printf(" "); }
int main(int argc, char **argv) {
    const char *mode = argv[1]; m = atoi(argv[2]); L = m - 1; NV = 1 << L; gen_subspaces(); rng_seed(8282);
    only_graphic = getenv("ONLY_GRAPHIC_THETA") != NULL; for (int i = 0; i < NB; i++) { int ic; sgraphic[i] = graphic(smask[i], &ic); }
    uint64_t lam[MAXN]; long tot = 0, dep = 0, fail = 0, below = 0; int arg = 0;
    if (!strcmp(mode, "rand")) {
        int n = atoi(argv[3]); long count = atol(argv[4]); rng_seed(atol(argv[5])); const char *kind = argv[6]; int minw = atoi(argv[7]);
        int *cls = (int *)malloc(sizeof(int) * NB), ncls = 0;
        for (int i = 0; i < NB; i++) { int ic, g = graphic(smask[i], &ic); if (!strcmp(kind, "binary") || (!strcmp(kind, "graphic") && g) || (!strcmp(kind, "class") && ic)) cls[ncls++] = i; }
        for (long it = 0; it < count;) { int w = 0; for (int x = 0; x < n; x++) { int id = cls[rng_below(ncls)]; lam[x] = smask[id]; w += sdim[id]; } if (w < minw) continue; it++;
            int rk = rank_k2(lam, n), b = min_theta(lam, n, &arg); tot++; dep += rk < w; below += b < rk;
            if (b > rk) { fail++; if (fail <= 12) { printf("FAIL rank %d min %d w %d: ", rk, b, w); for (int x = 0; x < n; x++) print_sub(lam[x]); printf("\n"); } } }
        printf("k=2, members %d, %d leaves, random %s patterns of weight >= %d (%d kinds of leaf): patterns %ld, rows dependent %ld, min over Theta > rank %ld, below (bug) %ld\n", m, n, kind, minw, ncls, tot, dep, fail, below);
    } else if (!strcmp(mode, "multi")) { // every multiset of n proper nonzero binary subspaces
        int n = atoi(argv[3]), idx[MAXN], *pl = (int *)malloc(sizeof(int) * NB), np = 0;
        for (int i = 0; i < NB; i++) if (sdim[i] > 0 && sdim[i] < L) pl[np++] = i;
        for (int i = 0; i < n; i++) idx[i] = 0;
        for (;;) {
            int w = 0; for (int x = 0; x < n; x++) { lam[x] = smask[pl[idx[x]]]; w += sdim[pl[idx[x]]]; }
            int rk = rank_k2(lam, n); tot++;
            if (rk < w && rk < 2 * L) { dep++; int bd = min_theta(lam, n, &arg); below += bd < rk; if (bd > rk) { fail++; if (fail <= 12) { printf("FAIL rank %d min %d: ", rk, bd); for (int x = 0; x < n; x++) print_sub(lam[x]); printf("\n"); } } }
            int i = n - 1; while (i >= 0 && idx[i] == np - 1) i--; if (i < 0) break; idx[i]++; for (int j = i + 1; j < n; j++) idx[j] = idx[i];
        }
        printf("k=2, members %d, all multisets of %d proper nonzero binary subspaces (%d kinds): %ld, rank below min(w, 2L): %ld, min over Theta > rank: %ld, below (bug) %ld\n", m, n, np, tot, dep, fail, below);
    } else {
        int *pl = (int *)malloc(sizeof(int) * NB), np = 0; const char *kind = argc > 3 ? argv[3] : "graphic";
        for (int i = 0; i < NB; i++) { int ic; if (sdim[i] == 2 && (graphic(smask[i], &ic) || !strcmp(kind, "binary"))) pl[np++] = i; }
        for (int a = 0; a < np; a++) for (int b = a + 1; b < np; b++) for (int c = b + 1; c < np; c++) for (int d = c + 1; d < np; d++) for (int e = d + 1; e < np; e++) {
            lam[0] = smask[pl[a]]; lam[1] = smask[pl[b]]; lam[2] = smask[pl[c]]; lam[3] = smask[pl[d]]; lam[4] = smask[pl[e]];
            int rk = rank_k2(lam, 5); tot++; if (rk == 10) continue; dep++;
            int bd = min_theta(lam, 5, &arg); below += bd < rk;
            if (bd > rk) { fail++; if (fail <= 12) { printf("FAIL rank %d min %d: ", rk, bd); for (int x = 0; x < 5; x++) print_sub(lam[x]); printf("\n"); } } }
        printf("k=2, members %d, all 5-subsets of the %d %s planes: %ld, rank below 10: %ld, min over Theta > rank: %ld, below (bug) %ld\n", m, np, kind, tot, dep, fail, below);
    }
    return 0;
}
