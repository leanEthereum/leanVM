// Referee 80: test of note 76's Conjecture 4.4 (three members: generic rank = split-and-merge recursion r_v of Theorem 4.1).
// Leaf types 0, a, b, c, F (spaces 0, three lines, K^2); join = sum of spaces. At every level each leaf of each sibling pair goes
// to side 0 or 1 (both to one side: their join); r_0(x, y) = dim(x + y) for the code {(m, m)}.
//   80_conj44 all48 <seed>                 every one of the 5^8 patterns at (4,8): exact rank (T2 and T1) against r_2
//   80_conj44 rand16 <seed> <patterns>     random and structured patterns at (8,16): exact rank against exact r_3
//   80_conj44 rand32 <seed> <patterns>     the same at (16,32): r_4 by search for a certificate (a labelling reaching the rank)
#include "80_gf.h"
static const unsigned CLS[5] = {0, 3, 5, 6, 7};
static const int DIM[5] = {0, 1, 1, 1, 2};
static int J[5][5];
static unsigned char *R2; static unsigned char R1[625], R0[25];
static const int P5[9] = {1, 5, 25, 125, 625, 3125, 15625, 78125, 390625};

static void build_tables(void) {
    for (int s = 0; s < 5; s++) for (int t = 0; t < 5; t++) J[s][t] = s == 0 ? t : t == 0 ? s : s == t ? s : 4;
    for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) R0[x + 5 * y] = DIM[J[x][y]];
    // options of a pair (x, y): (x | y), (y | x), (x + y | 0), (0 | x + y)
    for (int c = 0; c < 625; c++) {
        int t[4], cc = c, best = 0; for (int i = 0; i < 4; i++) { t[i] = cc % 5; cc /= 5; }
        for (int o = 0; o < 16; o++) {
            int s0[2], s1[2];
            for (int p = 0; p < 2; p++) { int x = t[2 * p], y = t[2 * p + 1], op = (o >> (2 * p)) & 3;
                s0[p] = op == 0 ? x : op == 1 ? y : op == 2 ? J[x][y] : 0; s1[p] = op == 0 ? y : op == 1 ? x : op == 2 ? 0 : J[x][y]; }
            int val = R0[s0[0] + 5 * s0[1]] + R0[s1[0] + 5 * s1[1]];
            if (val > best) best = val;
        }
        R1[c] = best;
    }
    R2 = malloc(390625);
    for (int c = 0; c < 390625; c++) {
        int t[8], cc = c, best = 0; for (int i = 0; i < 8; i++) { t[i] = cc % 5; cc /= 5; }
        for (int o = 0; o < 256; o++) {
            int i0 = 0, i1 = 0;
            for (int p = 0; p < 4; p++) { int x = t[2 * p], y = t[2 * p + 1], op = (o >> (2 * p)) & 3;
                i0 += P5[p] * (op == 0 ? x : op == 1 ? y : op == 2 ? J[x][y] : 0); i1 += P5[p] * (op == 0 ? y : op == 1 ? x : op == 2 ? 0 : J[x][y]); }
            int val = R1[i0] + R1[i1];
            if (val > best) best = val;
        }
        R2[c] = best;
    }
}
// exact r_3 of a pattern on 16 leaves (8 pairs): 4^8 options, meet in the middle over the two halves of the pairs
static int r3(const unsigned char *t) {
    int A0[256], A1[256], B0[256], B1[256];
    for (int o = 0; o < 256; o++) {
        int a0 = 0, a1 = 0, b0 = 0, b1 = 0;
        for (int p = 0; p < 4; p++) {
            int op = (o >> (2 * p)) & 3, x = t[2 * p], y = t[2 * p + 1];
            a0 += P5[p] * (op == 0 ? x : op == 1 ? y : op == 2 ? J[x][y] : 0); a1 += P5[p] * (op == 0 ? y : op == 1 ? x : op == 2 ? 0 : J[x][y]);
            x = t[8 + 2 * p]; y = t[8 + 2 * p + 1];
            b0 += P5[4 + p] * (op == 0 ? x : op == 1 ? y : op == 2 ? J[x][y] : 0); b1 += P5[4 + p] * (op == 0 ? y : op == 1 ? x : op == 2 ? 0 : J[x][y]);
        }
        A0[o] = a0; A1[o] = a1; B0[o] = b0; B1[o] = b1;
    }
    int best = 0;
    for (int i = 0; i < 256; i++) for (int j = 0; j < 256; j++) { int val = R2[A0[i] + B0[j]] + R2[A1[i] + B1[j]]; if (val > best) best = val; }
    return best;
}
// memo for r3 keyed by the base-5 code of the pattern
#define HB 22
static uint64_t *hkey; static unsigned char *hval;
static int r3_memo(const unsigned char *t) {
    uint64_t key = 0; for (int i = 15; i >= 0; i--) key = key * 5 + t[i];
    key += 1;
    uint64_t slot = (key * 0x9E3779B97F4A7C15ull) >> (64 - HB);
    for (int probe = 0; probe < 64; probe++) { uint64_t s = (slot + probe) & ((1u << HB) - 1); if (hkey[s] == key) return hval[s]; if (!hkey[s]) { int vv = r3(t); hkey[s] = key; hval[s] = vv; return vv; } }
    return r3(t);
}
static int exact_rank(tree_t *T, const unsigned char *t, fe *M) {
    unsigned cls[64]; for (int x = 0; x < T->n; x++) cls[x] = CLS[t[x]];
    int w = pat_matrix(T, cls, 2, M);
    return w ? fe_rank(M, w, 2 * T->k) : 0;
}

// ---- exact r_4 at (16,32) by branch and bound over the bottom options; bounds: weights, and the exact ranks of the two
// upper patterns with every undecided pair replaced by its join on both sides (r_3 <= rank by Theorem 4.1, rank is monotone)
static tree_t TU; static fe *MU; static long bb_nodes, bb_budget; static int bb_best; static const unsigned char *bb_t;
static int bb_remside[17], bb_full = 0; // bb_full: no pruning at all (set by the environment variable FULL)
static void bb(int p, unsigned char *s0, unsigned char *s1, int w0, int w1) {
    if (bb_nodes > bb_budget) return;
    bb_nodes++;
    if (p == 16) { int val = r3_memo(s0) + r3_memo(s1); if (val > bb_best) bb_best = val; return; }
    int x = bb_t[2 * p], y = bb_t[2 * p + 1], j = J[x][y];
    int oa[4] = {x, y, j, 0}, ob[4] = {y, x, 0, j};
    for (int o = 0; o < 4; o++) {
        int dup = 0; for (int o2 = 0; o2 < o; o2++) if (oa[o2] == oa[o] && ob[o2] == ob[o]) dup = 1;
        if (dup) continue;
        int W0 = w0 + DIM[oa[o]], W1 = w1 + DIM[ob[o]], rs = bb_remside[p + 1];
        int ub = (W0 + rs < 16 ? W0 + rs : 16) + (W1 + rs < 16 ? W1 + rs : 16);
        if (ub <= bb_best && !bb_full) continue;
        s0[p] = oa[o]; s1[p] = ob[o];
        if (bb_full) { bb(p + 1, s0, s1, W0, W1); continue; }
        unsigned char m0[16], m1[16];
        for (int q = 0; q < 16; q++) { if (q <= p) { m0[q] = s0[q]; m1[q] = s1[q]; } else { m0[q] = m1[q] = J[bb_t[2 * q]][bb_t[2 * q + 1]]; } }
        int ub2 = exact_rank(&TU, m0, MU) + exact_rank(&TU, m1, MU);
        if (ub2 <= bb_best) continue;
        bb(p + 1, s0, s1, W0, W1);
    }
}
static int exact_r4(const unsigned char *t, int incumbent, long budget, int *complete) {
    unsigned char s0[16], s1[16];
    bb_t = t; bb_best = incumbent; bb_nodes = 0; bb_budget = budget;
    bb_remside[16] = 0; for (int p = 15; p >= 0; p--) bb_remside[p] = bb_remside[p + 1] + DIM[J[t[2 * p]][t[2 * p + 1]]];
    bb(0, s0, s1, 0, 0);
    *complete = bb_nodes <= bb_budget;
    return bb_best;
}
static void gen_pattern(unsigned char *t, int n, int v) {
    int kind = rnd_below(5);
    if (kind == 0) { int p0 = rnd_below(70), pf = rnd_below(60); for (int x = 0; x < n; x++) { int r = rnd_below(100); t[x] = r < p0 ? 0 : r < p0 + pf ? 4 : 1 + rnd_below(3); } }
    else if (kind == 1) { // block-constant at a random scale, then a block of common zeros with one leftover leaf, then a few flips
        int b = 1 << (1 + rnd_below(v)); if (b > n / 2) b = n / 2;
        for (int q = 0; q < n / b; q++) { int ty = rnd_below(5); for (int j = 0; j < b; j++) t[q * b + j] = ty; }
        int q = rnd_below(n / b), keep = rnd_below(b); for (int j = 0; j < b; j++) t[q * b + j] = j == keep ? 0 : 4;
        int fl = rnd_below(4); for (int z = 0; z < fl; z++) t[rnd_below(n)] = rnd_below(5);
    } else if (kind == 2) { // two scales mixed
        int b1 = 1 << (1 + rnd_below(v)), b2 = 1 << rnd_below(v + 1); if (b1 > n / 2) b1 = n / 2;
        for (int q = 0; q < n / b1; q++) { int ty = rnd_below(5); for (int j = 0; j < b1; j++) t[q * b1 + j] = ty; }
        for (int q = 0; q < n / b2; q++) if (rnd_below(3) == 0) { int ty = rnd_below(5); for (int j = 0; j < b2; j++) t[q * b2 + j] = J[t[q * b2 + j]][ty]; }
    } else if (kind == 3) { // dense: mostly lines and F, few zeros
        int pz = rnd_below(15), pf = 10 + rnd_below(50); for (int x = 0; x < n; x++) { int r = rnd_below(100); t[x] = r < pz ? 0 : r < pz + pf ? 4 : 1 + rnd_below(3); }
    } else { // sibling-correlated
        for (int p = 0; p < n / 2; p++) { int ty = rnd_below(5); t[2 * p] = ty; t[2 * p + 1] = rnd_below(3) ? ty : (int)rnd_below(5); }
    }
}
int main(int argc, char **argv) {
    if (argc < 3) { printf("usage: see header\n"); return 1; }
    rnd_seed(strtoull(argv[2], 0, 10)); fe_selftest(); build_tables();
    if (!strcmp(argv[1], "all48")) {
        tree_t T2, T1; tree_init(&T2, 2, 2, 2); tree_init(&T1, 2, 2, 1);
        fe *M = malloc(sizeof(fe) * 64 * 16); long neq = 0, lt = 0, gt = 0, t1lt = 0, t1ne = 0, dep = 0; unsigned char t[8];
        for (int c = 0; c < 390625; c++) {
            int cc = c, w = 0; for (int i = 0; i < 8; i++) { t[i] = cc % 5; cc /= 5; w += DIM[t[i]]; }
            int rk = exact_rank(&T2, t, M), rk1 = exact_rank(&T1, t, M), r = R2[c];
            if (rk < w) dep++;
            if (r == rk) neq++; else if (r < rk) { lt++; if (lt <= 3) { printf("  r_2 = %d < rank %d:", r, rk); for (int i = 0; i < 8; i++) printf(" %d", t[i]); printf("\n"); } } else gt++;
            if (rk1 < r) t1lt++;
            if (rk1 != rk) t1ne++;
        }
        printf("(4,8), all 390625 three-member patterns (%ld with dependent rows): r_2 = rank(T2) in %ld, r_2 < rank in %ld, r_2 > rank in %ld; rank(T1) < r_2 in %ld; rank(T1) != rank(T2) in %ld\n", dep, neq, lt, gt, t1lt, t1ne);
        return 0;
    }
    if (!strcmp(argv[1], "exact32")) {
        tree_t T2; tree_init(&T2, 4, 2, 2); tree_init(&TU, 3, 2, 2); MU = malloc(sizeof(fe) * 64 * 32);
        hkey = calloc(1u << HB, sizeof(uint64_t)); hval = malloc(1u << HB);
        fe *M = malloc(sizeof(fe) * 128 * 64);
        for (int a = 3; a < argc; a++) {
            unsigned char t[32], u[32]; int cnt = 0; char buf[512]; strncpy(buf, argv[a], 511); buf[511] = 0;
            for (char *tok = strtok(buf, " "); tok && cnt < 32; tok = strtok(NULL, " ")) u[cnt++] = atoi(tok);
            if (cnt == 16) { for (int i = 0; i < 16; i++) t[2 * i] = t[2 * i + 1] = u[i]; } else if (cnt == 32) memcpy(t, u, 32); else { printf("need 16 or 32 types\n"); return 1; }
            int w = 0; for (int i = 0; i < 32; i++) w += DIM[t[i]];
            bb_full = getenv("FULL") != NULL;
            int rk = exact_rank(&T2, t, M), complete, ex = exact_r4(t, 0, bb_full ? 4000000000L : 50000000, &complete);
            printf("(16,32) pattern%s:", cnt == 16 ? " (lift of the given (8,16) pattern)" : ""); for (int i = 0; i < 32; i++) printf(" %d", t[i]);
            printf("\n   weight %d, exact rank %d, r_4 = %d (%s, %ld nodes)\n", w, rk, ex, complete ? (bb_full ? "exact: full enumeration, no pruning" : "exact: branch and bound complete") : "lower bound only", bb_nodes);
            if (cnt == 16) printf("   the (8,16) pattern itself: rank %d, r_3 = %d\n", exact_rank(&TU, u, MU), r3(u));
        }
        return 0;
    }
    long npat = argc > 3 ? atol(argv[3]) : 1000;
    if (!strcmp(argv[1], "rand16")) {
        tree_t T2, T1; tree_init(&T2, 3, 2, 2); tree_init(&T1, 3, 2, 1);
        fe *M = malloc(sizeof(fe) * 64 * 32); long neq = 0, lt = 0, gt = 0, t1lt = 0, t1ne = 0, dep = 0, strict = 0; unsigned char t[16];
        for (long it = 0; it < npat; it++) {
            gen_pattern(t, 16, 3);
            int w = 0; for (int i = 0; i < 16; i++) w += DIM[t[i]];
            int rk = exact_rank(&T2, t, M), rk1 = exact_rank(&T1, t, M), r = r3(t);
            if (rk < w) dep++;
            if (rk < w && rk < 16) strict++;
            if (r == rk) neq++; else if (r < rk) { lt++; if (lt <= 40) { printf("  COUNTEREXAMPLE (w %d) r_3 = %d < rank %d:", w, r, rk); for (int i = 0; i < 16; i++) printf(" %d", t[i]); printf("\n"); } } else { gt++; if (gt <= 5) { printf("  r_3 = %d > rank %d (Theorem 4.1 violated?):", r, rk); for (int i = 0; i < 16; i++) printf(" %d", t[i]); printf("\n"); } }
            if (rk1 < r) { t1lt++; if (t1lt <= 3) { printf("  T1: rank %d < r_3 %d:", rk1, r); for (int i = 0; i < 16; i++) printf(" %d", t[i]); printf("\n"); } }
            if (rk1 != rk) { t1ne++; if (t1ne <= 8) { printf("  T1 rank %d != T2 rank %d (w %d, r_3 %d):", rk1, rk, w, r); for (int i = 0; i < 16; i++) printf(" %d", t[i]); printf("\n"); } }
        }
        printf("(8,16), seed %s, %ld patterns (%ld with dependent rows, %ld with rank < min(w, 2k)): r_3 = rank(T2) in %ld, r_3 < rank in %ld, r_3 > rank in %ld; rank(T1) < r_3 in %ld; rank(T1) != rank(T2) in %ld\n", argv[2], npat, dep, strict, neq, lt, gt, t1lt, t1ne);
        return 0;
    }
    if (!strcmp(argv[1], "rand32")) {
        tree_t T2; tree_init(&T2, 4, 2, 2);
        hkey = calloc(1u << HB, sizeof(uint64_t)); hval = malloc(1u << HB);
        fe *M = malloc(sizeof(fe) * 128 * 64); long cert = 0, open_ = 0, above = 0, dep = 0, strict = 0, first_try = 0, counter = 0;
        tree_init(&TU, 3, 2, 2); MU = malloc(sizeof(fe) * 64 * 32); unsigned char t[32], s0[16], s1[16], opt[16];
        for (long it = 0; it < npat; it++) {
            gen_pattern(t, 32, 4);
            int w = 0; for (int i = 0; i < 32; i++) w += DIM[t[i]];
            int rk = exact_rank(&T2, t, M), best = -1;
            if (rk < w) dep++;
            if (rk < w && rk < 32) strict++;
            for (int restart = 0; restart < 60 && best < rk; restart++) {
                for (int p = 0; p < 16; p++) { opt[p] = restart == 0 ? 0 : rnd_below(4); }
                int cur = -1, improved = 1;
                while (improved && cur < rk) {
                    improved = 0;
                    for (int p = 0; p < 16 && cur < rk; p++) {
                        int keep = opt[p], bo = keep, bv = -1;
                        for (int o = 0; o < 4; o++) {
                            opt[p] = o;
                            for (int q = 0; q < 16; q++) { int x = t[2 * q], y = t[2 * q + 1], op = opt[q]; s0[q] = op == 0 ? x : op == 1 ? y : op == 2 ? J[x][y] : 0; s1[q] = op == 0 ? y : op == 1 ? x : op == 2 ? 0 : J[x][y]; }
                            int val = r3_memo(s0) + r3_memo(s1);
                            if (val > bv || (val == bv && o == keep)) { bv = val; bo = o; }
                        }
                        opt[p] = bo;
                        if (bv > cur) { cur = bv; improved = 1; }
                    }
                }
                if (cur > best) best = cur;
                if (restart == 0 && best >= rk) first_try++;
            }
            if (best == rk) cert++;
            else if (best > rk) { above++; printf("  r_4 >= %d > rank %d (Theorem 4.1 violated?):", best, rk); for (int i = 0; i < 32; i++) printf(" %d", t[i]); printf("\n"); }
            else { int complete, ex = exact_r4(t, best, 400000, &complete);
                if (ex == rk) cert++;
                else if (complete) { counter++; printf("  COUNTEREXAMPLE at (16,32): exact r_4 = %d < rank %d (w %d):", ex, rk, w); for (int i = 0; i < 32; i++) printf(" %d", t[i]); printf("\n"); }
                else { open_++; printf("  UNDECIDED: best labelling found %d, rank %d, w %d:", ex, rk, w); for (int i = 0; i < 32; i++) printf(" %d", t[i]); printf("\n"); } }
        }
        printf("(16,32), seed %s, %ld patterns (%ld with dependent rows, %ld with rank < min(w, 2k)): r_4 = rank certified for %ld (%ld on the first descent), exact r_4 < rank (counterexamples) %ld, undecided %ld, labelling above the rank %ld\n", argv[2], npat, dep, strict, cert, first_try, counter, open_, above);
        return 0;
    }
    return 1;
}
