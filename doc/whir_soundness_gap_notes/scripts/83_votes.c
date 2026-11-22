// Note 83: simulated annealing over voted lists of a top tree code C_N = [N, N/2] (T2, GF(2^64)), the class of lists of
// the tree code [N b, N b / 2] whose differences are A (x) B with one lower factor B in K^b having its b - 1 zeros in block 0
// (Lemma 3.1 of note 83 iterated). State: at every block q a label lab[q][j] for every member (members with equal labels
// have the same symbol at q) and b votes, each for a label; block 0 has b - 1 wildcard votes (the zeros of B) and one vote.
// A state is feasible if the top code carries M pairwise distinct codewords with all the coincidences of the voted classes
// (exact kernel test). Credit of a member = number of votes for its label (+ b - 1). Objective: sum_j min(credit_j, target).
// usage: 83_votes vtop b M target steps seed [zeros=1] [T0] [dead mask]   (dead: blocks without votes, for the limit b -> infinity)
// cc -O2 -DFB=64 -o 83_bin/votes 83_votes.c
#include "69_tree.h"
#include "69_lin.h"
#include <math.h>
#define MAXM 40
#define MAXNB 32
#define MAXB 64
static int N, ku, Mm, L, cols, b, zeros, target; static unsigned dead = 0; // bitmask of blocks whose votes do not count (punctured coordinates)
static fe *Gup, *Mx, *Kx; static long ntests = 0;
typedef struct { unsigned char lab[MAXNB][MAXM]; unsigned char vote[MAXNB][MAXB]; } st_t;
static int nvotes(int q) { if ((dead >> q) & 1) return 0; return (q == 0 && zeros) ? 1 : b; }
static int feasible(const st_t *s) {
    int rows = 0; ntests++;
    for (int q = 0; q < N; q++) {
        int used[MAXM] = {0};
        for (int i = 0; i < nvotes(q); i++) used[s->vote[q][i]] = 1;
        for (int a = 0; a < Mm; a++) { if (!used[a]) continue; int l0 = -1;
            for (int l = 0; l < Mm; l++) if (s->lab[q][l] == a) { if (l0 < 0) { l0 = l; continue; }
                fe *row = Mx + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
                memcpy(row + (l - 1) * ku, Gup + q * ku, sizeof(fe) * ku); if (l0 >= 1) memcpy(row + (l0 - 1) * ku, Gup + q * ku, sizeof(fe) * ku); rows++; } }
    }
    if (!rows) return 1;
    int dim = gf_kernel(Mx, rows, cols, Kx); if (!dim) return 0;
    for (int a = 0; a <= L; a++) for (int c = a + 1; c <= L; c++) { int all = 1;
        for (int t = 0; t < dim && all; t++) for (int e = 0; e < ku && all; e++) { fe da = a ? Kx[(size_t)t * cols + (a - 1) * ku + e] : 0, db = Kx[(size_t)t * cols + (c - 1) * ku + e]; all = (da == db); }
        if (all) return 0; }
    return dim;
}
static void credits(const st_t *s, int *cr) {
    for (int j = 0; j < Mm; j++) cr[j] = zeros ? b - 1 : 0;
    for (int q = 0; q < N; q++) for (int i = 0; i < nvotes(q); i++) { int a = s->vote[q][i]; for (int j = 0; j < Mm; j++) if (s->lab[q][j] == a) cr[j]++; }
}
static long objective(const st_t *s, int *mn) { int cr[MAXM]; credits(s, cr); long o = 0; *mn = 1 << 30; for (int j = 0; j < Mm; j++) { o += cr[j] < target ? cr[j] : target; if (cr[j] < *mn) *mn = cr[j]; } return o; }
static void print_state(const st_t *s) {
    for (int q = 0; q < N; q++) { printf(" [");
        for (int i = 0; i < nvotes(q); i++) { int a = s->vote[q][i]; if (i) printf(" "); int any = 0;
            for (int j = 0; j < Mm; j++) if (s->lab[q][j] == a) { printf("%c", j < 10 ? '0' + j : 'a' + j - 10); any = 1; } if (!any) printf("."); }
        if (q == 0 && zeros) printf(" *%d", b - 1); printf("]"); }
    printf("\n");
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: 83_votes vtop b M target steps seed [zeros] [T0]\n"); return 1; }
    int vt = atoi(argv[1]); b = atoi(argv[2]); Mm = atoi(argv[3]); target = atoi(argv[4]); long steps = atol(argv[5]); uint64_t seed = strtoull(argv[6], 0, 10);
    zeros = argc > 7 ? atoi(argv[7]) : 1; double T0 = argc > 8 ? atof(argv[8]) : 1.0; dead = argc > 9 ? (unsigned)strtoul(argv[9], 0, 0) : 0;
    rng_seed(seed); gf_init(); char modes[MAXV + 1]; for (int i = 0; i < vt; i++) modes[i] = '2'; modes[vt] = 0;
    tree_t T; tree_make(&T, vt, 1, modes); N = T.n; ku = T.k; L = Mm - 1; cols = L * ku;
    Gup = malloc(sizeof(fe) * N * ku); tree_gen(&T, Gup);
    Mx = malloc(sizeof(fe) * (size_t)(N * L + 1) * cols); Kx = malloc(sizeof(fe) * (size_t)cols * cols);
    st_t cur, best, nw; memset(&cur, 0, sizeof cur);
    for (int q = 0; q < N; q++) { for (int j = 0; j < Mm; j++) cur.lab[q][j] = j; for (int i = 0; i < b; i++) cur.vote[q][i] = rng_below(Mm); }
    int mn, bmn; long obj = objective(&cur, &mn), bobj = obj; best = cur; bmn = mn; long acc = 0;
    for (long st = 0; st < steps; st++) {
        double Tm = T0 * (1.0 - (double)st / steps) + 0.02;
        nw = cur; int q = rng_below(N), kind = rng_below(10); if ((dead >> q) & 1) continue;
        if (kind < 5) { int j = rng_below(Mm); int a; if (rng_below(3)) a = nw.vote[q][rng_below(nvotes(q))]; else a = rng_below(Mm); if (a == nw.lab[q][j]) continue; nw.lab[q][j] = a; }
        else if (kind < 8) { int i = rng_below(nvotes(q)); int a = rng_below(2) ? nw.lab[q][rng_below(Mm)] : rng_below(Mm); if (a == nw.vote[q][i]) continue; nw.vote[q][i] = a; }
        else { int j = rng_below(Mm), q2 = rng_below(N); if ((dead >> q2) & 1) continue; int a = nw.vote[q][rng_below(nvotes(q))]; if (a == nw.lab[q][j]) continue; nw.lab[q][j] = a; int j2 = rng_below(Mm); nw.lab[q2][j2] = rng_below(Mm); }
        int nmn; long nobj = objective(&nw, &nmn);
        if (nobj < obj) { double u = (double)(rng_u64() >> 11) / 9007199254740992.0; if (u >= exp((double)(nobj - obj) / Tm)) continue; }
        if (!feasible(&nw)) continue;
        cur = nw; obj = nobj; acc++;
        if (obj > bobj || (obj == bobj && nmn > bmn)) { bobj = obj; bmn = nmn; best = cur; if (bobj == (long)Mm * target) break; }
    }
    int cr[MAXM]; credits(&best, cr); int dim = feasible(&best);
    printf("top [%d,%d] b=%d (n=%d) M=%d target=%d zeros=%d dead=0x%x seed=%llu: best objective %ld of %ld, min credit %d, kernel dim %d, %ld accepted, %ld tests | credits:", N, ku, b, N * b, Mm, target, zeros, dead, (unsigned long long)seed, bobj, (long)Mm * target, bmn, dim, acc, ntests);
    for (int j = 0; j < Mm; j++) printf(" %d", cr[j]); printf(" | votes:"); print_state(&best);
    return 0;
}
