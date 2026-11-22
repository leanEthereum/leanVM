// Note 74, task 1: numerical check of the one-level rank identity (Lemma 2.2 / Proposition 2.4 / Theorem 2.5).
// For each pattern: exact rank of the incidence system over GF(2^64) (T2, random twiddles), the hull over several draws of
// the BOTTOM twiddles (upper twiddles fixed) of the relation components C_x, and Phi = 2 dim(sum (L'_p0 + L'_p1) (x) g_p) + sum (kappa - kappa').
// usage: 74_rec v r L seed nsamp patternfile   (patterns as printed by 69_pat.h; '-' reads stdin)
#include "69_pat.h"
#include "69_lin.h"
static int parse_pattern(const char *line, uint8_t *cls, int n) {
    const char *p = strstr(line, " | "); p = p ? p + 3 : line;
    int x = 0;
    while (*p && x < n) {
        while (*p == ' ') p++;
        if (!*p || *p == '\n') break;
        uint8_t c = 0;
        while (*p && *p != ' ' && *p != '\n') { if (*p >= '0' && *p <= '9') c |= (uint8_t)(1 << (*p - '0')); p++; }
        cls[x++] = c;
    }
    return x == n;
}
int main(int argc, char **argv) {
    int v = atoi(argv[1]), r = atoi(argv[2]), L = atoi(argv[3]); rng_seed(strtoull(argv[4], 0, 10)); int nsamp = atoi(argv[5]);
    FILE *f = strcmp(argv[6], "-") ? fopen(argv[6], "r") : stdin; int verbose = argc > 7;
    gf_init(); int n = 1 << (v + r), k = 1 << v, cols = L * k, hk = k / 2;
    char modes[MAXV + 1]; for (int i = 0; i < v; i++) modes[i] = '2'; modes[v] = 0;
    tree_t T; tree_make(&T, v, r, modes);
    fe *G = malloc(sizeof(fe) * n * k), *A = malloc(sizeof(fe) * (size_t)(L * n) * cols), *At = malloc(sizeof(fe) * (size_t)(L * n) * cols);
    fe *Kb = malloc(sizeof(fe) * (size_t)(L * n) * (L * n)), *H = malloc(sizeof(fe) * (size_t)n * (nsamp * L * n) * L), *Up = malloc(sizeof(fe) * (size_t)(L * n) * L * hk);
    int *hrows = malloc(sizeof(int) * n);
    char line[8192]; uint8_t cls[MAXN];
    long cnt = 0, bad = 0, trivial = 0, proper = 0, nongraphic = 0, dependent = 0, deficient_like = 0, rank_unstable = 0;
    while (fgets(line, sizeof line, f)) {
        if (!parse_pattern(line, cls, n)) continue;
        cnt++;
        int W = pat_weight(cls, n), rowx[MAXN * 8], rowl[MAXN * 8], rowl0[MAXN * 8], off[MAXN + 1], w = 0;
        for (int x = 0; x < n; x++) { off[x] = w; if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) { rowx[w] = x; rowl[w] = l; rowl0[w] = l0; w++; } } }
        off[n] = w; memset(hrows, 0, sizeof(int) * n);
        int rank = -1;
        for (int s = 0; s < nsamp; s++) {
            for (int x = 0; x < n; x++) T.tw[0][x] = gf_rand();
            tree_gen(&T, G);
            for (int a = 0; a < W; a++) {
                fe *row = A + (size_t)a * cols; memset(row, 0, sizeof(fe) * cols);
                memcpy(row + (rowl[a] - 1) * k, G + (size_t)rowx[a] * k, sizeof(fe) * k);
                if (rowl0[a] >= 1) memcpy(row + (rowl0[a] - 1) * k, G + (size_t)rowx[a] * k, sizeof(fe) * k);
            }
            for (int a = 0; a < W; a++) for (int c = 0; c < cols; c++) At[(size_t)c * W + a] = A[(size_t)a * cols + c];
            int dim = gf_kernel(At, cols, W, Kb), rk = W - dim;
            if (rank >= 0 && rk != rank) rank_unstable++;
            rank = rk;
            for (int x = 0; x < n; x++) { int kx = off[x + 1] - off[x]; if (!kx) continue;
                for (int b = 0; b < dim; b++) { memcpy(H + ((size_t)x * nsamp * L * n + hrows[x]) * L, Kb + (size_t)b * W + off[x], sizeof(fe) * kx); hrows[x]++; } }
        }
        int sumdrop = 0, ur = 0, anyproper = 0, anynong = 0;
        for (int x = 0; x < n; x++) {
            int kx = off[x + 1] - off[x]; if (!kx) continue;
            fe *Hx = H + (size_t)x * nsamp * L * n * L, tmp[64 * 8];
            // compact to kx columns
            fe *Hc = malloc(sizeof(fe) * (size_t)(hrows[x] + 1) * kx);
            for (int a = 0; a < hrows[x]; a++) memcpy(Hc + (size_t)a * kx, Hx + (size_t)a * L, sizeof(fe) * kx);
            int kp = hrows[x] ? gf_rank(Hc, hrows[x], kx) : 0;
            sumdrop += kx - kp; if (kp > 0 && kp < kx) anyproper = 1;
            // graphic test: number of independent differences e_l - e_l' (l, l' in the class) lying in the hull
            if (kp > 0 && kp < kx) {
                int members[16], nm = 0, l0 = __builtin_ctz(cls[x]); for (int l = l0; l <= L; l++) if ((cls[x] >> l) & 1) members[nm++] = l;
                // coordinates: basis vector a of Lambda_x is e_{members[a+1]} - e_{l0}; e_{m_i} - e_{m_j} has coordinate +1 at i-1 and at j-1 (char 2), i, j >= 1, or a single 1
                int gcount = 0; fe *Gm = malloc(sizeof(fe) * (size_t)(nm * nm) * kx);
                for (int i = 0; i < nm; i++) for (int j = i + 1; j < nm; j++) {
                    fe vec[16] = {0}; if (i >= 1) vec[i - 1] ^= 1; vec[j - 1] ^= 1;
                    memcpy(tmp, Hc, sizeof(fe) * (size_t)kp * kx); memcpy(tmp + (size_t)kp * kx, vec, sizeof(fe) * kx);
                    if (gf_rank(tmp, kp + 1, kx) == kp) { memcpy(Gm + (size_t)gcount * kx, vec, sizeof(fe) * kx); gcount++; }
                }
                int gr = gcount ? gf_rank(Gm, gcount, kx) : 0; free(Gm);
                if (gr < kp) anynong = 1;
            }
            for (int b = 0; b < kp; b++) {
                fe lam[16] = {0};
                for (int a = 0; a < kx; a++) { fe c = Hc[(size_t)b * kx + a]; lam[rowl[off[x] + a]] ^= c; lam[rowl0[off[x] + a]] ^= c; }
                fe *row = Up + (size_t)ur * L * hk;
                for (int l = 1; l <= L; l++) for (int e = 0; e < hk; e++) row[(l - 1) * hk + e] = gf_mul(lam[l], G[(size_t)x * k + 2 * e]);
                ur++;
            }
            free(Hc);
        }
        int du = ur ? gf_rank(Up, ur, L * hk) : 0, phi = 2 * du + sumdrop;
        if (phi != rank) bad++;
        if (rank < W) dependent++;
        if (ur == 0) trivial++;
        if (anyproper) proper++;
        if (anynong) nongraphic++;
        if (rank < (W < cols ? W : cols)) deficient_like++;
        if (verbose || phi != rank) { printf("W=%d rank=%d Phi=%d dimU'=%d dropped=%d proper=%d nongraphic=%d | ", W, rank, phi, du, sumdrop, anyproper, anynong); pat_print(stdout, cls, n, L); }
    }
    printf("# v=%d r=%d L=%d nsamp=%d: patterns %ld, Phi(hull) != rank: %ld, rank below min(W, Lk): %ld, dependent rows: %ld, hull zero: %ld, hull uses a proper nonzero subspace of some Lambda_x: %ld, of which not a sub-class (non-graphic): %ld, rank varied between draws: %ld\n", v, r, L, nsamp, cnt, bad, deficient_like, dependent, trivial, proper, nongraphic, rank_unstable);
    return 0;
}
