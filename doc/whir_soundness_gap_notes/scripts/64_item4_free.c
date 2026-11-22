// Note 64, item 4: free configurations of t Reed-Solomon codewords for the cube window, by greedy linear algebra.
// Usage: ./64_item4_free m N k t restarts seed [d gseed]   (m = 8 or 16, N <= 7, t <= 5, (t-1)k <= 260)
// With d > 0 the window of x is x and d random partners (note 66) drawn from gseed; d = 0 or absent: cube window.
// State: the space S of (P_1..P_{t-1}) (P_0 = 0), all of degree < k, satisfying the constraints imposed so far, as a
// basis in evaluation form. A move imposes P_i = P_j on a window x + C; its cost is the rank it removes from S, its
// geometric cost the number of window points where P_i = P_j was not yet forced. Forced coincidences are recomputed
// from S after every move, so a rank-deficient configuration shows up as cost < geometric cost or as free gains.
// Score = sum over x of (largest class of polynomials forced to coincide on the window of x) - 1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint16_t fe;
static int m, N, k, t, n, q, s, L, np, pidx[5][5], pi_[10], pj_[10];
static fe *EX; static int *LG;
static fe B[260][512], BK[260][512];
static int W[128][10], rw;   // window table, window size
static unsigned char PF[10][128], PFK[10][128], ban[10][128];
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline fe mul(fe a, fe b) { return (a && b) ? EX[LG[a] + LG[b]] : 0; }
static inline fe phi(const fe *v, int p, int y) { return (pi_[p] ? v[(pi_[p] - 1) * n + y] : 0) ^ v[(pj_[p] - 1) * n + y]; }
static void compute_pf(void) {
    for (int p = 0; p < np; p++) for (int y = 0; y < n; y++) {
        int f = 1;
        for (int b = 0; b < s && f; b++) if (phi(B[b], p, y)) f = 0;
        PF[p][y] = f;
    }
}
static int wf(int i, int j, int x) {   // P_i = P_j forced on the whole window of x
    if (i == j) return 1;
    const unsigned char *f = PF[pidx[i][j]];
    for (int d = 0; d < rw; d++) if (!f[W[x][d]]) return 0;
    return 1;
}
static int cls(int i, int x) { int c = 0; for (int j = 0; j < t; j++) c += wf(i, j, x); return c; }
static int cmax(int x) { int c = 0; for (int i = 0; i < t; i++) { int a = cls(i, x); if (a > c) c = a; } return c; }
static int score(void) { int sc = 0; for (int x = 0; x < n; x++) sc += cmax(x) - 1; return sc; }
static int cost(int p, int x, int *geom) {   // rank of the new window constraints on S
    static fe M[10][260]; int r = 0, g = 0;
    for (int d = 0; d < rw; d++) {
        int y = W[x][d];
        if (PF[p][y]) continue;
        g++;
        for (int b = 0; b < s; b++) M[r][b] = phi(B[b], p, y);
        r++;
    }
    int rk = 0;                            // plain elimination on r rows
    for (int c = 0; c < s && rk < r; c++) {
        int pv = -1; for (int a = rk; a < r; a++) if (M[a][c]) { pv = a; break; }
        if (pv < 0) continue;
        if (pv != rk) for (int b = 0; b < s; b++) { fe tmp = M[rk][b]; M[rk][b] = M[pv][b]; M[pv][b] = tmp; }
        fe iv = EX[q - 1 - LG[M[rk][c]]];
        for (int a = rk + 1; a < r; a++) if (M[a][c]) { fe f = mul(M[a][c], iv); for (int b = c; b < s; b++) M[a][b] ^= mul(f, M[rk][b]); }
        rk++;
    }
    *geom = g; return rk;
}
static void apply(int p, int x) {
    for (int d = 0; d < rw; d++) {
        int y = W[x][d], pv = -1;
        for (int b = 0; b < s; b++) if (phi(B[b], p, y)) { pv = b; break; }
        if (pv < 0) continue;
        fe iv = EX[q - 1 - LG[phi(B[pv], p, y)]];
        for (int b = pv + 1; b < s; b++) { fe f = phi(B[b], p, y); if (f) { f = mul(f, iv); for (int l = 0; l < L; l++) B[b][l] ^= mul(f, B[pv][l]); } }
        memcpy(B[pv], B[s - 1], sizeof(fe) * L); s--;
    }
}
static int feasible(void) {
    if (s < 1) return 0;
    for (int p = 0; p < np; p++) { int z = 0; for (int y = 0; y < n; y++) z += PF[p][y]; if (z == n) return 0; }
    return 1;
}
int main(int argc, char **argv) {
    m = atoi(argv[1]); N = atoi(argv[2]); k = atoi(argv[3]); t = atoi(argv[4]);
    int restarts = atoi(argv[5]); rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    n = 1 << N; q = 1 << m; L = (t - 1) * n;
    int dd = argc > 7 ? atoi(argv[7]) : 0; uint64_t keep = rs;
    rs = 88172645463325252ULL ^ (uint64_t)(argc > 8 ? atoll(argv[8]) : 1) * 0x9E3779B97F4A7C15ULL;
    rw = dd ? dd + 1 : N + 1;
    for (int x = 0; x < n; x++) {
        W[x][0] = x;
        for (int d = 1; d < rw; d++) {
            if (!dd) { W[x][d] = x ^ (1 << (d - 1)); continue; }
            for (;;) { int y = rnd() % n, ok = 1; for (int e = 0; e < d; e++) if (W[x][e] == y) ok = 0; if (ok) { W[x][d] = y; break; } }
        }
    }
    rs = keep;
    EX = malloc(sizeof(fe) * 2 * q); LG = malloc(sizeof(int) * q);
    int a = 1, mod = m == 8 ? 0x11D : 0x1100B;
    for (int i = 0; i < q - 1; i++) { EX[i] = a; LG[a] = i; a <<= 1; if (a >> m) a ^= mod; }
    for (int i = q - 1; i < 2 * q; i++) EX[i] = EX[i - (q - 1)];
    for (int i = 0; i < t; i++) for (int j = i + 1; j < t; j++) { pidx[i][j] = pidx[j][i] = np; pi_[np] = i; pj_[np] = j; np++; }
    int best = -1, bestD = -1000000, maxdef = 0, hist[400] = {0};
    for (int r = 0; r < restarts; r++) {
        s = (t - 1) * k; memset(B, 0, sizeof B); memset(ban, 0, sizeof ban);
        for (int i = 1; i < t; i++) for (int e = 0; e < k; e++) for (int y = 0; y < n; y++) {
            fe v = 1; for (int j = 0; j < e; j++) v = mul(v, (fe)y);
            B[(i - 1) * k + e][(i - 1) * n + y] = v;
        }
        compute_pf();
        double jit = (double[]){0.0, 0.3, 1.0, 2.5}[r % 4];
        int ctot = 0, gtot = 0, sc = 0;
        for (;;) {
            int bp = -1, bx = -1, bc = 0, bg = 0; double bkey = 1e9;
            for (int p = 0; p < np; p++) for (int x = 0; x < n; x++) {
                int i = pi_[p], j = pj_[p];
                if (ban[p][x] || wf(i, j, x)) continue;
                int cm = cmax(x), gain = cls(i, x) + cls(j, x) - cm, g;
                if (gain <= 0) continue;
                int c = cost(p, x, &g);
                double key = (double)c / gain + jit * (double)(rnd() >> 11) / 9007199254740992.0;
                if (key < bkey) { bkey = key; bp = p; bx = x; bc = c; bg = g; }
            }
            if (bp < 0) break;
            int s0 = s; memcpy(BK, B, sizeof(fe) * 512 * s0); memcpy(PFK, PF, sizeof PF);
            apply(bp, bx); compute_pf();
            if (!feasible()) { s = s0; memcpy(B, BK, sizeof(fe) * 512 * s0); memcpy(PF, PFK, sizeof PF); ban[bp][bx] = 1; continue; }
            ctot += bc; gtot += bg; sc = score();
            if (gtot - ctot > maxdef) maxdef = gtot - ctot;
            if (sc - ctot > bestD && sc >= 3 * (t - 1)) bestD = sc - ctot;
        }
        hist[sc < 400 ? sc : 399]++;
        if (sc > best) {
            best = sc;
            printf("restart %d: score %d, cost %d (dim left %d), geometric cost %d; per pair zeros/interior:", r, sc, ctot, s, gtot);
            for (int p = 0; p < np; p++) { int z = 0, w = 0; for (int y = 0; y < n; y++) { z += PF[p][y]; w += wf(pi_[p], pj_[p], y); } printf(" %d%d:%d/%d", pi_[p], pj_[p], z, w); }
            printf("\n");
        }
    }
    printf("q=2^%d N=%d k=%d t=%d d=%d: best score %d against (t-1)k = %d; best score - cost (score >= 3(t-1)) = %d; max deficiency (geometric - rank cost) = %d\nfinal scores:", m, N, k, t, dd, best, (t - 1) * k, bestD, maxdef);
    for (int i = 0; i < 400; i++) if (hist[i]) printf(" %d:%d", i, hist[i]);
    printf("\n");
    return 0;
}
