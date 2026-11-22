// Referee 87: independent exact toy check of note 84, Section 9.1.
// T2 over GF(2^8), rate 1/4, k = 4, n = 16, J = 0 (4 roots, two random levels, nothing checked).
// For each code: exhaustive depth-first search over all one-functional systems with directions
// e1, e2, e1+e2 (three codewords 0, c1, c2) that are genuine (none of m1, m2, m1+m2 is forced to 0),
// with branch and bound; outputs W = the largest number of leaves on which at least two of three
// distinct codewords coincide, and E = the largest excess |X| - rank of a genuine system.
// The witness of W is re-verified by solving for the messages and counting coincidences directly.
// usage: 87_toy3 <seed> <codes>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint8_t MUL[256][256], INV[256];
static uint8_t G[16][4];
static uint64_t rs;
static uint64_t rnd(void) { uint64_t z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }

static uint8_t slow_mul(uint8_t a, uint8_t b) { uint8_t r = 0; while (b) { if (b & 1) r ^= a; a = (uint8_t)((a << 1) ^ ((a & 0x80) ? 0x1D : 0)); b >>= 1; } return r; } // x^8+x^4+x^3+x^2+1

typedef struct {
    uint8_t R[8][8]; int piv[8]; int rank;
    uint8_t P[3][4][4]; int ppiv[3][4]; int prank[3];
} State;

static int bestW, bestE; static int bestX[16], curX[16]; static long nodes;

static void row_of(int x, int d, uint8_t *v) { // d: 0 = e1 (m1 g = 0), 1 = e2, 2 = e1+e2
    for (int c = 0; c < 4; c++) { v[c] = (d != 1) ? G[x][c] : 0; v[4 + c] = (d != 0) ? G[x][c] : 0; }
}
static int reduce8(const State *s, uint8_t *v) {
    for (int b = 0; b < s->rank; b++) { uint8_t c = v[s->piv[b]]; if (c) for (int i = 0; i < 8; i++) v[i] ^= MUL[c][s->R[b][i]]; }
    for (int i = 0; i < 8; i++) if (v[i]) return i;
    return -1;
}
static void proj_add(State *s, int l, const uint8_t *v8) {
    uint8_t w[4];
    for (int c = 0; c < 4; c++) w[c] = (l == 0) ? v8[4 + c] : (l == 1) ? v8[c] : (uint8_t)(v8[c] ^ v8[4 + c]);
    for (int b = 0; b < s->prank[l]; b++) { uint8_t c = w[s->ppiv[l][b]]; if (c) for (int i = 0; i < 4; i++) w[i] ^= MUL[c][s->P[l][b][i]]; }
    int p = -1; for (int i = 0; i < 4; i++) if (w[i]) { p = i; break; }
    if (p < 0) return;
    uint8_t iv = INV[w[p]]; int r = s->prank[l]++;
    for (int i = 0; i < 4; i++) s->P[l][r][i] = MUL[iv][w[i]];
    s->ppiv[l][r] = p;
}
static void dfs(int i, const State *s, int cnt) {
    nodes++;
    if (i == 16) {
        if (cnt > bestW) { bestW = cnt; memcpy(bestX, curX, sizeof curX); }
        if (cnt - s->rank > bestE) bestE = cnt - s->rank;
        return;
    }
    if (cnt + 16 - i <= bestW && cnt - s->rank + 16 - i <= bestE) return;
    for (int d = 0; d < 3; d++) {
        uint8_t v[8]; row_of(i, d, v);
        int p = reduce8(s, v);
        curX[i] = d;
        if (p < 0) { dfs(i + 1, s, cnt + 1); continue; }
        if (s->rank == 7) continue; // rank 8: no nonzero solution
        State t = *s;
        uint8_t iv = INV[v[p]];
        for (int c = 0; c < 8; c++) t.R[t.rank][c] = MUL[iv][v[c]];
        t.piv[t.rank] = p; t.rank++;
        for (int l = 0; l < 3; l++) proj_add(&t, l, t.R[t.rank - 1]);
        int ok = 1;
        for (int l = 0; l < 3; l++) if (t.rank - t.prank[l] >= 4) ok = 0; // lambda_l (x) K^4 inside R: member pair l forced equal
        if (ok) dfs(i + 1, &t, cnt + 1);
    }
    curX[i] = -1;
    dfs(i + 1, s, cnt);
}
// direct recount: solve the system of bestX for (m1, m2), check distinctness, count coincidence leaves
static int recount(void) {
    State s; memset(&s, 0, sizeof s);
    for (int x = 0; x < 16; x++) if (bestX[x] >= 0) {
        uint8_t v[8]; row_of(x, bestX[x], v); int p = reduce8(&s, v); if (p < 0) continue;
        uint8_t iv = INV[v[p]]; for (int c = 0; c < 8; c++) s.R[s.rank][c] = MUL[iv][v[c]]; s.piv[s.rank++] = p;
    }
    // random element of the null space: try random vectors of the orthogonal complement by solving with free coordinates
    int best = -1;
    for (int trial = 0; trial < 64; trial++) {
        uint8_t m[8]; int ispiv[8] = {0};
        for (int b = 0; b < s.rank; b++) ispiv[s.piv[b]] = 1;
        for (int c = 0; c < 8; c++) m[c] = ispiv[c] ? 0 : (uint8_t)rnd();
        for (int b = s.rank - 1; b >= 0; b--) { // back substitution: row b has zeros at earlier pivots only
            uint8_t acc = 0; for (int c = 0; c < 8; c++) if (c != s.piv[b]) acc ^= MUL[s.R[b][c]][m[c]];
            m[s.piv[b]] = acc;
        }
        int okrows = 1;
        for (int b = 0; b < s.rank; b++) { uint8_t acc = 0; for (int c = 0; c < 8; c++) acc ^= MUL[s.R[b][c]][m[c]]; if (acc) okrows = 0; }
        if (!okrows) continue;
        int z1 = 1, z2 = 1, z3 = 1; for (int c = 0; c < 4; c++) { if (m[c]) z1 = 0; if (m[4 + c]) z2 = 0; if (m[c] ^ m[4 + c]) z3 = 0; }
        if (z1 || z2 || z3) continue;
        int w = 0;
        for (int x = 0; x < 16; x++) { uint8_t a = 0, b2 = 0; for (int c = 0; c < 4; c++) { a ^= MUL[m[c]][G[x][c]]; b2 ^= MUL[m[4 + c]][G[x][c]]; } if (a == 0 || b2 == 0 || a == b2) w++; }
        if (w > best) best = w;
    }
    return best;
}
int main(int argc, char **argv) {
    rs = argc > 1 ? strtoull(argv[1], 0, 10) : 87; int codes = argc > 2 ? atoi(argv[2]) : 10;
    for (int a = 0; a < 256; a++) for (int b = 0; b < 256; b++) MUL[a][b] = slow_mul((uint8_t)a, (uint8_t)b);
    for (int a = 1; a < 256; a++) for (int b = 1; b < 256; b++) if (MUL[a][b] == 1) INV[a] = (uint8_t)b;
    int histW[17] = {0}, histE[17] = {0}, mism = 0;
    for (int cd = 0; cd < codes; cd++) {
        for (int root = 0; root < 4; root++) {
            uint8_t t1[2]; do { t1[0] = (uint8_t)rnd(); t1[1] = (uint8_t)rnd(); } while (t1[0] == t1[1]);
            for (int b = 0; b < 2; b++) {
                uint8_t t2[2]; do { t2[0] = (uint8_t)rnd(); t2[1] = (uint8_t)rnd(); } while (t2[0] == t2[1]);
                for (int b2 = 0; b2 < 2; b2++) { uint8_t *g = G[root * 4 + b * 2 + b2]; g[0] = 1; g[1] = t1[b]; g[2] = t2[b2]; g[3] = MUL[t1[b]][t2[b2]]; }
            }
        }
        State s; memset(&s, 0, sizeof s); bestW = 0; bestE = 0; nodes = 0;
        for (int x = 0; x < 16; x++) curX[x] = bestX[x] = -1;
        dfs(0, &s, 0);
        int rc = recount(); if (rc != bestW) mism++;
        histW[bestW]++; histE[bestE]++;
        printf("code %d: W = %d (recount %d), max excess = %d, nodes = %ld\n", cd, bestW, rc, bestE, nodes); fflush(stdout);
    }
    printf("seed %s codes %d: W histogram:", argc > 1 ? argv[1] : "87", codes); for (int w = 0; w <= 16; w++) if (histW[w]) printf(" %d:%d", w, histW[w]);
    printf(" | max excess histogram:"); for (int e = 0; e <= 16; e++) if (histE[e]) printf(" %d:%d", e, histE[e]);
    printf(" | recount mismatches %d\n", mism);
    return 0;
}
