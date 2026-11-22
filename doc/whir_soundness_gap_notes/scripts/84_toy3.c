// Note 84, Section 9: the event of Theorem 5.1 for t = 3 at toy size, exhaustively.
// Tree code T2 over GF(2^8), k = 4, n = 16 (rate 1/4, two levels, every twiddle random, J = 0).
// For each code: depth-first search over ALL genuine one-functional systems with directions
// e1, e2, e1+e2 (genuineness is closed under sub-systems, so the search prunes on it), recording
//   W = the largest number of leaves of a genuine system  (= the largest number of leaves where
//       at least two of three distinct codewords coincide), and
//   e = the largest excess |X| - rank of a genuine system.
// The members are renamed so that the first direction used is e1 and the second one e2.
// usage: 84_toy3 <first seed> <number of codes>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t EXP[510], LOG[256];
static inline uint8_t mul(uint8_t a, uint8_t b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static inline uint8_t inv(uint8_t a) { return EXP[255 - LOG[a]]; }

#define NL 16
#define DIM 8
static uint8_t G[NL][4];
static const uint8_t DIRS[3][2] = {{1, 0}, {0, 1}, {1, 1}};

typedef struct {
    uint8_t row[DIM][DIM];
    int8_t piv[DIM]; // pivot column of each row
    int rank;
} Basis;

static void reduce(const Basis *B, uint8_t *v) {
    for (int i = 0; i < B->rank; i++) {
        uint8_t f = v[B->piv[i]];
        if (f)
            for (int c = 0; c < DIM; c++) v[c] ^= mul(f, B->row[i][c]);
    }
}

// returns 1 if the rank grew
static int add(Basis *B, uint8_t *v) {
    reduce(B, v);
    int p = -1;
    for (int c = 0; c < DIM; c++)
        if (v[c]) { p = c; break; }
    if (p < 0) return 0;
    uint8_t fi = inv(v[p]);
    for (int c = 0; c < DIM; c++) v[c] = mul(fi, v[c]);
    for (int i = 0; i < B->rank; i++) {
        uint8_t f = B->row[i][p];
        if (f)
            for (int c = 0; c < DIM; c++) B->row[i][c] ^= mul(f, v[c]);
    }
    memcpy(B->row[B->rank], v, DIM);
    B->piv[B->rank] = (int8_t)p;
    B->rank++;
    return 1;
}

// direction d is genuine for the solution space of B: some lambda (x) e_c is outside the row space
static int dir_ok(const Basis *B, int d) {
    for (int c = 0; c < 4; c++) {
        uint8_t v[DIM] = {0};
        v[2 * c] = DIRS[d][0];
        v[2 * c + 1] = DIRS[d][1];
        reduce(B, v);
        for (int i = 0; i < DIM; i++)
            if (v[i]) return 1;
    }
    return 0;
}

static int bestW, bestE;
static uint64_t nodes;

static void dfs(int x, const Basis *B, int size, int used) {
    if (size > bestW) bestW = size;
    if (size - B->rank > bestE) bestE = size - B->rank;
    if (x == NL) return;
    dfs(x + 1, B, size, used);
    int nused = (used & 1) + ((used >> 1) & 1) + ((used >> 2) & 1);
    for (int d = 0; d < 3; d++) {
        // renaming of the members: first new direction is 0, second new direction is 1
        if (!(used >> d & 1)) {
            if (nused == 0 && d != 0) continue;
            if (nused == 1 && d != 1 && (used & 1)) continue;
        }
        Basis C = *B;
        uint8_t v[DIM];
        for (int c = 0; c < 4; c++) {
            v[2 * c] = mul(G[x][c], DIRS[d][0]);
            v[2 * c + 1] = mul(G[x][c], DIRS[d][1]);
        }
        int grew = add(&C, v);
        int nu = used | (1 << d);
        int ok = 1;
        if (grew) {
            for (int e = 0; e < 3 && ok; e++)
                if (nu >> e & 1) ok = dir_ok(&C, e);
        } else if (!(used >> d & 1)) {
            ok = dir_ok(&C, d);
        }
        nodes++;
        if (ok) dfs(x + 1, &C, size + 1, nu);
    }
}

static uint64_t rs;
static uint8_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return (uint8_t)(rs >> 29);
}

int main(int argc, char **argv) {
    uint64_t seed0 = argc > 1 ? strtoull(argv[1], 0, 10) : 1;
    int ncodes = argc > 2 ? atoi(argv[2]) : 10;
    uint8_t x = 1;
    for (int i = 0; i < 255; i++) {
        EXP[i] = x; LOG[x] = (uint8_t)i;
        uint8_t y = (uint8_t)(x << 1) ^ ((x & 0x80) ? 0x1b : 0);
        x = y ^ x;
    }
    for (int i = 255; i < 510; i++) EXP[i] = EXP[i - 255];
    for (int cidx = 0; cidx < ncodes; cidx++) {
        rs = 0x9E3779B97F4A7C15ULL * (seed0 + (uint64_t)cidx) + 0x1234567ULL;
        for (int i = 0; i < 20; i++) rnd();
        uint8_t t1[8], t2[16];
        for (int p = 0; p < 4; p++) { t1[2 * p] = rnd(); do t1[2 * p + 1] = rnd(); while (t1[2 * p + 1] == t1[2 * p]); }
        for (int p = 0; p < 8; p++) { t2[2 * p] = rnd(); do t2[2 * p + 1] = rnd(); while (t2[2 * p + 1] == t2[2 * p]); }
        for (int leaf = 0; leaf < NL; leaf++) {
            uint8_t a = t1[leaf >> 1], b = t2[leaf];
            G[leaf][0] = 1; G[leaf][1] = a; G[leaf][2] = b; G[leaf][3] = mul(a, b);
        }
        Basis B; memset(&B, 0, sizeof B);
        bestW = bestE = 0; nodes = 0;
        dfs(0, &B, 0, 0);
        printf("seed %llu W %d e %d nodes %llu\n", (unsigned long long)(seed0 + cidx), bestW, bestE, (unsigned long long)nodes);
        fflush(stdout);
    }
    return 0;
}
