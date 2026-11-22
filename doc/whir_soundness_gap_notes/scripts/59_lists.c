// 59_lists.c: exact weight distribution and exact lists of size 3 for [16, k] codes over GF(16), N = 4:
// plain Reed-Solomon on D = GF(16), the window-mixed code (Hamming-ball windows, uniform mu), a random linear code.
// Usage: ./59_lists type(rs|mix|rand) k seed T [part nparts]
// Counts the ordered pairs (c1, c2), c1 nonzero up to scaling, such that the triple {0, c1, c2} has a word agreeing
// with each member on at least T positions (exactly, by enumeration of all pairs that can reach T).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t mul[16][16];
static uint64_t st;
static uint64_t rnd(void) {
    uint64_t z = (st += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline int zeros(uint64_t w) {
    uint64_t m = (w | (w >> 1) | (w >> 2) | (w >> 3)) & 0x1111111111111111ULL;
    return 16 - __builtin_popcountll(m);
}
static uint64_t scale(uint64_t w, int a) {
    uint64_t r = 0;
    for (int x = 0; x < 16; x++) r |= (uint64_t)mul[a][(w >> (4 * x)) & 15] << (4 * x);
    return r;
}
// largest A such that a word agrees with each of the three members on at least A positions
static int best(int z0, int u1, int u2, int u3, int T) {
    int bestA = 0, r = 16 - z0 - u1 - u2 - u3;
    int slack = 16 + u1 + u2 + u3 + 2 * z0 - 3 * T; // each handed-over position lowers the total agreement by one
    for (int v1 = 0; v1 <= u1 && v1 <= slack; v1++)
        for (int v2 = 0; v2 <= u2 && v1 + v2 <= slack; v2++)
            for (int v3 = 0; v3 <= u3 && v1 + v2 + v3 <= slack; v3++) { // v_i pair positions handed to the third member instead
                int m0 = z0 + (u1 - v1) + (u2 - v2) + v3, m1 = z0 + (u1 - v1) + (u3 - v3) + v2,
                    m2 = z0 + (u2 - v2) + (u3 - v3) + v1;
                for (int a = 16; a > bestA; a--) {
                    int need = (a > m0 ? a - m0 : 0) + (a > m1 ? a - m1 : 0) + (a > m2 ? a - m2 : 0);
                    if (need <= r) { bestA = a; break; }
                }
            }
    return bestA;
}

int main(int argc, char **argv) {
    const char *type = argv[1];
    int k = atoi(argv[2]), T = atoi(argv[4]);
    int part = argc > 5 ? atoi(argv[5]) : 0, nparts = argc > 6 ? atoi(argv[6]) : 1;
    st = strtoull(argv[3], 0, 10) * 0x100000001B3ULL + 7;
    for (int a = 0; a < 16; a++)
        for (int b = 0; b < 16; b++) {
            int r = 0, x = a;
            for (int i = 0; i < 4; i++) {
                if ((b >> i) & 1) r ^= x;
                x <<= 1;
                if (x & 16) x ^= 0x13;
            }
            mul[a][b] = r;
        }
    uint8_t G[8][16];
    uint8_t pw[16][8];
    for (int x = 0; x < 16; x++) {
        pw[x][0] = 1;
        for (int j = 1; j < 8; j++) pw[x][j] = mul[pw[x][j - 1]][x];
    }
    for (int x = 0; x < 16; x++) {
        if (!strcmp(type, "rs")) {
            for (int j = 0; j < k; j++) G[j][x] = pw[x][j];
        } else if (!strcmp(type, "mix")) {
            int w[5] = {x, x ^ 1, x ^ 2, x ^ 4, x ^ 8};
            for (int j = 0; j < k; j++) G[j][x] = 0;
            for (int c = 0; c < 5; c++) {
                int mu = rnd() & 15;
                for (int j = 0; j < k; j++) G[j][x] ^= mul[mu][pw[w[c]][j]];
            }
        } else {
            for (int j = 0; j < k; j++) G[j][x] = rnd() & 15;
        }
    }
    uint64_t tab[8][16];
    for (int j = 0; j < k; j++) {
        uint64_t row = 0;
        for (int x = 0; x < 16; x++) row |= (uint64_t)G[j][x] << (4 * x);
        for (int a = 0; a < 16; a++) tab[j][a] = scale(row, a);
    }
    // pass 1: zero-count histogram of all codewords; pass 2: store the codewords with enough zeros
    uint64_t total = 1ULL << (4 * k), hist[17] = {0};
    int zmax = 0, zstore = 17;
    uint64_t *bucket[17] = {0}, cnt[17] = {0};
    for (int pass = 0; pass < 2; pass++) {
        for (uint64_t hi = 0; hi < (total >> 8); hi++) {
            uint64_t base = 0;
            for (int j = 2; j < k; j++) base ^= tab[j][(hi >> (4 * (j - 2))) & 15];
            for (int a = 0; a < 16; a++) {
                uint64_t b1 = base ^ tab[1][a];
                for (int b = 0; b < 16; b++) {
                    uint64_t w = b1 ^ tab[0][b];
                    int z = zeros(w);
                    if (pass == 0) hist[z]++;
                    else if (z >= zstore && z < 16) bucket[z][cnt[z]++] = w;
                }
            }
        }
        if (pass == 0) {
            for (int z = 0; z < 16; z++)
                if (hist[z]) zmax = z;
            if (part == 0) {
                printf("%s k=%d seed=%s: nonzero codewords by number of zeros:", type, k, argv[3]);
                for (int z = zmax; z >= 0 && z >= zmax - 5; z--) printf(" %d:%llu", z, (unsigned long long)hist[z]);
                printf("  min distance=%d (Singleton %d)%s\n", 16 - zmax, 16 - k + 1, hist[16] > 1 ? " NOT INJECTIVE" : "");
            }
            // a triple reaching T has z1 >= z2 >= z3, z1 + z2 + z3 >= 3T - 16, so z2 >= ceil((3T - 16 - zmax) / 2)
            zstore = (3 * T - 16 - zmax + 1) / 2;
            if (zstore < 0) zstore = 0;
            for (int z = zstore; z <= zmax; z++) bucket[z] = malloc(8 * (hist[z] + 1));
        }
    }
    double hits[17] = {0}, collinear = 0;
    uint64_t pairs = 0;
    for (int z1 = zmax; 3 * z1 >= 3 * T - 16 && z1 >= zstore; z1--)
        for (uint64_t i = 0; i < cnt[z1]; i++) {
            uint64_t c1 = bucket[z1][i];
            int lowest = (c1 >> (4 * (__builtin_ctzll(c1) / 4))) & 15;
            if (lowest != 1 || (int)(i % nparts) != part) continue;
            int z2min = (3 * T - 16 - z1 + 1) / 2;
            if (z2min < zstore) z2min = zstore;
            for (int z2 = z1; z2 >= z2min; z2--)
                for (uint64_t j = 0; j < cnt[z2]; j++) {
                    uint64_t c2 = bucket[z2][j];
                    int z3 = zeros(c1 ^ c2);
                    if (z3 > z2 || z1 + z2 + z3 < 3 * T - 16) continue;
                    pairs++;
                    int z0 = zeros(c1 | c2);
                    if (z1 + z2 + z3 - z0 < 3 * T - 16) continue;
                    int A = best(z0, z1 - z0, z2 - z0, z3 - z0, T);
                    if (A < T) continue;
                    int dep = 0;
                    for (int a = 2; a < 16 && !dep; a++) dep = (scale(c1, a) == c2);
                    double mult = (z1 == z2 && z2 == z3) ? 6 : (z1 == z2 || z2 == z3) ? 2 : 1;
                    if (dep) collinear += 6 / mult;
                    else hits[A] += 6 / mult;
                }
        }
    printf("%s k=%d seed=%s T=%d part %d/%d: zmax=%d stored>=%d candidate pairs=%llu; ordered independent pairs by best agreement:",
           type, k, argv[3], T, part, nparts, zmax, zstore, (unsigned long long)pairs);
    for (int a = 16; a >= T; a--)
        if (hits[a] > 0) printf(" %d:%.0f", a, hits[a]);
    printf("  collinear:%.0f\n", collinear);
    return 0;
}
