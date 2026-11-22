/* 55_pencils.c: exhaustive search for clean pencils at infinity on a "generic" 5-dimensional subspace
 * (referee test of Theorem 6.2 and Theorem 3.1 of note 53 at toy size; own code).
 *
 * D = span(b_1..b_5), b_i random in GF(2^64) = F_2[x]/(x^64 + x^4 + x^3 + x + 1), n = 32.
 * A clean pencil with polynomial centre psi of degree p and members P_i = psi + c Lambda_{O_i}, O_i subset D,
 * |O_i| = p, deg P_i <= Delta, is a family of p-subsets whose locators agree in the coefficients of
 * X^(p-1), .., X^(Delta+1): e_j(O_i) equal for 1 <= j <= J := p - Delta - 1. Because e_j(D) = 0 for 1 <= j <= 15,
 * this is the same as e_j(C_i) equal for j <= J for the complements C_i = D \ O_i (c = 32 - p points).
 *
 * For a given c the program enumerates ALL c-subsets, groups them by (e_1, e_2, e_3) (two passes: a 2^32-bucket
 * filter on a 64-bit hash, then exact comparison), refines the groups by e_4, .., e_7, and for every level
 * J = 3..7 reports the number of classes with at least two members, the largest class, the weights |C_i xor C_j|
 * inside classes, and whether every difference has Boolean degree <= 2 (J <= 6) or <= 1 (J = 7), which is what
 * Proposition 5.1 predicts (Gamma_inf(J) = RM(2, 5) for 3 <= J <= 6 and RM(1, 5) for J = 7).
 * Every class is re-evaluated on a second random basis: an identity in the formal model holds on both.
 * In a class with more than PAIRCAP members only the pairs that contain one of its first PAIRCAP members are examined.
 *
 *   cc -O2 -o 55_pencils 55_pencils.c ;  ./55_pencils c seed [selftest]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
#include <arm_neon.h>
static inline uint64_t gfmul(uint64_t a, uint64_t b) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    uint64_t lo = (uint64_t)p, hi = (uint64_t)(p >> 64);
    uint64_t top = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    return lo ^ hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4) ^ top ^ (top << 1) ^ (top << 3) ^ (top << 4);
}
#else
static inline uint64_t gfmul(uint64_t a, uint64_t b) {
    uint64_t r = 0;
    for (int i = 63; i >= 0; i--) {
        uint64_t carry = r >> 63;
        r <<= 1;
        if (carry) r ^= 0x1B;
        if ((b >> i) & 1) r ^= a;
    }
    return r;
}
#endif

static uint64_t gfmul_ref(uint64_t a, uint64_t b) {
    uint64_t r = 0;
    for (int i = 63; i >= 0; i--) {
        uint64_t carry = r >> 63;
        r <<= 1;
        if (carry) r ^= 0x1B;
        if ((b >> i) & 1) r ^= a;
    }
    return r;
}

static uint64_t rs;
static uint64_t rnd64(void) {
    rs += 0x9E3779B97F4A7C15ULL;
    uint64_t z = rs;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline uint64_t mix(uint64_t z) {
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

#define NN 5
#define NPT 32
#define JMAX 7
#define PAIRCAP 48
static uint64_t DA[NPT], DB[NPT];

static int f2rank(uint64_t *v, int k) {
    int r = 0;
    for (int bit = 63; bit >= 0; bit--) {
        int p = -1;
        for (int i = r; i < k; i++) if ((v[i] >> bit) & 1) { p = i; break; }
        if (p < 0) continue;
        uint64_t t = v[p]; v[p] = v[r]; v[r] = t;
        for (int i = 0; i < k; i++) if (i != r && ((v[i] >> bit) & 1)) v[i] ^= v[r];
        r++;
    }
    return r;
}

static void make_domain(uint64_t *D, uint64_t *basis) {
    for (int a = 0; a < NPT; a++) {
        uint64_t s = 0;
        for (int i = 0; i < NN; i++) if ((a >> i) & 1) s ^= basis[i];
        D[a] = s;
    }
}

static void esym(const uint64_t *D, uint32_t mask, uint64_t *e) { /* e[1..JMAX] */
    uint64_t t[JMAX + 1];
    memset(t, 0, sizeof t);
    t[0] = 1;
    for (int a = 0; a < NPT; a++)
        if ((mask >> a) & 1)
            for (int j = JMAX; j >= 1; j--) t[j] ^= gfmul(D[a], t[j - 1]);
    for (int j = 1; j <= JMAX; j++) e[j] = t[j];
}

static inline uint64_t key3(uint64_t e1, uint64_t e2, uint64_t e3) { return mix(e3 ^ mix(e2 ^ mix(e1 ^ 0x1234567ULL))); }

static uint8_t *seen1, *seen2;
typedef struct { uint64_t h; uint32_t mask; } rec_t;
static rec_t *cand;
static size_t ncand, capcand;
static uint64_t total;

static void visit(int pass, uint64_t e1, uint64_t e2, uint64_t e3, uint32_t mask) {
    uint64_t h = key3(e1, e2, e3);
    uint32_t b = (uint32_t)(h >> 32);
    if (pass == 1) {
        total++;
        if (seen1[b >> 3] & (1 << (b & 7))) seen2[b >> 3] |= (1 << (b & 7));
        else seen1[b >> 3] |= (1 << (b & 7));
    } else if (seen2[b >> 3] & (1 << (b & 7))) {
        if (ncand == capcand) { capcand = capcand ? 2 * capcand : (1 << 20); cand = realloc(cand, capcand * sizeof(rec_t)); }
        cand[ncand].h = h; cand[ncand].mask = mask; ncand++;
    }
}

static void dfs(int pass, int c, int start, int depth, uint64_t e1, uint64_t e2, uint64_t e3, uint32_t mask) {
    if (depth == c) { visit(pass, e1, e2, e3, mask); return; }
    for (int a = start; a <= NPT - (c - depth); a++) {
        uint64_t x = DA[a];
        dfs(pass, c, a + 1, depth + 1, e1 ^ x, e2 ^ gfmul(x, e1), e3 ^ gfmul(x, e2), mask | (1u << a));
    }
}

static int cmp_rec(const void *a, const void *b) {
    const rec_t *x = a, *y = b;
    if (x->h != y->h) return x->h < y->h ? -1 : 1;
    return x->mask < y->mask ? -1 : (x->mask > y->mask);
}

typedef struct { uint64_t e[JMAX + 1]; uint64_t eb[JMAX + 1]; uint32_t mask; } mem_t;
static int cmp_mem(const void *a, const void *b) {
    const mem_t *x = a, *y = b;
    for (int j = 1; j <= JMAX; j++) if (x->e[j] != y->e[j]) return x->e[j] < y->e[j] ? -1 : 1;
    return x->mask < y->mask ? -1 : (x->mask > y->mask);
}

static int bdeg(uint32_t tt) { /* Boolean degree of the function on F_2^5 with truth table tt */
    uint32_t a = tt;
    for (int i = 0; i < NN; i++) {
        uint32_t s = 1u << i, m = 0;
        for (int x = 0; x < NPT; x++) if (x & s) m |= 1u << x;
        a ^= (a << s) & m;
    }
    int d = -1;
    for (int x = 0; x < NPT; x++) if ((a >> x) & 1) { int w = __builtin_popcount(x); if (w > d) d = w; }
    return d;
}

/* statistics per level J = 3..7 */
static uint64_t nclass[JMAX + 1], maxclass[JMAX + 1], npairs[JMAX + 1], baddeg[JMAX + 1], badB[JMAX + 1];
static uint64_t wt_hist[JMAX + 1][NPT + 1];
static uint64_t size_hist[JMAX + 1][8];   /* sizes 2, 3, 4, 5..8, 9..16, 17..64, 65..512, > 512 */
static uint32_t best_ex[JMAX + 1][16];
static int best_n[JMAX + 1];

static void account(mem_t *g, int k) {
    /* g[0..k) share e_1..e_3 exactly and are sorted by (e_1..e_7) */
    for (int J = 3; J <= JMAX; J++) {
        int i = 0;
        while (i < k) {
            int j = i + 1;
            while (j < k && memcmp(&g[j].e[1], &g[i].e[1], J * sizeof(uint64_t)) == 0) j++;
            int sz = j - i;
            if (sz >= 2) {
                nclass[J]++;
                if ((uint64_t)sz > maxclass[J]) {
                    maxclass[J] = sz;
                    best_n[J] = sz < 16 ? sz : 16;
                    for (int t = 0; t < best_n[J]; t++) best_ex[J][t] = g[i + t].mask;
                }
                int b = sz == 2 ? 0 : sz == 3 ? 1 : sz == 4 ? 2 : sz <= 8 ? 3 : sz <= 16 ? 4 : sz <= 64 ? 5 : sz <= 512 ? 6 : 7;
                size_hist[J][b]++;
                int alim = (sz > PAIRCAP) ? i + PAIRCAP : j;   /* large classes: pairs with the first PAIRCAP members */
                for (int a = i; a < alim; a++)
                    for (int c = a + 1; c < j; c++) {
                        uint32_t T = g[a].mask ^ g[c].mask;
                        npairs[J]++;
                        wt_hist[J][__builtin_popcount(T)]++;
                        if (bdeg(T) > (J <= 6 ? 2 : 1)) baddeg[J]++;
                        if (memcmp(&g[a].eb[1], &g[c].eb[1], J * sizeof(uint64_t)) != 0) badB[J]++;
                    }
            }
            i = j;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: 55_pencils c seed [selftest]\n"); return 1; }
    int c = atoi(argv[1]);
    rs = strtoull(argv[2], 0, 10);
    if (argc > 3) { /* field self test: print products for comparison with 55_lib.py */
        for (int i = 0; i < 4; i++) {
            uint64_t a = rnd64(), b = rnd64();
            printf("selftest %016llx %016llx %016llx %d\n", (unsigned long long)a, (unsigned long long)b,
                   (unsigned long long)gfmul(a, b), gfmul(a, b) == gfmul_ref(a, b));
        }
        return 0;
    }
    uint64_t bA[NN], bB[NN];
    for (;;) { for (int i = 0; i < NN; i++) bA[i] = rnd64(); uint64_t t[NN]; memcpy(t, bA, sizeof t); if (f2rank(t, NN) == NN) break; }
    for (;;) { for (int i = 0; i < NN; i++) bB[i] = rnd64(); uint64_t t[NN]; memcpy(t, bB, sizeof t); if (f2rank(t, NN) == NN) break; }
    make_domain(DA, bA);
    make_domain(DB, bB);
    /* the monomials of degree <= 3 in the basis are F_2-independent in GF(2^64): 5 + 15 + 35 values */
    {
        uint64_t v[64]; int k = 0;
        for (int i = 0; i < NN; i++) for (int j = i; j < NN; j++) for (int l = j; l < NN; l++) v[k++] = gfmul(bA[i], gfmul(bA[j], bA[l]));
        int r3 = f2rank(v, k);
        k = 0;
        for (int i = 0; i < NN; i++) for (int j = i; j < NN; j++) v[k++] = gfmul(bA[i], bA[j]);
        int r2 = f2rank(v, k);
        printf("c = %d: F_2-rank of the monomials of degree 2 and 3 in the basis: %d of 15, %d of 35 "
               "(so equality of e_1, e_2, e_3 in GF(2^64) is the formal identity)\n", c, r2, r3);
    }
    seen1 = calloc(1u << 29, 1);
    seen2 = calloc(1u << 29, 1);
    dfs(1, c, 0, 0, 0, 0, 0, 0);
    dfs(2, c, 0, 0, 0, 0, 0, 0);
    qsort(cand, ncand, sizeof(rec_t), cmp_rec);
    mem_t *grp = 0; size_t capg = 0;
    size_t i = 0;
    while (i < ncand) {
        size_t j = i + 1;
        while (j < ncand && cand[j].h == cand[i].h) j++;
        if (j - i >= 2) {
            size_t k = j - i;
            if (k > capg) { capg = 2 * k; grp = realloc(grp, capg * sizeof(mem_t)); }
            for (size_t t = 0; t < k; t++) {
                grp[t].mask = cand[i + t].mask;
                esym(DA, grp[t].mask, grp[t].e);
                esym(DB, grp[t].mask, grp[t].eb);
            }
            qsort(grp, k, sizeof(mem_t), cmp_mem);
            /* split by exact (e1, e2, e3) (the hash could collide) */
            size_t a = 0;
            while (a < k) {
                size_t b = a + 1;
                while (b < k && memcmp(&grp[b].e[1], &grp[a].e[1], 3 * sizeof(uint64_t)) == 0) b++;
                if (b - a >= 2) account(grp + a, (int)(b - a));
                a = b;
            }
        }
        i = j;
    }
    printf("c = %d (p = %d): %llu subsets, %zu candidates after the filter\n", c, NPT - c, (unsigned long long)total, ncand);
    for (int J = 3; J <= JMAX; J++) {
        int p = NPT - c, Delta = p - J - 1;
        printf("  J = %d (Delta = %d): classes %llu, largest %llu, pairs examined %llu, degree violations %llu, not confirmed on "
               "the second basis %llu; sizes [2,3,4,5-8,9-16,17-64,65-512,>512] =",
               J, Delta, (unsigned long long)nclass[J], (unsigned long long)maxclass[J], (unsigned long long)npairs[J],
               (unsigned long long)baddeg[J], (unsigned long long)badB[J]);
        for (int b = 0; b < 8; b++) printf(" %llu", (unsigned long long)size_hist[J][b]);
        printf("; weights");
        for (int w = 0; w <= NPT; w++) if (wt_hist[J][w]) printf(" %d:%llu", w, (unsigned long long)wt_hist[J][w]);
        printf("\n");
        if (maxclass[J] >= 2 && maxclass[J] <= 16) {
            printf("     a largest class (complements C_i as masks):");
            for (int t = 0; t < best_n[J]; t++) printf(" %08x", best_ex[J][t]);
            printf("\n");
        }
    }
    return 0;
}
