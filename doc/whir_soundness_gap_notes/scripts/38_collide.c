/* Note 38, section 2: exact collision statistics of list families at DEEP points, on toy fields.
   Field E = GF(2^12), K = GF(2^6) its subfield, D = span(1, b, .., b^(N-1)) inside K (b a generator of K).
   Every member is "common word minus the locator of S", so two members collide at zeta iff
   Z_S(zeta) = Z_S'(zeta), Z_S = prod_{x in S} (X + x). Input (stdin): N, then one hex mask per member.
   Output: per class of zeta (in D, in K minus D, in E minus K) the number of colliding pairs, the largest
   set of members sharing one value, and the random-model prediction; then the same for two points.
   cc -O2 -o 38_collide 38_collide.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define EDEG 12
#define Q (1 << EDEG)
#define KQ 64
static int ex[2 * Q], lg[Q];
static int dom[64], n, N, L;
static uint64_t *mask;
static uint16_t *val; /* val[zeta * L + a] */
static uint8_t cls[Q]; /* 0: in D, 1: in K minus D, 2: in E minus K */
static uint64_t rng = 88172645463325252ULL;
static uint32_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint32_t)(rng >> 16); }
static int mul(int a, int b) { return (a && b) ? ex[lg[a] + lg[b]] : 0; }

static int cmp16(const void *a, const void *b) { return (int)*(const uint16_t *)a - (int)*(const uint16_t *)b; }

int main(int argc, char **argv) {
    int two = argc > 1 ? atoi(argv[1]) : 1;
    int a = 1;
    for (int i = 0; i < Q - 1; i++) { ex[i] = a; lg[a] = i; a <<= 1; if (a >> EDEG) a ^= 0x1053; }
    for (int i = Q - 1; i < 2 * Q; i++) ex[i] = ex[i - (Q - 1)];
    if (scanf("%d", &N) != 1) return 1;
    n = 1 << N;
    int b = ex[(Q - 1) / (KQ - 1)], pw[8]; /* generator of K */
    pw[0] = 1;
    for (int j = 1; j < 8; j++) pw[j] = mul(pw[j - 1], b);
    for (int i = 0; i < n; i++) { dom[i] = 0; for (int j = 0; j < N; j++) if (i >> j & 1) dom[i] ^= pw[j]; }
    for (int z = 0; z < Q; z++) { int t = z; for (int j = 0; j < 6; j++) t = mul(t, t); cls[z] = (t == z) ? 1 : 2; }
    for (int i = 0; i < n; i++) cls[dom[i]] = 0;
    int cap = 1 << 16; mask = malloc(cap * sizeof *mask); L = 0;
    char buf[64];
    while (scanf("%63s", buf) == 1) { if (L == cap) { cap *= 2; mask = realloc(mask, cap * sizeof *mask); } mask[L++] = strtoull(buf, 0, 16); }
    int T = __builtin_popcountll(mask[0]);
    printf("N=%d n=%d |K|=%d |E|=%d members L=%d agreement T=%d\n", N, n, KQ, Q, L, T);
    if (two) val = malloc((size_t)Q * L * sizeof *val);
    uint16_t *row = malloc(L * sizeof *row), *srt = malloc(L * sizeof *srt);
    double pairs[3] = {0, 0, 0}; long cnt[3] = {0, 0, 0}, hit[3] = {0, 0, 0}; int mx[3] = {0, 0, 0};
    for (int z = 0; z < Q; z++) {
        int lz[64];
        for (int i = 0; i < n; i++) lz[i] = (z ^ dom[i]) ? lg[z ^ dom[i]] : -1;
        for (int m = 0; m < L; m++) {
            uint64_t s = mask[m]; long acc = 0; int zero = 0;
            while (s) { int i = __builtin_ctzll(s); s &= s - 1; if (lz[i] < 0) { zero = 1; break; } acc += lz[i]; }
            row[m] = zero ? 0 : (uint16_t)ex[acc % (Q - 1)];
        }
        if (two) memcpy(val + (size_t)z * L, row, L * sizeof *row);
        memcpy(srt, row, L * sizeof *row); qsort(srt, L, sizeof *srt, cmp16);
        double p = 0; int best = 1;
        for (int i = 0; i < L;) { int j = i; while (j < L && srt[j] == srt[i]) j++; double c = j - i; p += c * (c - 1) / 2; if (j - i > best) best = j - i; i = j; }
        int c = cls[z]; pairs[c] += p; cnt[c]++; if (p > 0) hit[c]++; if (best > mx[c]) mx[c] = best;
    }
    double C2 = (double)L * (L - 1) / 2;
    const char *nm[3] = {"zeta in D      ", "zeta in K \\ D  ", "zeta in E \\ K  "};
    double bins[3] = {0, KQ, Q};
    printf("one point: class, #zeta, #zeta with a colliding pair, mean colliding pairs, largest clique, random model (pairs = C(L,2)/bins)\n");
    for (int c = 0; c < 3; c++) {
        printf("  %s %5ld %5ld  %12.2f  %6d", nm[c], cnt[c], hit[c], pairs[c] / cnt[c], mx[c]);
        if (c) printf("   model %.2f\n", C2 / bins[c]); else printf("   (members through a column: L*T/n = %.1f, C(.,2) = %.1f)\n", (double)L * T / n, ((double)L * T / n) * ((double)L * T / n - 1) / 2);
    }
    printf("  union bound C(L,2)*eps with eps = k/q (k = n/2 or n/4): not evaluated here; exact Pr[some pair collides at one uniform point] = %.5f\n", (double)(hit[0] + hit[1] + hit[2]) / Q);
    if (!two) return 0;
    /* two points */
    static uint16_t tab[1 << 24]; uint32_t *touched = malloc(L * sizeof *touched);
    int *ek = malloc(Q * sizeof *ek), nek = 0;
    for (int z = 0; z < Q; z++) if (cls[z] == 2) ek[nek++] = z;
    /* (i) both in D, distinct */
    long cov = 0, tot = 0; double sp = 0, sc = 0; int mxc = 0;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        if (i == j) continue;
        const uint16_t *v1 = val + (size_t)dom[i] * L, *v2 = val + (size_t)dom[j] * L; int nt = 0, best = 1; double p = 0;
        for (int m = 0; m < L; m++) { uint32_t key = (uint32_t)v1[m] << 12 | v2[m]; if (!tab[key]) touched[nt++] = key; tab[key]++; }
        for (int t = 0; t < nt; t++) { double c = tab[touched[t]]; p += c * (c - 1) / 2; if (tab[touched[t]] > best) best = tab[touched[t]]; tab[touched[t]] = 0; }
        tot++; if (p > 0) cov++; sp += p; sc += best; if (best > mxc) mxc = best;
    }
    printf("two points, both in D (all %ld ordered pairs): fraction with a pair colliding at both %.4f, mean pairs %.1f, mean clique %.1f, largest %d (L*(T/n)^2 = %.1f)\n",
           tot, (double)cov / tot, sp / tot, sc / tot, mxc, (double)L * T * T / n / n);
    /* (ii) one in D, one in E minus K */
    cov = tot = 0; sp = sc = 0; mxc = 0; double model = 0;
    for (int i = 0; i < n; i++) {
        int Lx = 0; for (int m = 0; m < L; m++) if (mask[m] >> i & 1) Lx++;
        for (int r = 0; r < 400; r++) {
            int z2 = ek[rnd() % nek];
            const uint16_t *v1 = val + (size_t)dom[i] * L, *v2 = val + (size_t)z2 * L; int nt = 0, best = 1; double p = 0;
            for (int m = 0; m < L; m++) { if (!(mask[m] >> i & 1)) continue; uint32_t key = v2[m]; if (!tab[key]) touched[nt++] = key; tab[key]++; }
            (void)v1;
            for (int t = 0; t < nt; t++) { double c = tab[touched[t]]; p += c * (c - 1) / 2; if (tab[touched[t]] > best) best = tab[touched[t]]; tab[touched[t]] = 0; }
            tot++; if (p > 0) cov++; sp += p; sc += best; if (best > mxc) mxc = best; model += (double)Lx * (Lx - 1) / 2 / Q;
        }
    }
    printf("two points, one in D and one in E \\ K (%ld samples), members through the column only: fraction with a colliding pair %.4f, mean pairs %.3f (model C(L_x,2)/q = %.3f), largest clique %d\n",
           tot, (double)cov / tot, sp / tot, model / tot, mxc);
    /* (iii) both in E minus K */
    cov = tot = 0; sp = 0; mxc = 0;
    for (int r = 0; r < 300000; r++) {
        int z1 = ek[rnd() % nek], z2 = ek[rnd() % nek];
        const uint16_t *v1 = val + (size_t)z1 * L, *v2 = val + (size_t)z2 * L; int nt = 0, best = 1; double p = 0;
        for (int m = 0; m < L; m++) { uint32_t key = (uint32_t)v1[m] << 12 | v2[m]; if (!tab[key]) touched[nt++] = key; tab[key]++; }
        for (int t = 0; t < nt; t++) { double c = tab[touched[t]]; p += c * (c - 1) / 2; if (tab[touched[t]] > best) best = tab[touched[t]]; tab[touched[t]] = 0; }
        tot++; if (p > 0) cov++; sp += p; if (best > mxc) mxc = best;
    }
    printf("two points, both in E \\ K (%ld samples): fraction with a pair colliding at both %.5f, mean pairs %.5f (model C(L,2)/q^2 = %.5f), largest clique %d\n",
           tot, (double)cov / tot, sp / tot, C2 / Q / Q, mxc);
    return 0;
}
