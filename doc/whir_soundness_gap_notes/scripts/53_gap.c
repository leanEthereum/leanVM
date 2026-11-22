/* 53_gap.c: does the code at infinity on a small-field domain keep the weight gap of RM(2, N)?
 * (Section 5.4 of 53-goppa-structure-degenerate.md.)
 *
 * Input: a basis of Gamma = Gamma_inf(g) written by `53_codes inf N m kind seed file g` (truth tables on F_2^N).
 * RM(2, N) has no word of weight strictly between 3n/8 and 7n/16. The program checks RM(2, N) subset Gamma,
 * takes a basis of Gamma / RM(2, N) (the "extra" words, of Boolean degree >= 3), and looks for words of Gamma
 * with a nonzero extra part and small weight, by randomized descent: moves = add one extra basis vector or one
 * quadratic monomial; the affine part is always optimal (weight = (n - max |Walsh|) / 2).
 * It reports the smallest weight found and the number of distinct words found with weight in [lo, hi).
 *
 *   ./53_gap N basisfile lo hi restarts seed
 * cc -O2 -o 53_gap 53_gap.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096
#define MAXD 1024

static int N, n;
static unsigned char tt[MAXD][MAXN];     /* truth tables of the basis */
static unsigned char anf[MAXD][MAXN];
static int d;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void mobius(unsigned char *a) {
    for (int s = 1; s < n; s <<= 1)
        for (int i = 0; i < n; i++)
            if (i & s) a[i] ^= a[i ^ s];
}

static int best_walsh(const unsigned char *f) {
    static int w[MAXN];
    for (int i = 0; i < n; i++) w[i] = f[i] ? -1 : 1;
    for (int s = 1; s < n; s <<= 1)
        for (int i = 0; i < n; i += 2 * s)
            for (int j = i; j < i + s; j++) { int a = w[j], b = w[j + s]; w[j] = a + b; w[j + s] = a - b; }
    int best = 0;
    for (int i = 0; i < n; i++) { int v = w[i] < 0 ? -w[i] : w[i]; if (v > best) best = v; }
    return best;
}

/* weight of f after the best change by a function a0 + a1 x_0 + x_0 lambda(x') + lambda0(x'), which is in RM(2, N):
 * the two halves x_0 = 0, 1 get independent affine corrections. */
static int best_split(const unsigned char *f) {
    static int w[MAXN];
    int tot = 0, h = n / 2;
    for (int half = 0; half < 2; half++) {
        for (int i = 0; i < h; i++) w[i] = f[2 * i + half] ? -1 : 1;
        for (int s = 1; s < h; s <<= 1)
            for (int i = 0; i < h; i += 2 * s)
                for (int j = i; j < i + s; j++) { int a = w[j], b = w[j + s]; w[j] = a + b; w[j + s] = a - b; }
        int best = 0;
        for (int i = 0; i < h; i++) { int v = w[i] < 0 ? -w[i] : w[i]; if (v > best) best = v; }
        tot += (h - best) / 2;
    }
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: 53_gap N basisfile lo hi restarts seed\n"); return 1; }
    N = atoi(argv[1]); n = 1 << N;
    int lo = atoi(argv[3]), hi = atoi(argv[4]), restarts = atoi(argv[5]);
    rs = strtoull(argv[6], 0, 10) * 0x9E3779B97F4A7C15ULL + 99;
    FILE *fp = fopen(argv[2], "r");
    static char line[MAXN / 4 + 16];
    d = 0;
    while (fgets(line, sizeof line, fp)) {
        int len = (int)strlen(line);
        while (len && (line[len - 1] == '\n' || line[len - 1] == '\r')) len--;
        if (len < n / 4) continue;
        for (int i = 0; i < n; i++) {
            char c = line[len - 1 - i / 4];
            int v = c <= '9' ? c - '0' : c - 'a' + 10;
            tt[d][i] = (v >> (i % 4)) & 1;
        }
        memcpy(anf[d], tt[d], n);
        mobius(anf[d]);
        d++;
    }
    fclose(fp);
    /* echelon form on the monomials of degree >= 3: the vectors with zero high part span Gamma cap RM(2, N) */
    static unsigned char hi_part[MAXD][MAXN], comb_tt[MAXD][MAXN];
    int nextra = 0, nlow = 0, maxdeg = 0;
    static int extra[MAXD];
    static int pivcol[MAXD];
    for (int t = 0; t < d; t++) {
        memcpy(hi_part[t], anf[t], n);
        for (int i = 0; i < n; i++) if (__builtin_popcount(i) <= 2) hi_part[t][i] = 0;
        memcpy(comb_tt[t], tt[t], n);
        for (int e = 0; e < nextra; e++) {
            int p = extra[e];
            if (hi_part[t][pivcol[e]]) {
                for (int i = 0; i < n; i++) { hi_part[t][i] ^= hi_part[p][i]; comb_tt[t][i] ^= comb_tt[p][i]; }
            }
        }
        int pc = -1;
        for (int i = 0; i < n; i++) if (hi_part[t][i]) { pc = i; break; }
        if (pc < 0) nlow++;
        else {
            for (int i = 0; i < n; i++) if (hi_part[t][i] && __builtin_popcount(i) > maxdeg) maxdeg = __builtin_popcount(i);
            pivcol[nextra] = pc; extra[nextra++] = t;
        }
    }
    int rm2 = 1 + N + N * (N - 1) / 2;
    printf("N=%d n=%d: dim Gamma = %d; dim (Gamma cap RM(2,N)) = %d (RM(2,N): %d); extra dimensions %d, of Boolean "
           "degree up to %d\n", N, n, d, nlow, rm2, nextra, maxdeg);
    if (nlow != rm2 || nextra == 0) { printf("no search (RM(2,N) not contained, or no extra word)\n"); return 0; }
    /* constructive stage: extra words whose part of degree >= 3 is x_0 * (quadratic form in x_1 .. x_{N-1}) */
    {
        static unsigned char ph[MAXD][MAXN], pt2[MAXD][MAXN], xt[MAXD][MAXN], hp[MAXN], tp[MAXN];
        static int pcol[MAXD];
        int nx = 0, npv = 0;
        for (int e = 0; e < nextra; e++) {
            memcpy(hp, hi_part[extra[e]], n); memcpy(tp, comb_tt[extra[e]], n);
            for (int q = 0; q < npv; q++)
                if (hp[pcol[q]]) for (int i = 0; i < n; i++) { hp[i] ^= ph[q][i]; tp[i] ^= pt2[q][i]; }
            /* forbidden monomials: degree >= 4, or degree 3 without x_0 */
            int pc = -1;
            for (int i = 0; i < n; i++) if (hp[i] && (__builtin_popcount(i) >= 4 || !(i & 1))) { pc = i; break; }
            if (pc >= 0) { memcpy(ph[npv], hp, n); memcpy(pt2[npv], tp, n); pcol[npv++] = pc; }
            else memcpy(xt[nx++], tp, n);
        }
        printf("   extra words with high part x_0 * (quadratic form): dimension %d (count bound C(N-1,2) - 2m)\n", nx);
        if (nx > 0) {
            static unsigned char ff[MAXN];
            int trials = 0, hits = 0, minw = n;
            static int wh[MAXN + 1];
            for (int t = 0; t < 4000; t++) {
                memset(ff, 0, n);
                int any = 0;
                for (int e = 0; e < nx; e++) if (rnd() & 1) { any = 1; for (int i = 0; i < n; i++) ff[i] ^= xt[e][i]; }
                if (!any) continue;
                /* q_0 = x_a x_b + x_c x_d on four distinct variables among x_1 .. x_{N-1} */
                int v[4];
                for (int c = 0; c < 4; c++) { int ok; do { ok = 1; v[c] = 1 + (int)(rnd() % (N - 1)); for (int c2 = 0; c2 < c; c2++) if (v[c2] == v[c]) ok = 0; } while (!ok); }
                for (int i = 0; i < n; i++) ff[i] ^= (((i >> v[0]) & (i >> v[1])) ^ ((i >> v[2]) & (i >> v[3]))) & 1;
                int w = best_split(ff);
                trials++; wh[w]++;
                if (w < minw) minw = w;
                if (w >= lo && w < hi) hits++;
            }
            printf("   x_0 Q + q_0 (q_0 of rank 4), halves corrected independently: %d trials, %d with weight in [%d, %d), "
                   "smallest %d; weights:", trials, hits, lo, hi, minw);
            for (int w = 0; w <= n; w++) if (wh[w]) printf(" %d:%d", w, wh[w]);
            printf("\n");
        }
    }
    /* quadratic monomials */
    int nq = N * (N - 1) / 2;
    static int qa[512], qb[512];
    { int c = 0; for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) { qa[c] = a; qb[c] = b; c++; } }
    static unsigned char f[MAXN], g[MAXN];
    static unsigned char coef[MAXD];
    int globalmin = n, inwin = 0, total_local = 0;
    static int hist[MAXN + 1];
    uint64_t seen[4096]; int nseen = 0;
    for (int r = 0; r < restarts; r++) {
        memset(f, 0, n); memset(coef, 0, nextra);
        int nz = 0;
        /* start: a sparse random extra combination and a random quadratic form */
        int k0 = 1 + (int)(rnd() % 3);
        for (int c = 0; c < k0; c++) {
            int e = (int)(rnd() % nextra);
            coef[e] ^= 1; nz += coef[e] ? 1 : -1;
            for (int i = 0; i < n; i++) f[i] ^= comb_tt[extra[e]][i];
        }
        if (!nz) { r--; continue; }
        for (int c = 0; c < nq; c++) if (rnd() & 1) for (int i = 0; i < n; i++) f[i] ^= ((i >> qa[c]) & (i >> qb[c]) & 1);
        int cur = (n - best_walsh(f)) / 2;
        int improved = 1;
        while (improved) {
            improved = 0;
            int nm = nextra + nq, start = (int)(rnd() % nm);
            for (int s = 0; s < nm; s++) {
                int mv = (start + s) % nm;
                if (mv < nextra) {
                    if (coef[mv] && nz == 1) continue;        /* keep the extra part nonzero */
                    for (int i = 0; i < n; i++) g[i] = f[i] ^ comb_tt[extra[mv]][i];
                } else {
                    int c = mv - nextra;
                    for (int i = 0; i < n; i++) g[i] = f[i] ^ ((i >> qa[c]) & (i >> qb[c]) & 1);
                }
                int w = (n - best_walsh(g)) / 2;
                if (w >= lo && w < hi) {
                    uint64_t h = 1469598103934665603ULL;
                    for (int i = 0; i < n; i++) h = (h ^ g[i]) * 1099511628211ULL;
                    int known = 0;
                    for (int q = 0; q < nseen; q++) if (seen[q] == h) known = 1;
                    if (!known && nseen < 4096) { seen[nseen++] = h; inwin++; }
                }
                if (w < cur) {
                    cur = w; memcpy(f, g, n);
                    if (mv < nextra) { coef[mv] ^= 1; nz += coef[mv] ? 1 : -1; }
                    improved = 1;
                }
            }
        }
        hist[cur]++; total_local++;
        if (cur < globalmin) globalmin = cur;
    }
    printf("   %d descents: smallest weight of a word with nonzero extra part: %d (%.4f n); 3n/8 = %d, 7n/16 = %d; "
           "distinct words (up to the affine part) met with weight in [%d, %d): %d%s\n", total_local, globalmin,
           (double)globalmin / n, 3 * n / 8, 7 * n / 16, lo, hi, inwin, nseen == 4096 ? "+" : "");
    printf("   local minima by weight:");
    for (int w = 0; w <= n; w++) if (hist[w]) printf(" %d:%d", w, hist[w]);
    printf("\n");
    return 0;
}
