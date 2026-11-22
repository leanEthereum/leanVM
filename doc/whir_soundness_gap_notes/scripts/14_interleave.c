/* Note 14, Theorem I (interleaving reduction): exhaustive check at toy sizes.
 *
 * Code: polynomials of degree <= d over F = GF(2^m), evaluated on D = span(1, x, .., x^(N-1)), n = 2^N.
 * For EVERY word (one representative per coset of the code) the full list at agreement A is computed, as the
 * set of its members' agreement masks (its "profile"). Then, exactly:
 *   L1 = max single-lane list,
 *   L2, L3 = max list of a 2-lane, 3-lane interleaved word (max over pairs/triples of profiles of the number of
 *            member tuples whose common agreement set has at least A columns),
 * and they are compared with the bound N_{L1,g}(n - d) of Theorem I, g = A - d:
 *   N(P) = 1 if P < 2g, else N(P - g) + (L1 - 1) N(floor(P / 2)).
 * Also checked on every pair of members of every single-lane list: the two facts the proof uses
 * (shrink(a) + shrink(a') >= |T| - d on T = D).
 *
 * Build: cc -O2 -o interleave14 14_interleave.c ; run: ./interleave14 m N d A
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int m, N, n, d, A, q;
static int EXP[64], LOG[32];
static inline int mul(int a, int b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static inline int inv(int a) { return EXP[(q - 1) - LOG[a]]; }

#define MAXP 128 /* masks per profile */
typedef struct { int len; uint16_t mk[MAXP]; } prof_t;

static int cmp_prof(const void *a, const void *b) {
    const prof_t *p = a, *r = b;
    if (p->len != r->len) return r->len - p->len; /* larger first */
    return memcmp(p->mk, r->mk, sizeof(uint16_t) * p->len);
}
static int cmp_u16(const void *a, const void *b) { return (int)*(const uint16_t *)a - (int)*(const uint16_t *)b; }

static int subset_of(const prof_t *a, const prof_t *b) { /* a subset of b, both sorted */
    int j = 0;
    for (int i = 0; i < a->len; i++) {
        while (j < b->len && b->mk[j] < a->mk[i]) j++;
        if (j == b->len || b->mk[j] != a->mk[i]) return 0;
        j++;
    }
    return 1;
}

static unsigned long long bound_N(long P, long g, unsigned long long L) {
    if (P < 2 * g) return 1;
    return bound_N(P - g, g, L) + (L - 1) * bound_N(P / 2, g, L);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s m N d A\n", argv[0]); return 1; }
    m = atoi(argv[1]); N = atoi(argv[2]); d = atoi(argv[3]); A = atoi(argv[4]);
    q = 1 << m; n = 1 << N;
    int poly = m == 3 ? 0xb : m == 4 ? 0x13 : m == 5 ? 0x25 : 0;
    if (!poly || N > m || n > 16 || d + 1 > A || A > n) { fprintf(stderr, "bad parameters\n"); return 1; }
    int v = 1;
    for (int i = 0; i < q - 1; i++) { EXP[i] = EXP[i + q - 1] = v; LOG[v] = i; v <<= 1; if (v & q) v ^= poly; }
    /* domain points: the integers 0..n-1 are the span of 1, x, .., x^(N-1) */
    int k = d + 1, rest = n - k;
    /* all k-subsets S with their extension matrices: value at y (not in S) = sum_s ext[y][s] w[s] */
    int nsub = 0, cap = 1 << 16;
    uint16_t *smask = malloc(cap * sizeof(uint16_t));
    uint8_t *ext = malloc((size_t)cap * 16 * 16);
    for (int S = 0; S < (1 << n); S++) {
        if (__builtin_popcount(S) != k) continue;
        if (nsub == cap) { fprintf(stderr, "too many subsets\n"); return 1; }
        smask[nsub] = (uint16_t)S;
        for (int y = 0; y < n; y++) {
            if (S >> y & 1) continue;
            for (int s = 0; s < n; s++) {
                if (!(S >> s & 1)) continue;
                int num = 1, den = 1;
                for (int t = 0; t < n; t++)
                    if ((S >> t & 1) && t != s) { num = mul(num, y ^ t); den = mul(den, s ^ t); }
                ext[((size_t)nsub * 16 + y) * 16 + s] = (uint8_t)mul(num, inv(den));
            }
        }
        nsub++;
    }
    /* words: zero on the first k points, free on the others */
    unsigned long long nwords = 1;
    for (int i = 0; i < rest; i++) nwords *= q;
    size_t pcap = 1 << 16, np = 0;
    prof_t *profs = malloc(pcap * sizeof(prof_t));
    int L1 = 0, overflow = 0;
    unsigned long long facts = 0, nonempty = 0;
    int w[16];
    for (unsigned long long idx = 0; idx < nwords; idx++) {
        unsigned long long t = idx;
        for (int i = 0; i < k; i++) w[i] = 0;
        for (int i = k; i < n; i++) { w[i] = (int)(t % q); t /= q; }
        prof_t p; p.len = 0;
        for (int si = 0; si < nsub; si++) {
            int S = smask[si], mask = S, miss = 0;
            const uint8_t *e = ext + (size_t)si * 256;
            for (int y = 0; y < n && miss <= n - A; y++) {
                if (S >> y & 1) continue;
                int val = 0;
                const uint8_t *row = e + y * 16;
                for (int s = 0; s < n; s++) if (S >> s & 1) val ^= mul(row[s], w[s]);
                if (val == w[y]) mask |= 1 << y; else miss++;
            }
            if (miss > n - A) continue;
            /* canonical subset: the lowest k points of the agreement set */
            int low = 0, c = 0;
            for (int y = 0; y < n && c < k; y++) if (mask >> y & 1) { low |= 1 << y; c++; }
            if (low != S) continue;
            if (p.len == MAXP) { overflow = 1; break; }
            p.mk[p.len++] = (uint16_t)mask;
        }
        if (p.len == 0) continue;
        nonempty++;
        if (p.len > L1) L1 = p.len;
        /* the proof's fact at the root (T = D): two members a != a' have shrink(a) + shrink(a') >= n - d */
        for (int i = 0; i < p.len; i++)
            for (int j = i + 1; j < p.len; j++) {
                int sa = n - __builtin_popcount(p.mk[i]), sb = n - __builtin_popcount(p.mk[j]);
                if (sa + sb < n - d) { printf("FACT VIOLATED\n"); return 2; }
                facts++;
            }
        if (p.len == 1) { /* singletons: keep only inclusion-relevant ones later; store all, dedupe below */ }
        qsort(p.mk, p.len, sizeof(uint16_t), cmp_u16);
        if (np == pcap) {
            /* compact: sort + unique */
            qsort(profs, np, sizeof(prof_t), cmp_prof);
            size_t o = 0;
            for (size_t i = 0; i < np; i++) if (o == 0 || cmp_prof(&profs[o - 1], &profs[i])) profs[o++] = profs[i];
            np = o;
            if (np > pcap / 2) { pcap *= 2; profs = realloc(profs, pcap * sizeof(prof_t)); }
        }
        profs[np++] = p;
    }
    qsort(profs, np, sizeof(prof_t), cmp_prof);
    size_t o = 0;
    for (size_t i = 0; i < np; i++) if (o == 0 || cmp_prof(&profs[o - 1], &profs[i])) profs[o++] = profs[i];
    np = o;
    /* inclusion-maximal profiles (sorted by decreasing size, so a superset comes earlier) */
    prof_t *mx = malloc(np * sizeof(prof_t));
    size_t nm = 0;
    for (size_t i = 0; i < np; i++) {
        int dominated = 0;
        for (size_t j = 0; j < nm && !dominated; j++)
            if (mx[j].len > profs[i].len && subset_of(&profs[i], &mx[j])) dominated = 1;
        if (!dominated) mx[nm++] = profs[i];
    }
    /* two lanes, exact */
    unsigned long long L2 = 0, L3 = 0;
    for (size_t i = 0; i < nm; i++)
        for (size_t j = i; j < nm; j++) {
            unsigned long long c = 0;
            for (int a = 0; a < mx[i].len; a++)
                for (int b = 0; b < mx[j].len; b++)
                    if (__builtin_popcount(mx[i].mk[a] & mx[j].mk[b]) >= A) c++;
            if (c > L2) L2 = c;
        }
    /* three lanes, exact when the number of maximal profiles allows it */
    int did3 = nm <= 1500;
    if (did3) {
        uint16_t *tmp = malloc(MAXP * MAXP * sizeof(uint16_t));
        for (size_t i = 0; i < nm; i++)
            for (size_t j = i; j < nm; j++) {
                int nt = 0;
                for (int a = 0; a < mx[i].len; a++)
                    for (int b = 0; b < mx[j].len; b++) {
                        int z = mx[i].mk[a] & mx[j].mk[b];
                        if (__builtin_popcount(z) >= A) tmp[nt++] = (uint16_t)z;
                    }
                if (nt == 0) continue;
                for (size_t l = j; l < nm; l++) {
                    unsigned long long c = 0;
                    for (int a = 0; a < nt; a++)
                        for (int b = 0; b < mx[l].len; b++)
                            if (__builtin_popcount(tmp[a] & mx[l].mk[b]) >= A) c++;
                    if (c > L3) L3 = c;
                }
            }
    }
    long g = A - d, P0 = n - d;
    unsigned long long B = bound_N(P0, g, (unsigned long long)L1);
    printf("GF(2^%d) n=%d d=%d A=%d g=%ld Phi0=%ld | words %llu (nonempty %llu) profiles %zu maximal %zu%s | L1=%d L2=%llu L3=%s%llu | N(L1)=%llu | pair facts %llu ok | %s\n",
           m, n, d, A, g, P0, nwords, nonempty, np, nm, overflow ? " OVERFLOW" : "", L1, L2, did3 ? "" : "(skipped)", L3, B, facts,
           (L2 <= B && L3 <= B) ? "bound holds" : "BOUND VIOLATED");
    return (L2 <= B && L3 <= B) ? 0 : 3;
}
