// Note 42 (referee of note 36): exact probabilities of the star events E_T on toy fields, t = 3.
//
// Field GF(p), p prime; polynomials of degree < k (k = 2 or 3); n evaluation points, an ordered tuple of
// distinct field elements, uniform. By translation f_1 = 0; the two other members are g2, g3, nonzero
// and distinct. A constraint pattern gives each coordinate one of
//   0: nothing   1: g2(a_i) = 0   2: g3(a_i) = 0   3: g2(a_i) = g3(a_i)   4: g2(a_i) = g3(a_i) = 0
// and E_P is the event that some (g2, g3) satisfies all of them. In the notation of note 36 these are
// the labels nothing, D_{2}, D_{3}, C_{23}, D_{23}. The program computes, for every one of the 5^n
// patterns, the exact number of point tuples for which E_P holds, by enumerating every point tuple
// (normalized by the affine symmetry x -> u x + v to a_1 = 0, a_2 = 1, which preserves every event)
// and every pair (g2, g3). It checks that the count depends only on the numbers of labels of each kind
// (exchangeability) and prints one line per count vector:
//   n1 n2 n3 n4 count total pairs
// where pairs is the number of (point tuple, g2, g3) satisfying the pattern: pairs / total is the expected
// number of bad configurations, the quantity that the first-moment proofs bound.
//
// With argument "lists" and k = 2 it also enumerates, for every point tuple, every word (normalized by
// translation by a codeword to y_1 = y_2 = 0) and prints the distribution of the largest list at each
// agreement A:  L A maxlist number_of_point_tuples
//
// Build: cc -O2 -o 42_toy 42_toy.c      Usage: ./42_toy p n k [lists]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 8
static int p, n, k;
static int a[MAXN];
static long npat;
static unsigned char *mark, *closed;
static long *count;
static unsigned *sigcnt;
static unsigned long long *psum, *pairs;
static long total;
static int npoly;
static int *val;                 // val[g * n + i] = g(a_i)
static long hist[MAXN + 1][64];  // hist[A][maxlist]
static int do_lists;

static int eval(int g, int x) {
    int c[3], r = 0;
    for (int j = 0; j < k; j++) { c[j] = g % p; g /= p; }
    for (int j = k - 1; j >= 0; j--) r = (r * x + c[j]) % p;
    return r;
}

static void lists(void) {
    // words with y_1 = y_2 = 0; lines y = c0 + c1 x; largest list at each agreement threshold
    int y[MAXN], best[MAXN + 1];
    for (int A = 0; A <= n; A++) best[A] = 0;
    long nw = 1;
    for (int i = 2; i < n; i++) nw *= p;
    int *agr = malloc(sizeof(int) * npoly);
    for (long w = 0; w < nw; w++) {
        long r = w;
        y[0] = y[1] = 0;
        for (int i = 2; i < n; i++) { y[i] = r % p; r /= p; }
        int cnt[MAXN + 1];
        for (int A = 0; A <= n; A++) cnt[A] = 0;
        for (int g = 0; g < npoly; g++) {
            int c = 0;
            for (int i = 0; i < n; i++) c += (val[g * n + i] == y[i]);
            cnt[c]++;
        }
        int cum = 0;
        for (int A = n; A >= 0; A--) { cum += cnt[A]; if (cum > best[A]) best[A] = cum; }
    }
    free(agr);
    for (int A = k; A <= n; A++) hist[A][best[A] < 63 ? best[A] : 63]++;
}

static void one_tuple(void) {
    total++;
    for (int g = 0; g < npoly; g++)
        for (int i = 0; i < n; i++) val[g * n + i] = eval(g, a[i]);
    memset(mark, 0, npat);
    memset(sigcnt, 0, sizeof(unsigned) * npat);
    for (int g2 = 1; g2 < npoly; g2++) {
        const int *v2 = val + g2 * n;
        for (int g3 = 1; g3 < npoly; g3++) {
            if (g3 == g2) continue;
            const int *v3 = val + g3 * n;
            long idx = 0, mul = 1;
            for (int i = 0; i < n; i++) {
                int s;
                if (v2[i] == 0) s = (v3[i] == 0) ? 4 : 1;
                else if (v3[i] == 0) s = 2;
                else s = (v2[i] == v3[i]) ? 3 : 0;
                idx += s * mul;
                mul *= 5;
            }
            mark[idx] = 1;
            sigcnt[idx]++;
        }
    }
    // downward closure: pattern c is satisfied by signature s iff c = 0, c = s, or s = 4
    memcpy(closed, mark, npat);
    long mul = 1;
    for (int i = 0; i < n; i++) {
        for (long base = 0; base < npat; base++) {
            if ((base / mul) % 5 != 0) continue;
            unsigned char s1 = closed[base + mul], s2 = closed[base + 2 * mul], s3 = closed[base + 3 * mul], s4 = closed[base + 4 * mul];
            closed[base + mul] = s1 | s4;
            closed[base + 2 * mul] = s2 | s4;
            closed[base + 3 * mul] = s3 | s4;
            closed[base] = closed[base] | s1 | s2 | s3 | s4;
        }
        mul *= 5;
    }
    for (long P = 0; P < npat; P++) count[P] += closed[P];
    // the same transform with sums: number of pairs satisfying each pattern
    for (long P = 0; P < npat; P++) psum[P] = sigcnt[P];
    mul = 1;
    for (int i = 0; i < n; i++) {
        for (long base = 0; base < npat; base++) {
            if ((base / mul) % 5 != 0) continue;
            unsigned long long s1 = psum[base + mul], s2 = psum[base + 2 * mul], s3 = psum[base + 3 * mul], s4 = psum[base + 4 * mul];
            psum[base + mul] = s1 + s4;
            psum[base + 2 * mul] = s2 + s4;
            psum[base + 3 * mul] = s3 + s4;
            psum[base] += s1 + s2 + s3 + s4;
        }
        mul *= 5;
    }
    for (long P = 0; P < npat; P++) pairs[P] += psum[P];
    if (do_lists) lists();
}

static void rec(int i, unsigned used) {
    if (i == n) { one_tuple(); return; }
    for (int x = 0; x < p; x++) {
        if (used >> x & 1) continue;
        a[i] = x;
        rec(i + 1, used | 1u << x);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s p n k [lists]\n", argv[0]); return 1; }
    p = atoi(argv[1]); n = atoi(argv[2]); k = atoi(argv[3]);
    do_lists = argc > 4 && k == 2;
    if (p > 31 || n > MAXN || k < 2 || k > 3) return 1;
    npat = 1;
    for (int i = 0; i < n; i++) npat *= 5;
    npoly = 1;
    for (int j = 0; j < k; j++) npoly *= p;
    mark = malloc(npat); closed = malloc(npat);
    count = calloc(npat, sizeof(long));
    sigcnt = malloc(sizeof(unsigned) * npat);
    psum = malloc(sizeof(unsigned long long) * npat);
    pairs = calloc(npat, sizeof(unsigned long long));
    val = malloc(sizeof(int) * npoly * n);
    a[0] = 0; a[1] = 1;
    rec(2, 3u);
    // aggregate by label counts and check exchangeability
    static long agg[MAXN + 1][MAXN + 1][MAXN + 1][MAXN + 1];
    static unsigned long long aggp[MAXN + 1][MAXN + 1][MAXN + 1][MAXN + 1];
    memset(agg, 0xff, sizeof agg);
    int bad = 0;
    for (long P = 0; P < npat; P++) {
        int c[5] = {0, 0, 0, 0, 0};
        long r = P;
        for (int i = 0; i < n; i++) { c[r % 5]++; r /= 5; }
        long *slot = &agg[c[1]][c[2]][c[3]][c[4]];
        if (*slot < 0) { *slot = count[P]; aggp[c[1]][c[2]][c[3]][c[4]] = pairs[P]; }
        else if (*slot != count[P] || aggp[c[1]][c[2]][c[3]][c[4]] != pairs[P]) bad++;
    }
    printf("# p=%d n=%d k=%d point tuples (a1=0, a2=1)=%ld exchangeability violations=%d\n", p, n, k, total, bad);
    for (int c1 = 0; c1 <= n; c1++) for (int c2 = 0; c1 + c2 <= n; c2++) for (int c3 = 0; c1 + c2 + c3 <= n; c3++)
        for (int c4 = 0; c1 + c2 + c3 + c4 <= n; c4++)
            printf("%d %d %d %d %ld %ld %llu\n", c1, c2, c3, c4, agg[c1][c2][c3][c4], total, aggp[c1][c2][c3][c4]);
    if (do_lists)
        for (int A = k; A <= n; A++) for (int L = 0; L < 64; L++)
            if (hist[A][L]) printf("L %d %d %ld\n", A, L, hist[A][L]);
    return 0;
}
