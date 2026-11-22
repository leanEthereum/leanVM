// Note 42 (referee of note 36): observed against predicted number of bad star configurations, on honest lists.
//
// Lines (k = 2) over GF(p), n = 10 random distinct evaluation points, agreement A = 4, list size M = 5.
// Five distinct lines each agreeing with one word on at least 4 of 10 columns: the lines agreeing at a
// column are concurrent there, two lines meet at most once, so sum_i C(r_i, 2) <= 10 with sum_i r_i >= 20
// forces r_i = 2 everywhere. Hence Bad(4, 5) holds exactly when the ten points are the abscissas of the ten
// intersection points of five lines (a complete 5-lateral), and no word has 6 such lines. The decision is
// therefore exhaustive: enumerate the bijections from pairs {j, j'} to columns, solve for the lines.
//
// A bijection phi is the canonical star labeling T of note 36 for the ordered list (D_{j} at phi{1,j},
// C_{jj'} at phi{j,j'}), with W_D = 4 and g = 6, and Lemma B1 predicts
//   E[number of solvable phi] <= 10! * p^10 / (p)_10 * p^(4*2 - 4) * (1/p)^6 = 10! p^-2 * p^10/(p)_10.
// The program prints the observed mean of the number N of solvable bijections and the frequency of N > 0.
//
// Normalization: by the action of S_5, N = 10 N_0 with N_0 the number of solvable phi with phi{1,2} = column 0.
// Lines: l_1 = 0, l_2 = x - a_12 (scaling), l_j = m_j (x - a_1j).
//
// Build: cc -O2 -o 42_lateral 42_lateral.c     Usage: ./42_lateral p samples seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static uint64_t s;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    int p = atoi(argv[1]);
    long samples = atol(argv[2]);
    s = 0x9E3779B97F4A7C15ull ^ (uint64_t)atol(argv[3]) * 1000003ull;
    int *inv = malloc(sizeof(int) * p);
    inv[1] = 1;
    for (int i = 2; i < p; i++) inv[i] = (int)((long)(p - p / i) * inv[p % i] % p);
    long hits = 0;
    double sumN = 0;
    for (long it = 0; it < samples; it++) {
        int a[10];
        for (int i = 0; i < 10;) {
            int x = (int)(rnd() % (uint64_t)p), ok = 1;
            for (int j = 0; j < i; j++) ok &= a[j] != x;
            if (ok) a[i++] = x;
        }
        long N0 = 0;
        int a12 = a[0];
        // columns 1..9: choose a13, a14, a15, then a23, a24, a25
        for (int i3 = 1; i3 < 10; i3++) for (int i4 = 1; i4 < 10; i4++) { if (i4 == i3) continue;
        for (int i5 = 1; i5 < 10; i5++) { if (i5 == i3 || i5 == i4) continue;
            int a1[3] = {a[i3], a[i4], a[i5]};
            int rest[6], nr = 0;
            for (int i = 1; i < 10; i++) if (i != i3 && i != i4 && i != i5) rest[nr++] = i;
            for (int u3 = 0; u3 < 6; u3++) for (int u4 = 0; u4 < 6; u4++) { if (u4 == u3) continue;
            for (int u5 = 0; u5 < 6; u5++) { if (u5 == u3 || u5 == u4) continue;
                int a2[3] = {a[rest[u3]], a[rest[u4]], a[rest[u5]]};
                long m[3];
                for (int j = 0; j < 3; j++)
                    m[j] = (long)((a2[j] - a12 + p) % p) * inv[(a2[j] - a1[j] + p) % p] % p;
                if (m[0] == m[1] || m[0] == m[2] || m[1] == m[2]) continue;
                int x[3], c = 0;
                for (int j = 0; j < 3; j++) for (int jj = j + 1; jj < 3; jj++) {
                    long num = ((m[j] * a1[j] - m[jj] * a1[jj]) % p + p) % p;
                    x[c++] = (int)(num * inv[(m[j] - m[jj] + p) % p] % p);
                }
                if (x[0] == x[1] || x[0] == x[2] || x[1] == x[2]) continue;
                int left[3], nl = 0, used = 0, ok = 1;
                for (int i = 0; i < 6; i++) if (i != u3 && i != u4 && i != u5) left[nl++] = a[rest[i]];
                for (int j = 0; j < 3 && ok; j++) {
                    int f = 0;
                    for (int l = 0; l < 3; l++) if (!(used >> l & 1) && left[l] == x[j]) { used |= 1 << l; f = 1; break; }
                    ok = f;
                }
                if (ok) N0++;
            }}
        }}
        if (N0) hits++;
        sumN += 10.0 * N0;
    }
    double corr = 1.0;
    for (int i = 0; i < 10; i++) corr *= (double)p / (p - i);
    printf("p=%d samples=%ld  Pr[Bad(4,5)]=%.6f (%ld hits)  observed E[N]=%.5f  Lemma B1 prediction 10! p^-2 corr=%.5f  ratio observed/predicted=%.3e  1/(p-1)=%.3e\n",
           p, samples, (double)hits / samples, hits, sumN / samples, 3628800.0 / ((double)p * p) * corr, sumN / samples / (3628800.0 / ((double)p * p) * corr), 1.0 / (p - 1));
    return 0;
}
