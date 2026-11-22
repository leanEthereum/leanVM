// Note 60: exhaustive search over all vertex subsets of the N-cube, N <= 5.
// cc -O2 -o /tmp/60_small 60_small.c -lpthread ; ./60_small 5
// Outputs:
//  (1) minimal |N[T]| by |T| (Harper check),
//  (2) number of nonempty T by boundary size, split by "N[T] = V" (periodic type) or not,
//      and restricted to |N[T]| <= n/2,
//  (3) minimal two-sided boundary |T \ int T| + |dT| over proper nonempty T,
//  (4) literal separator problem: min over B' of |B'| + (largest component of the rest),
//  (5) interior problem: Xi(m) = max |A| such that every distance-2 component Z of A
//      has |N[Z]| <= m (the Z are the interiors of disjoint fibres of size <= m),
//      and the same for |A| + (number of components).
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int N, n;
static uint64_t FULL, M0[6];

static inline uint64_t nb(uint64_t t) {
    uint64_t r = t;
    for (int i = 0; i < N; i++) r |= ((t & M0[i]) << (1 << i)) | ((t >> (1 << i)) & M0[i]);
    return r;
}

typedef struct {
    uint64_t lo, hi;
    int minN[33];
    uint64_t histP[33], histG[33], histHalf[33];
    int two;
    int fS;
    uint64_t fScount;
    int xi[33], xip[33];
} job_t;

static void *run(void *arg) {
    job_t *J = (job_t *)arg;
    for (int i = 0; i <= 32; i++) { J->minN[i] = 99; J->xi[i] = 0; J->xip[i] = 0; }
    memset(J->histP, 0, sizeof J->histP);
    memset(J->histG, 0, sizeof J->histG);
    memset(J->histHalf, 0, sizeof J->histHalf);
    J->two = 99; J->fS = 99; J->fScount = 0;
    for (uint64_t t = J->lo; t < J->hi; t++) {
        if (!t) continue;
        int c = __builtin_popcountll(t);
        uint64_t cl = nb(t);
        int d = __builtin_popcountll(cl);
        if (d < J->minN[c]) J->minN[c] = d;
        int b = d - c;
        if (cl == FULL) J->histP[b]++; else J->histG[b]++;
        if (2 * d <= n) J->histHalf[b]++;
        if (t != FULL) {
            uint64_t comp = FULL & ~t;
            int inner = c - (n - __builtin_popcountll(nb(comp)));
            if (inner + b < J->two) J->two = inner + b;
        }
        // (4) literal separator, B' = t
        if (c <= n / 2 + 1) {
            uint64_t rem = FULL & ~t;
            int mx = 0;
            while (rem) {
                uint64_t s = rem & (~rem + 1), s2;
                for (;;) { s2 = nb(s) & rem; if (s2 == s) break; s = s2; }
                int sz = __builtin_popcountll(s);
                if (sz > mx) mx = sz;
                rem &= ~s;
                if (c + mx > J->fS) break;
            }
            if (c + mx < J->fS) { J->fS = c + mx; J->fScount = 1; }
            else if (c + mx == J->fS && !rem) J->fScount++;
        }
        // (5) interior problem, A = t
        {
            uint64_t rem = t;
            int mx = 0, p = 0;
            while (rem) {
                uint64_t s = rem & (~rem + 1), s2;
                for (;;) { s2 = nb(nb(s)) & rem; if (s2 == s) break; s = s2; }
                int sz = __builtin_popcountll(nb(s));
                if (sz > mx) mx = sz;
                p++;
                rem &= ~s;
            }
            if (c > J->xi[mx]) J->xi[mx] = c;
            if (c + p > J->xip[mx]) J->xip[mx] = c + p;
        }
    }
    return NULL;
}

int main(int argc, char **argv) {
    N = argc > 1 ? atoi(argv[1]) : 4;
    int T = argc > 2 ? atoi(argv[2]) : 4;
    n = 1 << N;
    FULL = n == 64 ? ~0ULL : ((1ULL << n) - 1);
    for (int i = 0; i < N; i++) {
        M0[i] = 0;
        for (int v = 0; v < n; v++) if (!((v >> i) & 1)) M0[i] |= 1ULL << v;
    }
    uint64_t total = 1ULL << n;
    pthread_t th[16];
    job_t jobs[16];
    for (int i = 0; i < T; i++) {
        jobs[i].lo = total / T * i;
        jobs[i].hi = i == T - 1 ? total : total / T * (i + 1);
        pthread_create(&th[i], NULL, run, &jobs[i]);
    }
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    job_t R = jobs[0];
    for (int i = 1; i < T; i++) {
        for (int k = 0; k <= 32; k++) {
            if (jobs[i].minN[k] < R.minN[k]) R.minN[k] = jobs[i].minN[k];
            R.histP[k] += jobs[i].histP[k]; R.histG[k] += jobs[i].histG[k]; R.histHalf[k] += jobs[i].histHalf[k];
            if (jobs[i].xi[k] > R.xi[k]) R.xi[k] = jobs[i].xi[k];
            if (jobs[i].xip[k] > R.xip[k]) R.xip[k] = jobs[i].xip[k];
        }
        if (jobs[i].two < R.two) R.two = jobs[i].two;
        if (jobs[i].fS < R.fS) { R.fS = jobs[i].fS; R.fScount = jobs[i].fScount; }
        else if (jobs[i].fS == R.fS) R.fScount += jobs[i].fScount;
    }
    printf("N=%d n=%d\n(1) min |N[T]| by |T|=1..n:", N, n);
    for (int k = 1; k <= n; k++) printf(" %d", R.minN[k]);
    printf("\n(2) sets by boundary b: b, #(N[T]=V), #(N[T]!=V), #(|N[T]|<=n/2)\n");
    for (int k = 0; k <= n; k++) if (R.histP[k] || R.histG[k]) printf("   b=%d: %llu %llu %llu\n", k, (unsigned long long)R.histP[k], (unsigned long long)R.histG[k], (unsigned long long)R.histHalf[k]);
    printf("(3) min two-sided boundary over proper nonempty T: %d\n", R.two);
    printf("(4) literal separator: min |B'| + maxcomp = %d (number of optimal B' with |B'| <= n/2+1: %llu)\n", R.fS, (unsigned long long)R.fScount);
    printf("(5) Xi(m) for m=1..n (max total interior, fibres of size <= m):");
    int best = 0, bestp = 0;
    for (int k = 1; k <= n; k++) { if (R.xi[k] > best) best = R.xi[k]; printf(" %d", best); }
    printf("\n    same with +1 per cluster:");
    for (int k = 1; k <= n; k++) { if (R.xip[k] > bestp) bestp = R.xip[k]; printf(" %d", bestp); }
    printf("\n");
    return 0;
}
