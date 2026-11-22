// Note 65: what the access pattern of d partners a row costs, against note 61's NTT-shaped transform on the same
// buffer (the helpers, the transform and the buffer shape are note 61's file, included unchanged).
//   mode 0  partners x ^ 2^j, d directions spread over the cube (note 61's strided kernel)
//   mode 1  d uniformly random rows a row, indices from a cheap hash, software prefetch a batch of 16 rows ahead
//   mode 2  product structure: d random far blocks of 2^LOGB rows a block (shared by the block), and inside each a
//           random row a position
// Build: cc -O3 -mcpu=native -o 65_mix_bench 65_mix_bench.c
// Run:   ./65_mix_bench [LOGN=20] [LANES=40] [THREADS=1] [D=8] [LOGB=8]
#define main main61
#include "61_mix_bench.c"
#undef main

static int D8 = 8, LOGB = 8, LOGNN = 20;
static inline uint64_t h64(uint64_t x) {
    x += 0x9E3779B97F4A7C15ull; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ull;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBull; return x ^ (x >> 31);
}
static inline size_t partner(int mode, size_t x, int k) {
    size_t n = (size_t)1 << LOGNN;
    if (mode == 0) return x ^ ((size_t)1 << (k * (LOGNN - 1) / (D8 - 1)));
    if (mode == 1) return h64(x * 64 + k) & (n - 1);
    size_t blk = h64((x >> LOGB) * 64 + k + 0x5555) & ((n >> LOGB) - 1);
    return (blk << LOGB) | (h64(x * 64 + k) & (((size_t)1 << LOGB) - 1));
}
#define BATCH 16
typedef struct { int mode; const uint64_t *w; size_t from, to; uint64_t out; } job65;
static void *run65(void *arg) {
    job65 *j = arg;
    uint64_t sum = 0;
    size_t idx[BATCH * 32];
    u128 *acc = malloc(LANES * sizeof(u128));
    for (size_t x0 = j->from; x0 < j->to; x0 += BATCH) {
        for (size_t i = 0; i < BATCH; i++)
            for (int k = 0; k < D8; k++) {
                size_t p = idx[i * D8 + k] = partner(j->mode, x0 + i, k);
                for (size_t l = 0; l < LANES; l += 8) __builtin_prefetch(j->w + p * LANES + l);
            }
        for (size_t i = 0; i < BATCH; i++) {
            const uint64_t *row = j->w + (x0 + i) * LANES;
            for (size_t l = 0; l < LANES; l++) { acc[l].lo = row[l]; acc[l].hi = 0; }
            for (int k = 0; k < D8; k++) {
                const uint64_t *p = j->w + idx[i * D8 + k] * LANES;
                uint64_t m = h64(idx[i * D8 + k] + x0 + i) | 1;
                for (size_t l = 0; l < LANES; l++) {
                    u128 pr = clmul(m, p[l]);
                    acc[l].lo ^= pr.lo; acc[l].hi ^= pr.hi;
                }
            }
            for (size_t l = 0; l < LANES; l++) sum ^= reduce(acc[l]) + l;
        }
    }
    free(acc);
    j->out = sum;
    return 0;
}
static double time65(int mode, const uint64_t *w, size_t n, uint64_t *chk) {
    double best = 1e9;
    for (int rep = 0; rep < 3; rep++) {
        pthread_t th[64]; job65 jobs[64];
        double t0 = now();
        for (int t = 0; t < THREADS; t++) {
            jobs[t] = (job65){mode, w, n * t / THREADS, n * (t + 1) / THREADS, 0};
            pthread_create(&th[t], 0, run65, &jobs[t]);
        }
        for (int t = 0; t < THREADS; t++) { pthread_join(th[t], 0); *chk ^= jobs[t].out; }
        double t1 = now();
        if (t1 - t0 < best) best = t1 - t0;
    }
    return best;
}
int main(int argc, char **argv) {
    LOGNN = argc > 1 ? atoi(argv[1]) : 20;
    LANES = argc > 2 ? (size_t)atoi(argv[2]) : 40;
    THREADS = argc > 3 ? atoi(argv[3]) : 1;
    D8 = argc > 4 ? atoi(argv[4]) : 8;
    LOGB = argc > 5 ? atoi(argv[5]) : 8;
    int rate = THREADS > 1 ? 2 : 1;
    size_t n = (size_t)1 << LOGNN, words = n * LANES;
    uint64_t *w = malloc(words * 8), chk = 0;
    for (size_t i = 0; i < words; i++) w[i] = rng();
    double tn = 1e9;
    for (int rep = 0; rep < 2; rep++) {
        double t0 = now();
        par(1, w, (size_t)1 << rate, n >> rate, 0, 0);
        if (now() - t0 < tn) tn = now() - t0;
    }
    printf("rows 2^%d, lanes %zu, %d thread(s), d = %d, far blocks of 2^%d rows\n", LOGNN, LANES, THREADS, D8, LOGB);
    printf("ntt (%d layers)                %8.1f ms\n", LOGNN - rate, 1e3 * tn);
    const char *names[3] = {"strided x ^ 2^j        ", "uniformly random rows  ", "far blocks + local rows"};
    for (int mode = 0; mode < 3; mode++) {
        double t = time65(mode, w, n, &chk);
        printf("mix, %s  %8.1f ms   %.2f x ntt   %.3f x ntt a partner\n", names[mode], 1e3 * t, t / tn, t / tn / D8);
    }
    printf("checksum %016llx\n", (unsigned long long)chk);
    return 0;
}
