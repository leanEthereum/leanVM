// Note 61: one-thread kernel timings, window mixing against an additive-NTT-shaped transform, on one buffer.
//
// The buffer is 2^LOGN rows of LANES words of K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), row-major, as the level-0
// codeword of leanVM (a row is a Merkle leaf). Three kernels:
//
//   ntt     LOGN - RATE layers of butterflies u' = u + v t, v' = v + u' (one K product a pair), depth first: a block
//           larger than the cache takes its top layer in one pass and recurses into its halves. The twiddles are dummy
//           constants: only the work and the memory pattern matter. This is the shape of crates/stable_prover/pcs/src/ntt.rs
//           with one layer a pass where the real code takes three.
//   mix     out[x] = w[x] + sum_{j in J} mu(x, j) w[x ^ 2^j], J a set of R directions, rows in order, products
//           accumulated unreduced and reduced once a word; the result is folded into a checksum (in the prover it would
//           go to the leaf hasher). mu comes from a xorshift generator: the Keccak cost of deriving it is not here.
//   copy    one pass that reads the buffer and folds it into a checksum (a floor for one pass over memory).
//
// With THREADS > 1 the rows (mix, copy) or the 2^RATE top blocks (ntt) are split among plain threads, so RATE must
// be at least log2(THREADS) for the ntt to use them all.
//
// Build: cc -O3 -mcpu=native -o 61_mix_bench 61_mix_bench.c     (arm64 with PMULL; see the #error below)
// Run:   ./61_mix_bench [LOGN=20] [LANES=40] [RATE=1] [THREADS=1]
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(__aarch64__)
#include <arm_neon.h>
typedef struct { uint64_t lo, hi; } u128;
static inline u128 clmul(uint64_t a, uint64_t b) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    u128 r = {(uint64_t)p, (uint64_t)(p >> 64)};
    return r;
}
#else
#error "this benchmark needs arm64 PMULL (it was written for the swarm's Apple machine)"
#endif

static inline uint64_t reduce(u128 p) {
    u128 t = clmul(p.hi, 0x1B);
    u128 s = clmul(t.hi, 0x1B);
    return p.lo ^ t.lo ^ s.lo;
}
static inline uint64_t kmul(uint64_t a, uint64_t b) { return reduce(clmul(a, b)); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static _Thread_local uint64_t rng_state = 0x9E3779B97F4A7C15ull;
static inline uint64_t rng(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rng_state = x;
}

static size_t LANES;
#define CACHE_ROWS_BYTES (1u << 17) // a block of this many bytes is transformed in cache

static void layer(uint64_t *top, uint64_t *bot, size_t words, uint64_t t) {
    for (size_t i = 0; i < words; i++) {
        uint64_t u = top[i] ^ kmul(bot[i], t);
        top[i] = u;
        bot[i] ^= u;
    }
}

// Depth-first transform of `rows` rows from layer `depth` on; one twiddle a block, as in the additive NTT.
static void ntt(uint64_t *w, size_t rows, uint64_t tw) {
    if (rows == 1) return;
    size_t half = rows / 2;
    layer(w, w + half * LANES, half * LANES, tw);
    ntt(w, half, tw * 0x9E3779B97F4A7C15ull + 1);
    ntt(w + half * LANES, half, tw * 0xC2B2AE3D27D4EB4Full + 3);
}

static uint64_t mix_rows(const uint64_t *w, size_t from, size_t to, const int *dirs, int ndirs) {
    uint64_t sum = 0;
    uint64_t mu[64];
    u128 *acc = malloc(LANES * sizeof(u128));
    rng_state = 0x9E3779B97F4A7C15ull + from;
    for (size_t x = from; x < to; x++) {
        for (int k = 0; k < ndirs; k++) mu[k] = rng();
        const uint64_t *row = w + x * LANES;
        for (size_t l = 0; l < LANES; l++) { acc[l].lo = row[l]; acc[l].hi = 0; }
        for (int k = 0; k < ndirs; k++) {
            const uint64_t *p = w + (x ^ ((size_t)1 << dirs[k])) * LANES;
            uint64_t m = mu[k];
            for (size_t l = 0; l < LANES; l++) {
                u128 pr = clmul(m, p[l]);
                acc[l].lo ^= pr.lo;
                acc[l].hi ^= pr.hi;
            }
        }
        for (size_t l = 0; l < LANES; l++) sum ^= reduce(acc[l]) + l;
    }
    free(acc);
    return sum;
}

// The same sum, a block of BLOCK rows at a time and the partners in groups of GROUP: the accumulators of the block
// stay in cache between the groups, and no pass follows more than GROUP + 1 streams.
#define BLOCK 64
static int GROUP = 8;
static uint64_t mix_rows_grouped(const uint64_t *w, size_t from, size_t to, const int *dirs, int ndirs) {
    uint64_t sum = 0;
    u128 *acc = malloc(BLOCK * LANES * sizeof(u128));
    rng_state = 0x9E3779B97F4A7C15ull + from;
    for (size_t x0 = from; x0 < to; x0 += BLOCK) {
        size_t rows = to - x0 < BLOCK ? to - x0 : BLOCK;
        for (size_t i = 0; i < rows * LANES; i++) { acc[i].lo = w[x0 * LANES + i]; acc[i].hi = 0; }
        for (int g = 0; g < ndirs; g += GROUP) {
            int ge = g + GROUP < ndirs ? g + GROUP : ndirs;
            for (size_t i = 0; i < rows; i++) {
                u128 *a = acc + i * LANES;
                for (int k = g; k < ge; k++) {
                    const uint64_t *p = w + ((x0 + i) ^ ((size_t)1 << dirs[k])) * LANES;
                    uint64_t m = rng();
                    for (size_t l = 0; l < LANES; l++) {
                        u128 pr = clmul(m, p[l]);
                        a[l].lo ^= pr.lo;
                        a[l].hi ^= pr.hi;
                    }
                }
            }
        }
        for (size_t i = 0; i < rows * LANES; i++) sum ^= reduce(acc[i]) + i;
    }
    free(acc);
    return sum;
}

static uint64_t copy(const uint64_t *w, size_t words) {
    uint64_t sum = 0;
    for (size_t i = 0; i < words; i++) sum ^= w[i] + i;
    return sum;
}

static int THREADS = 1;
typedef struct { int kind; uint64_t *w; size_t from, to, blk; const int *dirs; int ndirs; uint64_t out; } job;
static void *run(void *arg) {
    job *j = arg;
    if (j->kind == 0) j->out = copy(j->w + j->from * LANES, (j->to - j->from) * LANES);
    if (j->kind == 1) for (size_t b = j->from; b < j->to; b++) ntt(j->w + b * j->blk * LANES, j->blk, 0x1234567 + b);
    if (j->kind == 2) j->out = mix_rows(j->w, j->from, j->to, j->dirs, j->ndirs);
    if (j->kind == 3) j->out = mix_rows_grouped(j->w, j->from, j->to, j->dirs, j->ndirs);
    return 0;
}
// Splits `count` items (rows, or top blocks of `blk` rows) among the threads.
static uint64_t par(int kind, uint64_t *w, size_t count, size_t blk, const int *dirs, int ndirs) {
    pthread_t th[64];
    job jobs[64];
    uint64_t out = 0;
    for (int t = 0; t < THREADS; t++) {
        jobs[t] = (job){kind, w, count * t / THREADS, count * (t + 1) / THREADS, blk, dirs, ndirs, 0};
        pthread_create(&th[t], 0, run, &jobs[t]);
    }
    for (int t = 0; t < THREADS; t++) { pthread_join(th[t], 0); out ^= jobs[t].out; }
    return out;
}
static uint64_t mix(uint64_t *w, int logn, const int *dirs, int ndirs) {
    return par(2, w, (size_t)1 << logn, 0, dirs, ndirs);
}

int main(int argc, char **argv) {
    int logn = argc > 1 ? atoi(argv[1]) : 20;
    LANES = argc > 2 ? (size_t)atoi(argv[2]) : 40;
    int rate = argc > 3 ? atoi(argv[3]) : 1;
    THREADS = argc > 4 ? atoi(argv[4]) : 1;
    if (THREADS < 1 || THREADS > 64) return 1;
    size_t n = (size_t)1 << logn, words = n * LANES;
    uint64_t *w = malloc(words * 8);
    if (!w) return 1;
    for (size_t i = 0; i < words; i++) w[i] = rng();
    printf("rows 2^%d, lanes %zu, %.0f MiB, %d thread(s)\n", logn, LANES, words * 8 / 1048576.0, THREADS);

    double best_copy = 1e9, best_ntt = 1e9;
    uint64_t chk = 0;
    for (int rep = 0; rep < 3; rep++) {
        double t0 = now();
        chk ^= par(0, w, n, 0, 0, 0);
        double t1 = now();
        if (t1 - t0 < best_copy) best_copy = t1 - t0;
    }
    printf("copy (one read pass)            %8.1f ms\n", 1e3 * best_copy);
    // The encoder's first `rate` layers are copies of the message, so it runs logn - rate layers: here the transform
    // of each of the 2^rate top blocks.
    for (int rep = 0; rep < 2; rep++) {
        double t0 = now();
        par(1, w, (size_t)1 << rate, n >> rate, 0, 0);
        double t1 = now();
        if (t1 - t0 < best_ntt) best_ntt = t1 - t0;
    }
    printf("ntt (%2d layers, depth first)    %8.1f ms   %.2f ns a word and layer\n", logn - rate, 1e3 * best_ntt,
           1e9 * best_ntt / ((double)words * (logn - rate) / 2) / 2);

    int all[64];
    int configs[4] = {logn, 16, 9, 4};
    for (int c = 0; c < 4; c++) {
        int nd = configs[c] < logn ? configs[c] : logn;
        // nd directions spread over the cube, the highest always included: the far partners are the costly ones.
        for (int k = 0; k < nd; k++) all[k] = (int)((long)k * (logn - 1) / (nd > 1 ? nd - 1 : 1));
        double best = 1e9;
        for (int rep = 0; rep < 2; rep++) {
            double t0 = now();
            chk ^= mix(w, logn, all, nd);
            double t1 = now();
            if (t1 - t0 < best) best = t1 - t0;
        }
        printf("mix r = %2d (%2d partners)        %8.1f ms   %.2f x ntt   %.2f ns a word and partner\n", nd + 1, nd,
               1e3 * best, best / best_ntt, 1e9 * best / ((double)words * nd));
    }
    // All directions again, in groups of at most GROUP streams.
    for (int k = 0; k < logn; k++) all[k] = k;
    for (GROUP = 5; GROUP <= 10; GROUP += 5) {
        double best = 1e9;
        for (int rep = 0; rep < 3; rep++) {
            double t0 = now();
            chk ^= par(3, w, n, 0, all, logn);
            double t1 = now();
            if (t1 - t0 < best) best = t1 - t0;
        }
        printf("mix r = %2d, groups of %2d         %8.1f ms   %.2f x ntt\n", logn + 1, GROUP, 1e3 * best, best / best_ntt);
    }
    // Low directions only (partners inside a 2^9-row block): the cost without the far partners.
    for (int k = 0; k < 9; k++) all[k] = k;
    double t0 = now();
    chk ^= mix(w, logn, all, 9);
    double t1 = now();
    printf("mix, 9 partners, all in a block %8.1f ms   %.2f x ntt\n", 1e3 * (t1 - t0), (t1 - t0) / best_ntt);
    printf("checksum %016llx\n", (unsigned long long)chk);
    free(w);
    return 0;
}
