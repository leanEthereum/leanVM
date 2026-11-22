// Referee 87: rebuild a list of the T2 tree code [n, n/2] over GF(2^64) from a class pattern, by encoding.
// usage: 87_lists V M SEED tok_0 ... tok_{n-1}
//   k = 2^V, n = 2k, M members named 0-9a-z; a token is the class of members agreeing with the word at that leaf,
//   "." = no member, "*" = all members. Fresh twiddles from SEED (own generator), own field arithmetic.
// Steps: incidence system (e_a - e_first) (x) g_x for every class; kernel; messages (member 0 = random common message);
// top-down folding encoder; the word is read off the classes; agreements are counted on the encoded codewords.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#if defined(__aarch64__)
#include <arm_neon.h>
#endif
typedef uint64_t u64;
static u64 gmul_ref(u64 a, u64 b) { u64 r = 0; while (b) { if (b & 1) r ^= a; b >>= 1; a = (a << 1) ^ ((a >> 63) ? 0x1BULL : 0); } return r; }
static inline u64 gmul(u64 a, u64 b) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_AES)
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b); u64 lo = (u64)p, hi = (u64)(p >> 64);
    poly128_t q = vmull_p64((poly64_t)hi, (poly64_t)0x1B); lo ^= (u64)q; u64 qh = (u64)(q >> 64);
    poly128_t s = vmull_p64((poly64_t)qh, (poly64_t)0x1B); return lo ^ (u64)s;
#else
    return gmul_ref(a, b);
#endif
}
static u64 ginv(u64 a) { u64 r = 1, s = a; for (int i = 1; i < 64; i++) { s = gmul(s, s); r = gmul(r, s); } return r; }
static u64 rs;
static u64 rnd(void) { u64 z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static int midx(char c) { return (c >= '0' && c <= '9') ? c - '0' : (c >= 'a' && c <= 'z') ? c - 'a' + 10 : -1; }

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    int V = atoi(argv[1]), M = atoi(argv[2]); rs = strtoull(argv[3], 0, 10); int k = 1 << V, n = 2 * k, L = M - 1, D = L * k;
    if (argc != 4 + n) { printf("need %d tokens, got %d\n", n, argc - 4); return 1; }
    for (int i = 0; i < 1000; i++) { u64 a = rnd(), b = rnd(); if (gmul(a, b) != gmul_ref(a, b) || (a && gmul(a, ginv(a)) != 1)) { printf("field self test failed\n"); return 1; } }
    // tree: g[x] in K^k for the leaves, twiddles tw[j][node]
    u64 **tw = malloc(sizeof(u64 *) * (V + 1)); u64 *g = calloc((size_t)n * k, sizeof(u64)), *gp = calloc((size_t)n * k, sizeof(u64));
    gp[0] = 1; gp[k] = 1; // two roots, row (1)
    for (int j = 1; j <= V; j++) { int nodes = 2 << j, kh = 1 << (j - 1); tw[j] = malloc(sizeof(u64) * nodes);
        for (int p = 0; p < nodes / 2; p++) { u64 t0, t1; do { t0 = rnd(); t1 = rnd(); } while (t0 == t1);
            for (int b = 0; b < 2; b++) { u64 t = b ? t1 : t0; tw[j][2 * p + b] = t; for (int c = 0; c < kh; c++) { g[(size_t)(2 * p + b) * k + c] = gp[(size_t)p * k + c]; g[(size_t)(2 * p + b) * k + kh + c] = gmul(t, gp[(size_t)p * k + c]); } } }
        memcpy(gp, g, sizeof(u64) * (size_t)n * k); }
    // classes
    unsigned long long *cls = calloc(n, sizeof *cls); int w = 0;
    for (int x = 0; x < n; x++) { const char *t = argv[4 + x]; if (!strcmp(t, "*")) cls[x] = (1ULL << M) - 1; else if (strcmp(t, ".")) for (const char *p = t; *p; p++) { int a = midx(*p); if (a < 0 || a >= M) { printf("bad token %s\n", t); return 1; } cls[x] |= 1ULL << a; }
        int c = __builtin_popcountll(cls[x]); if (c >= 2) w += c - 1; }
    // echelon of the incidence rows
    u64 **row = malloc(sizeof(u64 *) * (D + 1)); int *piv = malloc(sizeof(int) * (D + 1)); int rank = 0; u64 *v = malloc(sizeof(u64) * D);
    for (int x = 0; x < n; x++) { if (__builtin_popcountll(cls[x]) < 2) continue; int first = __builtin_ctzll(cls[x]);
        for (int a = first + 1; a < M; a++) if ((cls[x] >> a) & 1) {
            memset(v, 0, sizeof(u64) * D); memcpy(v + (size_t)(a - 1) * k, g + (size_t)x * k, sizeof(u64) * k); if (first > 0) memcpy(v + (size_t)(first - 1) * k, g + (size_t)x * k, sizeof(u64) * k);
            for (int b = 0; b < rank; b++) { u64 c = v[piv[b]]; if (c) for (int i = 0; i < D; i++) v[i] ^= gmul(c, row[b][i]); }
            int p = -1; for (int i = 0; i < D; i++) if (v[i]) { p = i; break; }
            if (p < 0) continue;
            u64 iv = ginv(v[p]); row[rank] = malloc(sizeof(u64) * D); for (int i = 0; i < D; i++) row[rank][i] = gmul(iv, v[i]); piv[rank++] = p; } }
    printf("n = %d, k = %d, members %d: weight %d, Lk = %d, rank %d, kernel dimension %d\n", n, k, M, w, D, rank, D - rank);
    if (rank == D) { printf("no solution\n"); return 0; }
    // reduce fully, then a random kernel vector
    for (int b = rank - 1; b >= 0; b--) for (int b2 = 0; b2 < b; b2++) { u64 c = row[b2][piv[b]]; if (c) for (int i = 0; i < D; i++) row[b2][i] ^= gmul(c, row[b][i]); }
    char *isp = calloc(D, 1); for (int b = 0; b < rank; b++) isp[piv[b]] = 1;
    u64 *sol = calloc(D, sizeof(u64)); for (int f = 0; f < D; f++) if (!isp[f]) sol[f] = rnd();
    for (int b = 0; b < rank; b++) { u64 s = 0; for (int f = 0; f < D; f++) if (!isp[f]) s ^= gmul(row[b][f], sol[f]); sol[piv[b]] = s; }
    // messages and encoding (folding encoder, uses the twiddles only)
    u64 *msg = malloc(sizeof(u64) * (size_t)M * k), *cw = malloc(sizeof(u64) * (size_t)M * n), *cur = malloc(sizeof(u64) * (size_t)n * k), *nxt = malloc(sizeof(u64) * (size_t)n * k);
    for (int c = 0; c < k; c++) msg[c] = rnd();
    for (int a = 1; a < M; a++) for (int c = 0; c < k; c++) msg[(size_t)a * k + c] = msg[c] ^ sol[(size_t)(a - 1) * k + c];
    for (int a = 0; a < M; a++) {
        for (int p = 0; p < 2; p++) memcpy(cur + (size_t)p * k, msg + (size_t)a * k, sizeof(u64) * k);
        for (int j = 1; j <= V; j++) { int len = k >> j; for (int x = 0; x < (2 << j); x++) for (int i = 0; i < len; i++) nxt[(size_t)x * k + i] = cur[(size_t)(x >> 1) * k + 2 * i] ^ gmul(tw[j][x], cur[(size_t)(x >> 1) * k + 2 * i + 1]); memcpy(cur, nxt, sizeof(u64) * (size_t)n * k); }
        for (int x = 0; x < n; x++) cw[(size_t)a * n + x] = cur[(size_t)x * k]; }
    int distinct = 1; for (int a = 0; a < M; a++) for (int b = a + 1; b < M; b++) if (!memcmp(cw + (size_t)a * n, cw + (size_t)b * n, sizeof(u64) * n)) distinct = 0;
    int classes_ok = 1, *agree = calloc(M, sizeof(int));
    for (int x = 0; x < n; x++) { u64 y; if (!cls[x]) y = rnd(); else { int first = __builtin_ctzll(cls[x]); y = cw[(size_t)first * n + x]; for (int a = 0; a < M; a++) if (((cls[x] >> a) & 1) && cw[(size_t)a * n + x] != y) classes_ok = 0; }
        for (int a = 0; a < M; a++) if (cw[(size_t)a * n + x] == y) agree[a]++; }
    int target = 5 * n / 8, at = 0; printf("codewords distinct: %s; classes agree: %s; agreements with the word:", distinct ? "yes" : "NO", classes_ok ? "yes" : "NO");
    for (int a = 0; a < M; a++) { printf(" %d", agree[a]); if (agree[a] >= target) at++; }
    printf(" ; members at agreement >= 5n/8 = %d: %d\n", target, at);
    return 0;
}
