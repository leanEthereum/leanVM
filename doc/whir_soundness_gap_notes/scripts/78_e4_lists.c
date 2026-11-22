// Note 78, experiment 4: the lifted lists of notes 69 and 74, as lists of MESSAGES built on a T2 tree code, encoded by
// each variant ON THE SAME TWIDDLES (every spec is built after reseeding, so its tree is the T2 tree), and the best common word.
// usage: 78_e4_lists pat   v r seed patternfile spec...   one list per pattern line (kernel point of the T2 incidence system)
//        78_e4_lists stair v r lo f want seed spec...      one-sided staircase of note 74 (zeros of B in block 0, f free blocks)
//        78_e4_lists bal   v r lo want seed spec...        balanced staircase of note 69 (zeros of B spread)
// Small lists (<= 12 members): exact weight of every sub-list (the word is free: weight = sum over leaves of largest class - 1),
// balanced agreement by greedy + local search (lower bound) and floor((n + W)/members) (upper bound).
// Large lists: per member r = number of leaves where it shares its symbol with another member. Adding a member to a sub-list T
// changes E(T) = W_T - ((|T|-1)k - 1) by at most r - k, and E of one member is 1. So if at most one member has r >= k (put it
// first), every sub-list of two or more has E <= 0: none is beyond the generalized Singleton weight, for any word (certificate). Otherwise a greedy search for a sub-list beyond it.
#include "69_pat.h"
#include "78_var.h"
static int v, r, n, k;
static long gsval(long M) { return (n + (M - 1) * (long)k - 1) / M; } // largest minimum agreement the generalized Singleton bound allows
typedef struct { fe val; int l; } vl_t;
static int cmp_vl(const void *a, const void *b) { const vl_t *x = a, *y = b; return x->val < y->val ? -1 : x->val > y->val ? 1 : x->l - y->l; }
// balanced agreement of the sub-list T (bitmask) given cid[x][l] (class representative), greedy + local search
static int balanced_small(const uint8_t *cid, int nm, uint32_t T) {
    int a[16] = {0}; uint32_t *ch = malloc(sizeof(uint32_t) * n), *masks = malloc(sizeof(uint32_t) * n * nm);
    for (int x = 0; x < n; x++) {
        for (int l = 0; l < nm; l++) masks[x * nm + l] = 0;
        for (int l = 0; l < nm; l++) if ((T >> l) & 1) masks[x * nm + cid[x * nm + l]] |= 1u << l;
        uint32_t best = 0; for (int l = 0; l < nm; l++) if (__builtin_popcount(masks[x * nm + l]) > __builtin_popcount(best)) best = masks[x * nm + l];
        if (__builtin_popcount(best) < 2) best = 0; // a free leaf
        ch[x] = best; for (int l = 0; l < nm; l++) a[l] += (best >> l) & 1;
    }
    for (int x = 0; x < n; x++) if (!ch[x]) { int b = -1; for (int l = 0; l < nm; l++) if (((T >> l) & 1) && (b < 0 || a[l] < a[b])) b = l; ch[x] = 1u << b; a[b]++; }
    for (int it = 0; it < 20 * n; it++) {
        int lm = -1; for (int l = 0; l < nm; l++) if (((T >> l) & 1) && (lm < 0 || a[l] < a[lm])) lm = l;
        int moved = 0;
        for (int x = 0; x < n && !moved; x++) {
            if ((ch[x] >> lm) & 1) continue;
            uint32_t nw = masks[x * nm + cid[x * nm + lm]], lose = ch[x] & ~nw; int ok = 1;
            for (int l = 0; l < nm; l++) if (((lose >> l) & 1) && a[l] - 1 <= a[lm]) ok = 0;
            if (!ok) continue;
            for (int l = 0; l < nm; l++) { a[l] -= (ch[x] >> l) & 1; a[l] += (nw >> l) & 1; }
            ch[x] = nw; moved = 1;
        }
        if (!moved) break;
    }
    int mn = n; for (int l = 0; l < nm; l++) if (((T >> l) & 1) && a[l] < mn) mn = a[l];
    free(ch); free(masks); return mn;
}
static void analyze(const char *spec, const var_t *V, const fe *Msg, long nm, const char *tag) {
    fe *CW = malloc(sizeof(fe) * (size_t)nm * n);
    for (long l = 0; l < nm; l++) var_encode(V, Msg + (size_t)l * k, CW + (size_t)l * n);
    long same = 0; for (long l = 1; l < nm && l < 200; l++) same += !memcmp(CW, CW + (size_t)l * n, sizeof(fe) * n);
    if (nm <= 12) {
        uint8_t *cid = malloc((size_t)n * nm);
        for (int x = 0; x < n; x++) for (int l = 0; l < nm; l++) { int c = l; for (int l2 = 0; l2 < l; l2++) if (CW[(size_t)l2 * n + x] == CW[(size_t)l * n + x]) { c = l2; break; } cid[x * nm + l] = (uint8_t)c; }
        long Wfull = 0; int bestsz = 0; long bestexc[16]; uint32_t bestT[16]; for (int i = 0; i < 16; i++) { bestexc[i] = -1000000; bestT[i] = 0; }
        for (uint32_t T = 1; T < (1u << nm); T++) {
            int sz = __builtin_popcount(T); if (sz < 2) continue;
            long W = 0;
            for (int x = 0; x < n; x++) { int cnt[16] = {0}, mx = 0; for (int l = 0; l < nm; l++) if ((T >> l) & 1) { int c = ++cnt[cid[x * nm + l]]; if (c > mx) mx = c; } W += mx - 1; }
            if (T == (1u << nm) - 1) Wfull = W;
            long exc = W - ((long)(sz - 1) * k - 1);
            if (exc > bestexc[sz]) { bestexc[sz] = exc; bestT[sz] = T; }
            if (exc > 0 && sz > bestsz && sz >= 3) bestsz = sz;
        }
        uint32_t full = (1u << nm) - 1; int lb = balanced_small(cid, (int)nm, full); long ub = (n + Wfull) / nm;
        printf("%s | %-12s members %ld: weight %ld (gS bound %ld), balanced agreement %d..%ld (gS value %ld)", tag, spec, nm, Wfull, (nm - 1) * (long)k - 1, lb, ub, gsval(nm));
        printf(" | largest sub-list beyond the gS weight: %d", bestsz);
        printf(" | excess of the best sub-list by size:"); for (int s = 2; s <= nm; s++) printf(" %d:%+ld", s, bestexc[s]);
        int bsz = 0, bag = 0; for (int s = 3; s <= nm; s++) { int ag = balanced_small(cid, (int)nm, bestT[s]); if (ag > gsval(s)) { bsz = s; bag = ag; } }
        if (bsz) printf(" | largest sub-list with balanced agreement above its gS value: %d members at %d (gS value %ld)", bsz, bag, gsval(bsz)); else printf(" | no sub-list of 3+ members with balanced agreement above its gS value");
        printf("\n"); free(cid);
    } else {
        int *rs = calloc(nm, sizeof(int)), *rp = calloc(nm, sizeof(int)); vl_t *col = malloc(sizeof(vl_t) * nm);
        uint8_t *inpl = calloc((size_t)nm * n, 1); long second = 0, Wfull = 0;
        for (int x = 0; x < n; x++) {
            for (long l = 0; l < nm; l++) { col[l].val = CW[(size_t)l * n + x]; col[l].l = (int)l; }
            qsort(col, nm, sizeof(vl_t), cmp_vl);
            long bs = 0, be = 0, nontriv = 0;
            for (long i = 0; i < nm;) { long j = i; while (j < nm && col[j].val == col[i].val) j++; if (j - i >= 2) { nontriv++; for (long t = i; t < j; t++) rp[col[t].l]++; } if (j - i > be - bs) { bs = i; be = j; } i = j; }
            if (be - bs >= 2) { for (long t = bs; t < be; t++) { rs[col[t].l]++; inpl[(size_t)col[t].l * n + x] = 1; } Wfull += be - bs - 1; }
            second += (nontriv >= 2);
        }
        int rmax = 0, rmin = n, rpmax = 0; for (long l = 0; l < nm; l++) { if (rs[l] > rmax) rmax = rs[l]; if (rs[l] < rmin) rmin = rs[l]; if (rp[l] > rpmax) rpmax = rp[l]; }
        printf("%s | %-12s members %ld (equal codewords among the first 200: %ld): weight of the plurality word %ld (gS bound %ld); shared agreements per member min %d max %d (in any class: max %d); leaves with two classes of 2+: %ld",
               tag, spec, nm, same, Wfull, (nm - 1) * (long)k - 1, rmin, rmax, rpmax, second);
        long Efull = Wfull - ((nm - 1) * (long)k - 1);
        long nbig = 0; for (long l = 0; l < nm; l++) nbig += (rp[l] >= k);
        if (nbig <= 1) printf(" | CERTIFIED: no sub-list is beyond the gS weight for any word (members sharing k = %d symbols or more: %ld; max %d)\n", k, nbig, rpmax);
        else { // greedy: grow T from the member with the largest r by the member that shares most leaves with T; E(T) = W_T - ((|T|-1)k - 1)
            int *cntx = calloc(n, sizeof(int)); uint8_t *inT = calloc(nm, 1); long best = 0; for (long l = 1; l < nm; l++) if (rs[l] > rs[best]) best = l;
            long E = 1, sz = 1, bestM = 0, bestag = 0, bestE = 0; inT[best] = 1; for (int x = 0; x < n; x++) cntx[x] += inpl[(size_t)best * n + x];
            long steps = nm - 1 < 400 ? nm - 1 : 400;
            for (long st = 0; st < steps; st++) {
                long bl = -1, bg = -1;
                for (long l = 0; l < nm; l++) if (!inT[l]) { long g = 0; const uint8_t *row = inpl + (size_t)l * n; for (int x = 0; x < n; x++) g += row[x] && cntx[x]; if (g > bg) { bg = g; bl = l; } }
                inT[bl] = 1; sz++; E += bg - k; for (int x = 0; x < n; x++) cntx[x] += inpl[(size_t)bl * n + x];
                if (E > 0 && sz >= 3) { // balanced agreement of T: shared leaves to their class, the others water-filled
                    long freel = 0, lo2 = 0, hi2 = n; int *aT = malloc(sizeof(int) * sz); long t = 0;
                    for (int x = 0; x < n; x++) freel += (cntx[x] <= 1);
                    for (long l = 0; l < nm; l++) if (inT[l]) { int a = 0; for (int x = 0; x < n; x++) a += inpl[(size_t)l * n + x] && cntx[x] >= 2; aT[t++] = a; }
                    while (lo2 < hi2) { long mid = (lo2 + hi2 + 1) / 2, need = 0; for (long i = 0; i < sz; i++) if (aT[i] < mid) need += mid - aT[i]; if (need <= freel) lo2 = mid; else hi2 = mid - 1; }
                    free(aT);
                    if (lo2 > gsval(sz)) { bestM = sz; bestag = lo2; bestE = E; }
                }
            }
            if (bestM) printf(" | SURVIVES: %ld members at balanced agreement %ld = %.4f n (gS value %ld), weight excess %ld; full list excess %ld\n", bestM, bestag, (double)bestag / n, gsval(bestM), bestE, Efull);
            else printf(" | no surviving sub-list found by the greedy search (%ld steps; full list excess %ld; not certified)\n", steps, Efull);
            free(cntx); free(inT);
        }
        free(rs); free(rp); free(col); free(inpl);
    }
    free(CW);
}
static int parse_pattern(const char *line, uint8_t *cls, int *Lout) {
    const char *p = strstr(line, " | "); p = p ? p + 3 : line; int x = 0, mx = 0;
    while (*p && x < n) { while (*p == ' ') p++; if (!*p || *p == '\n') break; uint8_t c = 0;
        while (*p && *p != ' ' && *p != '\n') { if (*p >= '0' && *p <= '9') { c |= (uint8_t)(1 << (*p - '0')); if (*p - '0' > mx) mx = *p - '0'; } p++; } cls[x++] = c; }
    *Lout = mx; return x == n;
}
int main(int argc, char **argv) {
    const char *mode = argv[1]; v = atoi(argv[2]); r = atoi(argv[3]); n = 1 << (v + r); k = 1 << v; gf_init();
    int a0; uint64_t seed; int lo = 0, f = 0; long want = 0; const char *pfile = 0;
    if (!strcmp(mode, "pat")) { seed = strtoull(argv[4], 0, 10); pfile = argv[5]; a0 = 6; }
    else if (!strcmp(mode, "stair")) { lo = atoi(argv[4]); f = atoi(argv[5]); want = atol(argv[6]); seed = strtoull(argv[7], 0, 10); a0 = 8; }
    else { lo = atoi(argv[4]); want = atol(argv[5]); seed = strtoull(argv[6], 0, 10); a0 = 7; }
    int ns = argc - a0; var_t T2, *V = malloc(sizeof(var_t) * ns);
    rng_seed(seed); var_make(&T2, "T2", v, r);
    for (int s = 0; s < ns; s++) { rng_seed(seed); if (!var_make(&V[s], argv[a0 + s], v, r)) { printf("bad spec %s\n", argv[a0 + s]); return 1; } }
    rng_seed(seed + 100003);
    char tag[256];
    if (pfile) {
        FILE *fp = fopen(pfile, "r"); char *line = malloc(1 << 16); uint8_t cls[MAXN]; int L, idx = 0;
        while (fgets(line, 1 << 16, fp)) {
            if (!parse_pattern(line, cls, &L)) continue;
            int cols = L * k, rows = 0; fe *M = malloc(sizeof(fe) * (size_t)(L * n + 1) * cols), *K = malloc(sizeof(fe) * (size_t)cols * cols);
            for (int x = 0; x < n; x++) if (cls[x]) { int l0 = __builtin_ctz(cls[x]); for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
                fe *row = M + (size_t)rows * cols; memset(row, 0, sizeof(fe) * cols);
                memcpy(row + (l - 1) * k, T2.G + (size_t)x * k, sizeof(fe) * k); if (l0 >= 1) memcpy(row + (l0 - 1) * k, T2.G + (size_t)x * k, sizeof(fe) * k); rows++; } }
            int dim = gf_kernel(M, rows, cols, K);
            fe *Msg = calloc((size_t)(L + 1) * k, sizeof(fe));
            for (int b = 0; b < dim; b++) { fe s = gf_rand(); for (int j = 0; j < cols; j++) Msg[k + j] ^= gf_mul(s, K[(size_t)b * cols + j]); }
            sprintf(tag, "pattern %d (k=%d n=%d, T2 pattern weight %d, T2 balanced %d, kernel dim %d)", idx++, k, n, pat_weight(cls, n), pat_balanced(cls, n, L), dim);
            if (dim) for (int s = 0; s < ns; s++) analyze(argv[a0 + s], &V[s], Msg, L + 1, tag); else printf("%s: no list in T2\n", tag);
            free(M); free(K); free(Msg);
        }
        return 0;
    }
    int N = n >> lo, ku = k >> lo, kl = 1 << lo, isst = !strcmp(mode, "stair"), m0 = isst ? 1 + f : 0, mb = N - m0;
    fe *row = malloc(sizeof(fe) * k), *Gup = malloc(sizeof(fe) * N * ku), *wup = malloc(sizeof(fe) * N);
    for (int p = 0; p < N; p++) { tree_row(&T2.T, p << lo, row); for (int e = 0; e < ku; e++) Gup[p * ku + e] = row[e << lo]; wup[p] = gf_rand(); }
    long total = 1; for (int a = 0; a < ku; a++) total = total * (mb - a) / (a + 1);
    int *S = malloc(sizeof(int) * (size_t)total * ku), c[64]; long cnt = 0;
    for (int a = 0; a < ku; a++) c[a] = a;
    for (;;) { for (int a = 0; a < ku; a++) S[cnt * ku + a] = m0 + c[a]; cnt++;
        int a = ku - 1; while (a >= 0 && c[a] == mb - ku + a) a--; if (a < 0) break; c[a]++; for (int b = a + 1; b < ku; b++) c[b] = c[b - 1] + 1; }
    if (want < total) for (long i = 0; i < want; i++) { long j = i + (long)rng_below((uint64_t)(total - i)); for (int a = 0; a < ku; a++) { int t = S[i * ku + a]; S[i * ku + a] = S[j * ku + a]; S[j * ku + a] = t; } }
    long nm = want < total ? want : total;
    int *z = calloc(N, sizeof(int));
    if (isst) z[0] = kl - 1;
    else { // zeros spread as in note 69: greedily on the blocks that raise the smallest gains
        int *gain = calloc(nm, sizeof(int)); uint8_t *cover = calloc((size_t)nm * N, 1);
        for (long m = 0; m < nm; m++) for (int a = 0; a < ku; a++) cover[m * N + S[m * ku + a]] = 1;
        for (int t = 0; t < kl - 1; t++) {
            int mn = gain[0]; for (long m = 1; m < nm; m++) if (gain[m] < mn) mn = gain[m];
            int best = -1; long bs2 = -1;
            for (int p = 0; p < N; p++) { if (z[p] == kl) continue; long sc = 0; for (long m = 0; m < nm; m++) if (!cover[m * N + p]) sc += (gain[m] == mn) ? 1000000 : 1; sc = sc * 4 + (3 - (z[p] < 3 ? z[p] : 3)); if (sc > bs2) { bs2 = sc; best = p; } }
            z[best]++; for (long m = 0; m < nm; m++) if (!cover[m * N + best]) gain[m]++;
        }
    }
    fe *Z = malloc(sizeof(fe) * kl * kl), *B = malloc(sizeof(fe) * kl * kl), *Ms = malloc(sizeof(fe) * ku * ku), *bs = malloc(sizeof(fe) * ku), *A = malloc(sizeof(fe) * ku); int nz = 0;
    for (int p = 0; p < N; p++) for (int a = 0; a < z[p]; a++) { tree_row(&T2.T, (p << lo) + a, row); memcpy(Z + nz * kl, row, sizeof(fe) * kl); nz++; }
    gf_kernel(Z, nz, kl, B);
    fe *Msg = calloc((size_t)nm * k, sizeof(fe)); long good = 0;
    for (long l = 0; l < nm; l++) {
        int *s = S + l * ku;
        for (int a = 0; a < ku; a++) { memcpy(Ms + a * ku, Gup + s[a] * ku, sizeof(fe) * ku); bs[a] = wup[s[a]]; }
        if (!gf_solve(Ms, bs, ku, A)) continue;
        for (int e = 0; e < ku; e++) for (int ff = 0; ff < kl; ff++) Msg[(size_t)good * k + ((e << lo) | ff)] = gf_mul(A[e], B[ff]);
        good++;
    }
    sprintf(tag, "%s staircase k=%d n=%d N=%d k_up=%d%s", isst ? "one-sided" : "balanced", k, n, N, ku, isst && f ? " (free blocks)" : "");
    for (int s = 0; s < ns; s++) analyze(argv[a0 + s], &V[s], Msg, good, tag);
    return 0;
}
