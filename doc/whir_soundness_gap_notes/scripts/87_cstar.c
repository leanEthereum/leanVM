// Referee 87: independent checker for note 82 (binary patterns on the T2 tree code over GF(2^64)).
// Own field arithmetic, own tree, own linear algebra. Modes:
//   selftest                       field and encoder self tests
//   chain R V M "<pattern>" [seed] rank, binary full part Q*, B(P;Q*) at every level of the chain
//   atom [seed]                    the Pappus atom at k = 2 (five planes of six members): rank and min over all binary Theta
//   lift [seed]                    rebuild the (8,32) Pappus lift by encoding six codewords, count agreements
//   search V M MODE COUNT SEED     targeted search for a failure of (C*) at rate 1/2 (R = 1), MODE = full | lift
//   minq R V M "<pattern>" [seed] min over all binary Q inside Q* of B(P;Q), for the pattern and for its saturation
//   exh V M [seed]                 every binary pattern at levels 1..V (rate 1/2): (C*) and (C')
//   climb V M COUNT SEED           same, on patterns enlarged greedily while they still carry a solution
// Pattern syntax: one token per leaf, "." empty, "012" a class, "03/14" several groups, "|" ignored.
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
static u64 ginv(u64 a) { u64 r = 1, s = a; for (int i = 1; i < 64; i++) { s = gmul(s, s); r = gmul(r, s); } return r; } // a^(2^64-2)
static u64 rs = 87;
static u64 rnd(void) { u64 z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }

#define MAXD 80
#define MAXROWS 81
#define MAXLV 6
#define MAXNODE 32
#define MAXK 16
typedef struct { int D, rank; int piv[MAXROWS]; u64 row[MAXROWS][MAXD]; } Ech;
static int ech_add(Ech *e, const u64 *vin) {
    u64 v[MAXD]; memcpy(v, vin, sizeof(u64) * e->D);
    for (int b = 0; b < e->rank; b++) { u64 c = v[e->piv[b]]; if (c) { const u64 *r = e->row[b]; for (int i = 0; i < e->D; i++) v[i] ^= gmul(c, r[i]); } }
    int p = -1; for (int i = 0; i < e->D; i++) if (v[i]) { p = i; break; }
    if (p < 0) return 0;
    u64 iv = ginv(v[p]); u64 *r = e->row[e->rank];
    for (int i = 0; i < e->D; i++) r[i] = gmul(iv, v[i]);
    e->piv[e->rank++] = p; return 1;
}
// kernel of the row space: returns nullity, vectors in ker[][]
static int ech_kernel(const Ech *e0, u64 ker[][MAXD]) {
    static Ech e; e = *e0; int D = e.D;
    for (int b = e.rank - 1; b >= 0; b--) for (int b2 = 0; b2 < b; b2++) { u64 c = e.row[b2][e.piv[b]]; if (c) for (int i = 0; i < D; i++) e.row[b2][i] ^= gmul(c, e.row[b][i]); }
    char ispiv[MAXD] = {0}; for (int b = 0; b < e.rank; b++) ispiv[e.piv[b]] = 1;
    int nk = 0;
    for (int f = 0; f < D; f++) if (!ispiv[f]) { memset(ker[nk], 0, sizeof(u64) * D); ker[nk][f] = 1; for (int b = 0; b < e.rank; b++) ker[nk][e.piv[b]] = e.row[b][f]; nk++; }
    return nk;
}

static int R_, V_, L_; // rate 2^-R, k = 2^V, L+1 members
static u64 G[MAXLV][MAXNODE][MAXK], TW[MAXLV][MAXNODE];
static void build_tree(void) {
    for (int p = 0; p < (1 << R_); p++) G[0][p][0] = 1;
    for (int j = 1; j <= V_; j++) for (int p = 0; p < (1 << (R_ + j - 1)); p++) {
        u64 t0, t1; do { t0 = rnd(); t1 = rnd(); } while (t0 == t1);
        for (int b = 0; b < 2; b++) { u64 t = b ? t1 : t0; TW[j][2 * p + b] = t; int kh = 1 << (j - 1);
            for (int c = 0; c < kh; c++) { G[j][2 * p + b][c] = G[j - 1][p][c]; G[j][2 * p + b][kh + c] = gmul(t, G[j - 1][p][c]); } }
    }
}
// top-down folding encoder, independent of G: node of level j holds k/2^j values
static void encode(const u64 *msg, u64 *cw) {
    static u64 cur[MAXNODE][MAXK], nxt[MAXNODE][MAXK]; int k = 1 << V_;
    for (int p = 0; p < (1 << R_); p++) memcpy(cur[p], msg, sizeof(u64) * k);
    for (int j = 1; j <= V_; j++) { int len = k >> j;
        for (int x = 0; x < (1 << (R_ + j)); x++) for (int i = 0; i < len; i++) nxt[x][i] = cur[x >> 1][2 * i] ^ gmul(TW[j][x], cur[x >> 1][2 * i + 1]);
        memcpy(cur, nxt, sizeof cur); }
    for (int x = 0; x < (1 << (R_ + V_)); x++) cw[x] = cur[x][0];
}

typedef struct { int nb[MAXNODE]; int bas[MAXNODE][5]; } Pat; // binary subspace of F_2^L at each node, echelon by leading bit
static int f2_add(int *bas, int *nb, int v) {
    for (int i = 0; i < *nb; i++) { int lead = 31 - __builtin_clz(bas[i]); if ((v >> lead) & 1) v ^= bas[i]; }
    if (!v) return 0;
    int lead = 31 - __builtin_clz(v);
    for (int i = 0; i < *nb; i++) if ((bas[i] >> lead) & 1) bas[i] ^= v;
    bas[(*nb)++] = v; return 1;
}
static int evec(int a) { return a == 0 ? 0 : 1 << (a - 1); } // e_0 = 0
static void pat_add_class(Pat *P, int node, int classmask) { // members with bit set agree
    int first = -1; for (int a = 0; a <= L_; a++) if ((classmask >> a) & 1) { if (first < 0) first = a; else f2_add(P->bas[node], &P->nb[node], evec(first) ^ evec(a)); }
}
static int parse(const char *s, Pat *P, int nnodes) {
    memset(P, 0, sizeof *P); int node = 0; const char *p = s;
    while (*p) { while (*p == ' ' || *p == '|') p++; if (!*p) break; if (node >= nnodes) return -1;
        int cm = 0; while (*p && *p != ' ' && *p != '|') { if (*p == '/') { pat_add_class(P, node, cm); cm = 0; } else if (*p >= '0' && *p <= '9') cm |= 1 << (*p - '0'); p++; }
        pat_add_class(P, node, cm); node++; }
    return node;
}
static int weight(const Pat *P, int nnodes) { int w = 0; for (int x = 0; x < nnodes; x++) w += P->nb[x]; return w; }
static void rowvec(int j, int node, int theta, u64 *v) { int kj = 1 << j; memset(v, 0, sizeof(u64) * L_ * kj); for (int l = 0; l < L_; l++) if ((theta >> l) & 1) memcpy(v + l * kj, G[j][node], sizeof(u64) * kj); }
static int pat_rank(int j, const Pat *P, Ech *e) {
    e->D = L_ << j; e->rank = 0; u64 v[MAXD];
    for (int x = 0; x < (1 << (R_ + j)); x++) for (int i = 0; i < P->nb[x]; i++) { rowvec(j, x, P->bas[x][i], v); ech_add(e, v); }
    return e->rank;
}
static u64 KER[MAXD][MAXD];
// binary full part of the pattern P at level j >= 1 (echelon e of its rows): pattern Q at level j-1
static void qstar(int j, const Ech *e, Pat *Q) {
    int nk = ech_kernel(e, KER); int kj = 1 << j, kh = kj >> 1; memset(Q, 0, sizeof *Q);
    for (int p = 0; p < (1 << (R_ + j - 1)); p++) {
        int mb[5], nm = 0;
        for (int a = 0; a < nk; a++) for (int c = 0; c < 2; c++) { u64 d[5];
            for (int l = 0; l < L_; l++) { u64 s = 0; for (int cc = 0; cc < kh; cc++) s ^= gmul(KER[a][l * kj + c * kh + cc], G[j - 1][p][cc]); d[l] = s; }
            for (int b = 0; b < 64 && nm < L_; b++) { int m = 0; for (int l = 0; l < L_; l++) m |= (int)((d[l] >> b) & 1) << l; if (m) f2_add(mb, &nm, m); } }
        for (int th = 1; th < (1 << L_); th++) { int ok = 1; for (int i = 0; i < nm; i++) if (__builtin_parity(th & mb[i])) ok = 0; if (ok) f2_add(Q->bas[p], &Q->nb[p], th); }
    }
}
static Ech EU;
// B(P;Q) = 2 r_up(Q) + sum_x (r_up(Q v Lambda_x@p) - r_up(Q)); P at level j, Q at level j-1
static int bound(int j, const Pat *P, const Pat *Q, int *rup) {
    int r = pat_rank(j - 1, Q, &EU); *rup = r; int tot = 2 * r; u64 v[MAXD];
    for (int x = 0; x < (1 << (R_ + j)); x++) { int saved = EU.rank; for (int i = 0; i < P->nb[x]; i++) { rowvec(j - 1, x >> 1, P->bas[x][i], v); ech_add(&EU, v); } tot += EU.rank - saved; EU.rank = saved; }
    return tot;
}
static void print_pat(const Pat *P, int nnodes) {
    for (int x = 0; x < nnodes; x++) { if (!P->nb[x]) printf(". "); else { for (int i = 0; i < P->nb[x]; i++) { if (i) printf("+"); int th = P->bas[x][i]; // print as a set of members: even-weight lift
                int par = __builtin_parity(th); if (par) printf("0"); for (int l = 0; l < L_; l++) if ((th >> l) & 1) printf("%d", l + 1); } printf(" "); } }
}
static Ech E1;
// returns 1 if B(P;Q*) == rank at level j
static int cstar(int j, const Pat *P, Pat *Q, int *rank, int *B, int *rup) { *rank = pat_rank(j, P, &E1); qstar(j, &E1, Q); *B = bound(j, P, Q, rup); return *B == *rank; }

static void do_chain(const char *s) {
    Pat P, Q; int n = 1 << (R_ + V_); if (parse(s, &P, n) != n) { printf("bad pattern length\n"); return; }
    for (int j = V_; j >= 1; j--) { int rank, B, rup; int ok = cstar(j, &P, &Q, &rank, &B, &rup); int nn = 1 << (R_ + j);
        printf("level (k=%d, n=%d): w = %d, Lk = %d, rank = %d, Q*: weight %d, rank %d, B(P;Q*) = %d  %s\n   Q* = ", 1 << j, nn, weight(&P, nn), L_ << j, rank, weight(&Q, nn / 2), rup, B, ok ? "(C*) holds" : "(C*) FAILS");
        print_pat(&Q, nn / 2); printf("\n"); P = Q; }
}

// all F_2-subspaces Theta of F_2^L: min of 2 dim Theta + sum_x dim(Lambda_x / (Lambda_x cap Theta)) at k = 2 (upper code has no twiddle)
static int min_theta(const Pat *P, int nleaves, long *nsub) {
    int best = 1 << 30; long cnt = 0; static char seen[1 << 16]; (void)seen;
    // enumerate subspaces by their reduced bases: brute force over all subsets of vectors as spanning sets up to dimension L, dedupe by the set of elements (bitmask of 2^L bits <= 32 bits)
    int nv = 1 << L_; static uint32_t list[100000]; int nl = 0;
    // closure-based enumeration: start with {0}, repeatedly add a vector
    list[nl++] = 1u; // subspace {0} as a bitmask over vectors
    for (int i = 0; i < nl; i++) { uint32_t S = list[i];
        for (int v = 1; v < nv; v++) if (!((S >> v) & 1)) { uint32_t T = S; for (int u = 0; u < nv; u++) if ((S >> u) & 1) T |= 1u << (u ^ v); int dup = 0; for (int q = 0; q < nl; q++) if (list[q] == T) { dup = 1; break; } if (!dup) list[nl++] = T; } }
    for (int i = 0; i < nl; i++) { uint32_t S = list[i]; int dim = __builtin_ctz(__builtin_popcount(S)); int val = 2 * dim; cnt++;
        for (int x = 0; x < nleaves; x++) { // dim(Lambda_x + Theta) - dim Theta
            int bas[5], nb = 0; for (int v = 1; v < nv; v++) if ((S >> v) & 1) f2_add(bas, &nb, v); int d0 = nb; for (int q = 0; q < P->nb[x]; q++) f2_add(bas, &nb, P->bas[x][q]); val += nb - d0; }
        if (val < best) best = val; }
    *nsub = cnt; return best;
}

static void do_lift(void) {
    R_ = 2; V_ = 3; L_ = 5; build_tree();
    // top pattern on the 8 nodes of level 1
    Pat T; parse("012 03/14 23/15 05/24 345 . . .", &T, 8); Ech e; int rk = pat_rank(1, &T, &e); static u64 ker[MAXD][MAXD]; int nk = ech_kernel(&e, ker);
    printf("top Pappus pattern on T_1 ([8,2]): weight %d, rank %d, kernel dimension %d\n", weight(&T, 8), rk, nk);
    if (nk != 1) { printf("unexpected kernel\n"); return; }
    u64 A[5][2]; for (int l = 0; l < 5; l++) for (int c = 0; c < 2; c++) A[l][c] = ker[0][l * 2 + c];
    // lower factor B in K^4 vanishing at the leaves 20, 25, 30; beta_x[e] = G[3][x][2e]
    Ech eb; eb.D = 4; eb.rank = 0; int zl[3] = {20, 25, 30}; for (int i = 0; i < 3; i++) { u64 v[MAXD]; for (int q = 0; q < 4; q++) v[q] = G[3][zl[i]][2 * q]; ech_add(&eb, v); }
    int nb = ech_kernel(&eb, ker); printf("lower factor: %d conditions, kernel dimension %d\n", eb.rank, nb); u64 Bv[4]; memcpy(Bv, ker[0], sizeof Bv);
    u64 msg[6][8], cw[6][32], common[8]; for (int c = 0; c < 8; c++) common[c] = rnd();
    for (int l = 0; l < 6; l++) for (int c = 0; c < 8; c++) msg[l][c] = common[c] ^ (l ? gmul(Bv[c >> 1], A[l - 1][c & 1]) : 0);
    for (int l = 0; l < 6; l++) encode(msg[l], cw[l]);
    // cross-check of the encoder against the rows G
    for (int l = 0; l < 6; l++) for (int x = 0; x < 32; x++) { u64 s = 0; for (int c = 0; c < 8; c++) s ^= gmul(msg[l][c], G[3][x][c]); if (s != cw[l][x]) { printf("ENCODER MISMATCH\n"); return; } }
    int distinct = 1; for (int a = 0; a < 6; a++) for (int b = a + 1; b < 6; b++) if (!memcmp(cw[a], cw[b], sizeof cw[a])) distinct = 0;
    const char *pat = "012 012 012 012 | 03 03 14 14 | 23 15 23 15 | 05 24 24 05 | 345 345 345 345 | 012345 . . . | . 012345 . . | . . 012345 .";
    int cls[32], nleaf = 0; { const char *p = pat; while (*p) { while (*p == ' ' || *p == '|') p++; if (!*p) break; int cm = 0; while (*p && *p != ' ' && *p != '|') { if (*p >= '0' && *p <= '9') cm |= 1 << (*p - '0'); p++; } cls[nleaf++] = cm; } }
    int w = 0, wplur = 0, agree[6] = {0}, okclass = 1;
    for (int x = 0; x < 32; x++) {
        int best = 1; for (int a = 0; a < 6; a++) { int c = 0; for (int b = 0; b < 6; b++) if (cw[b][x] == cw[a][x]) c++; if (c > best) best = c; } wplur += best - 1;
        if (cls[x]) { int first = __builtin_ctz(cls[x]); u64 y = cw[first][x]; for (int a = 0; a < 6; a++) if ((cls[x] >> a) & 1) { if (cw[a][x] != y) okclass = 0; }
            int c = 0; for (int a = 0; a < 6; a++) if (cw[a][x] == y) { agree[a]++; c++; } w += c - 1; }
    }
    printf("six codewords distinct: %s; every class of the pattern agrees: %s\n", distinct ? "yes" : "NO", okclass ? "yes" : "NO");
    printf("word y read off the pattern: agreements per codeword = %d %d %d %d %d %d, weight w = sum_x (c_x - 1) = %d, Lk = 40; plurality weight %d\n", agree[0], agree[1], agree[2], agree[3], agree[4], agree[5], w, wplur);
    Pat P; parse(pat, &P, 32); Ech e2; printf("rank of the class pattern at (8,32): %d (kernel %d)\n", pat_rank(3, &P, &e2), 40 - e2.rank);
}

static void rand_class(Pat *P, int node, int minsize) { int cm; do { cm = (int)(rnd() & ((1u << (L_ + 1)) - 1)); } while (__builtin_popcount(cm) < minsize); pat_add_class(P, node, cm); }
static int gen_pattern(int mode_lift, Pat *P) {
    int n = 1 << (R_ + V_), k = 1 << V_, full = (1 << (L_ + 1)) - 1;
    memset(P, 0, sizeof *P);
        if (!mode_lift) {
            int f = 3 + (int)(rnd() % (k / 2 + 1 - 2)); if (f > k) f = k; // full leaves in distinct pairs
            int pairs[MAXNODE]; for (int i = 0; i < n / 2; i++) pairs[i] = i; for (int i = n / 2 - 1; i > 0; i--) { int q = (int)(rnd() % (i + 1)); int t = pairs[i]; pairs[i] = pairs[q]; pairs[q] = t; }
            char isfull[MAXNODE] = {0}; for (int i = 0; i < f; i++) { int x = 2 * pairs[i] + (int)(rnd() & 1); isfull[x] = 1; pat_add_class(P, x, full); }
            int target = L_ * k - 3 + (int)(rnd() % (L_ + 6)); int pe = (int)(rnd() % 3);
            for (int tries = 0; tries < 4 * n && weight(P, n) < target; tries++) { int x = (int)(rnd() % n); if (isfull[x] || P->nb[x]) continue;
                if (pe == 0 && P->nb[x ^ 1] && !isfull[x ^ 1] && (rnd() & 1)) { P->nb[x] = P->nb[x ^ 1]; memcpy(P->bas[x], P->bas[x ^ 1], sizeof P->bas[x]); } // copy the sibling
                else { int sz = 2 + ((rnd() % 4 == 0) ? 1 + (int)(rnd() % L_) : 0); if (sz > L_ + 1) sz = L_ + 1; int cm = 0; while (__builtin_popcount(cm) < sz) cm |= 1 << (rnd() % (L_ + 1)); pat_add_class(P, x, cm); } }
        } else {
            // lift: random top partition pattern with a solution at split level s, zeros of the lower factor become full leaves
            int s = 1 + (int)(rnd() % (V_ - 1)); int ntop = 1 << (R_ + s), blk = 1 << (V_ - s); Pat T; Ech et; int tr = 0;
            do { memset(&T, 0, sizeof T); int tw = L_ * (1 << s) - 1 - (int)(rnd() % 2) + (int)(rnd() % 3);
                for (int tries = 0; tries < 8 * ntop && weight(&T, ntop) < tw; tries++) { int a = (int)(rnd() % ntop); int cm = 0; int sz = 2 + (int)(rnd() % 2); while (__builtin_popcount(cm) < sz) cm |= 1 << (rnd() % (L_ + 1)); pat_add_class(&T, a, cm); }
                tr++; } while (pat_rank(s, &T, &et) >= L_ * (1 << s) && tr < 200);
            if (tr >= 200) return 0;
            int nz = blk - 1; char isz[MAXNODE] = {0}; for (int i = 0; i < nz;) { int x = (int)(rnd() % n); if (!isz[x]) { isz[x] = 1; i++; } }
            for (int x = 0; x < n; x++) { int a = x >> (V_ - s);
                if (isz[x]) pat_add_class(P, x, full);
                else if (T.nb[a]) { // one group of the top space: a random nonzero vector of it gives a pair-like class; use a class contained in the top space
                    // pick a random class (subset of members) whose difference space lies in T[a]
                    for (int tries = 0; tries < 20; tries++) { int cm = 0; int sz = 2 + (int)(rnd() % L_); while (__builtin_popcount(cm) < sz) cm |= 1 << (rnd() % (L_ + 1));
                        Pat tmp; memset(&tmp, 0, sizeof tmp); pat_add_class(&tmp, 0, cm); int bas[5], nb = T.nb[a]; memcpy(bas, T.bas[a], sizeof bas); int inside = 1; for (int q = 0; q < tmp.nb[0]; q++) if (f2_add(bas, &nb, tmp.bas[0][q])) inside = 0;
                        if (inside) { pat_add_class(P, x, cm); break; } } } }
            int npert = (int)(rnd() % 3); for (int i = 0; i < npert; i++) { int x = (int)(rnd() % n); if (isz[x]) continue; P->nb[x] = 0; if (rnd() & 1) rand_class(P, x, 2); }
        }
    return 1;
}
static void do_search(int mode_lift, long count, int verbose) {
    R_ = 1; int n = 1 << (R_ + V_), k = 1 << V_; long tested = 0, dep = 0, fails = 0, withfull3 = 0, nontriv = 0, both = 0; Pat P, Q;
    build_tree();
    for (long it = 0; it < count; it++) {
        if (it % 2000 == 1999) build_tree(); // fresh twiddles now and then
        if (!gen_pattern(mode_lift, &P)) continue;
        int nfull = 0; for (int x = 0; x < n; x++) if (P.nb[x] == L_) nfull++;
        int rank, B, rup; int ok = cstar(V_, &P, &Q, &rank, &B, &rup); tested++; if (rank < weight(&P, n)) dep++; if (nfull >= 3) withfull3++; if (rank < L_ * k) { nontriv++; if (rank < weight(&P, n)) both++; }
        if (!ok) { fails++; printf("FAIL: w=%d rank=%d B(P;Q*)=%d : ", weight(&P, n), rank, B); print_pat(&P, n); printf("\n"); fflush(stdout); }
        else if (verbose && it < 5) { printf("sample: w=%d rank=%d B=%d rup=%d : ", weight(&P, n), rank, B, rup); print_pat(&P, n); printf("\n"); }
    }
    printf("search (k=%d, n=%d), %d members, mode %s: %ld patterns, %ld with dependent rows, %ld with a solution (rank < Lk), %ld with both, %ld with at least 3 full leaves, (C*) failures: %ld\n", k, n, L_ + 1, mode_lift ? "lift" : "full", tested, dep, nontriv, both, withfull3, fails);
}


static int cls_of(const Pat *P, int x) { int cm = 0; for (int i = 0; i < P->nb[x]; i++) { int th = P->bas[x][i]; if (__builtin_parity(th)) cm |= 1; cm |= th << 1; } return cm; }
// climb: start from a pattern with a solution, enlarge classes while a solution survives, test (C*) on the way and at the end
static void do_climb(long count) {
    R_ = 1; int n = 1 << (R_ + V_), k = 1 << V_; long starts = 0, tested = 0, fails = 0, sumdef = 0, maxdef = 0; Pat P, Q, T2; Ech e;
    build_tree();
    for (long it = 0; it < count; it++) {
        if (it % 500 == 499) build_tree();
        if (!gen_pattern((int)(it & 1), &P)) continue;
        if (pat_rank(V_, &P, &e) >= L_ * k) continue;
        starts++; int cls[MAXNODE]; for (int x = 0; x < n; x++) cls[x] = cls_of(&P, x);
        int acc = 0;
        for (int step = 0; step < 6 * n; step++) {
            int x = (int)(rnd() % n); int cm = cls[x]; int a = (int)(rnd() % (L_ + 1)); if ((cm >> a) & 1) continue;
            int ncm = cm | (1 << a); if (!cm) { int b2 = (int)(rnd() % (L_ + 1)); if (b2 == a) continue; ncm |= 1 << b2; }
            T2 = P; T2.nb[x] = 0; pat_add_class(&T2, x, ncm);
            if (pat_rank(V_, &T2, &e) < L_ * k) { P = T2; cls[x] = ncm; acc++;
                if (acc % (n / 2) == 0) { int rank, B, rup; tested++; if (!cstar(V_, &P, &Q, &rank, &B, &rup)) { fails++; printf("FAIL: w=%d rank=%d B(P;Q*)=%d : ", weight(&P, n), rank, B); print_pat(&P, n); printf("\n"); fflush(stdout); } } }
        }
        int rank, B, rup; tested++; int ok = cstar(V_, &P, &Q, &rank, &B, &rup); int def = weight(&P, n) - rank; sumdef += def; if (def > maxdef) maxdef = def;
        if (!ok) { fails++; printf("FAIL: w=%d rank=%d B(P;Q*)=%d : ", weight(&P, n), rank, B); print_pat(&P, n); printf("\n"); fflush(stdout); }
    }
    printf("climb (k=%d, n=%d), %d members: %ld starts with a solution, %ld patterns tested (all with a solution), mean final deficiency w - r = %.2f, max %ld, (C*) failures: %ld\n", k, n, L_ + 1, starts, tested, starts ? (double)sumdef / starts : 0.0, maxdef, fails);
}

// all subspaces of the span of bas[0..nb): returns their number, bases in out
static int subspaces(const int *bas, int nb, int out[][5], int *outnb) {
    int nv = 1 << L_; static uint32_t list[400]; int nl = 0; char inspan[32];
    for (int v = 0; v < nv; v++) { int b2[5], n2 = nb; memcpy(b2, bas, sizeof(int) * 5); inspan[v] = (v == 0) || !f2_add(b2, &n2, v); }
    list[nl++] = 1u;
    for (int i = 0; i < nl; i++) { uint32_t S = list[i];
        for (int v = 1; v < nv; v++) if (inspan[v] && !((S >> v) & 1)) { uint32_t T = S; for (int u = 0; u < nv; u++) if ((S >> u) & 1) T |= 1u << (u ^ v); int dup = 0; for (int q = 0; q < nl; q++) if (list[q] == T) { dup = 1; break; } if (!dup) list[nl++] = T; } }
    for (int i = 0; i < nl; i++) { outnb[i] = 0; for (int v = 1; v < nv; v++) if ((list[i] >> v) & 1) f2_add(out[i], &outnb[i], v); }
    return nl;
}
static int SUBS[MAXNODE][400][5], SUBNB[MAXNODE][400], NSUB[MAXNODE];
// min over all binary Q contained in Q* of B(P;Q) (every exact Q is contained in Q*); exhaustive if the product is small, else coordinate descent
static int min_over_q(int j, const Pat *P, const Pat *Qs, int *exhaustive, Pat *best) {
    int np = 1 << (R_ + j - 1); double total = 1; for (int p = 0; p < np; p++) { NSUB[p] = subspaces(Qs->bas[p], Qs->nb[p], SUBS[p], SUBNB[p]); total *= NSUB[p]; }
    int rup, bestB = 1 << 30; Pat Q;
    if (total <= 3e6) { *exhaustive = 1; int idx[MAXNODE] = {0};
        for (;;) { memset(&Q, 0, sizeof Q); for (int p = 0; p < np; p++) { Q.nb[p] = SUBNB[p][idx[p]]; memcpy(Q.bas[p], SUBS[p][idx[p]], sizeof Q.bas[p]); }
            int B = bound(j, P, &Q, &rup); if (B < bestB) { bestB = B; *best = Q; }
            int p = 0; while (p < np && ++idx[p] == NSUB[p]) idx[p++] = 0; if (p == np) break; }
        return bestB; }
    *exhaustive = 0;
    for (int start = 0; start < 6; start++) { // coordinate descent from Q*, from 0 and from random points
        int idx[MAXNODE]; for (int p = 0; p < np; p++) idx[p] = start == 0 ? NSUB[p] - 1 : start == 1 ? 0 : (int)(rnd() % NSUB[p]);
        int cur = 1 << 30, improved = 1;
        while (improved) { improved = 0;
            for (int p = 0; p < np; p++) { int keep = idx[p];
                for (int c = 0; c < NSUB[p]; c++) { idx[p] = c; memset(&Q, 0, sizeof Q); for (int q = 0; q < np; q++) { Q.nb[q] = SUBNB[q][idx[q]]; memcpy(Q.bas[q], SUBS[q][idx[q]], sizeof Q.bas[q]); }
                    int B = bound(j, P, &Q, &rup); if (B < cur) { cur = B; keep = c; improved = 1; if (B < bestB) { bestB = B; *best = Q; } } }
                idx[p] = keep; } } }
    return bestB;
}
static void do_minq(const char *s) {
    Pat P, Q, S, best; int n = 1 << (R_ + V_); if (parse(s, &P, n) != n) { printf("bad pattern length\n"); return; }
    int rank, B, rup; cstar(V_, &P, &Q, &rank, &B, &rup); int nk = ech_kernel(&E1, KER); int k = 1 << V_;
    // saturation: all binary functionals that vanish on every solution at the leaf
    memset(&S, 0, sizeof S);
    for (int x = 0; x < n; x++) { int mb[5], nm = 0;
        for (int a = 0; a < nk; a++) { u64 d[5]; for (int l = 0; l < L_; l++) { u64 t = 0; for (int c = 0; c < k; c++) t ^= gmul(KER[a][l * k + c], G[V_][x][c]); d[l] = t; }
            for (int b = 0; b < 64 && nm < L_; b++) { int m = 0; for (int l = 0; l < L_; l++) m |= (int)((d[l] >> b) & 1) << l; if (m) f2_add(mb, &nm, m); } }
        for (int th = 1; th < (1 << L_); th++) { int ok = 1; for (int i = 0; i < nm; i++) if (__builtin_parity(th & mb[i])) ok = 0; if (ok) f2_add(S.bas[x], &S.nb[x], th); } }
    Ech e; int rs2 = pat_rank(V_, &S, &e);
    printf("pattern   : w = %d, Lk = %d, rank = %d (kernel %d), Q*: weight %d, rank %d, B(P;Q*) = %d\n   P  = ", weight(&P, n), L_ * k, rank, L_ * k - rank, weight(&Q, n / 2), rup, B); print_pat(&P, n); printf("\n   Q* = "); print_pat(&Q, n / 2); printf("\n");
    int ex; int m1 = min_over_q(V_, &P, &Q, &ex, &best); printf("   min over binary Q inside Q* of B(P;Q) = %d (%s): (C') %s\n", m1, ex ? "exhaustive" : "coordinate descent, an upper estimate of the minimum", m1 == rank ? "holds" : "FAILS");
    int Bs = bound(V_, &S, &Q, &rup);
    printf("saturation: w = %d, rank = %d, B(S;Q*) = %d\n   S  = ", weight(&S, n), rs2, Bs); print_pat(&S, n); printf("\n");
    int m2 = min_over_q(V_, &S, &Q, &ex, &best); printf("   min over binary Q inside Q* of B(S;Q) = %d (%s): (C') %s for the saturated pattern\n   best Q = ", m2, ex ? "exhaustive" : "coordinate descent, an upper estimate of the minimum", m2 == rs2 ? "holds" : "FAILS"); print_pat(&best, n / 2); printf("\n");
}

// exhaustive check of (C') at levels 1..V over all binary patterns (all subspaces of F_2^L at every node)
static void do_exh(void) {
    build_tree(); static int ALL[400][5], ALLNB[400]; int fullb[5], nf = 0; for (int l = 0; l < L_; l++) f2_add(fullb, &nf, 1 << l);
    int nsub = subspaces(fullb, nf, ALL, ALLNB);
    for (int j = 1; j <= V_; j++) { int nn = 1 << (R_ + j); long tot = 0, dep = 0, star = 0, other = 0, fail = 0; int idx[MAXNODE] = {0}; Pat P, Q, best;
        for (;;) { for (int x = 0; x < nn; x++) { P.nb[x] = ALLNB[idx[x]]; memcpy(P.bas[x], ALL[idx[x]], sizeof P.bas[x]); }
            int rank, B, rup; tot++; int ok = cstar(j, &P, &Q, &rank, &B, &rup); if (rank < weight(&P, nn)) dep++;
            if (ok) star++; else { int ex; int m = min_over_q(j, &P, &Q, &ex, &best); if (m == rank && ex) other++; else { fail++; if (fail <= 5) { printf("  (C') not certified: rank %d min %d : ", rank, m); print_pat(&P, nn); printf("\n"); } } }
            int x = 0; while (x < nn && ++idx[x] == nsub) idx[x++] = 0; if (x == nn) break; }
        printf("exhaustive (k=%d, n=%d), %d members, %d subspaces a node: %ld patterns, %ld with dependent rows, B(P;Q*) = rank on %ld, another binary Q inside Q* reaches the rank on %ld, (C') fails on %ld\n", 1 << j, nn, L_ + 1, nsub, tot, dep, star, other, fail); fflush(stdout); }
}
int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "selftest")) {
        int bad = 0; for (int i = 0; i < 100000; i++) { u64 a = rnd(), b = rnd(), c = rnd(); if (gmul(a, b) != gmul_ref(a, b)) bad++; if (gmul(a, b ^ c) != (gmul(a, b) ^ gmul(a, c))) bad++; if (a && gmul(a, ginv(a)) != 1) bad++; if (gmul(gmul(a, b), c) != gmul(a, gmul(b, c))) bad++; }
        R_ = 2; V_ = 3; L_ = 2; build_tree(); u64 m[8], cw[32]; for (int c = 0; c < 8; c++) m[c] = rnd(); encode(m, cw);
        for (int x = 0; x < 32; x++) { u64 s = 0; for (int c = 0; c < 8; c++) s ^= gmul(m[c], G[3][x][c]); if (s != cw[x]) bad++; }
        printf("selftest: %d errors\n", bad); return bad != 0;
    }
    if (!strcmp(argv[1], "chain")) { R_ = atoi(argv[2]); V_ = atoi(argv[3]); L_ = atoi(argv[4]) - 1; if (argc > 6) rs = strtoull(argv[6], 0, 10); build_tree(); do_chain(argv[5]); return 0; }
    if (!strcmp(argv[1], "minq")) { R_ = atoi(argv[2]); V_ = atoi(argv[3]); L_ = atoi(argv[4]) - 1; if (argc > 6) rs = strtoull(argv[6], 0, 10); build_tree(); do_minq(argv[5]); return 0; }
    if (!strcmp(argv[1], "exh")) { R_ = 1; V_ = atoi(argv[2]); L_ = atoi(argv[3]) - 1; if (argc > 4) rs = strtoull(argv[4], 0, 10); do_exh(); return 0; }
    if (!strcmp(argv[1], "atom")) { if (argc > 2) rs = strtoull(argv[2], 0, 10); R_ = 2; V_ = 1; L_ = 5; build_tree(); Pat P; parse("012 03/14 23/15 05/24 345 . . .", &P, 8); Ech e; int r = pat_rank(1, &P, &e); long ns; int mt = min_theta(&P, 8, &ns);
        printf("Pappus atom at k = 2, five leaves: weight %d, rank %d; min over all %ld binary subspaces Theta of 2 dim Theta + sum_x dim(Lambda_x/(Lambda_x cap Theta)) = %d\n", weight(&P, 8), r, ns, mt);
        parse("01/23 02/14 03/15 04/25 05/34 . . .", &P, 8); r = pat_rank(1, &P, &e); mt = min_theta(&P, 8, &ns);
        printf("five double pairs (characteristic 2 atom): weight %d, rank %d; min over binary Theta = %d\n", weight(&P, 8), r, mt);
        L_ = 3; parse("02/13 01/23 03/12 . . . . .", &P, 8); r = pat_rank(1, &P, &e); mt = min_theta(&P, 8, &ns); printf("three matchings of four members (Finding 3.1): weight %d, rank %d; min over all %ld binary Theta = %d\n", weight(&P, 8), r, ns, mt); return 0; }
    if (!strcmp(argv[1], "lift")) { if (argc > 2) rs = strtoull(argv[2], 0, 10); do_lift(); return 0; }
    if (!strcmp(argv[1], "climb")) { V_ = atoi(argv[2]); L_ = atoi(argv[3]) - 1; rs = strtoull(argv[5], 0, 10); do_climb(atol(argv[4])); return 0; }
    if (!strcmp(argv[1], "search")) { V_ = atoi(argv[2]); L_ = atoi(argv[3]) - 1; int ml = !strcmp(argv[4], "lift"); long cnt = atol(argv[5]); rs = strtoull(argv[6], 0, 10); do_search(ml, cnt, argc > 7); return 0; }
    return 1;
}
