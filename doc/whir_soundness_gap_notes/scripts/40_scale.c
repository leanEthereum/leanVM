/* 40_scale.c: smallest weighted degree of a first integral dE (Y1-degree 1) with contact order 4 along
 * all lines of a word, on an F2-subspace of GF(2^16), for 40-rate-half-residual.md.
 *
 * E = sum e_ik X^i Y^k, exponents not both even. Contact order >= 4 at (alpha, y) iff the Taylor
 * coefficients (r, q) in {(1,0),(0,1),(1,1),(3,0),(2,1),(1,2),(0,3)} of E at that point vanish
 * (40_checks.py B). The weighted degree of dE for the weights (1, D, D) is the largest of i + D k (k odd)
 * and i - 1 + D k (k even, i odd). Columns are processed in increasing order of that number, so the first
 * column that depends on the previous ones gives the smallest W; the dependency is the polynomial E.
 *
 * Output per word: W_min, W_min / n, the number of independent solutions at W_min, deg_Y E, and the degree
 * of gcd(E_Y(x0, Y), E_X(x0, Y)) at a point x0 outside D (0 means dE has no factor involving Y0).
 *
 * Build: cc -O2 -o 40_scale 40_scale.c
 * With the environment variable J=3 the contact order imposed is 6 (15 conditions per point) instead of 4.
 * With the environment variable FULL set, the modes bin, tri, lin and inv use the whole solution space with
 * W <= 11n/4 - 4 instead of the first solution, and report a word iff a random combination is coprime.
 * Run:   ./40_scale N word [seed [dumpfile]]   (dumpfile: E, the domain and the word, read by 40_bezout.py)
 *        ./40_scale N word [seed]     word = e (the monomial X^e), or r (random word), or sweep (e = 0.66n..0.80n),
 *        or bin (all binomials X^e + c X^f, n/2 <= f < e < n, c = 1 and one random c; prints those whose
 *        W_min is below 11n/4 - 2 with coprime E_Y, E_X), or lin (X^e times a linearized polynomial),
 *        or full (every monomial word: the whole solution space with W <= 11n/4 - 4, gcd test on a random
 *        combination of the solutions; "solutions" is then the dimension of that space),
 *        or tri (all trinomials X^e + X^f + X^g, n/2 <= g < f < e < n), or inv (the words alpha^(-j) on
 *        D minus 0, 1 <= j < n, conditions on the n - 1 nonzero points only)
 *        domain: a random F2-subspace of dimension N; "N 0" as first argument pair uses a random set instead:
 *        ./40_scale -N word [seed]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define Q 65536
static uint16_t EXPT[2 * Q], LOGT[Q];

static void gf_init(void) {
    uint32_t v = 1;
    for (int i = 0; i < Q - 1; i++) {
        EXPT[i] = (uint16_t)v;
        LOGT[v] = (uint16_t)i;
        v <<= 1;
        if (v & Q) v ^= 0x1002D;
    }
    if (v != 1) { fprintf(stderr, "modulus not primitive\n"); exit(1); }
    for (int i = Q - 1; i < 2 * Q; i++) EXPT[i] = EXPT[i - (Q - 1)];
}
static inline uint16_t mul(uint16_t a, uint16_t b) { return (a && b) ? EXPT[LOGT[a] + LOGT[b]] : 0; }
static inline uint16_t inv(uint16_t a) { return EXPT[Q - 1 - LOGT[a]]; }
static uint16_t fpow(uint16_t a, long e) {
    if (e == 0) return 1;
    if (!a) return 0;
    return EXPT[(int)(((long)LOGT[a] * e) % (Q - 1))];
}
static uint64_t rs = 88172645463325252ULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }
static int binom2(int a, int b) { return b <= a && (b & ~a) == 0; }

typedef struct { int i, k, w; } Mono;
static int cmp_mono(const void *a, const void *b) {
    const Mono *x = a, *y = b;
    if (x->w != y->w) return x->w - y->w;
    if (x->k != y->k) return x->k - y->k;
    return x->i - y->i;
}

static int pdeg(const uint16_t *p, int n) { while (n > 0 && !p[n - 1]) n--; return n - 1; }
/* degree of gcd of two polynomials of length len (destroys them) */
static int gcd_deg(uint16_t *p, uint16_t *q, int len) {
    int dp = pdeg(p, len), dq = pdeg(q, len);
    while (dq >= 0) {
        while (dp >= dq) {
            uint16_t c = mul(p[dp], inv(q[dq]));
            for (int t = 0; t <= dq; t++) p[dp - dq + t] ^= mul(c, q[t]);
            dp = pdeg(p, dp + 1);
            if (dp < 0) break;
        }
        uint16_t *tp = p; p = q; q = tp;
        int td = dp; dp = dq; dq = td;
    }
    return dp;
}

static int last_gd, last_ky;
static int JJ = 2; /* half of the contact order imposed; set by the environment variable J (2 or 3) */
static FILE *dumpf = NULL; /* if set, the solution E, the domain and the word are written there */
static int full_Wt = -1; /* if >= 0: do not stop at the first solution, use every column of weight <= full_Wt
                           and test a random combination of all solutions (mode "full") */
static int run(int n, int Dc, const uint16_t *al, const uint16_t *be, int verbose) {
    /* contact order 2 * JJ: the Taylor coefficients (r, q), r + q < 2 JJ, not both even (7 for JJ = 2) */
    int RQ[64][2], NC = 0;
    for (int r = 0; r < 2 * JJ; r++)
        for (int q = 0; r + q < 2 * JJ; q++)
            if ((r & 1) || (q & 1)) { RQ[NC][0] = r; RQ[NC][1] = q; NC++; }
    int Whi = (JJ == 2) ? (int)(3.3 * n) + 8 : 3 * JJ * n;
    int cap = 8 * Whi + 64, C = 0;
    Mono *mo = malloc(sizeof(Mono) * cap);
    for (int k = 0; Dc * k <= Whi + 1; k++)
        for (int i = 0; i + Dc * k <= Whi + 1; i++) {
            int w;
            if (k & 1) w = i + Dc * k;
            else if (i & 1) w = i - 1 + Dc * k;
            else continue;
            if (w > Whi) continue;
            mo[C].i = i; mo[C].k = k; mo[C].w = w; C++;
        }
    qsort(mo, C, sizeof(Mono), cmp_mono);
    int R = NC * n, L = R + C;
    uint16_t **basis = malloc(sizeof(uint16_t *) * C);
    int *pivot = malloc(sizeof(int) * C);
    int nb = 0, Wmin = -1, nullity = 0;
    uint16_t *v = malloc(sizeof(uint16_t) * L), *sol = NULL;
    /* powers: alpha^i and beta^k on demand through logs */
    for (int c = 0; c < C; c++) {
        if (full_Wt >= 0) { if (mo[c].w > full_Wt) break; }
        else if (Wmin >= 0 && mo[c].w > Wmin) break;
        memset(v, 0, sizeof(uint16_t) * L);
        int i = mo[c].i, k = mo[c].k;
        for (int p = 0; p < n; p++)
            for (int t = 0; t < NC; t++) {
                int r = RQ[t][0], q = RQ[t][1];
                if (binom2(i, r) && binom2(k, q))
                    v[NC * p + t] = mul(fpow(al[p], i - r), fpow(be[p], k - q));
            }
        v[R + c] = 1;
        for (int b = 0; b < nb; b++) {
            uint16_t f = v[pivot[b]];
            if (!f) continue;
            int lf = LOGT[f];
            uint16_t *bv = basis[b];
            for (int t = 0; t < L; t++)
                if (bv[t]) v[t] ^= EXPT[LOGT[bv[t]] + lf];
        }
        int pv = -1;
        for (int t = 0; t < R; t++) if (v[t]) { pv = t; break; }
        if (pv < 0) {
            if (Wmin < 0) { Wmin = mo[c].w; sol = malloc(sizeof(uint16_t) * C); memcpy(sol, v + R, sizeof(uint16_t) * C); }
            else if (full_Wt >= 0) { uint16_t r = (uint16_t)(1 + rnd() % (Q - 1)); for (int t = 0; t < C; t++) sol[t] ^= mul(r, v[R + t]); }
            nullity++;
            continue;
        }
        uint16_t iv = inv(v[pv]);
        uint16_t *nv = malloc(sizeof(uint16_t) * L);
        for (int t = 0; t < L; t++) nv[t] = mul(v[t], iv);
        basis[nb] = nv; pivot[nb] = pv; nb++;
    }
    if (Wmin < 0) { if (verbose >= 0) printf("none with W <= %d\n", full_Wt >= 0 ? full_Wt : Whi); return -1; }
    int ky = 0;
    for (int c = 0; c < C; c++) if (sol[c] && mo[c].k > ky) ky = mo[c].k;
    /* coprimality of E_Y and E_X at a point x0 outside the domain */
    int gd = -1;
    for (int tries = 0; tries < 3; tries++) {
        uint16_t x0;
        for (;;) { x0 = (uint16_t)(rnd() % Q); int in = (x0 == 0); for (int p = 0; p < n && !in; p++) in = (al[p] == x0); if (!in) break; }
        uint16_t a[64] = {0}, cc[64] = {0};
        for (int c = 0; c < C; c++) {
            if (!sol[c]) continue;
            int i = mo[c].i, k = mo[c].k;
            if (k & 1) a[k - 1] ^= mul(sol[c], fpow(x0, i));
            if (i & 1) cc[k] ^= mul(sol[c], fpow(x0, i - 1));
        }
        int g = gcd_deg(a, cc, 64);
        if (g > gd) gd = g;
    }
    last_gd = gd; last_ky = ky;
    if (verbose >= 0) printf("W_min = %d (%.4f n), solutions %d, deg_Y E = %d, gcd degree %d\n", Wmin, (double)Wmin / n, nullity, ky, gd);
    if (dumpf) {
        fprintf(dumpf, "n %d D %d W %d\n", n, Dc, Wmin);
        for (int p = 0; p < n; p++) fprintf(dumpf, "pt %d %d\n", al[p], be[p]);
        for (int c = 0; c < C; c++) if (sol[c]) fprintf(dumpf, "mono %d %d %d\n", mo[c].i, mo[c].k, sol[c]);
    }
    if (verbose > 0) {
        printf("  support of E by Y-degree (number of nonzero coefficients, largest X-degree):");
        for (int k = 0; k <= ky; k++) {
            int cnt = 0, mx = -1;
            for (int c = 0; c < C; c++) if (sol[c] && mo[c].k == k) { cnt++; if (mo[c].i > mx) mx = mo[c].i; }
            printf(" Y^%d: %d, %d;", k, cnt, mx);
        }
        printf("\n");
    }
    for (int b = 0; b < nb; b++) free(basis[b]);
    free(basis); free(pivot); free(v); free(mo); free(sol);
    return Wmin;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s [-]N word [seed]\n", argv[0]); return 1; }
    gf_init();
    int N = atoi(argv[1]), randomset = 0;
    if (N < 0) { N = -N; randomset = 1; }
    int n = 1 << N, Dc = n / 2 - 1;
    if (argc > 3) rs ^= (uint64_t)atol(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (argc > 4) dumpf = fopen(argv[4], "w");
    for (int t = 0; t < 20; t++) rnd();
    uint16_t *al = malloc(sizeof(uint16_t) * n), *be = malloc(sizeof(uint16_t) * n);
    if (randomset) {
        char *used = calloc(Q, 1);
        for (int p = 0; p < n; ) { uint16_t x = (uint16_t)(rnd() % Q); if (x && !used[x]) { used[x] = 1; al[p++] = x; } }
        free(used);
    } else {
        for (;;) {
            al[0] = 0;
            int ok = 1;
            for (int d = 0; d < N && ok; d++) {
                uint16_t bvec = (uint16_t)(rnd() % Q);
                for (int t = 0; t < (1 << d); t++) if (al[t] == bvec) ok = 0;
                for (int t = 0; t < (1 << d); t++) al[(1 << d) + t] = al[t] ^ bvec;
            }
            if (ok) break;
        }
    }
    printf("n = %d, degree <= %d, %s domain in GF(2^16)\n", n, Dc, randomset ? "random" : "subspace");
    if (getenv("J")) { JJ = atoi(getenv("J")); printf("contact order %d\n", 2 * JJ); }
    if (getenv("FULL")) { full_Wt = 11 * n / 4 - 4; printf("FULL: whole solution space with W <= %d, gcd test on a random combination\n", full_Wt); }
    if (!strcmp(argv[2], "sweep")) {
        for (int e = (int)(0.66 * n); e <= (int)(0.80 * n); e++) {
            for (int p = 0; p < n; p++) be[p] = fpow(al[p], e);
            printf("  X^%d: ", e);
            run(n, Dc, al, be, 0);
            fflush(stdout);
        }
    } else if (!strcmp(argv[2], "bin")) {
        int thr = 11 * n / 4 - 2, cnt = 0, tot = 0, hist_irred_min = 1 << 30;
        for (int e = n / 2 + 1; e < n; e++)
            for (int f = n / 2; f < e; f++)
                for (int cc = 0; cc < 2; cc++) {
                    uint16_t c = cc ? (uint16_t)(1 + rnd() % (Q - 1)) : 1;
                    for (int p = 0; p < n; p++) be[p] = fpow(al[p], e) ^ mul(c, fpow(al[p], f));
                    int W = run(n, Dc, al, be, -1);
                    tot++;
                    if (W < 0) continue;
                    if (last_gd == 0 && W < hist_irred_min) hist_irred_min = W;
                    if (last_gd == 0 && W < thr) {
                        cnt++;
                        printf("  X^%d + %s X^%d: W_min = %d (%.4f n), deg_Y E = %d\n", e, cc ? "c" : "1", f, W, (double)W / n, last_ky);
                    }
                }
        printf("  %d binomial words; %d with a coprime solution below 11n/4 - 2 = %d; smallest coprime W_min = %d (0 = none)\n", tot, cnt, thr, hist_irred_min == (1 << 30) ? 0 : hist_irred_min);
    } else if (!strcmp(argv[2], "full")) {
        /* every monomial word X^e, n/2 <= e < n: all solutions with W <= 11n/4 - 4, random combination */
        full_Wt = 11 * n / 4 - 4;
        int cop = 0;
        for (int e = n / 2; e < n; e++) {
            for (int p = 0; p < n; p++) be[p] = fpow(al[p], e);
            printf("  X^%d, all solutions with W <= %d: ", e, full_Wt);
            int W = run(n, Dc, al, be, 0);
            if (W >= 0 && last_gd == 0) cop++;
        }
        printf("  words with a coprime random combination: %d\n", cop);
    } else if (!strcmp(argv[2], "tri")) {
        int thr = 11 * n / 4 - 2, cnt = 0, tot = 0, best = 1 << 30;
        for (int e = n / 2 + 2; e < n; e++)
            for (int f = n / 2 + 1; f < e; f++)
                for (int g = n / 2; g < f; g++) {
                    for (int p = 0; p < n; p++) be[p] = fpow(al[p], e) ^ fpow(al[p], f) ^ fpow(al[p], g);
                    int W = run(n, Dc, al, be, -1);
                    tot++;
                    if (W < 0) continue;
                    if (last_gd == 0 && W < best) best = W;
                    if (last_gd == 0 && W < thr) { cnt++; printf("  X^%d + X^%d + X^%d: W_min = %d (%.4f n), deg_Y E = %d\n", e, f, g, W, (double)W / n, last_ky); }
                }
        printf("  %d trinomial words; %d with a coprime solution below 11n/4 - 2 = %d; smallest coprime W_min = %d (0 = none)\n", tot, cnt, thr, best == (1 << 30) ? 0 : best);
    } else if (!strcmp(argv[2], "inv")) {
        /* al[0] = 0 for a subspace domain; use the other n - 1 points */
        int best = 1 << 30, bj = 0;
        for (int j = 1; j < n; j++) {
            for (int p = 1; p < n; p++) be[p] = inv(fpow(al[p], j));
            int W = run(n - 1, Dc, al + 1, be + 1, -1);
            if (W >= 0 && last_gd == 0) {
                printf("  alpha^(-%d) on D minus 0: W_min = %d (%.4f n), deg_Y E = %d\n", j, W, (double)W / n, last_ky);
                if (W < best) { best = W; bj = j; }
            }
        }
        if (best == (1 << 30)) printf("  no word with a coprime solution (11n/4 - 2 = %d)\n", 11 * n / 4 - 2);
        else printf("  smallest coprime W_min = %d at j = %d (11n/4 - 2 = %d)\n", best, bj, 11 * n / 4 - 2);
    } else if (!strcmp(argv[2], "lin")) {
        /* words X^e * l(X), l the subspace polynomial of the span of the first d basis vectors (2^d points al[0..2^d-1]) */
        int thr = 11 * n / 4 - 2;
        for (int d = 1; d < N; d++)
            for (int e = 0; e + (1 << d) < n; e++) {
                if (e + (1 << d) <= Dc) continue;
                for (int p = 0; p < n; p++) {
                    uint16_t v = 1;
                    for (int t = 0; t < (1 << d); t++) v = mul(v, al[p] ^ al[t]);
                    be[p] = mul(v, fpow(al[p], e));
                }
                int W = run(n, Dc, al, be, -1);
                if (W >= 0 && last_gd == 0 && W <= thr)
                    printf("  X^%d L_%d: W_min = %d (%.4f n), deg_Y E = %d\n", e, d, W, (double)W / n, last_ky);
            }
        printf("  done (threshold 11n/4 - 2 = %d)\n", thr);
    } else if (argv[2][0] == 'r') {
        for (int p = 0; p < n; p++) be[p] = (uint16_t)(rnd() % Q);
        printf("  random word: ");
        run(n, Dc, al, be, 1);
    } else {
        int e = atoi(argv[2]);
        for (int p = 0; p < n; p++) be[p] = fpow(al[p], e);
        printf("  X^%d: ", e);
        run(n, Dc, al, be, 1);
    }
    return 0;
}
