// Note 76: exhaustive search for the largest list of the generic [16,8] tree code at agreement >= 10 (error weight <= 6),
// by the secant form (76_sec.h): a list is a point s of P^7 and the minimal supports E, |E| <= 6, with s in span(g_E).
// Completeness argument (Section 3 of the note): give every member of a list a 6-set containing its support; any two of
// these 6-sets meet in at most 3 leaves. Take the pair (E1, E2) of smallest orbit rank under the tree automorphisms
// (order 2^15) and the exchange; by symmetry it is the orbit representative, V12 = span(E1) cap span(E2) has dimension 4
// and every other member E is "allowed": rank(E1,E), rank(E2,E) >= rank(E1,E2). E acts on V12 by a 2 x 4 matrix P_E.
//   Case A: some other member has rank P = 2 (a line of P(V12)); the others contain that line or meet it in the point s.
//           Lines are found by the Pluecker test; two lines through a common g_x, x in E1 cap E2, meet nowhere else.
//   Case B: all other members have rank P = 1 (planes of P(V12)): points on one, two or three planes.
// Every candidate point whose estimated list reaches the threshold is recomputed exactly (distinct minimal supports).
// Usage: 76_n16 seed part nparts threshold [print_threshold]      cc -O2 -o 76_bin/76_n16 76_n16.c
#include "76_sec.h"
#define MAXL 512
static sec_t S;
static int cmp_u32(const void *a, const void *b) { uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? -1 : x > y; }
static uint32_t canon_lab(const uint8_t *lab) {
    uint32_t c[16]; int len = 2;
    for (int i = 0; i < 16; i++) c[i] = lab[i];
    for (int cnt = 16; cnt > 1; cnt >>= 1, len <<= 1)
        for (int i = 0; i < cnt; i += 2) { uint32_t a = c[i], b = c[i + 1]; if (a > b) { uint32_t t = a; a = b; b = t; } c[i / 2] = (a << len) | b; }
    return c[0];
}
static uint32_t canon_pair(uint32_t A, uint32_t B) {
    uint8_t l1[16], l2[16];
    for (int x = 0; x < 16; x++) { int a = (A >> x) & 1, b = (B >> x) & 1; l1[x] = (uint8_t)(a | (b << 1)); l2[x] = (uint8_t)(b | (a << 1)); }
    uint32_t c1 = canon_lab(l1), c2 = canon_lab(l2);
    return c1 < c2 ? c1 : c2;
}
// orbit table: canonical code -> rank
#define TCAP (1u << 20)
static uint32_t *otab; static int32_t *orank;
static int orbit_rank(uint32_t c, int insert, int next) {
    size_t slot = (c * 2654435761u) & (TCAP - 1);
    while (orank[slot] >= 0) { if (otab[slot] == c) return orank[slot]; slot = (slot + 1) & (TCAP - 1); }
    if (insert) { otab[slot] = c; orank[slot] = next; }
    return -1;
}
typedef struct { fe th; int inf; int w; } hit_t;
static int cmp_hit(const void *a, const void *b) { const hit_t *x = a, *y = b; if (x->inf != y->inf) return x->inf - y->inf; return x->th < y->th ? -1 : x->th > y->th; }
static long hist_exact[MAXL]; static int best_exact = 0, print_threshold = 1000;
#define SEENBITS 24
static uint64_t *seen;
static int seen_add(uint64_t h) {
    if (!h) h = 1; uint64_t slot = h & ((1u << SEENBITS) - 1);
    while (seen[slot]) { if (seen[slot] == h) return 0; slot = (slot + 1) & ((1u << SEENBITS) - 1); }
    seen[slot] = h; return 1;
}
static long ncalls = 0, nnew = 0;
static void exact_list(const fe *s, int est) {
    int f = 0; while (f < S.k && !s[f]) f++; if (f == S.k) return;
    fe iv = gf_inv(s[f]); uint64_t hp = 0x9E3779B97F4A7C15ull;
    for (int t = f; t < S.k; t++) { hp ^= gf_mul(iv, s[t]) + 0x632BE59BD9B4E019ull * (uint64_t)(t + 1); hp *= 0xD6E8FEB86659FD93ull; hp ^= hp >> 32; }
    ncalls++; if (!seen_add(hp)) return; nnew++;
    uint32_t sup[MAXL]; int cnt = sec_list(&S, s, sup, MAXL);
    qsort(sup, cnt, sizeof(uint32_t), cmp_u32);
    hist_exact[cnt]++;
    int rec = cnt > best_exact; if (rec) best_exact = cnt;
    if (rec || cnt >= print_threshold) {
        printf("LIST %d (est %d):", cnt, est);
        for (int a = 0; a < cnt; a++) printf(" %04x", sup[a]);
        printf("\n"); fflush(stdout);
    }
}
static void point_of(const fe *u, const fe *B, fe *s) { for (int t = 0; t < 8; t++) { s[t] = 0; for (int j = 0; j < 4; j++) s[t] ^= gf_mul(u[j], B[j * 8 + t]); } }
int main(int argc, char **argv) {
    uint64_t seed = argc > 1 ? strtoull(argv[1], 0, 10) : 1; int part = argc > 2 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    int threshold = argc > 4 ? atoi(argv[4]) : 5; if (argc > 5) print_threshold = atoi(argv[5]);
    sec_init(&S, 3, 6, seed);
    int k = S.k, ns = S.nset;
    seen = (uint64_t *)calloc(1u << SEENBITS, sizeof(uint64_t));
    otab = (uint32_t *)calloc(TCAP, sizeof(uint32_t)); orank = (int32_t *)malloc(sizeof(int32_t) * TCAP); memset(orank, 0xff, sizeof(int32_t) * TCAP);
    size_t cap = 1 << 14, nrep = 0; uint64_t *reps = (uint64_t *)malloc(sizeof(uint64_t) * cap);
    for (int i = 0; i < ns; i++) for (int j = i + 1; j < ns; j++) {
        if (__builtin_popcount(S.mask[i] & S.mask[j]) > 3) continue;
        uint32_t c = canon_pair(S.mask[i], S.mask[j]);
        if (orbit_rank(c, 1, (int)nrep) >= 0) continue;
        if (nrep == cap) { cap *= 2; reps = (uint64_t *)realloc(reps, sizeof(uint64_t) * cap); }
        reps[nrep++] = ((uint64_t)i << 32) | (uint64_t)j;
    }
    fprintf(stderr, "pair orbits: %zu\n", nrep);
    fe *P = (fe *)malloc(sizeof(fe) * (size_t)ns * 8), *pl = (fe *)malloc(sizeof(fe) * (size_t)ns * 6);
    int *al = (int *)malloc(sizeof(int) * ns), *r1 = (int *)malloc(sizeof(int) * ns), *crep = (int *)malloc(sizeof(int) * ns), *csize = (int *)malloc(sizeof(int) * ns);
    hit_t *hits = (hit_t *)malloc(sizeof(hit_t) * (ns + 8));
    uint64_t *chash = (uint64_t *)malloc(sizeof(uint64_t) * (1 << 15)); int *cidx = (int *)malloc(sizeof(int) * (1 << 15));
    long tot_tests = 0, tot_hits = 0, tot_groups = 0, tot_allowed = 0, tot_r1 = 0, skippedB = 0; int max_r1 = 0, max_hyp = 0;
    for (size_t rp = 0; rp < nrep; rp++) {
        if ((int)(rp % nparts) != part) continue;
        int i1 = (int)(reps[rp] >> 32), i2 = (int)(reps[rp] & 0xffffffffu), id[2] = {i1, i2};
        uint32_t m1 = S.mask[i1], m2 = S.mask[i2], common = m1 & m2;
        fe B[8 * 8]; int d = sec_meet(&S, id, 2, B);
        if (d != 4) { fprintf(stderr, "pair meet of dimension %d\n", d); continue; }
        int na = 0, nr1 = 0, n0 = 0, ncl = 0;
        memset(chash, 0, sizeof(uint64_t) * (1 << 15));
        for (int E = 0; E < ns; E++) {
            if (E == i1 || E == i2) continue;
            uint32_t m = S.mask[E];
            if (__builtin_popcount(m & m1) > 3 || __builtin_popcount(m & m2) > 3) continue;
            if (orbit_rank(canon_pair(m1, m), 0, 0) < (int)rp || orbit_rank(canon_pair(m2, m), 0, 0) < (int)rp) continue;
            fe *p = P + (size_t)E * 8; const fe *nu = S.nrm + (size_t)E * 2 * k;
            for (int c = 0; c < 2; c++) for (int j = 0; j < 4; j++) p[c * 4 + j] = dot(nu + c * k, B + j * k, k);
            fe *q = pl + (size_t)E * 6; int t = 0, piv = -1;
            for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++) { q[t] = gf_mul(p[a], p[4 + b]) ^ gf_mul(p[b], p[4 + a]); if (piv < 0 && q[t]) piv = t; t++; }
            if (piv < 0) { int any = 0; for (int a = 0; a < 8; a++) any |= p[a] != 0; if (any) r1[nr1++] = E; else n0++; continue; }
            fe iv = gf_inv(q[piv]); uint64_t h = 0x243F6A8885A308D3ull + (uint64_t)piv;
            for (int a = 0; a < 6; a++) { q[a] = gf_mul(q[a], iv); h ^= q[a] + 0x9E3779B97F4A7C15ull * (uint64_t)(a + 1); h *= 0xD6E8FEB86659FD93ull; h ^= h >> 29; }
            if (!h) h = 1;
            size_t slot = h & ((1 << 15) - 1);
            while (chash[slot] && chash[slot] != h) slot = (slot + 1) & ((1 << 15) - 1);
            if (chash[slot]) csize[cidx[slot]]++;
            else { chash[slot] = h; cidx[slot] = ncl; crep[ncl] = E; csize[ncl] = 1; ncl++; }
            al[na++] = E;
        }
        tot_allowed += na + nr1; tot_r1 += nr1; if (nr1 > max_r1) max_r1 = nr1;
        if (getenv("PROGRESS")) fprintf(stderr, "pair %zu (%04x %04x): allowed rank-2 %d in %d lines, rank-1 %d, rank-0 %d, exact calls %ld new %ld best %d\n", rp, m1, m2, na, ncl, nr1, n0, ncalls, nnew, best_exact);
        // Case A
        for (int c3 = 0; c3 < ncl; c3++) {
            int E3 = crep[c3]; const fe *q3 = pl + (size_t)E3 * 6; uint32_t m3c = S.mask[E3] & common; int nh = 0, linew = 0;
            fe M[8], U[16]; memcpy(M, P + (size_t)E3 * 8, sizeof(M));
            if (gf_kernel(M, 2, 4, U) != 2) { fprintf(stderr, "kernel\n"); continue; }
            for (int c4 = c3 + 1; c4 < ncl; c4++) {
                int E4 = crep[c4]; if (S.mask[E4] & m3c) continue;
                const fe *q4 = pl + (size_t)E4 * 6; // pairs 01,02,03,12,13,23 against their complements 23,13,12,03,02,01
                fe t = gf_mul(q3[0], q4[5]) ^ gf_mul(q3[1], q4[4]) ^ gf_mul(q3[2], q4[3]) ^ gf_mul(q3[3], q4[2]) ^ gf_mul(q3[4], q4[1]) ^ gf_mul(q3[5], q4[0]);
                tot_tests++;
                if (t) continue;
                const fe *p4 = P + (size_t)E4 * 8; fe a = dot(p4, U, 4), b = dot(p4, U + 4, 4);
                if (!(a | b)) { a = dot(p4 + 4, U, 4); b = dot(p4 + 4, U + 4, 4); }
                if (!(a | b)) { fprintf(stderr, "distinct classes, same line?\n"); continue; }
                hits[nh].w = csize[c4]; hits[nh].inf = a == 0; hits[nh].th = a ? gf_mul(b, gf_inv(a)) : 0; nh++;
            }
            for (int z = 0; z < nr1; z++) {
                const fe *p4 = P + (size_t)r1[z] * 8; fe a = dot(p4, U, 4), b = dot(p4, U + 4, 4);
                if (!(a | b)) { a = dot(p4 + 4, U, 4); b = dot(p4 + 4, U + 4, 4); }
                if (!(a | b)) { linew++; continue; }
                hits[nh].w = 1; hits[nh].inf = a == 0; hits[nh].th = a ? gf_mul(b, gf_inv(a)) : 0; nh++;
            }
            tot_hits += nh;
            int base = 2 + csize[c3] + linew + n0;
            if (base >= threshold) { fe u[4], s[8]; fe c1 = gf_rand_nz(), c2 = gf_rand_nz(); for (int j = 0; j < 4; j++) u[j] = gf_mul(c1, U[j]) ^ gf_mul(c2, U[4 + j]); point_of(u, B, s); exact_list(s, base); }
            if (!nh) continue;
            qsort(hits, nh, sizeof(hit_t), cmp_hit);
            for (int a = 0; a < nh;) {
                int b = a, w = 0; while (b < nh && hits[b].inf == hits[a].inf && hits[b].th == hits[a].th) { w += hits[b].w; b++; }
                int est = base + w; tot_groups++;
                if (est >= threshold) { // a x + b y = 0 on u = x U1 + y U2: (x, y) = (th, 1), or (1, 0)
                    fe u[4], s[8];
                    for (int j = 0; j < 4; j++) u[j] = hits[a].inf ? U[j] : (gf_mul(hits[a].th, U[j]) ^ U[4 + j]);
                    point_of(u, B, s); exact_list(s, est);
                }
                a = b;
            }
        }
        // Case B: distinct planes h (rows of the rank-1 matrices), with multiplicities
        if (nr1 >= 1) {
            fe *H = (fe *)malloc(sizeof(fe) * 4 * nr1); int *hw = (int *)calloc(nr1, sizeof(int)), nhy = 0;
            for (int z = 0; z < nr1; z++) {
                const fe *p = P + (size_t)r1[z] * 8; const fe *row = (p[0] | p[1] | p[2] | p[3]) ? p : p + 4; fe h[4]; int piv = 0; while (!row[piv]) piv++;
                fe iv = gf_inv(row[piv]); for (int j = 0; j < 4; j++) h[j] = gf_mul(row[j], iv);
                int f = -1; for (int y = 0; y < nhy; y++) if (!memcmp(H + 4 * y, h, sizeof(h))) { f = y; break; }
                if (f < 0) { f = nhy++; memcpy(H + 4 * f, h, sizeof(h)); }
                hw[f]++;
            }
            if (nhy > max_hyp) max_hyp = nhy;
            if (nhy > 120) { skippedB++; fprintf(stderr, "pair %zu: %d distinct planes, case B skipped\n", rp, nhy); }
            else for (int a = 0; a < nhy; a++) for (int b = a; b < nhy; b++) for (int c = b; c < nhy; c++) {
                if (a == b && b != c) continue; // (a,a,a): one plane; (a,b,b): two planes; (a,b,c): three planes
                fe M[12], U[16]; int rows = a == c ? 1 : b == c ? 2 : 3;
                memcpy(M, H + 4 * a, 32); memcpy(M + 4, H + 4 * b, 32); memcpy(M + 8, H + 4 * c, 32);
                int du = gf_kernel(M, rows, 4, U); if (du < 1) continue;
                if (rows == 3 && du > 1) continue; // collinear planes: found as (a,b,b)
                fe u[4] = {0, 0, 0, 0}, s[8];
                for (int z = 0; z < du; z++) { fe co = du == 1 ? 1 : gf_rand_nz(); for (int j = 0; j < 4; j++) u[j] ^= gf_mul(co, U[z * 4 + j]); }
                int est = 2 + n0; for (int y = 0; y < nhy; y++) if (!dot(H + 4 * y, u, 4)) est += hw[y];
                if (est >= threshold) { point_of(u, B, s); exact_list(s, est); }
            }
            free(H); free(hw);
        }
        // the generic point of V12 (lists of two members and whatever contains V12)
        if (2 + n0 >= threshold) { fe u[4], s[8]; for (int j = 0; j < 4; j++) u[j] = gf_rand_nz(); point_of(u, B, s); exact_list(s, 2 + n0); }
    }
    printf("# seed %llu part %d/%d threshold %d: pair orbits %zu, allowed sets %ld (rank-1: %ld, most %d for one pair, most distinct planes %d, case B skipped %ld), Pluecker tests %ld, hits %ld, groups %ld, exact calls %ld, new points %ld\n",
           (unsigned long long)seed, part, nparts, threshold, nrep, tot_allowed, tot_r1, max_r1, max_hyp, skippedB, tot_tests, tot_hits, tot_groups, ncalls, nnew);
    for (int c = 0; c < MAXL; c++) if (hist_exact[c]) printf("exact %d: %ld\n", c, hist_exact[c]);
    printf("best exact: %d\n", best_exact);
    return 0;
}
