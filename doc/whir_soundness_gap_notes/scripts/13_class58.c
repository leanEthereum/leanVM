// Researcher 13. Step 3 of note 04, section 6: the fibres of e_{n/8} on the full common-top class at 5n/8, rate 1/2.
// For a subspace U of D with |U| = n/8, the word L_U^5 agrees on 5n/8 points with one polynomial of degree <= n/2
// for each set S = L_W^{-1}(Y), W a hyperplane of U, Y a 10-subset of the 16 labels L_W(D) with sum eta_W
// (note 02, Theorem 5: 56n - 392 sets). The members that are genuine codewords for one word (degree < n/2) are the
// ones that also share e_{n/8}, and e_{n/8}(S) = e_2(Y) (report 13, Lemma 2.1). In coordinates (eta; beta_1..beta_3),
// beta_i = L_W(v_i) = eta t_i with t_i^2 + t_i = L_U(v_i) alpha_W; alpha_W = eta_W^-2 and t_i are additive in the
// functional that defines W (L_W / eta_W is the linearized polynomial of that functional), e_2(Y) = eta^2 Q_c(t) where c(Y) in F_2^10 is the formal class of Y. Formal classes have at
// most 7 sets. The program lists every coincidence of e_2 between different formal classes: these are the
// non-formal (domain-specific) members of the genuine list at 5n/8 that this class contains.
// With a second field the key is the pair of values on the same domain (power shape reduced modulo both moduli):
// what collides then is an identity of F_2(x), up to 2^-(m+m2) per pair.
// usage: 13_class58 N shape U m r [m2 r2] [-n count] [-p passes] [-check] [-q]
//   shape: power | random:<seed>      U: low | high | random:<seed>  (with -n, seeds seed .. seed+count-1)
// build: cc -O2 -mcpu=native -o 13_class58 13_class58.c
#include "13_gf.h"
#include <math.h>

static int N, nf = 1, passes = 1, quiet = 0;
static gf_t F[2];
static u64 basis[2][64];
// formal classes of the label sets
static int ncls_ni, ncls_inv, cls_ni_mask[512], cls_ni_mult[512], cls_inv_mask[64], cls_inv_mult[64];
static u32 ysets[512]; static int ny, yinv[512], ymask[512];

static int cmask_of(u32 Y) {
  int n1[4] = {0}, n2[4][4] = {{0}};
  for (int y = 0; y < 16; y++) if (Y >> y & 1)
    for (int i = 0; i < 4; i++) if (y >> i & 1) { n1[i]++; for (int j = i + 1; j < 4; j++) if (y >> j & 1) n2[i][j]++; }
  int mask = 0, bit = 0;
  for (int i = 0; i < 4; i++) for (int j = i; j < 4; j++, bit++) {
    int c = i == j ? (n1[i] * (n1[i] - 1) / 2) & 1 : (n1[i] * n1[j] - n2[i][j]) & 1;
    mask |= c << bit;
  }
  return mask; // bit order: 00 01 02 03 11 12 13 22 23 33
}
static void build_classes(void) {
  ny = 0;
  for (u32 Y = 0; Y < 65536; Y++) if (__builtin_popcount(Y) == 10) {
    int x = 0; for (int y = 0; y < 16; y++) if (Y >> y & 1) x ^= y;
    if (x != 1) continue;
    int invar = 1; for (int y = 0; y < 16; y++) if ((Y >> y & 1) != (Y >> (y ^ 1) & 1)) invar = 0;
    ysets[ny] = Y; yinv[ny] = invar; ymask[ny] = cmask_of(Y); ny++;
  }
  ncls_ni = ncls_inv = 0;
  for (int i = 0; i < ny; i++) {
    int *masks = yinv[i] ? cls_inv_mask : cls_ni_mask, *mult = yinv[i] ? cls_inv_mult : cls_ni_mult, *n = yinv[i] ? &ncls_inv : &ncls_ni, j;
    for (j = 0; j < *n; j++) if (masks[j] == ymask[i]) break;
    if (j == *n) { masks[j] = ymask[i]; mult[j] = 0; (*n)++; }
    mult[j]++;
  }
}
typedef struct { u64 alpha[64], lam[4], tk[64][4]; } usetup;
static u32 ucomb[64]; // U basis and v_1..v_3 as combinations of the domain basis
static void setup_u(int f, usetup *s) {
  const gf_t *G = &F[f];
  u64 u[64], v[3]; int d = N - 3;
  for (int i = 0; i < N; i++) { u64 z = 0; for (int j = 0; j < N; j++) if (ucomb[i] >> j & 1) z ^= basis[f][j]; if (i < d) u[i] = z; else v[i - d] = z; }
  for (int i = 0; i < 3; i++) s->lam[i + 1] = v[i];
  gf_subspace_eval(G, u, d, &s->lam[1], 3);
  for (int k = 0; k < d; k++) {
    u64 h[64], z[4] = {u[k], v[0], v[1], v[2]}; int e = 0;
    for (int j = 0; j < d; j++) if (j != k) h[e++] = u[j];
    gf_subspace_eval(G, h, e, z, 4);
    u64 ie = gf_inv(G, z[0]);
    s->alpha[k] = gf_sqr(G, ie);
    for (int i = 1; i <= 3; i++) s->tk[k][i] = gf_mul(G, z[i], ie);
  }
}
// the ten monomials of (1, t1, t2, t3), in the bit order of cmask_of
static inline void monomials(const gf_t *G, const u64 *t, u64 *M) {
  M[0] = 1; M[1] = t[1]; M[2] = t[2]; M[3] = t[3];
  M[4] = gf_sqr(G, t[1]); M[5] = gf_mul(G, t[1], t[2]); M[6] = gf_mul(G, t[1], t[3]);
  M[7] = gf_sqr(G, t[2]); M[8] = gf_mul(G, t[2], t[3]); M[9] = gf_sqr(G, t[3]);
}
static inline u64 qeval(const u64 *M, int mask) { u64 q = 0; while (mask) { q ^= M[__builtin_ctz(mask)]; mask &= mask - 1; } return q; }
static inline u64 mix(u64 a, u64 b) {
  u64 h = a * 0x9e3779b97f4a7c15ull; h ^= h >> 32; h += b * 0xc2b2ae3d27d4eb4full; h ^= h >> 29;
  return h * 0xff51afd7ed558ccdull;
}
static usetup US[2];
// keys of all classes for the hyperplane phi; returns 0 if a consistency check fails
static int keys_of(u32 phi, const u64 *alpha, const u64 (*tt)[4], u64 *kni, u64 *kinv) {
  u64 k1[2][512], k2[2][64];
  for (int f = 0; f < nf; f++) {
    const gf_t *G = &F[f];
    u64 a = alpha[f], t[4], M[10], ia = gf_inv(G, a);
    for (int i = 1; i <= 3; i++) {
      t[i] = tt[f][i];
      if ((gf_sqr(G, t[i]) ^ t[i]) != gf_mul(G, US[f].lam[i], a)) { fprintf(stderr, "label check failed for phi=%x\n", phi); return 0; }
    }
    monomials(G, t, M);
    for (int j = 0; j < ncls_ni; j++) k1[f][j] = gf_mul(G, qeval(M, cls_ni_mask[j]), ia);
    for (int j = 0; j < ncls_inv; j++) k2[f][j] = gf_mul(G, qeval(M, cls_inv_mask[j]), ia);
  }
  for (int j = 0; j < ncls_ni; j++) kni[j] = nf == 2 ? mix(k1[0][j], k1[1][j]) : k1[0][j];
  for (int j = 0; j < ncls_inv; j++) kinv[j] = nf == 2 ? mix(k2[0][j], k2[1][j]) : k2[0][j];
  return 1;
}

// brute-force check of the lemma e_{n/8}(S) = e_2(Y) and of the common top, for small N
static void check(void) {
  const gf_t *G = &F[0]; int n = 1 << N, d = N - 3, g = n / 8, bad = 0, tested = 0;
  u64 u[64], v[3];
  for (int i = 0; i < N; i++) { u64 z = 0; for (int j = 0; j < N; j++) if (ucomb[i] >> j & 1) z ^= basis[0][j]; if (i < d) u[i] = z; else v[i - d] = z; }
  u64 *ref = 0;
  for (int trial = 0; trial < 6; trial++) {
    u32 phi = 1 + (u32)(rnd64() % ((1u << d) - 1));
    // W = ker phi inside U: basis from the u_k
    int p = __builtin_ctz(phi); u64 w[64]; int e = 0;
    for (int k = 0; k < d; k++) if (k != p) w[e++] = (phi >> k & 1) ? u[k] ^ u[p] : u[k];
    u64 lab[4] = {u[p], v[0], v[1], v[2]};
    gf_subspace_eval(G, w, e, lab, 4);
    u64 alpha = 0; for (int k = 0; k < d; k++) if (phi >> k & 1) alpha ^= US[0].alpha[k];
    if (gf_mul(G, gf_sqr(G, lab[0]), alpha) != 1) { printf("check: alpha additivity FAILED\n"); bad++; }
    // labels of all points of D in coordinates: x = sum over the combination basis
    u64 *pt = malloc(n * sizeof(u64)); int *lb = malloc(n * sizeof(int));
    // coordinates of x in the basis (w_0..w_{e-1}, u_p, v_1, v_2, v_3)
    u64 full[64]; for (int i = 0; i < e; i++) full[i] = w[i]; full[e] = u[p]; full[e + 1] = v[0]; full[e + 2] = v[1]; full[e + 3] = v[2];
    for (int x = 0; x < n; x++) { u64 z = 0; for (int j = 0; j < N; j++) if (x >> j & 1) z ^= full[j]; pt[x] = z; lb[x] = x >> e; }
    for (int s = 0; s < 4; s++) {
      int yi = (int)(rnd64() % ny); u32 Y = ysets[yi];
      u64 *E = calloc(g + 1, sizeof(u64)); E[0] = 1; int T = 0;
      for (int x = 0; x < n; x++) if (Y >> lb[x] & 1) { T++; for (int j = g; j >= 1; j--) E[j] ^= gf_mul(G, E[j - 1], pt[x]); }
      // e_2(Y) from the actual labels
      u64 e2 = 0;
      for (int y = 0; y < 16; y++) if (Y >> y & 1) for (int z = y + 1; z < 16; z++) if (Y >> z & 1) {
        u64 a = 0, b = 0; for (int i = 0; i < 4; i++) { if (y >> i & 1) a ^= lab[i]; if (z >> i & 1) b ^= lab[i]; }
        e2 ^= gf_mul(G, a, b);
      }
      // the same through the class mask and the Artin-Schreier labels of the main loop
      u64 t[4], M[10]; for (int i = 1; i <= 3; i++) t[i] = gf_mul(G, lab[i], gf_inv(G, lab[0]));
      monomials(G, t, M);
      u64 e2b = gf_mul(G, qeval(M, ymask[yi]), gf_sqr(G, lab[0]));
      if (!ref) { ref = malloc(g * sizeof(u64)); memcpy(ref, E, g * sizeof(u64)); }
      int ok = T == 5 * n / 8 && E[g] == e2 && e2 == e2b && !memcmp(ref, E, g * sizeof(u64));
      tested++; if (!ok) bad++;
      free(E);
    }
    free(pt); free(lb);
  }
  printf("check N=%d: %d sets, e_1..e_{n/8-1} common and e_{n/8}(S) = e_2(Y) = eta^2 Q_c(t): %s\n", N, tested, bad ? "FAILED" : "ok");
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: N shape U m r [m2 r2] [-n count] [-p passes] [-check] [-q]\n"); return 1; }
  N = atoi(argv[1]); const char *shape = argv[2], *utype = argv[3];
  gf_init(&F[0], atoi(argv[4]), strtoull(argv[5], 0, 0));
  int ai = 6, count = 1, docheck = 0;
  if (ai + 1 < argc && argv[ai][0] != '-') { gf_init(&F[1], atoi(argv[ai]), strtoull(argv[ai + 1], 0, 0)); nf = 2; ai += 2; }
  for (; ai < argc; ai++) {
    if (!strcmp(argv[ai], "-n")) count = atoi(argv[++ai]); else if (!strcmp(argv[ai], "-p")) passes = atoi(argv[++ai]);
    else if (!strcmp(argv[ai], "-check")) docheck = 1; else if (!strcmp(argv[ai], "-q")) quiet = 1;
  }
  build_classes();
  int maxformal = 0; for (int j = 0; j < ncls_ni; j++) if (cls_ni_mult[j] > maxformal) maxformal = cls_ni_mult[j];
  for (int j = 0; j < ncls_inv; j++) if (cls_inv_mult[j] > maxformal) maxformal = cls_inv_mult[j];
  for (int f = 0; f < nf; f++) {
    if (!strncmp(shape, "random", 6)) {
      rng_state = strtoull(shape + 7, 0, 10) * 0x2545F4914F6CDD1Dull + 77 * f + 1;
      for (;;) {
        for (int i = 0; i < N; i++) basis[f][i] = rnd64() & F[f].mask;
        u64 e[64]; int rk = 0; memset(e, 0, sizeof e);
        for (int i = 0; i < N; i++) { u64 v = basis[f][i]; for (int b = 63; b >= 0 && v; b--) if (v >> b & 1) { if (e[b]) v ^= e[b]; else { e[b] = v; rk++; break; } } }
        if (rk == N) break;
      }
    } else for (int i = 0; i < N; i++) basis[f][i] = 1ull << i;
  }
  int d = N - 3; size_t nphi = ((size_t)1 << d) - 1;
  double bits = nf == 2 ? F[0].m + F[1].m : F[0].m;
  printf("N=%d shape=%s m=%d r=0x%llx", N, shape, F[0].m, (unsigned long long)F[0].r);
  if (nf == 2) printf(" m2=%d r2=0x%llx", F[1].m, (unsigned long long)F[1].r);
  int ninv = 0, mh[16] = {0}; for (int i = 0; i < ny; i++) ninv += yinv[i];
  for (int j = 0; j < ncls_ni; j++) mh[cls_ni_mult[j]]++;
  for (int j = 0; j < ncls_inv; j++) mh[cls_inv_mult[j]]++;
  printf(": %d label sets (%d invariant under U), formal classes %d + %d, sizes", ny, ninv, ncls_ni, ncls_inv);
  for (int c = 1; c < 16; c++) if (mh[c]) printf(" %d:%d", c, mh[c]);
  // masks for which Q_c(t) / alpha does not depend on W (Proposition 4.1 of the report): c_00 = 0, c_ij = 0 for
  // 1 <= i < j, c_0i = c_ii. They must be exactly the classes of the U-invariant sets.
  int deg_ni = 0, deg_inv = 0;
  for (int j = 0; j < ncls_ni + ncls_inv; j++) {
    int mk = j < ncls_ni ? cls_ni_mask[j] : cls_inv_mask[j - ncls_ni];
    int dg = !(mk & 1) && !(mk >> 5 & 1) && !(mk >> 6 & 1) && !(mk >> 8 & 1) && (mk >> 1 & 1) == (mk >> 4 & 1) && (mk >> 2 & 1) == (mk >> 7 & 1) && (mk >> 3 & 1) == (mk >> 9 & 1);
    if (dg) { if (j < ncls_ni) deg_ni++; else deg_inv++; }
  }
  printf("; W-independent masks: %d of the invariant classes, %d of the others\n", deg_inv, deg_ni);
  double tot_pairs = 0, tot_expect = 0; int worst = maxformal; size_t fib[64]; memset(fib, 0, sizeof fib);
  u64 seed0 = !strncmp(utype, "random", 6) ? strtoull(utype + 7, 0, 10) : 0;
  for (int run = 0; run < count; run++) {
    // choose U
    if (!strcmp(utype, "low")) for (int i = 0; i < N; i++) ucomb[i] = 1u << i;
    else if (!strcmp(utype, "high")) { for (int i = 0; i < d; i++) ucomb[i] = 1u << (i + 3); for (int i = 0; i < 3; i++) ucomb[d + i] = 1u << i; }
    else {
      rng_state = (seed0 + run) * 0x9E3779B97F4A7C15ull + 12345;
      for (;;) {
        for (int i = 0; i < N; i++) ucomb[i] = (u32)(rnd64() & ((1ull << N) - 1));
        u32 e[32]; int rk = 0; memset(e, 0, sizeof e);
        for (int i = 0; i < N; i++) { u32 v = ucomb[i]; for (int b = 31; b >= 0 && v; b--) if (v >> b & 1) { if (e[b]) v ^= e[b]; else { e[b] = v; rk++; break; } } }
        if (rk == N) break;
      }
    }
    for (int f = 0; f < nf; f++) setup_u(f, &US[f]);
    if (docheck) { check(); if (run == count - 1) return 0; continue; }
    u64 kinv0[64]; int have_inv = 0; double R = 0, pairs = 0;
    u64 *dups = 0; size_t ndups = 0;
    for (int pass = 0; pass < passes; pass++) {
      size_t cap = (nphi / passes + 1024) * ncls_ni * 11 / 10 + 4096, nk = 0;
      u64 *keys = malloc(cap * sizeof(u64)); if (!keys) { fprintf(stderr, "oom\n"); return 1; }
      u64 alpha[2] = {0, 0}, tt[2][4] = {{0}};
      for (size_t i = 1; i <= nphi; i++) {
        u32 phi = (u32)(i ^ (i >> 1)); int flip = __builtin_ctzll(i);
        for (int f = 0; f < nf; f++) { alpha[f] ^= US[f].alpha[flip]; for (int l = 1; l <= 3; l++) tt[f][l] ^= US[f].tk[flip][l]; }
        u64 kni[512], kinv[64];
        if (!keys_of(phi, alpha, tt, kni, kinv)) return 1;
        if (!have_inv) { memcpy(kinv0, kinv, sizeof kinv0); have_inv = 1; if (pass == 0) for (int j = 0; j < ncls_inv; j++) keys[nk++] = kinv[j]; }
        else if (memcmp(kinv0, kinv, ncls_inv * sizeof(u64))) { fprintf(stderr, "invariant sets changed key at phi=%x: pipeline error\n", phi); return 1; }
        for (int j = 0; j < ncls_ni; j++) {
          if (passes > 1 && (int)((kni[j] * 0x9e3779b97f4a7c15ull) >> 40) % passes != pass) continue;
          if (nk == cap) { fprintf(stderr, "key buffer full\n"); return 1; }
          keys[nk++] = kni[j];
        }
      }
      if (pass == 0 && passes > 1) { // invariant keys belong to their own pass: drop the ones that do not
        size_t w = 0; for (size_t i = 0; i < nk; i++) if (i >= (size_t)ncls_inv || (int)((keys[i] * 0x9e3779b97f4a7c15ull) >> 40) % passes == 0) keys[w++] = keys[i];
        nk = w;
      }
      R += (double)nk; radix_sort(keys, nk);
      for (size_t s = 0; s < nk;) {
        size_t t = s + 1; while (t < nk && keys[t] == keys[s]) t++;
        if (t - s >= 2) { pairs += (double)(t - s) * (t - s - 1) / 2; dups = realloc(dups, (ndups + 1) * sizeof(u64)); dups[ndups++] = keys[s]; }
        s = t;
      }
      free(keys);
    }
    if (passes > 1) R += 0; // (invariant keys of the other passes are not stored: at most ncls_inv records)
    double expect = R * (R - 1) / 2 / pow(2.0, bits);
    tot_pairs += pairs; tot_expect += expect;
    // identify the colliding classes and the number of sets in each fibre
    int runworst = maxformal;
    if (ndups) {
      radix_sort(dups, ndups);
      int *sets = calloc(ndups, sizeof(int));
      u64 alpha[2] = {0, 0}, tt[2][4] = {{0}};
      for (size_t i = 1; i <= nphi; i++) {
        u32 phi = (u32)(i ^ (i >> 1)); int flip = __builtin_ctzll(i);
        for (int f = 0; f < nf; f++) { alpha[f] ^= US[f].alpha[flip]; for (int l = 1; l <= 3; l++) tt[f][l] ^= US[f].tk[flip][l]; }
        u64 kni[512], kinv[64]; keys_of(phi, alpha, tt, kni, kinv);
        for (int j = 0; j < ncls_ni + (i == 1 ? ncls_inv : 0); j++) {
          u64 key = j < ncls_ni ? kni[j] : kinv[j - ncls_ni]; int mult = j < ncls_ni ? cls_ni_mult[j] : cls_inv_mult[j - ncls_ni];
          size_t lo = 0, hi = ndups; while (lo < hi) { size_t mid = (lo + hi) / 2; if (dups[mid] < key) lo = mid + 1; else hi = mid; }
          if (lo < ndups && dups[lo] == key) { sets[lo] += mult; if (!quiet && count == 1 && ndups <= 64) printf("  coincidence key=%016llx phi=%x class=%03x%s sets=%d\n", (unsigned long long)key, phi, j < ncls_ni ? cls_ni_mask[j] : cls_inv_mask[j - ncls_ni], j < ncls_ni ? "" : " (U-invariant)", mult); }
        }
      }
      for (size_t i = 0; i < ndups; i++) { if (sets[i] > runworst) runworst = sets[i]; if (sets[i] < 64) fib[sets[i]]++; }
      free(sets); free(dups);
    }
    if (runworst > worst) worst = runworst;
    if (!quiet) printf("  U=%s#%d: records %.0f (2^%.2f), coincidences between formal classes: %.0f pairs, random model %.4g; genuine list at 5n/8 from this class: %d\n",
           utype, run, R, log2(R), pairs, expect, runworst);
    fflush(stdout);
  }
  if (!docheck) {
    printf("  total over %d subspaces U: %.0f coincident pairs, random model %.4g (ratio %.4f); largest genuine list %d (formal %d)\n", count, tot_pairs, tot_expect,
           tot_expect > 0 ? tot_pairs / tot_expect : 0.0, worst, maxformal);
    printf("  merged fibres by number of sets:"); for (int c = 2; c < 64; c++) if (fib[c]) printf(" %d:%zu", c, fib[c]); printf("\n");
  }
  return 0;
}
