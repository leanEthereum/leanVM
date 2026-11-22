// Referee 46: triple functions, periods, primitive sublists, the difference descent (note 37 Proposition 3.3)
// and the formal-model lemmas of note 37 section 4, on the full list of w = X^(n/2) L_W (n = 32 or 64) as
// produced by 46_tops / 46_rm / 46_family ("support double out" in hex, one member per line).
//
// cc -O2 -o 46_triples 46_triples.c -lpthread
// ./46_triples N seed dumpfile pairs P | bmin | prim R | descent [b | pow M k] | transfer T | perturb lambda | classes [file]
//   descent: pair of W-invariant members; b: pair of members with double points and a common period; pow M k: the
//   list in the dump is that of X^M in degree < k (for instance the flats, 46_tops 5 1 8 15 pow 15 dump f).
#include "46_gf.h"
#include <pthread.h>
#include <stdatomic.h>
typedef struct { int deg; u64 c[42]; } spoly;
static int N, n, L, KAP, wn;
static u64 pts[64], basis[8];
static u64 *supp, *dbl;
static u64 taus[2];
static u64 *ztab;
#define ZT(l, tt, a) ztab[((size_t)(l) * 2 + (tt)) * n + (a)]
static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static u64 shiftmask(u64 m, int a) { u64 r = 0; while (m) { int i = __builtin_ctzll(m); m &= m - 1; r |= 1ULL << (i ^ a); } return r; }
static int type_of(int l) { // 0: W-invariant set, 1: other set, 2: has double points
  if (dbl[l]) return 2;
  for (int b = 0; b < N - 3; b++) if (shiftmask(supp[l], 1 << b) != supp[l]) return 1;
  return 0;
}
static void load(const char *fn) {
  FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
  size_t cap = 1 << 17; supp = malloc(cap * 8); dbl = malloc(cap * 8); L = 0;
  unsigned long long a, b; int o;
  while (fscanf(f, "%llx %llx %d", &a, &b, &o) == 3) {
    if ((size_t)L == cap) { cap *= 2; supp = realloc(supp, cap * 8); dbl = realloc(dbl, cap * 8); }
    supp[L] = a; dbl[L] = b; L++;
  }
  fclose(f);
}
static void build_ztab(void) {
  ztab = malloc((size_t)L * 2 * n * 8);
  for (int l = 0; l < L; l++) for (int tt = 0; tt < 2; tt++) for (int a = 0; a < n; a++) {
    u64 y = taus[tt] ^ pts[a], p = 1, m = supp[l];
    while (m) { int x = __builtin_ctzll(m); m &= m - 1; u64 f = y ^ pts[x]; p = gmul(p, f); if ((dbl[l] >> x) & 1) p = gmul(p, f); }
    ZT(l, tt, a) = p;
  }
}
// periods of xi = (c_l - c_i)/(c_j - c_i) = (Z_i - Z_l)/(Z_i - Z_j): mask of the a != 0 with xi(X + a) = xi(X)
static u64 periods(int i, int j, int l) {
  u64 res = 0;
  u64 u0 = ZT(i, 0, 0) ^ ZT(j, 0, 0), v0 = ZT(i, 0, 0) ^ ZT(l, 0, 0);
  u64 u0b = ZT(i, 1, 0) ^ ZT(j, 1, 0), v0b = ZT(i, 1, 0) ^ ZT(l, 1, 0);
  for (int a = 1; a < n; a++) {
    u64 ua = ZT(i, 0, a) ^ ZT(j, 0, a), va = ZT(i, 0, a) ^ ZT(l, 0, a);
    if (gmul(va, u0) != gmul(v0, ua)) continue;
    ua = ZT(i, 1, a) ^ ZT(j, 1, a); va = ZT(i, 1, a) ^ ZT(l, 1, a);
    if (gmul(va, u0b) != gmul(v0b, ua)) continue;
    res |= 1ULL << a;
  }
  return res;
}
// number of thirds without any period (and not collinear) for the pair (i, j); hist[log2 |Pi|] optional
static long Bpair(int i, int j, long *hist, long *collinear) {
  u64 gam[64];
  u64 iu = ginv(ZT(i, 0, 0) ^ ZT(j, 0, 0));
  for (int a = 1; a < n; a++) gam[a] = gmul(ZT(i, 0, a) ^ ZT(j, 0, a), iu);
  long B = 0;
  for (int l = 0; l < L; l++) {
    if (l == i || l == j) continue;
    u64 v0 = ZT(i, 0, 0) ^ ZT(l, 0, 0); int any = 0;
    for (int a = 1; a < n; a++) if ((ZT(i, 0, a) ^ ZT(l, 0, a)) == gmul(v0, gam[a])) { any = 1; break; }
    if (!any) { B++; if (hist) hist[0]++; continue; }
    u64 pm = periods(i, j, l);
    if (!pm) { B++; if (hist) hist[0]++; continue; }
    int c = __builtin_popcountll(pm) + 1;
    if (c == n) { if (collinear) (*collinear)++; }
    else if (hist) hist[__builtin_ctz(c)]++;
  }
  return B;
}

// ---------------------------------------------------------------- pairs
static void cmd_pairs(int P) {
  int *winv = malloc(L * sizeof(int)), nw = 0;
  for (int l = 0; l < L; l++) if (type_of(l) == 0) winv[nw++] = l;
  printf("members %d, W-invariant %d\n", L, nw);
  long hist[8] = {0}, col = 0;
  long B = Bpair(winv[0], winv[1], hist, &col);
  printf("first W-invariant pair: period-free thirds B = %ld of %d; |Pi(xi_l)| :", B, L - 2);
  for (int e = 0; e < 8; e++) if (hist[e]) printf(" %d : %ld,", 1 << e, hist[e]);
  printf(" collinear : %ld\n", col);
  long mn = L, mx = 0;
  for (int t = 0; t < P; t++) { int a = winv[rnd() % nw], b = winv[rnd() % nw]; if (a == b) { t--; continue; } long b2 = Bpair(a, b, NULL, NULL); if (b2 < mn) mn = b2; if (b2 > mx) mx = b2; }
  printf("%d random W-invariant pairs: B between %ld and %ld\n", P, mn, mx);
  mn = L; double fr = 0;
  for (int t = 0; t < P; t++) { int a = rnd() % L, b = rnd() % L; if (a == b) { t--; continue; } long b2 = Bpair(a, b, NULL, NULL); if (b2 < mn) mn = b2; fr += 1.0 - (double)b2 / (L - 2); }
  printf("%d random pairs: least B %ld, mean fraction of thirds with a period %.4f\n", P, mn, fr / P);
}

// ---------------------------------------------------------------- bmin
static int bm_i; static atomic_int bm_next; static long bm_best[4]; static int bm_arg[4];
static void *bm_worker(void *arg) {
  int t = (int)(size_t)arg; bm_best[t] = L; bm_arg[t] = -1;
  for (;;) { int j = atomic_fetch_add(&bm_next, 1); if (j >= L) break; if (j == bm_i) continue; long b = Bpair(bm_i, j, NULL, NULL); if (b < bm_best[t]) { bm_best[t] = b; bm_arg[t] = j; } }
  return NULL;
}
static void cmd_bmin(void) {
  for (int ty = 0; ty < 3; ty++) {
    int rep = -1; for (int l = 0; l < L; l++) if (type_of(l) == ty) { rep = l; break; }
    if (rep < 0) continue;
    bm_i = rep; atomic_store(&bm_next, 0);
    pthread_t th[4]; for (size_t t = 0; t < 4; t++) pthread_create(&th[t], NULL, bm_worker, (void *)t);
    long best = L; int arg = -1;
    for (int t = 0; t < 4; t++) { pthread_join(th[t], NULL); if (bm_best[t] < best) { best = bm_best[t]; arg = bm_arg[t]; } }
    printf("first member of type %d (index %d): least B(i, j) over all %d partners j is %ld (partner of type %d)\n", ty, rep, L - 1, best, arg >= 0 ? type_of(arg) : -1);
  }
}

// ---------------------------------------------------------------- prim
static int prim_runs; static int prim_best[4]; static int *prim_set[4];
static void *prim_worker(void *arg) {
  int t = (int)(size_t)arg;
  u64 s = 0x1234567 + 7919ULL * (t + 1) + rs;
  int cap = 300; int *set = malloc(cap * sizeof(int)); int *perm = malloc(L * sizeof(int));
  u64 *gam = malloc((size_t)cap * (cap - 1) / 2 * n * 8); // pair (a1 < a2) at index a2 (a2 - 1)/2 + a1
  prim_best[t] = 0; prim_set[t] = malloc(cap * sizeof(int));
  for (int run = 0; run < prim_runs; run++) {
    for (int i = 0; i < L; i++) perm[i] = i;
    for (int i = L - 1; i > 0; i--) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; int j = (int)(s % (u64)(i + 1)); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
    int sz = 0;
    for (int q = 0; q < L; q++) {
      int l = perm[q], bad = 0;
      for (int a2 = 1; a2 < sz && !bad; a2++) {
        int j = set[a2];
        for (int a1 = 0; a1 < a2 && !bad; a1++) {
          int i = set[a1]; const u64 *g = gam + ((size_t)a2 * (a2 - 1) / 2 + a1) * n;
          u64 v0 = ZT(i, 0, 0) ^ ZT(l, 0, 0);
          for (int a = 1; a < n; a++) if ((ZT(i, 0, a) ^ ZT(l, 0, a)) == gmul(v0, g[a])) { if (periods(i, j, l)) { bad = 1; break; } }
        }
      }
      if (bad || sz == cap) continue;
      for (int a1 = 0; a1 < sz; a1++) {
        int i = set[a1]; u64 *g = gam + ((size_t)sz * (sz - 1) / 2 + a1) * n;
        u64 iu = ginv(ZT(i, 0, 0) ^ ZT(l, 0, 0));
        for (int a = 1; a < n; a++) g[a] = gmul(ZT(i, 0, a) ^ ZT(l, 0, a), iu);
      }
      set[sz++] = l;
    }
    if (sz > prim_best[t]) { prim_best[t] = sz; memcpy(prim_set[t], set, sz * sizeof(int)); }
  }
  return NULL;
}
static void cmd_prim(int R) {
  prim_runs = (R + 3) / 4;
  pthread_t th[4]; for (size_t t = 0; t < 4; t++) pthread_create(&th[t], NULL, prim_worker, (void *)t);
  int best = 0, bt = 0; for (int t = 0; t < 4; t++) { pthread_join(th[t], NULL); if (prim_best[t] > best) { best = prim_best[t]; bt = t; } }
  int *set = prim_set[bt]; long badtriples = 0; int ty[3] = {0, 0, 0};
  for (int a = 0; a < best; a++) { ty[type_of(set[a])]++; for (int b = a + 1; b < best; b++) for (int c = b + 1; c < best; c++) if (periods(set[a], set[b], set[c])) badtriples++; }
  printf("greedy primitive sublists, %d runs: largest has %d members (W-invariant %d, other sets %d, with double points %d); bad triples on full re-verification: %ld of %ld\n",
         prim_runs * 4, best, ty[0], ty[1], ty[2], badtriples, (long)best * (best - 1) * (best - 2) / 6);
}

// ---------------------------------------------------------------- polynomials of the members
static void zpoly(int l, poly *z) {
  pone(z);
  u64 m = supp[l];
  while (m) {
    int x = __builtin_ctzll(m); m &= m - 1;
    int rep = ((dbl[l] >> x) & 1) ? 2 : 1;
    for (int r = 0; r < rep; r++) { for (int j = z->deg + 1; j >= 1; j--) z->c[j] = z->c[j - 1] ^ gmul(pts[x], z->c[j]); z->c[0] = gmul(pts[x], z->c[0]); z->deg++; }
  }
}

// ---------------------------------------------------------------- descent (note 37 Proposition 3.3), any level
typedef struct { int cnt; poly *P; int *agr; u64 y[64], v[64]; int valid[64]; int kappa, m; } level;
static int agreement(const level *lv, const poly *P) { int c = 0; for (int x = 0; x < n; x++) if (lv->valid[x] && peval(P, lv->y[x]) == lv->v[x]) c++; return c; }
static int descend(const level *in, int i0, int i1, u64 ap, level *out, int *newi0, int *newi1) {
  poly u, u0, u1, eu, euq, rho, rem;
  padd(&u, &in->P[i1], &in->P[i0]);
  psplit(&u0, &u1, &u, ap);
  if (u1.deg < 0) { eu = u0; pmonic(&eu); } else if (u0.deg < 0) { eu = u1; pmonic(&eu); } else pgcd(&eu, &u0, &u1);
  pcompose_q(&euq, &eu, ap);
  pdivrem(&rho, &rem, &u, &euq);
  if (rem.deg >= 0) { printf("  ERROR: e_u(q) does not divide u\n"); return -1; }
  u64 r1 = rnd(), r2 = rnd();
  u64 ua[2] = {peval(&u, r1), peval(&u, r2)}, ub[2] = {peval(&u, r1 ^ ap), peval(&u, r2 ^ ap)};
  int kp = (in->kappa - rho.deg) / 2;
  out->cnt = 0; out->P = malloc((size_t)in->cnt * sizeof(poly)); out->agr = malloc((size_t)in->cnt * sizeof(int));
  out->kappa = kp; out->m = 2 * in->m;
  int z0 = 0, rootsrho = 0;
  u64 p0v[64], rhov[64];
  for (int x = 0; x < n; x++) {
    p0v[x] = peval(&in->P[i0], in->y[x]); rhov[x] = peval(&rho, in->y[x]);
    if (rhov[x] == 0) { rootsrho++; if (in->valid[x] && in->v[x] == p0v[x]) z0++; }
    out->y[x] = gsq(in->y[x]) ^ gmul(ap, in->y[x]);
    out->valid[x] = in->valid[x] && rhov[x] != 0;
    out->v[x] = out->valid[x] ? gmul(in->v[x] ^ p0v[x], ginv(rhov[x])) : 0;
  }
  long errors = 0, notin_checked = 0, notin_wrong = 0; int minslack_in = 1 << 30, minslack_out = 1 << 30, maxdegQ = -1;
  for (int l = 0; l < in->cnt; l++) {
    poly d; padd(&d, &in->P[l], &in->P[i0]);
    int per = 1;
    u64 da[2] = {peval(&d, r1), peval(&d, r2)}, db[2] = {peval(&d, r1 ^ ap), peval(&d, r2 ^ ap)};
    for (int t = 0; t < 2; t++) if (gmul(da[t], ub[t]) != gmul(db[t], ua[t])) per = 0;
    poly q, r, A, B;
    pdivrem(&q, &r, &d, &rho);
    int algebraic = 0;
    if (r.deg < 0) { psplit(&A, &B, &q, ap); if (B.deg < 0) algebraic = 1; }
    if (!per) { if (notin_checked < 3000) { notin_checked++; if (algebraic) notin_wrong++; } continue; }
    if (!algebraic) { errors++; continue; }
    if (A.deg > kp) errors++;
    if (A.deg > maxdegQ) maxdegQ = A.deg;
    int ag = agreement(out, &A);
    if (ag != in->agr[l] - z0) errors++;
    int sin = in->agr[l] - in->m * in->kappa, sout = ag - out->m * kp;
    if (sout < sin) errors++;
    if (sin < minslack_in) minslack_in = sin;
    if (sout < minslack_out) minslack_out = sout;
    if (l == i0) *newi0 = out->cnt;
    if (l == i1) *newi1 = out->cnt;
    out->P[out->cnt] = A; out->agr[out->cnt] = ag; out->cnt++;
  }
  printf("  |U| %d -> %d, degree bound %d -> %d, deg rho %d (roots of rho in D: %d), z0 %d <= |U| deg rho = %d: %s\n", in->m, out->m, in->kappa, kp, rho.deg, rootsrho, z0, in->m * rho.deg, z0 <= in->m * rho.deg ? "ok" : "VIOLATED");
  printf("  members %d, of which with period a': %d (largest deg Q %d); least slack before %d, after %d; non-members of M tested %ld, wrongly of the form P0 + rho Q(q): %ld; errors %ld\n",
         in->cnt, out->cnt, maxdegQ, minslack_in, minslack_out, notin_checked, notin_wrong, errors);
  return (int)errors + (int)notin_wrong;
}
static int powM = 0; // > 0: the word is X^powM (flats and their relatives) instead of X^(n/2) L_W
static void cmd_descent(int startpair) {
  level *lv = calloc(1, sizeof(level)), *nx;
  lv->cnt = L; lv->P = malloc((size_t)L * sizeof(poly)); lv->agr = malloc(L * sizeof(int)); lv->kappa = KAP; lv->m = 1;
  // the word w = X^(n/2) L_W on D, members c_l = w - Z_mu_l
  poly w; pone(&w); for (int x = 0; x < wn && !powM; x++) { for (int j = w.deg + 1; j >= 1; j--) w.c[j] = w.c[j - 1] ^ gmul(pts[x], w.c[j]); w.c[0] = gmul(pts[x], w.c[0]); w.deg++; }
  { int shf = powM ? powM : n / 2; poly sh; pzero(&sh); for (int j = 0; j <= w.deg; j++) sh.c[j + shf] = w.c[j]; sh.deg = w.deg + shf; w = sh; }
  for (int x = 0; x < n; x++) { lv->y[x] = pts[x]; lv->v[x] = peval(&w, pts[x]); lv->valid[x] = 1; }
  int maxdeg = 0, i0 = -1, i1 = -1;
  for (int l = 0; l < L; l++) {
    poly z; zpoly(l, &z); padd(&lv->P[l], &w, &z); if (lv->P[l].deg > maxdeg) maxdeg = lv->P[l].deg;
    lv->agr[l] = agreement(lv, &lv->P[l]);
    if (lv->agr[l] != __builtin_popcountll(supp[l])) { printf("ERROR: agreement of member %d is %d, support %d\n", l, lv->agr[l], __builtin_popcountll(supp[l])); exit(1); }
    int ty = type_of(l);
    if (powM) { if ((supp[l] | 1) == shiftmask(supp[l] | 1, 1)) { if (i0 < 0) i0 = l; else if (i1 < 0) i1 = l; } }
    else if (startpair == 0) { if (ty == 0) { if (i0 < 0) i0 = l; else if (i1 < 0) i1 = l; } }
    else { if (ty == 2 && supp[l] == shiftmask(supp[l], 1) && dbl[l] == shiftmask(dbl[l], 1)) { if (i0 < 0) i0 = l; else if (i1 < 0) i1 = l; } }
  }
  printf("level 0: %d members, largest degree of a codeword %d (bound %d), all agreements equal the supports\n", L, maxdeg, KAP);
  if (i0 < 0 || i1 < 0) { printf("no starting pair of the requested kind\n"); return; }
  int total = 0;
  for (int step = 0; step < N - 2; step++) {
    if (lv->cnt < 3 || lv->kappa < 1) break;
    u64 ap = lv->y[1 << step];
    if (ap == 0) break;
    printf("step %d: pair (%d, %d), direction a' = image of basis vector %d\n", step, i0, i1, step);
    nx = calloc(1, sizeof(level));
    int n0 = -1, n1 = -1;
    int e = descend(lv, i0, i1, ap, nx, &n0, &n1);
    if (e < 0) break;
    total += e; lv = nx; i0 = n0; i1 = n1;
  }
  printf("descent: total errors %d\n", total);
}

// ---------------------------------------------------------------- transfer lemma, rigidity, gap theorem (note 37 section 4)
static void cmd_transfer(int Tn) {
  long tested = 0, viol41 = 0, forced = 0, informative = 0, viol42 = 0, hyp42 = 0, viol43 = 0, hyp43 = 0, flats = 0, ctrl_viol = 0, ctrl = 0;
  long maxP = -1000; double minratio = 1e9;
  poly *Z = malloc((size_t)L * sizeof(poly));
  for (int l = 0; l < L; l++) zpoly(l, &Z[l]);
  for (int it = 0; it < Tn; it++) {
    int i = rnd() % L, j = rnd() % L, l = rnd() % L;
    if (it % 3 == 1) { while (dbl[i]) i = rnd() % L; while (dbl[j]) j = rnd() % L; while (dbl[l]) l = rnd() % L; }
    if (it % 3 == 2) { while (type_of(i)) i = rnd() % L; while (dbl[j]) j = rnd() % L; while (dbl[l]) l = rnd() % L; }
    if (i == j || i == l || j == l) { it--; continue; }
    poly d[3], G, u[3], rem;
    padd(&d[0], &Z[j], &Z[l]); padd(&d[1], &Z[l], &Z[i]); padd(&d[2], &Z[i], &Z[j]);
    pgcd(&G, &d[0], &d[1]);
    int delta = 0, r[3], s[3]; u64 R[3];
    for (int t = 0; t < 3; t++) { pdivrem(&u[t], &rem, &d[t], &G); if (rem.deg >= 0) { printf("gcd error\n"); exit(1); } if (u[t].deg > delta) delta = u[t].deg; }
    if (delta == 0) { it--; continue; } // collinear
    for (int t = 0; t < 3; t++) { R[t] = 0; for (int x = 0; x < n; x++) if (peval(&u[t], pts[x]) == 0) R[t] |= 1ULL << x; r[t] = __builtin_popcountll(R[t]); s[t] = delta - r[t]; }
    int nu = r[0] + r[1] + r[2], ss = 3 * delta - nu;
    // period group
    u64 r1 = rnd(), r2 = rnd(); int per = 1; u64 pmask = 1;
    for (int a = 1; a < n; a++) {
      if (gmul(peval(&u[0], r1), peval(&u[1], r1 ^ pts[a])) == gmul(peval(&u[0], r1 ^ pts[a]), peval(&u[1], r1)) &&
          gmul(peval(&u[0], r2), peval(&u[1], r2 ^ pts[a])) == gmul(peval(&u[0], r2 ^ pts[a]), peval(&u[1], r2))) { per++; pmask |= 1ULL << a; }
    }
    tested++;
    if (nu - 2 * delta - per > maxP) maxP = nu - 2 * delta - per;
    // Lemma 4.1
    for (int rep = 0; rep < 2; rep++) {
      u64 Q[3];
      if (rep == 0) { Q[0] = R[0]; Q[1] = R[1]; Q[2] = R[2]; }
      else { // control: random disjoint sets of the same sizes
        int perm[64]; for (int x = 0; x < n; x++) perm[x] = x;
        for (int x = n - 1; x > 0; x--) { int y = rnd() % (x + 1); int t2 = perm[x]; perm[x] = perm[y]; perm[y] = t2; }
        int pos = 0; for (int t = 0; t < 3; t++) { Q[t] = 0; for (int c = 0; c < r[t]; c++) Q[t] |= 1ULL << perm[pos++]; }
      }
      int anyviol = 0;
      for (int z = 1; z < n; z++) {
        int t01 = __builtin_popcountll(Q[0] & shiftmask(Q[1], z)), t02 = __builtin_popcountll(Q[0] & shiftmask(Q[2], z)), t12 = __builtin_popcountll(Q[1] & shiftmask(Q[2], z));
        int none = t01 <= s[2] && t02 <= s[1] && t12 <= s[0];
        int ty2 = t01 >= r[0] - s[1] && t02 <= s[1] && t12 <= s[0];
        int ty1 = t02 >= r[0] - s[2] && t01 <= s[2] && t12 <= s[0];
        int ty0 = t12 >= r[1] - s[2] && t01 <= s[2] && t02 <= s[1];
        if (!(none || ty0 || ty1 || ty2)) anyviol = 1;
        if (rep == 0) { if (!none) forced++; if (nu - 2 * delta >= 2) informative++; }
      }
      if (rep == 0) viol41 += anyviol; else { ctrl++; ctrl_viol += anyviol; }
    }
    // Lemma 4.2
    for (int a = 1; a < n; a++) {
      int sum = 0; for (int t = 0; t < 3; t++) sum += __builtin_popcountll(R[t] & shiftmask(R[t], a));
      if (sum >= 2 * delta) { hyp42++; if (!((pmask >> a) & 1)) viol42++; }
    }
    // Theorem 4.3
    if (ss == 0 && per == delta) flats++;
    else { double ratio = (double)ss * 4 * n / ((double)delta * delta); if (ratio < minratio) minratio = ratio; }
    if (4L * n * ss < (long)delta * delta) { hyp43++; if (!(ss == 0 && per == delta)) viol43++; }
  }
  printf("triples tested %ld (non-collinear), directions per triple %d\n", tested, n - 1);
  printf("Lemma 4.1: triples with a direction of no admissible type: %ld; directions with a forced transfer type: %ld; directions tested with nu - 2 delta >= 2: %ld\n", viol41, forced, informative);
  printf("   control (random disjoint sets of the same sizes): %ld of %ld violate\n", ctrl_viol, ctrl);
  printf("Lemma 4.2: directions with sum |R_i & (R_i + a)| >= 2 delta: %ld, not periods: %ld\n", hyp42, viol42);
  printf("Theorem 4.3: flats %ld; functions with s < delta^2/4n: %ld, of which not flats: %ld; least s * 4n / delta^2 over non-flats: %.3f\n", flats, hyp43, viol43, minratio);
  printf("largest nu - 2 delta - |Pi| (Conjecture P of note 17 says <= 0): %ld\n", maxP);
}

// ---------------------------------------------------------------- perturbation (note 37 Proposition 2.1), small n
static void cmd_perturb(double lam) {
  u64 Pm = 0; for (int x = 0; x < n; x++) if ((double)(rnd() >> 11) / 9007199254740992.0 < lam) Pm |= 1ULL << x;
  long st_before = 0, st_after = 0; double sig_b = 0, sig_a = 0, sz_a = 0; long lost[65]; memset(lost, 0, sizeof lost);
  for (int l = 0; l < L; l++) {
    u64 S = supp[l], S2 = S & ~Pm; int mb = 0, ma = 0, sb = 0, sa = 0;
    for (int a = 1; a < n; a++) {
      int cb = __builtin_popcountll(S & shiftmask(S, a)), ca = __builtin_popcountll(S2 & shiftmask(S2, a));
      if (cb > mb) mb = cb; if (ca > ma) ma = ca;
      if (cb == __builtin_popcountll(S)) sb = 1;
      if (ca == __builtin_popcountll(S2)) sa = 1;
    }
    st_before += sb; st_after += sa;
    sig_b += (double)mb / __builtin_popcountll(S); sig_a += (double)ma / __builtin_popcountll(S2); sz_a += (double)__builtin_popcountll(S2) / __builtin_popcountll(S);
    lost[__builtin_popcountll(S & Pm)]++;
  }
  printf("perturbed set P: %d points of %d (lambda %.3f)\n", __builtin_popcountll(Pm), n, lam);
  printf("members whose agreement set has a nonzero period: before %ld of %d, after %ld (those are the members with S & P invariant)\n", st_before, L, st_after);
  printf("mean of max_a |S & (S+a)| / |S|: before %.4f, after %.4f; mean |S'|/|S| %.4f\n", sig_b / L, sig_a / L, sz_a / L);
  printf("agreement lost (points of S in P) : members:"); for (int c = 0; c <= 64; c++) if (lost[c]) printf(" %d : %ld,", c, lost[c]); printf("\n");
  printf("all %d codewords remain codewords agreeing with the new word exactly on S \\ P, and their triple functions are unchanged (they depend on the codewords only)\n", L);
}

// ---------------------------------------------------------------- classes: sublists that are lists in degree < n/2
// Members with the same coefficient of X^(n/2) in Z_mu differ in degree < n/2: each class is a list of the code
// of degree < n/2 (k = n/2) for the word w + gamma X^(n/2), at the same agreement. Writes the largest class.
typedef struct { u64 key; int idx; } kv;
static int cmpkv(const void *a, const void *b) { const kv *x = a, *y = b; if (x->key != y->key) return x->key < y->key ? -1 : 1; return x->idx - y->idx; }
static void cmd_classes(const char *outfn) {
  kv *t = malloc((size_t)L * sizeof(kv));
  for (int l = 0; l < L; l++) { poly z; zpoly(l, &z); t[l].key = z.c[n / 2]; t[l].idx = l; }
  qsort(t, L, sizeof(kv), cmpkv);
  long hist[4096]; memset(hist, 0, sizeof hist); int best = 0, bs = 0, nc = 0;
  for (int a = 0; a < L;) { int b = a; while (b < L && t[b].key == t[a].key) b++; int c = b - a; nc++; if (c < 4096) hist[c]++; if (c > best) { best = c; bs = a; } a = b; }
  printf("%d members in %d classes by the coefficient of X^(n/2); class size : number of classes:", L, nc);
  for (int c = 1; c < 4096; c++) if (hist[c]) printf(" %d : %ld,", c, hist[c]);
  printf("\nlargest class %d members", best);
  int ty[3] = {0, 0, 0}; for (int a = bs; a < bs + best; a++) ty[type_of(t[a].idx)]++;
  printf(" (W-invariant %d, other sets %d, with double points %d)\n", ty[0], ty[1], ty[2]);
  if (outfn) { FILE *f = fopen(outfn, "w"); for (int a = bs; a < bs + best; a++) fprintf(f, "%016llx %016llx 0\n", (unsigned long long)supp[t[a].idx], (unsigned long long)dbl[t[a].idx]); fclose(f); }
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: 46_triples N seed dumpfile pairs P | bmin | prim R | descent [b] | transfer T | perturb lambda\n"); return 1; }
  N = atoi(argv[1]); n = 1 << N; u64 seed = strtoull(argv[2], 0, 10); KAP = n / 2; wn = n / 8;
  make_domain(N, seed, basis, pts);
  load(argv[3]);
  rs ^= seed * 0x2545F4914F6CDD1DULL; taus[0] = rnd(); taus[1] = rnd();
  const char *cmd = argv[4];
  if (!strcmp(cmd, "pairs") || !strcmp(cmd, "bmin") || !strcmp(cmd, "prim")) build_ztab();
  if (!strcmp(cmd, "pairs")) cmd_pairs(argc > 5 ? atoi(argv[5]) : 20);
  else if (!strcmp(cmd, "bmin")) cmd_bmin();
  else if (!strcmp(cmd, "prim")) cmd_prim(argc > 5 ? atoi(argv[5]) : 8);
  else if (!strcmp(cmd, "descent")) {
    if (argc > 7 && !strcmp(argv[5], "pow")) { powM = atoi(argv[6]); KAP = atoi(argv[7]) - 1; cmd_descent(0); }
    else cmd_descent(argc > 5 ? 1 : 0);
  }
  else if (!strcmp(cmd, "transfer")) cmd_transfer(argc > 5 ? atoi(argv[5]) : 300);
  else if (!strcmp(cmd, "perturb")) cmd_perturb(argc > 5 ? atof(argv[5]) : 0.125);
  else if (!strcmp(cmd, "classes")) cmd_classes(argc > 5 ? argv[5] : NULL);
  else { fprintf(stderr, "unknown command\n"); return 1; }
  return 0;
}
