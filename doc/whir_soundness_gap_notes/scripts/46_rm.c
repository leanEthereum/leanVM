// Referee 46: exhaustive list of a top-type word at n = 64 (also n = 32) by linearization of the power sums.
// Own design, no result of notes 02/12/39 is used (no Theorem W, no Theorem S, no classification).
//
// Word w = X^a Z_B, mass M, codewords of degree < k, agreement >= T, m' = M - k + 1, rev(w) = t mod Z^m'.
// A member is P = w - c: monic, degree M, e_j(roots of P) = t_j for j < m', at least T distinct roots in D.
// Let m in F_2^D be the parity of the multiplicities of the roots of P in D. In characteristic two the power
// sums of the roots in D are F_2-LINEAR in m: p_j = sum_x m_x x^j, and p_j of all roots is a polynomial pi_j in
// t_1..t_j (Newton), equal to its value on the reference multiset. So:
//  Case A (every root outside D has even multiplicity): sum_x m_x x^j = pi_j for odd j < m'. This is a linear
//    system over F_2 (64 unknowns, 64 equations per j), solved exactly on the numeric domain. For every solution
//    m of admissible weight, R = t / Psi_m must be the square Psi_nu(Z)^2 of the missing part nu (mass
//    (M - |m|)/2), which determines nu when 2 mass(nu) < m'; its roots are then located (in D or not).
//  Case B (M - T = 2, m' >= 8: two DISTINCT roots r, r + d outside D, 38 simple roots in D): e_1 gives
//    d = pi_1 + sum m_x x in D \ 0, p_3 gives h2 = r(r + d) = (pi_3 + d^3 + sum m_x x^3)/d, and p_5 becomes
//    sum_x m_x (x^5 + d^2 x^3 + x^6/d) = const(d), again F_2-linear. For each d the system is solved, h2 is
//    constant on the solution space (checked; otherwise its values are enumerated), p_7 adds a linear equation,
//    and every solution of weight M - 2 is verified in full. Solutions whose r lies in D are multiset tops already
//    found in case A (their number is predicted from case A and compared); the others are members with roots
//    outside D.
// Cases A and B exhaust the members when M - T <= 2 (a single root outside D is impossible: e_1 is in D).
//
// cc -O2 -o 46_rm 46_rm.c -lpthread
// ./46_rm N seed k T pow M | xlw a j | xb a hexmask [dump file] [maxe E]
//   maxe: case B skips (and reports) a direction d for which h2 has more than E free dimensions (default 8);
//   on a random basis the largest value met is 5, on the real shape it is larger and case B is then incomplete.
#include "46_gf.h"
#include <pthread.h>
#include <stdatomic.h>
#define MAXM 16
#define NW 4
static int N, n, K, T, M, mp;
static u64 pts[64], basis[8], tser[MAXM], pi_[MAXM];
typedef struct { u64 supp, dbl; int out, maxmult; } member;
typedef struct { member *a; size_t len, cap; } mlist;
static void madd(mlist *l, member m) {
  if (l->len == l->cap) { l->cap = l->cap ? 2 * l->cap : 1024; l->a = realloc(l->a, l->cap * sizeof(member)); }
  l->a[l->len++] = m;
}

// Solve sum_x m_x col[x] = rhs over F_2 (nw words per vector). Returns kernel dimension, -1 if inconsistent.
static int solve(int nw, u64 (*col)[NW], const u64 *rhs, u64 *part, u64 *ker) {
  u64 prow[64]; int prhs[64]; int pcol[64], np = 0; // pivot rows in reduced form
  int haspiv[64]; memset(haspiv, 0, sizeof haspiv);
  for (int w = 0; w < nw; w++) for (int b = 0; b < 64; b++) {
    u64 row = 0; int rb = (int)((rhs[w] >> b) & 1);
    for (int x = 0; x < n; x++) if ((col[x][w] >> b) & 1) row |= 1ULL << x;
    for (int i = 0; i < np; i++) if ((row >> pcol[i]) & 1) { row ^= prow[i]; rb ^= prhs[i]; }
    if (!row) { if (rb) return -1; continue; }
    int p = __builtin_ctzll(row);
    for (int i = 0; i < np; i++) if ((prow[i] >> p) & 1) { prow[i] ^= row; prhs[i] ^= rb; }
    prow[np] = row; prhs[np] = rb; pcol[np] = p; haspiv[p] = 1; np++;
  }
  *part = 0;
  for (int i = 0; i < np; i++) if (prhs[i]) *part |= 1ULL << pcol[i];
  int d = 0;
  for (int f = 0; f < n; f++) if (!haspiv[f]) {
    u64 v = 1ULL << f;
    for (int i = 0; i < np; i++) if ((prow[i] >> f) & 1) v |= 1ULL << pcol[i];
    ker[d++] = v;
  }
  return d;
}

static void psi_of(u64 m, u64 *P) {
  memset(P, 0, MAXM * sizeof(u64)); P[0] = 1;
  while (m) { int x = __builtin_ctzll(m); m &= m - 1; for (int j = mp - 1; j >= 1; j--) P[j] ^= gmul(pts[x], P[j - 1]); }
}

static long cntA_cand = 0, unresolved = 0;
static void procA(u64 m, mlist *out) {
  int w = __builtin_popcountll(m), j2 = M - w;
  if (j2 < 0 || (j2 & 1)) return;
  int j = j2 / 2;
  if (w + j < T) return;
  if (2 * j > mp - 1) { unresolved++; return; }
  cntA_cand++;
  u64 P[MAXM], R[MAXM];
  psi_of(m, P);
  R[0] = 1;
  for (int a = 1; a < mp; a++) { u64 v = tser[a]; for (int i = 1; i <= a; i++) v ^= gmul(P[i], R[a - i]); R[a] = v; }
  for (int a = 1; a < mp; a += 2) if (R[a]) return;
  for (int i = j + 1; 2 * i < mp; i++) if (R[2 * i]) return;
  // nu = X^j + s_1 X^(j-1) + .. + s_j
  u64 h[MAXM]; int deg = j;
  h[j] = 1; for (int i = 1; i <= j; i++) h[j - i] = gsqrt(R[2 * i]);
  int mult[64]; for (int i = 0; i < n; i++) mult[i] = (int)((m >> i) & 1);
  for (int i = 0; i < n && deg > 0; i++) {
    for (;;) {
      u64 v = 0; for (int e = deg; e >= 0; e--) v = gmul(v, pts[i]) ^ h[e];
      if (v) break;
      u64 q[MAXM]; q[deg - 1] = h[deg];
      for (int e = deg - 1; e >= 1; e--) q[e - 1] = h[e] ^ gmul(pts[i], q[e]);
      for (int e = 0; e < deg; e++) h[e] = q[e];
      deg--; mult[i] += 2;
      if (deg == 0) break;
    }
  }
  member mm; mm.supp = 0; mm.dbl = 0; mm.out = 2 * deg; mm.maxmult = 0;
  for (int i = 0; i < n; i++) {
    if (mult[i]) mm.supp |= 1ULL << i;
    if (mult[i] >= 2) mm.dbl |= 1ULL << i;
    if (mult[i] > mm.maxmult) mm.maxmult = mult[i];
  }
  if (__builtin_popcountll(mm.supp) < T) return;
  madd(out, mm);
}

// Case B
static atomic_int nextd;
static int maxe_allowed = 8;
typedef struct { mlist phantom; long inD[3], cand, sols; int maxe, maxdim, nosol, skipped; } bctx;
static void caseB_d(int di, bctx *c) {
  u64 d = pts[di], id = ginv(d), d2 = gsq(d), d3 = gmul(d2, d), d5 = gmul(d3, d2), d7 = gmul(d5, d2);
  u64 kap = pi_[3] ^ d3;
  u64 c5 = pi_[5] ^ d5 ^ gmul(d2, kap) ^ gmul(gsq(kap), id);
  u64 col[64][NW], rhs[NW], x3[64], x7[64];
  for (int x = 0; x < n; x++) {
    u64 v = pts[x], v2 = gsq(v), v3 = gmul(v2, v), v5 = gmul(v3, v2), v6 = gsq(v3), v7 = gmul(v5, v2);
    x3[x] = v3; x7[x] = v7;
    col[x][0] = v; col[x][1] = v5 ^ gmul(d2, v3) ^ gmul(v6, id); col[x][2] = v3; col[x][3] = v7;
  }
  rhs[0] = d ^ pi_[1]; rhs[1] = c5;
  u64 part1, ker1[64];
  int d1 = solve(2, col, rhs, &part1, ker1);
  if (d1 < 0) { c->nosol++; return; }
  // values of lambda_3 on the solution space: lam3(part1) + span(lam3(ker1))
  u64 l3p = 0; for (int x = 0; x < n; x++) if ((part1 >> x) & 1) l3p ^= x3[x];
  u64 sp[64]; int e = 0; u64 red[64]; memset(red, 0, sizeof red);
  for (int i = 0; i < d1; i++) {
    u64 v = 0, orig; for (int x = 0; x < n; x++) if ((ker1[i] >> x) & 1) v ^= x3[x];
    orig = v;
    for (int b = 63; b >= 0 && v; b--) { if (!((v >> b) & 1)) continue; if (red[b]) v ^= red[b]; else { red[b] = v; sp[e++] = orig; v = 0; } }
  }
  if (e > c->maxe) c->maxe = e;
  if (e > maxe_allowed) { c->skipped++; return; }
  for (unsigned long comb = 0; comb < (1UL << e); comb++) {
    u64 l3 = l3p; for (int i = 0; i < e; i++) if ((comb >> i) & 1) l3 ^= sp[i];
    u64 h2 = gmul(kap ^ l3, id);
    rhs[2] = l3; rhs[3] = pi_[7] ^ d7 ^ gmul(d5, h2) ^ gmul(d, gmul(h2, gsq(h2)));
    u64 part2, ker2[64];
    int dd = solve(4, col, rhs, &part2, ker2);
    if (dd < 0) continue;
    if (dd > c->maxdim) c->maxdim = dd;
    if (dd > 30) { fprintf(stderr, "solution space of dimension %d: not enumerated\n", dd); exit(1); }
    u64 m = part2;
    for (unsigned long g = 0;; g++) {
      if (__builtin_popcountll(m) == M - 2) {
        c->cand++;
        u64 P[MAXM]; psi_of(m, P);
        int ok = 1;
        for (int a = 1; a < mp && ok; a++) {
          u64 v = P[a] ^ gmul(d, P[a - 1]) ^ (a >= 2 ? gmul(h2, P[a - 2]) : 0);
          if (v != tser[a]) ok = 0;
        }
        if (ok) {
          c->sols++;
          int ri = -1;
          for (int x = 0; x < n; x++) if ((gsq(pts[x]) ^ gmul(d, pts[x])) == h2) { ri = x; break; }
          if (ri < 0) { member mm; mm.supp = m; mm.dbl = 0; mm.out = 2; mm.maxmult = 1; madd(&c->phantom, mm); }
          else { int in = (int)((m >> ri) & 1) + (int)((m >> (ri ^ di)) & 1); c->inD[in]++; }
        }
      }
      unsigned long nx = g + 1;
      if (nx >> dd) break;
      m ^= ker2[__builtin_ctzl(nx)];
    }
  }
}
static void *workerB(void *arg) {
  bctx *c = arg;
  for (;;) { int di = atomic_fetch_add(&nextd, 1); if (di >= n) break; caseB_d(di, c); }
  return NULL;
}

static int cmpm(const void *a, const void *b) {
  const member *x = a, *y = b;
  if (x->supp != y->supp) return x->supp < y->supp ? -1 : 1;
  if (x->dbl != y->dbl) return x->dbl < y->dbl ? -1 : 1;
  return x->out - y->out;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: 46_rm N seed k T pow M | xlw a j | xb a hexmask [dump file]\n"); return 1; }
  N = atoi(argv[1]); n = 1 << N; u64 seed = strtoull(argv[2], 0, 10); K = atoi(argv[3]); T = atoi(argv[4]);
  make_domain(N, seed, basis, pts);
  int ai = 5; int a = 0; u64 B = 0;
  if (!strcmp(argv[ai], "pow")) { a = atoi(argv[ai + 1]); ai += 2; }
  else if (!strcmp(argv[ai], "xlw")) { a = atoi(argv[ai + 1]); int j = atoi(argv[ai + 2]); B = (j == 6) ? ~0ULL : ((1ULL << (1 << j)) - 1); ai += 3; }
  else if (!strcmp(argv[ai], "xb")) { a = atoi(argv[ai + 1]); B = strtoull(argv[ai + 2], 0, 16); ai += 3; }
  else { fprintf(stderr, "bad word\n"); return 1; }
  const char *dump = NULL;
  for (; ai < argc; ai++) { if (!strcmp(argv[ai], "dump")) dump = argv[++ai]; else if (!strcmp(argv[ai], "maxe")) maxe_allowed = atoi(argv[++ai]); }
  M = a + __builtin_popcountll(B); mp = M - K + 1;
  if (mp > MAXM || mp < 2 || M - T > 2) { fprintf(stderr, "need m' <= %d and M - T <= 2 (M=%d m'=%d)\n", MAXM, M, mp); return 1; }
  psi_of(B, tser);
  memset(pi_, 0, sizeof pi_);
  for (int x = 0; x < n; x++) if ((B >> x) & 1) { u64 pw = 1; for (int j = 1; j < MAXM; j++) { pw = gmul(pw, pts[x]); pi_[j] ^= pw; } }
  printf("N=%d seed=%llu k=%d T=%d M=%d m'=%d\n", N, (unsigned long long)seed, K, T, M, mp);
  // Case A
  u64 col[64][NW], rhs[NW]; int nodd = 0;
  for (int j = 1; j < mp; j += 2) { if (nodd == NW) { fprintf(stderr, "m' too large for NW\n"); return 1; } for (int x = 0; x < n; x++) col[x][nodd] = gpow(pts[x], j); rhs[nodd] = pi_[j]; nodd++; }
  u64 part, ker[64];
  int dA = solve(nodd, col, rhs, &part, ker);
  printf("case A: linear system of %d x 64 equations in %d unknowns, solution space of dimension %d\n", nodd, n, dA);
  if (dA < 0 || dA > 30) { fprintf(stderr, "case A not enumerable\n"); return 1; }
  mlist LA = {0};
  { u64 m = part; for (unsigned long g = 0;; g++) { procA(m, &LA); unsigned long nx = g + 1; if (nx >> dA) break; m ^= ker[__builtin_ctzl(nx)]; } }
  long simple = 0, twodbl = 0, onedbl = 0, other = 0, outA = 0;
  for (size_t i = 0; i < LA.len; i++) {
    int s = __builtin_popcountll(LA.a[i].supp), dd = __builtin_popcountll(LA.a[i].dbl);
    if (LA.a[i].out) outA++;
    else if (s == M && dd == 0) simple++;
    else if (s == M - 2 && dd == 2 && LA.a[i].maxmult == 2) twodbl++;
    else if (s == M - 1 && dd == 1 && LA.a[i].maxmult == 2) onedbl++;
    else other++;
  }
  printf("case A: %ld parity vectors of admissible weight examined (unresolved %ld), members %zu\n", cntA_cand, unresolved, LA.len);
  printf("        simple %ld, one double point %ld, two double points %ld, other multiset tops %ld, with a multiple root OUTSIDE D %ld\n", simple, onedbl, twodbl, other, outA);
  mlist LB = {0};
  if (M - T == 2 && mp >= 8) {
    int nt = 4; pthread_t th[4]; bctx bc[4]; memset(bc, 0, sizeof bc);
    atomic_store(&nextd, 1);
    for (int t = 0; t < nt; t++) pthread_create(&th[t], NULL, workerB, &bc[t]);
    long inD[3] = {0, 0, 0}, cand = 0, sols = 0; int maxe = 0, maxdim = 0, nosol = 0, skipped = 0;
    for (int t = 0; t < nt; t++) {
      pthread_join(th[t], NULL);
      for (int i = 0; i < 3; i++) inD[i] += bc[t].inD[i];
      cand += bc[t].cand; sols += bc[t].sols; nosol += bc[t].nosol; skipped += bc[t].skipped;
      if (bc[t].maxe > maxe) maxe = bc[t].maxe;
      if (bc[t].maxdim > maxdim) maxdim = bc[t].maxdim;
      for (size_t i = 0; i < bc[t].phantom.len; i++) madd(&LB, bc[t].phantom.a[i]);
    }
    long predicted = simple * ((long)M * (M - 1) / 2) + twodbl + onedbl * (M - 2);
    printf("case B: %d directions d, %d without solution, free dimensions of h2 at most %d, solution spaces of dimension at most %d\n", n - 1, nosol, maxe, maxdim);
    if (skipped) printf("case B: INCOMPLETE, %d directions skipped because h2 has more than %d free dimensions (the prediction below then need not match)\n", skipped, maxe_allowed);
    printf("case B: %ld sets of weight %d verified, %ld solutions; pair in D: outside the set %ld, one inside %ld, both inside %ld; predicted from case A %ld\n", cand, M - 2, sols, inD[0], inD[1], inD[2], predicted);
    printf("case B: members with two distinct roots OUTSIDE D: %zu\n", LB.len);
  } else if (M - T == 2) printf("case B skipped (needs m' >= 8)\n");
  size_t tot = LA.len + LB.len;
  member *all = malloc((tot + 1) * sizeof(member));
  memcpy(all, LA.a, LA.len * sizeof(member)); if (LB.len) memcpy(all + LA.len, LB.a, LB.len * sizeof(member));
  qsort(all, tot, sizeof(member), cmpm);
  size_t dup = 0; for (size_t i = 1; i < tot; i++) if (!cmpm(&all[i - 1], &all[i])) dup++;
  printf("TOTAL members at agreement >= %d: %zu (duplicates %zu)\n", T, tot, dup);
  if (dump) {
    FILE *f = fopen(dump, "w");
    for (size_t i = 0; i < tot; i++) fprintf(f, "%016llx %016llx %d\n", (unsigned long long)all[i].supp, (unsigned long long)all[i].dbl, all[i].out);
    fclose(f);
  }
  return 0;
}
