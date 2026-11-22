// Referee 46: direct exhaustive test of note 39 Theorem 2.3 at n = 16.
// For EVERY f : D \ 0 -> {-1, 0, 1} (3^15 functions) and every type (alpha, beta), alpha >= beta (the other half
// is f -> -f), decide whether Psi_f = prod (1 + sZ)^f(s) agrees modulo Z^m' with a rational function A/B,
// deg A <= alpha, deg B <= beta, B(0) = 1. If so, reduce the fraction and test whether all its zeros and poles
// are of the form 1/s, s in D \ 0. Theorem 2.3 says they are when m' >= 2(alpha + beta). The same count is
// printed for m' = 2(alpha + beta) - 1 and - 2 (sharpness).
// cc -O2 -o 46_pade16 46_pade16.c -lpthread ; ./46_pade16 seed   (seed 0: real shape)
#include "46_gf.h"
#include <pthread.h>
#include <stdatomic.h>
#define PREC 8
static int n = 16;
static u64 pts[16], basis[4];
typedef struct { int s, mp, al, be; } test;
static test tests[64]; static int ntest;
typedef struct { long sol[64], nontriv[64], viol[64]; long leaves; } ctx;
static atomic_int nexttask;

// roots of the reversed polynomial must all lie in D \ 0
static int splits(const poly *A) { // A(Z) with A(0) != 0
  if (A->deg <= 0) return 1;
  poly r; pzero(&r); r.deg = A->deg;
  for (int j = 0; j <= A->deg; j++) r.c[A->deg - j] = A->c[j];
  int deg = r.deg;
  for (int i = 1; i < n && deg > 0; i++) {
    for (;;) {
      if (peval(&r, pts[i])) break;
      poly lin, q; pzero(&lin); lin.deg = 1; lin.c[1] = 1; lin.c[0] = pts[i];
      pdivrem(&q, NULL, &r, &lin); r = q; deg = r.deg;
      if (deg <= 0) break;
    }
  }
  return deg <= 0;
}

// returns 0: no approximant; 1: exists and splits over D; 2: exists and does not split
static int pade(const u64 *c, int mp, int al, int be) {
  int E = mp - 1 - al;
  u64 Mx[8][6];
  for (int i = 0; i < E; i++) {
    int row = al + 1 + i;
    for (int j = 1; j <= be; j++) Mx[i][j - 1] = (row - j >= 0) ? c[row - j] : 0;
    Mx[i][be] = c[row];
  }
  // fraction-free elimination
  int piv[6], rank = 0;
  for (int col = 0; col < be && rank < E; col++) {
    int p = -1;
    for (int i = rank; i < E; i++) if (Mx[i][col]) { p = i; break; }
    if (p < 0) continue;
    if (p != rank) for (int j = 0; j <= be; j++) { u64 t = Mx[p][j]; Mx[p][j] = Mx[rank][j]; Mx[rank][j] = t; }
    for (int i = rank + 1; i < E; i++) if (Mx[i][col]) {
      u64 f = Mx[i][col], g = Mx[rank][col];
      for (int j = 0; j <= be; j++) Mx[i][j] = gmul(Mx[i][j], g) ^ gmul(Mx[rank][j], f);
    }
    piv[rank++] = col;
  }
  for (int i = rank; i < E; i++) if (Mx[i][be]) return 0;
  // back substitution, free unknowns zero
  u64 b[6]; memset(b, 0, sizeof b);
  for (int rI = rank - 1; rI >= 0; rI--) {
    u64 v = Mx[rI][be];
    for (int j = piv[rI] + 1; j < be; j++) v ^= gmul(Mx[rI][j], b[j]);
    b[piv[rI]] = gmul(v, ginv(Mx[rI][piv[rI]]));
  }
  poly A, B, G, Ar, Br; pzero(&A); pzero(&B);
  B.c[0] = 1; for (int j = 1; j <= be; j++) B.c[j] = b[j - 1];
  B.deg = be; pnorm(&B);
  for (int i = 0; i <= al; i++) { u64 v = 0; for (int j = 0; j <= be && j <= i; j++) v ^= gmul(B.c[j], c[i - j]); A.c[i] = v; }
  A.deg = al; pnorm(&A);
  pgcd(&G, &A, &B);
  pdivrem(&Ar, NULL, &A, &G); pdivrem(&Br, NULL, &B, &G);
  return (splits(&Ar) && splits(&Br)) ? 1 : 2;
}

static void leaf(ctx *c, const u64 *P, int nz) {
  c->leaves++;
  for (int t = 0; t < ntest; t++) {
    int r = pade(P, tests[t].mp, tests[t].al, tests[t].be);
    if (!r) continue;
    c->sol[t]++;
    if (nz > tests[t].al + tests[t].be) c->nontriv[t]++;
    if (r == 2) c->viol[t]++;
  }
}
static void dfs(ctx *c, int i, const u64 *P, int nz) {
  if (i == n) { leaf(c, P, nz); return; }
  u64 Q[PREC], x = pts[i];
  dfs(c, i + 1, P, nz);
  Q[0] = 1; for (int j = PREC - 1; j >= 1; j--) Q[j] = P[j] ^ gmul(x, P[j - 1]);
  dfs(c, i + 1, Q, nz + 1);
  Q[0] = 1; for (int j = 1; j < PREC; j++) Q[j] = P[j] ^ gmul(x, Q[j - 1]);
  dfs(c, i + 1, Q, nz + 1);
}
static void *worker(void *arg) {
  ctx *c = arg;
  for (;;) {
    int t = atomic_fetch_add(&nexttask, 1);
    if (t >= 27) break;
    u64 P[PREC], Q[PREC]; memset(P, 0, sizeof P); P[0] = 1; int nz = 0;
    for (int i = 1; i <= 3; i++) {
      int ch = (t / (i == 1 ? 1 : i == 2 ? 3 : 9)) % 3; u64 x = pts[i];
      if (ch == 1) { Q[0] = 1; for (int j = PREC - 1; j >= 1; j--) Q[j] = P[j] ^ gmul(x, P[j - 1]); memcpy(P, Q, sizeof P); nz++; }
      if (ch == 2) { Q[0] = 1; for (int j = 1; j < PREC; j++) Q[j] = P[j] ^ gmul(x, Q[j - 1]); memcpy(P, Q, sizeof P); nz++; }
    }
    dfs(c, 4, P, nz);
  }
  return NULL;
}
int main(int argc, char **argv) {
  u64 seed = argc > 1 ? strtoull(argv[1], 0, 10) : 1;
  make_domain(4, seed, basis, pts);
  for (int s = 2; s <= 4; s++) for (int mp = 2 * s - 2; mp <= 2 * s; mp++) for (int be = 0; 2 * be <= s; be++) {
    if (mp <= s || mp > PREC) continue;
    tests[ntest].s = s; tests[ntest].mp = mp; tests[ntest].al = s - be; tests[ntest].be = be; ntest++;
  }
  pthread_t th[4]; ctx c[4]; memset(c, 0, sizeof c);
  for (int t = 0; t < 4; t++) pthread_create(&th[t], NULL, worker, &c[t]);
  for (int t = 0; t < 4; t++) pthread_join(th[t], NULL);
  long leaves = 0; for (int t = 0; t < 4; t++) leaves += c[t].leaves;
  printf("n=16 seed=%llu: %ld functions f with values in {-1,0,1}\n", (unsigned long long)seed, leaves);
  printf("alpha+beta  m'  (alpha,beta)  covered  approximants  with support > alpha+beta  NOT split over D\n");
  for (int t = 0; t < ntest; t++) {
    long a = 0, b = 0, v = 0; for (int i = 0; i < 4; i++) { a += c[i].sol[t]; b += c[i].nontriv[t]; v += c[i].viol[t]; }
    printf("%5d %7d     (%d,%d)      %s %12ld %12ld %18ld\n", tests[t].s, tests[t].mp, tests[t].al, tests[t].be, tests[t].mp >= 2 * tests[t].s ? "yes" : "no ", a, b, v);
  }
  return 0;
}
