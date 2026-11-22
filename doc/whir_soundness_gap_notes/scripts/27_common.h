// Researcher 27. Shared code for the four-member programs: GF(2^64) (leanVM modulus), a random ("generic") F_2-subspace
// domain, small polynomial arithmetic, and the invariants of a four-member configuration.
//
// A configuration is three polynomials u_i = c_i - c_0 (i = 1, 2, 3). With G = gcd(u_1, u_2, u_3) and v_i = u_i / G the
// curve is Xi = (v_1 : v_2 : v_3) : P^1 -> P^2 of degree delta = max deg v_i, and
//   I(Xi) = sum over x in D with G(x) != 0 of (4 - number of distinct values among 0, v_1(x), v_2(x), v_3(x)).
// On algebraically independent points I <= 3 delta + 2. The five cross-ratio functions of the five marked values
// (c_0, c_1, c_2, c_3, infinity) are the four triple functions xi_l (member l omitted) and the cross-ratio Phi of the
// four members; for each one the program computes its degree, nu = #{x in D : value in {0, 1, infinity}} and its
// period group {a in D : f(X + a) = f(X)}.
#ifndef C27_H
#define C27_H
#include "02_gf.h"
#define MAXN 32
#define PD 72
static int NN, n;
static u64 pts[MAXN];
static u64 rs = 88172645463325252ull;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline u64 mul(u64 a, u64 b) { return mul64(a, b); }
static u64 inv(u64 a) { u64 r = 1, s = mul(a, a); for (int i = 1; i < 64; i++) { r = mul(r, s); s = mul(s, s); } return r; }

// real = 0: random basis; real = 1: basis 1, x, ..., x^{N-1} (the leanVM domain)
static void domain_init(int N, u64 seed, int real) {
  NN = N; n = 1 << N;
  if (seed) rs = seed * 0x9e3779b97f4a7c15ull + 12345;
  for (int i = 0; i < 20; i++) rnd();
  u64 b[8];
  for (int i = 0; i < N; i++) b[i] = real ? (1ull << i) : rnd();
  for (int x = 0; x < n; x++) { u64 v = 0; for (int i = 0; i < N; i++) if (x >> i & 1) v ^= b[i]; pts[x] = v; }
}

typedef struct { int d; u64 c[PD]; } poly; // d = -1: zero
static void pnorm(poly *a) { while (a->d >= 0 && !a->c[a->d]) a->d--; }
static void pzero(poly *a) { a->d = -1; }
static void padd(poly *r, const poly *a, const poly *b) {
  int d = a->d > b->d ? a->d : b->d;
  for (int i = 0; i <= d; i++) r->c[i] = (i <= a->d ? a->c[i] : 0) ^ (i <= b->d ? b->c[i] : 0);
  r->d = d; pnorm(r);
}
static void pmul(poly *r, const poly *a, const poly *b) {
  poly t; if (a->d < 0 || b->d < 0) { r->d = -1; return; }
  t.d = a->d + b->d; if (t.d >= PD) { fprintf(stderr, "poly overflow\n"); exit(1); }
  for (int i = 0; i <= t.d; i++) t.c[i] = 0;
  for (int i = 0; i <= a->d; i++) if (a->c[i]) for (int j = 0; j <= b->d; j++) t.c[i + j] ^= mul(a->c[i], b->c[j]);
  *r = t;
}
// a = q b + r
static void pdivmod(poly *q, poly *r, const poly *a, const poly *b) {
  poly x = *a; poly qq; qq.d = a->d - b->d; u64 iv = inv(b->c[b->d]);
  for (int i = 0; i <= qq.d; i++) qq.c[i] = 0;
  for (int i = x.d; i >= b->d; i--) { u64 f = mul(x.c[i], iv); qq.c[i - b->d] = f; if (f) for (int j = 0; j <= b->d; j++) x.c[i - b->d + j] ^= mul(f, b->c[j]); }
  if (qq.d < 0) qq.d = -1;
  x.d = b->d - 1 < x.d ? b->d - 1 : x.d; pnorm(&x); pnorm(&qq);
  if (q) *q = qq; if (r) *r = x;
}
static void pgcd(poly *g, const poly *a, const poly *b) {
  poly x = *a, y = *b, r;
  while (y.d >= 0) { if (x.d < y.d) { poly t = x; x = y; y = t; continue; } pdivmod(NULL, &r, &x, &y); x = y; y = r; }
  if (x.d >= 0) { u64 iv = inv(x.c[x.d]); for (int i = 0; i <= x.d; i++) x.c[i] = mul(x.c[i], iv); }
  *g = x;
}
static u64 peval(const poly *a, u64 x) { u64 v = 0; for (int i = a->d; i >= 0; i--) v = mul(v, x) ^ a->c[i]; return v; }

// rational function num/den: reduce, degree, nu, period mask (bit a set iff a is a period; bit 0 always)
typedef struct { int deg, nu; unsigned per; int npi; poly p, q; } rat;
static void rat_make(rat *r, const poly *num, const poly *den) {
  poly g; pgcd(&g, num, den);
  pdivmod(&r->p, NULL, num, &g); pdivmod(&r->q, NULL, den, &g);
  r->deg = r->p.d > r->q.d ? r->p.d : r->q.d;
  r->nu = 0; r->per = 0;
  if (r->deg == 0) { r->per = n == 32 ? ~0u : (1u << n) - 1; r->npi = n; return; }
  for (int x = 0; x < n; x++) { u64 a = peval(&r->p, pts[x]), b = peval(&r->q, pts[x]); if (!a || !b || a == b) r->nu++; }
  u64 lr = 0x243f6a8885a308d3ull ^ r->p.c[0] ^ (r->q.c[0] << 1) ^ ((u64)r->deg << 40); if (!lr) lr = 1;
  for (int a = 0; a < n; a++) {
    int ok = 1;
    for (int tr = 0; tr < 2 && ok; tr++) { u64 y = (lr ^= lr << 13, lr ^= lr >> 7, lr ^= lr << 17, lr); if (mul(peval(&r->p, y ^ pts[a]), peval(&r->q, y)) != mul(peval(&r->p, y), peval(&r->q, y ^ pts[a]))) ok = 0; }
    if (ok) r->per |= 1u << a;
  }
  r->npi = __builtin_popcount(r->per);
}

typedef struct {
  int degenerate;      // two members equal
  int gam, gamD;       // deg G, roots of G in D
  int delta, I;        // degree of the curve, incidences at the points of D off the roots of G
  int npair, ntrip, ndbl; // points of D (off G) where exactly one pair coincides, three coincide, two disjoint pairs coincide
  rat f[5];            // f[l], l < 4: triple function with member l omitted; f[4]: cross-ratio of the four
  rat z[3];            // opposite ratios (c0-c1)/(c2-c3), (c0-c2)/(c1-c3), (c0-c3)/(c1-c2)
  int wdef;            // 2 delta - 2 - deg(Xi x Xi'): ramification of the curve at infinity
  int summ;            // sum of mtrip
  int mtrip[4];        // degree of the gcd of the differences of the triple omitting l (after removing G)
  unsigned perXi; int npiXi;
  int exc, flag;       // exc = I - (3 delta + 2); flag = (max_Q |Pi_Q| - 1) + (|Pi_Xi| - 1)
  poly v[4];
} info4;

static void analyse4(const poly u[3], info4 *o) {
  poly G, t; pgcd(&t, &u[0], &u[1]); pgcd(&G, &t, &u[2]);
  o->degenerate = 0;
  if (u[0].d < 0 || u[1].d < 0 || u[2].d < 0) { o->degenerate = 1; return; }
  pzero(&o->v[0]);
  for (int i = 0; i < 3; i++) pdivmod(&o->v[i + 1], NULL, &u[i], &G);
  poly dd[4][4];
  for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) { padd(&dd[i][j], &o->v[i], &o->v[j]); dd[j][i] = dd[i][j]; if (dd[i][j].d < 0) { o->degenerate = 1; return; } }
  o->gam = G.d; o->gamD = 0; o->delta = 0; o->I = 0; o->npair = o->ntrip = o->ndbl = 0;
  for (int i = 1; i < 4; i++) if (o->v[i].d > o->delta) o->delta = o->v[i].d;
  for (int x = 0; x < n; x++) {
    if (!peval(&G, pts[x])) { o->gamD++; continue; }
    u64 val[4]; val[0] = 0; for (int i = 1; i < 4; i++) val[i] = peval(&o->v[i], pts[x]);
    int eq = 0; for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) eq += val[i] == val[j];
    // eq = 0: free; 1: one pair; 2: two disjoint pairs; 3: a triple; 6: all four (impossible off G)
    if (eq == 1) { o->I += 1; o->npair++; } else if (eq == 2) { o->I += 2; o->ndbl++; } else if (eq == 3) { o->I += 2; o->ntrip++; } else if (eq == 6) o->I += 3;
  }
  for (int l = 0; l < 4; l++) {
    int a = (l + 1) & 3, b = (l + 2) & 3, c = (l + 3) & 3;
    poly g; pgcd(&g, &dd[a][b], &dd[a][c]); o->mtrip[l] = g.d;
    rat_make(&o->f[l], &dd[a][b], &dd[a][c]);
  }
  poly nu, de; pmul(&nu, &dd[0][1], &dd[2][3]); pmul(&de, &dd[0][2], &dd[1][3]);
  rat_make(&o->f[4], &nu, &de);
  rat_make(&o->z[0], &dd[0][1], &dd[2][3]); rat_make(&o->z[1], &dd[0][2], &dd[1][3]); rat_make(&o->z[2], &dd[0][3], &dd[1][2]);
  { int dw = -1; for (int a = 1; a < 4; a++) for (int b = a + 1; b < 4; b++) { poly da, db, t1, t2, w; da.d = o->v[a].d - 1; for (int i = 1; i <= o->v[a].d; i++) da.c[i - 1] = (i & 1) ? o->v[a].c[i] : 0; pnorm(&da);
      db.d = o->v[b].d - 1; for (int i = 1; i <= o->v[b].d; i++) db.c[i - 1] = (i & 1) ? o->v[b].c[i] : 0; pnorm(&db);
      pmul(&t1, &o->v[a], &db); pmul(&t2, &o->v[b], &da); padd(&w, &t1, &t2); if (w.d > dw) dw = w.d; }
    o->wdef = dw < 0 ? 99 : 2 * o->delta - 2 - dw; }
  o->summ = o->mtrip[0] + o->mtrip[1] + o->mtrip[2] + o->mtrip[3];
  o->perXi = o->f[3].per & o->f[2].per; o->npiXi = __builtin_popcount(o->perXi);
  int mx = 0; for (int q = 0; q < 5; q++) if (o->f[q].npi > mx) mx = o->f[q].npi;
  o->exc = o->I - (3 * o->delta + 2);
  o->flag = (mx - 1) + (o->npiXi - 1);
}

// histogram of text keys
#define MAXKEY 4000
static char hkey[MAXKEY][200]; static double hcnt[MAXKEY]; static long hraw[MAXKEY]; static int nkey = 0;
static void hadd(const char *key, double w) {
  for (int i = 0; i < nkey; i++) if (!strcmp(hkey[i], key)) { hcnt[i] += w; hraw[i]++; return; }
  if (nkey == MAXKEY) { fprintf(stderr, "too many keys\n"); exit(1); }
  strcpy(hkey[nkey], key); hcnt[nkey] = w; hraw[nkey] = 1; nkey++;
}
static int cmpi(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }
// key: delta gam I | Pi_Xi | sorted triples (deg,nu,pi) | Phi (deg,nu,pi)
static void key4(const info4 *o, char *s) {
  int tr[4]; for (int l = 0; l < 4; l++) tr[l] = o->f[l].deg * 10000 + o->f[l].nu * 100 + o->f[l].npi;
  qsort(tr, 4, sizeof(int), cmpi);
  int p = sprintf(s, "delta=%d gam=%d I=%d exc=%d flag=%d | pts pair=%d trip=%d dbl=%d | PiXi=%d | triples", o->delta, o->gam, o->I, o->exc, o->flag, o->npair, o->ntrip, o->ndbl, o->npiXi);
  for (int l = 0; l < 4; l++) p += sprintf(s + p, " (%d,%d,%d)", tr[l] / 10000, tr[l] / 100 % 100, tr[l] % 100);
  p += sprintf(s + p, " | Phi (%d,%d,%d)", o->f[4].deg, o->f[4].nu, o->f[4].npi);
  int zz[3]; for (int l = 0; l < 3; l++) zz[l] = o->z[l].deg * 100 + o->z[l].npi; qsort(zz, 3, sizeof(int), cmpi);
  sprintf(s + p, " | opp (%d,%d) (%d,%d) (%d,%d) | wdef=%d summ=%d", zz[0] / 100, zz[0] % 100, zz[1] / 100, zz[1] % 100, zz[2] / 100, zz[2] % 100, o->wdef, o->summ);
}
static int cmpkey(const void *a, const void *b) { return strcmp(hkey[*(const int *)a], hkey[*(const int *)b]); }
static void hprint(void) {
  int *ord = malloc(nkey * sizeof(int)); for (int i = 0; i < nkey; i++) ord[i] = i;
  qsort(ord, nkey, sizeof(int), cmpkey);
  for (int i = 0; i < nkey; i++) printf("%12.1f %9ld  %s\n", hcnt[ord[i]], hraw[ord[i]], hkey[ord[i]]);
  free(ord);
}
#endif
