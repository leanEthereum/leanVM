// Researcher 18. Exact maximum list size over ALL words, Reed-Solomon code of degree < k on a 16-point F_2-subspace D.
//
// Syndrome form. With s_i = sum_{a in D} w(a) a^i, i < M = n - k (on a subspace the column multipliers are constant),
// a codeword agrees with w outside a set E iff s lies in U_E = span{(a^i)_i : a in E} iff the functional s kills
// x^l Z_E(x) for l < m = M - |E|. So the list of w at agreement T is the set of e-sets E, e = n - T, with s in U_E
// (counted by their exact error supports), and Lambda(T) is the largest number of U_E through one point of P^{M-1}.
//
// Search. Depth first over chains E_0, E_1, ... that cut the space I of admissible syndromes down, with
//   - the first two members taken up to the symmetry group (AGL(4,2) on a generic domain, translations on the
//     real shape), and every later member X restricted to pairs (Y, X) of a class not treated before;
//   - at a node with space I: a candidate X is free (I inside U_X), dead (I meets U_X in 0), a point (one point of
//     P(I)), or a subspace. Points are hashed, so a node whose candidates are all points is settled without branching;
//     only subspace candidates are branched on, in index order;
//   - the bound "members so far + live candidates" prunes.
// Every count that matters is recomputed exactly at a concrete syndrome (distinct error supports), so the reported
// maximum is exact for the domain and field of the run. All extremal families are kept and classified up to symmetry.
//
// usage: 18_exhaust k T dom seed threads [target [r]]
//   dom = rand (random basis in GF(2^64), symmetry AGL(4,2)) | real64, real10, real11, real12, ... (span(1,x,x^2,x^3)
//   in GF(2^m), symmetry: translations). target: start value of the pruning threshold (default 1).
//   r: restrict to words that are polynomials of degree <= T + r modulo codewords (phantom degree <= r).
// build: cc -O2 -mcpu=native -o 18_exhaust 18_exhaust.c -lpthread
#include "18_gf.h"
#include <pthread.h>
#include <stdatomic.h>

#define N 16
#define MAXD 16
#define MAXROWS 32
#define MAXDEPTH 12
#define MAXFAM 256
#define RECMAX 200000

static int K, T, EE, MM, MD, CAP, OSC = -1; // e = n - T, m = T - k, M = n - k, CAP = max |E cap E'| for distinct members
static u64 pt[N];
static int ns;
static uint16_t *smask;
static int idxof[65536];
static u64 *loc;
#define LOC(i) (loc + (size_t)(i) * (EE + 1))

// ---------- symmetry ----------
static int ng;
static uint8_t (*G)[N];
static int norb, *orb, *orbrep;
static uint8_t (*tr)[N];        // tr[X]: permutation taking X to the representative of its orbit
static int *stabn; static uint8_t (**stab)[N];
static uint16_t **sto;          // sto[o][X]: orbit id of X under Stab(rep_o)
static int *nsto, **storep;

static inline unsigned ap(const uint8_t *p, unsigned mask) {
  unsigned r = 0;
  while (mask) { int b = __builtin_ctz(mask); mask &= mask - 1; r |= 1u << p[b]; }
  return r;
}
static void build_group(int full) {
  if (!full) {
    ng = 16; G = malloc(16 * N);
    for (int t = 0; t < 16; t++) for (int x = 0; x < 16; x++) G[t][x] = x ^ t;
    return;
  }
  G = malloc((size_t)322560 * N); ng = 0;
  for (int c0 = 1; c0 < 16; c0++) for (int c1 = 1; c1 < 16; c1++) for (int c2 = 1; c2 < 16; c2++) for (int c3 = 1; c3 < 16; c3++) {
    int c[4] = {c0, c1, c2, c3}, img[16], ok = 1;
    for (int x = 0; x < 16 && ok; x++) { int y = 0; for (int i = 0; i < 4; i++) if (x >> i & 1) y ^= c[i]; img[x] = y; if (x && !y) ok = 0; }
    if (!ok) continue;
    for (int t = 0; t < 16; t++) { for (int x = 0; x < 16; x++) G[ng][x] = img[x] ^ t; ng++; }
  }
}
static int uf_find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }
static void build_orbits(void) {
  orb = malloc(ns * sizeof(int)); tr = malloc((size_t)ns * N);
  for (int i = 0; i < ns; i++) orb[i] = -1;
  norb = 0; orbrep = NULL; stabn = NULL; stab = NULL;
  int *par = malloc(ns * sizeof(int));
  sto = NULL; nsto = NULL; storep = NULL;
  for (int i = 0; i < ns; i++) {
    if (orb[i] >= 0) continue;
    int o = norb++;
    orbrep = realloc(orbrep, norb * sizeof(int)); stabn = realloc(stabn, norb * sizeof(int));
    stab = realloc(stab, norb * sizeof(*stab)); sto = realloc(sto, norb * sizeof(*sto));
    nsto = realloc(nsto, norb * sizeof(int)); storep = realloc(storep, norb * sizeof(*storep));
    orbrep[o] = i; stabn[o] = 0; stab[o] = NULL; int cap = 0;
    for (int g = 0; g < ng; g++) {
      int y = idxof[ap(G[g], smask[i])];
      if (orb[y] < 0) { orb[y] = o; for (int x = 0; x < N; x++) tr[y][G[g][x]] = x; }
      if (y == i) {
        if (stabn[o] == cap) { cap = cap ? 2 * cap : 16; stab[o] = realloc(stab[o], (size_t)cap * N); }
        memcpy(stab[o][stabn[o]++], G[g], N);
      }
    }
    // orbits of the stabilizer on all sets
    for (int x = 0; x < ns; x++) par[x] = x;
    for (int h = 0; h < stabn[o]; h++) {
      uint16_t lo[256], hi[256];
      for (int b = 0; b < 256; b++) { lo[b] = ap(stab[o][h], b); hi[b] = ap(stab[o][h], b << 8); }
      for (int x = 0; x < ns; x++) {
        int y = idxof[lo[smask[x] & 255] | hi[smask[x] >> 8]];
        int a = uf_find(par, x), b = uf_find(par, y);
        if (a != b) { if (a < b) par[b] = a; else par[a] = b; }
      }
    }
    sto[o] = malloc(ns * sizeof(uint16_t)); storep[o] = malloc(ns * sizeof(int)); nsto[o] = 0;
    for (int x = 0; x < ns; x++) {
      int r = uf_find(par, x);
      if (r == x) { sto[o][x] = nsto[o]; storep[o][nsto[o]++] = x; } else sto[o][x] = sto[o][r];
    }
  }
  free(par);
}

// ---------- linear algebra ----------
// Fraction-free Gauss-Jordan on A (rows x d, destroyed). Returns the rank; Kb gets a basis of the kernel, (d - r) x d.
static int kern(u64 *A, int rows, int d, u64 *Kb) {
  int pc[MAXD], isp[MAXD], r = 0;
  memset(isp, 0, sizeof isp);
  for (int c = 0; c < d && r < rows; c++) {
    int p = -1;
    for (int i = r; i < rows; i++) if (A[i * d + c]) { p = i; break; }
    if (p < 0) continue;
    if (p != r) for (int j = 0; j < d; j++) { u64 t = A[p * d + j]; A[p * d + j] = A[r * d + j]; A[r * d + j] = t; }
    u64 pv = A[r * d + c];
    for (int i = 0; i < rows; i++) {
      if (i == r) continue;
      u64 f = A[i * d + c];
      if (!f) continue;
      for (int j = 0; j < d; j++) A[i * d + j] = gf_mul(A[i * d + j], pv) ^ gf_mul(A[r * d + j], f);
    }
    pc[r] = c; isp[c] = 1; r++;
  }
  if (!Kb) return r;
  u64 pre[MAXD + 1], suf[MAXD + 1];
  pre[0] = 1; for (int i = 0; i < r; i++) pre[i + 1] = gf_mul(pre[i], A[i * d + pc[i]]);
  suf[r] = 1; for (int i = r - 1; i >= 0; i--) suf[i] = gf_mul(suf[i + 1], A[i * d + pc[i]]);
  int t = 0;
  for (int f = 0; f < d; f++) {
    if (isp[f]) continue;
    u64 *v = Kb + (size_t)t * d;
    memset(v, 0, d * sizeof(u64));
    v[f] = pre[r];
    for (int i = 0; i < r; i++) if (A[i * d + f]) v[pc[i]] = gf_mul(A[i * d + f], gf_mul(pre[i], suf[i + 1]));
    t++;
  }
  return r;
}
// exact error support of the member E (set index x) at the syndrome s: the points a of E with s(Z_{E minus a}) != 0
static unsigned support(int x, const u64 *s) {
  const u64 *sg = LOC(x);
  unsigned mask = smask[x], sup = 0;
  u64 q[MAXD];
  while (mask) {
    int a = __builtin_ctz(mask); mask &= mask - 1;
    q[EE - 1] = 1;
    for (int j = EE - 1; j >= 1; j--) q[j - 1] = sg[j] ^ gf_mul(pt[a], q[j]);
    if (gf_dot(q, s, EE)) sup |= 1u << a;
  }
  return sup;
}
static inline int member(int x, const u64 *s) {
  const u64 *sg = LOC(x);
  for (int l = 0; l < MD; l++) if (gf_dot(sg, s + l, EE) ^ s[l + EE]) return 0;
  return 1;
}
static int cmp16(const void *a, const void *b) { return (int)*(const uint16_t *)a - (int)*(const uint16_t *)b; }
// full list at s: distinct error supports over all e-sets; fam gets the agreement sets (complements), sorted
static int full_list(const u64 *s, uint16_t *fam) {
  int L = 0;
  for (int x = 0; x < ns; x++) {
    if (!member(x, s)) continue;
    uint16_t S = (uint16_t)~support(x, s);
    int dup = 0;
    for (int i = 0; i < L; i++) if (fam[i] == S) { dup = 1; break; }
    if (!dup) { if (L == MAXFAM) { fprintf(stderr, "family too large\n"); exit(1); } fam[L++] = S; }
  }
  qsort(fam, L, sizeof(uint16_t), cmp16);
  return L;
}

// ---------- records ----------
typedef struct { int L; uint16_t fam[MAXFAM]; u64 s[MAXD]; } rec_t;
static rec_t *recs; static size_t nrec, caprec, rec_over;
#define HBITS 20
static uint32_t *rhash; // open addressing on a hash of the family, value = record index + 1
static pthread_mutex_t rec_mu = PTHREAD_MUTEX_INITIALIZER;
static _Atomic int target;
static _Atomic long n_nodes, n_cand, n_oracle;

static void record(const u64 *s) {
  uint16_t fam[MAXFAM];
  int L = full_list(s, fam);
  atomic_fetch_add(&n_oracle, 1);
  if (L < atomic_load(&target)) return;
  pthread_mutex_lock(&rec_mu);
  if (!rhash) rhash = calloc((size_t)1 << HBITS, sizeof(uint32_t));
  if (L > atomic_load(&target)) { atomic_store(&target, L); nrec = 0; rec_over = 0; memset(rhash, 0, sizeof(uint32_t) << HBITS); }
  if (L == atomic_load(&target)) {
    u64 h = 0x243f6a8885a308d3ull;
    for (int i = 0; i < L; i++) { h ^= fam[i]; h *= 0x9e3779b97f4a7c15ull; h ^= h >> 31; }
    size_t slot = h >> (64 - HBITS); int dup = 0;
    while (rhash[slot]) {
      if (!memcmp(recs[rhash[slot] - 1].fam, fam, L * sizeof(uint16_t))) { dup = 1; break; }
      slot = (slot + 1) & (((size_t)1 << HBITS) - 1);
    }
    if (!dup) {
      if (nrec >= RECMAX) rec_over++;
      else {
        if (nrec == caprec) { caprec = caprec ? 2 * caprec : 256; recs = realloc(recs, caprec * sizeof(rec_t)); }
        recs[nrec].L = L; memcpy(recs[nrec].fam, fam, L * sizeof(uint16_t)); memcpy(recs[nrec].s, s, MM * sizeof(u64)); nrec++;
        rhash[slot] = (uint32_t)nrec;
      }
    }
  }
  pthread_mutex_unlock(&rec_mu);
}

// ---------- search ----------
typedef struct {
  int o, j;                    // current pair class
  int mem[4096], nmem;         // chain and free members
  int *cand[MAXDEPTH], *pidx[MAXDEPTH], *subs[MAXDEPTH];
  u64 *pvec[MAXDEPTH];
  u64 *pkey[MAXDEPTH], *pinv[MAXDEPTH];
  int *ord[MAXDEPTH];
  u64 rs;
} tc_t;

static inline u64 trand(tc_t *tc) { u64 z = (tc->rs += 0x9e3779b97f4a7c15ull); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull; z = (z ^ (z >> 27)) * 0x94d049bb133111ebull; return (z ^ (z >> 31)) & FMASK; }

// may X join a list that contains E, given that pairs of a class below (o, j) are excluded?
static inline int allowed(const tc_t *tc, int E, int X) {
  if (__builtin_popcount(smask[E] & smask[X]) > CAP) return 0;
  const uint16_t *st = sto[tc->o];
  if (orb[E] == tc->o && st[idxof[ap(tr[E], smask[X])]] < tc->j) return 0;
  if (orb[X] == tc->o && st[idxof[ap(tr[X], smask[E])]] < tc->j) return 0;
  return 1;
}
// number of distinct error supports among the members mem[0..nmem) and extra[0..nx) at s
static int local_count(tc_t *tc, const u64 *s, const int *extra, int nx) {
  unsigned sup[4096 + 64]; int c = 0;
  for (int i = 0; i < tc->nmem + nx && c < 4096; i++) {
    int x = i < tc->nmem ? tc->mem[i] : extra[i - tc->nmem];
    unsigned u = support(x, s);
    int dup = 0;
    for (int t = 0; t < c; t++) if (sup[t] == u) { dup = 1; break; }
    if (!dup) sup[c++] = u;
  }
  return c;
}
static void restricted(const u64 *B, int d, int x, u64 *A) { // A[l*d + i] = (x^l Z_E)(B_i)
  const u64 *sg = LOC(x);
  for (int l = 0; l < MD; l++) for (int i = 0; i < d; i++) A[l * d + i] = gf_dot(sg, B + i * MM + l, EE) ^ B[i * MM + l + EE];
}
typedef struct { u64 key; int i; } ks_t;
static int cmpks(const void *a, const void *b) { u64 x = ((const ks_t *)a)->key, y = ((const ks_t *)b)->key; return x < y ? -1 : x > y; }

static void node(tc_t *tc, int depth, const u64 *B, int d, const int *cand, int nc) {
  if (depth >= MAXDEPTH) { fprintf(stderr, "depth overflow\n"); exit(1); }
  int base = tc->nmem;
  int *pidx = tc->pidx[depth], *subs = tc->subs[depth];
  u64 *pvec = tc->pvec[depth];
  int np = 0, nsb = 0;
  u64 A[MAXROWS * MAXD], Kb[MAXD * MAXD];
  atomic_fetch_add(&n_nodes, 1);
  atomic_fetch_add(&n_cand, nc);
  for (int ci = 0; ci < nc; ci++) {
    int x = cand[ci];
    const u64 *sg = LOC(x);
    if (d == 2) {
      u64 a0 = gf_dot(sg, B, EE) ^ B[EE], b0 = gf_dot(sg, B + MM, EE) ^ B[MM + EE], a = a0, b = b0;
      int dead = 0;
      for (int l = 1; l < MD; l++) {
        u64 a1 = gf_dot(sg, B + l, EE) ^ B[l + EE], b1 = gf_dot(sg, B + MM + l, EE) ^ B[MM + l + EE];
        if (!(a | b)) { a = a1; b = b1; continue; }
        if (gf_mul(a, b1) != gf_mul(a1, b)) { dead = 1; break; }
      }
      if (dead) continue;
      if (!(a | b)) { tc->mem[tc->nmem++] = x; continue; }
      pidx[np] = x; pvec[2 * np] = b; pvec[2 * np + 1] = a; np++; // kernel of (a, b): (b, a)
      continue;
    }
    restricted(B, d, x, A);
    int r = kern(A, MD, d, d - 1 <= MD ? Kb : NULL);
    if (r == d) continue;
    if (r == 0) { if (tc->nmem >= 4000) { fprintf(stderr, "member overflow\n"); exit(1); } tc->mem[tc->nmem++] = x; continue; }
    if (r == d - 1) { pidx[np] = x; memcpy(pvec + (size_t)np * d, Kb, d * sizeof(u64)); np++; }
    else subs[nsb++] = x;
  }
  int thr = atomic_load(&target);
  if (tc->nmem + np + nsb < thr) { tc->nmem = base; return; }
  if (tc->nmem >= thr) { // a generic point of I
    u64 s[MAXD];
    memset(s, 0, sizeof s);
    for (int i = 0; i < d; i++) { u64 c = trand(tc) | 1; for (int j = 0; j < MM; j++) s[j] ^= gf_mul(c, B[i * MM + j]); }
    if (local_count(tc, s, NULL, 0) >= thr) record(s);
  }
  if (np && tc->nmem + 1 >= thr - np) {
    // normalise the points (first nonzero coordinate 1), hash, group
    ks_t *ks = (ks_t *)tc->pkey[depth];
    u64 *pre = tc->pinv[depth]; // batch inversion of the leading coordinates
    u64 acc = 1;
    for (int i = 0; i < np; i++) { const u64 *v = pvec + (size_t)i * d; int f = 0; while (!v[f]) f++; pre[i] = acc; acc = gf_mul(acc, v[f]); }
    acc = gf_inv(acc);
    for (int i = np - 1; i >= 0; i--) {
      u64 *v = pvec + (size_t)i * d;
      int f = 0; while (!v[f]) f++;
      u64 iv = gf_mul(acc, pre[i]); acc = gf_mul(acc, v[f]);
      for (int j = f; j < d; j++) v[j] = gf_mul(v[j], iv);
    }
    for (int i = 0; i < np; i++) {
      u64 *v = pvec + (size_t)i * d;
      u64 h = 0x243f6a8885a308d3ull;
      for (int j = 0; j < d; j++) { h ^= v[j]; h *= 0x9e3779b97f4a7c15ull; h ^= h >> 29; }
      ks[i].key = h; ks[i].i = i;
    }
    qsort(ks, np, sizeof(ks_t), cmpks);
    for (int i = 0; i < np;) {
      int j = i; while (j < np && ks[j].key == ks[i].key) j++;
      if (tc->nmem + (j - i) >= thr) {
        int extra[64], nx = 0;
        for (int t = i; t < j && nx < 64; t++) extra[nx++] = pidx[ks[t].i];
        const u64 *v = pvec + (size_t)ks[i].i * d;
        u64 s[MAXD];
        memset(s, 0, sizeof s);
        for (int c = 0; c < d; c++) if (v[c]) for (int q = 0; q < MM; q++) s[q] ^= gf_mul(v[c], B[c * MM + q]);
        if (local_count(tc, s, extra, nx) >= thr) record(s);
        thr = atomic_load(&target);
      }
      i = j;
    }
  }
  // branch on the subspace candidates
  int *child = tc->cand[depth + 1];
  u64 Bc[MAXD * MAXD];
  for (int a = 0; a < nsb; a++) {
    thr = atomic_load(&target);
    if (tc->nmem + 1 + np + (nsb - a - 1) < thr) break;
    int x = subs[a];
    restricted(B, d, x, A);
    int r = kern(A, MD, d, Kb), dc = d - r;
    for (int t = 0; t < dc; t++) for (int q = 0; q < MM; q++) {
      u64 acc = 0;
      for (int c = 0; c < d; c++) if (Kb[t * d + c]) acc ^= gf_mul(Kb[t * d + c], B[c * MM + q]);
      Bc[t * MM + q] = acc;
    }
    int ncc = 0;
    for (int i = 0; i < np; i++) if (allowed(tc, x, pidx[i])) child[ncc++] = pidx[i];
    for (int b = a + 1; b < nsb; b++) if (allowed(tc, x, subs[b])) child[ncc++] = subs[b];
    tc->mem[tc->nmem++] = x;
    node(tc, depth + 1, Bc, dc, child, ncc);
    tc->nmem--;
  }
  tc->nmem = base;
}

typedef struct { int o, j; } task_t;
static task_t *tasks; static int ntasks; static _Atomic int next_task;
static int PROGRESS;

static void run_task(tc_t *tc, int o, int j) {
  int E0 = orbrep[o], E1 = storep[o][j];
  tc->o = o; tc->j = j; tc->nmem = 0;
  u64 A[MAXROWS * MAXD], B[MAXD * MAXD];
  memset(A, 0, sizeof A);
  for (int l = 0; l < MD; l++) for (int c = 0; c <= EE; c++) { A[l * MM + l + c] = LOC(E0)[c]; A[(MD + l) * MM + l + c] = LOC(E1)[c]; }
  int extra = 0;
  if (OSC >= 0) for (int i = 0; i < EE - 1 - OSC; i++) { A[(2 * MD + extra) * MM + i] = 1; extra++; } // degree <= T + OSC
  int r = kern(A, 2 * MD + extra, MM, B), d = MM - r;
  if (d <= 0) return;
  tc->mem[tc->nmem++] = E0; tc->mem[tc->nmem++] = E1;
  int *cand = tc->cand[0], nc = 0;
  for (int x = 0; x < ns; x++) {
    if (x == E0 || x == E1 || orb[x] < o) continue;
    if (!allowed(tc, E0, x) || !allowed(tc, E1, x)) continue;
    cand[nc++] = x;
  }
  node(tc, 0, B, d, cand, nc);
}
static void *worker(void *arg) {
  tc_t *tc = arg;
  for (;;) {
    int t = atomic_fetch_add(&next_task, 1);
    if (t >= ntasks) break;
    run_task(tc, tasks[t].o, tasks[t].j);
    if (PROGRESS && t % PROGRESS == 0) fprintf(stderr, "task %d of %d done, target %d, nodes %ld\n", t, ntasks, atomic_load(&target), atomic_load(&n_nodes));
  }
  return NULL;
}

// ---------- classification of the extremal families ----------
static int cmpfam(const uint16_t *a, const uint16_t *b, int L) { for (int i = 0; i < L; i++) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1; return 0; }
static void canon(const uint16_t *fam, int L, int full, uint16_t *out) {
  // smallest sorted image under the group. Uses the members of size exactly T (their complements are indexed sets).
  int omin = 1 << 30;
  for (int i = 0; i < L; i++) if (__builtin_popcount(fam[i]) == T) { int o = orb[idxof[(uint16_t)~fam[i]]]; if (o < omin) omin = o; }
  uint16_t cur[MAXFAM], f1[MAXFAM]; int have = 0;
  if (omin == 1 << 30 || !full) { // brute force over the whole group
    for (int g = 0; g < ng; g++) {
      for (int i = 0; i < L; i++) cur[i] = ap(G[g], fam[i]);
      qsort(cur, L, sizeof(uint16_t), cmp16);
      if (!have || cmpfam(cur, out, L) < 0) { memcpy(out, cur, L * sizeof(uint16_t)); have = 1; }
    }
    return;
  }
  for (int y = 0; y < L; y++) {
    if (__builtin_popcount(fam[y]) != T) continue;
    int Y = idxof[(uint16_t)~fam[y]];
    if (orb[Y] != omin) continue;
    for (int i = 0; i < L; i++) f1[i] = ap(tr[Y], fam[i]);
    for (int h = 0; h < stabn[omin]; h++) {
      for (int i = 0; i < L; i++) cur[i] = ap(stab[omin][h], f1[i]);
      qsort(cur, L, sizeof(uint16_t), cmp16);
      if (!have || cmpfam(cur, out, L) < 0) { memcpy(out, cur, L * sizeof(uint16_t)); have = 1; }
    }
  }
}
// structure of a word (syndrome s) with the family fam of agreement sets
static void analyze(const u64 *s, const uint16_t *fam, int L, const char *tag) {
  // leading zeros of s: the word is a polynomial of degree n - 1 - z modulo codewords
  int z = 0; while (z < MM && !s[z]) z++;
  // d1 = least j with a nonzero sigma of degree <= j killing the Hankel windows of s
  int d1 = -1; u64 g1[MAXD + 1];
  for (int j = 0; j <= MM && d1 < 0; j++) {
    int rows = MM - j, d = j + 1;
    if (rows <= 0) { d1 = j; memset(g1, 0, sizeof g1); g1[0] = 1; break; }
    u64 *A = calloc((size_t)rows * d, sizeof(u64)), Kb[(MAXD + 1) * (MAXD + 1)];
    for (int l = 0; l < rows; l++) for (int c = 0; c < d; c++) A[l * d + c] = s[l + c];
    int r = kern(A, rows, d, Kb);
    free(A);
    if (r < d) { d1 = j; memcpy(g1, Kb, d * sizeof(u64)); }
  }
  int degg = d1; while (degg > 0 && !g1[degg]) degg--;
  int rootsD = 0;
  {
    u64 q[MAXD + 2]; int dq = degg; memcpy(q, g1, (degg + 1) * sizeof(u64));
    for (int a = 0; a < N; a++) for (;;) {
      u64 v = 0; for (int c = dq; c >= 0; c--) v = gf_mul(v, pt[a]) ^ q[c];
      if (v || dq == 0) break;
      u64 carry = 0; for (int c = dq; c >= 0; c--) { u64 t = q[c] ^ gf_mul(carry, pt[a]); q[c] = carry; carry = t; }
      dq--; rootsD++;
    }
  }
  // per member: does the error evaluator Omega = (w - c)/Z_S (up to a constant) split over D?
  int split = 0;
  for (int i = 0; i < L; i++) {
    unsigned sup = (uint16_t)~fam[i]; int e = __builtin_popcount(sup);
    int pts_[N], c = 0; for (int a = 0; a < N; a++) if (sup >> a & 1) pts_[c++] = a;
    u64 om[MAXD + 2]; memset(om, 0, sizeof om);
    for (int t = 0; t < e; t++) { // y_a Z_{sup minus a}, y_a = s(Z_{sup minus a}) / Z_{sup minus a}(a)
      u64 q[MAXD + 2]; memset(q, 0, sizeof q); q[0] = 1; int dq = 0;
      for (int u = 0; u < e; u++) if (u != t) { for (int c2 = dq + 1; c2 >= 1; c2--) q[c2] = q[c2 - 1] ^ gf_mul(q[c2], pt[pts_[u]]); q[0] = gf_mul(q[0], pt[pts_[u]]); dq++; }
      u64 num = gf_dot(q, s, e), den = 0;
      for (int c2 = dq; c2 >= 0; c2--) den = gf_mul(den, pt[pts_[t]]) ^ q[c2];
      u64 y = gf_mul(num, gf_inv(den));
      for (int c2 = 0; c2 <= dq; c2++) om[c2] ^= gf_mul(y, q[c2]);
    }
    int dq = e - 1; while (dq > 0 && !om[dq]) dq--;
    int roots = 0, deg0 = dq;
    for (int a = 0; a < N; a++) for (;;) {
      u64 v = 0; for (int c2 = dq; c2 >= 0; c2--) v = gf_mul(v, pt[a]) ^ om[c2];
      if (v || dq == 0) break;
      u64 carry = 0; for (int c2 = dq; c2 >= 0; c2--) { u64 t2 = om[c2] ^ gf_mul(carry, pt[a]); om[c2] = carry; carry = t2; }
      dq--; roots++;
    }
    if (roots == deg0) split++;
  }
  printf("    %s: polynomial of degree %d modulo codewords (phantom degree %d); d1 = %d: %d roots at infinity, %d in D, %d elsewhere; (w - c)/Z_S splits over D for %d of %d members; type: %s\n",
         tag, N - 1 - z, N - 1 - z - T, d1, d1 - degg, rootsD, degg - rootsD, split, L,
         N - 1 - z == T ? "STRICT TOP" : split == L ? "MULTISET TOP" : "NOT A TOP");
  printf("      syndrome:"); for (int i = 0; i < MM; i++) printf(" %016llx", (unsigned long long)s[i]);
  // a word with this syndrome: the error vector of the first member
  {
    unsigned sup = (uint16_t)~fam[0]; int e = __builtin_popcount(sup);
    int pts_[N], c = 0; for (int a = 0; a < N; a++) if (sup >> a & 1) pts_[c++] = a;
    u64 w[N]; memset(w, 0, sizeof w);
    for (int t = 0; t < e; t++) {
      u64 q[MAXD + 2]; memset(q, 0, sizeof q); q[0] = 1; int dq = 0;
      for (int u = 0; u < e; u++) if (u != t) { for (int c2 = dq + 1; c2 >= 1; c2--) q[c2] = q[c2 - 1] ^ gf_mul(q[c2], pt[pts_[u]]); q[0] = gf_mul(q[0], pt[pts_[u]]); dq++; }
      u64 num = gf_dot(q, s, e), den = 0;
      for (int c2 = dq; c2 >= 0; c2--) den = gf_mul(den, pt[pts_[t]]) ^ q[c2];
      w[pts_[t]] = gf_mul(num, gf_inv(den));
    }
    printf("\n      WORD"); for (int a = 0; a < N; a++) printf(" %llx", (unsigned long long)w[a]);
  }
  printf("\n");
}
static void describe(const rec_t *R) {
  int L = R->L;
  int sizes[N + 1], ih[N + 1], deg[N];
  memset(sizes, 0, sizeof sizes); memset(ih, 0, sizeof ih); memset(deg, 0, sizeof deg);
  for (int i = 0; i < L; i++) sizes[__builtin_popcount(R->fam[i])]++;
  for (int i = 0; i < L; i++) for (int j = i + 1; j < L; j++) ih[__builtin_popcount(R->fam[i] & R->fam[j])]++;
  for (int i = 0; i < L; i++) for (int a = 0; a < N; a++) if (R->fam[i] >> a & 1) deg[a]++;
  printf("    sets:"); for (int i = 0; i < L; i++) printf(" %04x", R->fam[i]);
  printf("\n    agreement sizes:"); for (int a = 0; a <= N; a++) if (sizes[a]) printf(" %dx%d", sizes[a], a);
  printf("; pairwise intersections:"); for (int a = 0; a <= N; a++) if (ih[a]) printf(" %dx%d", ih[a], a);
  printf("; point degrees:"); for (int a = 0; a < N; a++) printf(" %d", deg[a]);
  printf("\n");
  // the space I_F of syndromes having every set of the family as an agreement set
  int rows = 0; for (int i = 0; i < L; i++) rows += MM - (N - __builtin_popcount(R->fam[i]));
  u64 *A0 = calloc((size_t)(rows + MM) * MM, sizeof(u64)), *A = malloc((size_t)(rows + MM) * MM * sizeof(u64)); int rr = 0;
  for (int i = 0; i < L; i++) {
    unsigned sup = (uint16_t)~R->fam[i]; int e = __builtin_popcount(sup);
    u64 q[MAXD + 2]; memset(q, 0, sizeof q); q[0] = 1; int dq = 0;
    for (int a = 0; a < N; a++) if (sup >> a & 1) { for (int c = dq + 1; c >= 1; c--) q[c] = q[c - 1] ^ gf_mul(q[c], pt[a]); q[0] = gf_mul(q[0], pt[a]); dq++; }
    for (int l = 0; l < MM - e; l++) { for (int c = 0; c <= e; c++) A0[rr * MM + l + c] = q[c]; rr++; }
  }
  memcpy(A, A0, (size_t)rr * MM * sizeof(u64));
  int dimI = MM - kern(A, rr, MM, NULL);
  printf("    words with this family: a space of projective dimension %d\n", dimI - 1);
  analyze(R->s, R->fam, L, "recorded word");
  // the lowest-degree word of I_F: add the conditions s_0 = ... = s_{z-1} = 0, largest z that leaves something
  for (int z = MM - 1; z >= 1; z--) {
    memcpy(A, A0, (size_t)rr * MM * sizeof(u64));
    memset(A + (size_t)rr * MM, 0, (size_t)z * MM * sizeof(u64));
    for (int i = 0; i < z; i++) A[(size_t)(rr + i) * MM + i] = 1;
    u64 Kb[MAXD * MAXD];
    int dk = MM - kern(A, rr + z, MM, Kb);
    if (dk <= 0) continue;
    u64 s[MAXD]; memset(s, 0, sizeof s);
    for (int t = 0; t < dk; t++) { u64 c = dk == 1 ? 1 : (gf_rand() | 1); for (int q = 0; q < MM; q++) s[q] ^= gf_mul(c, Kb[t * MM + q]); }
    uint16_t fam2[MAXFAM]; int L2 = full_list(s, fam2);
    printf("    lowest-degree words of the family: degree %d modulo codewords, a space of projective dimension %d; list of a generic one: %d%s\n",
           N - 1 - z, dk - 1, L2, L2 == L && !memcmp(fam2, R->fam, L * sizeof(uint16_t)) ? " (the same family)" : " (a different family)");
    analyze(s, fam2, L2, "lowest-degree word");
    break;
  }
  free(A); free(A0);
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: %s k T dom seed threads [target]\n", argv[0]); return 1; }
  K = atoi(argv[1]); T = atoi(argv[2]);
  const char *dom = argv[3];
  u64 seed = strtoull(argv[4], 0, 0);
  int nth = atoi(argv[5]);
  atomic_store(&target, argc > 6 ? atoi(argv[6]) : 1);
  if (argc > 7) OSC = atoi(argv[7]);            // only words that are polynomials of degree <= T + OSC modulo codewords
  if (getenv("PROGRESS")) PROGRESS = atoi(getenv("PROGRESS"));
  EE = N - T; MD = T - K; MM = N - K; CAP = 2 * EE - MM - 1;
  int full = !strcmp(dom, "rand");
  if (full) {
    gf_init(64);
    rng_state ^= seed * 0x2545f4914f6cdd1dull;
    for (;;) { // random independent basis
      u64 b[4]; for (int i = 0; i < 4; i++) b[i] = gf_rand();
      int ok = 1;
      for (int a = 0; a < N; a++) { pt[a] = 0; for (int i = 0; i < 4; i++) if (a >> i & 1) pt[a] ^= b[i]; if (a && !pt[a]) ok = 0; }
      if (ok) break;
    }
  } else {
    gf_init(atoi(dom + 4));
    for (int a = 0; a < N; a++) pt[a] = a;
  }
  printf("# n=16 k=%d T=%d e=%d m=%d  domain %s seed %llu  field GF(2^%d)  Johnson radius sqrt(n(k-1)) = %.3f\n", K, T, EE, MD, dom, (unsigned long long)seed, FM, __builtin_sqrt(16.0 * (K - 1)));
  if (OSC >= 0) printf("# restricted to words of degree <= %d modulo codewords\n", T + OSC);
  printf("PTS"); for (int a = 0; a < N; a++) printf(" %llx", (unsigned long long)pt[a]); printf("\n");
  if (MD < 1 || EE < 1) { printf("nothing to do\n"); return 0; }
  if (CAP < 0) { printf("RESULT k=%d T=%d dom=%s max=1 (unique decoding)\n", K, T, dom); return 0; }
  ns = 0; smask = malloc(65536 * sizeof(uint16_t));
  for (int mk = 0; mk < 65536; mk++) { idxof[mk] = -1; if (__builtin_popcount(mk) == EE) { idxof[mk] = ns; smask[ns++] = mk; } }
  loc = malloc((size_t)ns * (EE + 1) * sizeof(u64));
  for (int x = 0; x < ns; x++) {
    u64 *q = LOC(x); memset(q, 0, (EE + 1) * sizeof(u64)); q[0] = 1; int dq = 0;
    for (int a = 0; a < N; a++) if (smask[x] >> a & 1) { for (int c = dq + 1; c >= 1; c--) q[c] = q[c - 1] ^ gf_mul(q[c], pt[a]); q[0] = gf_mul(q[0], pt[a]); dq++; }
  }
  build_group(full);
  build_orbits();
  // tasks: pairs (rep of orbit o, rep of stabilizer orbit j), not equivalent to an earlier pair
  tasks = NULL; ntasks = 0; int captasks = 0;
  for (int o = 0; o < norb; o++) for (int j = 0; j < nsto[o]; j++) {
    int E0 = orbrep[o], X = storep[o][j];
    if (X == E0 || orb[X] < o || __builtin_popcount(smask[E0] & smask[X]) > CAP) continue;
    if (orb[X] == o && sto[o][idxof[ap(tr[X], smask[E0])]] < j) continue;
    if (ntasks == captasks) { captasks = captasks ? 2 * captasks : 1024; tasks = realloc(tasks, captasks * sizeof(task_t)); }
    tasks[ntasks].o = o; tasks[ntasks].j = j; ntasks++;
  }
  printf("# sets %d, group %d, orbits %d, pair classes %d\n", ns, ng, norb, ntasks);
  fflush(stdout);
  pthread_t th[64]; tc_t *tcs = calloc(nth, sizeof(tc_t));
  for (int t = 0; t < nth; t++) {
    tcs[t].rs = rnd64();
    for (int dpt = 0; dpt < MAXDEPTH; dpt++) {
      tcs[t].cand[dpt] = malloc(ns * sizeof(int)); tcs[t].pidx[dpt] = malloc(ns * sizeof(int)); tcs[t].subs[dpt] = malloc(ns * sizeof(int));
      tcs[t].pvec[dpt] = malloc((size_t)ns * MAXD * sizeof(u64)); tcs[t].pkey[dpt] = malloc((size_t)ns * sizeof(ks_t)); tcs[t].pinv[dpt] = malloc((size_t)ns * sizeof(u64));
    }
    pthread_create(&th[t], NULL, worker, &tcs[t]);
  }
  for (int t = 0; t < nth; t++) pthread_join(th[t], NULL);
  int best = atomic_load(&target);
  printf("# nodes %ld, candidate tests %ld, exact list evaluations %ld\n", atomic_load(&n_nodes), atomic_load(&n_cand), atomic_load(&n_oracle));
  if (!nrec) { printf("RESULT k=%d T=%d dom=%s: no list of size >= %d\n", K, T, dom, best); return 0; }
  // classes up to symmetry
  uint16_t (*cf)[MAXFAM] = malloc(nrec * sizeof(*cf));
  int *cls = malloc(nrec * sizeof(int)), ncls = 0, *crep = malloc(nrec * sizeof(int)), *ccount = malloc(nrec * sizeof(int));
  for (size_t i = 0; i < nrec; i++) {
    canon(recs[i].fam, best, full, cf[i]);
    cls[i] = -1;
    for (int c = 0; c < ncls; c++) if (!memcmp(cf[crep[c]], cf[i], best * sizeof(uint16_t))) { cls[i] = c; ccount[c]++; break; }
    if (cls[i] < 0) { cls[i] = ncls; crep[ncls] = (int)i; ccount[ncls] = 1; ncls++; }
  }
  printf("RESULT k=%d T=%d dom=%s max=%d families_found=%zu%s classes=%d\n", K, T, dom, best, nrec, rec_over ? "+" : "", ncls);
  for (int c = 0; c < ncls && c < 80; c++) {
    printf("  class %d (%d families found):\n", c, ccount[c]);
    describe(&recs[crep[c]]);
  }
  if (ncls > 80) printf("  ... %d more classes\n", ncls - 80);
  return 0;
}
