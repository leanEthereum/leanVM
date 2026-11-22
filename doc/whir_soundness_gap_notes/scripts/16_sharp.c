// Researcher 16: exact block statistics for the DEEP fold on toy fields (note 16).
//
// One lane. E = GF(2^m), D = {0..n-1} (the span of 1, x, .., x^(N-1)), words f0, f1 : D -> E, degree d, agreement A.
// T = {(c, P) : c = (alpha, beta) in E^2, deg P <= d, P agrees with f1 + (alpha + beta x) f0 on at least A points}.
// For points zeta_1..zeta_s and answers m = (yF_i, yG_i), the block W(m) is the set of elements with
// P(zeta_i) = yG_i + (alpha + beta zeta_i) yF_i for all i. The program finds, for every point tuple it is given,
// every block with at least kmin distinct challenges (exactly: all q^(2s) answer vectors are covered), and for each
// such block the largest class through a set of anchors (32 elements spread over the block) and whether that class is a near pair (a polynomial pair
// of degrees (d-1, d) agreeing with (f0, f1) on at least A-1 points).
//
// A point tuple is "exceptional" here if some block has at least k0 distinct challenges and no class holding
// 74 percent of it (the conclusion of note 07, Theorem 3, fails).
//
// Build: cc -O2 -o sharp16 16_sharp.c -lpthread
// Usage: ./sharp16 m=6 N=4 d=3 A=5 word=kpairs k=3 r=3 s=2 zmode=all [seed=1] [threads=4] [k0=..] [samples=..]
//   word = random | kpairs (k near pairs (F, G + R H_j), R of degree r with roots outside D)
//        | polek (pole pair over a word with k list members C_0 + R H_j of degree d+1)
//        | flatlist (f0 = F, f1 = G + x^(2d+1); use A = 2d+1)
//   zmode = all (every unordered tuple, s = 2 only) | uniform (samples uniform tuples)
//         | generic (samples tuples outside D, distinct, not roots of R)
//         | roots (s-1 coordinates run over the roots of R, the last over all of E)
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXQ 256
#define MAXN 32
#define MAXD 8
#define MAXS 3

static int FM, Q, NN, DEG, AGR, K0, KMIN, NTHREADS = 4;
static uint8_t MUL[MAXQ][MAXQ], INV[MAXQ];
static uint8_t F0[MAXN], F1[MAXN];
static int ROOTS[MAXD + 2], NROOTS;

typedef struct {
  uint32_t ch; // alpha * Q + beta
  uint8_t co[MAXD + 1];
} elem_t;
static elem_t *TT;
static int NT, CAPT;
static pthread_mutex_t MU = PTHREAD_MUTEX_INITIALIZER;

static uint64_t rng_s = 88172645463325252ull;
static uint64_t rnd(void) {
  rng_s ^= rng_s << 13;
  rng_s ^= rng_s >> 7;
  rng_s ^= rng_s << 17;
  return rng_s;
}
static int rq(void) { return (int)((rnd() >> 24) % (uint64_t)Q); }

static void gf_init(int m) {
  static const int irr[9] = {0, 0, 0, 0, 0, 0x25, 0x43, 0x83, 0x11B};
  FM = m;
  Q = 1 << m;
  for (int a = 0; a < Q; a++)
    for (int b = 0; b < Q; b++) {
      int r = 0, x = a, y = b;
      while (y) {
        if (y & 1) r ^= x;
        y >>= 1;
        x <<= 1;
        if (x & Q) x ^= irr[m];
      }
      MUL[a][b] = (uint8_t)r;
    }
  for (int a = 1; a < Q; a++)
    for (int b = 1; b < Q; b++)
      if (MUL[a][b] == 1) INV[a] = (uint8_t)b;
}

static inline int peval(const uint8_t *co, int deg, int x) {
  int r = co[deg];
  for (int i = deg - 1; i >= 0; i--) r = MUL[r][x] ^ co[i];
  return r;
}

// ---- lists of all folds: every (d+1)-subset, emitted once from the first d+1 agreement points ----
static int NSUB;
static uint8_t *SUB;  // NSUB * (d+1) points
static uint8_t *EVM;  // NSUB * (d+1) * n : value of the j-th Lagrange basis polynomial at each point
static uint8_t *COM;  // NSUB * (d+1) * (d+1) : its coefficients

static void build_subsets(void) {
  int k = DEG + 1, idx[MAXD + 1];
  long cnt = 1;
  for (int i = 0; i < k; i++) cnt = cnt * (NN - i) / (i + 1);
  NSUB = (int)cnt;
  SUB = malloc((size_t)NSUB * k);
  EVM = malloc((size_t)NSUB * k * NN);
  COM = malloc((size_t)NSUB * k * k);
  for (int i = 0; i < k; i++) idx[i] = i;
  for (int s = 0; s < NSUB; s++) {
    for (int i = 0; i < k; i++) SUB[s * k + i] = (uint8_t)idx[i];
    for (int j = 0; j < k; j++) {
      uint8_t po[MAXD + 2] = {1};
      int deg = 0, den = 1;
      for (int i = 0; i < k; i++) {
        if (i == j) continue;
        for (int t = deg + 1; t >= 1; t--) po[t] = (uint8_t)((t <= deg ? MUL[po[t]][idx[i]] : 0) ^ po[t - 1]);
        po[0] = MUL[po[0]][idx[i]];
        deg++;
        den = MUL[den][idx[j] ^ idx[i]];
      }
      int iv = INV[den];
      for (int t = 0; t < k; t++) COM[((size_t)s * k + j) * k + t] = MUL[po[t]][iv];
      for (int x = 0; x < NN; x++) EVM[((size_t)s * k + j) * NN + x] = (uint8_t)peval(&COM[((size_t)s * k + j) * k], DEG, x);
    }
    int p = k - 1;
    while (p >= 0 && idx[p] == NN - k + p) p--;
    if (p < 0) break;
    idx[p]++;
    for (int i = p + 1; i < k; i++) idx[i] = idx[i - 1] + 1;
  }
}

static volatile int NEXT_ALPHA;
static void *list_worker(void *arg) {
  (void)arg;
  int k = DEG + 1;
  elem_t *loc = malloc(sizeof(elem_t) * 4096);
  for (;;) {
    pthread_mutex_lock(&MU);
    int al = NEXT_ALPHA++;
    pthread_mutex_unlock(&MU);
    if (al >= Q) break;
    for (int be = 0; be < Q; be++) {
      uint8_t w[MAXN];
      int nl = 0;
      for (int x = 0; x < NN; x++) w[x] = (uint8_t)(F1[x] ^ MUL[al ^ MUL[be][x]][F0[x]]);
      for (int s = 0; s < NSUB; s++) {
        const uint8_t *sb = &SUB[s * k];
        const uint8_t *ev = &EVM[(size_t)s * k * NN];
        int agree = k, ok = 1, last = sb[k - 1], si = 0;
        for (int x = 0; x < NN && ok; x++) {
          if (si < k && sb[si] == x) {
            si++;
            continue;
          }
          int v = 0;
          for (int j = 0; j < k; j++) v ^= MUL[w[sb[j]]][ev[j * NN + x]];
          if (v == w[x]) {
            if (x < last) ok = 0; // not the first d+1 agreement points
            else agree++;
          }
        }
        if (!ok || agree < AGR) continue;
        elem_t e;
        memset(&e, 0, sizeof e);
        e.ch = (uint32_t)(al * Q + be);
        for (int t = 0; t < k; t++) {
          int v = 0;
          for (int j = 0; j < k; j++) v ^= MUL[w[sb[j]]][COM[((size_t)s * k + j) * k + t]];
          e.co[t] = (uint8_t)v;
        }
        if (nl < 4096) loc[nl++] = e;
      }
      pthread_mutex_lock(&MU);
      if (NT + nl > CAPT) {
        CAPT = 2 * (NT + nl) + 1024;
        TT = realloc(TT, sizeof(elem_t) * (size_t)CAPT);
      }
      memcpy(TT + NT, loc, sizeof(elem_t) * (size_t)nl);
      NT += nl;
      pthread_mutex_unlock(&MU);
    }
  }
  free(loc);
  return NULL;
}
static int elem_cmp(const void *x, const void *y) {
  const elem_t *a = x, *b = y;
  if (a->ch != b->ch) return a->ch < b->ch ? -1 : 1;
  return memcmp(a->co, b->co, MAXD + 1);
}
static void build_lists(void) {
  pthread_t th[16];
  build_subsets();
  NEXT_ALPHA = 0;
  for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, list_worker, NULL);
  for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);
  qsort(TT, (size_t)NT, sizeof(elem_t), elem_cmp);
}

// ---- near pairs and the unexplained part of T ----
// Near pairs: (F, G) with deg F <= d-1, deg G <= d, agreeing with (f0, f1) on at least A-1 common points.
// Returns their number; *unexpl receives the number of elements of T that lie in no near-pair class.
static int near_pairs(int *unexpl) {
  int k = DEG + 1, np = 0;
  uint8_t *mark = calloc((size_t)NT + 1, 1);
  int *first = malloc(sizeof(int) * ((size_t)Q * Q + 1));
  for (int c = 0, i = 0; c <= Q * Q; c++) {
    while (i < NT && (int)TT[i].ch < c) i++;
    first[c] = i;
  }
  for (int s = 0; s < NSUB; s++) {
    const uint8_t *sb = &SUB[s * k];
    uint8_t F[MAXD + 1] = {0}, G[MAXD + 1] = {0};
    for (int t = 0; t < k; t++)
      for (int j = 0; j < k; j++) {
        F[t] ^= MUL[F0[sb[j]]][COM[((size_t)s * k + j) * k + t]];
        G[t] ^= MUL[F1[sb[j]]][COM[((size_t)s * k + j) * k + t]];
      }
    if (F[DEG]) continue;
    int z = 0, ok = 1, si = 0;
    for (int x = 0; x < NN && ok; x++) {
      int in = peval(F, DEG, x) == F0[x] && peval(G, DEG, x) == F1[x];
      if (si < k && sb[si] == x) {
        si++;
        z++;
      } else if (in) {
        if (x < sb[k - 1]) ok = 0;
        else z++;
      }
    }
    if (!ok || z < AGR - 1) continue;
    np++;
    for (int al = 0; al < Q; al++)
      for (int be = 0; be < Q; be++) {
        uint8_t P[MAXD + 1];
        for (int t = 0; t <= DEG; t++) P[t] = (uint8_t)(G[t] ^ MUL[al][F[t]] ^ (t ? MUL[be][F[t - 1]] : 0));
        int c = al * Q + be;
        for (int i = first[c]; i < first[c + 1]; i++)
          if (!memcmp(TT[i].co, P, (size_t)k)) mark[i] = 1;
      }
  }
  int u = 0;
  for (int i = 0; i < NT; i++) u += !mark[i];
  *unexpl = u;
  free(mark);
  free(first);
  return np;
}

// ---- classes ----
typedef struct {
  uint8_t key[MAXD + 3];
} ckey_t;
static int key_cmp(const void *x, const void *y) { return memcmp(x, y, sizeof(ckey_t)); }

// the rational F of the class through e0 and e, in a canonical form
static void class_key(const elem_t *e0, const elem_t *e, ckey_t *k) {
  int da = (int)(e0->ch / Q) ^ (int)(e->ch / Q), db = (int)(e0->ch % Q) ^ (int)(e->ch % Q);
  uint8_t nu[MAXD + 1];
  memset(k, 0, sizeof *k);
  for (int t = 0; t <= DEG; t++) nu[t] = e0->co[t] ^ e->co[t];
  if (db == 0) { // F = N / da, a polynomial of degree at most d
    int iv = INV[da];
    k->key[0] = 0;
    for (int t = 0; t <= DEG; t++) k->key[2 + t] = MUL[nu[t]][iv];
    return;
  }
  int iv = INV[db], x0 = MUL[da][iv];
  for (int t = 0; t <= DEG; t++) nu[t] = MUL[nu[t]][iv];
  if (peval(nu, DEG, x0) == 0) { // divide by X + x0
    uint8_t qo[MAXD + 1] = {0};
    int carry = 0;
    for (int t = DEG; t >= 1; t--) {
      carry = nu[t] ^ MUL[carry][x0];
      qo[t - 1] = (uint8_t)carry;
    }
    k->key[0] = 0;
    for (int t = 0; t < DEG; t++) k->key[2 + t] = qo[t];
  } else {
    k->key[0] = 1;
    k->key[1] = (uint8_t)x0;
    for (int t = 0; t <= DEG; t++) k->key[2 + t] = nu[t];
  }
}

// is the class with polynomial F (key type 0) through e0 a near pair?
static int near_pair(const elem_t *e0, const ckey_t *k) {
  if (k->key[0] != 0 || k->key[2 + DEG] != 0) return 0;
  int al = (int)(e0->ch / Q), be = (int)(e0->ch % Q), z = 0;
  for (int x = 0; x < NN; x++) {
    int f = peval(&k->key[2], DEG, x);
    int g = peval(e0->co, DEG, x) ^ MUL[al ^ MUL[be][x]][f];
    if (f == F0[x] && g == F1[x]) z++;
  }
  return z >= AGR - 1;
}

typedef struct {
  int count, maxclass, maxnear, maxpole, nclass_big; // nclass_big: classes through the anchors with >= Q/2 elements
} blk_t;

// idx: all elements of a block (sorted by challenge, possibly several per challenge); n its number of distinct challenges.
// A class has at most one element per challenge, so class sizes are counted in challenges.
static blk_t analyse(const int *idx, int cnt, int n) {
  blk_t b = {n, 1, 0, 0, 0};
  ckey_t *ks = malloc(sizeof(ckey_t) * (size_t)(cnt + 1));
  int nanch = cnt < 32 ? cnt : 32;
  for (int a = 0; a < nanch; a++) {
    int ia = idx[(int)((long)a * cnt / nanch)], nk = 0;
    for (int i = 0; i < cnt; i++)
      if (TT[idx[i]].ch != TT[ia].ch) class_key(&TT[ia], &TT[idx[i]], &ks[nk++]);
    qsort(ks, (size_t)nk, sizeof(ckey_t), key_cmp);
    for (int i = 0; i < nk;) {
      int j = i;
      while (j < nk && !memcmp(&ks[i], &ks[j], sizeof(ckey_t))) j++;
      int sz = j - i + 1;
      if (sz > b.maxclass) b.maxclass = sz;
      if (sz >= 3) {
        if (near_pair(&TT[ia], &ks[i])) {
          if (sz > b.maxnear) b.maxnear = sz;
        } else if (ks[i].key[0] == 1 || ks[i].key[2 + DEG] != 0) {
          if (sz > b.maxpole) b.maxpole = sz;
        }
      }
      i = j;
    }
  }
  free(ks);
  return b;
}

// ---- blocks at a point tuple ----
typedef struct {
  int z[MAXS];
  int maxcount;      // largest block (distinct challenges)
  int maxunexp;      // largest block with no class holding 74 percent
  int maxunexp_cls;  // the largest class of that block
  int maxunexp_near; // its largest near-pair class
  int maxunexp_pole; // its largest class with a pole (or of degree d)
  long nbig;         // blocks with at least KMIN challenges
  long nexc;         // blocks with at least K0 challenges and no class holding 74 percent
} zres_t;

typedef struct {
  uint8_t *p[MAXS], *a[MAXS]; // per element: P(zeta_i), alpha + beta zeta_i
  uint32_t *cnt, *stamp;
  int *cell, *sub, *sub2;
  uint32_t *cnt3, *stamp3;
} ws_t;

static void ws_init(ws_t *w) {
  for (int i = 0; i < MAXS; i++) {
    w->p[i] = malloc((size_t)NT);
    w->a[i] = malloc((size_t)NT);
  }
  w->cnt = malloc(sizeof(uint32_t) * (size_t)Q * Q);
  w->stamp = malloc(sizeof(uint32_t) * (size_t)Q * Q);
  w->cell = malloc(sizeof(int) * (size_t)NT);
  w->sub = malloc(sizeof(int) * (size_t)NT);
  w->sub2 = malloc(sizeof(int) * (size_t)NT);
  w->cnt3 = malloc(sizeof(uint32_t) * (size_t)Q);
  w->stamp3 = malloc(sizeof(uint32_t) * (size_t)Q);
}

static void record(zres_t *r, const int *idx, int cnt, int n) {
  r->nbig++;
  if (n > r->maxcount) r->maxcount = n;
  blk_t b = analyse(idx, cnt, n);
  if (100 * b.maxclass < 74 * n) {
    if (n >= K0) r->nexc++;
    if (n > r->maxunexp) {
      r->maxunexp = n;
      r->maxunexp_cls = b.maxclass;
      r->maxunexp_near = b.maxnear;
      r->maxunexp_pole = b.maxpole;
    }
  }
}

// elements idx[0..n) (sorted by challenge), consistent with the answers at the first lvl points: split on point lvl
static void refine(ws_t *w, zres_t *r, const int *idx, int n, int lvl, int s) {
  if (lvl == s) {
    int m = 0; // distinct challenges
    for (int i = 0; i < n; i++)
      if (i == 0 || TT[idx[i - 1]].ch != TT[idx[i]].ch) m++;
    if (m >= KMIN) record(r, idx, n, m);
    return;
  }
  const uint8_t *p = w->p[lvl], *a = w->a[lvl];
  int *nxt = malloc(sizeof(int) * (size_t)n);
  for (int yf = 0; yf < Q; yf++) {
    memset(w->cnt3, 0, sizeof(uint32_t) * (size_t)Q);
    for (int i = 0; i < n; i++) {
      int e = idx[i], yg = p[e] ^ MUL[a[e]][yf];
      if (w->cnt3[yg] == 0 || w->stamp3[yg] != TT[e].ch) {
        w->cnt3[yg]++;
        w->stamp3[yg] = TT[e].ch;
      }
    }
    for (int yg = 0; yg < Q; yg++) {
      if ((int)w->cnt3[yg] < KMIN) continue;
      int m = 0;
      for (int i = 0; i < n; i++) {
        int e = idx[i];
        if ((p[e] ^ MUL[a[e]][yf]) == yg) nxt[m++] = e;
      }
      uint32_t save[MAXQ], savs[MAXQ];
      memcpy(save, w->cnt3, sizeof(uint32_t) * (size_t)Q);
      memcpy(savs, w->stamp3, sizeof(uint32_t) * (size_t)Q);
      refine(w, r, nxt, m, lvl + 1, s);
      memcpy(w->cnt3, save, sizeof(uint32_t) * (size_t)Q);
      memcpy(w->stamp3, savs, sizeof(uint32_t) * (size_t)Q);
    }
  }
  free(nxt);
}

static void do_point(ws_t *w, zres_t *r, int s) {
  r->maxcount = r->maxunexp = r->maxunexp_cls = r->maxunexp_near = r->maxunexp_pole = 0;
  r->nbig = r->nexc = 0;
  for (int i = 0; i < s; i++)
    for (int e = 0; e < NT; e++) {
      int al = (int)(TT[e].ch / Q), be = (int)(TT[e].ch % Q);
      w->p[i][e] = (uint8_t)peval(TT[e].co, DEG, r->z[i]);
      w->a[i][e] = (uint8_t)(al ^ MUL[be][r->z[i]]);
    }
  if (s == 1) {
    int *all = malloc(sizeof(int) * (size_t)NT);
    for (int e = 0; e < NT; e++) all[e] = e;
    refine(w, r, all, NT, 0, 1);
    free(all);
    return;
  }
  // first two points together: for each (yF1, yF2) a histogram over (yG1, yG2)
  uint8_t *g1 = malloc((size_t)NT);
  for (int yf1 = 0; yf1 < Q; yf1++) {
    for (int e = 0; e < NT; e++) g1[e] = w->p[0][e] ^ MUL[w->a[0][e]][yf1];
    for (int yf2 = 0; yf2 < Q; yf2++) {
      memset(w->cnt, 0, sizeof(uint32_t) * (size_t)Q * Q);
      int any = 0;
      const uint8_t *m2 = MUL[yf2];
      for (int e = 0; e < NT; e++) {
        int c = g1[e] * Q + (w->p[1][e] ^ m2[w->a[1][e]]);
        w->cell[e] = c;
        if (w->cnt[c] == 0 || w->stamp[c] != TT[e].ch) {
          w->stamp[c] = TT[e].ch;
          if ((int)++w->cnt[c] == KMIN) any = 1;
        }
      }
      if (!any) continue;
      for (int c = 0; c < Q * Q; c++) {
        if ((int)w->cnt[c] < KMIN) continue;
        int m = 0;
        for (int e = 0; e < NT; e++)
          if (w->cell[e] == c) w->sub[m++] = e;
        int *cp = malloc(sizeof(int) * (size_t)m);
        memcpy(cp, w->sub, sizeof(int) * (size_t)m);
        refine(w, r, cp, m, 2, s);
        free(cp);
      }
    }
  }
  free(g1);
}

static zres_t *ZL;
static int NZ, SPTS;
static volatile int NEXT_Z;
static void *z_worker(void *arg) {
  (void)arg;
  ws_t w;
  ws_init(&w);
  for (;;) {
    pthread_mutex_lock(&MU);
    int i = NEXT_Z++;
    pthread_mutex_unlock(&MU);
    if (i >= NZ) break;
    do_point(&w, &ZL[i], SPTS);
  }
  return NULL;
}

// ---- words ----
static void rand_poly(uint8_t *co, int deg, int top) {
  for (int i = 0; i <= top; i++) co[i] = (uint8_t)(i <= deg ? rq() : 0);
}
static int is_root(int x) {
  for (int i = 0; i < NROOTS; i++)
    if (ROOTS[i] == x) return 1;
  return 0;
}
static int reval(int x) { // R(x)
  int v = 1;
  for (int i = 0; i < NROOTS; i++) v = MUL[v][x ^ ROOTS[i]];
  return v;
}
static void make_word(const char *kind, int k, int r) {
  NROOTS = 0;
  if (!strcmp(kind, "random")) {
    for (int x = 0; x < NN; x++) F0[x] = (uint8_t)rq(), F1[x] = (uint8_t)rq();
    return;
  }
  uint8_t F[MAXD + 2], G[MAXD + 2], H[8][MAXD + 2];
  if (!strcmp(kind, "flatlist")) {
    // f0 = F, f1 = G + x^(2d+1): the pairs (F, G + Q_V) for every flat V of size 2(d+1), agreement 2d+1 (note 00, section 1)
    rand_poly(F, DEG - 1, MAXD + 1);
    rand_poly(G, DEG, MAXD + 1);
    for (int x = 0; x < NN; x++) {
      int p = 1;
      for (int i = 0; i < 2 * DEG + 1; i++) p = MUL[p][x];
      F0[x] = (uint8_t)peval(F, DEG, x);
      F1[x] = (uint8_t)(peval(G, DEG, x) ^ p);
    }
    return;
  }
  while (NROOTS < r) {
    int x = rq();
    if (x >= NN && !is_root(x)) ROOTS[NROOTS++] = x;
  }
  int perm[MAXN];
  for (int i = 0; i < NN; i++) perm[i] = i;
  for (int i = NN - 1; i > 0; i--) {
    int j = (int)((rnd() >> 24) % (uint64_t)(i + 1)), t = perm[i];
    perm[i] = perm[j];
    perm[j] = t;
  }
  if (!strcmp(kind, "kpairs")) {
    // f0 = F (degree d-1), f1 = G + R H_j on the j-th block of A points, H_j of degree d - r
    rand_poly(F, DEG - 1, MAXD + 1);
    rand_poly(G, DEG, MAXD + 1);
    for (int j = 0; j < k; j++) rand_poly(H[j], DEG - r, MAXD + 1);
    for (int i = 0; i < NN; i++) {
      int x = perm[i], j = i / AGR;
      F0[x] = (uint8_t)peval(F, DEG, x);
      F1[x] = j < k ? (uint8_t)(peval(G, DEG, x) ^ MUL[reval(x)][peval(H[j], DEG, x)]) : (uint8_t)rq();
    }
  } else if (!strcmp(kind, "polek")) {
    // f0 = 1/(x - x0), f1 = w/(x - x0), w = C0 + R H_j on the j-th block, deg C0 <= d+1, deg H_j <= d+1-r
    int x0;
    do x0 = rq();
    while (x0 < NN || is_root(x0));
    rand_poly(G, DEG + 1, MAXD + 1);
    for (int j = 0; j < k; j++) rand_poly(H[j], DEG + 1 - r, MAXD + 1);
    for (int i = 0; i < NN; i++) {
      int x = perm[i], j = i / AGR, iv = INV[x ^ x0];
      int w = j < k ? (peval(G, DEG + 1, x) ^ MUL[reval(x)][peval(H[j], DEG + 1, x)]) : rq();
      F0[x] = (uint8_t)iv;
      F1[x] = MUL[w][iv];
    }
  } else {
    fprintf(stderr, "unknown word %s\n", kind);
    exit(1);
  }
}

static const char *arg(int argc, char **argv, const char *key, const char *def) {
  size_t n = strlen(key);
  for (int i = 1; i < argc; i++)
    if (!strncmp(argv[i], key, n) && argv[i][n] == '=') return argv[i] + n + 1;
  return def;
}

static const char *category(const zres_t *r, int s, int *nr_out) {
  int nd = 0, nr = 0, eq = 0;
  for (int i = 0; i < s; i++) {
    if (r->z[i] < NN) nd++;
    if (is_root(r->z[i])) nr++;
    for (int j = 0; j < i; j++)
      if (r->z[i] == r->z[j]) eq = 1;
  }
  *nr_out = nr;
  if (nr >= s) return "all roots";
  if (nr == s - 1 && s > 1) return "s-1 roots";
  if (eq) return "equal coords";
  if (nd == s) return "all in D";
  if (nd == s - 1 && s > 1) return "s-1 in D";
  if (nr > 0) return "fewer roots";
  if (nd > 0) return "some in D";
  return "generic";
}

int main(int argc, char **argv) {
  int m = atoi(arg(argc, argv, "m", "6")), N = atoi(arg(argc, argv, "N", "4"));
  DEG = atoi(arg(argc, argv, "d", "3"));
  AGR = atoi(arg(argc, argv, "A", "5"));
  int k = atoi(arg(argc, argv, "k", "3")), r = atoi(arg(argc, argv, "r", "3"));
  int s = atoi(arg(argc, argv, "s", "2")), samples = atoi(arg(argc, argv, "samples", "200"));
  const char *word = arg(argc, argv, "word", "kpairs"), *zmode = arg(argc, argv, "zmode", "all");
  NTHREADS = atoi(arg(argc, argv, "threads", "4"));
  rng_s ^= (uint64_t)atoll(arg(argc, argv, "seed", "1")) * 0x9E3779B97F4A7C15ull;
  gf_init(m);
  NN = 1 << N;
  K0 = atoi(arg(argc, argv, "k0", "0"));
  if (!K0) K0 = (272 * Q + 99) / 100;
  KMIN = atoi(arg(argc, argv, "kmin", "0"));
  if (!KMIN) KMIN = Q + Q / 4;
  make_word(word, k, r);
  build_lists();
  int nonempty = 0, maxl = 0;
  for (int i = 0; i < NT;) {
    int j = i;
    while (j < NT && TT[j].ch == TT[i].ch) j++;
    nonempty++;
    if (j - i > maxl) maxl = j - i;
    i = j;
  }
  printf("# GF(2^%d) n=%d d=%d A=%d word=%s k=%d r=%d  |T|=%d  challenges with a close codeword=%d of %d  Lambda=%d  K0=%d kmin=%d\n", m,
         NN, DEG, AGR, word, k, r, NT, nonempty, Q * Q, maxl, K0, KMIN);
  int unexpl, np = near_pairs(&unexpl);
  printf("# near pairs (agreement >= A-1): %d   unexplained elements |T_un| = %d = %.1f q\n", np, unexpl, (double)unexpl / Q);
  printf("# roots of R:");
  for (int i = 0; i < NROOTS; i++) printf(" %d", ROOTS[i]);
  printf("\n");

  // the point tuples
  SPTS = s;
  if (!strcmp(zmode, "all")) {
    NZ = 0;
    ZL = calloc((size_t)Q * Q * (s == 3 ? Q : 1), sizeof(zres_t));
    if (s == 1)
      for (int a = 0; a < Q; a++) ZL[NZ++].z[0] = a;
    else if (s == 2)
      for (int a = 0; a < Q; a++)
        for (int b = a; b < Q; b++) ZL[NZ].z[0] = a, ZL[NZ++].z[1] = b;
    else {
      fprintf(stderr, "zmode=all needs s <= 2\n");
      return 1;
    }
  } else if (!strcmp(zmode, "roots")) {
    // s-1 coordinates over the roots (non-decreasing), the last over all of E
    NZ = 0;
    ZL = calloc((size_t)Q * 64, sizeof(zres_t));
    if (s == 2)
      for (int i = 0; i < NROOTS; i++)
        for (int b = 0; b < Q; b++) ZL[NZ].z[0] = ROOTS[i], ZL[NZ++].z[1] = b;
    else
      for (int i = 0; i < NROOTS; i++)
        for (int j = i; j < NROOTS; j++)
          for (int b = 0; b < Q; b++) ZL[NZ].z[0] = ROOTS[i], ZL[NZ].z[1] = ROOTS[j], ZL[NZ++].z[2] = b;
  } else {
    int generic = !strcmp(zmode, "generic");
    NZ = samples;
    ZL = calloc((size_t)NZ, sizeof(zres_t));
    for (int i = 0; i < NZ; i++)
      for (int j = 0; j < s; j++) {
        int x, bad;
        do {
          x = rq();
          bad = 0;
          if (generic) {
            if (x < NN || is_root(x)) bad = 1;
            for (int t = 0; t < j; t++)
              if (ZL[i].z[t] == x) bad = 1;
          }
        } while (bad);
        ZL[i].z[j] = x;
      }
  }
  pthread_t th[16];
  NEXT_Z = 0;
  for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, z_worker, NULL);
  for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);

  // summary by category
  const char *cats[] = {"all roots", "s-1 roots", "equal coords", "all in D", "s-1 in D", "fewer roots", "some in D", "generic"};
  printf("# s=%d zmode=%s tuples=%d (zmode=all lists unordered tuples; weights are the ordered counts)\n", s, zmode, NZ);
  printf("%-13s %9s %9s %9s %12s %12s %10s %10s %10s\n", "category", "tuples", "weight", "exc.wt", "max block", "max unexpl", "its class", "its near", "its pole");
  double totw = 0, totexc = 0;
  for (int c = 0; c < 8; c++) {
    long n = 0;
    double wsum = 0, wexc = 0;
    int mb = 0, mu = 0, mc = 0, mn = 0, mp = 0;
    for (int i = 0; i < NZ; i++) {
      int nr;
      if (strcmp(category(&ZL[i], s, &nr), cats[c])) continue;
      double wgt = 1;
      if (!strcmp(zmode, "all") && s == 2) wgt = ZL[i].z[0] == ZL[i].z[1] ? 1 : 2;
      n++;
      wsum += wgt;
      int exc = ZL[i].nexc > 0;
      if (exc) wexc += wgt;
      if (ZL[i].maxcount > mb) mb = ZL[i].maxcount;
      if (ZL[i].maxunexp > mu) mu = ZL[i].maxunexp, mc = ZL[i].maxunexp_cls, mn = ZL[i].maxunexp_near, mp = ZL[i].maxunexp_pole;
    }
    if (!n) continue;
    totw += wsum;
    totexc += wexc;
    printf("%-13s %9ld %9.0f %9.0f %12d %12d %10d %10d %10d\n", cats[c], n, wsum, wexc, mb, mu, mc, mn, mp);
  }
  printf("total weight %.0f, exceptional weight %.0f, frequency %.6f\n", totw, totexc, totexc / totw);
  return 0;
}
