// Researcher 10 (red team): brute-force checks of note 07, Theorem 3 ("DEEP fold") and Corollary 4.
//
// Toy setting: E = GF(2^m), 5 <= m <= 8, D = {0, .., n-1} (the F_2-span of 1, x, .., x^(N-1)), two halves f0, f1 of
// H lanes each (H = 1 or 2), degree bound d, threshold A. For every challenge c = (alpha, beta) the program computes
// the full list L(c) of H-tuples of degree <= d agreeing with f1 + (alpha + beta x) f0 on at least A points, by a
// method independent of scripts/07_deep_fold_check.py: a depth-first walk over the (d+1)-subsets S of the first
// n - A + d + 1 domain points with Newton updates; for a fixed S the interpolant of the fold is affine in c, so each
// other point x agrees on a line of challenges (or everywhere, or nowhere), and the challenges on enough lines are
// read off per alpha. Each pair (c, P) is produced once, from the first d + 1 points of its agreement set.
//
// Analyses on the set T of all pairs (c, P):
//   classes   dependency classes through anchors (Lemma 2): pole classes, polynomial classes, explained or not;
//   points    for s points z_i = (r_i, zeta_i): the exact maximum over ALL answer vectors m in E^(2s) of the number of
//             challenges with an m-consistent list member (exact above a floor), and the class structure of the winner;
//   tables    Corollary 4 with a running claim: the exact maximum over all answer vectors AND all round messages
//             (v_G, v_F, sigma_0, sigma_1) of the number of winning challenges; also with no points at all (today's
//             protocol shape), to see the list factor come back;
//   nested    a 4-lane word, two fold rounds with the same points: for every first challenge, the second round's maximum.
//
// Build: cc -O2 -o deep10 10_deep_redteam.c -lpthread     Run: see 10_run.sh.
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXQ 256
#define MAXN 64
#define MAXD 20 // d + 1 <= MAXD
#define MAXH 2
#define MAXS 6

static int FM, Q, NN, DEG, AGR, H = 1, T0, KNEED, NTHREADS = 4, QUIET = 0;
static uint8_t MUL[MAXQ][MAXQ], INV[MAXQ];
static uint8_t F0[MAXH][MAXN], F1[MAXH][MAXN], FX[MAXH][MAXN];

typedef struct {
  uint8_t a, b;
  uint8_t co[MAXH][MAXD];
} elem_t;

static elem_t *TT;
static int NT;

static uint64_t rng_s = 88172645463325252ull;
static uint64_t rnd(void) {
  rng_s ^= rng_s << 13;
  rng_s ^= rng_s >> 7;
  rng_s ^= rng_s << 17;
  return rng_s;
}
static int rq(void) { return (int)((rnd() >> 24) % (uint64_t)Q); }
static int rmod(int k) { return (int)((rnd() >> 24) % (uint64_t)k); }

static void gf_init(int m) {
  static const int poly[9] = {0, 0, 0, 0, 0, 0x25, 0x43, 0x83, 0x11B};
  FM = m;
  Q = 1 << m;
  for (int a = 0; a < Q; a++)
    for (int b = 0; b < Q; b++) {
      int r = 0, x = a, y = b;
      while (y) {
        if (y & 1) r ^= x;
        x <<= 1;
        if (x >> m) x ^= poly[m];
        y >>= 1;
      }
      MUL[a][b] = (uint8_t)r;
    }
  for (int a = 1; a < Q; a++)
    for (int b = 1; b < Q; b++)
      if (MUL[a][b] == 1) INV[a] = (uint8_t)b;
}

static inline int peval(const uint8_t *co, int deg, int x) {
  int r = 0;
  for (int j = deg; j >= 0; j--) r = MUL[r][x] ^ co[j];
  return r;
}

// ------------------------------------------------------------------------------------------------------------
// The lists of all folds.

typedef struct {
  uint8_t nval[MAXN];
  uint8_t ncoef[MAXD + 1];
  uint8_t err[3 * MAXH][MAXN];
  uint8_t ico[3 * MAXH][MAXD];
} node_t;

typedef struct {
  node_t st[MAXD + 2];
  int S[MAXD + 1];
  elem_t *out;
  int nout, cap;
  int cnt[MAXQ], cstamp[MAXQ], fstamp[MAXQ], stamp;
} thr_t;

static void push(thr_t *t, int k, int s) {
  node_t *a = &t->st[k], *b = &t->st[k + 1];
  int iv = INV[a->nval[s]];
  for (int g = 0; g < 3 * H; g++) {
    int c = MUL[a->err[g][s]][iv];
    const uint8_t *mc = MUL[c];
    for (int x = 0; x < NN; x++) b->err[g][x] = a->err[g][x] ^ mc[a->nval[x]];
    for (int j = 0; j <= k; j++) b->ico[g][j] = (j < k ? a->ico[g][j] : 0) ^ mc[a->ncoef[j]];
  }
  for (int x = 0; x < NN; x++) b->nval[x] = MUL[a->nval[x]][x ^ s];
  for (int j = 0; j <= k + 1; j++) b->ncoef[j] = (j > 0 ? a->ncoef[j - 1] : 0) ^ (j <= k ? MUL[s][a->ncoef[j]] : 0);
  t->S[k] = s;
}

static void emit(thr_t *t, int alpha, int beta) {
  if (t->nout == t->cap) {
    t->cap = t->cap ? 2 * t->cap : 1024;
    t->out = realloc(t->out, (size_t)t->cap * sizeof(elem_t));
  }
  elem_t *e = &t->out[t->nout++];
  node_t *nd = &t->st[DEG + 1];
  memset(e, 0, sizeof *e);
  e->a = (uint8_t)alpha;
  e->b = (uint8_t)beta;
  for (int u = 0; u < H; u++)
    for (int j = 0; j <= DEG; j++)
      e->co[u][j] = nd->ico[3 * u][j] ^ MUL[alpha][nd->ico[3 * u + 1][j]] ^ MUL[beta][nd->ico[3 * u + 2][j]];
}

static void leaf(thr_t *t) {
  node_t *nd = &t->st[DEG + 1];
  int smax = t->S[DEG];
  uint64_t inS = 0;
  for (int k = 0; k <= DEG; k++) inS |= 1ull << t->S[k];
  int nx = 0, xs[MAXN];
  uint8_t U[MAXN][MAXH], V[MAXN][MAXH], md[MAXN][MAXH];
  for (int x = 0; x < NN; x++) {
    if ((inS >> x) & 1) continue;
    int always = 1;
    for (int u = 0; u < H; u++) {
      int a1 = nd->err[3 * u][x], a2 = nd->err[3 * u + 1][x], a3 = nd->err[3 * u + 2][x];
      if (a3) {
        md[nx][u] = 1;
        U[nx][u] = MUL[a1][INV[a3]];
        V[nx][u] = MUL[a2][INV[a3]];
        always = 0;
      } else {
        md[nx][u] = 0;
        U[nx][u] = (uint8_t)a1;
        V[nx][u] = (uint8_t)a2;
        if (a1 | a2) always = 0;
      }
    }
    if (always && x < smax) return; // an earlier point always agrees: S is never the canonical subset
    xs[nx++] = x;
  }
  for (int alpha = 0; alpha < Q; alpha++) {
    const uint8_t *ma = MUL[alpha];
    int stamp = ++t->stamp, base = 0, skip = 0, ntouch = 0, touched[MAXN];
    for (int i = 0; i < nx && !skip; i++) {
      int state = 2, beta = 0; // 2: every beta, 1: one beta, 0: none
      for (int u = 0; u < H && state; u++) {
        int v = U[i][u] ^ ma[V[i][u]];
        if (md[i][u]) {
          if (state == 2) state = 1, beta = v;
          else if (beta != v) state = 0;
        } else if (v) state = 0;
      }
      if (xs[i] < smax) {
        if (state == 2) skip = 1;
        else if (state == 1) t->fstamp[beta] = stamp;
      } else if (state == 2) base++;
      else if (state == 1) {
        if (t->cstamp[beta] != stamp) t->cstamp[beta] = stamp, t->cnt[beta] = 0, touched[ntouch++] = beta;
        t->cnt[beta]++;
      }
    }
    if (skip) continue;
    if (base >= KNEED) {
      for (int beta = 0; beta < Q; beta++)
        if (t->fstamp[beta] != stamp) emit(t, alpha, beta);
    } else
      for (int i = 0; i < ntouch; i++) {
        int beta = touched[i];
        if (t->cnt[beta] + base >= KNEED && t->fstamp[beta] != stamp) emit(t, alpha, beta);
      }
  }
}

static void dfs(thr_t *t, int k, int last) {
  if (k == DEG + 1) {
    leaf(t);
    return;
  }
  int need = DEG + 1 - k;
  for (int s = last + 1; s <= T0 - need; s++) {
    push(t, k, s);
    dfs(t, k + 1, s);
  }
}

static int (*TASKS)[3], NTASKS, PREF;
static volatile int NEXT_TASK;
static pthread_mutex_t TASK_MU = PTHREAD_MUTEX_INITIALIZER;

static void *worker(void *arg) {
  thr_t *t = arg;
  node_t *r = &t->st[0];
  memset(r, 0, sizeof *r);
  for (int x = 0; x < NN; x++) r->nval[x] = 1;
  r->ncoef[0] = 1;
  for (int u = 0; u < H; u++)
    for (int x = 0; x < NN; x++) r->err[3 * u][x] = F1[u][x], r->err[3 * u + 1][x] = F0[u][x], r->err[3 * u + 2][x] = FX[u][x];
  for (;;) {
    pthread_mutex_lock(&TASK_MU);
    int id = NEXT_TASK < NTASKS ? NEXT_TASK++ : -1;
    pthread_mutex_unlock(&TASK_MU);
    if (id < 0) break;
    for (int k = 0; k < PREF; k++) push(t, k, TASKS[id][k]);
    dfs(t, PREF, TASKS[id][PREF - 1]);
  }
  return NULL;
}

static int elem_cmp(const void *x, const void *y) { return memcmp(x, y, sizeof(elem_t)); }

static void build_lists(void) {
  for (int u = 0; u < H; u++)
    for (int x = 0; x < NN; x++) FX[u][x] = MUL[x][F0[u][x]];
  T0 = NN - AGR + DEG + 1;
  KNEED = AGR - (DEG + 1);
  if (KNEED < 1 || T0 < DEG + 1) {
    fprintf(stderr, "need d + 1 < A <= n\n");
    exit(1);
  }
  PREF = DEG + 1 < 3 ? DEG + 1 : 3;
  NTASKS = 0;
  free(TASKS);
  TASKS = malloc(sizeof(int[3]) * (size_t)(T0 * T0 * T0 / 6 + T0 * T0 + 8));
  int idx[3];
  for (idx[0] = 0; idx[0] < T0; idx[0]++)
    if (PREF == 1) TASKS[NTASKS][0] = idx[0], NTASKS++;
    else
      for (idx[1] = idx[0] + 1; idx[1] < T0; idx[1]++)
        if (PREF == 2) TASKS[NTASKS][0] = idx[0], TASKS[NTASKS][1] = idx[1], NTASKS++;
        else
          for (idx[2] = idx[1] + 1; idx[2] < T0; idx[2]++) memcpy(TASKS[NTASKS++], idx, sizeof idx);
  // keep only prefixes that can be completed
  int w = 0;
  for (int i = 0; i < NTASKS; i++)
    if (TASKS[i][PREF - 1] <= T0 - (DEG + 1 - PREF) - 1 || DEG + 1 == PREF) memcpy(TASKS[w++], TASKS[i], sizeof idx);
  NTASKS = w;
  NEXT_TASK = 0;
  int nth = NTHREADS;
  thr_t **ths = malloc(sizeof(thr_t *) * (size_t)nth);
  pthread_t tid[64];
  for (int i = 0; i < nth; i++) {
    ths[i] = calloc(1, sizeof(thr_t));
    if (nth > 1) pthread_create(&tid[i], NULL, worker, ths[i]);
    else worker(ths[i]);
  }
  NT = 0;
  for (int i = 0; i < nth; i++) {
    if (nth > 1) pthread_join(tid[i], NULL);
    NT += ths[i]->nout;
  }
  free(TT);
  TT = malloc(sizeof(elem_t) * (size_t)(NT + 1));
  int p = 0;
  for (int i = 0; i < nth; i++) {
    if (ths[i]->nout) memcpy(TT + p, ths[i]->out, sizeof(elem_t) * (size_t)ths[i]->nout);
    p += ths[i]->nout;
    free(ths[i]->out);
    free(ths[i]);
  }
  free(ths);
  qsort(TT, (size_t)NT, sizeof(elem_t), elem_cmp);
}

static inline int chal(int e) { return TT[e].a * Q + TT[e].b; }

static void list_stats(int *nonempty, int *maxlist) {
  int ne = 0, mx = 0, run = 0;
  for (int e = 0; e < NT; e++) {
    if (e == 0 || chal(e) != chal(e - 1)) ne++, run = 0;
    run++;
    if (run > mx) mx = run;
  }
  *nonempty = ne;
  *maxlist = mx;
}

// Independent check of the lists on a few challenges: all (d+1)-subsets of D, Lagrange interpolation.
static int naive_check(int trials) {
  int bad = 0;
  for (int tr = 0; tr < trials; tr++) {
    int alpha = rq(), beta = rq(), nfound = 0;
    static uint8_t found[4096][MAXH][MAXN];
    int S[MAXD + 1];
    for (int k = 0; k <= DEG; k++) S[k] = k;
    for (;;) {
      uint8_t val[MAXH][MAXN];
      int agree = 0, first = 1;
      for (int x = 0; x < NN; x++) {
        int ok = 1;
        for (int u = 0; u < H; u++) {
          int r = 0;
          for (int j = 0; j <= DEG; j++) {
            int num = 1, den = 1;
            for (int k = 0; k <= DEG; k++)
              if (k != j) num = MUL[num][x ^ S[k]], den = MUL[den][S[j] ^ S[k]];
            int wj = F1[u][S[j]] ^ MUL[alpha ^ MUL[beta][S[j]]][F0[u][S[j]]];
            r ^= MUL[wj][MUL[num][INV[den]]];
          }
          val[u][x] = (uint8_t)r;
          if (r != (F1[u][x] ^ MUL[alpha ^ MUL[beta][x]][F0[u][x]])) ok = 0;
        }
        agree += ok;
        if (ok && agree <= DEG + 1 && x != S[agree - 1]) first = 0;
      }
      if (agree >= AGR && first && nfound < 4096) memcpy(found[nfound++], val, sizeof val);
      int k = DEG;
      while (k >= 0 && S[k] == NN - 1 - (DEG - k)) k--;
      if (k < 0) break;
      S[k]++;
      for (int j = k + 1; j <= DEG; j++) S[j] = S[j - 1] + 1;
    }
    int mine = 0, match = 0;
    for (int e = 0; e < NT; e++)
      if (TT[e].a == alpha && TT[e].b == beta) {
        mine++;
        for (int f = 0; f < nfound; f++) {
          int same = 1;
          for (int u = 0; u < H && same; u++)
            for (int x = 0; x < NN && same; x++)
              if (peval(TT[e].co[u], DEG, x) != found[f][u][x]) same = 0;
          match += same;
        }
      }
    if (mine != nfound || match != nfound) bad++;
  }
  return bad;
}

// ------------------------------------------------------------------------------------------------------------
// Dependency classes (Lemma 2).

typedef struct {
  int pole, x0;
  uint8_t f[MAXH][MAXD + 1];
  uint8_t res[MAXH];
} rat_t;

// F = (P_e + P_0) / (a_e + a_0) for two elements with distinct challenges.
static void rat_of(const elem_t *e0, const elem_t *e, rat_t *r) {
  int da = e0->a ^ e->a, db = e0->b ^ e->b;
  memset(r, 0, sizeof *r);
  for (int u = 0; u < H; u++) {
    uint8_t num[MAXD];
    for (int j = 0; j <= DEG; j++) num[j] = e0->co[u][j] ^ e->co[u][j];
    if (!db) {
      int iv = INV[da];
      for (int j = 0; j <= DEG; j++) r->f[u][j] = MUL[num[j]][iv];
    } else {
      int x0 = MUL[da][INV[db]], iv = INV[db], carry = 0;
      for (int j = DEG; j >= 1; j--) {
        carry = num[j] ^ MUL[x0][carry];
        r->f[u][j - 1] = MUL[carry][iv];
      }
      int rem = num[0] ^ MUL[x0][carry];
      if (rem) r->pole = 1, r->x0 = x0, r->res[u] = MUL[rem][iv];
    }
  }
}

static uint64_t rat_hash(const rat_t *r) {
  uint64_t h = 1469598103934665603ull;
  const uint8_t *p = (const uint8_t *)r;
  for (size_t i = 0; i < sizeof *r; i++) h = (h ^ p[i]) * 1099511628211ull;
  return h;
}

typedef struct {
  uint64_t h;
  int pos;
} hp_t;
static int hp_cmp(const void *x, const void *y) {
  const hp_t *a = x, *b = y;
  return a->h < b->h ? -1 : a->h > b->h ? 1 : a->pos - b->pos;
}

typedef struct {
  int size, pole, explained, degF, degG, Z;
} cls_t;

static int poly_deg(const uint8_t *co, int top) {
  while (top >= 0 && !co[top]) top--;
  return top;
}

// Classify the class of the anchor e0 and the element e1 (polynomial case): degrees and common agreement with (f0, f1).
static void classify(const elem_t *e0, const rat_t *r, cls_t *c) {
  c->pole = r->pole;
  c->explained = 0;
  c->degF = c->degG = -1;
  c->Z = 0;
  if (r->pole) return;
  uint8_t G[MAXH][MAXD + 2];
  for (int u = 0; u < H; u++) {
    for (int j = 0; j <= DEG + 1; j++)
      G[u][j] = (j <= DEG ? e0->co[u][j] ^ MUL[e0->a][r->f[u][j]] : 0) ^ (j >= 1 ? MUL[e0->b][r->f[u][j - 1]] : 0);
    int dF = poly_deg(r->f[u], DEG), dG = poly_deg(G[u], DEG + 1);
    if (dF > c->degF) c->degF = dF;
    if (dG > c->degG) c->degG = dG;
  }
  for (int x = 0; x < NN; x++) {
    int ok = 1;
    for (int u = 0; u < H; u++)
      if (peval(r->f[u], DEG, x) != F0[u][x] || peval(G[u], DEG + 1, x) != F1[u][x]) ok = 0;
    c->Z += ok;
  }
  c->explained = c->degF <= DEG - 1 && c->degG <= DEG && c->Z >= AGR - 1;
}

// Classes through the anchor idx[apos] inside the subset idx[0..cnt). Returns the largest; updates the global maxima.
static int CL_EXPL, CL_UNEXPL, CL_POLE, CL_VIOL, CL_EXPL_Z;
static hp_t *HP;
static cls_t anchor_scan(const int *idx, int cnt, int apos) {
  const elem_t *e0 = &TT[idx[apos]];
  int m = 0;
  rat_t r;
  for (int i = 0; i < cnt; i++) {
    const elem_t *e = &TT[idx[i]];
    if (e->a == e0->a && e->b == e0->b) continue;
    rat_of(e0, e, &r);
    HP[m].h = rat_hash(&r);
    HP[m].pos = i;
    m++;
  }
  qsort(HP, (size_t)m, sizeof(hp_t), hp_cmp);
  cls_t best = {0, 0, 0, -1, -1, 0};
  int big = Q > NN * (NN - 1) / 2 ? Q : NN * (NN - 1) / 2;
  for (int i = 0; i < m;) {
    int j = i;
    while (j < m && HP[j].h == HP[i].h) j++;
    int size = j - i + 1;
    if (size >= 3 && (size > best.size || size > CL_EXPL || size > CL_UNEXPL || size > CL_POLE)) {
      cls_t c;
      rat_of(e0, &TT[idx[HP[i].pos]], &r);
      classify(e0, &r, &c);
      c.size = size;
      if (c.pole) {
        if (size > CL_POLE) CL_POLE = size;
        if (size > Q) CL_VIOL++;
      } else if (c.explained) {
        if (size > CL_EXPL) CL_EXPL = size, CL_EXPL_Z = c.Z;
      } else {
        if (size > CL_UNEXPL) CL_UNEXPL = size;
        if (size > big) CL_VIOL++;
      }
      if (size > best.size) best = c;
    }
    i = j;
  }
  return best;
}

static void class_scan(int anchors) {
  int *idx = malloc(sizeof(int) * (size_t)(NT + 1));
  for (int i = 0; i < NT; i++) idx[i] = i;
  HP = realloc(HP, sizeof(hp_t) * (size_t)(NT + 1));
  CL_EXPL = CL_UNEXPL = CL_POLE = CL_VIOL = CL_EXPL_Z = 0;
  int na = anchors < NT ? anchors : NT;
  for (int k = 0; k < na; k++) anchor_scan(idx, NT, na == NT ? k : rmod(NT));
  int big = Q > NN * (NN - 1) / 2 ? Q : NN * (NN - 1) / 2;
  printf("  classes (%d anchors%s): largest explained by a pair of L_pair: %d (its pair agrees on %d points); largest "
         "unexplained polynomial class: %d; largest pole class: %d; max(q, C(n,2)) = %d; Lemma 2 violations: %d\n",
         na, na == NT ? ", all" : "", CL_EXPL, CL_EXPL_Z, CL_UNEXPL, CL_POLE, big, CL_VIOL);
  free(idx);
}

// ------------------------------------------------------------------------------------------------------------
// Points: the exact maximum over all answer vectors.

static int SP;
static uint8_t ZR[MAXS], ZZ[MAXS];
static uint8_t *PT[MAXS], *PE[MAXS];
static int *LV[MAXS + 1];
static int BEST, FLOOR_, BEST_N, *BEST_IDX, CUR_Y[MAXS], CUR_K[MAXS], BEST_Y[MAXS], BEST_K[MAXS];

static inline int ev_point(const elem_t *e, int i) {
  int p0 = peval(e->co[0], DEG, ZZ[i]);
  if (H == 1) return p0;
  int p1 = peval(e->co[1], DEG, ZZ[i]);
  return p0 ^ MUL[ZR[i]][p0 ^ p1]; // eq(r, 0) P_0 + eq(r, 1) P_1
}

static void prep_points(void) {
  for (int i = 0; i < SP; i++) {
    PT[i] = realloc(PT[i], (size_t)NT + 1);
    PE[i] = realloc(PE[i], (size_t)NT + 1);
    for (int e = 0; e < NT; e++) {
      PT[i][e] = TT[e].a ^ MUL[TT[e].b][ZZ[i]];
      PE[i][e] = (uint8_t)ev_point(&TT[e], i);
    }
  }
  for (int i = 0; i <= SP; i++) LV[i] = realloc(LV[i], sizeof(int) * (size_t)(NT + 1));
  BEST_IDX = realloc(BEST_IDX, sizeof(int) * (size_t)(NT + 1));
}

static int distinct(const int *idx, int cnt) {
  int d = 0, last = -1;
  for (int i = 0; i < cnt; i++) {
    int c = chal(idx[i]);
    if (c != last) d++, last = c;
  }
  return d;
}

// Cells collected for the table search.
typedef struct {
  int count;
  uint8_t y[MAXS], k[MAXS];
} cell_t;
static cell_t *CELLS;
static int NCELLS, CELLCAP, COLLECT_MIN, COLLECT;

static void refine(const int *idx, int cnt, int level) {
  int *out = LV[level + 1];
  const uint8_t *pt = PT[level], *pe = PE[level];
  uint8_t *keys = malloc((size_t)cnt + 1);
  for (int y = 0; y < Q; y++) {
    int hist[MAXQ + 1] = {0}, start[MAXQ + 1];
    const uint8_t *my = MUL[y];
    for (int i = 0; i < cnt; i++) {
      keys[i] = pe[idx[i]] ^ my[pt[idx[i]]];
      hist[keys[i]]++;
    }
    int thr = BEST > FLOOR_ ? BEST : FLOOR_, any = 0;
    if (COLLECT && COLLECT_MIN - 1 < thr) thr = COLLECT_MIN - 1;
    for (int k = 0, p = 0; k < Q; k++) start[k] = p, p += hist[k], any |= hist[k] > thr;
    if (!any) continue;
    int pos[MAXQ];
    memcpy(pos, start, sizeof pos);
    for (int i = 0; i < cnt; i++) out[pos[keys[i]]++] = idx[i];
    CUR_Y[level] = y;
    for (int k = 0; k < Q; k++) {
      thr = BEST > FLOOR_ ? BEST : FLOOR_;
      if (COLLECT && COLLECT_MIN - 1 < thr) thr = COLLECT_MIN - 1;
      if (hist[k] <= thr) continue;
      int dc = distinct(out + start[k], hist[k]);
      if (dc <= thr) continue;
      CUR_K[level] = k;
      if (level == SP - 1) {
        if (COLLECT && dc >= COLLECT_MIN) {
          if (NCELLS == CELLCAP) CELLCAP = CELLCAP ? 2 * CELLCAP : 1024, CELLS = realloc(CELLS, sizeof(cell_t) * (size_t)CELLCAP);
          CELLS[NCELLS].count = dc;
          for (int i = 0; i < SP; i++) CELLS[NCELLS].y[i] = (uint8_t)CUR_Y[i], CELLS[NCELLS].k[i] = (uint8_t)CUR_K[i];
          NCELLS++;
        }
        if (dc > BEST) {
          BEST = dc;
          BEST_N = hist[k];
          memcpy(BEST_IDX, out + start[k], sizeof(int) * (size_t)hist[k]);
          memcpy(BEST_Y, CUR_Y, sizeof CUR_Y);
          memcpy(BEST_K, CUR_K, sizeof CUR_K);
        }
      } else
        refine(out + start[k], hist[k], level + 1);
    }
  }
  free(keys);
}

// Exact max over all m of the number of challenges with an m-consistent member; exact when the result is > floor.
static int max_wins(int s, int floor_) {
  int save = SP;
  SP = s;
  BEST = 0;
  BEST_N = 0;
  FLOOR_ = floor_;
  for (int i = 0; i < NT; i++) LV[0][i] = i;
  refine(LV[0], NT, 0);
  SP = save;
  return BEST;
}

// Largest class inside a cell (a set of elements consistent with one answer vector).
static cls_t cell_class(const int *cell, int n) {
  cls_t best = {0, 0, 0, -1, -1, 0};
  if (n < 3) return best;
  HP = realloc(HP, sizeof(hp_t) * (size_t)(NT + 1));
  int na = n < 400 ? n : 400;
  int se = CL_EXPL, su = CL_UNEXPL, sp = CL_POLE, sv = CL_VIOL, sz = CL_EXPL_Z;
  for (int k = 0; k < na; k++) {
    CL_EXPL = CL_UNEXPL = CL_POLE = 0; // classify every candidate class of this anchor
    cls_t c = anchor_scan(cell, n, na == n ? k : rmod(n));
    if (c.size > best.size) best = c;
  }
  CL_EXPL = se, CL_UNEXPL = su, CL_POLE = sp, CL_VIOL = sv, CL_EXPL_Z = sz;
  return best;
}
static cls_t best_cell_class(void) { return cell_class(BEST_IDX, BEST_N); }

static int cell_cmp(const void *x, const void *y) { return ((const cell_t *)y)->count - ((const cell_t *)x)->count; }

static int cell_members(const cell_t *c, int s, int *idx) {
  int cnt = 0;
  for (int e = 0; e < NT; e++) {
    int ok = 1;
    for (int i = 0; i < s && ok; i++) ok = (PE[i][e] ^ MUL[PT[i][e]][c->y[i]]) == c->k[i];
    if (ok) idx[cnt++] = e;
  }
  return cnt;
}

// The event of Theorem 3 for these points: the number of answer vectors m whose consistent set has at least k0
// challenges with less than 74 percent of them on one pair of L_pair. Every such m is examined.
static int count_exceptional(int s, int k0, int *ncells_out) {
  int save = SP, bad = 0;
  SP = s;
  NCELLS = 0;
  COLLECT = 1;
  COLLECT_MIN = k0;
  BEST = 1 << 30;
  FLOOR_ = 0;
  for (int i = 0; i < NT; i++) LV[0][i] = i;
  refine(LV[0], NT, 0);
  COLLECT = 0;
  int *idx = malloc(sizeof(int) * (size_t)(NT + 1));
  for (int c = 0; c < NCELLS; c++) {
    int n = cell_members(&CELLS[c], s, idx);
    cls_t cl = cell_class(idx, n);
    if (!(cl.explained && cl.size >= 0.74 * CELLS[c].count)) bad++;
  }
  free(idx);
  *ncells_out = NCELLS;
  SP = save;
  return bad;
}

// ------------------------------------------------------------------------------------------------------------
// Corollary 4: running claim and round message.

static uint8_t WT[2][MAXH][MAXD];
static int CRUN;

static inline int lam(int iota, const uint8_t co[MAXH][MAXD]) {
  int r = 0;
  for (int u = 0; u < H; u++)
    for (int j = 0; j <= DEG; j++) r ^= MUL[WT[iota][u][j]][co[u][j]];
  return r;
}

// Max over all round messages (v_G, v_F, s0, s1) of the number of distinct challenges of idx[0..cnt) (sorted by
// challenge) whose member satisfies the folded running claim
//   <W_alpha, P> = v_G + alpha (v_G + c) + alpha^2 v_F + beta s0 + alpha beta (s0 + s1).
static int table_search(const int *idx, int cnt) {
  uint8_t *R0 = malloc((size_t)cnt), *KF = malloc((size_t)cnt), *K0 = malloc((size_t)cnt), *K1 = malloc((size_t)cnt);
  uint8_t *A1 = malloc((size_t)cnt), *part = malloc((size_t)cnt), *part2 = malloc((size_t)cnt);
  int *ch = malloc(sizeof(int) * (size_t)cnt);
  for (int i = 0; i < cnt; i++) {
    const elem_t *e = &TT[idx[i]];
    int al = e->a, be = e->b;
    int val = MUL[1 ^ al][lam(0, e->co)] ^ MUL[al][lam(1, e->co)];
    int rhs = val ^ MUL[al][CRUN];
    // (1 + al) vG + al^2 vF + be (1 + al) s0 + al be s1 = rhs
    ch[i] = al * Q + be;
    if (al != 1) {
      int iv = INV[1 ^ al];
      A1[i] = 0;
      R0[i] = MUL[rhs][iv];
      KF[i] = MUL[MUL[al][al]][iv];
      K0[i] = (uint8_t)be;
      K1[i] = MUL[MUL[al][be]][iv];
    } else {
      A1[i] = 1;
      R0[i] = (uint8_t)rhs;
      KF[i] = 1;
      K0[i] = 0;
      K1[i] = (uint8_t)be;
    }
  }
  int best = 0;
  int cntv[MAXQ], stampv[MAXQ], lastch[MAXQ], stamp = 0;
  memset(stampv, 0, sizeof stampv);
  for (int vF = 0; vF < Q; vF++) {
    for (int i = 0; i < cnt; i++) part[i] = R0[i] ^ MUL[KF[i]][vF];
    for (int s0 = 0; s0 < Q; s0++) {
      for (int i = 0; i < cnt; i++) part2[i] = part[i] ^ MUL[K0[i]][s0];
      for (int s1 = 0; s1 < Q; s1++) {
        const uint8_t *m1 = MUL[s1];
        int base = 0, lastall = -1, mx = 0;
        stamp++;
        for (int i = 0; i < cnt; i++) {
          int v = part2[i] ^ m1[K1[i]];
          if (A1[i]) {
            if (!v && ch[i] != lastall) base++, lastall = ch[i];
          } else {
            if (stampv[v] != stamp) stampv[v] = stamp, cntv[v] = 0, lastch[v] = -1;
            if (lastch[v] != ch[i]) {
              lastch[v] = ch[i];
              if (++cntv[v] > mx) mx = cntv[v];
            }
          }
        }
        if (base + mx > best) best = base + mx;
      }
    }
  }
  free(R0), free(KF), free(K0), free(K1), free(A1), free(part), free(part2), free(ch);
  return best;
}

// Exact max over all answer vectors (s points) and all round messages. Cells below `minc` consistent challenges are
// not examined, so the result is exact when it is >= minc. Returns the max; *ncell_out the number of cells examined.
static int cor4_search(int s, int minc, int maxcells, int *examined, int *top_count, int *exact) {
  int save = SP;
  SP = s;
  NCELLS = 0;
  COLLECT = 1;
  COLLECT_MIN = minc;
  BEST = 1 << 30; // disable pruning by BEST: collect every cell with at least minc challenges
  FLOOR_ = 0;
  for (int i = 0; i < NT; i++) LV[0][i] = i;
  refine(LV[0], NT, 0);
  COLLECT = 0;
  qsort(CELLS, (size_t)NCELLS, sizeof(cell_t), cell_cmp);
  int best = 0, done = 0;
  int *idx = malloc(sizeof(int) * (size_t)(NT + 1));
  *top_count = NCELLS ? CELLS[0].count : 0;
  *exact = 1;
  for (int c = 0; c < NCELLS; c++) {
    if (CELLS[c].count <= best) break;
    if (done == maxcells) {
      *exact = 0;
      break;
    }
    int cnt = cell_members(&CELLS[c], s, idx);
    int w = table_search(idx, cnt);
    if (w > best) best = w;
    done++;
  }
  free(idx);
  *examined = done;
  SP = save;
  return best;
}

// ------------------------------------------------------------------------------------------------------------
// Words.

static uint8_t PF[MAXH][MAXD + 2], PG[MAXH][MAXD + 2]; // a planted pair, when the word has one
static int HAVE_PAIR, XPOLE, EXC[MAXS], NEXC;

static void rand_poly(uint8_t *co, int deg) {
  memset(co, 0, MAXD + 2);
  for (int j = 0; j <= deg; j++) co[j] = (uint8_t)rq();
}

static void shuffle(int *p, int n) {
  for (int i = 0; i < n; i++) p[i] = i;
  for (int i = n - 1; i > 0; i--) {
    int j = rmod(i + 1), t = p[i];
    p[i] = p[j], p[j] = t;
  }
}

static int outside(void) { // a random element of E \ D
  for (;;) {
    int x = rq();
    if (x >= NN) return x;
  }
}

static void make_word(const char *kind) {
  int perm[MAXN];
  HAVE_PAIR = 0;
  NEXC = 0;
  XPOLE = outside();
  memset(F0, 0, sizeof F0);
  memset(F1, 0, sizeof F1);
  shuffle(perm, NN);
  if (!strcmp(kind, "random")) {
    for (int u = 0; u < H; u++)
      for (int x = 0; x < NN; x++) F0[u][x] = (uint8_t)rq(), F1[u][x] = (uint8_t)rq();
  } else if (!strncmp(kind, "planted", 7)) { // plantedK: a pair agreeing on exactly A - K common points
    int k = atoi(kind + 7);
    HAVE_PAIR = 1;
    for (int u = 0; u < H; u++) {
      rand_poly(PF[u], DEG - 1), rand_poly(PG[u], DEG);
      for (int i = 0; i < NN; i++) {
        int x = perm[i], vf = peval(PF[u], DEG, x), vg = peval(PG[u], DEG, x);
        if (i < AGR - k) F0[u][x] = (uint8_t)vf, F1[u][x] = (uint8_t)vg;
        else if (u == 0) F0[u][x] = (uint8_t)(vf ^ (1 + rmod(Q - 1))), F1[u][x] = (uint8_t)rq(); // really wrong at x
        else F0[u][x] = (uint8_t)rq(), F1[u][x] = (uint8_t)rq();
      }
    }
  } else if (!strcmp(kind, "pole") || !strcmp(kind, "poleflat") || !strcmp(kind, "cosetpole") || !strcmp(kind, "polerh") ||
             !strcmp(kind, "five8")) {
    uint8_t w[MAXN];
    if (!strcmp(kind, "pole"))
      for (int x = 0; x < NN; x++) w[x] = (uint8_t)rq();
    else if (!strcmp(kind, "poleflat")) { // w = x^(2(d+1)): degree d+1 on every flat of size 2(d+1)
      for (int x = 0; x < NN; x++) {
        int r = 1;
        for (int j = 0; j < 2 * (DEG + 1); j++) r = MUL[r][x];
        w[x] = (uint8_t)r;
      }
    } else if (!strcmp(kind, "cosetpole")) { // w = L_W(x), W the smallest subspace {0..|W|-1} with |W| >= A
      int sz = 1;
      while (sz < AGR) sz *= 2;
      for (int x = 0; x < NN; x++) {
        int r = 1;
        for (int v = 0; v < sz; v++) r = MUL[r][x ^ v];
        w[x] = (uint8_t)r;
      }
    } else if (!strcmp(kind, "five8")) { // w = x^(n/2) L_W(x), W = span(1, x): note 05, Theorem 2.1 (n = 32, d = 15, A <= 20)
      for (int x = 0; x < NN; x++) {
        int r = 1;
        for (int j = 0; j < NN / 2; j++) r = MUL[r][x];
        for (int v = 0; v < 4; v++) r = MUL[r][x ^ v];
        w[x] = (uint8_t)r;
      }
    } else { // polerh: floor(n / A) list members C_i = C_0 + R H_i of degree d+1 on disjoint sets, R with roots outside D
      int nr = DEG + 1 >= 6 ? 3 : 2, nm = NN / AGR;
      uint8_t C0[MAXD + 2], Rc[MAXD + 2] = {1}, Hc[MAXD + 2];
      rand_poly(C0, DEG + 1);
      for (int k = 0; k < nr; k++) {
        int rho;
        do {
          rho = outside();
          for (int j = 0; j < k; j++)
            if (EXC[j] == rho) rho = XPOLE;
        } while (rho == XPOLE);
        EXC[NEXC++] = rho;
        for (int j = k + 1; j >= 0; j--) Rc[j] = (j > 0 ? Rc[j - 1] : 0) ^ MUL[rho][Rc[j]];
      }
      for (int x = 0; x < NN; x++) w[x] = (uint8_t)rq();
      for (int i = 0; i < nm; i++) {
        rand_poly(Hc, DEG + 1 - nr);
        if (i == 0) memset(Hc, 0, sizeof Hc);
        for (int k = 0; k < AGR; k++) {
          int x = perm[i * AGR + k];
          w[x] = (uint8_t)(peval(C0, DEG + 1, x) ^ MUL[peval(Rc, nr, x)][peval(Hc, DEG + 1, x)]);
        }
      }
      // the exceptional answers: y^F = 1/(zeta - x0), y^G = C_0(zeta)/(zeta - x0); kept as a rational "pair" in PF, PG
      memcpy(PG[0], C0, sizeof C0);
    }
    for (int x = 0; x < NN; x++) F0[0][x] = INV[x ^ XPOLE], F1[0][x] = MUL[w[x]][INV[x ^ XPOLE]];
    for (int u = 1; u < H; u++) { // other lanes: exact codewords
      rand_poly(PF[u], DEG - 1), rand_poly(PG[u], DEG);
      for (int x = 0; x < NN; x++) F0[u][x] = (uint8_t)peval(PF[u], DEG, x), F1[u][x] = (uint8_t)peval(PG[u], DEG, x);
    }
  } else if (!strcmp(kind, "flatlist")) { // f0 = F exactly, f1 = G + x^(2d+1): the pairs (F, G + Q_V), V a flat of size 2(d+1)
    HAVE_PAIR = 0;
    for (int u = 0; u < H; u++) {
      rand_poly(PF[u], DEG - 1), rand_poly(PG[u], DEG);
      for (int x = 0; x < NN; x++) {
        int r = u == 0;
        for (int j = 0; j < 2 * DEG + 1 && u == 0; j++) r = MUL[r][x];
        F0[u][x] = (uint8_t)peval(PF[u], DEG, x), F1[u][x] = (uint8_t)(peval(PG[u], DEG, x) ^ (u == 0 ? r : 0));
      }
    }
  } else if (!strcmp(kind, "twopairs")) { // (F, G) on A points and (F, G + R H) on A other points, R with roots outside D
    int nr = 2;
    uint8_t Rc[MAXD + 2] = {1}, Hc[MAXD + 2];
    HAVE_PAIR = 1;
    for (int k = 0; k < nr; k++) {
      int rho;
      do rho = outside();
      while (k > 0 && rho == EXC[0]);
      EXC[NEXC++] = rho;
      for (int j = k + 1; j >= 0; j--) Rc[j] = (j > 0 ? Rc[j - 1] : 0) ^ MUL[rho][Rc[j]];
    }
    for (int u = 0; u < H; u++) {
      rand_poly(PF[u], DEG - 1), rand_poly(PG[u], DEG), rand_poly(Hc, DEG - nr);
      for (int i = 0; i < NN; i++) {
        int x = perm[i], vg = peval(PG[u], DEG, x);
        F0[u][x] = (uint8_t)peval(PF[u], DEG, x);
        F1[u][x] = (uint8_t)(i < AGR ? vg : i < 2 * AGR ? vg ^ MUL[peval(Rc, nr, x)][peval(Hc, DEG, x)] : rq());
      }
    }
  } else {
    fprintf(stderr, "unknown word %s\n", kind);
    exit(1);
  }
}

// ------------------------------------------------------------------------------------------------------------

// mode 0: uniform in E (the distribution of Theorem 3); 1: generic (outside D, distinct, not the pole of the word);
// 2: the exceptional points of the word (roots of R), then generic ones.
static void pick_points(int s, int mode) {
  for (int i = 0; i < s; i++) {
    ZR[i] = (uint8_t)rq();
    if (mode == 2 && i < NEXC) ZZ[i] = (uint8_t)EXC[i];
    else if (mode == 0) ZZ[i] = (uint8_t)rq();
    else
      for (int ok = 0; !ok;) {
        ZZ[i] = (uint8_t)outside();
        ok = ZZ[i] != XPOLE;
        for (int j = 0; j < i; j++) ok = ok && ZZ[j] != ZZ[i];
      }
  }
}

static const char *arg(int argc, char **argv, const char *key, const char *def) {
  size_t l = strlen(key);
  for (int i = 1; i < argc; i++)
    if (!strncmp(argv[i], key, l) && argv[i][l] == '=') return argv[i] + l + 1;
  return def;
}

static void run_points(int argc, char **argv) {
  int smax = atoi(arg(argc, argv, "s", "3")), trials = atoi(arg(argc, argv, "trials", "4")), smin = atoi(arg(argc, argv, "smin", "1"));
  int pmode = atoi(arg(argc, argv, "pmode", "0")), fl = atoi(arg(argc, argv, "floor", "0"));
  int big = NN * (NN - 1) / 2 > 2 * Q ? NN * (NN - 1) / 2 : 2 * Q, lg = H == 2;
  double k0 = 2.72 * Q;
  int k0i = (int)(k0 + 0.999);
  int mx[MAXS + 1] = {0}, mn[MAXS + 1], exc[MAXS + 1] = {0}, big_cells[MAXS + 1] = {0};
  for (int s = 1; s <= smax; s++) mn[s] = 1 << 30;
  for (int tr = 0; tr < trials; tr++) {
    pick_points(smax, pmode);
    SP = smax;
    prep_points();
    if (!QUIET) {
      printf("  points");
      for (int i = 0; i < smax; i++) printf(" (r=%d, zeta=%d%s)", ZR[i], ZZ[i], ZZ[i] < NN ? " in D" : "");
      printf(":");
    }
    for (int s = smin; s <= smax; s++) {
      int w = max_wins(s, fl), nc = 0, bad = 0;
      cls_t c = best_cell_class();
      if (w > mx[s]) mx[s] = w;
      if (w < mn[s]) mn[s] = w;
      if (w >= k0i) bad = count_exceptional(s, k0i, &nc);
      exc[s] += bad > 0;
      big_cells[s] += nc > 0;
      if (!QUIET)
        printf("  s=%d: %d%s [largest class %d, %s]%s", s, w, w <= fl ? " (<= floor)" : "", c.size,
               c.size == 0 ? "-" : c.pole ? "pole" : c.explained ? "pair of L_pair" : "polynomial, unexplained", bad ? " EXCEPTIONAL" : "");
    }
    if (!QUIET) printf("\n");
    fflush(stdout);
  }
  printf("  summary over %d point tuples (pmode %d), K0 = ceil(2.72 q) = %d, M = max(2q, C(n,2)) = %d:\n", trials, pmode, k0i, big);
  for (int s = smin; s <= smax; s++) {
    double eps = (double)(DEG + 1 + lg) / Q, bT = (double)NT * NT * NT, bL;
    for (int i = 0; i < s; i++) bT *= eps;
    bT /= (double)k0i * (k0i - 1) * (k0i - big > 0 ? k0i - big : 1);
    int ne, ml;
    list_stats(&ne, &ml);
    bL = 4.0 * ml * ml * ml * __builtin_pow(Q, 6) * __builtin_pow(eps, s) / (k0 * k0 * k0);
    printf("    s=%d: best answer vector wins between %d and %d challenges; tuples with some answer vector winning >= K0: %d; tuples in the "
           "exceptional set of Theorem 3 (an answer vector with >= K0 wins, < 74%% of them on one pair of L_pair): %d of %d; bounds on that "
           "fraction: |T|^3 eps^s / (K0 (K0-1) (K0-M)) = %.3g%s, 4 Lambda^3 q^6 eps^s / K0^3 = %.3g\n",
           s, mn[s], mx[s], big_cells[s], exc[s], trials, bT, k0i > big ? "" : " (K0 <= M: not applicable)", bL);
  }
}

static void run_tables(int argc, char **argv) {
  int s = atoi(arg(argc, argv, "s", "2")), trials = atoi(arg(argc, argv, "trials", "2"));
  int pmode = atoi(arg(argc, argv, "pmode", "1")), low = atoi(arg(argc, argv, "low", "-1"));
  int minc = atoi(arg(argc, argv, "minc", "0")), maxcells = atoi(arg(argc, argv, "maxcells", "40"));
  int nopoints = atoi(arg(argc, argv, "nopoints", "1"));
  if (low < 0) low = DEG; // coefficients of index >= low carry no weight (the high part)
  if (!minc) minc = Q / 2;
  for (int i = 0; i < 2; i++)
    for (int u = 0; u < H; u++)
      for (int j = 0; j <= DEG; j++) WT[i][u][j] = j < low ? (uint8_t)rq() : 0;
  // The running claim: false for the planted pair if there is one, else random.
  if (HAVE_PAIR) {
    uint8_t f[MAXH][MAXD], g[MAXH][MAXD];
    for (int u = 0; u < H; u++) memcpy(f[u], PF[u], MAXD), memcpy(g[u], PG[u], MAXD);
    CRUN = lam(0, f) ^ lam(1, g) ^ (1 + rmod(Q - 1));
  } else
    CRUN = rq();
  printf("  running claim: weights on coefficients below %d, c = %d%s\n", low, CRUN, HAVE_PAIR ? " (false for the planted pair)" : "");
  int *all = malloc(sizeof(int) * (size_t)(NT + 1));
  for (int i = 0; i < NT; i++) all[i] = i;
  if (nopoints) {
    int w = table_search(all, NT);
    printf("  no point claims (today's round shape): best round message wins %d of %d challenges (q = %d, 2q = %d)\n", w, Q * Q, Q, 2 * Q);
    fflush(stdout);
  }
  for (int tr = 0; tr < trials; tr++) {
    pick_points(s, pmode);
    SP = s;
    prep_points();
    int examined, top, exact;
    int w = cor4_search(s, minc, maxcells, &examined, &top, &exact);
    printf("  s=%d points", s);
    for (int i = 0; i < s; i++) printf(" (r=%d, zeta=%d)", ZR[i], ZZ[i]);
    printf(": max over all answers and round messages = %d winning challenges%s; largest consistent cell %d; cells examined %d; "
           "K0 = 2.72 q = %.0f\n",
           w, !exact ? " (NOT exact: cell cap hit)" : w >= minc ? " (exact)" : " (exact bound: below the cell floor)", top, examined, 2.72 * Q);
    fflush(stdout);
  }
  free(all);
}

// Two fold rounds of a 4-lane word with shared points: lanes (i1, i2), index 2 i1 + i2. Round 1 folds i1.
static void run_nested(int argc, char **argv, const char *kind) {
  int s = atoi(arg(argc, argv, "s", "2")), trials = atoi(arg(argc, argv, "trials", "1")), nc1 = atoi(arg(argc, argv, "nc1", "0"));
  uint8_t Uw[4][MAXN], cand[4][MAXD + 2];
  int perm[MAXN];
  shuffle(perm, NN);
  XPOLE = outside();
  for (int l = 0; l < 4; l++) rand_poly(cand[l], DEG - 2 >= 0 ? DEG - 2 : 0);
  for (int l = 0; l < 4; l++)
    for (int i = 0; i < NN; i++) {
      int x = perm[i];
      if (!strcmp(kind, "random")) Uw[l][x] = (uint8_t)rq();
      else if (!strncmp(kind, "planted", 7)) Uw[l][x] = i < AGR - atoi(kind + 7) ? (uint8_t)peval(cand[l], DEG, x) : (uint8_t)rq();
      else if (!strcmp(kind, "pole")) Uw[l][x] = l == 0 ? INV[x ^ XPOLE] : l == 3 ? 0 : MUL[rq()][INV[x ^ XPOLE]];
      else if (!strcmp(kind, "poleflat")) { // lane (0,0) = 1/(x - x0), lane (1,1) = x^(2(d+1))/(x - x0), others 0
        int r = 1;
        for (int j = 0; j < 2 * (DEG + 1); j++) r = MUL[r][x];
        Uw[l][x] = l == 0 ? INV[x ^ XPOLE] : l == 3 ? MUL[r][INV[x ^ XPOLE]] : 0;
      } else {
        fprintf(stderr, "unknown nested word %s\n", kind);
        exit(1);
      }
    }
  H = 1;
  int save_threads = NTHREADS;
  NTHREADS = 1;
  double k0 = 2.72 * Q;
  for (int tr = 0; tr < trials; tr++) {
    pick_points(s, 1);
    int total = nc1 ? nc1 : Q * Q, hist_over_q = 0, over_k0 = 0, worst = 0, worst_a = 0, worst_b = 0, nonempty_sum = 0;
    long tsum = 0;
    for (int it = 0; it < total; it++) {
      int a1 = nc1 ? rq() : it / Q, b1 = nc1 ? rq() : it % Q;
      for (int x = 0; x < NN; x++) {
        int ac = a1 ^ MUL[b1][x];
        F0[0][x] = Uw[2][x] ^ MUL[ac][Uw[0][x]]; // lane i2 = 0 of the fold: the F half of round 2
        F1[0][x] = Uw[3][x] ^ MUL[ac][Uw[1][x]]; // lane i2 = 1: the G half
      }
      build_lists();
      tsum += NT;
      int ne, ml;
      list_stats(&ne, &ml);
      nonempty_sum += ne;
      if (NT < 3) continue;
      SP = s;
      prep_points();
      int w = max_wins(s, Q); // anything above one line
      if (w > Q) hist_over_q++;
      if (w >= k0) {
        cls_t c = best_cell_class();
        if (!(c.explained && c.size >= 0.74 * w)) over_k0++;
      }
      if (w > worst) worst = w, worst_a = a1, worst_b = b1;
    }
    printf("  nested %s, points", kind);
    for (int i = 0; i < s; i++) printf(" zeta=%d", ZZ[i]);
    printf(": %d first challenges, mean |T| of round 2 = %.0f, mean challenges with a close codeword %.0f; round-2 max wins > q for %d of "
           "them; >= K0 = %.0f and not explained by a pair for %d; worst %d at c1 = (%d, %d)\n",
           total, (double)tsum / total, (double)nonempty_sum / total, hist_over_q, k0, over_k0, worst, worst_a, worst_b);
    fflush(stdout);
  }
  NTHREADS = save_threads;
}

int main(int argc, char **argv) {
  int m = atoi(arg(argc, argv, "m", "5")), nlog = atoi(arg(argc, argv, "N", "4"));
  const char *kind = arg(argc, argv, "word", "random"), *mode = arg(argc, argv, "mode", "points");
  gf_init(m);
  NN = 1 << nlog;
  DEG = atoi(arg(argc, argv, "d", "3"));
  AGR = atoi(arg(argc, argv, "A", "6"));
  H = atoi(arg(argc, argv, "H", "1"));
  NTHREADS = atoi(arg(argc, argv, "threads", "4"));
  QUIET = atoi(arg(argc, argv, "quiet", "0"));
  rng_s ^= (uint64_t)atoll(arg(argc, argv, "seed", "1")) * 0x9E3779B97F4A7C15ull;
  for (int i = 0; i < 20; i++) rnd();
  if (NN > MAXN || NN >= Q || DEG + 1 > MAXD - 1 || H > MAXH) {
    fprintf(stderr, "bad sizes\n");
    return 1;
  }
  printf("== GF(2^%d), n = %d, d = %d, A = %d (Johnson sqrt(n d) = %.2f), H = %d, word = %s, mode = %s, seed %s\n", m, NN, DEG, AGR,
         __builtin_sqrt((double)NN * DEG), H, kind, mode, arg(argc, argv, "seed", "1"));
  if (!strcmp(mode, "nested")) {
    run_nested(argc, argv, kind);
    return 0;
  }
  make_word(kind);
  build_lists();
  int ne, ml;
  list_stats(&ne, &ml);
  printf("  |T| = %d pairs (c, P); challenges with a close codeword: %d of %d; largest list Lambda = %d\n", NT, ne, Q * Q, ml);
  int nchk = atoi(arg(argc, argv, "check", "0"));
  if (nchk) printf("  naive list check on %d random challenges: %d mismatches\n", nchk, naive_check(nchk));
  fflush(stdout);
  if (NT < 3) return 0;
  class_scan(atoi(arg(argc, argv, "anchors", "600")));
  fflush(stdout);
  if (!strcmp(mode, "points")) run_points(argc, argv);
  else if (!strcmp(mode, "tables")) run_tables(argc, argv);
  return 0;
}
