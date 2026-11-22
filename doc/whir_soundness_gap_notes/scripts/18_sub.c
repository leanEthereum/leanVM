// Researcher 18. Exact maximum list over all words of a LINEAR FAMILY of words, n = 16 or 32 (subspace domain).
//
// The family is a space I of words modulo codewords, given by d basis words. A T-set S is an agreement set for the
// word w iff the Newton coefficients of w on S of order k..T-1 vanish. The scan walks all T-sets in increasing order of
// points, keeps the divided-difference diagonal of each basis word, and after each point beyond the k-th appends one
// row (the new top coefficients of the d basis words). When the rows reach rank d the whole subtree is dead and is cut.
// A surviving T-set has a kernel: a point of P(I) (hashed, then counted), or a larger subspace (recursed on).
// So one scan gives the exact maximum list over all words of I, provided d <= m + 1 (m = T - k). A family with
// d <= 2m + 1 is settled by taking the first member up to the symmetry group of the family (orbit representatives of
// all T-sets, by union-find) and scanning the subfamily it leaves, anchored at that member (codeword 0).
// Every count that matters is recomputed as a number of distinct maximal agreement sets of a concrete word, and the
// full list of that word is then computed by a scan with d = 1. The run says so when it is not exhaustive
// (a representative skipped as too large, or more subfamilies than SUBMAX).
//
// usage: 18_sub N k T dom seed threads mode ...
//   dom:  rand | real<m>            (random basis in GF(2^64) | span(1, x, .., x^{N-1}) in GF(2^m))
//   mode: fam S1 [S2 ...]           all lists containing the given agreement sets (hex masks, each of size >= T)
//         fix h                     all words invariant modulo codewords under the translations by the first h basis vectors
//         osc r                     all words that are polynomials of degree <= T + r modulo codewords
//         fixosc h r                both conditions
//         word w0 w1 ...            the list of one word (n hex values)
// build: cc -O2 -mcpu=native -o 18_sub 18_sub.c -lpthread
#include "18_gf.h"
#include <pthread.h>
#include <stdatomic.h>

#define NP 32
#define DMAX 16
static int NN, n, K, T, MD, MM, NTH;
static u64 pt[NP], inv[NP][NP];

// ---------- linear algebra: fraction-free Gauss-Jordan, kernel basis ----------
static int kern(u64 *A, int rows, int d, u64 *Kb) {
  int pc[64], isp[64], r = 0;
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
  u64 pre[65], suf[65];
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
// Newton coefficients of order K..|S|-1 of the d words W (d x n) on the set S: rows[(l)*d + i]
static int newton_rows(const u64 *W, int d, uint32_t S, u64 *rows) {
  int a[NP], c = 0;
  for (int x = 0; x < n; x++) if (S >> x & 1) a[c++] = x;
  u64 dg[NP];
  int nr = c - K;
  for (int i = 0; i < d; i++) {
    const u64 *w = W + (size_t)i * n;
    for (int j = 0; j < c; j++) {
      u64 cur = w[a[j]];
      for (int r = 1; r <= j; r++) { u64 nx = gf_mul(cur ^ dg[r - 1], inv[a[j]][a[j - r]]); dg[r - 1] = cur; cur = nx; }
      dg[j] = cur;
      if (j >= K) rows[(size_t)(j - K) * d + i] = cur;
    }
  }
  return nr > 0 ? nr : 0;
}
// words of span(W) that are a codeword on S: new basis W2 (returns its dimension)
static int restrict_basis(const u64 *W, int d, uint32_t S, u64 *W2) {
  u64 *rows = malloc((size_t)NP * d * sizeof(u64)), *Kb = malloc((size_t)d * d * sizeof(u64));
  int nr = newton_rows(W, d, S, rows);
  int dk = d - kern(rows, nr, d, Kb);
  for (int t = 0; t < dk; t++) for (int x = 0; x < n; x++) {
    u64 acc = 0;
    for (int i = 0; i < d; i++) if (Kb[t * d + i]) acc ^= gf_mul(Kb[t * d + i], W[(size_t)i * n + x]);
    W2[(size_t)t * n + x] = acc;
  }
  free(rows); free(Kb);
  return dk;
}
// maximal agreement set of the degree < K interpolant of w through the first K points of S
static uint32_t max_agree(const u64 *w, uint32_t S) {
  int a[NP], c = 0;
  for (int x = 0; x < n && c < K; x++) if (S >> x & 1) a[c++] = x;
  u64 cf[NP], dg[NP];
  for (int j = 0; j < K; j++) {
    u64 cur = w[a[j]];
    for (int r = 1; r <= j; r++) { u64 nx = gf_mul(cur ^ dg[r - 1], inv[a[j]][a[j - r]]); dg[r - 1] = cur; cur = nx; }
    dg[j] = cur; cf[j] = cur;
  }
  uint32_t M = 0;
  for (int x = 0; x < n; x++) {
    u64 v = cf[K - 1];
    for (int j = K - 2; j >= 0; j--) v = gf_mul(v, pt[x] ^ pt[a[j]]) ^ cf[j];
    if (v == w[x]) M |= 1u << x;
  }
  return M;
}

// w := w - (its degree < K interpolant through the first K points of S)
static void subtract_codeword(u64 *w, uint32_t S) {
  int a[NP], c = 0;
  for (int x = 0; x < n && c < K; x++) if (S >> x & 1) a[c++] = x;
  u64 cf[NP], dg[NP];
  for (int j = 0; j < K; j++) {
    u64 cur = w[a[j]];
    for (int r = 1; r <= j; r++) { u64 nx = gf_mul(cur ^ dg[r - 1], inv[a[j]][a[j - r]]); dg[r - 1] = cur; cur = nx; }
    dg[j] = cur; cf[j] = cur;
  }
  for (int x = 0; x < n; x++) {
    u64 v = cf[K - 1];
    for (int j = K - 2; j >= 0; j--) v = gf_mul(v, pt[x] ^ pt[a[j]]) ^ cf[j];
    w[x] ^= v;
  }
}

// ---------- families of words ----------
// span(W) (d x n). The last f basis words are the indicator words of "free" points fp[0..f) (at most m of them): points
// on which the family is unconstrained. Such a word is a codeword on every set avoiding its point, so for a set S only the columns
// of the other basis words and of the free points inside S count ("active"). ord lists the free points first.
typedef struct { u64 *W; int d, f, anchored; int fp[NP], ord[NP]; u64 hash; } fam_t;

static void make_family(const u64 *Win, int d, fam_t *F) {
  u64 *A = malloc((size_t)(d + 1) * n * sizeof(u64));
  memcpy(A, Win, (size_t)d * n * sizeof(u64));
  int pc[NP], r = 0;
  for (int c = 0; c < n && r < d; c++) {
    int p = -1;
    for (int i = r; i < d; i++) if (A[(size_t)i * n + c]) { p = i; break; }
    if (p < 0) continue;
    if (p != r) for (int j = 0; j < n; j++) { u64 t = A[(size_t)p * n + j]; A[(size_t)p * n + j] = A[(size_t)r * n + j]; A[(size_t)r * n + j] = t; }
    u64 iv = gf_inv(A[(size_t)r * n + c]);
    for (int j = 0; j < n; j++) A[(size_t)r * n + j] = gf_mul(A[(size_t)r * n + j], iv);
    for (int i = 0; i < d; i++) {
      if (i == r) continue;
      u64 f = A[(size_t)i * n + c];
      if (!f) continue;
      for (int j = 0; j < n; j++) A[(size_t)i * n + j] ^= gf_mul(A[(size_t)r * n + j], f);
    }
    pc[r++] = c;
  }
  if (r != d) { fprintf(stderr, "dependent family basis (%d of %d)\n", r, d); exit(1); }
  F->W = malloc((size_t)(d + 1) * n * sizeof(u64)); F->d = d; F->f = 0; F->anchored = 0;
  u64 h = 0x243f6a8885a308d3ull;
  for (size_t i = 0; i < (size_t)d * n; i++) { h ^= A[i]; h *= 0x9e3779b97f4a7c15ull; h ^= h >> 29; }
  F->hash = h;
  int isfree[NP]; memset(isfree, 0, sizeof isfree);
  int nz = 0, q = 0;
  // at most m free points: a word supported on at most m points has list 1, which is what dropping them relies on
  for (int i = 0; i < d; i++) { int wt = 0; for (int j = 0; j < n; j++) wt += A[(size_t)i * n + j] != 0; if (wt == 1 && F->f < MD) { isfree[pc[i]] = 1; F->fp[F->f++] = pc[i]; } }
  for (int i = 0; i < d; i++) { if (!isfree[pc[i]]) memcpy(F->W + (size_t)(nz++) * n, A + (size_t)i * n, n * sizeof(u64)); }
  for (int t = 0; t < F->f; t++) { memset(F->W + (size_t)(nz + t) * n, 0, n * sizeof(u64)); F->W[(size_t)(nz + t) * n + F->fp[t]] = 1; }
  for (int t = 0; t < F->f; t++) F->ord[q++] = F->fp[t];
  for (int x = 0; x < n; x++) if (!isfree[x]) F->ord[q++] = x;
  free(A);
}
// Given the m raw rows (orders K..T-1, all d columns) of a T-set S: rank over the active columns, kernel dimension,
// and for a one-dimensional kernel its vector (in all d coordinates) and a hash of the projective point.
static u64 point_key(const u64 *v, int d) { // v already normalised
  u64 h = 0x243f6a8885a308d3ull;
  for (int j = 0; j < d; j++) { h ^= v[j]; h *= 0x9e3779b97f4a7c15ull; h ^= h >> 29; }
  return h | 1;
}
// In an anchored family every word vanishes on the first member, whose codeword is 0. A set on which all the
// kernel words vanish is then only another agreement set of that same codeword, and is dropped (kd = 0).
static void classify(const fam_t *F, const u64 *raw, uint32_t S, int *rank, int *kd, u64 *key, u64 *vec) {
  int d = F->d, act[DMAX + NP], na = 0;
  for (int i = 0; i < d - F->f; i++) act[na++] = i;
  for (int t = 0; t < F->f; t++) if (S >> F->fp[t] & 1) act[na++] = d - F->f + t;
  u64 *A = malloc((size_t)(MD + 1) * (na + 1) * sizeof(u64)), *Kb = malloc((size_t)(na + 1) * (na + 1) * sizeof(u64));
  for (int l = 0; l < MD; l++) for (int c = 0; c < na; c++) A[l * na + c] = raw[(size_t)l * d + act[c]];
  int r = kern(A, MD, na, Kb);
  *rank = r; *kd = na - r;
  if (key) *key = 0;
  if (F->anchored && r > 0 && na - r >= 1) {
    int allzero = 1;
    for (int t = 0; t < na - r && allzero; t++) for (int x = 0; x < n && allzero; x++) if (S >> x & 1) {
      u64 acc = 0;
      for (int c = 0; c < na; c++) if (Kb[t * na + c]) acc ^= gf_mul(Kb[t * na + c], F->W[(size_t)act[c] * n + x]);
      if (acc) allzero = 0;
    }
    if (allzero) *kd = 0;
  }
  if (*kd == 1) {
    // normalise on the constrained part: a word supported on free points only is within m of a codeword, list 1
    u64 v[DMAX + NP]; memset(v, 0, sizeof v);
    for (int c = 0; c < na; c++) v[act[c]] = Kb[c];
    int d0 = d - F->f, fz = 0;
    while (fz < d0 && !v[fz]) fz++;
    if (fz == d0) *kd = 0;
    else {
      u64 iv = v[fz] == 1 ? 1 : gf_inv(v[fz]);
      for (int c = 0; c < d; c++) if (v[c]) v[c] = gf_mul(v[c], iv);
      if (key) *key = point_key(v, d0);
      if (vec) memcpy(vec, v, d * sizeof(u64));
    }
  }
  free(A); free(Kb);
}

// ---------- the scan ----------
typedef struct { uint32_t mask; uint8_t rank, kd; u64 key; } surv_t;
typedef struct {
  const fam_t *F;
  surv_t *out; size_t nout, cap;
  long nodes;
  u64 dg[NP + 1][DMAX][NP];       // divided-difference diagonals per depth
  u64 rows[NP + 1][DMAX * DMAX];  // echelon rows per depth (forward reduced)
  u64 raw[NP][DMAX];              // raw rows by order
  int rk[NP + 1], pcol[NP + 1][DMAX];
  int a[NP];
} scan_t;

static void push(scan_t *sc, uint32_t mask, int rank, int kd, u64 key) {
  if (sc->nout == sc->cap) { sc->cap = sc->cap ? 2 * sc->cap : 1024; sc->out = realloc(sc->out, sc->cap * sizeof(surv_t)); }
  sc->out[sc->nout].mask = mask; sc->out[sc->nout].rank = rank; sc->out[sc->nout].kd = kd; sc->out[sc->nout].key = key; sc->nout++;
}
// add the point x as the (j+1)-th point. Returns the new rank.
static inline int step(scan_t *sc, int j, int x) {
  int d = sc->F->d; const u64 *W = sc->F->W;
  for (int i = 0; i < d; i++) {
    const u64 *old = sc->dg[j][i]; u64 *nw = sc->dg[j + 1][i];
    u64 cur = W[(size_t)i * n + x];
    nw[0] = cur;
    for (int r = 1; r <= j; r++) { cur = gf_mul(cur ^ old[r - 1], inv[x][sc->a[j - r]]); nw[r] = cur; }
  }
  sc->a[j] = x;
  if (j < K) { sc->rk[j + 1] = 0; return 0; }
  u64 v[DMAX];
  for (int i = 0; i < d; i++) { v[i] = sc->dg[j + 1][i][j]; sc->raw[j][i] = v[i]; }
  int r = sc->rk[j];
  memcpy(sc->rows[j + 1], sc->rows[j], (size_t)r * d * sizeof(u64));
  memcpy(sc->pcol[j + 1], sc->pcol[j], r * sizeof(int));
  for (int p = 0; p < r; p++) {
    int c = sc->pcol[j][p]; u64 f = v[c];
    if (!f) continue;
    u64 pv = sc->rows[j][p * d + c];
    for (int i = 0; i < d; i++) v[i] = gf_mul(v[i], pv) ^ gf_mul(sc->rows[j][p * d + i], f);
  }
  int c = 0; while (c < d && !v[c]) c++;
  if (c < d) { memcpy(sc->rows[j + 1] + (size_t)r * d, v, d * sizeof(u64)); sc->pcol[j + 1][r] = c; r++; }
  sc->rk[j + 1] = r;
  return r;
}
// j points chosen, next position >= start; nskip free points were passed over
static void rec(scan_t *sc, int j, int start, uint32_t mask, int nskip) {
  const fam_t *F = sc->F; int d = F->d, f = F->f;
  if (j == T) {
    if (start < f) nskip += f - start;
    int r = sc->rk[T], deff = d - nskip;
    if (r >= deff) return;
    if (r == 0) { push(sc, mask, 0, deff, 0); return; }
    u64 raw[NP * DMAX], key; int r2, kd;
    for (int l = 0; l < MD; l++) memcpy(raw + (size_t)l * d, sc->raw[K + l], d * sizeof(u64));
    classify(F, raw, mask, &r2, &kd, &key, NULL);
    if (kd) push(sc, mask, r2, kd, key);
    return;
  }
  for (int p = start; p <= n - (T - j); p++) {
    sc->nodes++;
    int nsk = nskip + ((p < f ? p : f) - (start < f ? start : f));
    int r = step(sc, j, F->ord[p]);
    if (j >= K && p >= f - 1 && r >= d - nsk) continue; // dead subtree
    rec(sc, j + 1, p + 1, mask | 1u << F->ord[p], nsk);
  }
}
#define SPLIT 3
typedef struct { scan_t *sc; _Atomic int *next; int ntask; const int (*task)[SPLIT]; } wk_t;
static void *scan_worker(void *arg) {
  wk_t *w = arg; scan_t *sc = w->sc; const fam_t *F = sc->F;
  for (;;) {
    int t = atomic_fetch_add(w->next, 1);
    if (t >= w->ntask) break;
    sc->rk[0] = 0;
    uint32_t mask = 0; int nsk = 0, prev = 0, dead = 0;
    for (int j = 0; j < SPLIT && !dead; j++) {
      int p = w->task[t][j];
      nsk += (p < F->f ? p : F->f) - (prev < F->f ? prev : F->f);
      int r = step(sc, j, F->ord[p]);
      if (j >= K && p >= F->f - 1 && r >= F->d - nsk) dead = 1;
      mask |= 1u << F->ord[p]; prev = p + 1;
    }
    if (!dead) rec(sc, SPLIT, prev, mask, nsk);
  }
  return NULL;
}
// all T-sets S on which some word of the family, nonzero on the active part, is a codeword. Caller frees.
static size_t scan(const fam_t *F, surv_t **out, long *nodes) {
  if (T < SPLIT) { fprintf(stderr, "T too small\n"); exit(1); }
  static int (*task)[SPLIT]; int nt = 0;
  task = malloc((size_t)NP * NP * NP * sizeof(*task));
  for (int p0 = 0; p0 < n; p0++) for (int p1 = p0 + 1; p1 < n; p1++) for (int p2 = p1 + 1; p2 <= n - (T - 2); p2++) { task[nt][0] = p0; task[nt][1] = p1; task[nt][2] = p2; nt++; }
  _Atomic int next = 0;
  pthread_t th[64]; wk_t wk[64]; scan_t **scs = malloc(NTH * sizeof(*scs));
  for (int t = 0; t < NTH; t++) {
    scs[t] = calloc(1, sizeof(scan_t)); scs[t]->F = F;
    wk[t].sc = scs[t]; wk[t].next = &next; wk[t].ntask = nt; wk[t].task = (const int (*)[SPLIT])task;
    pthread_create(&th[t], NULL, scan_worker, &wk[t]);
  }
  size_t tot = 0; long nd = 0;
  for (int t = 0; t < NTH; t++) { pthread_join(th[t], NULL); tot += scs[t]->nout; nd += scs[t]->nodes; }
  surv_t *all = malloc((tot + 1) * sizeof(surv_t)); size_t p = 0;
  for (int t = 0; t < NTH; t++) { if (scs[t]->nout) memcpy(all + p, scs[t]->out, scs[t]->nout * sizeof(surv_t)); p += scs[t]->nout; free(scs[t]->out); free(scs[t]); }
  free(scs); free(task);
  *out = all; if (nodes) *nodes += nd;
  return tot;
}
static int cmpsurv(const void *a, const void *b) {
  const surv_t *x = a, *y = b;
  if (x->key != y->key) return x->key < y->key ? -1 : 1;
  return x->mask < y->mask ? -1 : x->mask > y->mask;
}
static int cmp32(const void *a, const void *b) { uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? -1 : x > y; }

// exact list of one word: distinct maximal agreement sets of size >= T. fam gets up to cap of them.
static int word_list(const u64 *w, uint32_t *fam, int cap) {
  fam_t F; F.W = (u64 *)w; F.d = 1; F.f = 0; for (int x = 0; x < n; x++) F.ord[x] = x;
  surv_t *sv; size_t ns = scan(&F, &sv, NULL);
  int L = 0;
  for (size_t i = 0; i < ns; i++) {
    int known = 0;
    for (int t = 0; t < L && t < cap; t++) if ((sv[i].mask & fam[t]) == sv[i].mask) { known = 1; break; }
    if (known) continue;
    uint32_t M = max_agree(w, sv[i].mask);
    if (L < cap) fam[L] = M;
    L++;
  }
  free(sv);
  if (L <= cap) qsort(fam, L, sizeof(uint32_t), cmp32);
  return L;
}

// ---------- results ----------
static int best = 0; static long best_count = 0;
static uint32_t best_fam[8][512]; static int best_nf = 0; static u64 best_word[8][NP];
static long hist[4096];
#define SUBMAX 20000
static int truncated, VERBOSE;

static void consider(const u64 *w) {
  uint32_t fam[512];
  int L = word_list(w, fam, 512);
  if (L > best) { best = L; best_count = 0; best_nf = 0; }
  if (L == best) {
    int dup = 0;
    for (int t = 0; t < best_nf; t++) if (!memcmp(best_fam[t], fam, (L < 512 ? L : 512) * sizeof(uint32_t))) dup = 1;
    if (!dup) { best_count++; if (best_nf < 8) { memcpy(best_fam[best_nf], fam, (L < 512 ? L : 512) * sizeof(uint32_t)); memcpy(best_word[best_nf], w, n * sizeof(u64)); best_nf++; } }
  }
}
static uint32_t chain[1 << 16]; static int nchain; // members fixed above the current node
// number of distinct codewords among the known members of w (the chain and `sets`); the full list is computed
// only when this reaches the best value so far
static void eval_point(const u64 *w, const surv_t *sets, size_t nsets) {
  uint32_t ms[1024]; int c = 0;
  for (size_t i = 0; i < (size_t)nchain + nsets && c < 1024; i++) {
    uint32_t S = i < (size_t)nchain ? chain[i] : sets[i - nchain].mask;
    int known = 0;
    for (int t = 0; t < c; t++) if ((S & ms[t]) == S) { known = 1; break; }
    if (!known) ms[c++] = max_agree(w, S);
  }
  if (c > best || (c == best && best_nf < 8)) consider(w);
}
// Members of one group (same constrained part vv[0..d0)) fix the word on the free points they contain. Exact search
// for the assignments of the free values (st[t] = 0 undecided, 1 fixed to val[t], 2 generic) with a compatible family
// that can reach the best list; every maximal one is evaluated.
static void asg_rec(const fam_t *F, const surv_t *mem, const u64 *vv, size_t g, int *st, u64 *val, surv_t *sel) {
  int d = F->d, f = F->f, d0 = d - f;
  size_t cnt = 0, live = 0; int pick = -1;
  for (size_t u = 0; u < g; u++) {
    int ok = 1, pend = -1;
    for (int t = 0; t < f && ok; t++) if (mem[u].mask >> F->fp[t] & 1) {
      if (st[t] == 2) ok = 0;
      else if (st[t] == 1) ok = val[t] == vv[u * d + d0 + t];
      else if (pend < 0) pend = t;
    }
    if (!ok) continue;
    live++;
    if (pend < 0) sel[cnt++] = mem[u]; else if (pick < 0) pick = pend;
  }
  if (!live || (long)live + nchain < best) return;
  if (pick < 0) {
    u64 w[NP]; memset(w, 0, sizeof w);
    for (int t = 0; t < d0; t++) if (vv[t]) for (int x = 0; x < n; x++) w[x] ^= gf_mul(vv[t], F->W[(size_t)t * n + x]);
    for (int t = 0; t < f; t++) w[F->fp[t]] ^= st[t] == 1 ? val[t] : (gf_rand() | 1);
    eval_point(w, sel, cnt);
    return;
  }
  // branch on the free point `pick`: each value proposed by a live member, or generic
  u64 *seen = malloc((g + 1) * sizeof(u64)); size_t nseen = 0;
  for (size_t u = 0; u < g; u++) {
    if (!(mem[u].mask >> F->fp[pick] & 1)) continue;
    int ok = 1;
    for (int t = 0; t < f && ok; t++) if (mem[u].mask >> F->fp[t] & 1) { if (st[t] == 2) ok = 0; else if (st[t] == 1) ok = val[t] == vv[u * d + d0 + t]; }
    if (!ok) continue;
    u64 a = vv[u * d + d0 + pick]; int known = 0;
    for (size_t z = 0; z < nseen; z++) if (seen[z] == a) { known = 1; break; }
    if (!known) seen[nseen++] = a;
  }
  for (size_t z = 0; z < nseen; z++) { st[pick] = 1; val[pick] = seen[z]; asg_rec(F, mem, vv, g, st, val, sel); }
  st[pick] = 2; asg_rec(F, mem, vv, g, st, val, sel);
  st[pick] = 0;
  free(seen);
}
static void first_T(uint32_t S, uint32_t *S2) { int c = 0; *S2 = 0; for (int x = 0; x < n && c < T; x++) if (S >> x & 1) { *S2 |= 1u << x; c++; } }
// node: scans all T-sets (cand == NULL) or a list of candidates against the family F.
static void node(const fam_t *F, const uint32_t *cand, size_t ncand, int depth, long *nodes) {
  int d = F->d;
  surv_t *sv; size_t ns;
  u64 *rows = malloc((size_t)NP * d * sizeof(u64));
  if (!cand) ns = scan(F, &sv, nodes);
  else {
    sv = malloc((ncand + 1) * sizeof(surv_t)); ns = 0;
    for (size_t i = 0; i < ncand; i++) {
      uint32_t S2; first_T(cand[i], &S2);
      newton_rows(F->W, d, S2, rows);
      int r, kd; u64 key;
      classify(F, rows, S2, &r, &kd, &key, NULL);
      if (kd == 0) continue;
      sv[ns].mask = cand[i]; sv[ns].rank = r; sv[ns].kd = kd; sv[ns].key = r == 0 ? 0 : key; ns++;
    }
  }
  size_t nfree = 0, npt = 0, nsub = 0;
  for (size_t i = 0; i < ns; i++) { if (sv[i].rank == 0) nfree++; else if (sv[i].kd == 1) npt++; else nsub++; }
  if (depth == 0 || VERBOSE) printf("#   %*snode d=%d (free points %d): survivors %zu (free %zu, points %zu, subspaces %zu)\n", 2 * depth, "", d, F->f, ns, nfree, npt, nsub), fflush(stdout);
  int base = nchain;
  for (size_t i = 0; i < ns && nchain < (1 << 16) - 2; i++) if (sv[i].rank == 0) chain[nchain++] = sv[i].mask;
  { // a generic word of the family
    u64 w[NP]; memset(w, 0, sizeof w);
    for (int i = 0; i < d; i++) { u64 c = d == 1 ? 1 : (gf_rand() | 1); for (int x = 0; x < n; x++) w[x] ^= gf_mul(c, F->W[(size_t)i * n + x]); }
    eval_point(w, NULL, 0);
  }
  // points: group by the constrained part of the word; inside a group the members also fix the word on their free
  // points, and members that disagree there are incompatible. Try every assignment of the free values.
  surv_t *pts = malloc((npt + 1) * sizeof(surv_t)); size_t q = 0;
  for (size_t i = 0; i < ns; i++) if (sv[i].rank > 0 && sv[i].kd == 1) pts[q++] = sv[i];
  qsort(pts, q, sizeof(surv_t), cmpsurv);
  int f = F->f;
  for (size_t i = 0; i < q;) {
    size_t j = i; while (j < q && pts[j].key == pts[i].key) j++;
    if (depth == 0) hist[j - i < 4095 ? j - i : 4095]++;
    if ((long)(j - i) + nchain >= best) {
      size_t g = j - i;
      u64 *vv = malloc(g * (size_t)d * sizeof(u64));
      for (size_t t = 0; t < g; t++) {
        uint32_t S2; first_T(pts[i + t].mask, &S2);
        newton_rows(F->W, d, S2, rows);
        int r, kd; u64 key;
        classify(F, rows, S2, &r, &kd, &key, vv + t * d);
      }
      // exact search over the assignments of the free values (asg_rec)
      surv_t *sel = malloc((g + 1) * sizeof(surv_t));
      int st[NP]; u64 val[NP];
      for (int t = 0; t < f; t++) st[t] = 0;
      asg_rec(F, pts + i, vv, g, st, val, sel);
      free(sel); free(vv);
    }
    i = j;
  }
  // subspace survivors: recurse, each with the points and the later subspace survivors as candidates.
  // Equal subfamilies are treated once (the first occurrence has the largest candidate list).
  if (nsub) {
    uint32_t *sub = malloc(nsub * sizeof(uint32_t)), *cl = malloc((ns + 1) * sizeof(uint32_t)); size_t s2 = 0;
    for (size_t i = 0; i < ns; i++) if (sv[i].rank > 0 && sv[i].kd >= 2) sub[s2++] = sv[i].mask;
    u64 *seen = malloc((nsub + 1) * sizeof(u64)); size_t nseen = 0; long done = 0;
    u64 *W2 = malloc((size_t)(d + 1) * n * sizeof(u64));
    for (size_t a = 0; a < nsub; a++) {
      uint32_t S2; first_T(sub[a], &S2);
      int d2 = restrict_basis(F->W, d, S2, W2);
      fam_t F2; make_family(W2, d2, &F2); F2.anchored = F->anchored;
      int dup = 0;
      for (size_t t = 0; t < nseen; t++) if (seen[t] == F2.hash) { dup = 1; break; }
      if (!dup) {
        seen[nseen++] = F2.hash;
        if (done >= SUBMAX) { if (!truncated) printf("#   WARNING: more than %d distinct subfamilies at depth %d: NOT exhaustive\n", SUBMAX, depth); truncated = 1; free(F2.W); break; }
        done++;
        size_t nc = 0;
        for (size_t i = 0; i < q; i++) cl[nc++] = pts[i].mask;
        for (size_t b2 = a + 1; b2 < nsub; b2++) cl[nc++] = sub[b2];
        chain[nchain++] = sub[a];
        node(&F2, cl, nc, depth + 1, nodes);
        nchain--;
      }
      free(F2.W);
    }
    if (depth == 0) printf("#   distinct subfamilies recursed on: %ld\n", done);
    free(sub); free(cl); free(seen); free(W2);
  }
  nchain = base;
  free(pts); free(sv); free(rows);
}

// ---------- families ----------
static int binom_odd(int j, int i) { return (i & j) == i; }
// words (as polynomials sum_{j>=K} c_j x^j) fixed modulo codewords by the translations by the first h basis vectors,
// with c_j = 0 for j > maxdeg. Returns the dimension, basis words in W.
static int fixed_words(int h, int maxdeg, const u64 *basis, u64 *W) {
  int cols = maxdeg - K + 1; // unknowns c_K..c_maxdeg
  int rows = h * cols;
  u64 *A = calloc((size_t)(rows + 1) * cols, sizeof(u64)), *Kb = malloc((size_t)cols * cols * sizeof(u64));
  for (int g = 0; g < h; g++) {
    u64 tp[NP + 1]; tp[0] = 1; for (int i = 1; i <= n; i++) tp[i] = gf_mul(tp[i - 1], basis[g]);
    // coefficient of x^i, i >= K, in sum_j c_j ((x+t)^j - x^j) = sum_{j>i} C(j,i) t^(j-i) c_j
    for (int i = K; i <= maxdeg; i++) for (int j = i + 1; j <= maxdeg; j++) if (binom_odd(j, i)) A[(size_t)(g * cols + i - K) * cols + (j - K)] = tp[j - i];
  }
  int dk = cols - kern(A, rows, cols, Kb);
  for (int t = 0; t < dk; t++) for (int x = 0; x < n; x++) {
    u64 acc = 0, xp = 1;
    for (int j = 0; j < K; j++) xp = gf_mul(xp, pt[x]);
    for (int j = K; j <= maxdeg; j++) { if (Kb[t * cols + j - K]) acc ^= gf_mul(Kb[t * cols + j - K], xp); xp = gf_mul(xp, pt[x]); }
    W[(size_t)t * n + x] = acc;
  }
  free(A); free(Kb);
  return dk;
}

// ---------- orbit representatives of T-sets under the stabiliser of span(b_0..b_{h-1}) in AGL(N,2) ----------
static u64 binom[33][33];
static inline u64 rank_set(uint32_t m) { u64 r = 0; int i = 1; while (m) { int b = __builtin_ctz(m); m &= m - 1; r += binom[b][i++]; } return r; }
static inline uint32_t apply_tab(const uint32_t tab[4][256], uint32_t m) { return tab[0][m & 255] | tab[1][m >> 8 & 255] | tab[2][m >> 16 & 255] | tab[3][m >> 24]; }
static size_t orbit_reps(int h, uint32_t **reps) {
  for (int i = 0; i <= 32; i++) { binom[i][0] = 1; for (int j = 1; j <= 32; j++) binom[i][j] = i ? binom[i - 1][j - 1] + binom[i - 1][j] : 0; }
  int ts = T <= n - T ? T : n - T; // work with the smaller of the set and its complement
  size_t tot = binom[n][ts];
  uint32_t *par = malloc(tot * sizeof(uint32_t));
  for (size_t i = 0; i < tot; i++) par[i] = (uint32_t)i;
  // generators: translation by b_{N-1}; E_{ij}: e_j -> e_j + e_i allowed unless (j < h and i >= h)
  int ngen = 0; uint8_t gen[64][NP];
  for (int x = 0; x < n; x++) gen[ngen][x] = x ^ (1 << (NN - 1));
  ngen++;
  if (h > 0) { for (int x = 0; x < n; x++) gen[ngen][x] = x ^ 1; ngen++; }
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) {
    if (i == j || (j < h && i >= h)) continue;
    for (int x = 0; x < n; x++) gen[ngen][x] = (x >> j & 1) ? x ^ (1 << i) : x;
    ngen++;
  }
  for (int g = 0; g < ngen; g++) {
    uint32_t tab[4][256];
    for (int by = 0; by < 4; by++) for (int v = 0; v < 256; v++) { uint32_t r = 0; for (int b = 0; b < 8; b++) if (v >> b & 1) { int x = 8 * by + b; if (x < n) r |= 1u << gen[g][x]; } tab[by][v] = r; }
    uint32_t m = (ts == 32) ? ~0u : ((1u << ts) - 1);
    for (size_t idx = 0; idx < tot; idx++) {
      size_t y = rank_set(apply_tab(tab, m));
      size_t a = idx, b = y;
      while (par[a] != a) { par[a] = par[par[a]]; a = par[a]; }
      while (par[b] != b) { par[b] = par[par[b]]; b = par[b]; }
      if (a != b) { if (a < b) par[b] = (uint32_t)a; else par[a] = (uint32_t)b; }
      // next mask with the same popcount (Gosper)
      uint32_t c = m & -m, r = m + c;
      if (r == 0 || idx + 1 == tot) break;
      m = (((r ^ m) >> 2) / c) | r;
    }
  }
  size_t nr = 0, cap = 0; *reps = NULL;
  uint32_t m = (1u << ts) - 1, full = n == 32 ? ~0u : ((1u << n) - 1);
  for (size_t idx = 0; idx < tot; idx++) {
    if (par[idx] == idx) { if (nr == cap) { cap = cap ? 2 * cap : 1024; *reps = realloc(*reps, cap * sizeof(uint32_t)); } (*reps)[nr++] = ts == T ? m : (full & ~m); }
    uint32_t c = m & -m, r = m + c;
    if (r == 0 || idx + 1 == tot) break;
    m = (((r ^ m) >> 2) / c) | r;
  }
  free(par);
  return nr;
}

static void print_word_info(const u64 *w, const uint32_t *fam, int L) {
  // degree of the interpolant modulo codewords: via the syndrome's leading zeros
  int z = 0;
  for (; z < MM; z++) { u64 s = 0; for (int x = 0; x < n; x++) { u64 p = 1; for (int i = 0; i < z; i++) p = gf_mul(p, pt[x]); s ^= gf_mul(w[x], p); } if (s) break; }
  int sizes[NP + 1], ih[NP + 1], deg[NP];
  memset(sizes, 0, sizeof sizes); memset(ih, 0, sizeof ih); memset(deg, 0, sizeof deg);
  for (int i = 0; i < L; i++) sizes[__builtin_popcount(fam[i])]++;
  for (int i = 0; i < L; i++) for (int j = i + 1; j < L; j++) ih[__builtin_popcount(fam[i] & fam[j])]++;
  for (int i = 0; i < L; i++) for (int a = 0; a < n; a++) if (fam[i] >> a & 1) deg[a]++;
  // invariance of the family under translations
  int ninv = 0;
  for (int t = 1; t < n; t++) {
    int ok = 1;
    for (int i = 0; i < L && ok; i++) { uint32_t s = 0; for (int x = 0; x < n; x++) if (fam[i] >> x & 1) s |= 1u << (x ^ t); int f = 0; for (int j = 0; j < L; j++) if (fam[j] == s) f = 1; ok = f; }
    ninv += ok;
  }
  printf("    word of degree %d modulo codewords (phantom degree %d); family invariant under %d nonzero translations\n", n - 1 - z, n - 1 - z - T, ninv);
  // per member: the cofactor (w - c)/Z_S of the lowest-degree representative of the word, and its roots in D.
  // All roots in D for all members: a multiset top. Degree 0: a strict top.
  {
    // monomial coefficients of the interpolant of w on D, reduced modulo codewords (degrees < K dropped at the end)
    u64 nc[NP], dg[NP], poly[NP + 1], bas[NP + 1];
    for (int j = 0; j < n; j++) { u64 cur = w[j]; for (int r = 1; r <= j; r++) { u64 nx = gf_mul(cur ^ dg[r - 1], inv[j][j - r]); dg[r - 1] = cur; cur = nx; } dg[j] = cur; nc[j] = cur; }
    memset(poly, 0, sizeof poly); memset(bas, 0, sizeof bas); bas[0] = 1; int db = 0;
    for (int j = 0; j < n; j++) {
      for (int c = 0; c <= db; c++) poly[c] ^= gf_mul(nc[j], bas[c]);
      for (int c = db + 1; c >= 1; c--) bas[c] = bas[c - 1] ^ gf_mul(bas[c], pt[j]);
      bas[0] = gf_mul(bas[0], pt[j]); db++;
    }
    int nsplit = 0, maxdeg = 0;
    for (int i = 0; i < L; i++) {
      // c = interpolant on the first K points of the member; q = (poly - c) / Z_S
      u64 num[NP + 1]; memcpy(num, poly, sizeof num);
      int a[NP], cnt = 0; for (int x = 0; x < n && cnt < K; x++) if (fam[i] >> x & 1) a[cnt++] = x;
      u64 cf[NP];
      for (int j = 0; j < K; j++) { u64 cur = w[a[j]]; for (int r = 1; r <= j; r++) { u64 nx = gf_mul(cur ^ dg[r - 1], inv[a[j]][a[j - r]]); dg[r - 1] = cur; cur = nx; } dg[j] = cur; cf[j] = cur; }
      memset(bas, 0, sizeof bas); bas[0] = 1; db = 0;
      for (int j = 0; j < K; j++) {
        for (int c = 0; c <= db; c++) num[c] ^= gf_mul(cf[j], bas[c]);
        for (int c = db + 1; c >= 1; c--) bas[c] = bas[c - 1] ^ gf_mul(bas[c], pt[a[j]]);
        bas[0] = gf_mul(bas[0], pt[a[j]]); db++;
      }
      int dn = n - 1; while (dn > 0 && !num[dn]) dn--;
      for (int x = 0; x < n; x++) if (fam[i] >> x & 1) { // divide by (X - pt[x]), exactly
        u64 carry = 0; for (int c = dn; c >= 0; c--) { u64 t2 = num[c] ^ gf_mul(carry, pt[x]); num[c] = carry; carry = t2; }
        dn--;
      }
      int deg0 = dn, roots = 0;
      for (int x = 0; x < n; x++) for (;;) {
        u64 v = 0; for (int c = dn; c >= 0; c--) v = gf_mul(v, pt[x]) ^ num[c];
        if (v || dn == 0) break;
        u64 carry = 0; for (int c = dn; c >= 0; c--) { u64 t2 = num[c] ^ gf_mul(carry, pt[x]); num[c] = carry; carry = t2; }
        dn--; roots++;
      }
      if (roots == deg0) nsplit++;
      if (deg0 > maxdeg) maxdeg = deg0;
    }
    printf("    cofactors (w - c)/Z_S have degree at most %d and split over D for %d of %d members: %s\n", maxdeg, nsplit, L, maxdeg == 0 ? "STRICT TOP" : nsplit == L ? "MULTISET TOP" : "NOT A TOP");
  }
  printf("    agreement sizes:"); for (int a = 0; a <= n; a++) if (sizes[a]) printf(" %dx%d", sizes[a], a);
  printf("; pairwise intersections:"); for (int a = 0; a <= n; a++) if (ih[a]) printf(" %dx%d", ih[a], a);
  printf("\n    point degrees:"); for (int a = 0; a < n; a++) printf(" %d", deg[a]);
  printf("\n    sets:"); for (int i = 0; i < L && i < 64; i++) printf(" %0*x", n / 4, fam[i]);
  printf("\n    word:"); for (int x = 0; x < n; x++) printf(" %llx", (unsigned long long)w[x]);
  printf("\n    points:"); for (int x = 0; x < n; x++) printf(" %llx", (unsigned long long)pt[x]);
  printf("\n");
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: %s N k T dom seed threads mode ...\n", argv[0]); return 1; }
  NN = atoi(argv[1]); n = 1 << NN; K = atoi(argv[2]); T = atoi(argv[3]);
  const char *dom = argv[4]; u64 seed = strtoull(argv[5], 0, 0); NTH = atoi(argv[6]);
  const char *mode = argv[7];
  VERBOSE = getenv("VERBOSE") != NULL;
  MD = T - K; MM = n - K;
  u64 basis[8];
  if (!strcmp(dom, "rand")) {
    gf_init(64);
    rng_state ^= seed * 0x2545f4914f6cdd1dull;
    for (;;) {
      for (int i = 0; i < NN; i++) basis[i] = gf_rand();
      int ok = 1;
      for (int a = 0; a < n; a++) { pt[a] = 0; for (int i = 0; i < NN; i++) if (a >> i & 1) pt[a] ^= basis[i]; if (a && !pt[a]) ok = 0; }
      if (ok) break;
    }
  } else {
    gf_init(atoi(dom + 4));
    for (int i = 0; i < NN; i++) basis[i] = 1ull << i;
    for (int a = 0; a < n; a++) pt[a] = a;
  }
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) inv[a][b] = a == b ? 0 : gf_inv(pt[a] ^ pt[b]);
  printf("# n=%d k=%d T=%d m=%d domain %s seed %llu mode", n, K, T, MD, dom, (unsigned long long)seed);
  for (int i = 7; i < argc && i < 12; i++) printf(" %s", argv[i]);
  printf("\n");
  u64 *W = calloc((size_t)(n + 1) * n, sizeof(u64)); int d = 0;
  long nodes = 0;
  if (!strcmp(mode, "word")) {
    u64 w[NP]; for (int x = 0; x < n; x++) w[x] = strtoull(argv[8 + x], 0, 16);
    consider(w);
  } else if (!strcmp(mode, "fam")) {
    // words vanishing on the first set, then restricted by the others
    uint32_t S0 = (uint32_t)strtoul(argv[8], 0, 16);
    for (int x = 0; x < n; x++) if (!(S0 >> x & 1)) { W[(size_t)d * n + x] = 1; d++; }
    for (int i = 9; i < argc; i++) {
      u64 *W2 = calloc((size_t)(n + 1) * n, sizeof(u64));
      d = restrict_basis(W, d, (uint32_t)strtoul(argv[i], 0, 16), W2);
      free(W); W = W2;
    }
    fam_t F; make_family(W, d, &F); F.anchored = 1;
    printf("# family space of dimension %d, of which %d free points\n", d, F.f);
    if (d > DMAX) { printf("too large\n"); return 0; }
    node(&F, NULL, 0, 0, &nodes);
  } else {
    int h = 0, r = -1;
    if (!strcmp(mode, "fix")) h = atoi(argv[8]);
    else if (!strcmp(mode, "osc")) r = atoi(argv[8]);
    else if (!strcmp(mode, "fixosc")) { h = atoi(argv[8]); r = atoi(argv[9]); }
    else { fprintf(stderr, "unknown mode\n"); return 1; }
    int maxdeg = r >= 0 ? T + r : n - 1;
    if (maxdeg > n - 1) maxdeg = n - 1;
    d = fixed_words(h, maxdeg, basis, W);
    printf("# family space of dimension %d\n", d);
    if (d <= MD + 1 && d <= DMAX) { fam_t F; make_family(W, d, &F); node(&F, NULL, 0, 0, &nodes); }
    else {
      // first member up to symmetry
      if (r >= 0 && h == 0) { /* the osculating flag is invariant under the whole affine group */ }
      uint32_t *reps; size_t nr = orbit_reps(h, &reps);
      printf("# first member: %zu orbit representatives\n", nr);
      fflush(stdout);
      u64 *W2 = calloc((size_t)(n + 1) * n, sizeof(u64));
      int dmaxseen = 0; long skipped = 0;
      long skipped_inv = 0;
      for (size_t i = 0; i < nr; i++) {
        if (h >= 1) { // a first member invariant under b_0: lists of invariant members only are lifts from n/2 points
          uint32_t sh = 0; for (int x = 0; x < n; x++) if (reps[i] >> x & 1) sh |= 1u << (x ^ 1);
          if (sh == reps[i]) { skipped_inv++; continue; }
        }
        int d2 = restrict_basis(W, d, reps[i], W2);
        if (d2 == 0) continue;
        for (int t = 0; t < d2; t++) subtract_codeword(W2 + (size_t)t * n, reps[i]);
        if (d2 > dmaxseen) dmaxseen = d2;
        if (d2 > DMAX || d2 > MD + 1) { skipped++; continue; }
        fam_t F; make_family(W2, d2, &F); F.anchored = 1;
        if (VERBOSE) printf("# representative %zu: %08x, family dimension %d\n", i, reps[i], d2), fflush(stdout);
        node(&F, NULL, 0, 1, &nodes);
        free(F.W);
        if ((i & 15) == 15) { printf("#   %zu of %zu representatives, best so far %d\n", i + 1, nr, best); fflush(stdout); }
      }
      printf("# largest second-level dimension %d, representatives skipped as too large %ld (if nonzero: NOT exhaustive), invariant first members left to the lift %ld\n", dmaxseen, skipped, skipped_inv);
      if (skipped) truncated = 1;
    }
  }
  printf("# scan nodes %ld\n", nodes);
  printf("RESULT n=%d k=%d T=%d dom=%s mode=%s: max list %d, distinct extremal families seen %ld%s\n", n, K, T, dom, mode, best, best_count, truncated ? " (TRUNCATED, lower bound only)" : "");
  for (int t = 0; t < best_nf && t < 3; t++) print_word_info(best_word[t], best_fam[t], best < 512 ? best : 512);
  if (hist[1] + hist[2] + hist[3]) { printf("# multiplicity of points at the top node:"); for (int i = 1; i < 4096; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]); printf("\n"); }
  return 0;
}
