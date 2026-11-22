// Referee check 1 (note 20): who is right about the exceptional set, note 16 or notes 10, 11, 14?
//
// Written from scratch (no code shared with 10_deep_redteam.c, 15_nesting.c or 16_sharp.c).
//
// Setting: GF(2^6) (q = 64), D = span(1, x, x^2, x^3) (n = 16), one lane per half, degree d = 2, agreement A = 5,
// s = 2 points, every one of the q^2 ordered point pairs. Words:
//   kpairs  note 16's word: O_0 = F (degree 1), O_1 = G + R H_a on three disjoint sets of five columns, R of
//           degree 2 with both roots outside D, H_a three distinct constants. The three members (F, G + R H_a)
//           share their answers at every root of R.
//   random  O_0, O_1 uniform.
//
// For a point pair z the program enumerates the complete set T of (challenge, close codeword) once, then all q^4
// answer vectors, and reports per category of z how many pairs have:
//   K_void >= K0   K_void is the largest number of distinct challenges consistent with one answer vector that NO
//                  near pair (member of List(O; A-1, d)) matches at both points. For such answers the hypothesis
//                  of Lemma F(2) of note 14 is void, so with the zero weight every one of these challenges wins:
//                  the conclusion of Lemma F(2) fails at z, and z must lie in any valid exceptional set.
//   E3weak         the test of 10_deep_redteam.c (count_exceptional): some answer vector has >= K0 challenges and
//                  its largest class has less than 74 percent of that number.
//   E3strong       the conclusion of note 07's Theorem 3 fails: some answer vector has a set W of >= K0 elements
//                  with distinct challenges and no class holding 74 percent of W (note 15's criterion: at least
//                  0.26 K0 challenges have a consistent element outside the largest class).
//   in Exc14       for the best void block, the exact number N_lb of ordered triples of the block (one element per
//                  challenge) with pairwise different challenges and Q != 0. The program checks Q(zeta_m) = 0 for
//                  each, so each is counted by N(z) of note 14. N_lb >= K0 (K0-1) (K0-M) proves z is in Exc_j(O)
//                  as note 14 defines it (computed for the pairs with K_void >= K0).
//
// Build: cc -O2 -Wall -Wextra -o lines20 20_lines.c -lpthread
// Run:   ./lines20 [word=kpairs|random] [seed=20] [threads=3]   (kpairs: about 22 CPU-minutes, 8 minutes on three
//        idle threads; random: about 8 CPU-minutes)
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 64
#define N 16
#define DEG 2
#define AGR 5
#define MAXT 60000
#define MAXNP 512

static uint8_t MUL[Q][Q], INV[Q];
static uint64_t RNG = 88172645463325252ull;
static uint64_t rnd(void) {
  RNG ^= RNG << 13;
  RNG ^= RNG >> 7;
  RNG ^= RNG << 17;
  return RNG;
}
static int rq(void) { return (int)(rnd() % Q); }

static void init_field(void) {
  int ex[2 * Q], lg[Q], v = 1;
  for (int i = 0; i < Q - 1; i++) {
    ex[i] = v;
    lg[v] = i;
    v <<= 1;
    if (v & Q) v ^= 0x43; // x^6 + x + 1
  }
  for (int i = Q - 1; i < 2 * Q; i++) ex[i] = ex[i - (Q - 1)];
  for (int a = 1; a < Q; a++)
    for (int b = 1; b < Q; b++) MUL[a][b] = (uint8_t)ex[lg[a] + lg[b]];
  for (int a = 1; a < Q; a++) INV[a] = (uint8_t)ex[(Q - 1 - lg[a]) % (Q - 1)];
}

static int ev2(const uint8_t *c, int x) { return c[0] ^ MUL[c[1]][x] ^ MUL[c[2]][MUL[x][x]]; }

typedef struct {
  uint8_t al, be, p[3];
} elem_t;
static elem_t T[MAXT];
static int NT;
typedef struct {
  uint8_t f[2], g[3];
} pair_t;
static pair_t NP[MAXNP];
static int NNP;
static uint8_t O0[N], O1[N];
static int ROOT[2], NROOT;
static int K0, BIGM;
static long long THRESH;

static void interp3(const int *x, const uint8_t *y, uint8_t *c) {
  c[0] = c[1] = c[2] = 0;
  for (int i = 0; i < 3; i++) {
    int xi = x[i], xj = x[(i + 1) % 3], xk = x[(i + 2) % 3];
    int dn = INV[MUL[xi ^ xj][xi ^ xk]];
    c[0] ^= MUL[y[i]][MUL[MUL[xj][xk]][dn]];
    c[1] ^= MUL[y[i]][MUL[xj ^ xk][dn]];
    c[2] ^= MUL[y[i]][dn];
  }
}

static void build_word(const char *word) {
  NROOT = 0;
  if (!strcmp(word, "random")) {
    for (int x = 0; x < N; x++) O0[x] = (uint8_t)rq(), O1[x] = (uint8_t)rq();
    return;
  }
  uint8_t F[3] = {(uint8_t)rq(), (uint8_t)(1 + rnd() % (Q - 1)), 0}, G[3] = {(uint8_t)rq(), (uint8_t)rq(), (uint8_t)rq()};
  while (NROOT < 2) {
    int r = N + (int)(rnd() % (Q - N));
    if (NROOT == 0 || ROOT[0] != r) ROOT[NROOT++] = r;
  }
  uint8_t R[3] = {MUL[ROOT[0]][ROOT[1]], (uint8_t)(ROOT[0] ^ ROOT[1]), 1};
  int H[3] = {0, 0, 0}, nh = 0;
  while (nh < 3) {
    int h = 1 + (int)(rnd() % (Q - 1));
    if ((nh < 1 || H[0] != h) && (nh < 2 || H[1] != h)) H[nh++] = h;
  }
  int cols[N];
  for (int i = 0; i < N; i++) cols[i] = i;
  for (int i = N - 1; i > 0; i--) {
    int j = (int)(rnd() % (unsigned)(i + 1)), t = cols[i];
    cols[i] = cols[j];
    cols[j] = t;
  }
  for (int x = 0; x < N; x++) O0[x] = (uint8_t)ev2(F, x), O1[x] = (uint8_t)rq();
  for (int a = 0; a < 3; a++) {
    uint8_t Ga[3];
    for (int i = 0; i < 3; i++) Ga[i] = G[i] ^ MUL[R[i]][H[a]];
    for (int k = 0; k < 5; k++) O1[cols[5 * a + k]] = (uint8_t)ev2(Ga, cols[5 * a + k]);
  }
}

static void enumerate_T(void) {
  NT = 0;
  for (int al = 0; al < Q; al++)
    for (int be = 0; be < Q; be++) {
      uint8_t w[N];
      for (int x = 0; x < N; x++) w[x] = O1[x] ^ MUL[al ^ MUL[be][x]][O0[x]];
      int start = NT;
      for (int a = 0; a < N; a++)
        for (int b = a + 1; b < N; b++)
          for (int c = b + 1; c < N; c++) {
            int xs[3] = {a, b, c};
            uint8_t ys[3] = {w[a], w[b], w[c]}, co[3];
            interp3(xs, ys, co);
            int ag = 0;
            for (int x = 0; x < N; x++) ag += ev2(co, x) == w[x];
            if (ag < AGR) continue;
            int dup = 0;
            for (int i = start; i < NT && !dup; i++) dup = !memcmp(T[i].p, co, 3);
            if (dup) continue;
            if (NT >= MAXT) {
              fprintf(stderr, "T overflow\n");
              exit(1);
            }
            T[NT].al = (uint8_t)al, T[NT].be = (uint8_t)be;
            memcpy(T[NT].p, co, 3);
            NT++;
          }
    }
}

static void near_pairs(void) {
  NNP = 0;
  for (int a = 0; a < N; a++)
    for (int b = a + 1; b < N; b++)
      for (int c = b + 1; c < N; c++)
        for (int e = c + 1; e < N; e++) {
          int dn = INV[a ^ b];
          uint8_t f[3] = {0, MUL[O0[a] ^ O0[b]][dn], 0};
          f[0] = O0[a] ^ MUL[f[1]][a];
          if (ev2(f, c) != O0[c] || ev2(f, e) != O0[e]) continue;
          int xs[3] = {a, b, c};
          uint8_t ys[3] = {O1[a], O1[b], O1[c]}, g[3];
          interp3(xs, ys, g);
          if (ev2(g, e) != O1[e]) continue;
          int dup = 0;
          for (int i = 0; i < NNP && !dup; i++) dup = NP[i].f[0] == f[0] && NP[i].f[1] == f[1] && !memcmp(NP[i].g, g, 3);
          if (dup) continue;
          if (NNP >= MAXNP) {
            fprintf(stderr, "near pair overflow\n");
            exit(1);
          }
          NP[NNP].f[0] = f[0], NP[NNP].f[1] = f[1];
          memcpy(NP[NNP].g, g, 3);
          NNP++;
        }
}

static int in_class(const elem_t *e, const pair_t *u) {
  return e->p[0] == (u->g[0] ^ MUL[e->al][u->f[0]]) && e->p[1] == (u->g[1] ^ MUL[e->al][u->f[1]] ^ MUL[e->be][u->f[0]]) &&
         e->p[2] == (u->g[2] ^ MUL[e->be][u->f[1]]);
}

typedef struct {
  int kvoid, e3weak, e3strong, inexc, checked;
  long long nlb;
} res_t;

// Ordered triples of the elements idx[0..k) (pairwise different challenges) with Q != 0; verifies Q(zeta) = 0.
static long long count_triples(const int *idx, int k, const int *z, int *ok) {
  long long total = 0;
  *ok = 1;
  for (int i = 0; i < k; i++)
    for (int j = 0; j < k; j++) {
      if (j == i) continue;
      const elem_t *a = &T[idx[i]], *b = &T[idx[j]];
      for (int l = 0; l < k; l++) {
        if (l == i || l == j) continue;
        const elem_t *c = &T[idx[l]];
        // Q = (a_b + a_c) P_a + (a_a + a_c) P_b + (a_a + a_b) P_c, with a_e = al + be X
        int l1a = b->al ^ c->al, l1b = b->be ^ c->be, l2a = a->al ^ c->al, l2b = a->be ^ c->be, l3a = a->al ^ b->al, l3b = a->be ^ b->be;
        uint8_t qc[4] = {0, 0, 0, 0};
        for (int t = 0; t < 3; t++) {
          qc[t] ^= MUL[l1a][a->p[t]] ^ MUL[l2a][b->p[t]] ^ MUL[l3a][c->p[t]];
          qc[t + 1] ^= MUL[l1b][a->p[t]] ^ MUL[l2b][b->p[t]] ^ MUL[l3b][c->p[t]];
        }
        if (!(qc[0] | qc[1] | qc[2] | qc[3])) continue;
        total++;
        for (int m = 0; m < 2; m++) {
          int zz = z[m], z2 = MUL[zz][zz];
          if (qc[0] ^ MUL[qc[1]][zz] ^ MUL[qc[2]][z2] ^ MUL[qc[3]][MUL[z2][zz]]) *ok = 0;
        }
      }
    }
  return total;
}

static void analyse(const int *z, res_t *out, uint16_t *hist, uint8_t *g1, uint8_t *g2all, int *members, uint8_t *xy) {
  memset(out, 0, sizeof *out);
  out->checked = 1;
  uint8_t *x1 = xy, *y1 = xy + MAXT, *x2 = xy + 2 * MAXT, *y2 = xy + 3 * MAXT;
  for (int e = 0; e < NT; e++) {
    x1[e] = T[e].al ^ MUL[T[e].be][z[0]], y1[e] = (uint8_t)ev2(T[e].p, z[0]);
    x2[e] = T[e].al ^ MUL[T[e].be][z[1]], y2[e] = (uint8_t)ev2(T[e].p, z[1]);
  }
  for (int yf2 = 0; yf2 < Q; yf2++)
    for (int e = 0; e < NT; e++) g2all[yf2 * NT + e] = y2[e] ^ MUL[yf2][x2[e]];
  int best_key[4] = {-1, 0, 0, 0};
  for (int yf1 = 0; yf1 < Q; yf1++) {
    memset(hist, 0, sizeof(uint16_t) * Q * Q * Q);
    for (int e = 0; e < NT; e++) g1[e] = y1[e] ^ MUL[yf1][x1[e]];
    for (int yf2 = 0; yf2 < Q; yf2++) {
      const uint8_t *g2 = g2all + yf2 * NT;
      for (int e = 0; e < NT; e++) hist[(g1[e] * Q + yf2) * Q + g2[e]]++;
    }
    for (int b = 0; b < Q * Q * Q; b++) {
      if (hist[b] < 100) continue;
      int yg1 = b / (Q * Q), yf2 = (b / Q) % Q, yg2 = b % Q, nm = 0;
      const uint8_t *g2 = g2all + yf2 * NT;
      uint8_t seen[Q * Q];
      memset(seen, 0, sizeof seen);
      int k = 0;
      for (int e = 0; e < NT; e++)
        if (g1[e] == yg1 && g2[e] == yg2) {
          members[nm++] = e;
          int ch = T[e].al * Q + T[e].be;
          if (!seen[ch]) seen[ch] = 1, k++;
        }
      // matched by a near pair at both points?
      int matched = 0;
      for (int u = 0; u < NNP && !matched; u++) {
        uint8_t f[3] = {NP[u].f[0], NP[u].f[1], 0};
        matched = ev2(f, z[0]) == yf1 && ev2(NP[u].g, z[0]) == yg1 && ev2(f, z[1]) == yf2 && ev2(NP[u].g, z[1]) == yg2;
      }
      if (!matched && k > out->kvoid) {
        out->kvoid = k;
        best_key[0] = yf1, best_key[1] = yg1, best_key[2] = yf2, best_key[3] = yg2;
      }
      if (k < K0) continue;
      // largest class: a class that is not a near pair's has at most max(q, C(n,2)) = 120 < 0.74 K0 elements
      int largest = 0, top = -1;
      for (int u = 0; u < NNP; u++) {
        memset(seen, 0, sizeof seen);
        int sz = 0;
        for (int i = 0; i < nm; i++)
          if (in_class(&T[members[i]], &NP[u])) {
            int ch = T[members[i]].al * Q + T[members[i]].be;
            if (!seen[ch]) seen[ch] = 1, sz++;
          }
        if (sz > largest) largest = sz, top = u;
      }
      if (largest < 0.74 * k) out->e3weak = 1;
      memset(seen, 0, sizeof seen);
      int alt = 0;
      for (int i = 0; i < nm; i++)
        if (top < 0 || !in_class(&T[members[i]], &NP[top])) {
          int ch = T[members[i]].al * Q + T[members[i]].be;
          if (!seen[ch]) seen[ch] = 1, alt++;
        }
      if (alt >= 0.26 * K0) out->e3strong = 1;
    }
  }
  if (out->kvoid >= K0) {
    int yf1 = best_key[0], yg1 = best_key[1], yf2 = best_key[2], yg2 = best_key[3], nm = 0;
    uint8_t seen[Q * Q];
    memset(seen, 0, sizeof seen);
    for (int e = 0; e < NT; e++)
      if ((y1[e] ^ MUL[yf1][x1[e]]) == yg1 && (y2[e] ^ MUL[yf2][x2[e]]) == yg2) {
        int ch = T[e].al * Q + T[e].be;
        if (!seen[ch]) seen[ch] = 1, members[nm++] = e;
      }
    int ok;
    if (nm > 400) nm = 400; // a subset still gives a lower bound on N(z)
    out->nlb = count_triples(members, nm, z, &ok);
    out->checked = ok;
    out->inexc = out->nlb >= THRESH;
  }
}

static res_t RES[Q * Q];
static int NTHREADS = 3;
static void *worker(void *arg) {
  int id = (int)(intptr_t)arg;
  uint16_t *hist = malloc(sizeof(uint16_t) * Q * Q * Q);
  uint8_t *g1 = malloc(MAXT), *g2all = malloc((size_t)Q * MAXT), *xy = malloc(4 * MAXT);
  int *members = malloc(sizeof(int) * MAXT);
  for (int zi = id; zi < Q * Q; zi += NTHREADS) {
    int z[2] = {zi / Q, zi % Q};
    analyse(z, &RES[zi], hist, g1, g2all, members, xy);
  }
  free(hist), free(g1), free(g2all), free(members), free(xy);
  return NULL;
}

static int is_root(int x) {
  for (int i = 0; i < NROOT; i++)
    if (ROOT[i] == x) return 1;
  return 0;
}

int main(int argc, char **argv) {
  const char *word = "kpairs";
  for (int i = 1; i < argc; i++) {
    if (!strncmp(argv[i], "word=", 5)) word = argv[i] + 5;
    if (!strncmp(argv[i], "seed=", 5)) RNG ^= (uint64_t)atoll(argv[i] + 5) * 0x9e3779b97f4a7c15ull;
    if (!strncmp(argv[i], "threads=", 8)) NTHREADS = atoi(argv[i] + 8);
  }
  for (int i = 0; i < 20; i++) rnd();
  init_field();
  K0 = (int)(2.72 * Q) + 1; // ceil(2.72 q) = 175
  BIGM = 2 * Q > N * (N - 1) / 2 ? 2 * Q : N * (N - 1) / 2;
  THRESH = (long long)K0 * (K0 - 1) * (K0 - BIGM);
  build_word(word);
  enumerate_T();
  near_pairs();
  int unexplained = 0;
  for (int e = 0; e < NT; e++) {
    int ex = 0;
    for (int u = 0; u < NNP && !ex; u++) ex = in_class(&T[e], &NP[u]);
    unexplained += !ex;
  }
  printf("q = %d, n = %d, d = %d, A = %d, s = 2, K0 = %d, M = %d, K0 (K0-1) (K0-M) = %lld\n", Q, N, DEG, AGR, K0, BIGM, THRESH);
  printf("word %s: roots of R:", word);
  for (int i = 0; i < NROOT; i++) printf(" %d", ROOT[i]);
  printf("; |T| = %d, near pairs = %d, elements in no near pair's class = %d\n", NT, NNP, unexplained);
  pthread_t th[16];
  for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, worker, (void *)(intptr_t)i);
  for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);
  const char *names[6] = {"both coordinates roots of R", "exactly one root of R", "equal coordinates, not a root", "both in D, distinct",
                          "exactly one in D, other not a root", "generic"};
  int cnt[6] = {0}, kv[6] = {0}, ew[6] = {0}, es[6] = {0}, ie[6] = {0}, lo[6], hi[6] = {0}, bad = 0;
  for (int c = 0; c < 6; c++) lo[c] = 1 << 30;
  for (int zi = 0; zi < Q * Q; zi++) {
    int a = zi / Q, b = zi % Q, c;
    int ra = is_root(a), rb = is_root(b);
    if (ra && rb) c = 0;
    else if (ra || rb) c = 1;
    else if (a == b) c = 2;
    else if (a < N && b < N) c = 3;
    else if (a < N || b < N) c = 4;
    else c = 5;
    const res_t *r = &RES[zi];
    cnt[c]++, kv[c] += r->kvoid >= K0, ew[c] += r->e3weak, es[c] += r->e3strong, ie[c] += r->inexc;
    if (r->kvoid < lo[c]) lo[c] = r->kvoid;
    if (r->kvoid > hi[c]) hi[c] = r->kvoid;
    bad += !r->checked;
  }
  printf("%-36s %6s %11s %7s %9s %9s  %s\n", "category of the point pair", "pairs", "K_void>=K0", "E3weak", "E3strong", "in Exc14", "K_void range (blocks below 100 not examined)");
  int tk = 0, tw = 0, ts = 0, ti = 0;
  for (int c = 0; c < 6; c++) {
    if (!cnt[c]) continue;
    printf("%-36s %6d %11d %7d %9d %9d  %d to %d\n", names[c], cnt[c], kv[c], ew[c], es[c], ie[c], lo[c], hi[c]);
    tk += kv[c], tw += ew[c], ts += es[c], ti += ie[c];
  }
  printf("%-36s %6d %11d %7d %9d %9d\n", "all", Q * Q, tk, tw, ts, ti);
  printf("frequencies: K_void >= K0: %.4f, E3weak: %.4f, E3strong: %.4f\n", tk / (double)(Q * Q), tw / (double)(Q * Q), ts / (double)(Q * Q));
  if (NROOT) {
    double r = NROOT, q = Q;
    printf("predictions: note 16, 2 (r/q)(1 - r/q) + (q - r)/q^2 = %.4f; note 10's formula (n/q)^2 + C(3,2) (d/q)^2 = %.4f\n",
           2 * r / q * (1 - r / q) + (q - r) / (q * q), (N / q) * (N / q) + 3 * (DEG / q) * (DEG / q));
  }
  printf("triples counted in N_lb with Q(zeta_m) != 0 at some point: %s\n", bad ? "SOME (error)" : "none (as Lemma L1(c) says)");
  return 0;
}
