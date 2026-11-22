// Researcher 15: is the nesting loss of Lemma D6 (note 11) / Proposition 8.1 (note 10) real?
//
// Reuses the red team's brute-force harness (10_deep_redteam.c: the complete lists of all folds of a pair of words,
// dependency classes, the exact maximum over all answer vectors and round messages) by including it, and adds:
//
//   mode=scan   a 4-lane word, lanes (u1, u2) at index 2 u1 + u2; round 1 folds u1 with c1 = (alpha1, beta1); for every
//               c1 the complete lists of round 2 are rebuilt and the point tuple is tested for the event of Theorem 3
//               of note 07 / Lemma D4 of note 11 in its semantic form:
//                 SPOILED(c1): some answer vector has a set W of consistent elements, pairwise distinct challenges,
//                 |W| >= K0 = ceil(2.72 q), in which no dependency class holds 74 percent of W.
//               For a cell (the elements consistent with one answer vector) with nch >= K0 distinct challenges and
//               largest class L1, such a W exists iff alt >= 0.26 K0, alt = number of challenges of the cell that have
//               a consistent element outside L1 (take 0.27 K0 such elements and fill up with L1). This differs from
//               10_deep_redteam.c's count_exceptional, which compares the size of L1 with nch and so does not see two
//               full classes that share all their answers.
//               For spoiled c1 (and a sample of the others) the exact maximum over all answer vectors and all round
//               messages of the number of winning second challenges is computed, with a running claim that the
//               planted members violate (Corollary 4 of note 07).
//               With fresh=1, every spoiled c1 is tested again with one more point drawn uniformly after c1 (a fresh
//               batch of one point): the collision survives only if the new point is a root of the difference.
//   mode=alg    the collision predicate of the planted family, exhaustively over all point tuples and all c1.
//   mode=scan2  an 8-lane word (word n2), lanes (u1, u2, u3) at index 4 u1 + 2 u2 + u3, two folds, then the same test on
//               round 3: prefixes (c1, c2) drawn from the predicted tree (c1 on its line, then c2 on its line), prefixes
//               with only c1 on its line, and uniform prefixes; and for one c1 on its line and one c1 off it, all c2.
//
// Words (word=...):
//   n1        Construction N1 of note 15: M members U_i = U_1 + R0 * (0, h_i, 0, H'_i), R0 with roots outside D, lanes
//             (0,0) and (1,0) exact, lanes (0,1) and (1,1) equal to member i on a set S_i of A points (disjoint sets).
//   flat4     lanes (0,1) = mu x^(2d-1), (1,1) = G + x^(2d-1), 2d a power of two (d = 4, flats of size 8): the members
//             G + (1 + mu a_c1) Q_V, V a flat of size 2d, for every c1.
//   n2        8 lanes, two members U_2 = U_1 + (X - rho) * (lambda0, 1) (x) (h, H') on the lanes with u3 = 1: the fold of
//             the difference is (X - rho)(1 + lambda0 a_c1)(H' + h a_c2).
//   random, planted1, planted2, pole, poleflat: the red team's nested words (Section 5.5 of note 10).
//
// Points (pts=...): generic (outside D, distinct, not special), roots (the first s-1 points at the special points of
// the word: roots of R0 for n1, points of D for flat4; the last one generic), uniform.
//
// Build: cc -O2 -o nest15 15_nesting.c -lpthread        Run: see 15_run.sh.
#define main redteam_main
#include "10_deep_redteam.c"
#undef main

static uint8_t Uw[4][MAXN];
static int NMEMB, NROOT, ROOTS[MAXD], MH[8]; // member i: lane (0,1) += R0 h_i, lane (1,1) += R0 H'_i
static uint8_t MHP[8][MAXD + 2];
static uint8_t MB[4][MAXD + 2];                                 // U_1
static uint8_t R0c[MAXD + 2];
static int MU; // flat4

static void fold_c1(int a1, int b1) {
  for (int x = 0; x < NN; x++) {
    int ac = a1 ^ MUL[b1][x];
    F0[0][x] = Uw[2][x] ^ MUL[ac][Uw[0][x]];
    F1[0][x] = Uw[3][x] ^ MUL[ac][Uw[1][x]];
  }
}

static void make_n1(int nmemb, int nroot) {
  int perm[MAXN];
  shuffle(perm, NN);
  NMEMB = nmemb;
  NROOT = nroot;
  if (nmemb * AGR > NN || nroot > DEG - 1 || nmemb > 8) {
    fprintf(stderr, "n1: need M A <= n, roots <= d - 1, M <= 8\n");
    exit(1);
  }
  rand_poly(MB[0], DEG - 2), rand_poly(MB[1], DEG - 1), rand_poly(MB[2], DEG - 1), rand_poly(MB[3], DEG);
  memset(R0c, 0, sizeof R0c);
  R0c[0] = 1;
  for (int k = 0; k < nroot; k++) {
    int rho, ok;
    do {
      rho = outside();
      ok = 1;
      for (int j = 0; j < k; j++) ok = ok && ROOTS[j] != rho;
    } while (!ok);
    ROOTS[k] = rho;
    for (int j = k + 1; j >= 0; j--) R0c[j] = (j > 0 ? R0c[j - 1] : 0) ^ MUL[rho][R0c[j]];
  }
  for (int i = 0; i < nmemb; i++) {
    MH[i] = i ? 1 + rmod(Q - 1) : 0;
    memset(MHP[i], 0, sizeof MHP[i]);
    if (i) rand_poly(MHP[i], DEG - nroot);
    for (int j = 0; j < i; j++)
      if (MH[j] == MH[i]) MH[i] ^= 1, j = -1; // distinct h_i, so every pair has a line
  }
  for (int x = 0; x < NN; x++) {
    Uw[0][x] = (uint8_t)peval(MB[0], DEG, x), Uw[2][x] = (uint8_t)peval(MB[2], DEG, x);
    Uw[1][x] = (uint8_t)rq(), Uw[3][x] = (uint8_t)rq();
  }
  for (int i = 0; i < nmemb; i++)
    for (int k = 0; k < AGR; k++) {
      int x = perm[i * AGR + k], r0 = peval(R0c, nroot, x);
      Uw[1][x] = (uint8_t)(peval(MB[1], DEG, x) ^ MUL[r0][MH[i]]);
      Uw[3][x] = (uint8_t)(peval(MB[3], DEG, x) ^ MUL[r0][peval(MHP[i], DEG, x)]);
    }
}

// The collision predicate of N1: members i < j have equal folded evaluations at zeta (both halves) under c1.
static inline int n1_coll_at(int i, int j, int a1, int b1, int zeta) {
  if (peval(R0c, NROOT, zeta) == 0) return 1;
  int ac = a1 ^ MUL[b1][zeta];
  return (peval(MHP[i], DEG, zeta) ^ peval(MHP[j], DEG, zeta) ^ MUL[ac][MH[i] ^ MH[j]]) == 0;
}
// The two folds are the same pair (then nothing collides: one pair with a larger agreement set).
static int n1_same(int i, int j, int a1, int b1) {
  // H'_i - H'_j + (a1 + b1 X)(h_i - h_j) == 0 as a polynomial
  int dh = MH[i] ^ MH[j];
  for (int k = 0; k <= DEG; k++) {
    int c = MHP[i][k] ^ MHP[j][k];
    if (k == 0) c ^= MUL[a1][dh];
    if (k == 1) c ^= MUL[b1][dh];
    if (c) return 0;
  }
  return 1;
}
static int n1_predict(int a1, int b1, int s) { // number of member pairs that collide at all s points
  int cnt = 0;
  for (int i = 0; i < NMEMB; i++)
    for (int j = i + 1; j < NMEMB; j++) {
      if (n1_same(i, j, a1, b1)) continue;
      int ok = 1;
      for (int m = 0; m < s && ok; m++) ok = n1_coll_at(i, j, a1, b1, ZZ[m]);
      cnt += ok;
    }
  return cnt;
}

static void make_flat4(void) {
  // d even, 2d a power of two (d = 4): lane (0,1) = mu x^(2d-1), lane (1,1) = G + x^(2d-1), lanes (0,0), (1,0) exact.
  uint8_t G[MAXD + 2];
  rand_poly(MB[0], DEG - 2), rand_poly(MB[2], DEG - 1), rand_poly(G, DEG);
  MU = 1 + rmod(Q - 1);
  for (int x = 0; x < NN; x++) {
    int r = 1;
    for (int j = 0; j < 2 * DEG - 1; j++) r = MUL[r][x];
    Uw[0][x] = (uint8_t)peval(MB[0], DEG, x), Uw[2][x] = (uint8_t)peval(MB[2], DEG, x);
    Uw[1][x] = MUL[MU][r];
    Uw[3][x] = (uint8_t)(peval(G, DEG, x) ^ r);
  }
}

// flat4: on the line a_c1(zeta_0) = 1/mu every member has the same folded value at zeta_0; the members whose flats
// contain the other points (points of D) then share all answers.
static int flat4_predict(int a1, int b1, int s) {
  if ((a1 ^ MUL[b1][ZZ[0]]) != INV[MU]) return 0;
  if (a1 == INV[MU] && b1 == 0) return 0; // the fold is G exactly
  for (int m = 1; m < s; m++)
    if (ZZ[m] == 0 || ZZ[m] >= NN) return 0;
  return 1;
}
static int predict(const char *word, int a1, int b1, int s) {
  if (!strcmp(word, "n1")) return n1_predict(a1, b1, s);
  if (!strcmp(word, "flat4")) return flat4_predict(a1, b1, s);
  return 0;
}

static void make_redteam(const char *kind) { // as run_nested of 10_deep_redteam.c
  uint8_t cand[4][MAXD + 2];
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
      else if (!strcmp(kind, "poleflat")) {
        int r = 1;
        for (int j = 0; j < 2 * (DEG + 1); j++) r = MUL[r][x];
        Uw[l][x] = l == 0 ? INV[x ^ XPOLE] : l == 3 ? MUL[r][INV[x ^ XPOLE]] : 0;
      } else {
        fprintf(stderr, "unknown word %s\n", kind);
        exit(1);
      }
    }
}

// ---- the semantic event of Theorem 3 for the current lists and points -------------------------------------------

typedef struct {
  int nch, n, l1, alt, cells;
} spoil_t;

static uint8_t *MARK;
static int cell_alt(const int *idx, int n, int nch, int thr, int *l1_out) {
  // smallest alt over the classes found through up to 40 anchors; early exit when alt < thr
  int best_alt = 1 << 30, best_l1 = 0;
  rat_t r;
  HP = realloc(HP, sizeof(hp_t) * (size_t)(NT + 2));
  MARK = realloc(MARK, (size_t)Q * Q);
  for (int tr = 0; tr < 40 && best_alt >= thr; tr++) {
    int ap = tr < n && n <= 40 ? tr : rmod(n);
    const elem_t *e0 = &TT[idx[ap]];
    int m = 0;
    for (int i = 0; i < n; i++) {
      const elem_t *e = &TT[idx[i]];
      if (e->a == e0->a && e->b == e0->b) continue;
      rat_of(e0, e, &r);
      HP[m].h = rat_hash(&r), HP[m].pos = i, m++;
    }
    qsort(HP, (size_t)m, sizeof(hp_t), hp_cmp);
    uint64_t bh = 0;
    int bs = 0;
    for (int i = 0; i < m;) {
      int j = i;
      while (j < m && HP[j].h == HP[i].h) j++;
      if (j - i > bs) bs = j - i, bh = HP[i].h;
      i = j;
    }
    // alt for the class (anchor, bh)
    memset(MARK, 0, (size_t)Q * Q);
    int alt = 0;
    for (int i = 0; i < n; i++) {
      const elem_t *e = &TT[idx[i]];
      int in = i == ap;
      if (!in && !(e->a == e0->a && e->b == e0->b)) {
        rat_of(e0, e, &r);
        in = bs > 0 && rat_hash(&r) == bh;
      }
      if (!in && !MARK[chal(idx[i])]) MARK[chal(idx[i])] = 1, alt++;
    }
    if (alt < best_alt) best_alt = alt, best_l1 = bs + 1;
  }
  (void)nch;
  *l1_out = best_l1;
  return best_alt;
}

static int spoiled(int s, int k0, spoil_t *info) {
  int save = SP, bad = 0;
  SP = s;
  NCELLS = 0, COLLECT = 1, COLLECT_MIN = k0, BEST = 1 << 30, FLOOR_ = 0;
  for (int i = 0; i < NT; i++) LV[0][i] = i;
  refine(LV[0], NT, 0);
  COLLECT = 0;
  int *idx = malloc(sizeof(int) * (size_t)(NT + 1));
  int thr = (int)(0.26 * k0 + 0.999);
  memset(info, 0, sizeof *info);
  info->cells = NCELLS;
  for (int c = 0; c < NCELLS; c++) {
    int n = cell_members(&CELLS[c], s, idx), l1;
    int alt = cell_alt(idx, n, CELLS[c].count, thr, &l1);
    if (alt >= thr) bad++;
    if (alt >= info->alt) info->alt = alt, info->nch = CELLS[c].count, info->n = n, info->l1 = l1;
  }
  free(idx);
  SP = save;
  return bad;
}

// Exact max over answers and round messages, with a running claim violated by every planted member's fold.
static int wins_once(int s, int a1, int b1, int minc, int maxcells, int *exact);
// At toy sizes a fold has a few pairs of L_pair by chance, and one of them satisfies a random claim with probability
// 1/q each (then every c2 wins, legitimately). The claim is redrawn up to four times when that happens.
static int wins_with_claim(int s, int a1, int b1, int minc, int maxcells, int *exact, int *redraws) {
  int w = 0;
  for (*redraws = 0; *redraws < 4; ++*redraws) {
    w = wins_once(s, a1, b1, minc, maxcells, exact);
    if (w < Q * Q / 4) break;
  }
  return w;
}
static int wins_once(int s, int a1, int b1, int minc, int maxcells, int *exact) {
  for (int i = 0; i < 2; i++)
    for (int j = 0; j <= DEG; j++) WT[i][0][j] = j < DEG ? (uint8_t)rq() : 0;
  if (NMEMB) {
    int vals[8], ac0 = a1, ac1 = b1;
    for (int i = 0; i < NMEMB; i++) {
      uint8_t f[MAXH][MAXD], g[MAXH][MAXD];
      memset(f, 0, sizeof f), memset(g, 0, sizeof g);
      // F = U_10 + a U_00, G = U_11 + a U_01 with U = U_1 + R0 (0, h_i, 0, H'_i)
      uint8_t l1[MAXD + 2], l3[MAXD + 2];
      for (int j = 0; j <= DEG; j++) l1[j] = MB[1][j], l3[j] = MB[3][j];
      for (int j = 0; j <= NROOT; j++) l1[j] ^= MUL[R0c[j]][MH[i]];
      for (int j = 0; j <= NROOT; j++)
        for (int k = 0; j + k <= DEG; k++) l3[j + k] ^= MUL[R0c[j]][MHP[i][k]];
      for (int j = 0; j <= DEG; j++) {
        f[0][j] = MB[2][j] ^ MUL[ac0][MB[0][j]] ^ (j ? MUL[ac1][MB[0][j - 1]] : 0);
        g[0][j] = l3[j] ^ MUL[ac0][l1[j]] ^ (j ? MUL[ac1][l1[j - 1]] : 0);
      }
      vals[i] = lam(0, f) ^ lam(1, g);
    }
    for (;;) {
      CRUN = rq();
      int ok = 1;
      for (int i = 0; i < NMEMB; i++) ok = ok && CRUN != vals[i];
      if (ok) break;
    }
  } else
    CRUN = rq();
  int examined, top;
  return cor4_search(s, minc, maxcells, &examined, &top, exact);
}

static void pick15(int s, const char *pts, const char *word) {
  int special[MAXN], nsp = 0;
  if (!strcmp(word, "n1"))
    for (int k = 0; k < NROOT; k++) special[nsp++] = ROOTS[k];
  else
    for (int x = 1; x < NN; x++) special[nsp++] = x; // flat4 and others: nonzero points of D
  for (int i = 0; i < s; i++) {
    ZR[i] = 0;
    int want_special = !strcmp(pts, "roots") && i >= 1; // point 0 stays generic
    if (!strcmp(pts, "roots1")) want_special = i >= 2;  // two generic points
    if (want_special) {
      if (!strcmp(word, "n1")) ZZ[i] = (uint8_t)special[(i - 1) % nsp];
      else {
        for (int ok = 0; !ok;) {
          ZZ[i] = (uint8_t)special[rmod(nsp)];
          ok = 1;
          for (int j = 1; j < i; j++) ok = ok && ZZ[j] != ZZ[i];
        }
      }
    } else if (!strcmp(pts, "uniform"))
      ZZ[i] = (uint8_t)rq();
    else
      for (int ok = 0; !ok;) {
        ZZ[i] = (uint8_t)outside();
        ok = ZZ[i] != XPOLE;
        for (int k = 0; k < NROOT && !strcmp(word, "n1"); k++) ok = ok && ZZ[i] != ROOTS[k];
        for (int j = 0; j < i; j++) ok = ok && ZZ[j] != ZZ[i];
      }
  }
}

static void run_scan(int argc, char **argv, const char *word) {
  int s = atoi(arg(argc, argv, "s", "3")), trials = atoi(arg(argc, argv, "trials", "1"));
  int nc1 = atoi(arg(argc, argv, "nc1", "0")), cor = atoi(arg(argc, argv, "cor", "6"));
  int fresh = atoi(arg(argc, argv, "fresh", "0")), fr_tested = 0, fr_still = 0, fr_pred = 0;
  int online = atoi(arg(argc, argv, "online", "0")); // with nc1: first scan this many random c1 with a predicted collision
  const char *pts = arg(argc, argv, "pts", "generic");
  double k0m = atof(arg(argc, argv, "k0", "2.72"));
  int k0 = (int)(k0m * Q + 0.999);
  printf("  K0 = %.2f q = %d\n", k0m, k0);
  H = 1;
  NTHREADS = 1;
  for (int tr = 0; tr < trials; tr++) {
    pick15(s, pts, word);
    printf("  points (%s):", pts);
    for (int i = 0; i < s; i++) printf(" zeta=%d%s", ZZ[i], ZZ[i] < NN ? " (in D)" : "");
    printf("\n");
    int total = nc1 ? nc1 : Q * Q, nsp = 0, npred = 0, both = 0, maxalt = 0, shown = 0, corA = 0, corB = 0;
    int *list = malloc(sizeof(int) * (size_t)(Q * Q + 1)), nlist = 0;
    if (nc1 && online) { // predicted c1 first (a random subset of `online` of them), then random ones
      for (int c = 0; c < Q * Q; c++)
        if (predict(word, c / Q, c % Q, s)) list[nlist++] = c;
      printf("  c1 with a predicted full collision: %d of %d", nlist, Q * Q);
      if (!strcmp(word, "n1")) {
        int vals[64], nv = 0;
        for (int i = 0; i < NMEMB; i++)
          for (int j = i + 1; j < NMEMB; j++) {
            int v = MUL[peval(MHP[i], DEG, ZZ[0]) ^ peval(MHP[j], DEG, ZZ[0])][INV[MH[i] ^ MH[j]]], seen = 0;
            for (int k = 0; k < nv; k++) seen |= vals[k] == v;
            if (!seen) vals[nv++] = v;
          }
        printf(" (%d member pairs, %d distinct lines a_c1(zeta_0) = const)", NMEMB * (NMEMB - 1) / 2, nv);
      }
      printf("\n");
      for (int i = nlist - 1; i > 0; i--) {
        int j = rmod(i + 1), t = list[i];
        list[i] = list[j], list[j] = t;
      }
      if (nlist > online) nlist = online;
      npred = nlist;
      for (int i = 0; i < nc1; i++) list[nlist++] = rq() * Q + rq();
      total = nlist;
    } else
      for (int i = 0; i < total; i++) list[nlist++] = nc1 ? rq() * Q + rq() : i;
    int npredseen = 0;
    long tsum = 0;
    for (int it = 0; it < total; it++) {
      int a1 = list[it] / Q, b1 = list[it] % Q;
      fold_c1(a1, b1);
      build_lists();
      tsum += NT;
      int pred = predict(word, a1, b1, s);
      npredseen += pred > 0;
      spoil_t inf = {0, 0, 0, 0, 0};
      int sp = 0;
      if (NT >= 3) {
        SP = s;
        prep_points();
        sp = spoiled(s, k0, &inf) > 0;
      }
      nsp += sp;
      both += sp && pred > 0;
      if (inf.alt > maxalt) maxalt = inf.alt;
      int do_cor = (sp && corA < cor) || (!sp && corB < cor && rmod(total) < 4 * cor);
      if (sp && shown < 8) {
        printf("    SPOILED c1 = (%d, %d): a cell with %d challenges, %d elements, largest class %d, alt = %d; predicted colliding member "
               "pairs: %d\n",
               a1, b1, inf.nch, inf.n, inf.l1, inf.alt, pred);
        shown++;
      }
      if (sp && fresh && s < MAXS) { // one more point, sampled after c1
        ZZ[s] = (uint8_t)rq(), ZR[s] = 0;
        SP = s + 1;
        prep_points();
        spoil_t inf2;
        int still = spoiled(s + 1, k0, &inf2) > 0;
        fr_tested++, fr_still += still, fr_pred += predict(word, a1, b1, s + 1) > 0;
        SP = s;
        prep_points();
      }
      if (do_cor && NT >= 3) {
        int exact, redraws, w = wins_with_claim(s, a1, b1, Q + Q / 2, 40, &exact, &redraws);
        printf("    c1 = (%d, %d) %s: max over all answers and round messages = %d winning c2%s (q = %d, 2q = %d, 4q = %d, K0 = %d)", a1, b1,
               sp ? "SPOILED" : "not spoiled", w, exact ? (w >= Q + Q / 2 ? " (exact)" : " (below the cell floor 1.5 q)") : " (cell cap hit)", Q,
               2 * Q, 4 * Q, k0);
        if (redraws) printf(" [claim redrawn %d times: a chance pair satisfied it]", redraws);
        printf("\n");
        if (sp) corA++;
        else corB++;
      }
      fflush(stdout);
    }
    printf("  %s, s = %d: %d first challenges scanned (mean |T| of round 2 = %.0f); SPOILED for %d of them (fraction %.5f; 1/q = %.5f); largest alt "
           "seen %d (threshold %d)",
           word, s, total, (double)tsum / total, nsp, (double)nsp / total, 1.0 / Q, maxalt, (int)(0.26 * k0 + 0.999));
    if (!strcmp(word, "n1") || !strcmp(word, "flat4"))
      printf("; c1 with a predicted full collision among those scanned: %d, of which spoiled: %d", npredseen, both);
    if (npred) printf(" (the first %d scanned were drawn from the predicted set, the other %d uniformly)", npred, total - npred);
    printf("\n");
    if (fresh)
      printf("  fresh point after c1: of the %d spoiled c1, %d are still spoiled with one more uniform point (predicted by the collision predicate: %d; "
             "expected about (r + 1)/q of them)\n",
             fr_tested, fr_still, fr_pred);
    free(list);
    fflush(stdout);
  }
}

// Exhaustive algebra for N1: for every point tuple, the number of c1 at which some member pair collides.
static void run_alg(int argc, char **argv) {
  int s = atoi(arg(argc, argv, "s", "3"));
  long nz = 1;
  for (int i = 0; i < s; i++) nz *= Q;
  long hist_ge_line = 0, hist_any = 0, tot = 0, hist_all = 0;
  int npairs = NMEMB * (NMEMB - 1) / 2;
  long *bycount = calloc((size_t)(Q * Q + 1), sizeof(long));
  for (long zi = 0; zi < nz; zi++) {
    long t = zi;
    for (int i = 0; i < s; i++) ZZ[i] = (uint8_t)(t % Q), t /= Q;
    int cnt = 0;
    for (int c = 0; c < Q * Q; c++) cnt += n1_predict(c / Q, c % Q, s) > 0;
    tot += cnt;
    bycount[cnt]++;
    hist_any += cnt > 0;
    hist_ge_line += cnt >= Q - 1;
    hist_all += cnt >= Q * Q - npairs;
  }
  double ez = (double)tot / ((double)nz * Q * Q);
  printf("  n1 algebra, M = %d members (%d pairs), R0 of degree %d, s = %d, all %ld point tuples and all %d c1:\n", NMEMB, npairs, NROOT, s, nz, Q * Q);
  printf("    E_z[fraction of c1 with a collision] = %.3e  (((r+1)/q)^s = %.3e per pair, times %d pairs = %.3e)\n", ez,
         __builtin_pow((NROOT + 1.0) / Q, s), npairs, npairs * __builtin_pow((NROOT + 1.0) / Q, s));
  printf("    point tuples with at least one such c1: %ld (%.3e); with at least q - 1 of them (a line): %ld (%.3e); with all c1: %ld (%.3e)\n",
         hist_any, (double)hist_any / nz, hist_ge_line, (double)hist_ge_line / nz, hist_all, (double)hist_all / nz);
  printf("    predictions: a line with probability about s (r/q)^(s-1) = %.3e; all c1 with probability (r/q)^s = %.3e\n",
         s * __builtin_pow((double)NROOT / Q, s - 1), __builtin_pow((double)NROOT / Q, s));
  for (int k = 1; k <= npairs; k++) {
    long c = 0;
    for (int v = k * (Q - 1); v < (k + 1) * (Q - 1) && v <= Q * Q; v++) c += bycount[v];
    if (k * (Q - 1) <= Q * Q) printf("    tuples with between %d and %d bad c1 (%d lines): %ld\n", k * (Q - 1), (k + 1) * (Q - 1) - 1, k, c);
  }
  for (int k = 1; k <= npairs; k++) {
    long c = 0;
    for (int v = k * (Q - 1) - (k - 1); v <= Q * Q; v++) c += bycount[v]; // k lines share at most k - 1 points pairwise here
    double tau = (double)(k * (Q - 1) - (k - 1)) / (Q * Q);
    printf("    Markov at tau = %d lines (%.5f): Pr_z[fraction >= tau] = %.3e, bound E/tau = %.3e, ratio %.3f\n", k, tau, (double)c / nz, ez / tau,
           ((double)c / nz) / (ez / tau));
  }
  (void)hist_ge_line;
  free(bycount);
}

// ---- depth two: an 8-lane word ------------------------------------------------------------------------------------
static uint8_t Uw8[8][MAXN];
static int L0, RHO, H2;
static uint8_t HP2[MAXD + 2];

static void make_n2(void) {
  int perm[MAXN];
  uint8_t base[8][MAXD + 2];
  shuffle(perm, NN);
  if (2 * AGR > NN || DEG < 3) {
    fprintf(stderr, "n2: need 2 A <= n, d >= 3\n");
    exit(1);
  }
  for (int l = 0; l < 8; l++) {
    int zeros = 3 - ((l >> 2) & 1) - ((l >> 1) & 1) - (l & 1);
    rand_poly(base[l], DEG - zeros);
  }
  RHO = outside();
  L0 = 1 + rmod(Q - 1), H2 = 1 + rmod(Q - 1);
  rand_poly(HP2, 1);
  for (int l = 0; l < 8; l++)
    for (int x = 0; x < NN; x++) Uw8[l][x] = (l & 1) ? (uint8_t)rq() : (uint8_t)peval(base[l], DEG, x);
  for (int i = 0; i < 2; i++)
    for (int k = 0; k < AGR; k++) {
      int x = perm[i * AGR + k];
      for (int l = 1; l < 8; l += 2) {
        int v = (l >> 2) & 1 ? 1 : L0, w = (l >> 1) & 1 ? peval(HP2, DEG, x) : H2;
        Uw8[l][x] = (uint8_t)(peval(base[l], DEG, x) ^ (i ? MUL[x ^ RHO][MUL[v][w]] : 0));
      }
    }
}
static void fold8(int a1, int b1) { // round 1 folds u1: the 4-lane word Uw, index 2 u2 + u3
  for (int l = 0; l < 4; l++)
    for (int x = 0; x < NN; x++) Uw[l][x] = Uw8[4 + l][x] ^ MUL[a1 ^ MUL[b1][x]][Uw8[l][x]];
}
static int n2_k1(int a1, int b1, int zeta) { return (MUL[L0][a1 ^ MUL[b1][zeta]] ^ 1) == 0; }
static int n2_k2(int a2, int b2, int zeta) { return (MUL[H2][a2 ^ MUL[b2][zeta]] ^ peval(HP2, DEG, zeta)) == 0; }
static int n2_predict(int a1, int b1, int a2, int b2, int s) {
  if (a1 == INV[L0] && b1 == 0) return 0;                               // 1 + lambda0 a_c1 = 0: the folds coincide
  if (MUL[H2][a2] == HP2[0] && MUL[H2][b2] == HP2[1]) return 0;         // H' + h a_c2 = 0: the same
  for (int m = 0; m < s; m++)
    if (!(ZZ[m] == RHO || n2_k1(a1, b1, ZZ[m]) || n2_k2(a2, b2, ZZ[m]))) return 0;
  return 1;
}
static int test_prefix(int a1, int b1, int a2, int b2, int s, int k0, spoil_t *inf) {
  fold8(a1, b1);
  fold_c1(a2, b2);
  build_lists();
  memset(inf, 0, sizeof *inf);
  if (NT < 3) return 0;
  SP = s;
  prep_points();
  return spoiled(s, k0, inf) > 0;
}
static void run_scan2(int argc, char **argv) {
  int s = atoi(arg(argc, argv, "s", "3")), ns = atoi(arg(argc, argv, "ns", "40"));
  double k0m = atof(arg(argc, argv, "k0", "2.72"));
  int k0 = (int)(k0m * Q + 0.999);
  H = 1, NTHREADS = 1, XPOLE = -1;
  // points: zeta_0, zeta_1 generic, the others at rho
  for (int i = 0; i < s; i++) {
    ZR[i] = 0;
    if (i >= 2) ZZ[i] = (uint8_t)RHO;
    else
      for (int ok = 0; !ok;) {
        ZZ[i] = (uint8_t)outside();
        ok = ZZ[i] != RHO && (i == 0 || ZZ[0] != ZZ[i]);
      }
  }
  printf("  n2: rho = %d, lambda0 = %d; points:", RHO, L0);
  for (int i = 0; i < s; i++) printf(" zeta=%d", ZZ[i]);
  printf("; K0 = %d\n", k0);
  long npred = 0, nhalf = 0;
  for (int c1 = 0; c1 < Q * Q; c1++) {
    int on1 = n2_k1(c1 / Q, c1 % Q, ZZ[0]) || n2_k1(c1 / Q, c1 % Q, ZZ[1]);
    nhalf += on1;
    for (int c2 = 0; c2 < Q * Q; c2++) npred += n2_predict(c1 / Q, c1 % Q, c2 / Q, c2 % Q, s);
  }
  printf("  predicted: %ld of %ld prefixes (c1, c2) have a full collision at round 3 (2 q^2 = %d); c1 on one of its two lines: %ld of %d\n", npred,
         (long)Q * Q * Q * Q, 2 * Q * Q, nhalf, Q * Q);
  spoil_t inf;
  int cnt[3] = {0, 0, 0}, sp[3] = {0, 0, 0}, shown = 0;
  while (cnt[0] < ns || cnt[1] < ns || cnt[2] < ns) {
    int a1 = rq(), b1 = rq(), a2 = rq(), b2 = rq(), kind;
    if (cnt[0] < ns) { // from the predicted tree
      b1 = rq(), a1 = INV[L0] ^ MUL[b1][ZZ[0]];
      b2 = rq(), a2 = MUL[peval(HP2, DEG, ZZ[1])][INV[H2]] ^ MUL[b2][ZZ[1]];
      if (!n2_predict(a1, b1, a2, b2, s)) continue;
      kind = 0;
    } else if (cnt[1] < ns) { // c1 on its line, c2 uniform
      b1 = rq(), a1 = INV[L0] ^ MUL[b1][ZZ[0]];
      if (n2_predict(a1, b1, a2, b2, s)) continue;
      kind = 1;
    } else {
      if (n2_predict(a1, b1, a2, b2, s)) continue;
      kind = 2;
    }
    int r = test_prefix(a1, b1, a2, b2, s, k0, &inf);
    cnt[kind]++, sp[kind] += r;
    if (r && shown < 3)
      printf("    SPOILED prefix c1 = (%d, %d), c2 = (%d, %d): a cell with %d challenges, %d elements, largest class %d, alt = %d\n", a1, b1, a2, b2,
             inf.nch, inf.n, inf.l1, inf.alt),
          shown++;
  }
  printf("  round 3 spoiled: %d of %d prefixes from the predicted tree; %d of %d with c1 on its line and c2 uniform; %d of %d uniform prefixes\n", sp[0],
         cnt[0], sp[1], cnt[1], sp[2], cnt[2]);
  // all c2 for one c1 on the line and one c1 off it
  for (int which = 0; which < 2; which++) {
    int b1 = rq(), a1 = which == 0 ? INV[L0] ^ MUL[b1][ZZ[0]] : rq(), nsp = 0, npr = 0, both = 0;
    if (which == 1 && (n2_k1(a1, b1, ZZ[0]) || n2_k1(a1, b1, ZZ[1]))) a1 ^= 1;
    for (int c2 = 0; c2 < Q * Q; c2++) {
      int pr = n2_predict(a1, b1, c2 / Q, c2 % Q, s), r = test_prefix(a1, b1, c2 / Q, c2 % Q, s, k0, &inf);
      nsp += r, npr += pr, both += r && pr;
    }
    printf("  c1 = (%d, %d) %s: all %d second challenges: round 3 spoiled for %d, predicted %d, both %d\n", a1, b1,
           which == 0 ? "on its line" : "off its lines", Q * Q, nsp, npr, both);
    fflush(stdout);
  }
}

int main(int argc, char **argv) {
  int m = atoi(arg(argc, argv, "m", "5")), nlog = atoi(arg(argc, argv, "N", "4"));
  const char *word = arg(argc, argv, "word", "n1"), *mode = arg(argc, argv, "mode", "scan");
  gf_init(m);
  NN = 1 << nlog;
  DEG = atoi(arg(argc, argv, "d", "3"));
  AGR = atoi(arg(argc, argv, "A", "6"));
  rng_s ^= (uint64_t)atoll(arg(argc, argv, "seed", "1")) * 0x9E3779B97F4A7C15ull;
  for (int i = 0; i < 20; i++) rnd();
  if (NN > MAXN || NN >= Q || DEG + 1 > MAXD - 1) {
    fprintf(stderr, "bad sizes\n");
    return 1;
  }
  printf("== GF(2^%d), n = %d, d = %d, A = %d, word = %s, mode = %s, seed %s\n", m, NN, DEG, AGR, word, mode, arg(argc, argv, "seed", "1"));
  XPOLE = -1;
  if (!strcmp(word, "n1")) {
    make_n1(atoi(arg(argc, argv, "M", "2")), atoi(arg(argc, argv, "r", "2")));
    printf("  N1: %d members, R0 with roots", NMEMB);
    for (int k = 0; k < NROOT; k++) printf(" %d", ROOTS[k]);
    printf(" (outside D)\n");
  } else if (!strcmp(word, "flat4"))
    make_flat4(), printf("  flat4: mu = %d\n", MU);
  else if (!strcmp(word, "n2"))
    make_n2();
  else
    make_redteam(word);
  if (!strcmp(mode, "alg")) run_alg(argc, argv);
  else if (!strcmp(mode, "scan2")) run_scan2(argc, argv);
  else run_scan(argc, argv, word);
  return 0;
}
