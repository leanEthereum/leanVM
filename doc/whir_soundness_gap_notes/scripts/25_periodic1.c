// Researcher 25. Hyperplane-periodic members of U-periodic words (note 25, section 2).
//
// Lambda_U = span(u_1..u_r) is a random r-dimensional subspace of GF(2^64) (M = 2^r labels), h = M/2.
// For a parameter theta the F_2-linear map Psi_theta : Lambda_U -> K satisfies Psi^2 + Psi = s(theta) u.
// A type is (A, B, chi): A, B disjoint sets of labels, chi : B -> F_2. A word f on C = A + B has a member of
// that type for theta iff  f = g + (Psi_theta + chi) Z_A G_1 on C  with deg g <= h - 1 + slack, deg G_1 < h - |A|.
// The agreement on the 2M-point label domain is |S| = 2|A| + |B|, of 2M.
// The program enumerates the types with a given |S| (chi modulo affine functions) and reports those for which
// the spaces of admissible f, taken modulo polynomials of degree <= h - 1 + slack on C, have a common nonzero
// element for NT random values of theta. Such a type is a family that grows linearly with n.
//
// cc -O2 -o 25_periodic1 25_periodic1.c ;  ./25_periodic1 r S slack [seed] [verbose] [R]
// R (default 1) is the rate 2^-R: then h = M / 2^R and the label code has degree <= 2h - 1 + slack.
// r <= 4: every type. r = 5 (rate 1/2 only): the types allowed by the balance condition, see run5.
#include "25_gf.h"
#define NT 5
#define MAXM 32

static int r, M, h, slack, verbose;
static u64 ub[6], U[MAXM], lc[7], Psi[NT][MAXM], sth[NT];

static void setup(void) {
  for (int i = 0; i < r; i++) ub[i] = rnd();
  for (int x = 0; x < M; x++) { U[x] = 0; for (int i = 0; i < r; i++) if (x >> i & 1) U[x] ^= ub[i]; }
  // L(X) = sum lc[i] X^(2^i), lc[r] = 1
  u64 a[7] = {1, 0, 0, 0, 0, 0, 0};
  for (int t = 0; t < r; t++) {
    u64 v = 0, pw = ub[t];
    for (int i = 0; i <= t; i++) { v ^= gmul(a[i], pw); pw = gsq(pw); }
    u64 b[7] = {0};
    for (int i = 0; i <= t + 1; i++) b[i] = (i ? gsq(a[i - 1]) : 0) ^ gmul(v, a[i]);
    memcpy(a, b, sizeof a);
  }
  memcpy(lc, a, sizeof lc);
  for (int t = 0; t < NT; t++) {
    u64 al[6], top = rnd();
    al[r - 1] = top;
    for (int i = r - 1; i >= 1; i--) al[i - 1] = gsqrt(gmul(gsq(top), lc[i]) ^ al[i]);
    sth[t] = al[0] ^ gmul(gsq(top), lc[0]);
    for (int x = 0; x < M; x++) {
      u64 v = 0, pw = U[x];
      for (int i = 0; i < r; i++) { v ^= gmul(al[i], pw); pw = gsq(pw); }
      Psi[t][x] = v;
      if ((gsq(v) ^ v) != gmul(sth[t], U[x])) { fprintf(stderr, "Psi check failed\n"); exit(1); }
    }
  }
}

static long n_types, n_hits;

// one (A, B): enumerate chi
static void do_AB(unsigned A, unsigned B, long *hits_here) {
  int p = __builtin_popcount(A), sp = __builtin_popcount(B), nC = p + sp;
  int hd = h - 1 + slack;       // degree bound of g
  int dq = nC - (hd + 1);       // dimension of K^C / P_{<=hd}
  int nv = h - p;               // coefficients of G_1
  if (dq <= 0 || nv <= 0) return;
  unsigned Cm = A | B;
  u64 w[MAXM], za[MAXM];
  for (int x = 0; x < M; x++) {
    if (!(Cm >> x & 1)) continue;
    u64 d = 1;
    for (int y = 0; y < M; y++) if ((Cm >> y & 1) && y != x) d = gmul(d, U[x] ^ U[y]);
    w[x] = ginv(d);
    u64 z = 1;
    for (int y = 0; y < M; y++) if (A >> y & 1) z = gmul(z, U[x] ^ U[y]);
    za[x] = z;
  }
  // col[x][j*dq+i] = w_x za_x u_x^(i+j)
  static u64 col[MAXM][16 * 32], cls0[NT][16 * 32], d[16 * 32];
  int bl[MAXM], nb = 0;
  for (int x = 0; x < M; x++) if (B >> x & 1) bl[nb++] = x;
  for (int t = 0; t < NT; t++) memset(cls0[t], 0, sizeof(u64) * nv * dq);
  for (int q = 0; q < nb; q++) {
    int x = bl[q];
    u64 pw[64], c = gmul(w[x], za[x]);
    for (int e = 0; e < nv + dq; e++) { pw[e] = c; c = gmul(c, U[x]); }
    for (int j = 0; j < nv; j++) for (int i = 0; i < dq; i++) col[x][j * dq + i] = pw[i + j];
    for (int t = 0; t < NT; t++)
      for (int e = 0; e < nv * dq; e++) cls0[t][e] ^= gmul(col[x][e], Psi[t][x]);
  }
  // chi modulo affine functions: fix chi = 0 on a maximal affinely independent subset of B
  int fr[MAXM], nf = 0;
  {
    unsigned basis[6]; int nbas = 0, x0 = bl[0];
    for (int q = 1; q < nb; q++) {
      unsigned v = bl[q] ^ x0;
      for (int i = 0; i < nbas; i++) if ((v ^ basis[i]) < v) v ^= basis[i];
      if (v) { basis[nbas++] = v; for (int i = nbas - 1; i > 0 && basis[i] > basis[i - 1]; i--) { unsigned t = basis[i]; basis[i] = basis[i - 1]; basis[i - 1] = t; } }
      else fr[nf++] = bl[q];
    }
  }
  memset(d, 0, sizeof(u64) * nv * dq);
  unsigned chi = 0;
  u64 mat[2 * 16 * 32], I[16 * 32], J[16 * 32], Xt[16 * 32];
  for (unsigned long g = 0;; g++) {
    n_types++;
    int quick_ok = 0;
    if (2 * nv <= dq) {
      for (int e = 0; e < nv * dq; e++) { mat[e] = cls0[0][e] ^ d[e]; mat[nv * dq + e] = cls0[1][e] ^ d[e]; }
      if (rank_inplace(mat, 2 * nv, dq) == 2 * nv) quick_ok = 1;
    }
    if (!quick_ok) {
      for (int e = 0; e < nv * dq; e++) I[e] = cls0[0][e] ^ d[e];
      int di = rank_inplace(I, nv, dq);
      for (int t = 1; t < NT && di > 0; t++) {
        for (int e = 0; e < nv * dq; e++) Xt[e] = cls0[t][e] ^ d[e];
        di = row_intersect(I, di, Xt, nv, dq, J);
        memcpy(I, J, sizeof(u64) * di * dq);
      }
      if (di > 0) {
        n_hits++; (*hits_here)++;
        if (verbose || *hits_here <= 3) {
          printf("  HIT p=%d s'=%d A=%08x B=%08x chi=%08x dim=%d", p, sp, A, B, chi, di);
          if (nC == M) {
            // a representative of the class: f = (Psi_0 + chi) Z_A G_1 on B, 0 on A; its syndromes sum f u^i
            // The class in the quotient is I[0]; coordinates there are the syndromes sum_x w_x f_x u_x^i, i < dq,
            // and w_x is constant when C is everything, so the first nonzero coordinate gives the degree.
            int i0 = 0; while (i0 < dq && !I[i0]) i0++;
            printf("  f = polynomial of degree %d modulo degree <= %d (2*deg = %d, |S| = %d)", M - 1 - i0, hd, 2 * (M - 1 - i0), 2 * p + sp);
          }
          printf("\n");
        }
      }
    }
    if (g + 1 == (1ul << nf)) break;
    int bit = __builtin_ctzl(g + 1);
    int x = fr[bit];
    chi ^= 1u << x;
    for (int e = 0; e < nv * dq; e++) d[e] ^= col[x][e];
  }
}

// r = 5: A contains the affine basis {0, e1, .., e5} (true up to the affine group whenever A is in no hyperplane,
// which the balance condition forces), one representative per orbit of the 720 affine maps that permute these
// six points; B is the complement of A minus `omit` points; only (A, B) passing the balance condition
// 2|A| + |B cap H| <= M for all affine hyperplanes H (note 25, Proposition 2.6) are examined.
static int balance_ok(unsigned A, unsigned B) {
  int p = __builtin_popcount(A);
  for (unsigned phi = 1; phi < (unsigned)M; phi++) {
    unsigned H = 0;
    for (int x = 0; x < M; x++) if (__builtin_parity(x & phi)) H |= 1u << x;
    int b1 = __builtin_popcount(B & H), b0 = __builtin_popcount(B & ~H);
    if (2 * p + b1 > M || 2 * p + b0 > M) return 0;
  }
  return 1;
}
static unsigned apply_perm6(unsigned A, const int *pi) {
  // affine map sending base point i to base point pi[i], base points: 0 -> 0, i -> e_i (index 1 << (i-1))
  static const int bp[6] = {0, 1, 2, 4, 8, 16};
  int t = bp[pi[0]], img[5];
  for (int i = 0; i < 5; i++) img[i] = bp[pi[i + 1]] ^ t;
  unsigned out = 0;
  for (int x = 0; x < 32; x++) if (A >> x & 1) {
    int y = t;
    for (int i = 0; i < 5; i++) if (x >> i & 1) y ^= img[i];
    out |= 1u << y;
  }
  return out;
}
static int is_canonical6(unsigned A) {
  int pi[6] = {0, 1, 2, 3, 4, 5};
  // all 720 permutations by Heap-free simple enumeration
  int c[6] = {0};
  if (apply_perm6(A, pi) < A) return 0;
  int i = 0;
  while (i < 6) {
    if (c[i] < i) {
      int a = (i % 2 == 0) ? 0 : c[i];
      int t = pi[a]; pi[a] = pi[i]; pi[i] = t;
      if (apply_perm6(A, pi) < A) return 0;
      c[i]++; i = 0;
    } else { c[i] = 0; i++; }
  }
  return 1;
}
static void run5(int S) {
  if (4 * S <= 5 * M) { printf("the r = 5 reduction is only valid above 5/8 (|S| > 5M'/4), where B lies in no hyperplane\n"); return; }
  const unsigned base = 1u | 1u << 1 | 1u << 2 | 1u << 4 | 1u << 8 | 1u << 16;
  int rest[26], nr = 0;
  for (int x = 0; x < 32; x++) if (!(base >> x & 1)) rest[nr++] = x;
  for (int p = 6; p < h; p++) {
    int sp = S - 2 * p;
    if (sp < 1 || p + sp > M) continue;
    int omit = M - p - sp, extra = p - 6;
    long types0 = n_types, hits = 0, nA = 0, nAB = 0;
    { // Parseval form of the balance condition: beta = 2M - 4p - s' >= 0 and beta^2 (M - 1) >= s' (M - s')
      int beta = 2 * M - 4 * p - sp;
      if (beta < 0 || beta * beta * (M - 1) < sp * (M - sp)) {
        printf("type (p=%d, s'=%d): excluded by the Parseval form of the balance condition\n", p, sp);
        continue;
      }
    }
    int idx[8];
    for (int i = 0; i < extra; i++) idx[i] = i;
    for (;;) {
      unsigned A = base;
      for (int i = 0; i < extra; i++) A |= 1u << rest[idx[i]];
      int a_ok = 1; // necessary for balance: every affine hyperplane holds at least 2p - M/2 - omit points of A
      for (unsigned phi = 1; phi < (unsigned)M && a_ok; phi++) {
        unsigned H = 0;
        for (int x = 0; x < M; x++) if (__builtin_parity(x & phi)) H |= 1u << x;
        int c1 = __builtin_popcount(A & H), c0 = p - c1;
        if (c1 < 2 * p - M / 2 - omit || c0 < 2 * p - M / 2 - omit) a_ok = 0;
      }
      if (a_ok && is_canonical6(A)) {
        nA++;
        int cl[32], nc = 0;
        for (int x = 0; x < 32; x++) if (!(A >> x & 1)) cl[nc++] = x;
        // choose the omitted points
        int od[4];
        for (int i = 0; i < omit; i++) od[i] = i;
        for (;;) {
          unsigned B = ~A;
          for (int i = 0; i < omit; i++) B &= ~(1u << cl[od[i]]);
          if (balance_ok(A, B)) { nAB++; do_AB(A, B, &hits); }
          int i = omit - 1;
          while (i >= 0 && od[i] == nc - omit + i) i--;
          if (i < 0) break;
          od[i]++;
          for (int j2 = i + 1; j2 < omit; j2++) od[j2] = od[j2 - 1] + 1;
        }
      }
      int i = extra - 1;
      while (i >= 0 && idx[i] == nr - extra + i) i--;
      if (i < 0) break;
      idx[i]++;
      for (int j2 = i + 1; j2 < extra; j2++) idx[j2] = idx[j2 - 1] + 1;
    }
    printf("type (p=%d, s'=%d): %ld sets A (representatives), %ld balanced (A, B), %ld types (chi modulo affine), %ld with a common word\n", p, sp, nA, nAB, n_types - types0, hits);
    fflush(stdout);
  }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s r S slack [seed] [verbose] [R]\n", argv[0]); return 1; }
  r = atoi(argv[1]); int S = atoi(argv[2]); slack = atoi(argv[3]);
  if (argc > 4) { rng_s = strtoull(argv[4], 0, 0); for (int i = 0; i < 20; i++) rnd(); }
  verbose = argc > 5 ? atoi(argv[5]) : 0;
  int R = argc > 6 ? atoi(argv[6]) : 1; // rate 2^-R: label degree < 2h with h = M / 2^R
  M = 1 << r; h = M >> R;
  setup();
  printf("r=%d M'=%d labels 2M'=%d, |S|=%d (fraction %.4f), slack=%d, rate 1/%d (h=%d)\n", r, M, 2 * M, S, S / (2.0 * M), slack, 1 << R, h);
  if (r == 5 && R == 1) { run5(S); printf("total: %ld types, %ld hits\n", n_types, n_hits); return 0; }
  for (int p = 0; p < h; p++) {
    int sp = S - 2 * p;
    if (sp < 1 || p + sp > M) continue;
    long types0 = n_types, hits = 0;
    // all A of size p, all B of size sp in the complement
    for (unsigned long AA = 0; AA < (1ul << M); AA++) {
      unsigned A = (unsigned)AA;
      if (__builtin_popcount(A) != p) continue;
      unsigned comp = (unsigned)((1ul << M) - 1) & ~A;
      // enumerate subsets B of comp of size sp
      int cl[MAXM], nc = 0;
      for (int x = 0; x < M; x++) if (comp >> x & 1) cl[nc++] = x;
      int idx[MAXM];
      for (int i = 0; i < sp; i++) idx[i] = i;
      for (;;) {
        unsigned B = 0;
        for (int i = 0; i < sp; i++) B |= 1u << cl[idx[i]];
        do_AB(A, B, &hits);
        int i = sp - 1;
        while (i >= 0 && idx[i] == nc - sp + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j2 = i + 1; j2 < sp; j2++) idx[j2] = idx[j2 - 1] + 1;
      }
    }
    printf("type (p=%d, s'=%d): %ld types (chi modulo affine), %ld with a common word\n", p, sp, n_types - types0, hits);
    fflush(stdout);
  }
  printf("total: %ld types, %ld hits\n", n_types, n_hits);
  return 0;
}
