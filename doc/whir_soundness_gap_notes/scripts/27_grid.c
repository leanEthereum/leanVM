// Researcher 27. The grid at n = 32: U1 = <b0, b1>, U2 = <b2, b3>, four pairwise disjoint cosets P1, P1' of U1 and
// P2, P2' of U2, error sets P1^(') u P2^('). The four sets are congruent modulo 4 in the sense of Theorem W, so they
// are the error sets of a strict-top list (T = 24, k = 21). The program builds the differences Z_{S_0} - Z_{S_i} and
// prints the invariants of the curve: expected degree 4, J = 16, excess 2, opposite ratios with period groups of
// size 4, no period of the curve, of the triple functions or of the cross-ratio.
//   cc -O2 -o 27_grid 27_grid.c && ./27_grid [seed]
#include "27_common.h"
static void loc(unsigned S, poly *z) { z->d = 0; z->c[0] = 1; for (int p = 0; p < 32; p++) if (S >> p & 1) { z->c[z->d + 1] = 0; for (int j = z->d + 1; j >= 1; j--) z->c[j] = z->c[j - 1] ^ mul(z->c[j], pts[p]); z->c[0] = mul(z->c[0], pts[p]); z->d++; } }
int main(int argc, char **argv) {
  domain_init(5, argc > 1 ? strtoull(argv[1], 0, 10) : 1, 0);
  unsigned P1 = 0x0000000f, P1p = 0x000000f0, P2 = 0, P2p = 0;
  for (int u = 0; u < 4; u++) { P2 |= 1u << (16 + 4 * u); P2p |= 1u << (17 + 4 * u); }
  unsigned E[4] = {P1 | P2, P1p | P2, P1 | P2p, P1p | P2p};
  poly z[4], u[3]; for (int i = 0; i < 4; i++) loc(~E[i], &z[i]);
  for (int i = 1; i < 4; i++) padd(&u[i - 1], &z[0], &z[i]);
  printf("degrees of the differences: %d %d %d (k - 1 = 20)\n", u[0].d, u[1].d, u[2].d);
  info4 o; analyse4(u, &o); char key[400]; key4(&o, key);
  printf("J = %d, excJ = %d, gamD = %d\n%s\n", o.npair + 2 * o.ntrip + o.ndbl, o.npair + 2 * o.ntrip + o.ndbl - 3 * o.delta - 2, o.gamD, key);
  return 0;
}
