// Note 74, Theorem 2.5 probe: random subspaces U_i of F_2^N (so: many special positions), generic t_i in GF(2^64).
// Checks dim sum U_i (x) (1,t_i) == Phi(hull of the relation components). usage: 74_star trials seed Nmax mmax umax
#include "69_gf.h"
#include "69_tree.h"
#include "69_lin.h"
int main(int argc, char **argv) {
    long trials = atol(argv[1]); rng_seed(strtoull(argv[2], 0, 10)); int Nmax = atoi(argv[3]), mmax = atoi(argv[4]), umax = atoi(argv[5]);
    gf_init(); long bad = 0, dep = 0, proper = 0, nons = 0; int nsamp = 5;
    fe B[16][8][8], A[64 * 16], At[64 * 16], Kb[64 * 64], H[16][5 * 64 * 8], Up[64 * 8];
    for (long tr = 0; tr < trials; tr++) {
        int N = 2 + rng_below(Nmax - 1), m = 3 + rng_below(mmax - 2), u[16], off[17], W = 0;
        for (int i = 0; i < m; i++) { u[i] = 1 + rng_below(umax); if (u[i] > N) u[i] = N; off[i] = W; W += u[i];
            for (;;) { fe tmp[64]; for (int a = 0; a < u[i]; a++) for (int c = 0; c < N; c++) { B[i][a][c] = rng_u64() & 1; tmp[a * N + c] = B[i][a][c]; } if (gf_rank(tmp, u[i], N) == u[i]) break; } }
        off[m] = W; int hr[16] = {0}, rank = -1;
        for (int s = 0; s < nsamp; s++) {
            fe t[16]; for (int i = 0; i < m; i++) t[i] = gf_rand();
            for (int i = 0; i < m; i++) for (int a = 0; a < u[i]; a++) for (int c = 0; c < N; c++) { A[(off[i] + a) * 2 * N + c] = B[i][a][c]; A[(off[i] + a) * 2 * N + N + c] = B[i][a][c] ? t[i] : 0; }
            for (int a = 0; a < W; a++) for (int c = 0; c < 2 * N; c++) At[c * W + a] = A[a * 2 * N + c];
            int dim = gf_kernel(At, 2 * N, W, Kb); rank = W - dim;
            for (int i = 0; i < m; i++) for (int b = 0; b < dim; b++) { memcpy(H[i] + hr[i] * 8, Kb + b * W + off[i], sizeof(fe) * u[i]); hr[i]++; }
        }
        int drop = 0, ur = 0, pr = 0;
        for (int i = 0; i < m; i++) {
            fe Hc[5 * 64 * 8]; for (int a = 0; a < hr[i]; a++) memcpy(Hc + a * u[i], H[i] + a * 8, sizeof(fe) * u[i]);
            int kp = hr[i] ? gf_rank(Hc, hr[i], u[i]) : 0; drop += u[i] - kp; if (kp && kp < u[i]) pr = 1;
            for (int b = 0; b < kp; b++) { for (int c = 0; c < N; c++) { fe x = 0; for (int a = 0; a < u[i]; a++) if (B[i][a][c]) x ^= Hc[b * u[i] + a]; Up[ur * N + c] = x; } ur++; }
        }
        int du = ur ? gf_rank(Up, ur, N) : 0, phi = 2 * du + drop;
        if (phi != rank) { bad++; if (bad <= 5) { printf("MISMATCH N=%d m=%d rank=%d phi=%d W=%d\n", N, m, rank, phi, W); for (int i = 0; i < m; i++) { printf("  U_%d:", i); for (int a = 0; a < u[i]; a++) { printf(" "); for (int c = 0; c < N; c++) printf("%d", (int)B[i][a][c]); } printf("\n"); } } }
        if (rank < W) dep++; if (pr) proper++; if (rank < W && rank < 2 * N) nons++;
    }
    printf("# trials %ld (N<=%d, m<=%d, dims<=%d): Phi(hull) != rank: %ld, dependent: %ld, dependent and not of full rank 2N: %ld, hull proper somewhere: %ld\n", trials, Nmax, mmax, umax, bad, dep, nons, proper);
    return 0;
}
