// Referee 80, item 3: the inequality of Section 6.1 on closures of free patterns under a cross-tree permutation (three members, exact ranks).
// usage: 80_closure <v> <variant 1|2> <patterns> <seed>
// Phi_x in {0, <a>, <b>, <c>, K^2} at random, pi a random permutation exchanging the trees, Psi_y = Phi_y + Phi_{pi^-1 y}.
// Checked: rank(Psi) >= A_j := sum_{x in T_j} dim(Phi_{pi^-1 x} + Phi_x + Phi_{pi x}) for j = 0, 1, and A_j >= w_Phi - ov_j.
#include "80_gf.h"
static unsigned join3(unsigned a, unsigned b) { // sum of two graphic spaces on three members (bitmask classes; 0 = zero space)
    if (popc(a) < 2) return popc(b) < 2 ? 0 : b;
    if (popc(b) < 2) return a;
    return a | b; // two classes of size >= 2 among three members always meet
}
int main(int argc, char **argv) {
    if (argc < 5) { printf("usage: 80_closure v variant patterns seed\n"); return 1; }
    int v = atoi(argv[1]), variant = atoi(argv[2]), npat = atoi(argv[3]); rnd_seed(strtoull(argv[4], 0, 10)); fe_selftest();
    tree_t T; tree_init(&T, v, 2, variant);
    int k = T.k, n = T.n, L = 2;
    static const unsigned TY[5] = {0, 3, 5, 6, 7};
    unsigned *phi = malloc(sizeof(unsigned) * n), *psi = malloc(sizeof(unsigned) * n);
    int *pi = malloc(sizeof(int) * n), *pinv = malloc(sizeof(int) * n), *a = malloc(sizeof(int) * k);
    fe *M = malloc(sizeof(fe) * (size_t)(2 * n + 1) * L * k);
    long viol = 0, viol2 = 0, below_w = 0, eq = 0, tested = 0, r4viol = 0, r4ok = 0; int worst = 1 << 20;
    fe *Kb = malloc(sizeof(fe) * (size_t)L * k * L * k);
    for (int it = 0; it < npat; it++) {
        int p0 = 20 + rnd_below(60), pf = rnd_below(30), run = rnd_below(3); // % of zero leaves, of K^2 leaves; runs along the orbit or not
        for (int h = 0; h < 2; h++) {
            for (int x = 0; x < k; x++) a[x] = x;
            for (int x = k - 1; x > 0; x--) { int y = rnd_below(x + 1), t = a[x]; a[x] = a[y]; a[y] = t; }
            for (int x = 0; x < k; x++) pi[h * k + x] = (1 - h) * k + a[x];
        }
        for (int x = 0; x < n; x++) pinv[pi[x]] = x;
        if (run == 0) for (int x = 0; x < n; x++) { int r = rnd_below(100); phi[x] = r < p0 ? 0 : r < p0 + pf ? 7 : TY[1 + rnd_below(3)]; }
        else { // constant runs along the orbits of pi (long free arcs)
            char *seen = calloc(n, 1);
            for (int s = 0; s < n; s++) { if (seen[s]) continue; int x = s; unsigned cur = TY[rnd_below(5)];
                do { seen[x] = 1; if (rnd_below(run == 1 ? 3 : 8) == 0) cur = TY[rnd_below(5)]; phi[x] = cur; x = pi[x]; } while (x != s); }
            free(seen);
        }
        int wphi = 0, A[2] = {0, 0}, ov[2] = {0, 0};
        for (int x = 0; x < n; x++) {
            psi[x] = join3(phi[x], phi[pinv[x]]);
            wphi += cls_dim(phi[x]);
            int j = x >= k;
            A[j] += cls_dim(join3(join3(phi[pinv[x]], phi[x]), phi[pi[x]]));
            ov[j] += cls_dim(phi[x]) + cls_dim(phi[pi[x]]) - cls_dim(join3(phi[x], phi[pi[x]]));
        }
        int w = pat_matrix(&T, psi, L, M);
        int rk = w ? fe_rank(M, w, L * k) : 0;
        tested++;
        int Amax = A[0] > A[1] ? A[0] : A[1], ovmin = ov[0] < ov[1] ? ov[0] : ov[1];
        if (rk < Amax) { viol++; if (viol <= 3) printf("VIOLATION: rank %d < A %d\n", rk, Amax); }
        if (Amax < wphi - ovmin) viol2++;
        if (rk == Amax) eq++;
        if (rk < wphi) { below_w++;
            if (rk <= 2 * k - 1) { // Proposition R4: such a pattern carries no list
                int dim = fe_kernel(M, w, L * k, Kb), g1 = 0, g2 = 0, g12 = 0;
                for (int d = 0; d < dim; d++) for (int e = 0; e < k; e++) { fe u1 = Kb[(size_t)d * 2 * k + e], u2 = Kb[(size_t)d * 2 * k + k + e]; if (u1) g1 = 1; if (u2) g2 = 1; if (u1 ^ u2) g12 = 1; }
                if (g1 && g2 && g12) { r4viol++; if (r4viol <= 3) printf("R4 VIOLATION: rank %d w_Phi %d\n", rk, wphi); } else r4ok++;
            }
        }
        if (rk - Amax < worst) worst = rk - Amax;
    }
    printf("(k,n)=(%d,%d) T%d: %ld closure patterns; rank < max_j A_j: %ld; A_j < w_Phi - ov_j: %ld; rank = max_j A_j in %ld; least rank - max A = %d; rank(Psi) < w_Phi in %ld, of which %ld have rank <= 2k - 1: %ld of those carry a list (R4 predicts 0)\n",
           k, n, variant, tested, viol, viol2, eq, worst, below_w, r4viol + r4ok, r4viol);
    return 0;
}
