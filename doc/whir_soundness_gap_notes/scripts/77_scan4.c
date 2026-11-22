// Note 77: all rank-deficient patterns of four members (or three, -DMEMB=3) for RS_4 on an 8-point F_2-subspace D of GF(2^64),
// up to the symmetries of the code (translations of D, 8) and of the list (relabelling the members), with a classification of the kernel.
// usage: 77_scan4 kind seed part nparts     kind P: D = <1,x,x^2>; G: random subspace; H: <1,r,r^2>, r random.
// A pattern gives each point a class (bitmask of members, empty or >= 2 members). Unknowns d_1..d_L in K^4 (d_0 = 0), coefficients of 1,y,y^2,y^3.
// Deficient: rank for the code < rank for a uniform random 8 x 4 matrix U. For each deficient canonical pattern one line:
//   pattern, orbit size, weight, rank U, rank code, then flags
//   F1: kernel in span{A_l(W_b) B(y)} for b = the first basis vector (the flag) plus the trivial family a_l B(y)
//   F2: the same with all 7 one-dimensional subspaces {0,b}     F3: F2 plus the common-upper-factor family A(W_b) B_l(y), all b
//   G: the kernel carries 4 distinct members     S: number of deficient three-member sub-lists (members relabelled), and their largest deficiency
//   NL: how many of those sub-lists have a kernel outside the span of the lifts     bal: balanced agreement (free points handed to the weakest member)
#include "69_gf.h"
#include "69_lin.h"
#ifndef MEMB
#define MEMB 4
#endif
#define LL (MEMB - 1)
#define NP 8
#define KK 4
static fe pts[NP], pw[NP][KK], Um[NP][KK];
static const fe (*GEN)[KK];
static int build(const fe g[NP][KK], const uint8_t *cls, int L, fe *M) {
    int cols = L * KK, rows = 0;
    for (int x = 0; x < NP; x++) {
        if (!cls[x]) continue;
        int l0 = __builtin_ctz(cls[x]);
        for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
            fe *row = M + rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * KK, g[x], sizeof(fe) * KK);
            if (l0 >= 1) memcpy(row + (l0 - 1) * KK, g[x], sizeof(fe) * KK);
            rows++;
        }
    }
    return rows;
}
static int rank_of(const fe g[NP][KK], const uint8_t *cls, int L, fe *Kout) {
    static fe M[64 * 16], Kb[17 * 16];
    int rows = build(g, cls, L, M);
    int d = rows ? gf_kernel(M, rows, L * KK, Kout ? Kout : Kb) : L * KK;
    if (!rows && Kout) { memset(Kout, 0, sizeof(fe) * L * KK * L * KK); for (int i = 0; i < L * KK; i++) Kout[i * L * KK + i] = 1; }
    return L * KK - d;
}
// echelon space of vectors of length 12
typedef struct { fe b[12][12]; int piv[12]; int dim; } space_t;
static int sp_add(space_t *S, const fe *v, int len) {
    fe w[12]; memcpy(w, v, sizeof(fe) * len);
    for (int i = 0; i < S->dim; i++) { fe f = w[S->piv[i]]; if (f) for (int j = 0; j < len; j++) w[j] ^= gf_mul(f, S->b[i][j]); }
    int p = -1; for (int j = 0; j < len; j++) if (w[j]) { p = j; break; }
    if (p < 0) return 0;
    fe inv = gf_inv(w[p]);
    for (int j = 0; j < len; j++) S->b[S->dim][j] = gf_mul(w[j], inv);
    S->piv[S->dim++] = p;
    return 1;
}
// generic small top system: unknown (X_1..X_L), X_l in K^dimx; a point x not in skip gives rows vec_x at members of its class
static int top_kernel(const uint8_t *cls, int L, int dimx, const fe vec[NP][4], uint32_t skipmask, fe *Kb) {
    static fe M[64 * 12];
    int cols = L * dimx, rows = 0;
    for (int x = 0; x < NP; x++) {
        if (!cls[x] || ((skipmask >> x) & 1)) continue;
        int l0 = __builtin_ctz(cls[x]);
        for (int l = l0 + 1; l <= L; l++) if ((cls[x] >> l) & 1) {
            fe *row = M + rows * cols; memset(row, 0, sizeof(fe) * cols);
            memcpy(row + (l - 1) * dimx, vec[x], sizeof(fe) * dimx);
            if (l0 >= 1) memcpy(row + (l0 - 1) * dimx, vec[x], sizeof(fe) * dimx);
            rows++;
        }
    }
    if (!rows) { memset(Kb, 0, sizeof(fe) * cols * cols); for (int i = 0; i < cols; i++) Kb[i * cols + i] = 1; return cols; }
    return gf_kernel(M, rows, cols, Kb);
}
static void add_low(space_t *S, const uint8_t *cls, int L, int b) { // A_l(W_b) (y + z)
    fe beta = pts[b], vec[NP][4], Kb[7 * 6];
    for (int x = 0; x < NP; x++) { vec[x][0] = 1; vec[x][1] = gf_mul(pts[x], pts[x]) ^ gf_mul(beta, pts[x]); }
    for (int z = 0; z < NP; z++) {
        int d = top_kernel(cls, L, 2, vec, 1u << z, Kb);
        for (int i = 0; i < d; i++) {
            fe v[12];
            for (int l = 0; l < L; l++) {
                fe a0 = Kb[i * 2 * L + 2 * l], a1 = Kb[i * 2 * L + 2 * l + 1], zz = pts[z];
                v[4 * l] = gf_mul(a0, zz); v[4 * l + 1] = a0 ^ gf_mul(a1, gf_mul(zz, beta)); v[4 * l + 2] = gf_mul(a1, zz ^ beta); v[4 * l + 3] = a1;
            }
            sp_add(S, v, 4 * L);
        }
    }
}
static void add_up(space_t *S, const uint8_t *cls, int L, int b) { // (W_b + omega_q) B_l(y)
    fe beta = pts[b], vec[NP][4], Kb[7 * 6];
    for (int x = 0; x < NP; x++) { vec[x][0] = 1; vec[x][1] = pts[x]; }
    for (int q = 0; q < NP; q++) {
        if ((q ^ b) < q) continue;
        fe om = gf_mul(pts[q], pts[q]) ^ gf_mul(beta, pts[q]);
        int d = top_kernel(cls, L, 2, vec, (1u << q) | (1u << (q ^ b)), Kb);
        for (int i = 0; i < d; i++) {
            fe v[12];
            for (int l = 0; l < L; l++) {
                fe b0 = Kb[i * 2 * L + 2 * l], b1 = Kb[i * 2 * L + 2 * l + 1];
                v[4 * l] = gf_mul(om, b0); v[4 * l + 1] = gf_mul(om, b1) ^ gf_mul(beta, b0); v[4 * l + 2] = b0 ^ gf_mul(beta, b1); v[4 * l + 3] = b1;
            }
            sp_add(S, v, 4 * L);
        }
    }
}
static void add_triv(space_t *S, const uint8_t *cls, int L) { // a_l Lambda_Z(y), |Z| = 3
    fe vec[NP][4], Kb[4 * 3];
    for (int x = 0; x < NP; x++) vec[x][0] = 1;
    for (int z1 = 0; z1 < NP; z1++) for (int z2 = z1 + 1; z2 < NP; z2++) for (int z3 = z2 + 1; z3 < NP; z3++) {
        int d = top_kernel(cls, L, 1, vec, (1u << z1) | (1u << z2) | (1u << z3), Kb);
        if (!d) continue;
        fe a = pts[z1], bb = pts[z2], c = pts[z3];
        fe B[4] = {gf_mul(a, gf_mul(bb, c)), gf_mul(a, bb) ^ gf_mul(a, c) ^ gf_mul(bb, c), a ^ bb ^ c, 1};
        for (int i = 0; i < d; i++) {
            fe v[12];
            for (int l = 0; l < L; l++) for (int e = 0; e < 4; e++) v[4 * l + e] = gf_mul(Kb[i * L + l], B[e]);
            sp_add(S, v, 4 * L);
        }
    }
}
static int contains(space_t *S, const fe *Kc, int dc, int len) { space_t T = *S; for (int i = 0; i < dc; i++) if (sp_add(&T, Kc + i * len, len)) return 0; return 1; }
static int genuine(const fe *Kc, int dc, int L) {
    for (int a = 0; a <= L; a++) for (int b = a + 1; b <= L; b++) {
        int differ = 0;
        for (int i = 0; i < dc && !differ; i++) for (int e = 0; e < 4; e++) {
            fe va = a ? Kc[i * 4 * L + 4 * (a - 1) + e] : 0, vb = Kc[i * 4 * L + 4 * (b - 1) + e];
            if (va != vb) { differ = 1; break; }
        }
        if (!differ) return 0;
    }
    return 1;
}
static uint8_t pm[24][16];
static int nperm;
static void make_perms(void) {
    int p[4] = {0, 1, 2, 3}; nperm = 0;
    for (p[0] = 0; p[0] < MEMB; p[0]++) for (p[1] = 0; p[1] < MEMB; p[1]++) for (p[2] = 0; p[2] < MEMB; p[2]++) for (p[3] = 0; p[3] < (MEMB == 4 ? 4 : 1); p[3]++) {
        int used = 0, ok = 1;
        for (int i = 0; i < MEMB; i++) { if ((used >> p[i]) & 1) ok = 0; used |= 1 << p[i]; }
        if (!ok) continue;
        for (int m = 0; m < 16; m++) { int r = 0; for (int i = 0; i < MEMB; i++) if ((m >> i) & 1) r |= 1 << p[i]; pm[nperm][m] = (uint8_t)r; }
        nperm++;
    }
}
static int canon(const uint8_t *cls) { // 0 if a smaller image exists, else the size of the stabilizer
    int stab = 0;
    for (int p = 0; p < nperm; p++) for (int t = 0; t < NP; t++) {
        int cmp = 0;
        for (int x = 0; x < NP && !cmp; x++) { int v = pm[p][cls[x ^ t]]; cmp = v < cls[x] ? -1 : v > cls[x] ? 1 : 0; }
        if (cmp < 0) return 0;
        if (cmp == 0) stab++;
    }
    return stab;
}
static void pat_str(const uint8_t *cls, char *s) {
    for (int x = 0; x < NP; x++) { if (!cls[x]) *s++ = '.'; else for (int l = 0; l < MEMB; l++) if ((cls[x] >> l) & 1) *s++ = (char)('0' + l); *s++ = (x == NP - 1) ? 0 : ' '; }
}
static long long ncanon = 0, ndef = 0;
static void handle(const uint8_t *cls, int stab) {
    ncanon++;
    int w = 0; for (int x = 0; x < NP; x++) if (cls[x]) w += __builtin_popcount(cls[x]) - 1;
    static fe Kc[13 * 12];
    int L = LL, rc = rank_of(GEN, cls, L, Kc);
    if (rc == (w < 4 * L ? w : 4 * L)) return;
    int ru = rank_of(Um, cls, L, 0);
    if (ru == rc) return;
    ndef++;
    int dc = 4 * L - rc;
    space_t S; S.dim = 0;
    add_triv(&S, cls, L); add_low(&S, cls, L, 1);
    int F1 = contains(&S, Kc, dc, 4 * L);
    for (int b = 2; b < NP; b++) add_low(&S, cls, L, b);
    int F2 = contains(&S, Kc, dc, 4 * L);
    for (int b = 1; b < NP; b++) add_up(&S, cls, L, b);
    int F3 = contains(&S, Kc, dc, 4 * L);
    int gen = genuine(Kc, dc, L), nsub = 0, maxsub = 0, nsubnl = 0;
    if (MEMB == 4) for (int m = 0; m < 4; m++) {
        uint8_t sub[NP];
        for (int x = 0; x < NP; x++) { int c = cls[x] & ~(1 << m), r = 0, j = 0; for (int l = 0; l < 4; l++) if (l != m) { if ((c >> l) & 1) r |= 1 << j; j++; } sub[x] = __builtin_popcount(r) >= 2 ? (uint8_t)r : 0; }
        static fe Ks[9 * 8];
        int a = rank_of(GEN, sub, 2, Ks), b = rank_of(Um, sub, 2, 0);
        if (b > a) {
            nsub++; if (b - a > maxsub) maxsub = b - a;
            space_t T; T.dim = 0; add_triv(&T, sub, 2); for (int bb = 1; bb < NP; bb++) add_low(&T, sub, 2, bb);
            if (!contains(&T, Ks, 8 - a, 8)) nsubnl++;
        }
    }
    int cnt[4] = {0, 0, 0, 0}, fl = 0;
    for (int x = 0; x < NP; x++) { if (!cls[x]) fl++; for (int l = 0; l < MEMB; l++) cnt[l] += (cls[x] >> l) & 1; }
    while (fl--) { int bm = 0; for (int l = 1; l < MEMB; l++) if (cnt[l] < cnt[bm]) bm = l; cnt[bm]++; }
    int bal = cnt[0]; for (int l = 1; l < MEMB; l++) if (cnt[l] < bal) bal = cnt[l];
    char s[64]; pat_str(cls, s);
    printf("%s | orbit %d w %d rU %d rC %d F %d%d%d G %d S %d %d NL %d bal %d\n", s, nperm * NP / stab, w, ru, rc, F1, F2, F3, gen, nsub, maxsub, nsubnl, bal);
}
int main(int argc, char **argv) {
    char kind = argv[1][0]; rng_seed(strtoull(argv[2], 0, 10)); int part = atoi(argv[3]), nparts = atoi(argv[4]);
    fe basis[3];
    if (kind == 'P') { basis[0] = 1; basis[1] = 2; basis[2] = 4; }
    else if (kind == 'H') { fe r = gf_rand(); basis[0] = 1; basis[1] = r; basis[2] = gf_mul(r, r); }
    else for (int i = 0; i < 3; i++) basis[i] = gf_rand();
    for (int j = 0; j < NP; j++) { pts[j] = 0; for (int i = 0; i < 3; i++) if ((j >> i) & 1) pts[j] ^= basis[i]; }
    for (int j = 0; j < NP; j++) { pw[j][0] = 1; for (int e = 1; e < KK; e++) pw[j][e] = gf_mul(pw[j][e - 1], pts[j]); }
    rng_seed(987654321); // the same reference matrix for every kind and part
    for (int j = 0; j < NP; j++) for (int e = 0; e < KK; e++) Um[j][e] = gf_rand();
    GEN = (const fe (*)[KK])pw;
    make_perms();
    uint8_t opts[12]; int no = 0;
    for (int m = 0; m < (1 << MEMB); m++) if (m == 0 || __builtin_popcount(m) >= 2) opts[no++] = (uint8_t)m;
    long long total = 1; for (int x = 0; x < NP; x++) total *= no;
    for (long long id = part; id < total; id += nparts) {
        uint8_t cls[NP]; long long t = id;
        for (int x = NP - 1; x >= 0; x--) { cls[x] = opts[t % no]; t /= no; }
        int stab = canon(cls);
        if (stab) handle(cls, stab);
    }
    fprintf(stderr, "kind %c members %d part %d/%d: canonical patterns %lld, deficient %lld\n", kind, MEMB, part, nparts, ncanon, ndef);
    return 0;
}
