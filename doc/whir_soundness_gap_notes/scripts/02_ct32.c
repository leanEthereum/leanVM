// Common-top classes for n = 32 (N = 5), exhaustive, by meet in the middle.
// usage: 02_ct32 m modlow_hex tmax dump T b0 b1 b2 b3 b4   (basis in hex)
// For the given T, prints for t = 1..tmax the largest number of T-subsets of D sharing (e_1..e_t), and how many
// classes reach it. For T odd only e_1 = 0 is enumerated (translation by a in D shifts e_1 by a and maps classes to
// classes), and class counts are multiplied by 32. With dump = 1, one maximal class per t is printed as hex masks.
#include "02_gf.h"

#define TM 10
static int tmax, T;
static u64 pts[32];
static u64 (*eh[2])[TM + 1]; // eh[h][mask][j] = e_j of the subset mask of half h
static u16 *grp[2][17][32]; static int ngrp[2][17][32];
typedef struct { u64 key; u32 id; } rec;
static u64 best[TM + 1], nbest[TM + 1];
static u32 *dump[TM + 1];
static int want_dump;

static inline u64 ecomb(u32 id, int t) {
  u64 *a = eh[0][id >> 16], *b = eh[1][id & 0xffff], r = a[t] ^ b[t];
  for (int i = 1; i < t; i++) r ^= gmul(a[i], b[t - i]);
  return r;
}
static int cmp(const void *x, const void *y) { u64 a = ((const rec *)x)->key, b = ((const rec *)y)->key; return a < b ? -1 : a > b; }

static void note(int t, rec *r, size_t len, u64 mult) {
  if (len > best[t]) {
    best[t] = len; nbest[t] = mult;
    if (want_dump) { dump[t] = realloc(dump[t], len * sizeof(u32)); for (size_t i = 0; i < len; i++) dump[t][i] = r[i].id; }
  } else if (len == best[t]) nbest[t] += mult;
}

static void refine(rec *r, size_t len, int t, u64 mult) { // r is one class at level t-1
  if (t > tmax) return;
  if (len == 1) { for (int j = t; j <= tmax; j++) note(j, r, 1, mult); return; }
  for (size_t i = 0; i < len; i++) r[i].key = ecomb(r[i].id, t);
  qsort(r, len, sizeof(rec), cmp);
  size_t s = 0;
  while (s < len) {
    size_t e = s + 1;
    while (e < len && r[e].key == r[s].key) e++;
    note(t, r + s, e - s, mult);
    refine(r + s, e - s, t + 1, mult);
    s = e;
  }
}

int main(int argc, char **argv) {
  if (argc != 11) { fprintf(stderr, "usage: m modlow tmax dump T b0..b4\n"); return 1; }
  gf_init(atoi(argv[1]), strtoull(argv[2], 0, 16));
  tmax = atoi(argv[3]); want_dump = atoi(argv[4]); T = atoi(argv[5]);
  u64 basis[5];
  for (int i = 0; i < 5; i++) basis[i] = strtoull(argv[6 + i], 0, 16);
  for (int i = 0; i < 32; i++) { pts[i] = 0; for (int j = 0; j < 5; j++) if (i >> j & 1) pts[i] ^= basis[j]; }
  for (int h = 0; h < 2; h++) {
    eh[h] = malloc(65536 * sizeof(*eh[h]));
    memset(eh[h][0], 0, sizeof(*eh[h])); eh[h][0][0] = 1;
    for (u32 S = 1; S < 65536; S++) {
      int i = __builtin_ctz(S); u64 s = pts[16 * h + i]; u64 *p = eh[h][S & (S - 1)];
      eh[h][S][0] = 1;
      for (int j = 1; j <= TM; j++) eh[h][S][j] = p[j] ^ gmul(p[j - 1], s);
    }
    for (int pass = 0; pass < 2; pass++) {
      if (pass) for (int a = 0; a <= 16; a++) for (int s = 0; s < 32; s++) { grp[h][a][s] = malloc((ngrp[h][a][s] + 1) * sizeof(u16)); ngrp[h][a][s] = 0; }
      for (u32 S = 0; S < 65536; S++) {
        int a = __builtin_popcount(S), x = 0;
        for (int i = 0; i < 16; i++) if (S >> i & 1) x ^= 16 * h + i;
        if (pass) grp[h][a][x][ngrp[h][a][x]] = (u16)S;
        ngrp[h][a][x]++;
      }
    }
  }
  int cmaxv = (T & 1) ? 1 : 32; u64 mult = (T & 1) ? 32 : 1;
  rec *r = 0; size_t cap = 0;
  for (int c = 0; c < cmaxv; c++) {
    size_t len = 0;
    for (int pass = 0; pass < 2; pass++) {
      if (pass) { if (len > cap) { cap = len; r = realloc(r, cap * sizeof(rec)); } len = 0; }
      for (int a = 0; a <= 16; a++) {
        int b = T - a; if (b < 0 || b > 16) continue;
        for (int sa = 0; sa < 32; sa++) {
          int sb = sa ^ c; size_t na = ngrp[0][a][sa], nb = ngrp[1][b][sb];
          if (!pass) { len += na * nb; continue; }
          for (size_t i = 0; i < na; i++) for (size_t j = 0; j < nb; j++) r[len++].id = (u32)grp[0][a][sa][i] << 16 | grp[1][b][sb][j];
        }
      }
    }
    if (!len) continue;
    note(1, r, len, mult);
    refine(r, len, 2, mult);
  }
  printf("T=%d", T);
  for (int t = 1; t <= tmax; t++) printf(" %llu(%llu)", (unsigned long long)best[t], (unsigned long long)nbest[t]);
  printf("\n");
  if (want_dump) for (int t = 1; t <= tmax; t++) {
    if (best[t] > 2000) continue;
    printf("dump T=%d t=%d:", T, t);
    for (u64 i = 0; i < best[t]; i++) { u32 id = dump[t][i]; printf(" %08x", (id & 0xffff) << 16 | id >> 16); }
    printf("\n");
  }
  return 0;
}
