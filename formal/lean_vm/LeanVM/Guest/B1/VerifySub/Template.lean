/-
  LeanVM.Guest.B1.VerifySub.Template

  `verify_sub`'s body as a template (G:3531-3731), section by section.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Whir.Split

/-!
# `verify_sub` as a template

The sections, in order (G = `lean_ethereum.py` at the commit in `leanvm-rev`):

* `vsHeadT`: the pool, the seed's permutation (`keccak_cells`), the stream (G:3541-3551);
* `vsReadsT`: the eight announced words read (`fs_next`), the table rows stored, the first four
  absorbed (G:3559-3574);
* `vsSizesT`: the rate and the memory's log-size as `g`-powers, their range checks, `dims_g`, `kb`
  in the frame and `kappa_base` (G:3575-3594);
* `vsPushT`: the push blocks' total `g_squares[kb[src]·g^adj]`, the bus depth `g^μ`, `zeta`
  (G:3597-3601);
* `vsRootsT`: the last four announced words absorbed, the root's two words read (G:3605-3612);
* `vsPlaceT`: `certify_placement`, the stack's log `g^m` and `g^(m - 20)` range-checked
  (G:3616-3619);
* `vsOodT`: the out-of-domain grind and point (`squeeze_point_from`), its value and the bus
  grind's nonce (`opening_message`) (G:3624-3629);
* `vsBusGrindT`: the bus grind, dispatched on `μ - 20` (G:3636-3638);
* `vsFpwT`: the sixteen slot weights, then `β` (G:3639-3646);
* `vsCallsT`: `verify_bus_gkr`, `verify_tables`, `verify_keccak` (G:3649-3660);
* `vsMapsT`: the ring map's sixteen challenges after a grind (G:3661-3678);
* `vsCtabT`: their Frobenius coefficients `c_table`, and `ring_switch_target` (G:3680-3688);
* `vsLamT`: the batching challenge and the target, the pooled values read from `claim_pool` and
  `col_eval_words` (the output lanes' left out), the Keccak reduction's and the out-of-domain
  claims last (G:3697-3712);
* `vsTailT`: the dispatch to `open_stacked` on the stack's size, the terminal, the deferred claim
  (G:3716-3731).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Atoms on numbered values -/

/-- `d = p[off]`. -/
def vsLd (d p off : ℕ) : Stmt := .atom (.load (.n d) (.n p) off)

/-- `d = c`. -/
def vsConst (d : ℕ) (c : E) : Stmt := .atom (.const (.n d) c)

/-- `d = a · b`. -/
def vsMul (d a b : ℕ) : Stmt := .atom (.mul (.n d) (.n a) (.n b))

/-- `d = a + b`. -/
def vsAdd (d a b : ℕ) : Stmt := .atom (.add (.n d) (.n a) (.n b))

/-- `d = s`. -/
def vsCopy (d s : ℕ) : Stmt := .atom (.copy (.n d) (.n s))

/-- A fresh buffer of `n` words at `d`. -/
def vsAlloc (d n : ℕ) : Stmt := .atom (.hint (.alloc (.n d) n))

/-- `assert log x < log k` through `y`, `t1`, `t2`. -/
def vsRange (x y t1 t2 k : ℕ) : Stmt := .atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k))

/-- A call on numbered values. -/
def vsCall (f : String) (args rets : List ℕ) : Stmt := .call f (args.map .n) (rets.map .n)

/-- The values `b, …, b + n - 1`. -/
def vsRun (b n : ℕ) : List V := (List.range n).map fun k ↦ .n (b + k)

/-- `g^WIN_TAB_AT`, the window table's offset in the exponent tables (`tabs = g_squares·g^…`). -/
def vsWinWord : E := word 133823759239872512 0

/-- `tabs` into `d`: the constant at `c`, then `g_squares · c`. -/
def vsTabsT (c d : ℕ) : List Stmt := [vsConst c vsWinWord, vsMul d 4 c]

/-- A squeeze with nothing waiting (the zero cell `8`, the cells `9 .. 11`), on the capacity
from `capb`, outputs from `o`, the challenge at `o + 13`. -/
def vsSqzT (capb o : ℕ) : List Stmt :=
  keccakA ([.n 8, .n 8, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11] ++ vsRun capb 5) (vsRun o 13) ::
    challengeT (.n o) (o + 13)

/-! ## The sections -/

/-- The pool, the seed, the stream (G:3541-3551). -/
def vsHeadT : List Stmt :=
  [vsAlloc 6 159, vsConst 7 (word 1 0), vsConst 8 (word 0 0), vsConst 9 (word 0 0),
    vsConst 10 (word 0 0), vsConst 11 (word 0 0),
    keccakA [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11]
      (vsRun 12 13),
    vsAlloc 25 8192, .atom (.hint (.witness "stream" (.heap (.n 25) 0 8192))), vsAlloc 26 6]

/-- The eight announced words: `x_i` at `27 + 3 i` (`i < 4`) and `52 + 3 (i - 4)`, rows `1 .. 6`
stored in `table_rows`, the first four absorbed after the fourth (G:3559-3574). -/
def vsReadsT : List Stmt :=
  fsNextT (.n 25) 0 27 ++ fsNextT (.n 25) 1 30 ++ [vsLd 30 26 0] ++ fsNextT (.n 25) 2 33 ++
    [vsLd 33 26 1] ++ fsNextT (.n 25) 3 36 ++ [vsLd 36 26 2] ++
    [keccakA [.n 28, .n 29, .n 31, .n 32, .n 34, .n 35, .n 37, .n 38, .n 20, .n 21, .n 22, .n 23,
      .n 24] (vsRun 39 13)] ++
    fsNextT (.n 25) 4 52 ++ [vsLd 52 26 3] ++ fsNextT (.n 25) 5 55 ++ [vsLd 55 26 4] ++
    fsNextT (.n 25) 6 58 ++ [vsLd 58 26 5] ++ fsNextT (.n 25) 7 61

/-- The rate and the memory's log as `g`-powers, `dims_g`, `kb` in the frame and `kappa_base`
(G:3575-3594). -/
def vsSizesT : List Stmt :=
  [vsCall "g_power_of_word" [61] [64], vsConst 65 (word 2 0), vsMul 64 66 65,
    vsConst 67 (word 8 0), vsRange 66 68 69 70 67, vsAlloc 71 7,
    vsCall "g_power_of_word" [27] [72], vsConst 73 (word 1073741824 0),
    vsRange 72 74 75 76 73, vsConst 77 (word 4294967296 0), vsConst 78 (word 2 0),
    vsMul 72 79 78, vsRange 79 80 81 82 77, vsLd 72 71 0,
    .atom (.hint (.witness "table_logs" (.heap (.n 71) 1 6))), vsAlloc 83 8,
    vsConst 84 (word 1 0), vsCopy 85 72] ++
  (List.range 6).map (fun t ↦ vsLd (86 + t) 71 (1 + t)) ++
  (List.range 8).map (fun i ↦ vsLd (84 + i) 83 i)

/-- The running product after push block `b`. -/
def vsPV (b : ℕ) : ℕ := 93 + 3 * b

/-- Push block `b`: `g_squares[kb[src] · g^adj]`, multiplied in. -/
def vsPushStep (b : ℕ) : List Stmt :=
  if b = 0 then [vsMul 92 4 (84 + Tables.blockKappaSrc.getD 0 0), vsLd 93 92 (Tables.blockKappaAdj 0)]
  else [vsMul (91 + 3 * b) 4 (84 + Tables.blockKappaSrc.getD b 0),
    vsLd (92 + 3 * b) (91 + 3 * b) (Tables.blockKappaAdj b),
    vsMul (vsPV b) (vsPV (b - 1)) (92 + 3 * b)]

/-- The push blocks' total, the bus depth, `zeta` (G:3597-3601). -/
def vsPushT : List Stmt :=
  (List.range 54).flatMap vsPushStep ++
    [vsCall "log2_ceil_in_the_exponent__L0_L34" [252, 4] [253],
      .atom (.hint (.allocDyn (.n 254) (.n 253)))]

/-- The last four words absorbed, the root's two words read (G:3605-3612). -/
def vsRootsT : List Stmt :=
  [keccakA [.n 53, .n 54, .n 56, .n 57, .n 59, .n 60, .n 62, .n 63, .n 47, .n 48, .n 49,
    .n 50, .n 51] (vsRun 255 13)] ++
  fsNextT (.n 25) 8 268 ++ fsNextT (.n 25) 9 271

/-- `LIG_MIN_SHIFT_INV = g^-20`. -/
def vsGinv20 : E := word 14347465658197868555 0

/-- The placement, the stack's log `g^m`, `size_sel = g^(m - 20)` below `g^10` (G:3616-3619). -/
def vsPlaceT : List Stmt :=
  [vsCall "certify_placement" [83, 4] [274, 275],
    vsCall "log2_ceil_in_the_exponent__L16_L34" [274, 4] [276], vsConst 277 vsGinv20,
    vsMul 278 276 277, vsConst 279 (word 1024 0), vsRange 278 280 281 282 279]

/-- `squeeze_point_from`'s specializations for the stack logs `20 .. 30`. -/
def vsSqpNames : List String :=
  ["squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22",
    "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25",
    "squeeze_point_from__L26", "squeeze_point_from__L27", "squeeze_point_from__L28",
    "squeeze_point_from__L29", "squeeze_point_from__L30"]

/-- The out-of-domain sample: the root's two words and the grind's nonce in one permutation, the
grind, the point at `ood_z` from its challenge, the value and the bus grind's nonce
(`opening_message`) (G:3624-3629). -/
def vsOodT : List Stmt :=
  fsNonceT (.n 25) 10 283 ++ zero2T 286 ++
  [keccakA [.n 269, .n 270, .n 272, .n 273, .n 284, .n 285, .n 286, .n 287, .n 263, .n 264,
    .n 265, .n 266, .n 267] (vsRun 288 13)] ++ vsTabsT 301 302 ++
  [grindCallT 15 (.n 289) (.n 302), vsCopy 303 288, vsAlloc 304 30,
    .dispatch (.n 278) vsSqpNames [.n 296, .n 297, .n 298, .n 299, .n 300, .n 303, .n 304]
      (vsRun 305 5),
    vsAlloc 310 1, vsConst 311 (word 2048 0), vsMul 312 25 311,
    vsCall "opening_message__L1_L1" [305, 306, 307, 308, 309, 312, 310]
      ((List.range 8).map (313 + ·))]

/-- `INV_GEN^BUS_MIN_MU = g^-20`. -/
def vsGinvBus : E := word 14347465658197868555 0

/-- `bus_grind_check`'s specializations for `μ - 20 < 14`. -/
def vsBgNames : List String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3",
    "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7",
    "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11",
    "bus_grind_check__L12", "bus_grind_check__L13"]

/-- The bus grind: `g^(μ - 20)` below `g^13`, its check dispatched on it (G:3636-3638). -/
def vsBusGrindT : List Stmt :=
  [vsConst 321 vsGinvBus, vsMul 322 253 321, vsConst 323 (word 8192 0),
    vsRange 322 324 325 326 323] ++ vsTabsT 327 328 ++
  [.dispatch (.n 322) vsBgNames [.n 314, .n 328] [.n 329]]

/-- The sixteen slot weights, the first `opening_message`'s, then `β` (G:3639-3646). -/
def vsFpwT : List Stmt :=
  (List.range 5).map (fun i ↦ vsCopy (330 + i) (315 + i)) ++ [vsAlloc 335 16, vsLd 313 335 0] ++
  (List.range 15).flatMap (fun i ↦ vsSqzT (330 + 14 * i) (336 + 14 * i) ++
    [vsLd (349 + 14 * i) 335 (i + 1)]) ++ vsSqzT 540 546

/-- The bus's GKR, the tables, the Keccak reduction (G:3649-3660). -/
def vsCallsT : List Stmt :=
  vsTabsT 560 561 ++
  [vsCall "verify_bus_gkr" [554, 555, 556, 557, 558, 320, 253, 254, 561] ((List.range 7).map (562 + ·)),
    vsAlloc 569 34, vsAlloc 570 4] ++ vsTabsT 571 572 ++
  [vsCall "verify_tables" [562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4, 335, 559, 6,
      569, 568, 572, 570] ((List.range 10).map (573 + ·)),
    vsLd 583 71 6, vsAlloc 584 78, vsAlloc 585 64, vsConst 586 (word 3710851743744 0),
    vsMul 587 582 586] ++ vsTabsT 588 589 ++
  [vsCall "verify_keccak" [573, 574, 575, 576, 577, 578, 583, 569, 587, 584, 585, 589]
      ((List.range 7).map (590 + ·))]

/-- The value of the ring map's challenge `i`. -/
def vsCh (i : ℕ) : ℕ := 621 + 15 * i

/-- The capacity's first value before the ring map's squeeze `i` (`i < 15`). -/
def vsChCap (i : ℕ) : ℕ := if i = 0 then 613 else 615 + 15 * i

/-- The ring map's sixteen challenges: a grind's nonce absorbed, the first drawn by its
permutation, fifteen squeezed, then stored in `map_challenges` (G:3669-3678). -/
def vsMapsT : List Stmt :=
  (List.range 5).map (fun i ↦ vsCopy (597 + i) (590 + i)) ++ fsNonceT (.n 595) 0 602 ++
  [keccakA [.n 603, .n 604, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11, .n 597, .n 598, .n 599, .n 600,
    .n 601] (vsRun 605 13)] ++ vsTabsT 618 619 ++
  [grindCallT 13 (.n 606) (.n 619), vsCopy 620 605, vsCopy 621 620] ++
  (List.range 15).flatMap (fun i ↦ vsSqzT (vsChCap i) (622 + 15 * i) ++
    [vsCopy (vsCh (i + 1)) (635 + 15 * i)]) ++
  vsAlloc 847 16 :: (List.range 16).map (fun i ↦ vsLd (vsCh i) 847 i)

/-- The squarings of `c_table`'s term `q + 1` in block `b` (from `s`), from the previous power. -/
def vsSqT (b s q : ℕ) : List Stmt :=
  (List.range 8).map fun k ↦
    let t := s + 1 + 9 * q
    let x := if k = 0 then (if q = 0 then vsCh (8 + b) else t - 2) else t + k - 1
    vsMul (t + k) x x

/-- Block `b` of `c_table` (from `s = 849 + 64 b`): `c[8p + b] = f_p · g_b^(2^(8p))`. -/
def vsCtabBlock (b : ℕ) : List Stmt :=
  let s := 849 + 64 * b
  [vsMul s (vsCh 0) (vsCh (8 + b)), vsLd s 848 b] ++
  (List.range 7).flatMap fun q ↦
    let t := s + 1 + 9 * q
    vsSqT b s q ++ [vsMul (t + 8) (vsCh (q + 1)) (t + 7), vsLd (t + 8) 848 (8 * (q + 1) + b)]

/-- `c_table`, then `ring_switch_target` (G:3680-3688). -/
def vsCtabT : List Stmt :=
  vsAlloc 848 64 :: (List.range 8).flatMap vsCtabBlock ++
    [vsCall "ring_switch_target" [585, 847] [1361]]

/-- The pooled claim of the `i`-th batched one: the output lanes' `105 .. 129` are left out. -/
def vsKept (i : ℕ) : ℕ := if i < 105 then i else i + 25

/-- Where pooled claim `j`'s value is: the bus's `4` and the public input's `2` in `claim_pool`
(`6`), the tables' `153` column evaluations at `col_eval_words` (`582`), from `j - 4`. -/
def vsClaimAt (j : ℕ) : ℕ × ℕ := if 4 ≤ j ∧ j < 157 then (582, j - 4) else (6, j)

/-- The power of `λ` before batched claim `i`. -/
def vsPw (i : ℕ) : ℕ := 1375 + 4 * i

/-- The target before batched claim `i`. -/
def vsTg (i : ℕ) : ℕ := if i = 0 then 1361 else 1374 + 4 * i

/-- Batched claim `i`: its value read, the target and the power updated. -/
def vsLamStep (i : ℕ) : List Stmt :=
  [vsLd (1376 + 4 * i) (vsClaimAt (vsKept i)).1 (vsClaimAt (vsKept i)).2,
    vsMul (1377 + 4 * i) (vsPw i) (1376 + 4 * i), vsAdd (1378 + 4 * i) (vsTg i) (1377 + 4 * i),
    vsMul (1379 + 4 * i) (vsPw i) 1375]

/-- The batching challenge, the target: the `134` pooled claims, the Keccak reduction's, the
out-of-domain value (G:3697-3712). -/
def vsLamT : List Stmt :=
  vsSqzT 840 1362 ++ (List.range 134).flatMap vsLamStep ++
    [vsMul 1912 1911 596, vsAdd 1913 1910 1912, vsMul 1914 1911 1375, vsLd 1915 310 0,
      vsMul 1916 1914 1915, vsAdd 1917 1913 1916]

/-- `open_stacked`'s specializations, in dispatch order. -/
def vsOpenNames : List String :=
  ["open_stacked__L0", "open_stacked__L1", "open_stacked__L2", "open_stacked__L3",
    "open_stacked__L4", "open_stacked__L5", "open_stacked__L6", "open_stacked__L7",
    "open_stacked__L8", "open_stacked__L9", "open_stacked__L10"]

/-- The dispatch to `open_stacked` on the stack's size `size_sel`, the rate `rate_sel` its first
argument, the terminal, the deferred claim (G:3716-3731). -/
def vsTailT : List Stmt :=
  [vsConst 1918 (word 2 0), vsMul 1919 595 1918] ++ vsTabsT 1920 1921 ++
  [.dispatch (.n 278) vsOpenNames
      [.n 66, .n 1370, .n 1371, .n 1372, .n 1373, .n 1374, .n 1917, .n 268, .n 271, .n 1919,
        .n 1921]
      (vsRun 1922 5),
    vsCall "check_opening_terminal" [4, 254, 569, 581, 253, 579, 72, 583, 83, 1375, 275, 584, 848,
      1923, 1924, 1925, 1926, 1922, 304, 276] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1927 + k) 254 k, vsLd (1927 + k) 5 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (1946 + k) 570 k, vsLd (1946 + k) 5 (19 + k)]) ++
  [vsLd 580 5 23, .ret []]

/-- **`verify_sub`'s body as a template.** -/
def vsT : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsPlaceT ++ vsOodT ++ vsBusGrindT ++
    vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT

end
end LeanVM.Guest.B1.VerifySub
