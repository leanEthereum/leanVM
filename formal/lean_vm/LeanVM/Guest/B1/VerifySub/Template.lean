/-
  LeanVM.Guest.B1.VerifySub.Template

  `verify_sub`'s body as a template (G:3321-3513), section by section.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Whir.Names

/-!
# `verify_sub` as a template

The sections, in order (G = `lean_ethereum.py` at leanVM `40f877dc`):

* `vsHeadT`: the pool, the seed's permutation (`keccak_cells`), the stream (G:3331-3340);
* `vsReadsT`: the eight announced words read (`fs_next`), the table rows stored, the first four
  absorbed (G:3348-3363);
* `vsSizesT`: the rate and the memory's log-size as `g`-powers, their range checks, `dims_g`, `kb`
  in the frame and `kappa_base` (G:3364-3383);
* `vsPushT`: the push blocks' total `g_squares[kb[src]·g^adj]` and the bus depth `g^μ`, `zeta`
  (G:3386-3390);
* `vsRootsT`: the last four announced words absorbed, the root's two words read and checked
  (G:3394-3406);
* `vsAlphasT`: the four bus challenges (G:3412-3418);
* `vsFpwT`: their equality weights, then `β` (G:3419-3422);
* `vsCallsT`: `verify_bus_gkr`, `verify_tables`, `verify_keccak` (G:3425-3436);
* `vsMapsT`: the ring map's challenges (G:3444-3450);
* `vsCtabT`: their Frobenius coefficients `c_table`, and `ring_switch_target` (G:3454-3463);
* `vsLamT`: the batching challenge and the target, the pooled values read from `claim_pool` and
  `col_eval_words` (G:3472-3485);
* `vsTailT`: `certify_placement`, the stack's log, its size selector, the dispatch to
  `open_stacked` on the size with the rate's selector passed on, the terminal, the deferred claim
  (G:3534-3557).
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

/-- A fresh buffer of `n` words at `d`. -/
def vsAlloc (d n : ℕ) : Stmt := .atom (.hint (.alloc (.n d) n))

/-- `assert log x < log k` through `y`, `t1`, `t2`. -/
def vsRange (x y t1 t2 k : ℕ) : Stmt := .atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k))

/-- A call on numbered values. -/
def vsCall (f : String) (args rets : List ℕ) : Stmt := .call f (args.map .n) (rets.map .n)

/-- The values `b, …, b + n - 1`. -/
def vsRun (b n : ℕ) : List V := (List.range n).map fun k ↦ .n (b + k)

/-- A squeeze with nothing waiting (the zero cell `8`, the cells `9 .. 11`), on the capacity
from `capb`, outputs from `o`, the challenge at `o + 19`. -/
def vsSqzT (capb o : ℕ) : List Stmt :=
  keccakA ([.n 8, .n 8, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11] ++ vsRun capb 5) (vsRun o 13) ::
    challengeT (.n o) (.n (o + 1)) (o + 13)

/-! ## The sections -/

/-- The pool, the seed, the stream (G:3331-3340). -/
def vsHeadT : List Stmt :=
  [vsAlloc 6 167, vsConst 7 (word 1 0 0), vsConst 8 (word 0 0 0),
    vsConst 9 (word 0 0 0), vsConst 10 (word 0 0 0), vsConst 11 (word 0 0 0),
    keccakA [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11]
      (vsRun 12 13),
    vsAlloc 25 8192, .atom (.hint (.witness "stream" (.heap (.n 25) 0 8192))), vsAlloc 26 6]

/-- The eight announced words: `x_i` at `27 + 10 i` (`i < 4`) and `80 + 10 (i - 4)`, rows `1 .. 6`
stored in `table_rows`, the first four absorbed after the fourth (G:3348-3363). -/
def vsReadsT : List Stmt :=
  fsNextT (.n 25) 0 27 ++ fsNextT (.n 25) 1 37 ++ [vsLd 37 26 0] ++ fsNextT (.n 25) 2 47 ++
    [vsLd 47 26 1] ++ fsNextT (.n 25) 3 57 ++ [vsLd 57 26 2] ++
    [keccakA [.n 34, .n 36, .n 44, .n 46, .n 54, .n 56, .n 64, .n 66, .n 20, .n 21, .n 22, .n 23,
      .n 24] (vsRun 67 13)] ++
    fsNextT (.n 25) 4 80 ++ [vsLd 80 26 3] ++ fsNextT (.n 25) 5 90 ++ [vsLd 90 26 4] ++
    fsNextT (.n 25) 6 100 ++ [vsLd 100 26 5] ++ fsNextT (.n 25) 7 110

/-- The rate and the memory's log as `g`-powers, `dims_g`, `kb` in the frame and `kappa_base`
(G:3364-3383). -/
def vsSizesT : List Stmt :=
  [vsCall "g_power_of_word" [110] [120], vsConst 121 (word 2 0 0), vsMul 120 122 121,
    vsConst 123 (word 8 0 0), vsRange 122 124 125 126 123, vsAlloc 127 7,
    vsCall "g_power_of_word" [27] [128], vsConst 129 (word (2 ^ 30) 0 0),
    vsRange 128 130 131 132 129, vsConst 133 (word (2 ^ 32) 0 0), vsConst 134 (word 2 0 0),
    vsMul 128 135 134, vsRange 135 136 137 138 133, vsLd 128 127 0,
    .atom (.hint (.witness "table_logs" (.heap (.n 127) 1 6))), vsAlloc 139 8,
    vsConst 140 (word 1 0 0), .atom (.copy (.n 141) (.n 128))] ++
  (List.range 6).map (fun t ↦ vsLd (142 + t) 127 (1 + t)) ++
  (List.range 8).map (fun i ↦ vsLd (140 + i) 139 i)

/-- The running product after push block `b`. -/
def vsPV (b : ℕ) : ℕ := 149 + 3 * b

/-- Push block `b`: `g_squares[kb[src] · g^adj]`, multiplied in. -/
def vsPushStep (b : ℕ) : List Stmt :=
  if b = 0 then [vsMul 148 4 (140 + Tables.blockKappaSrc.getD 0 0), vsLd 149 148 (Tables.blockKappaAdj 0)]
  else [vsMul (147 + 3 * b) 4 (140 + Tables.blockKappaSrc.getD b 0),
    vsLd (148 + 3 * b) (147 + 3 * b) (Tables.blockKappaAdj b),
    vsMul (vsPV b) (vsPV (b - 1)) (148 + 3 * b)]

/-- The push blocks' total, the bus depth, `zeta` (G:3386-3390). -/
def vsPushT : List Stmt :=
  (List.range 54).flatMap vsPushStep ++
    [vsCall "log2_ceil_in_the_exponent__L0_L34" [308, 4] [309],
      .atom (.hint (.allocDyn (.n 310) (.n 309)))]

/-- The last four words absorbed, the root read and checked (G:3394-3406). -/
def vsRootsT : List Stmt :=
  [keccakA [.n 87, .n 89, .n 97, .n 99, .n 107, .n 109, .n 117, .n 119, .n 75, .n 76, .n 77,
    .n 78, .n 79] (vsRun 311 13)] ++
  fsNextT (.n 25) 8 324 ++ fsNextT (.n 25) 9 334 ++
  [vsCall "assert_canonical" [324] [344], vsCall "assert_canonical" [334] [345], vsAlloc 346 4]

/-- The four bus challenges, the first with the root waiting (G:3412-3418). -/
def vsAlphasT : List Stmt :=
  keccakA [.n 331, .n 333, .n 341, .n 343, .n 8, .n 9, .n 10, .n 11, .n 319, .n 320, .n 321,
    .n 322, .n 323] (vsRun 347 13) :: challengeT (.n 347) (.n 348) 360 ++ [vsLd 366 346 0] ++
  vsSqzT 355 367 ++ [vsLd 386 346 1] ++ vsSqzT 375 387 ++ [vsLd 406 346 2] ++
  vsSqzT 395 407 ++ [vsLd 426 346 3]

/-- One factor of `eq_weight(bus_alpha, 4, x, 0)` at `v`: `α_t` or `1 + α_t`; the statements, the
factor's value and the next free value. -/
def vsEqwFactor (x t v : ℕ) : List Stmt × ℕ × ℕ :=
  if x.testBit t then ([vsLd v 346 t], v, v + 1)
  else ([vsLd v 346 t, vsConst (v + 1) (word 1 0 0), vsAdd (v + 2) (v + 1) v], v + 2, v + 3)

/-- `eq_weight(bus_alpha, 4, x, 0)` from `v`, the product of its factors in order: the
statements, the product's value and the next free value. -/
def vsEqwT (x v : ℕ) : List Stmt × ℕ × ℕ :=
  let f0 := vsEqwFactor x 0 v
  let f1 := vsEqwFactor x 1 f0.2.2
  let p1 := f1.2.2
  let f2 := vsEqwFactor x 2 (p1 + 1)
  let p2 := f2.2.2
  let f3 := vsEqwFactor x 3 (p2 + 1)
  let p3 := f3.2.2
  (f0.1 ++ f1.1 ++ [vsMul p1 f0.2.1 f1.2.1] ++ f2.1 ++ [vsMul p2 p1 f2.2.1] ++ f3.1 ++
    [vsMul p3 p2 f3.2.1], p3, p3 + 1)

/-- The first value of `fp_w[x]`'s block. -/
def vsFpwStart : ℕ → ℕ
  | 0 => 428
  | x + 1 => (vsEqwT x (vsFpwStart x)).2.2

/-- `fp_w`, then `β` (G:3419-3422). -/
def vsFpwT : List Stmt :=
  vsAlloc 427 16 :: (List.range 16).flatMap (fun x ↦
    (vsEqwT x (vsFpwStart x)).1 ++ [vsLd (vsEqwT x (vsFpwStart x)).2.1 427 x]) ++ vsSqzT 415 604

/-- The bus's GKR, the tables, the Keccak reduction (G:3425-3436). -/
def vsCallsT : List Stmt :=
  [vsConst 624 (word 1024 0 0), vsMul 625 25 624,
    vsCall "verify_bus_gkr" [612, 613, 614, 615, 616, 625, 309, 310] ((List.range 9).map (626 + ·)),
    vsAlloc 635 34,
    vsCall "verify_tables" [626, 627, 628, 629, 630, 631, 0, 1, 310, 309, 127, 26, 4, 427, 623, 6,
      635, 632, 633, 634] ((List.range 10).map (636 + ·)),
    vsLd 646 127 6, vsAlloc 647 78, vsAlloc 648 64, vsConst 649 (word 237494511599616 0 0),
    vsMul 650 645 649,
    vsCall "verify_keccak" [636, 637, 638, 639, 640, 641, 646, 635, 650, 647, 648]
      ((List.range 8).map (651 + ·))] ++
  (List.range 5).map fun i ↦ .atom (.copy (.n (659 + i)) (.n (651 + i)))

/-- The ring map's challenges: the first from `verify_keccak`, five squeezed (G:3444-3450). -/
def vsMapsT : List Stmt :=
  [vsAlloc 664 6, vsAlloc 665 64, vsLd 658 664 0] ++
  vsSqzT 659 666 ++ [vsLd 685 664 1] ++ vsSqzT 674 686 ++ [vsLd 705 664 2] ++
  vsSqzT 694 706 ++ [vsLd 725 664 3] ++ vsSqzT 714 726 ++ [vsLd 745 664 4] ++
  vsSqzT 734 746 ++ [vsLd 765 664 5]

/-- `v ↦ v²`, `s` times, from `v` (`v + 1 .. v + s`). -/
def vsSqChainT (v s : ℕ) : List Stmt := (List.range s).map fun k ↦ vsMul (v + 1 + k) (v + k) (v + k)

/-- Slot `slot` of a stage of shift `s` with challenge `mc`, from `v`:
`c[2 s·slot + s] = mc · c[2 s·slot]^(2^s)`. -/
def vsSlotT (mc s slot v : ℕ) : List Stmt :=
  vsLd v 665 (2 * s * slot) :: vsSqChainT v s ++
    [vsMul (v + s + 1) mc (v + s), vsLd (v + s + 1) 665 (2 * s * slot + s)]

/-- Stage `st` of shift `s` from `b`: its challenge, then its `32 / s` slots. -/
def vsStageT (st s b : ℕ) : List Stmt :=
  vsLd b 664 st :: (List.range (32 / s)).flatMap fun slot ↦ vsSlotT b s slot (b + 1 + slot * (s + 2))

/-- `c_table`, then `ring_switch_target` (G:3454-3463). -/
def vsCtabT : List Stmt :=
  [vsConst 766 (word 1 0 0), vsLd 766 665 0] ++ vsStageT 0 32 767 ++ vsStageT 1 16 802 ++
    vsStageT 2 8 839 ++ vsStageT 3 4 880 ++ vsStageT 4 2 929 ++ vsStageT 5 1 994 ++
    [vsCall "ring_switch_target" [648, 664] [1091]]

/-- The pooled claim of the `i`-th batched one: the output lanes' `112 .. 136` are left out. -/
def vsKept (i : ℕ) : ℕ := if i < 112 then i else i + 25

/-- Where pooled claim `j`'s value is: the bus's `5` and the public input's `3` in `claim_pool`
(`6`), the tables' `159` column evaluations in `col_eval_words` (`645`), from `j - 5`. -/
def vsClaimAt (j : ℕ) : ℕ × ℕ := if 5 ≤ j ∧ j < 164 then (645, j - 5) else (6, j)

/-- The power of `λ` before batched claim `i`. -/
def vsPw (i : ℕ) : ℕ := if i = 0 then 1111 else 1111 + 4 * i

/-- The target before batched claim `i`. -/
def vsTg (i : ℕ) : ℕ := if i = 0 then 1091 else 1110 + 4 * i

/-- Batched claim `i`: its value read, the target and the power updated. -/
def vsLamStep (i : ℕ) : List Stmt :=
  [vsLd (1112 + 4 * i) (vsClaimAt (vsKept i)).1 (vsClaimAt (vsKept i)).2,
    vsMul (1113 + 4 * i) (vsPw i) (1112 + 4 * i), vsAdd (1114 + 4 * i) (vsTg i) (1113 + 4 * i),
    vsMul (1115 + 4 * i) (vsPw i) 1111]

/-- The batching challenge, the target (G:3472-3485). -/
def vsLamT : List Stmt :=
  vsSqzT 754 1092 ++ (List.range 142).flatMap vsLamStep ++
    [vsMul 1680 1679 657, vsAdd 1681 1678 1680]

/-- `open_stacked`'s specializations, named by `natStr` (which the kernel evaluates). -/
def vsOpenNames : List String := (List.range 11).map fun m ↦ "open_stacked__L" ++ B1.Whir.natStr m

theorem vsOpenNames_eq : vsOpenNames = B1.Whir.openNames := by
  simp only [vsOpenNames, B1.Whir.openNames, B1.Whir.natStr_eq]

/-- The placement, the stack's log and its size selector, the dispatch on the size with the rate's
selector passed on, the terminal, the deferred claim (G:3534-3557). -/
def vsTailT : List Stmt :=
  [vsCall "certify_placement" [139, 4] [1682, 1683],
    vsCall "log2_ceil_in_the_exponent__L16_L34" [1682, 4] [1684],
    vsConst 1685 (word 14347465658197868555 0 0), vsMul 1686 1684 1685, vsConst 1687 (word 1024 0 0),
    vsRange 1686 1688 1689 1690 1687,
    .dispatch (.n 1686) vsOpenNames
      [.n 122, .n 1100, .n 1101, .n 1102, .n 1103, .n 1104, .n 1681, .n 324, .n 334, .n 656]
      (vsRun 1691 5),
    vsCall "check_opening_terminal" [4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647,
      665, 1692, 1693, 1694, 1695, 1691] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1696 + k) 310 k, vsLd (1696 + k) 5 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (1715 + k) 346 k, vsLd (1715 + k) 5 (19 + k)]) ++
  [vsLd 643 5 23, .ret []]

/-- **`verify_sub`'s body as a template.** -/
def vsT : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT

end
end LeanVM.Guest.B1.VerifySub
