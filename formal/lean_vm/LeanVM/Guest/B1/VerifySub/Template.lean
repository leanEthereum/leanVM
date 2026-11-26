/-
  LeanVM.Guest.B1.VerifySub.Template

  `verify_sub`'s body as a template, section by section.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.VerifySub.GrindOff
public import LeanVM.Guest.B1.Whir.Split
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
public import LeanVM.Guest.B1.Tables.InterfaceP

/-!
# `verify_sub` as a template

The sections, in order (G = `lean_ethereum.py`):

* `vsHeadT`: the pool, the seed's permutation (`keccak_cells`), the stream;
* `vsReadsT`: the eight announced words read (`fs_next`), the table rows stored, the first four
  absorbed;
* `vsSizesT`: the rate and the memory's log-size as `g`-powers, their range checks, `dims_g`, `kb`
  in the frame and `kappa_base`;
* `vsPushT`: the push blocks' total `g_squares[kb[src]·g^adj]`, the bus depth `g^μ`, `zeta`
 ;
* `vsRootsT`: the last four announced words absorbed, the root's two words read;
* `vsPlaceT`: `certify_placement`, the stack's log `g^m` and `g^(m - 20)` range-checked
 ;
* `vsOodT`: the out-of-domain grind (inlined, `gcInlineOT`) and point (`squeeze_point_from`), its value and the bus
  grind's nonce (`opening_message`);
* `vsBusGrindT`: the bus grind, dispatched on `μ - 20`;
* `vsFpwT`: the sixteen slot weights, then `β`;
* `vsCallsT`: `verify_bus_gkr`, `verify_tables`, `verify_keccak`;
* `vsMapsT`: the ring map's sixteen challenges after a grind (inlined);
* `vsCtabT`: their Frobenius coefficients `c_table`, and `ring_switch_target`;
* `vsLamT`: the batching challenge and the target, the pooled values read from `claim_pool` and
  `col_eval_words` (the output lanes' left out), the Keccak reduction's and the out-of-domain
  claims last;
* `vsTailT`: the dispatch to `open_stacked` on the stack's size, the terminal, the deferred claim
 .
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

/-- A permutation with nothing waiting (the zero cell `8`, the cells `9 .. 11`), on the capacity
from `capb`, outputs from `o`: its first output is the challenge. -/
def vsPermT (capb o : ℕ) : Stmt :=
  keccakA ([.n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[2]"), .n (val% «verify_sub» "s3#0[3]"), .n (val% «verify_sub» "s3#0[4]")] ++ vsRun capb 5) (vsRun o 13)

/-- A squeeze with nothing waiting (the zero cell `8`, the cells `9 .. 11`), on the capacity
from `capb`, outputs from `o`, the challenge at `o + 13`. -/
def vsSqzT (capb o : ℕ) : List Stmt :=
  keccakA ([.n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[2]"), .n (val% «verify_sub» "s3#0[3]"), .n (val% «verify_sub» "s3#0[4]")] ++ vsRun capb 5) (vsRun o 13) ::
    challengeT (.n o) (o + 13)

/-! ## The sections -/

/-- The pool, the seed, the stream. -/
def vsHeadT : List Stmt :=
  [vsAlloc 6 159, vsConst 7 (word 1 0), vsConst 8 (word 0 0), vsConst 9 (word 0 0),
    vsConst 10 (word 0 0), vsConst 11 (word 0 0),
    keccakA [.n (val% «verify_sub» "seed_0"), .n (val% «verify_sub» "seed_1"), .n (val% «verify_sub» "pi_0"), .n (val% «verify_sub» "pi_1"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[2]"), .n (val% «verify_sub» "s3#0[3]"), .n (val% «verify_sub» "s3#0[4]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[2]"), .n (val% «verify_sub» "s3#0[3]"), .n (val% «verify_sub» "s3#0[4]")]
      (vsRun 12 13),
    vsAlloc 25 8192, .atom (.hint (.witness "stream" (.heap (.n (val% «verify_sub» "stream")) 0 8192))), vsAlloc 26 6]

/-- The eight announced words: `x_i` at `27 + 3 i` (`i < 4`) and `52 + 3 (i - 4)`, rows `1 .. 6`
stored in `table_rows`, the first four absorbed after the fourth. -/
def vsReadsT : List Stmt :=
  fsNextT (.n (val% «verify_sub» "stream")) 0 (val% «verify_sub» "x@1") ++ fsNextT (.n (val% «verify_sub» "stream")) 1 (val% «verify_sub» "x@2") ++ [vsLd 30 26 0] ++ fsNextT (.n (val% «verify_sub» "stream")) 2 (val% «verify_sub» "x@3") ++
    [vsLd 33 26 1] ++ fsNextT (.n (val% «verify_sub» "stream")) 3 (val% «verify_sub» "x@4") ++ [vsLd 36 26 2] ++
    [keccakA [.n (val% «verify_sub» "rate[0]@1"), .n (val% «verify_sub» "rate[1]@1"), .n (val% «verify_sub» "rate[2]@1"), .n (val% «verify_sub» "rate[3]@1"), .n (val% «verify_sub» "rate[4]@1"), .n (val% «verify_sub» "rate[5]@1"), .n (val% «verify_sub» "rate[6]@1"), .n (val% «verify_sub» "rate[7]@1"), .n (val% «verify_sub» "sp[8]"), .n (val% «verify_sub» "sp[9]"), .n (val% «verify_sub» "sp[10]"), .n (val% «verify_sub» "sp[11]"),
      .n (val% «verify_sub» "sp[12]")] (vsRun 39 13)] ++
    fsNextT (.n (val% «verify_sub» "stream")) 4 (val% «verify_sub» "x@5") ++ [vsLd 52 26 3] ++ fsNextT (.n (val% «verify_sub» "stream")) 5 (val% «verify_sub» "x@6") ++ [vsLd 55 26 4] ++
    fsNextT (.n (val% «verify_sub» "stream")) 6 (val% «verify_sub» "x@7") ++ [vsLd 58 26 5] ++ fsNextT (.n (val% «verify_sub» "stream")) 7 (val% «verify_sub» "x@8")

/-- The rate and the memory's log as `g`-powers, `dims_g`, `kb` in the frame and `kappa_base`
. -/
def vsSizesT : List Stmt :=
  [vsCall "g_power_of_word" [61] [64], vsConst 65 (word 2 0), vsMul 64 66 65,
    vsConst 67 (word 8 0), vsRange 66 68 69 70 67, vsAlloc 71 7,
    vsCall "g_power_of_word" [27] [72], vsConst 73 (word 1073741824 0),
    vsRange 72 74 75 76 73, vsConst 77 (word 4294967296 0), vsConst 78 (word 2 0),
    vsMul 72 79 78, vsRange 79 80 81 82 77, vsLd 72 71 0,
    .atom (.hint (.witness "table_logs" (.heap (.n (val% «verify_sub» "dims_g")) 1 6))), vsAlloc 83 8,
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

/-- The push blocks' total, the bus depth, `zeta`. -/
def vsPushT : List Stmt :=
  (List.range 54).flatMap vsPushStep ++
    [vsCall "log2_ceil_in_the_exponent__L0_L34" [252, 4] [253],
      vsAlloc (val% «verify_sub» "zeta") 34]

/-- The last four words absorbed, the root's two words read. -/
def vsRootsT : List Stmt :=
  [keccakA [.n (val% «verify_sub» "rate[0]@2"), .n (val% «verify_sub» "rate[1]@2"), .n (val% «verify_sub» "rate[2]@2"), .n (val% «verify_sub» "rate[3]@2"), .n (val% «verify_sub» "rate[4]@2"), .n (val% «verify_sub» "rate[5]@2"), .n (val% «verify_sub» "rate[6]@2"), .n (val% «verify_sub» "rate[7]@2"), .n (val% «verify_sub» "nxt[8]@1"), .n (val% «verify_sub» "nxt[9]@1"), .n (val% «verify_sub» "nxt[10]@1"),
    .n (val% «verify_sub» "nxt[11]@1"), .n (val% «verify_sub» "nxt[12]@1")] (vsRun 255 13)] ++
  fsNextT (.n (val% «verify_sub» "stream")) 8 (val% «verify_sub» "x@9") ++ fsNextT (.n (val% «verify_sub» "stream")) 9 (val% «verify_sub» "x@10")

/-- `LIG_MIN_SHIFT_INV = g^-20`. -/
def vsGinv20 : E := word 14347465658197868555 0

/-- The placement, the stack's log `g^m`, `size_sel = g^(m - 20)` below `g^10`. -/
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
(`opening_message`). -/
def vsOodT : List Stmt :=
  fsNonceT (.n (val% «verify_sub» "stream")) 10 (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0") ++ zero2T 286 ++
  [keccakA [.n (val% «verify_sub» "rate[0]@3"), .n (val% «verify_sub» "rate[1]@3"), .n (val% «verify_sub» "rate[2]@3"), .n (val% «verify_sub» "rate[3]@3"), .n (val% «verify_sub» "rate[4]@3"), .n (val% «verify_sub» "rate[5]@3"), .n (val% «verify_sub» "rate[6]@3"), .n (val% «verify_sub» "rate[7]@3"), .n (val% «verify_sub» "nxt[8]@2"), .n (val% «verify_sub» "nxt[9]@2"),
    .n (val% «verify_sub» "nxt[10]@2"), .n (val% «verify_sub» "nxt[11]@2"), .n (val% «verify_sub» "nxt[12]@2")] (vsRun 288 13)] ++
  gcInlineOT 15 301 winTabAt (.n (val% «verify_sub» "nxt[1]@3")) (.n (val% «verify_sub» "g_squares")) ++
  [vsAlloc 355 30,
    .dispatch (.n (val% «verify_sub» "size_sel")) vsSqpNames [.n (val% «verify_sub» "nxt[8]@3"), .n (val% «verify_sub» "nxt[9]@3"), .n (val% «verify_sub» "nxt[10]@3"), .n (val% «verify_sub» "nxt[11]@3"), .n (val% «verify_sub» "nxt[12]@3"), .n (val% «verify_sub» "nxt[0]@3"), .n (val% «verify_sub» "ood_z")]
      (vsRun 356 5),
    vsAlloc 361 1, vsConst 362 (word 2048 0), vsMul 363 25 362,
    vsCall "opening_message__L1_L1" [356, 357, 358, 359, 360, 363, 361]
      ((List.range 8).map (364 + ·))]

/-- `INV_GEN^BUS_MIN_MU = g^-20`. -/
def vsGinvBus : E := word 14347465658197868555 0

/-- `bus_grind_check`'s specializations for `μ - 20 < 14`. -/
def vsBgNames : List String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3",
    "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7",
    "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11",
    "bus_grind_check__L12", "bus_grind_check__L13"]

/-- The bus grind: `g^(μ - 20)` below `g^13`, its check dispatched on it. -/
def vsBusGrindT : List Stmt :=
  [vsConst 372 vsGinvBus, vsMul 373 253 372, vsConst 374 (word 8192 0),
    vsRange 373 375 376 377 374] ++ vsTabsT 378 379 ++
  [.dispatch (.n (val% «verify_sub» "bus_grind")) vsBgNames [.n (val% «verify_sub» "pow_word"), .n (val% «verify_sub» "done~2")] [.n (val% «verify_sub» "done")]]

/-- The capacity's first value before slot weight `i + 1`'s permutation. -/
def vsFpwCap (i : ℕ) : ℕ := if i = 0 then 381 else 382 + 13 * i

/-- The sixteen slot weights, the first `opening_message`'s, then `β`. -/
def vsFpwT : List Stmt :=
  (List.range 5).map (fun i ↦ vsCopy (381 + i) (366 + i)) ++ [vsAlloc 386 16, vsLd 364 386 0] ++
  (List.range 15).flatMap (fun i ↦ [vsPermT (vsFpwCap i) (387 + 13 * i),
    vsLd (387 + 13 * i) 386 (i + 1)]) ++ [vsPermT 577 582]

/-- The bus's GKR, the tables, the Keccak reduction. -/
def vsCallsT : List Stmt :=
  vsTabsT 595 596 ++
  [vsCall "verify_bus_gkr" [590, 591, 592, 593, 594, 371, 253, 254, 596, 25] ((List.range 7).map (597 + ·)),
    vsAlloc 604 34, vsAlloc 605 4] ++ vsTabsT 606 607 ++
  [vsCall "verify_tables" [597, 598, 599, 600, 601, 602, 0, 1, 254, 253, 71, 26, 4, 386, 582, 6,
      604, 603, 607, 605, 25] ((List.range 10).map (608 + ·)),
    vsLd 618 71 6, vsAlloc 619 78, vsAlloc 620 64, vsConst 621 (word 3710851743744 0),
    vsMul 622 617 621] ++ vsTabsT 623 624 ++
  [vsCall "verify_keccak" [608, 609, 610, 611, 612, 613, 618, 604, 622, 619, 620, 624, 25]
      ((List.range 7).map (625 + ·))]

/-- The value of the ring map's challenge `i`. -/
def vsCh (i : ℕ) : ℕ := 707 + 14 * i

/-- The capacity's first value before the ring map's squeeze `i` (`i < 15`). -/
def vsChCap (i : ℕ) : ℕ := if i = 0 then 648 else 702 + 14 * i

/-- The ring map's sixteen challenges: a grind's nonce absorbed, the first drawn by its
permutation, fifteen squeezed, then stored in `map_challenges`. -/
def vsMapsT : List Stmt :=
  (List.range 5).map (fun i ↦ vsCopy (632 + i) (625 + i)) ++ fsNonceT (.n (val% «verify_sub» "cursor@4")) 0 (val% «verify_sub» "s63.i0:fs_grind_squeeze.s0.e.s0.e.s0#0") ++
  [keccakA [.n (val% «verify_sub» "rate[0]@4"), .n (val% «verify_sub» "rate[1]@4"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[1]"), .n (val% «verify_sub» "s3#0[2]"), .n (val% «verify_sub» "s3#0[3]"), .n (val% «verify_sub» "s3#0[4]"), .n (val% «verify_sub» "sp[0]@3"), .n (val% «verify_sub» "sp[1]@3"), .n (val% «verify_sub» "sp[2]@3"), .n (val% «verify_sub» "sp[3]@3"),
    .n (val% «verify_sub» "sp[4]@3")] (vsRun 640 13)] ++
  gcInlineOT 13 653 winTabAt (.n (val% «verify_sub» "nxt[1]@20")) (.n (val% «verify_sub» "g_squares")) ++
  [vsCopy 707 640] ++
  (List.range 15).flatMap (fun i ↦ vsSqzT (vsChCap i) (708 + 14 * i)) ++
  vsAlloc 918 16 :: (List.range 16).map (fun i ↦ vsLd (vsCh i) 918 i)

/-- The squarings of `c_table`'s term `q + 1` in block `b` (from `s`), from the previous power. -/
def vsSqT (b s q : ℕ) : List Stmt :=
  (List.range 8).map fun k ↦
    let t := s + 1 + 9 * q
    let x := if k = 0 then (if q = 0 then vsCh (8 + b) else t - 2) else t + k - 1
    vsMul (t + k) x x

/-- Block `b` of `c_table` (from `s = 920 + 64 b`): `c[8p + b] = f_p · g_b^(2^(8p))`. -/
def vsCtabBlock (b : ℕ) : List Stmt :=
  let s := 920 + 64 * b
  [vsMul s (vsCh 0) (vsCh (8 + b)), vsLd s 919 b] ++
  (List.range 7).flatMap fun q ↦
    let t := s + 1 + 9 * q
    vsSqT b s q ++ [vsMul (t + 8) (vsCh (q + 1)) (t + 7), vsLd (t + 8) 919 (8 * (q + 1) + b)]

/-- `c_table`, then `ring_switch_target`. -/
def vsCtabT : List Stmt :=
  vsAlloc 919 64 :: (List.range 8).flatMap vsCtabBlock ++
    [vsCall "ring_switch_target" [620, 918] [1432]]

/-- The pooled claim of the `i`-th batched one: the output lanes' `105 .. 129` are left out. -/
def vsKept (i : ℕ) : ℕ := if i < 105 then i else i + 25

/-- Where pooled claim `j`'s value is: the bus's `4` and the public input's `2` in `claim_pool`
(`6`), the tables' `153` column evaluations at `col_eval_words` (`617`), from `j - 4`. -/
def vsClaimAt (j : ℕ) : ℕ × ℕ := if 4 ≤ j ∧ j < 157 then (617, j - 4) else (6, j)

/-- The power of `λ` before batched claim `i`: `λ` itself (`1433`) before the first. -/
def vsPw (i : ℕ) : ℕ := if i = 0 then 1433 else 1445 + 4 * i

/-- The target before batched claim `i`. -/
def vsTg (i : ℕ) : ℕ := if i = 0 then 1432 else 1444 + 4 * i

/-- Batched claim `i`: its value read, the target and the power updated. -/
def vsLamStep (i : ℕ) : List Stmt :=
  [vsLd (1446 + 4 * i) (vsClaimAt (vsKept i)).1 (vsClaimAt (vsKept i)).2,
    vsMul (1447 + 4 * i) (vsPw i) (1446 + 4 * i), vsAdd (1448 + 4 * i) (vsTg i) (1447 + 4 * i),
    vsMul (1449 + 4 * i) (vsPw i) 1433]

/-- The batching challenge, the target: the `134` pooled claims, the Keccak reduction's, the
out-of-domain value. -/
def vsLamT : List Stmt :=
  vsPermT 912 1433 :: (List.range 134).flatMap vsLamStep ++
    [vsMul 1982 1981 631, vsAdd 1983 1980 1982, vsMul 1984 1981 1433, vsLd 1985 361 0,
      vsMul 1986 1984 1985, vsAdd 1987 1983 1986]

/-- `open_stacked`'s specializations, in dispatch order. -/
def vsOpenNames : List String :=
  ["open_stacked__L0", "open_stacked__L1", "open_stacked__L2", "open_stacked__L3",
    "open_stacked__L4", "open_stacked__L5", "open_stacked__L6", "open_stacked__L7",
    "open_stacked__L8", "open_stacked__L9", "open_stacked__L10"]

/-- The dispatch to `open_stacked` on the stack's size `size_sel`, the rate `rate_sel` its first
argument, the terminal, the deferred claim. -/
def vsTailT : List Stmt :=
  [vsConst 1988 (word 2 0), vsMul 1989 630 1988] ++ vsTabsT 1990 1991 ++
  [.dispatch (.n (val% «verify_sub» "size_sel")) vsOpenNames
      [.n (val% «verify_sub» "rate_sel"), .n (val% «verify_sub» "nxt[8]@36"), .n (val% «verify_sub» "nxt[9]@36"), .n (val% «verify_sub» "nxt[10]@36"), .n (val% «verify_sub» "nxt[11]@36"), .n (val% «verify_sub» "nxt[12]@36"), .n (val% «verify_sub» "target@136"), .n (val% «verify_sub» "x@9"), .n (val% «verify_sub» "x@10"), .n (val% «verify_sub» "sumcheck_target~2"),
        .n (val% «verify_sub» "sumcheck_target~4")]
      (vsRun 1992 5),
    vsCall "check_opening_terminal" [4, 254, 604, 616, 253, 614, 72, 618, 83, 1433, 275, 619, 919,
      1993, 1994, 1995, 1996, 1992, 355, 276] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1997 + k) 254 k, vsLd (1997 + k) 5 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (2016 + k) 605 k, vsLd (2016 + k) 5 (19 + k)]) ++
  [vsLd 615 5 23, .ret []]

/-- **`verify_sub`'s body as a template.** -/
def vsT : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsPlaceT ++ vsOodT ++ vsBusGrindT ++
    vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT

end
end LeanVM.Guest.B1.VerifySub
