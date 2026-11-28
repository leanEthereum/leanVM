/-
  LeanVM.Guest.B1.Stack.TermT

  `check_stack_terminal`'s core IR as a template.
-/

module

public import LeanVM.Guest.B1.Stack.StkSel
public import LeanVM.Guest.B1.Stack.TermPure
public import LeanVM.Guest.B1.Eq.EqTree

/-!
# `check_stack_terminal`: the template

`cstBody`, checked against the core IR (`check_stack_terminal_body`): the header (`(g_n g)^64`, the
buffers, the selectors' dispatch on the stack's size, the kappa sources, `q_keccak`'s ring row by
`rs_eq_run`, `cstHead`), the row's sum (`cstRowSum`), the pointers' scales (`cstRq`), the ring
rows and the slots' `eq` weights (`eqtreeT`), per table the pointers' masks (`cstMasks`) and
`ring_cols` (`cstTab0`, `cstTab`), the prefix chains of the memory, the public input, the Keccak
output, the out-of-domain point and the row point (`cstMem`), the sent columns by Horner
(`cstSent`), and the check (`cstTail`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The selectors' dispatch, by the stack's log-size from `16`. -/
def cstArms : List String :=
  ["stack_selectors__L4", "stack_selectors__L5", "stack_selectors__L5", "stack_selectors__L5",
    "stack_selectors__L5", "stack_selectors__L6", "stack_selectors__L6", "stack_selectors__L6",
    "stack_selectors__L6", "stack_selectors__L7", "stack_selectors__L7", "stack_selectors__L7",
    "stack_selectors__L7", "stack_selectors__L8", "stack_selectors__L8"]

/-- The header. -/
def cstHead : List Stmt :=
  [osCst 23 (word 2 0), osMul 24 6 23, osMul 25 24 24, osMul 26 25 25, osMul 27 26 26, osMul 28 27 27,
    osMul 29 28 28, osMul 30 29 29,
    .atom (.hint (.allocDyn (.n 31) (.n 30))), .atom (.hint (.alloc (.n 32) 33)),
    .atom (.hint (.alloc (.n 33) 33)), .atom (.hint (.alloc (.n 34) 42)), .atom (.hint (.alloc (.n 35) 42)),
    .atom (.hint (.alloc (.n 36) 42)), .atom (.hint (.alloc (.n 37) 42)), .atom (.hint (.alloc (.n 38) 31)),
    .atom (.hint (.alloc (.n 39) 126)), .atom (.hint (.alloc (.n 40) 31)),
    osCst 41 (word 8198521646651277316 0), osMul 42 4 41,
    .dispatch (.n 42) cstArms [.n 2, .n 3, .n 17, .n 18, .n 0] [.n 43],
    osLd 44 1 0, osLd 45 1 1, osLd 46 1 2, osLd 47 1 3, osLd 48 1 4, osLd 49 1 5, osLd 50 1 6, osLd 51 1 7,
    osLd 52 43 2, osLd 53 43 0, osLd 54 43 1, osCst 55 (word 549755813888 0), osMul 56 10 55,
    osCst 57 (word 64 0), osMul 58 51 57, .call "rs_eq_run" [.n 56, .n 18, .n 58, .n 12] [.n 59]]

/-- The sum of `q_keccak`'s ring row, times its selector. -/
def cstRowSum : List Stmt :=
  [osLd 60 59 0, osLd 61 59 1, osAdd 62 60 61] ++
    ((List.range 62).map fun i ↦ [osLd (63 + 2 * i) 59 (i + 2), osAdd (64 + 2 * i) (62 + 2 * i) (63 + 2 * i)]).flatten ++
    [osMul 187 186 52]

/-- The pointers' scales `rho · eq(q_point, q)`. -/
def cstRq : List Stmt :=
  ((List.range 33).map fun q ↦
    [osLd (188 + 2 * q) 11 (62 + q), osMul (189 + 2 * q) 13 (188 + 2 * q), osLd (189 + 2 * q) 33 q]).flatten

/-- The values a pointer's mask takes. -/
def maskVals (k : ℕ) : ℕ := if k < 52 then 1 else 2

/-- Pointer `q`'s mask from value `v`: its block's selector, or its slot's weight times `q_keccak`'s. -/
def cstMask (v q k : ℕ) : List Stmt :=
  if k < 52 then [osLd v 43 k, osLd v 32 q] else [osLd v 39 (k + 10), osMul (v + 1) v 52, osLd (v + 1) 32 q]

/-- The masks of pointers `q ..` of kinds `ks`, from value `v`. -/
def cstMasks : ℕ → ℕ → List ℕ → List Stmt
  | _, _, [] => []
  | v, q, k :: ks => cstMask v q k ++ cstMasks (v + maskVals k) (q + 1) ks

/-- The values the masks of kinds `ks` take. -/
def masksVals : List ℕ → ℕ
  | [] => 0
  | k :: ks => maskVals k + masksVals ks

/-- `kb^64` from `w`. -/
def cstSq (w kb : ℕ) : List Stmt := osMul w kb kb :: (List.range 5).map fun i ↦ osMul (w + 1 + i) (w + i) (w + i)

/-- Table `0`'s pointers. -/
def cstTab0 : List Stmt :=
  cstMasks 459 0 [9, 8, 5, 6, 7] ++ cstSq 464 46 ++
    [osMul 470 31 469, .call "ring_cols__L5" [.n 470, .n 33, .n 32] [.n 471]]

/-- A later table's pointers: masks from `v0` (pointers `q0 ..` of kinds `ks`), its height's word `kb`, the
scales' and masks' pointers moved by `W` from `rq`, `pm`, and the running sum `acc`. -/
def cstTab (v0 q0 : ℕ) (ks : List ℕ) (kb : ℕ) (W : E) (rq pm acc : ℕ) (name : String) : List Stmt :=
  let w := v0 + masksVals ks
  cstMasks v0 q0 ks ++ cstSq w kb ++
    [osMul (w + 6) 31 (w + 5), osCst (w + 7) W, osMul (w + 8) rq (w + 7), osCst (w + 9) W,
      osMul (w + 10) pm (w + 9), .call name [.n (w + 6), .n (w + 8), .n (w + 10)] [.n (w + 11)],
      osAdd (w + 12) acc (w + 11)]

/-- The ring rows, the slots' weights and the tables' pointers. -/
def cstRing : List Stmt :=
  [.call "ring_rows" [.n 31, .n 5, .n 18, .n 12, .n 6] [], osMul 254 17 51] ++ eqtreeT (.n 254) (.n 39) 0 255 6 ++
    cstTab0 ++ cstTab 472 5 [18, 17, 14, 15, 16] 47 (word 32 0) 33 32 471 "ring_cols__L5" ++
    cstTab 490 10 [23, 22, 21] 48 (word 32 0) 485 487 489 "ring_cols__L3" ++
    cstTab 506 13 [33, 32, 29, 30, 31] 49 (word 8192 0) 33 32 505 "ring_cols__L5" ++
    cstTab 524 18 [47, 46, 43, 44, 45] 50 (word 32 0) 519 521 523 "ring_cols__L5" ++
    cstTab 542 23 [51, 50, 110, 111, 112, 113, 114, 115, 48, 49] 51 (word 32 0) 537 539 541 "ring_cols__L10" ++
    [osAdd 571 187 570]

/-- The prefix chains and the claims before the sent columns. -/
def cstMem : List Stmt :=
  [osCst 572 (word 1 0), .call "eq_prefix_chain" [.n 36, .n 572, .n 7, .n 18, .n 8] [], osMul 573 36 8,
    osLd 574 573 0, osMul 575 15 53, osMul 576 16 54, osAdd 577 575 576, osMul 578 574 577, osLd 9 38 0] ++
    ((List.range 30).map fun i ↦ [osCst (579 + i) (word 0 0), osLd (579 + i) 38 (i + 1)]).flatten ++
    [osCst 609 (word 1 0), .call "eq_prefix_chain" [.n 37, .n 609, .n 38, .n 18, .n 8] [], osMul 610 37 8,
      osLd 611 610 0, osCst 612 (word 1 0), osCst 613 (word 64 0), osMul 614 51 613,
      .call "eq_prefix_chain" [.n 35, .n 612, .n 10, .n 18, .n 614] [],
      osCst 615 (word 1 0), .call "eq_prefix_chain" [.n 40, .n 615, .n 22, .n 18, .n 4] [],
      osCst 616 (word 1 0), .call "eq_prefix_chain" [.n 34, .n 616, .n 5, .n 18, .n 6] [],
      osMul 617 40 4, osLd 618 617 0, osMul 619 618 14, osMul 620 35 51, osLd 621 620 6, osMul 622 621 52,
      osAdd 623 619 622, osMul 624 623 14, osMul 625 611 54, osAdd 626 624 625, osMul 627 626 14,
      osMul 628 611 53, osAdd 629 627 628, osMul 630 34 51, osLd 631 630 0, osMul 632 631 52]

/-- The values a sent column takes. -/
def sentVals (k : ℕ) : ℕ := if k < 52 then 7 else 4

/-- A sent column of kind `k` from value `v`, the batch so far at `acc`. -/
def cstSentOne (v acc k : ℕ) : List Stmt :=
  if k < 52 then
    [osLd v 3 k, osMul (v + 1) 34 v, osLd (v + 2) (v + 1) 0, osLd (v + 3) 43 k, osMul (v + 4) (v + 2) (v + 3),
      osMul (v + 5) acc 14, osAdd (v + 6) (v + 5) (v + 4)]
  else [osLd v 39 (k + 10), osMul (v + 1) 632 v, osMul (v + 2) acc 14, osAdd (v + 3) (v + 2) (v + 1)]

/-- The sent columns of kinds `ks`, by Horner. -/
def cstSent : ℕ → ℕ → List ℕ → List Stmt
  | _, _, [] => []
  | v, acc, k :: ks => cstSentOne v acc k ++ cstSent (v + sentVals k) (v + sentVals k - 1) ks

/-- The check. -/
def cstTail : List Stmt :=
  [osMul 919 918 14, osAdd 920 919 578, osMul 921 920 14, osAdd 922 571 921, osAdd 923 19 922,
    osMul 924 923 20, .atom (.assertEq (.n 924) (.n 21))]

/-- `check_stack_terminal` before its return. -/
def cstBodyA : List Stmt :=
  cstHead ++ cstRowSum ++ cstRq ++ cstRing ++ cstMem ++ cstSent 633 629 sentList.reverse ++ cstTail

/-- **The expansion of `check_stack_terminal`.** -/
def cstBody : List Stmt := cstBodyA ++ [.ret []]

set_option maxRecDepth 100000 in
theorem check_stack_terminal_body : Fn.body fn% «check_stack_terminal» = cstBody :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Stack
