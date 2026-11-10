/-
  LeanVM.Guest.B1.Terminal.Template

  `check_opening_terminal`'s body as a template: its head, the committed columns' selectors, one block
  per claim the opening batches, and the tail.
-/

module

public import LeanVM.Guest.B1.Terminal.Interface
public import LeanVM.Guest.Data.Source

/-!
# `check_opening_terminal`, as a template

The guest unrolls the selectors' loop (G:3260-3263) and the claims' loop (G:3267-3301) at compile
time on its tables `COL_KAPPA_SRC`, `COL_KAPPA_ADJ` (`Tables.colKappaSrc`, `Tables.colKappaAdj`),
`CLAIM_POINT_BUF`, `CLAIM_COMMITTED_COL`, `CLAIM_KAPPA_SRC`, `CLAIM_KAPPA_ADJ` and
`CLAIM_QKECCAK_SLOT_BITS`; here they are `termKind`, `termCol`, `claimKappaSrc`, `claimKappaAdj` and
the slot `termSlot j`:

* claims `0 .. 4`, the bus's, on the prefix chain at `zeta` (kind `0`), committed columns `0 .. 4`;
* claims `5 .. 71`, `86` and `137 .. 163`, the tables' committed columns, on the chain at `chi`
  (kind `1`);
* claims `72 .. 85` and `87 .. 111`, `KECCAK`'s columns with a `q_keccak` slot (its fourteen
  operand and flag columns, slots `50 .. 63`, and its input lanes, slots `0 .. 24`), on the chain
  at `chi` and their slot's bits (kind `2`), on `q_keccak` (committed column `5`);
* claims `112 .. 136`, `KECCAK`'s output lanes, skipped (kind `4`);
* claims `164 .. 166`, the public input's, on the chain of `(rm, 0, …, 0)` (kind `3`).

Every claim's source and adjustment are its column's, so the guest emits no length check
(G:3295-3299); a low length `kb[s]·g^a` is `kb[s]` itself at `a = 0` (`kapT`). The running power
of `λ` starts at `lam_cl` itself and is multiplied by it after each kept claim.

`termT` is the body (`termFound`, by kernel evaluation in `Terminal/Body`); `claimKappa_source`
checks `claimKappaSrc`, `claimKappaAdj` against the source's arrays, entry by entry.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- The kind of claim `j`'s low point (`CLAIM_POINT_BUF`): `0` the bus point, `1` the table
point, `2` a `q_keccak` lane, `3` the public input's, `4` a `KECCAK` output lane. -/
def termKind (j : ℕ) : ℕ :=
  if j < 5 then 0 else if j < 72 then 1 else if j < 86 then 2 else if j = 86 then 1
  else if j < 112 then 2 else if j < 137 then 4 else if j < 164 then 1 else 3

/-- Claim `j`'s committed column (`CLAIM_COMMITTED_COL`). -/
def termCol (j : ℕ) : ℕ :=
  if j < 5 then j else if j < 72 then j + 1 else if j < 86 then 5 else if j = 86 then 73
  else if j < 137 then 5 else if j < 164 then j - 63 else j - 164

/-- The `q_keccak` slot of claim `j` of kind `2` (`CLAIM_QKECCAK_SLOT_BITS`). -/
def termSlot (j : ℕ) : ℕ := if j < 86 then j - 22 else j - 87

/-- The claims' sources and adjustments are the source's arrays `CLAIM_KAPPA_SRC`,
`CLAIM_KAPPA_ADJ`. -/
theorem claimKappa_source :
    (List.range Tables.nClaims).all (fun j ↦
      claimKappaSrc j == (Data.arr_CLAIM_KAPPA_SRC.getD j (0, 0, 0)).1 &&
        claimKappaAdj j == (Data.arr_CLAIM_KAPPA_ADJ.getD j (0, 0, 0)).1) = true := by
  decide +kernel

/-- The selectors' specializations, `column_selector__L{κ}`, `κ < 33`. -/
def colSelNames : List String := (List.range 33).map (Tables.lName "column_selector")

/-- The value holding `kappa_base[i]`, read in the head (G:3254-3256). -/
abbrev kbV (i : ℕ) : ℕ := 33 + i

/-- `kb[src]·g^adj` from value `r`: the statements, the value holding it and the next value; at
`adj = 0` the compiler uses `kb[src]` itself. -/
def kapT (src adj r : ℕ) : List Stmt × ℕ × ℕ :=
  if adj = 0 then ([], kbV src, r) else
    ([.atom (.const (.n r) (word (2 ^ adj) 0 0)), .atom (.mul (.n (r + 1)) (.n (kbV src)) (.n r))],
      r + 1, r + 2)

/-- The first value of committed column `c`'s selector block. -/
def selStart (c : ℕ) : ℕ := 42 + 4 * c + (if 4 < c then 2 else 0) + (if 5 < c then 2 else 0)

/-- Committed column `c`'s `g^κ`, from its block's second value. -/
def selKap (c : ℕ) : List Stmt × ℕ × ℕ :=
  kapT (Tables.colKappaSrc c) (Tables.colKappaAdj c) (selStart c + 1)

/-- The value of committed column `c`'s selector. -/
def selV (c : ℕ) : ℕ := (selKap c).2.2 + 2

/-- The head (G:3239-3258): the chains at `zeta` (`18`) and `chi` (`20`), the slot points (`22`,
`23`), the public input's chain (`24`, its loop `__loop14`) and its value (`32`), the base
`kappa_base` (`33 .. 40`), the selector tables (`41`). -/
def termHeadT : List Stmt :=
  [.atom (.hint (.alloc (.n 18) 35)), .atom (.const (.n 19) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 18, .n 19, .n 1, .n 14, .n 4] [],
    .atom (.hint (.alloc (.n 20) 35)), .atom (.const (.n 21) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 20, .n 21, .n 2, .n 14, .n 5] [],
    .atom (.mul (.n 22) (.n 13) (.n 7)), .atom (.mul (.n 23) (.n 14) (.n 7)),
    .atom (.hint (.alloc (.n 24) 35)), .atom (.const (.n 25) (word 1 0 0)),
    .atom (.load (.n 25) (.n 24) 0), .atom (.load (.n 26) (.n 14) 0),
    .atom (.add (.n 27) (.n 3) (.n 26)), .atom (.load (.n 27) (.n 24) 1),
    .atom (.const (.n 28) (word 2 0 0)), .atom (.add (.n 29) (.n 28) (.n 6)),
    .atom (.const (.n 30) (word 2 0 0)),
    .callIf (.n 29) "__loop14" [.n 30, .n 6, .n 24, .n 14],
    .atom (.mul (.n 31) (.n 24) (.n 6)), .atom (.load (.n 32) (.n 31) 0),
    .atom (.load (.n 33) (.n 8) 0), .atom (.load (.n 34) (.n 8) 1),
    .atom (.load (.n 35) (.n 8) 2), .atom (.load (.n 36) (.n 8) 3),
    .atom (.load (.n 37) (.n 8) 4), .atom (.load (.n 38) (.n 8) 5),
    .atom (.load (.n 39) (.n 8) 6), .atom (.load (.n 40) (.n 8) 7),
    .call "selector_tables" [.n 13, .n 14] [.n 41]]

/-- Committed column `c`'s selector (G:3260-3263): its offset, its `g^κ`, `sel_g = g_squares·g^34`
and the dispatch on `κ`. -/
def selBlockT (c : ℕ) : List Stmt :=
  [.atom (.load (.n (selStart c)) (.n 10) c)] ++ (selKap c).1 ++
    [.atom (.const (.n (selKap c).2.2) (word 17179869184 0 0)),
      .atom (.mul (.n ((selKap c).2.2 + 1)) (.n 0) (.n (selKap c).2.2)),
      .dispatch (.n (selKap c).2.1) colSelNames
        [.n (selStart c), .n 41, .n ((selKap c).2.2 + 1)] [.n (selV c)]]

/-- The selectors, one per committed column. -/
def selsT : List Stmt := (List.range Tables.nCommittedCols).flatMap selBlockT

/-- The claims' first value: past the selectors. -/
abbrev claimsStart : ℕ := 450

/-- A claim on a prefix chain at `ch` (kinds `0`, `1`), its length's `g`-power at `kr`, its
column's selector at `sel`, the running power at `lr`, from value `r`, the sum so far at `acc`. -/
def zrT (ch kr sel lr r acc : ℕ) : List Stmt :=
  [.atom (.mul (.n r) (.n ch) (.n kr)), .atom (.load (.n (r + 1)) (.n r) 0),
    .atom (.mul (.n (r + 2)) (.n lr) (.n (r + 1))),
    .atom (.mul (.n (r + 3)) (.n (r + 2)) (.n sel)),
    .atom (.add (.n (r + 4)) (.n acc) (.n (r + 3))), .atom (.mul (.n (r + 5)) (.n lr) (.n 9))]

/-- Slot bit `k` of `s`'s point: `slot_point` (`22`) at a one, `slot_point1` (`23`) at a zero. -/
def slotPt (s k : ℕ) : ℕ := if s.testBit k then 22 else 23

/-- A `q_keccak` lane's claim (kind `2`) at slot `s`. -/
def qT (s kr lr r acc : ℕ) : List Stmt :=
  [.atom (.load (.n r) (.n (slotPt s 5)) 5), .atom (.load (.n (r + 1)) (.n (slotPt s 4)) 4),
    .atom (.mul (.n (r + 2)) (.n r) (.n (r + 1))),
    .atom (.load (.n (r + 3)) (.n (slotPt s 3)) 3),
    .atom (.mul (.n (r + 4)) (.n (r + 2)) (.n (r + 3))),
    .atom (.load (.n (r + 5)) (.n (slotPt s 2)) 2),
    .atom (.mul (.n (r + 6)) (.n (r + 4)) (.n (r + 5))),
    .atom (.load (.n (r + 7)) (.n (slotPt s 1)) 1),
    .atom (.mul (.n (r + 8)) (.n (r + 6)) (.n (r + 7))),
    .atom (.load (.n (r + 9)) (.n (slotPt s 0)) 0),
    .atom (.mul (.n (r + 10)) (.n (r + 8)) (.n (r + 9))),
    .atom (.mul (.n (r + 11)) (.n 20) (.n kr)), .atom (.load (.n (r + 12)) (.n (r + 11)) 0),
    .atom (.mul (.n (r + 13)) (.n (r + 10)) (.n (r + 12))),
    .atom (.mul (.n (r + 14)) (.n lr) (.n (r + 13))),
    .atom (.mul (.n (r + 15)) (.n (r + 14)) (.n (selV 5))),
    .atom (.add (.n (r + 16)) (.n acc) (.n (r + 15))), .atom (.mul (.n (r + 17)) (.n lr) (.n 9))]

/-- A public input's claim (kind `3`). -/
def pT (sel lr r acc : ℕ) : List Stmt :=
  [.atom (.mul (.n r) (.n lr) (.n 32)), .atom (.mul (.n (r + 1)) (.n r) (.n sel)),
    .atom (.add (.n (r + 2)) (.n acc) (.n (r + 1))), .atom (.mul (.n (r + 3)) (.n lr) (.n 9))]

/-- Claim `j`'s low length's `g`-power, from value `r`. -/
def claimKap (j r : ℕ) : List Stmt × ℕ × ℕ := kapT (claimKappaSrc j) (claimKappaAdj j) r

/-- Claim `j`'s block from value `r`, the sum so far at `acc`, the running power at `lr`: the
statements, the next value, the sum's value and the next power's. -/
def claimT (j r acc lr : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  match termKind j with
  | 0 => ((claimKap j r).1 ++
        zrT 18 (claimKap j r).2.1 (selV (termCol j)) lr (claimKap j r).2.2 acc,
      (claimKap j r).2.2 + 6, (claimKap j r).2.2 + 4, (claimKap j r).2.2 + 5)
  | 1 => ((claimKap j r).1 ++
        zrT 20 (claimKap j r).2.1 (selV (termCol j)) lr (claimKap j r).2.2 acc,
      (claimKap j r).2.2 + 6, (claimKap j r).2.2 + 4, (claimKap j r).2.2 + 5)
  | 2 => ((claimKap j r).1 ++ qT (termSlot j) (claimKap j r).2.1 lr (claimKap j r).2.2 acc,
      (claimKap j r).2.2 + 18, (claimKap j r).2.2 + 16, (claimKap j r).2.2 + 17)
  | 3 => (pT (selV (termCol j)) lr r acc, r + 4, r + 2, r + 3)
  | _ => ([], r, acc, lr)

/-- The claims `js` from value `r`, the sum so far at `acc`, the running power at `lr`: the
statements, the next value, the sum's value and the power's. -/
def claimsT : List ℕ → ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ × ℕ
  | [], r, acc, lr => ([], r, acc, lr)
  | j :: js, r, acc, lr =>
      let b := claimT j r acc lr
      let rest := claimsT js b.2.1 b.2.2.1 b.2.2.2
      (b.1 ++ rest.1, rest.2)

/-- The tail (G:3308-3318) from value `b`, the claims' sum at `acc`, `lam_out` at `lo`: the
outputs' chain, the ring switch's weight, the terminal check. -/
def termTailT (b acc lo : ℕ) : List Stmt :=
  [.atom (.hint (.alloc (.n b) 41)), .atom (.const (.n (b + 1)) (word 1 0 0)),
    .atom (.const (.n (b + 2)) (word 64 0 0)), .atom (.mul (.n (b + 3)) (.n 7) (.n (b + 2))),
    .call "eq_prefix_chain" [.n b, .n (b + 1), .n 11, .n 14, .n (b + 3)] [],
    .atom (.const (.n (b + 4)) (word 549755813888 0 0)),
    .atom (.mul (.n (b + 5)) (.n 11) (.n (b + 4))),
    .atom (.const (.n (b + 6)) (word 64 0 0)), .atom (.mul (.n (b + 7)) (.n 7) (.n (b + 6))),
    .call "ring_switch_weight" [.n (b + 5), .n 14, .n 12, .n (b + 7)] [.n (b + 8)],
    .atom (.mul (.n (b + 9)) (.n b) (.n 7)), .atom (.load (.n (b + 10)) (.n (b + 9)) 6),
    .atom (.mul (.n (b + 11)) (.n lo) (.n (b + 10))),
    .atom (.add (.n (b + 12)) (.n (b + 8)) (.n (b + 11))),
    .atom (.mul (.n (b + 13)) (.n (b + 12)) (.n (selV 5))),
    .atom (.add (.n (b + 14)) (.n acc) (.n (b + 13))),
    .atom (.mul (.n (b + 15)) (.n (b + 14)) (.n 16)), .atom (.assertEq (.n (b + 15)) (.n 17)),
    .ret []]

/-- The claims' blocks, from the first claim value, the sum at `inner_total` (`15`) and the power
at `lam_cl` (`9`). -/
def termClaims : List Stmt × ℕ × ℕ × ℕ := claimsT (List.range Tables.nClaims) claimsStart 15 9

/-- **`check_opening_terminal`'s body.** -/
def termT : List Stmt :=
  termHeadT ++ selsT ++ termClaims.1 ++
    termTailT termClaims.2.1 termClaims.2.2.1 termClaims.2.2.2

end
end LeanVM.Guest.B1.VerifySub
