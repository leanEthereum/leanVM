/-
  LeanVM.Guest.B1.Tables.VerifyTablesBus

  `verify_tables`' bus decomposition: what each side's tables owe, from the framework blocks'
  fingerprints, the selectors and the padding rows.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesAir
public import LeanVM.Guest.B1.Tables.VerifyTablesSel

/-!
# The bus decomposition (G:1559-1694)

For each side, `verify_tables` computes `bus_table_total`: the side's GKR value plus the framework
blocks' fingerprints weighted by their selectors, the selectors' sum plus one, and the padding
rows' mass. The value is the expression `pushTotalEx` (and its pull and count counterparts),
built from the specification's fingerprints and its forms at the padding rows: the normal forms
agree by kernel evaluation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-- Block `i`'s selector, push or count (`selNames` order), by value number. -/
def busSel (i : ℕ) : Ex := .var (selVal.getD i 0 + 23)

/-- The owners of the push side's table blocks. -/
def pushOwners : List ℕ :=
  [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

/-- The push side's table blocks' coordinates, symbolically, in block order. -/
def pushCoordsC : List (List FormC) := (List.finRange 6).flatMap fun t => pySideC t .push

/-- A table's padding row in `K` (`Table.padding`). -/
def padK (t c : ℕ) : K :=
  let tb := tables.getD t default
  let slots := if tb.opcode = opBlake2s then blake2sSlots else []
  match tb.columns[c]? with
  | some name => if some name ∈ slots then K.ofBits (paddingInstance.getD (slots.idxOf (some name)) 0)
      else 0
  | none => 0

/-- A symbolic coordinate's value at table `t`'s padding row. -/
def coordPadK (t : ℕ) (f : FormC) : K := termsEval (padK t) f.termsK

/-- A push or pull table block's form at its padding row plus one:
`β + 1 + Σ_i fp_w[i]·coord_i(padding)`. -/
def padBlockEx (t : ℕ) (coords : List FormC) : Ex :=
  .add (.add (.var 12) (sumEx (coords.zipIdx.map fun p => .mul (.ext p.2) (.lit (coordPadK t p.1)))))
    (.lit 1)

/-- The push side's padding mass, block by block: the block's selector times its table's padding
weight times its form at the padding row plus one. -/
def pushPadEx : Ex :=
  sumEx ((List.range 34).map fun j => .mul (.mul (busSel (3 + j))
    (.var (1739 + 14 * pushOwners.getD j 0))) (padBlockEx (pushOwners.getD j 0) (pushCoordsC.getD j [])))

/-- The push side's framework fingerprints, weighted by their selectors (`fingerprints` at
`pc = 1`, unit counts). -/
def pushFwEx : Ex :=
  sumEx [.mul (busSel 0) (.add (.var 12) (sumEx [.ext 0, .ext 1, .ext 2])),
    .mul (busSel 1) (.add (.var 12) (sumEx [.mul (.ext 0) (.lit (K.ofBits 2)), .mul (.ext 1) (.var 1931),
      .ext 2, .mul (.ext 3) (.var 1937), .mul (.ext 4) (.var 1955), .mul (.ext 5) (.var 1973)])),
    .mul (busSel 2) (.add (.var 12) (.add (sumEx [.mul (.ext 0) (.lit (K.ofBits 4)),
      .mul (.ext 1) (.var 2035), .ext 2]) (.var 1732)))]

/-- What the push side's tables owe (`bus_table_total[PUSH]`). -/
def pushTotalEx : Ex :=
  sumEx [.var 21, pushFwEx, sumEx ((List.range 37).map busSel), .lit 1, pushPadEx]

/-- The guest's push total, symbolically. -/
noncomputable def pushTotalSym : Ex :=
  (symExec vtFpwTab [] (((vtPre.drop 1505).take 1587).filterMap atomOf)).get 3326

theorem vt_push_total : pushTotalSym.norm = pushTotalEx.norm := by decide +kernel

/-- The pull side's table blocks' coordinates, symbolically, in block order. -/
def pullCoordsC : List (List FormC) := (List.finRange 6).flatMap fun t => pySideC t .pull

/-- The pull side's padding mass, block by block, its blocks' selectors their push twins'. -/
def pullPadEx : Ex :=
  sumEx ((List.range 34).map fun j => .mul (.mul (busSel (3 + j))
    (.var (1739 + 14 * pushOwners.getD j 0))) (padBlockEx (pushOwners.getD j 0) (pullCoordsC.getD j [])))

/-- The pull side's framework fingerprints, weighted by their selectors (`fingerprints` at the
final `pc`, the final counters). -/
def pullFwEx : Ex :=
  sumEx [.mul (busSel 0) (.add (.var 12) (sumEx [.ext 0,
      .mul (.ext 1) (.lit (gpowK (2 ^ 18 - 1))), .ext 2])),
    .mul (busSel 1) (.add (.var 12) (sumEx [.mul (.ext 0) (.lit (K.ofBits 2)), .mul (.ext 1) (.var 1931),
      .mul (.ext 2) (.var 3359), .mul (.ext 3) (.var 1937), .mul (.ext 4) (.var 1955),
      .mul (.ext 5) (.var 1973)])),
    .mul (busSel 2) (.add (.var 12) (.add (sumEx [.mul (.ext 0) (.lit (K.ofBits 4)),
      .mul (.ext 1) (.var 2035), .mul (.ext 2) (.var 3409)]) (.var 1732)))]

/-- What the pull side's tables owe (`bus_table_total[PULL]`). -/
def pullTotalEx : Ex :=
  sumEx [.var 22, pullFwEx, sumEx ((List.range 37).map busSel), .lit 1, pullPadEx]

/-- The loads the pull side reads back: the push side's index values and the memory claims. -/
def pullLoadTab : LoadTab :=
  vtFpwTab ++ [((1852, 1), .var 1931), ((1852, 2), .var 2035), ((13, 0), .var 1937),
    ((13, 1), .var 1955), ((13, 2), .var 1973)]

/-- The guest's pull total, symbolically. -/
noncomputable def pullTotalSym : Ex :=
  (symExec pullLoadTab [] (((vtPre.drop 1505).take 1892).filterMap atomOf)).get 3705

theorem vt_pull_total : pullTotalSym.norm = pullTotalEx.norm := by decide +kernel

/-- The owners of the count side's blocks. -/
def countOwners : List ℕ :=
  [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

/-- The count side's padding mass, block by block: a count block's form at its padding row is
its count there. -/
def countPadEx : Ex :=
  sumEx ((List.range 28).map fun j => .mul (.mul (busSel (37 + j))
    (.var (1739 + 14 * countOwners.getD j 0)))
    (.add (.lit (padK (countOwners.getD j 0) (vtCountCols.flatten.getD j 0))) (.lit 1)))

/-- What the count side's tables owe (`bus_table_total[COUNT]`). -/
def countTotalEx : Ex :=
  sumEx [.var 23, sumEx ((List.range 28).map fun j => busSel (37 + j)), .lit 1, countPadEx]

/-- The guest's count total, symbolically. -/
noncomputable def countTotalSym : Ex :=
  (symExec [] [] (((vtPre.drop 3397).take 876).filterMap atomOf)).get 4553

theorem vt_count_total : countTotalSym.norm = countTotalEx.norm := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
