/-
  LeanVM.Prover.Complete.Link.Fields

  `LinkCore`'s `rowStart` and `columns` from their identities alone, their shapes discharged.
-/

module

public import LeanVM.Prover.Complete.Link.ColumnShape

/-!
# Two of `LinkCore`'s fields, from their identities

`linkCore_rowStart`: `LinkCore.rowStart` on the honest witness from `RowIdentity` (the index
side's value at `r` is the rows' claim), the rows' shape being `rowOK_linkRowStart`.
`linkCore_columns`: `LinkCore.columns` from `ColumnSplit` (the bound rows' claim is the pointer
columns' cube sum), their count and shape being `length_linkColumns`, `tabs_columnProds`,
`termsLE_columnProds`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- **The row side's identity**: the index side's value at `r` is the rows' claim. -/
def RowIdentity (W : Witness) : Prop :=
  ∀ y x, HonestPre W y x → x.index.value = rowClaim (linkRowStart W x)

/-- **The pointer columns' split**: the bound rows' claim is the pointer columns' cube sum. -/
def ColumnSplit (W : Witness) : Prop :=
  ∀ y x, HonestPre W y x → ∀ chi : List E, chi.length = linkNRows W →
    let st := chi.foldl rowFold (linkRowStart W x)
    rowClaim st = cubeSum (2 ^ log2Ceil (linkColumns W x chi st).length)
      (linkColumnProds W x chi st)

theorem linkCore_rowStart {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (h : RowIdentity W) :
    ∀ y x, HonestPre W y x →
      RowOK (roundCoefficients W.chunks.d).1 (linkRowStart W x) ∧
        x.index.value = rowClaim (linkRowStart W x) :=
  fun y x hp ↦ ⟨rowOK_linkRowStart hW x ⟨y.theta0, y.drawn, hp.drawn, hp.ch⟩, h y x hp⟩

theorem linkCore_columns {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (h : ColumnSplit W) :
    ∀ y x, HonestPre W y x → ∀ chi : List E, chi.length = linkNRows W →
      let st := chi.foldl rowFold (linkRowStart W x)
      (linkColumns W x chi st).length = linkNPointers W.layout ∧
        Tabs (log2Ceil (linkColumns W x chi st).length) (linkColumnProds W x chi st) ∧
        (∀ cf ∈ (linkColumnProds W x chi st).terms,
          cf.2.size + 1 ≤ (roundCoefficients W.chunks.d).2) ∧
        rowClaim st = cubeSum (2 ^ log2Ceil (linkColumns W x chi st).length)
          (linkColumnProds W x chi st) := by
  intro y x hp chi hchi
  obtain ⟨htab, hch, -, -⟩ := linkSizes hW
  exact ⟨length_linkColumns W htab x chi _, tabs_columnProds _ _ _ _ _ _,
    termsLE_columnProds _ _ (one_le_d hch) _ _ _ _, h y x hp chi hchi⟩

end LeanVM.Prover.Complete

end
