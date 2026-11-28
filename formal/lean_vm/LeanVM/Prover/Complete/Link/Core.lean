/-
  LeanVM.Prover.Complete.Link.Core

  `LinkWins` from the link's arithmetic on the honest witness alone: the sizes, the index side's
  shape and the message's length discharged.
-/

module

public import LeanVM.Prover.Complete.Link.Sizes
public import LeanVM.Prover.Complete.Link.IndexTabs

/-!
# The link's remaining facts

`LinkCore W`: the four facts of `LinkFacts` the sizes do not give, the link's arithmetic on the
honest witness (the index side's identity, the row side's start, the pointer columns, the terminal
check and what the link returns). `linkWins_of_core`: they give `LinkWins`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- **The link's arithmetic on the honest witness**: `LinkFacts`' `index`, `rowStart`, `columns`
and `tail`. -/
structure LinkCore (W : Witness) : Prop where
  index : ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    let ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
    linkEqAt ch.zeta 0 * (1 + ch.gammaState.getD 0 0 * 1 + ch.gammaState.getD 1 0 * 1) +
      linkEqAt ch.zeta (W.layout.tableRows.foldl (· + ·) 0) *
        (1 + ch.gammaState.getD 0 0 * gpow (2 ^ W.layout.logBytecode - 1) +
          ch.gammaState.getD 1 0 * 1) =
      cubeSum (2 ^ W.chunks.width) (indexProds W ch)
  rowStart : ∀ y x, HonestPre W y x →
    RowOK (roundCoefficients W.chunks.d).1 (linkRowStart W x) ∧
      x.index.value = rowClaim (linkRowStart W x)
  columns : ∀ y x, HonestPre W y x → ∀ chi : List E, chi.length = linkNRows W →
    let st := chi.foldl rowFold (linkRowStart W x)
    (linkColumns W x chi st).length = linkNPointers W.layout ∧
      Tabs (log2Ceil (linkColumns W x chi st).length) (linkColumnProds W x chi st) ∧
      (∀ cf ∈ (linkColumnProds W x chi st).terms,
        cf.2.size + 1 ≤ (roundCoefficients W.chunks.d).2) ∧
      rowClaim st = cubeSum (2 ^ log2Ceil (linkColumns W x chi st).length)
        (linkColumnProds W x chi st)
  tail : ∀ y x, HonestPre W y x → ∀ chi qPoint : List E, chi.length = linkNRows W →
    qPoint.length = log2Ceil (linkNPointers W.layout) →
    let st := chi.foldl rowFold (linkRowStart W x)
    ∃ e, linkTail W.layout y (honestProgramSide W y) chi qPoint
        (qPoint.foldl Prods.fold (linkColumnProds W x chi st)).value
        (linkMessage W x chi qPoint st) = .ret e ∧ LinkOut W e

/-- The facts, from the honest witness and its arithmetic. -/
theorem linkFacts_of {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) (h : LinkCore W) : LinkFacts W := by
  obtain ⟨htab, hch, hnr, hbc⟩ := linkSizes hW
  exact ⟨htab, hch, hnr, hbc, fun θ drawn hlen ↦ indexTabs_of W θ drawn hlen, h.index, h.rowStart,
    h.columns, fun _ x _ chi qPoint ↦ linkMessage_length W htab x chi qPoint _, h.tail⟩

/-- **`LinkWins`** from the link's arithmetic on every admitted execution's witness. -/
theorem linkWins_of_core
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Witness), Admitted prog input t ρ W → LinkCore W) : LinkWins :=
  linkWins_of_facts fun prog input t ρ W hA ↦ linkFacts_of hA.witness (h prog input t ρ W hA)

end LeanVM.Prover.Complete

end
