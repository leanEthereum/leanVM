/-
  LeanVM.Prover.Complete.Link.Open

  The link's four open arithmetic facts, each a proposition, and `LinkCore` from them.
-/

module

public import LeanVM.Prover.Complete.Link.Fields
public import LeanVM.Prover.Complete.Link.Core

/-!
# The link's open facts

`LinkCore W` (`Core.lean`) with its structural halves proved (`Fields.lean`) leaves four identities
of Hotwire's link on the honest witness:

* `LinkIndexIdentity W`: the index side's cube sum is `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin` (the state
  chain telescopes, the memory and program lookups balance);
* `RowIdentity W` (`Fields.lean`): the row side's sum at the index point is the index summand there;
* `ColumnSplit W` (`Fields.lean`): the bound rows split into the pointer columns' terms and the base;
* `LinkTailHolds W`: the terminal check passes on the honest message, and what the link returns
  holds (`LinkOut`).

`linkCore_of`: they give `LinkCore W`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- **The index side's identity** (`LinkCore.index`). -/
def LinkIndexIdentity (W : Witness) : Prop :=
  ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    let ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
    linkEqAt ch.zeta 0 * (1 + ch.gammaState.getD 0 0 * 1 + ch.gammaState.getD 1 0 * 1) +
      linkEqAt ch.zeta (W.layout.tableRows.foldl (· + ·) 0) *
        (1 + ch.gammaState.getD 0 0 * gpow (2 ^ W.layout.logBytecode - 1) +
          ch.gammaState.getD 1 0 * 1) =
      cubeSum (2 ^ W.chunks.width) (indexProds W ch)

/-- **The terminal check and the link's end** (`LinkCore.tail`). -/
def LinkTailHolds (W : Witness) : Prop :=
  ∀ y x, HonestPre W y x → ∀ chi qPoint : List E, chi.length = linkNRows W →
    qPoint.length = log2Ceil (linkNPointers W.layout) →
    let st := chi.foldl rowFold (linkRowStart W x)
    ∃ e, linkTail W.layout y (honestProgramSide W y) chi qPoint
        (qPoint.foldl Prods.fold (linkColumnProds W x chi st)).value
        (linkMessage W x chi qPoint st) = .ret e ∧ LinkOut W e

/-- **`LinkCore` from the four identities.** -/
theorem linkCore_of {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hi : LinkIndexIdentity W)
    (hr : RowIdentity W) (hc : ColumnSplit W) (ht : LinkTailHolds W) : LinkCore W :=
  ⟨hi, linkCore_rowStart hW hr, linkCore_columns hW hc, ht⟩

end LeanVM.Prover.Complete

end
