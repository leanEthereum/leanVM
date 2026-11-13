/-
  LeanVM.Protocol.Verifier.Phases

  The verifier's phases in normal form: each phase's spec lemma, which the proofs about the phase
  rewrite with instead of unfolding it.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# The phases, in normal form

`readAnnouncedSizes` (step 1) reads `2 + tables.length` scalars and then only checks them:
`readAnnouncedSizes_eq` is `readScalars` followed by `liftOption (sizesOf bytecode ·)`, by `simp`
from the statement's definition, and `sizesOf_spec` is what a value it returns satisfies. The
proofs about the phase (`allRet_readSizes`, `readSizes_bytecode`, `costs_readSizes`,
`moves_readSizes_le`, `readSizes_ret`, `readSizesPure`) rewrite with the first and read the
second, so a change to the phase's checks changes `sizesOf` and this module only.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile

@[expose] public section

theorem ret_eq_liftOption {α : Type} (a : α) : VerifierProgram.ret a = liftOption (some a) := rfl

theorem require_bind_liftOption {α : Type} (c : Prop) [Decidable c] (o : Option α) :
    (VerifierProgram.require c).bind (fun _ ↦ liftOption o) = liftOption (if c then o else none) := by
  by_cases h : c <;> simp only [VerifierProgram.require, h, ↓reduceIte] <;> rfl

theorem liftOption_bind_liftOption {α β : Type} (o : Option α) (g : α → Option β) :
    (liftOption o).bind (fun a ↦ liftOption (g a)) = liftOption (o.bind g) := by
  cases o <;> rfl

/-! ## Step 1: the announced sizes -/

/-- **What `readAnnouncedSizes` makes of the scalars it read**: its checks, in its order, and the
layout and rate it returns. -/
def sizesOf (bytecode : List K) (announced : List E) : Option (Layout × ℕ) :=
  if (announced.all fun value ↦ value.limb 1 = 0) then
    let logMemory := kToNat ((announced.headD 0).limb 0)
    let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
    let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
    if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
      (buildLayout bytecode logMemory tableRows).bind fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some (layout, logInverseRate)
        else none
    else none
  else none

/-- **`readAnnouncedSizes`, normal form**: its reads, then its checks (`sizesOf`). -/
theorem readAnnouncedSizes_eq (bytecode : List K) :
    readAnnouncedSizes bytecode = VerifierProgram.readScalars (2 + tables.length) >>= fun announced ↦
      liftOption (sizesOf bytecode announced) := by
  simp only [readAnnouncedSizes, VerifierProgram.bind_eq, VerifierProgram.pure_eq, ret_eq_liftOption,
    require_bind_liftOption, liftOption_bind_liftOption]
  rfl

/-- What a value `readAnnouncedSizes` returns satisfies, of the scalars it read. -/
structure SizesSpec (bytecode : List K) (announced : List E) (x : Layout × ℕ) : Prop where
  limbs : announced.all fun value ↦ value.limb 1 = 0
  rate_ge : 1 ≤ x.2
  rate_le : x.2 ≤ 4
  rate : x.2 = kToNat ((announced.getLastD 0).limb 0)
  layout : buildLayout bytecode (kToNat ((announced.headD 0).limb 0))
    (((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)) = some x.1
  stack_ge : Whir.minLogStack ≤ x.1.stackLog
  stack_le : x.1.stackLog ≤ Whir.maxLogStack

theorem sizesOf_spec {bytecode : List K} {announced : List E} {x : Layout × ℕ}
    (h : sizesOf bytecode announced = some x) : SizesSpec bytecode announced x := by
  simp only [sizesOf, Option.ite_none_right_eq_some, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨h1, h2, layout, hb, h3, rfl⟩ := h
  exact ⟨h1, h2.1, h2.2, rfl, hb, h3.1, h3.2⟩

end
end LeanVM.Protocol.Verifier
