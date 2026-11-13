/-
  LeanVM.Guest.B2C.ChainDefs

  The chained `match`es' static check (`B2C/Chain.lean` proves it sound), apart from the proofs
  on function `j`'s data: the checks of `ChainCheck.lean` (`chainFn_eq`, `chainWin_eq`, by `rfl`).
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.Share
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.B2C.ChainCheck

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-- The fixed, temporaries', runs', call sites' and `match` targets' cells of function `j`. -/
noncomputable def fixedBits (j : ℕ) : ℕ :=
  bitsOf ((plumbOf j).stat.map Prod.fst ++ (plumbOf j).tmps.map Prod.snd ++
    (plumbOf j).runs.map Prod.snd ++ siteCells (plumbOf j) ++ (plumbOf j).arms.map (·.2.1))

/-- **The chains' static check of function `j`.** -/
noncomputable def chainFn (j : ℕ) : Bool :=
  chainsPw (plumbOf j).chains &&
  (plumbOf j).chains.all fun ch ↦
    ch.2.2.1.all (fun t ↦ !(fixedBits j).testBit t) && Nat.ble ch.2.2.1.length 65536 &&
    match (coreOf j).body[ch.1]?, (coreOf j).body[ch.1 + 1]? with
    | some (.match_ x arms), some (.match_ y arms') =>
      decide (x = V.n ch.2.1) && decide (y = V.n ch.2.2.2.1) && Nat.beq arms.length ch.2.2.1.length &&
        (List.range arms'.length).all fun e ↦ (glob.jt.get (ch.2.2.2.2 + e)).isSome
    | _, _ => false

/-- **The chains' check of window `i` of function `j`.** -/
noncomputable def chainWin (j i : ℕ) : Bool :=
  (plumbOf j).chains.isEmpty ||
  ((listElementOrDefault (certOf j).cells i []).all (fun c ↦ Nat.blt c 65536) &&
    natSeq (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))) fun F ↦ (clocW (certOf j) i).seq fun loc ↦
      (bif Nat.beq i 0 then avoidL loc F (coreOf j).params else true) &&
      chainStmts (plumbOf j).chains loc F ((certOf j).cutAt i).start ((certOf j).stmtsAt (coreOf j) i))

/-- **The chains' checks of function `j`.** -/
def ChainOk (j : ℕ) : Prop := chainFn j = true ∧ ∀ i ≤ (certOf j).cuts.length, chainWin j i = true

/-- A function without chains passes. -/
theorem chainOk_of_nil {j : ℕ} (h : (plumbOf j).chains.isEmpty = true) : ChainOk j := by
  have h' : (plumbOf j).chains = [] := List.isEmpty_iff.mp h
  refine ⟨?_, fun i _ ↦ ?_⟩
  · simp [chainFn, h', chainsPw]
  · simp [chainWin, h']

theorem chainFn_eq (j : ℕ) : chainFn j = chainFnD glob.jt (plumbOf j) (coreOf j) := rfl

theorem chainWin_eq (j i : ℕ) : chainWin j i = chainWinD (plumbOf j) (coreOf j) (certOf j) i := rfl

end
end LeanVM.Guest.B2C
