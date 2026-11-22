module

public import Statement.LeanIsa

/-!
# Two runs that step alike

`SameSteps prog M rd n r`: along `n` steps of the run on `M` from `r`, each step reads the same
on `rd` as on `M`. Two memories whose runs step alike count the same instructions
(`opcodeCountInRun_congr`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- Along `n` steps of the run on `M` from `r`, each step reads the same on `rd` as on `M`. -/
def SameSteps {κ : ℕ} (prog : LeanIsaProgram) (M : MemoryImage κ) (rd : K → Option E) :
    ℕ → Registers K → Prop
  | 0, _ => True
  | n + 1, r => (prog.fetch r.pc >>= executeWith rd r) = step prog M r ∧
      ∀ r', step prog M r = some r' → SameSteps prog M rd n r'

/-- Runs that step alike count the same instructions. -/
theorem opcodeCountInRun_congr {κ κ' : ℕ} {prog : LeanIsaProgram} {M : MemoryImage κ}
    {M' : MemoryImage κ'} (op : Opcode) :
    ∀ (n : ℕ) (r : Registers K), SameSteps prog M M'.read n r →
      opcodeCountInRun prog M' op n r = opcodeCountInRun prog M op n r
  | 0, _, _ => rfl
  | n + 1, r, ⟨h1, h2⟩ => by
    have hs : step prog M' r = step prog M r := h1
    rw [opcodeCountInRun, opcodeCountInRun, hs]
    cases prog.fetch r.pc with
    | none => rfl
    | some ins =>
      cases hst : step prog M r with
      | none => rfl
      | some r' => exact congrArg _ (opcodeCountInRun_congr op n r' (h2 r' hst))

end

end LeanVM.Prover.Exec
