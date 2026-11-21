/-
  LeanVM.Core.Memory.LoopPre

  A loop helper's arguments from a start below its end, for its words bound (`TotalLeOn`).
-/

module

public import LeanVM.Core.Memory.SizeTotal
public import LeanVM.Core.Value.Bits

namespace LeanVM.Core.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core.Value

@[expose] public section

/-- **A loop helper's arguments from a start below its end**: the counter `g^a`, the end `g^e`,
`a < e` below the order of `g`. -/
def LoopPre (args : List E) : Prop :=
  ∃ a e, args.getD 0 0 = ofK (addressOfIndex a) ∧ args.getD 1 0 = ofK (addressOfIndex e) ∧ a < e ∧ e
      < 2 ^ 64 - 1

/-- A loop helper's call from `1` to `gen ^ m`, `0 < m < 2^64 - 1`, satisfies `LoopPre`. -/
theorem loopPre_gen {m : ℕ} (h0 : 0 < m) (hm : m < 2 ^ 64 - 1) (rest : List E) :
    LoopPre ((1 : E) :: LeanVM.Protocol.Verifier.gen ^ m :: rest) :=
  ⟨0, m, by simp [Parameters.addressOfIndex], by simp [gen_pow_eq_ofK], h0, hm⟩

end
end LeanVM.Core.Memory
