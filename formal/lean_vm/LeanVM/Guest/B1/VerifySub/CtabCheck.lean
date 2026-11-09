/-
  LeanVM.Guest.B1.VerifySub.CtabCheck

  `c_table`'s monomials, by kernel evaluation of the pass.
-/

module

public import LeanVM.Guest.B1.VerifySub.CtabPass

/-!
# `c_table`'s monomials

`ctPre`, `c_table`'s section before its call: `ctRun` from nothing records, at every cell `k < 64`
of the table, the exponents `specEV k` of `ringCoefficients`' `k`-th product (challenge `i` with
shift `s_i` contributes `2^(k mod s_i)` when `k` has the bit `s_i`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `c_table`'s section before `ring_switch_target`. -/
def ctPre : List Stmt :=
  [vsConst 766 (word 1 0 0), vsLd 766 665 0] ++ vsStageT 0 32 767 ++ vsStageT 1 16 802 ++
    vsStageT 2 8 839 ++ vsStageT 3 4 880 ++ vsStageT 4 2 929 ++ vsStageT 5 1 994

theorem vsCtabT_eq : vsCtabT = ctPre ++ [vsCall "ring_switch_target" [648, 664] [1091]] := rfl

/-- The exponents of `ringCoefficients`' `k`-th product. -/
def specEV (k : ℕ) : List ℕ :=
  (List.range 6).map fun i ↦
    if k &&& ringMapShifts.getD i 0 ≠ 0 then 2 ^ (k % ringMapShifts.getD i 0) else 0

/-- **The pass on `c_table`** records `specEV k` at every cell `k < 64`. -/
theorem ct_check : (ctRun ⟨[], []⟩ ctPre).map (fun st ↦
    (List.range 64).all fun k ↦ st.mem.lookup k == some (specEV k)) = some true := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
