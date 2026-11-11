/-
  LeanVM.Guest.B1.VerifySub.H.TermCB

  `check_opening_terminal` as `verify_sub`'s thirteenth callee on an honest child, within a bound.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.B1.Terminal.TermCompleteB

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- The terminal's bound (`check_opening_terminal_completeAtB`'s). -/
def termBound (fs : String → ℕ) (Beqc K15 Bcs Brs : ℕ) : ℕ :=
  fs "check_opening_terminal" + 146 + 3 * Beqc + (32 * K15 + fs "__loop14") +
    (fs "selector_tables" + 512) + 101 * Bcs + (fs "ring_switch_weight" + 2240 + Brs)

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal is complete on an honest child within `termBound`**, entered on what
`certify_placement` and `open_stacked` return, its pure callees' words by hypotheses. -/
theorem term_completeB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ) (bs : List ℕ) (sqE : ℕ)
    (hwl : S.w.point.length = S.μs) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 12 noKid pv).taken = true)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs "__loop14")
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs) :
    CompleteAtB fs cert κ ((S.kids bs sqE).getD 12 noKid pv).f
      ((S.kids bs sqE).getD 12 noKid pv).Lin ((S.kids bs sqE).getD 12 noKid pv).args
      ((S.kids bs sqE).getD 12 noKid pv).Out (termBound fs Beqc K15 Bcs Brs) :=
  term_via hbl S bs sqE hwl pv ht (fun f L a O ↦ CompleteAtB fs cert κ f L a O _)
    fun _ B hpre hreg ↦
      check_opening_terminal_completeAtB κ (by omega) B _ (nc := S.H.n) (S.H_n_le40 hbl) rfl hpre
        hreg (S.bus_point_le34 hbl) (S.fin hbl) hEqc hL15 hCsF hrs

end
end LeanVM.Guest.B1.VerifySub
