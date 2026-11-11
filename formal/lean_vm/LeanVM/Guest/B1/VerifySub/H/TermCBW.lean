/-
  LeanVM.Guest.B1.VerifySub.H.TermCBW

  `check_opening_terminal` as `verify_sub`'s thirteenth callee on an honest child, within a bound,
  by a tree within its weights.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermCB
public import LeanVM.Guest.B1.Terminal.TermWeight

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal is complete on an honest child within `termBound`, by a tree within its
weights** (`term_via` by `check_opening_terminal_completeAtBW`). -/
theorem term_completeBW {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ) (bs : List ℕ) (sqE : ℕ)
    (hwl : S.w.point.length = S.μs) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 12 noKid pv).taken = true)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs "__loop14")
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs)
    {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "__loop14" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs "__loop14") → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ω i) ≤ Wrsw i) :
    CompleteAtDTB fs cert κ ((S.kids bs sqE).getD 12 noKid pv).f
      ((S.kids bs sqE).getD 12 noKid pv).Lin ((S.kids bs sqE).getD 12 noKid pv).args
      ((S.kids bs sqE).getD 12 noKid pv).Out
      (fun t => ∀ i, Budget.WeighsLe coreProgram (ω i)
        (ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum) t)
      (termBound fs Beqc K15 Bcs Brs) :=
  term_via hbl S bs sqE hwl pv ht (fun f L a O ↦ CompleteAtDTB fs cert κ f L a O _ _)
    fun _ B hpre hreg ↦
      check_opening_terminal_completeAtBW κ (by omega) B _ (nc := S.H.n) (S.H_n_le40 hbl) rfl hpre
        hreg (S.bus_point_le34 hbl) (S.fin hbl) hEqc hL15 hCsF hrs ω Weqc W15 Wst Wcs Wrsw hEqcW
        hStW hCsW h15W hrswW

end
end LeanVM.Guest.B1.VerifySub
