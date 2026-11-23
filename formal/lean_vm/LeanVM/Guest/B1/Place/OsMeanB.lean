/-
  LeanVM.Guest.B1.Place.OsMeanB

  open_stacked's named callees placed within their words bounds.
-/

module

public import LeanVM.Guest.B1.Place.OsSpec
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.Budget.LiftB
public import LeanVM.Guest.Budget.Bounded

/-!
# The named callees within their bounds

**`kindDB`**: a named callee whose valid trees total at most `B` words (`TotalLe`) is complete
placed on its meaning and regions within `B`, by `completeRelRegDB_of_iff`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-! ## The named callees within their bounds -/

/-- **A named callee is complete placed on its meaning and regions, within its bound.** -/
theorem kindDB {B : ℕ} {f : String} (hb : TotalLe coreProgram fs f (fun _ ↦ B))
    {K : OsKind} (hK : osKindOf f = some K) :
    CompleteRelRegDB fs cert κ f K.Pre (RegPtrs K.spec) (fun _ ↦ B) := by
  have he := osKindEntry_ok hK
  cases K with
  | tail =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he
    exact completeRelRegDB_of_iff (leafSpecOk_of tail_leafSpec) opening_tail_round_holds κ hb
  | msg n nonce =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact completeRelRegDB_of_iff (leafSpecOk_allP msg_leafSpec _ hm) (opening_message_holds _ hm)
      κ hb
  | spf n =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact completeRelRegDB_of_iff (leafSpecOk_allP spf_leafSpec _ hm)
      (squeeze_point_from_holds _ hm) κ hb
  | cap d =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact completeRelRegDB_of_iff (leafSpecOk_all merkleCap_leafSpec _ he)
      (verify_merkle_cap_holds _ he) κ hb
  | ffm n =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact completeRelRegDB_of_iff (leafSpecOk_all foldFinal_leafSpec _ he)
      (fold_final_msg_holds _ he) κ hb
  | iz =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he
    exact completeRelRegDB_of_iff iz_leafSpec (fun rd a r ↦ is_zero_iff rd a r) κ hb

end
end LeanVM.Guest.B1
