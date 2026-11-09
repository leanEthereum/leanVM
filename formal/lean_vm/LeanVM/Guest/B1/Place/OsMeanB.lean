/-
  LeanVM.Guest.B1.Place.OsMeanB

  open_stacked's named callees, placed within their words bounds.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.Budget.LiftB

/-!
# The named callees within their bounds

`OsLeafBounds fs Bnd`: each named callee `f`'s trees total at most `Bnd f` words (G7-cnt's
certificates give it). `OsCalleesRegD.kindDB`: a named callee is complete placed on its meaning and
regions within that bound (G7's `completeRelRegDB_of_iff`). `os_kid_namedB`: a named call of a body
proved at `osCR` on every memory holding `Lk` is `CompleteAtB` on `Lk` within its bound.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **The named callees' words bounds**, fs-generic: callee `f`'s trees total at most `Bnd f`
words. -/
def OsLeafBounds (fs : String → ℕ) (Bnd : String → ℕ) : Prop :=
  ∀ f K, osKindOf f = some K → TotalLe coreProgram fs f (fun _ ↦ Bnd f)

/-- **A named callee is complete placed on its meaning and regions, within its bound.** -/
theorem kindDB {Bnd : String → ℕ} (hT : OsLeafBounds fs Bnd) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) :
    CompleteRelRegDB fs cert κ f K.Pre (RegPtrs K.spec) (fun _ ↦ Bnd f) := by
  have hb := hT f K hK
  have hm := os_mem_of_lookup osKindTable hK
  simp only [osKindTable, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩
  · exact completeRelRegDB_of_iff (leafSpecOk_of fold_leafSpec) opening_fold_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of canonical_leafSpec) assert_canonical_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of grind_leafSpec) grind_check_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of rowWeights4_leafSpec)
      opening_row_weights_holds.2 κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of rowWeights6_leafSpec)
      opening_row_weights_holds.1 κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all ood_leafSpec p hp)
      (opening_ood_point_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all finalMsg_leafSpec p hp)
      (opening_final_message_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all merkleCap_leafSpec p hp)
      (verify_merkle_cap_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all foldFinal_leafSpec p hp)
      (fold_final_msg_holds p hp) κ hb

/-- **A named call of a body proved at `osCR` on every memory holding `Lk`** is complete placed on
`Lk` within its bound. -/
theorem os_kid_namedB {Bnd : String → ℕ} (hT : OsLeafBounds fs Bnd) {Lk : Layout}
    {σ : Val} {pre : List Stmt} {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) :
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bnd c.f) := by
  have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c.args.map σ) (c.rets.map σ) ∧
      OsXOk κ Lk K (c.args.map σ) := fun rd hl hm ↦ by
    have h := os_calls_of_allOk (hall rd hl hm) c hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have hfix := kind_fixed (fun n hn ↦ osKindOf_ood_pos (hn ▸ hK)) ⟨rd0, hl0, hm0⟩
    (fun rd hl hm ↦ (hpre rd hl hm).1) (hpre rd0 hl0 hm0).2
  have h := kindDB (cert := cert) (κ := κ) hT hK _ _ Lk (fixedReads_region hfix ⟨rd0, hl0, hm0⟩)
    fun rd hl hm ↦ (hpre rd hl hm).1
  intro fp
  obtain ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  exact ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm ↦ (hr rd hl hm).relAtIn⟩

end
end LeanVM.Guest.B1
