/-
  LeanVM.Guest.B1.Place.OsMeanB

  open_stacked's named callees, placed within their words bounds.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.Budget.LiftB

/-!
# The named callees within their bounds

`kindDB`: a named callee whose trees total at most `Bnd f` words (`TotalLe`, from
`OsLeafBounds`) is complete placed on its meaning and regions within that bound (G7's
`completeRelRegDB_of_iff`; `opening_fold_round` by its placed statement, `ofr_completeRelRegDB`).
`os_kid_namedB`: a named call of a flat body proved at `osCR` on every memory holding `Lk` is
`CompleteAtB` on `Lk` within its bound.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **`opening_fold_round`, placed on its meaning within a bound**, from its placed statement. -/
theorem ofr_completeRelRegDB {name : String} {b B : ℕ} (h : OfrAtO fs cert κ name b (some B))
    (hb : TotalLe coreProgram fs name (fun _ ↦ B)) :
    CompleteRelRegDB fs cert κ name (OsKind.ofr b).Pre (RegPtrs (OsKind.ofr b).spec) (fun _ ↦ B) := by
  intro args rets Lin hreg hpre
  refine CompleteAtB.toDTB ?_
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  · obtain ⟨rd0, hl0, hm0⟩ := hex
    obtain ⟨hcan, hm⟩ := hpre rd0 hl0 hm0
    exact (h Lin args rets (meaningFoldRound_length hm) hcan hreg (fun rd hl hm ↦ (hpre rd hl hm).2)
      (fun B' hB' ↦ by cases hB'; exact hb)).toB
  · exact fun fp ↦ ⟨0, [], rets, [], ⟨rfl, rfl⟩, fun q hq ↦ by simp at hq, disj_nil, Nat.zero_le _,
      fun rd hl hm ↦ (hex ⟨rd, hl, by simpa using hm⟩).elim⟩

/-- **A named callee is complete placed on its meaning and regions, within its bound.** -/
theorem kindDB {Bnd : String → ℕ} {f : String} (hb : TotalLe coreProgram fs f (fun _ ↦ Bnd f))
    (hofr : ∀ e ∈ ofrTable, ∀ Bd, OfrAtO fs cert κ e.1 e.2 Bd) {K : OsKind}
    (hK : osKindOf f = some K) :
    CompleteRelRegDB fs cert κ f K.Pre (RegPtrs K.spec) (fun _ ↦ Bnd f) := by
  have hm := os_mem_of_lookup osKindTable hK
  simp only [osKindTable, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rcases hm with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) |
    ⟨p, hp, rfl, rfl⟩
  · exact completeRelRegDB_of_iff (leafSpecOk_of fold_leafSpec) opening_fold_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of canonical_leafSpec) assert_canonical_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of grind_leafSpec) grind_check_holds κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of rowWeights4_leafSpec)
      opening_row_weights_holds.2 κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_of rowWeights6_leafSpec)
      opening_row_weights_holds.1 κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all ood_leafSpec p hp)
      (opening_ood_point_all_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all finalMsg_leafSpec p hp)
      (opening_final_message_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all merkleCap_leafSpec p hp)
      (verify_merkle_cap_holds p hp) κ hb
  · exact completeRelRegDB_of_iff (leafSpecOk_all foldFinal_leafSpec p hp)
      (fold_final_msg_holds p hp) κ hb
  · exact ofr_completeRelRegDB (hofr p hp (some _)) hb

/-- **A named call of a flat body proved at `osCR` on every memory holding `Lk`** is complete
placed on `Lk` within its bound. -/
theorem os_kid_namedB {Bnd : String → ℕ} (hofr : ∀ e ∈ ofrTable, ∀ Bd, OfrAtO fs cert κ e.1 e.2 Bd)
    {Lk : Layout} {σ : Val} {pre : List Stmt} {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
    (hdo : ∀ s ∈ pre, DispOk σ s) (hfl : DispShort pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) (hb : TotalLe coreProgram fs c.f (fun _ ↦ Bnd c.f))
    (hR : ∀ b, K = .ofr b → RegPtrs K.spec (c.args.map σ) (RegionL Lk)) :
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bnd c.f) := by
  have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c.args.map σ) (c.rets.map σ) ∧
      OsXOk κ Lk K (c.args.map σ) := fun rd hl hm ↦ by
    have h := os_calls_of_allOkF (hall rd hl hm) hdo hfl c hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have hreg := kind_region (fun n hn ↦ osKindOf_ood_pos (hn ▸ hK)) ⟨rd0, hl0, hm0⟩
    (fun rd hl hm ↦ (hpre rd hl hm).1) (hpre rd0 hl0 hm0).2 hR
  have h := kindDB (cert := cert) (κ := κ) hb hofr hK _ _ Lk hreg fun rd hl hm ↦ (hpre rd hl hm).1
  intro fp
  obtain ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  exact ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm ↦ (hr rd hl hm).relAtIn⟩

end
end LeanVM.Guest.B1
