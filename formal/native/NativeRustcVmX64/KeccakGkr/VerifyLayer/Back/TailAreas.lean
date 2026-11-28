module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.State

/-! # The transpose's scratch regions and read-only permutation table -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm (Region)

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem transpose_areas (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    {d : MachineData} (hb : Body m0 W 16 d) :
    Areas d linearTransposeStack
      [⟨sA m0 + BitVec.ofNat 64 76800, 25600⟩, ⟨sA m0 + BitVec.ofNat 64 102400, 5120⟩,
        ⟨sA m0 + BitVec.ofNat 64 25600, 25600⟩]
      [⟨sA m0 + BitVec.ofNat 64 51200, 25600⟩, rhoRegion] := by
  have g := geo_of hpre
  have hA := pre_areas hpre
  have hm : rhoRegion ∈ [a.region, rcRegion, projectRegion, rhoRegion] := by simp
  have hrok := hA.1 _ (List.mem_append.mpr (.inr hm))
  have h0 := hA.2.2 _ List.mem_cons_self _ hm
  have h3 := hA.2.2 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩
    (by simp [NativeRustcVm.KeccakGkr.scratchBytes]) _ hm
  have hN := g.hN
  have hss := g.hss
  have hs := g.hs
  have htop := g.top
  have hsp : (rspOf d).toNat = (rspOf m0).toNat - 2016 + 16 := by
    rw [hb.fr.sp]
    exact g.fa (by decide)
  have hlt : linearTransposeStack = 64 := by decide
  have hst : (stackBelow d linearTransposeStack).toNat = (rspOf m0).toNat - 2064 := by
    rw [hlt, stackBelow_toNat (by omega), hsp]
    omega
  have hrw := hrok.2
  unfold NativeRustcVm.NoWrap at hrw
  unfold NativeRustcVm.Apart at h0 h3
  simp only [stackRegion, NativeRustcVm.KeccakGkr.scratchBytes, rhoRegion] at h0 h3 hrw
  rw [g.sbN] at h0
  have e1 := g.sa (o := 76800) (by decide)
  have e2 := g.sa (o := 102400) (by decide)
  have e3 := g.sa (o := 25600) (by decide)
  have e4 := g.sa (o := 51200) (by decide)
  have hsub : ∀ o n, 0 < n → o + n ≤ 205824 →
      Region.Ok d.dmem ⟨sA m0 + BitVec.ofNat 64 o, n⟩ := by
    intro o n hn hon
    exact scrOk hpre hb (by omega) hon
  refine ⟨fun r hr ↦ ?_, ?_, fun w hw r hr ↦ ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact ⟨fun i hi ↦ hb.fr.kept _ (hrok.1 i hi), hrok.2⟩
  · simp only [stackRegion, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, NativeRustcVm.Disjoint, List.Pairwise.nil,
      List.pairwise_cons, and_true, false_implies, implies_true]
    unfold NativeRustcVm.Apart
    rw [hst, e1, e2, e3, hlt]
    omega
  · simp only [stackRegion, List.mem_cons, List.not_mem_nil, or_false] at hw hr
    unfold NativeRustcVm.Apart
    rcases hr with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      simp only [rhoRegion] <;> (try rw [e4]) <;> (try rw [hst]) <;> (try rw [e1]) <;>
      (try rw [e2]) <;> (try rw [e3]) <;> (try rw [hlt]) <;> omega

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
