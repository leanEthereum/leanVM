/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub`'s sixteen callees on an honest child, each placed within its bound
  (`BoundsB`'s `vsBsAt`).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.WhirLen
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.KeccakGkr.VkCW

/-!
# `verify_sub`'s callees within their bounds

`kidsDepB_of`: callees by position, each within its bound. `vs_kidsDepBAt_of`: on an honest child
(`ChildSegs`), the callees are `KidsDepB` within `vsBsAt W Bvk μ r` at the child's stack log and
rate, given `verify_tables`', `verify_keccak`'s and the terminal's placed completeness on the
child's words (`hvt`, `hvk`, `hterm`); the others from their own theorems (`H/KidsB`, `os_kidB`
from `open_stacked_completeAtB_Spec`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- Callees by position, each within its bound. -/
theorem kidsDepB_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ), ks.length = Bs.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepB fs cert κ ks Bs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: ks, _ :: Bs, hl, h =>
    ⟨h 0 (by simp), kidsDepB_of ks Bs (by simpa using hl) fun j hj ↦ h (j + 1) (by simp; omega)⟩

theorem squeezeName_eq {μ : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) :
    squeezeNames.getD (μ - 22) "" = spfName μ := by
  interval_cases μ <;> rfl

theorem busGrindName_eq (d : ℕ) : busGrindNames.getD d "" = busGrindName d := rfl

theorem squeezeName_mem {μ : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) :
    squeezeNames.getD (μ - 22) "" ∈ squeezeNames := by
  interval_cases μ <;> decide

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 → (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_cap_length n s.squeeze.2 (by simp [Fs.squeeze, capOf])

theorem mem_st15 : "grind_check__L15" ∈ vsStaticS := by simp [vsStaticS]
theorem mem_st14 : "grind_check__L14" ∈ vsStaticS := by simp [vsStaticS]
theorem mem_stOm : "opening_message__L1_L1" ∈ vsStaticS := by simp [vsStaticS]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- `opening_message__L1_L1` on the honest child. -/
theorem om_kid (κ : ℕ) (W : VsWordsOs fs) (bs : List ℕ) :
    CompleteAtB fs cert κ "opening_message__L1_L1"
      [(vb bs 1 + 11, [S.oodV, S.busN]), (vb bs 7, [S.oodV])]
      (S.sZ.cap ++ [ptr (vb bs 1) * gen ^ 11, ptr (vb bs 7)])
      (Returns ([cellsOfState S.busSt false 0, cellsOfState S.busSt false 1] ++ capOf S.busSt ++
        [ptr (vb bs 1) * gen ^ 11 * gen ^ 2])) (W.Kst "opening_message__L1_L1") :=
  om_kidB κ (W.hst _ mem_stOm) S.sZ.cap (squeezeN_cap_length _ _ (by simp [capOf])) S.oodV S.busN
    (vb bs 1) (vb bs 7)

/-- `squeeze_point_from` on the honest child, at its stack log's arm. -/
theorem spf_kid (κ : ℕ) (W : VsWordsOs fs) (bs : List ℕ) :
    CompleteAtB fs cert κ (squeezeNames.getD (S.μs - 22) "") [(vb bs 6, S.oodZ)]
      (capOf S.oodSt ++ [challengeOf S.oodSt, ptr (vb bs 6)]) (Returns S.sZ.cap)
      (armMax W.Kst squeezeNames) := by
  have hμ1 : 22 ≤ S.μs := S.hmu22
  have hμ2 : S.μs ≤ 28 := S.hmu28
  have hm := squeezeName_mem hμ1 hμ2
  have e := squeezeName_eq hμ1 hμ2
  have hT : TotalLe coreProgram fs (spfName S.μs) fun _ ↦ W.Kst (squeezeNames.getD (S.μs - 22) "") := by
    rw [← e]; exact W.hst _ (List.mem_append_left _ (List.mem_append_right _ hm))
  have h := spf_kidB (cert := cert) (n := S.μs) (List.mem_map.2 ⟨S.μs - 6, List.mem_range.2 (by omega), by omega⟩) κ hT S.oodSt (vb bs 6)
  rw [← e] at h
  exact h.mono le_rfl (le_armMax W.Kst hm)

/-- The bus grind's arm on the honest child. -/
theorem busGrind_kid (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 11 ≤ κ) (sqE : ℕ) :
    CompleteAtB fs cert κ (busGrindNames.getD (S.d - 16) "") (vsExpLin sqE)
      [cellsOfState S.busSt false 1, ptr sqE * gen ^ winTabAt] (Returns [0]) (busGrindMax fs) := by
  have hd := S.d_bounds hbl
  rw [busGrindName_eq]
  exact (busGrind_kidB (d := S.d - 16) (List.mem_range.2 (by omega)) hκ sqE
    (S.busPow hbl)).mono le_rfl (le_busGrindMax (by omega))

theorem sZ_cap_length : S.sZ.cap.length = 5 := squeezeN_cap_length _ _ (by simp [capOf])

end ChildSegs

/-- **`verify_sub`'s callees on an honest child, each within its bound**, given `verify_tables`',
`verify_keccak`'s and the terminal's. -/
theorem vs_kidsDepBAt_of {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs fs) (Bvk : ℕ) (hos : open_stacked_completeAtB_Spec)
    (bs : List ℕ) (sqE : ℕ) (hsl : S.kc.2.2.length = 64)
    (hvt : ∀ pv, CompleteAtB fs cert κ "verify_tables" ((S.kids bs sqE).getD 10 noKid pv).Lin
      ((S.kids bs sqE).getD 10 noKid pv).args ((S.kids bs sqE).getD 10 noKid pv).Out
      (vtMax fs W.Kf W.Ksh W.K10))
    (hvk : CompleteAtB fs cert κ "verify_keccak" ((S.kids bs sqE).getD 11 noKid []).Lin
      ((S.kids bs sqE).getD 11 noKid []).args ((S.kids bs sqE).getD 11 noKid []).Out Bvk)
    (hterm : ∀ pv, ((S.kids bs sqE).getD 15 noKid pv).taken = true →
      CompleteAtB fs cert κ "check_opening_terminal" ((S.kids bs sqE).getD 15 noKid pv).Lin
        ((S.kids bs sqE).getD 15 noKid pv).args ((S.kids bs sqE).getD 15 noKid pv).Out
        (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) :
    KidsDepB fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) := by
  refine kidsDepB_of _ _ (by rw [ChildSegs.kids_length]; rfl) fun j hj pv ↦ ?_
  have hj16 : j < 16 := by simpa [ChildSegs.kids_length] using hj
  have hμ1 := S.hmu22
  have hμ2 := S.hmu28
  have hd := S.d_bounds hbl
  have hdE : S.d = log2Ceil S.pushT := S.d_eq hbl
  have hst := S.stackTotal_le hbl
  obtain ⟨hhs, h5⟩ := S.hs_bounds hbl
  have hstat : ∀ g ∈ vsStaticS, TotalLe coreProgram fs g fun _ ↦ W.Kst g := W.hst
  interval_cases j <;> simp only [vsBsAt, vsBsWith, List.getD_cons_succ, List.getD_cons_zero]
  · exact ⟨fun _ ↦ vs_gpw_completeAtB κ [] (by have := S.hr4; omega) W.hg, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ vs_gpw_completeAtB κ [] (by have := S.h32; omega) W.hg, fun h ↦ by cases h⟩
  · refine ⟨fun _ ↦ log2_L0_completeAtB κ (by omega) S.pushT sqE ?_ ?_, fun h ↦ by cases h⟩
    · have := log2Ceil_le_iff.mp (show log2Ceil S.pushT ≤ 29 by omega)
      calc S.pushT ≤ 2 ^ 29 := this
        _ < 2 ^ 34 := by norm_num
    · show max 0 (log2Ceil S.pushT) < 34; omega
  · exact ⟨fun _ ↦ (Tables.certify_placement_completeAtB fs cert (by omega)
      (heights_length6 S.rowsN S.hrowsL) S.h32 hhs (show S.hs.getD 5 0 ≤ 27 by omega) _ _).toCompleteAtB,
      fun h ↦ by cases h⟩
  · have hl : log2Ceil (Tables.stackTotal S.kappas) ≤ 28 := log2Ceil_le_iff.mpr hst
    exact ⟨fun _ ↦ log2_L15_completeAtB κ (by omega) _ sqE
      (lt_of_le_of_lt hst (by norm_num)) (by omega), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ grind_kidB (bits := 15) (κ := κ) (by decide) (by omega)
      (hstat _ mem_st15) sqE S.oodPow, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.spf_kid κ W bs, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.om_kid κ W bs, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.busGrind_kid hbl (by omega) sqE, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.vbg_kidB hbl (by omega) W bs sqE, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ hvt pv, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ hvk, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ grind_kidB (bits := 14) (κ := κ) (by decide) (by omega)
      (hstat _ mem_st14) sqE S.ringPow, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ rst_completeAtB κ hsl S.rchs_length W.hl14,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.os_kidB hos (by omega) hrf hcons W bs sqE, fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ hterm pv ht, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

end
end LeanVM.Guest.B1.VerifySub
