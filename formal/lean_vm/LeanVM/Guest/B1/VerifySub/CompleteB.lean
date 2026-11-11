/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub`'s sixteen callees on an honest child, each placed within its bound
  (`BoundsB`'s `vsBsAt`).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.WhirLen
public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.B1.VerifySub.H.Vt
public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.B1.Tables.VtC.ABound
public import LeanVM.Guest.B1.Tables.VtC.AWeight
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.KeccakGkr.VkCW

/-!
# `verify_sub`'s callees within their bounds

`kidsDepB_of`: callees by position, each within its bound. `vs_kidsDepBAt_of`: on an honest child
(`ChildSegs`), the callees are `KidsDepB` within `vsBsAt W Bvk μ r` at the child's stack log and
rate, given `verify_tables`', `verify_keccak`'s and the terminal's placed completeness on the
child's words (`hvt`, `hvk`, `hterm`); the others from their own theorems (`H/KidsB`, `os_kidB`
from `open_stacked_completeAtB_Spec`). `vs_kidsDepBAt`: those three discharged (`vt_kidB`,
`vk_kidB`, `term_kidB`), `verify_keccak` by `VkCompleteAtBK`. `vs_kidsDepBP`: each callee by a tree
of its predicate (`vsPs`: `verify_tables`' and the terminal's within their weights).
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
theorem mem_st13 : "grind_check__L13" ∈ vsStaticS := by simp [vsStaticS]
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
  · exact ⟨fun _ ↦ grind_kidB (bits := 13) (κ := κ) (by decide) (by omega)
      (hstat _ mem_st13) sqE S.ringPow, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ rst_completeAtB κ hsl S.rchs_length W.hl14,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.os_kidB hos (by omega) hrf hcons W bs sqE, fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ hterm pv ht, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- `verify_tables`' own buffers. -/
theorem vt_sizes_sum : S.H.sizes.sum = 3841 + S.H.μ + 9 * (S.H.n + 1) := by
  simp only [Tables.VtHonest.sizes, List.sum_append, List.sum_cons, List.sum_nil,
    List.sum_replicate, smul_eq_mul]
  omega

theorem vt_bound_le (hbl : bytecode.length = 2 ^ 23) (W : VsWordsOs fs) :
    fs "verify_tables" + S.H.sizes.sum + ((Tables.vtBs W.Kf W.Ksh
      (Tables.vtRunB fs W.K10 S.H.n)).sum + Tables.ifFrames fs Tables.vtPre) ≤
      vtMax fs W.Kf W.Ksh W.K10 := by
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  have hHμ : S.H.μ < 30 := by show S.rG.2.1.length < 30; omega
  have hn : S.H.n < 29 := by have := S.nT_le hbl; show S.nT < 29; omega
  rw [S.vt_sizes_sum]
  unfold vtMax
  exact le_lmax2 (vtBnd fs W.Kf W.Ksh W.K10) hHμ hn

/-- **`verify_tables` on an honest child, within `vtMax`.** -/
theorem vt_kidB (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 14 ≤ κ) (W : VsWordsOs fs)
    (B : Tables.VtBases) :
    CompleteAtB fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (vtMax fs W.Kf W.Ksh W.K10) :=
  (Tables.verify_tables_completeAtTB hκ (S.H_run hbl).1 (S.H_shape hbl) B W.Kf W.Ksh W.K10 W.hKf
    W.hsh W.h10).toCompleteAtB.mono le_rfl (S.vt_bound_le hbl W)

/-- **`verify_tables` on an honest child, within `vtMax` by a tree within its weights.** -/
theorem vt_kidBW (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 14 ≤ κ) (W : VsWordsOs fs)
    (B : Tables.VtBases) :
    CompleteAtDTB fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t)
      (vtMax fs W.Kf W.Ksh W.K10) :=
  (Tables.verify_tables_completeAtTBW' hκ (S.H_run hbl).1 (S.H_shape hbl) B W.Kf W.Ksh W.K10 W.hKf
    W.hsh W.h10 W.ωv W.Kvw W.Wss W.Kw10 W.hKvw W.hssw W.h10w).mono (S.vt_bound_le hbl W)
    fun _ h ↦ h

/-- **`verify_keccak` on an honest child**, from its bounded completeness. -/
theorem vk_kidB (hbl : bytecode.length = 2 ^ 23) {κ Bvk : ℕ} (hvk : VkCompleteAtBK fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    CompleteAtB fs cert κ "verify_keccak" ((S.kids bs sqE).getD 11 noKid []).Lin
      ((S.kids bs sqE).getD 11 noKid []).args ((S.kids bs sqE).getD 11 noKid []).Out Bvk := by
  obtain ⟨-, -, hrun⟩ := S.keccak_run hbl
  obtain ⟨h9, h22, hn, ho, hf, -⟩ := S.keccak_facts hbl
  obtain ⟨-, -, h5⟩ := S.H_spec hbl
  have hc : ∃ sp, (⟨S.H.s3.squeeze.2.cap, []⟩ : Fs).Carries sp := by rw [← h5]; exact S.c5
  exact hvk S.τ _ S.H.chiW S.outs S.xsK S.kOut.point S.kc.2.1 S.kc.2.2 S.kOut.value S.s6 (S.cK bs)
    (vb bs 9) (S.cL bs) (vb bs 11) (vb bs 12) (sqE + winTabAt) h9 (by omega) hn ho hf hc hrun

end ChildSegs

/-- **`verify_sub`'s callees on an honest child, each within its bound**, `open_stacked` within
its candidate's. -/
theorem vs_kidsDepBAt {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk : ℕ} (hvk : VkCompleteAtBK fs cert κ Bvk)
    (hos : open_stacked_completeAtB_Spec) (bs : List ℕ) (sqE : ℕ) :
    KidsDepB fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) :=
  vs_kidsDepBAt_of hbl S hκ hrf hcons W Bvk hos bs sqE (S.keccak_facts hbl).2.2.2.2.2.2.2
    (fun pv ↦ S.vt_kidB hbl (by omega) W _) (S.vk_kidB hbl hvk bs sqE)
    (fun pv ht ↦ S.term_kidB hbl (by omega) W bs sqE pv ht)

/-- The `j`-th callee of callees within their bounds. -/
theorem kidsDepB_getD {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    ∀ (j : ℕ), j < ks.length → ∀ (pv : List (List E × Main.Layout)),
      ((ks.getD j noKid pv).taken = true →
        CompleteAtB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)
  | [], _, _, _, hj, _ => absurd hj (by simp)
  | _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _, pv => h.1 pv
  | _ :: _, _ :: _, h, j + 1, hj, pv => kidsDepB_getD h.2 j (by simpa using hj) pv

theorem kidsDepBP_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    ks.length = Bs.length → ks.length = Ps.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtDTB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ ↦ True)
          (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepBP fs cert κ ks Bs Ps
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | _ :: ks, _ :: Bs, _ :: Ps, hl, hl', h =>
    ⟨h 0 (by simp), kidsDepBP_of ks Bs Ps (by simpa using hl) (by simpa using hl')
      fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-- **`verify_sub`'s callees on an honest child, each within its bound by a tree of its
predicate**, `open_stacked` within its candidate's. -/
theorem vs_kidsDepBP {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk : ℕ} (hvk : VkCompleteAtBK fs cert κ Bvk)
    (hos : open_stacked_completeAtB_Spec) (bs : List ℕ) (sqE : ℕ) :
    KidsDepBP fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) (vsPs W) := by
  have hB := kidsDepB_getD (vs_kidsDepBAt hbl S hκ hrf hcons W hvk hos bs sqE)
  refine kidsDepBP_of _ _ _ (by rw [ChildSegs.kids_length]; rfl)
    (by rw [ChildSegs.kids_length]; rfl) fun j hj pv ↦ ?_
  have hj16 : j < 16 := by simpa [ChildSegs.kids_length] using hj
  have hP : j ≠ 10 → j ≠ 15 → (vsPs W).getD j (fun _ ↦ True) = fun _ ↦ True := by
    intro h10 h15
    interval_cases j <;> first | rfl | exact absurd rfl h10 | exact absurd rfl h15
  by_cases h10 : j = 10
  · subst h10
    refine ⟨fun _ ↦ ?_, fun h ↦ by cases h⟩
    have e : (vsBsAt W Bvk S.μs S.rate).getD 10 0 = vtMax fs W.Kf W.Ksh W.K10 := by
      simp only [vsBsAt, vsBsWith, List.getD_cons_succ, List.getD_cons_zero]
    rw [e]
    exact S.vt_kidBW hbl (by omega) W _
  by_cases h15 : j = 15
  · subst h15
    have e : (vsBsAt W Bvk S.μs S.rate).getD 15 0 = termBound fs W.Beqc W.K15 W.Bcs W.Brs := by
      simp only [vsBsAt, vsBsWith, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨fun ht ↦ ?_, (hB 15 (by rw [ChildSegs.kids_length]; omega) pv).2⟩
    rw [e]
    exact S.term_kidBW hbl (by omega) W bs sqE pv ht
  rw [hP h10 h15]
  exact ⟨fun h ↦ ((hB j hj pv).1 h).toDTB, (hB j hj pv).2⟩

end
end LeanVM.Guest.B1.VerifySub
