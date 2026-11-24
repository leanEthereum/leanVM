/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub`'s callees on an honest child: their names, and the static ones within their bounds.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.WhirLen
public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.B1.VerifySub.H.Vt
public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.B1.Tables.VtWordsC
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.KeccakGkr.VkCW

/-!
# `verify_sub`'s callees within their bounds

The names of `verify_sub`'s callees at the child's shape (`squeezeName_eq`, `busGrindName_eq`, `squeezeName_mem`), and
the static callees within their bounds (`om_kid`, `spf_kid`); `vt_dims`: `verify_tables`' dimensions on the honest
child.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem squeezeName_eq {μ : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) :
    squeezeNames.getD (μ - 20) "" = spfName μ := by
  interval_cases μ <;> rfl

theorem busGrindName_eq (d : ℕ) : busGrindNames.getD d "" = busGrindName d := rfl

theorem squeezeName_mem {μ : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) :
    squeezeNames.getD (μ - 20) "" ∈ squeezeNames := by
  interval_cases μ <;> decide

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 → (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_cap_length n s.squeeze.2 (by simp [Fs.squeeze, capOf])

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
    CompleteAtB fs cert κ (squeezeNames.getD (S.μs - 20) "") [(vb bs 6, S.oodZ)]
      (capOf S.oodSt ++ [challengeOf S.oodSt, ptr (vb bs 6)]) (Returns S.sZ.cap)
      (armMax W.Kst squeezeNames) := by
  have hμ1 : 20 ≤ S.μs := S.hmu20
  have hμ2 : S.μs ≤ 30 := S.hmu30
  have hm := squeezeName_mem hμ1 hμ2
  have e := squeezeName_eq hμ1 hμ2
  have hT : TotalLe coreProgram fs (spfName S.μs) fun _ ↦ W.Kst (squeezeNames.getD (S.μs - 20) "") := by
    rw [← e]; exact W.hst _ (List.mem_append_left _ (List.mem_append_right _ hm))
  have h := spf_kidB (cert := cert) (n := S.μs) (List.mem_map.2 ⟨S.μs - 6, List.mem_range.2 (by omega), by omega⟩) κ hT S.oodSt (vb bs 6)
  rw [← e] at h
  exact h.mono le_rfl (le_armMax W.Kst hm)

end ChildSegs

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- `verify_tables`' bus depth and largest height on an honest child, within its words interface's ranges. -/
theorem vt_dims (hbl : bytecode.length = 2 ^ 23) : S.H.μ < 32 ∧ S.H.n < 31 := by
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  exact ⟨by show S.rG.2.1.length < 32; omega, by have := S.nT_le hbl; show S.nT < 31; omega⟩

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
