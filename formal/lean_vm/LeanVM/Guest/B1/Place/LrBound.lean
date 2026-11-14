/-
  LeanVM.Guest.B1.Place.LrBound

  `level_residual` within every words bound of its trees, frames below `2^32`.
-/

module

public import LeanVM.Guest.B1.Place.LrProof
public import LeanVM.Guest.B1.Place.LpBound
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_residual` within a words bound

`lr_size_le`: placed after a fresh copy of its words (positions, basis row, high part, all zero),
`level_residual` holds on a fresh memory, so a words bound of its trees is at least its frame and
buffers. `level_residual_completeAtB`: each entry is `LrAtO` at `some B`: on an instance whose
buffers and caller's words some memory holds, the placed tree's words are at most `B`
(`relAtIn_le`); on any other, its frame and buffers alone, the relation vacuous.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

theorem lrSizes_sum_le (q : ℕ) : (lrSizes q).sum ≤ 2 * q + 4 := by
  have h1 := Nat.div_add_mod q 8
  unfold lrSizes
  simp only [resBatch]
  split <;> simp <;> omega

theorem lrLb_within (fs : String → ℕ) (name : String) (q cols nhs hbits : ℕ) (D : ℕ → E)
    (hsv : List E) (p : ℕ → E) (M : E) (fp : ℕ) :
    Within (lrLb fs name q cols nhs hbits D hsv p M fp) fp (fs name + (lrSizes q).sum) :=
  (bufL_within _ _ _ (lrWords_fit q cols nhs hbits D hsv p M)).mono (Nat.le_add_right _ _)
    (by omega)

theorem lrLb_disj (fs : String → ℕ) (name : String) (q cols nhs hbits : ℕ) (D : ℕ → E)
    (hsv : List E) (p : ℕ → E) (M : E) (fp : ℕ) :
    DisjL (lrLb fs name q cols nhs hbits D hsv p M fp) :=
  bufL_disj _ _ _ (lrWords_fit q cols nhs hbits D hsv p M)

set_option maxHeartbeats 800000 in
/-- **A words bound of `level_residual`'s trees is at least its frame and buffers**, frames below
`2^32`. -/
theorem lr_size_le {name loop1 loop2 : String} {q cols nhs hbits : ℕ}
    (hlr : FnIs name (osParams 4) (lrBody q loop1 loop2))
    (hl1 : FnIs loop1 (osParams 7) (lrLoop1Body cols nhs hbits loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 7) (lrLoop2Body cols nhs hbits loop2))
    (hF : LrFacts q cols nhs hbits loop1 loop2) (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) (hfs : ∀ f, fs f < 2 ^ 32) {B : ℕ} (hT : TotalLe coreProgram fs name (fun _ ↦ B)) :
    fs name + (lrSizes q).sum ≤ B := by
  have hsm : q + cols + nhs ≤ 2 ^ 20 := hF.2.2.2.2.2.2.2.2
  set posW : List E := List.replicate q 0 with hposW
  set dW : List E := List.replicate cols 0 with hdW
  set hsW : List E := List.replicate nhs 0 with hhsW
  set Lin0 : Layout := [(0, posW), (q, dW), (q + cols, hsW)] with hLin0
  set fp0 := q + cols + nhs with hfp0
  have hlP : posW.length = q := by simp [hposW]
  have hlD : dW.length = cols := by simp [hdW]
  have hlH : hsW.length = nhs := by simp [hhsW]
  have hLW : Within Lin0 0 fp0 := by
    intro e he
    simp only [hLin0, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [hlP]; omega
    · simp only [hlD]; omega
    · simp only [hlH]; omega
  have hLD : DisjL Lin0 := by
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons
      (fun _ h ↦ absurd h List.not_mem_nil) .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · left; simp only [hlP]; omega
      · left; simp only [hlP]; omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      left; simp only [hlD]; omega
  have hreg : RegPtrs [(0, q), (1, cols), (2, nhs)]
      [ofK (addressOfIndex 0), ofK (addressOfIndex q), ofK (addressOfIndex (q + cols)), 0]
      (RegionL Lin0) := by
    intro e he t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨0 + t, Main.addr_ofK _ _, (0, posW), by simp [hLin0], by omega, by simp only [hlP]; omega⟩
    · exact ⟨q + t, Main.addr_ofK _ _, (q, dW), by simp [hLin0], by omega, by simp only [hlD]; omega⟩
    · exact ⟨q + cols + t, Main.addr_ofK _ _, (q + cols, hsW), by simp [hLin0], by omega,
        by simp only [hlH]; omega⟩
  have hmem : ∀ rd, LowDef κ rd → MemL rd Lin0 →
      (∀ i < q, LoadHolds rd (ofK (addressOfIndex 0)) i ((fun _ ↦ (0 : E)) i)) ∧
      (∀ s < cols, LoadHolds rd (ofK (addressOfIndex q)) s ((fun _ ↦ (0 : E)) s)) ∧
      ∀ c < nhs, LoadHolds rd (ofK (addressOfIndex (q + cols))) c (hsW.getD c 0) := by
    intro rd _ hm
    have h0 := hm (0, posW) (by simp [hLin0])
    have h1 := hm (q, dW) (by simp [hLin0])
    have h2 := hm (q + cols, hsW) (by simp [hLin0])
    refine ⟨fun i hi ↦ ?_, fun s hs ↦ ?_, fun c hc ↦ ?_⟩
    · have := h0 i (by rw [hlP]; exact hi); simpa [hposW] using this
    · have := h1 s (by rw [hlD]; exact hs); simpa [hdW] using this
    · have := h2 c (by rw [hlH]; exact hc)
      rwa [List.getD_eq_getElem _ _ (by rw [hlH]; exact hc)]
  obtain ⟨m, hm⟩ := lr_key hlr hl1 hl2 hF fs cert κ (D := fun _ ↦ 0) (p := fun _ ↦ 0) hlH hreg hmem fp0
  have hlt : fp0 + (fs name + (lrSizes q).sum) < 2 ^ 64 - 1 := by
    have := hfs name
    have := lrSizes_sum_le q
    omega
  obtain ⟨rd, hlow, hmm⟩ := fresh_pair κ (lrLb_disj fs name q cols nhs hbits _ _ _ 0 fp0)
    (lrLb_within fs name q cols nhs hbits _ _ _ 0 fp0) hLD hLW hlt
  have := relAtIn_le (hm rd hlow hmm) hT
  omega

/-- **`level_residual` within every words bound of its trees**, frames below `2^32`. -/
theorem level_residual_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfs : ∀ f, fs f < 2 ^ 32) :
    ∀ e ∈ lrTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
      Arm.LrAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (some B) := by
  intro e he B hT
  obtain ⟨hlr, hl1, hl2⟩ := lrTable_ok e he
  have hF := lrTable_facts e he
  have hsz := lr_size_le hlr hl1 hl2 hF fs cert κ hfs hT
  intro Lin P BD HS M D p hsv hlen hreg hmem fp
  classical
  obtain ⟨m, hm⟩ := lr_key hlr hl1 hl2 hF fs cert κ hlen hreg hmem fp
  have hW := lrLb_within fs e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 D hsv p M fp
  have hD := lrLb_disj fs e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 D hsv p M fp
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (lrLb fs e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 D hsv p M fp ++ Lin)
  · obtain ⟨rd0, hl0, hm0⟩ := hex
    refine ⟨fs e.1 + (lrSizes e.2.1).sum + m, lrLb fs e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 D hsv p M fp,
      _, [], ⟨rfl, rfl⟩, by simpa using hW.mono le_rfl (by omega), by simpa using hD,
      fun B' hB' ↦ by cases hB'; exact relAtIn_le (hm rd0 hl0 hm0) hT,
      fun rd hl hL ↦ relAtIn_dmono (hm rd hl (by simpa using hL)) (fun i hi ↦ ?_)⟩
    obtain ⟨x, hx, _⟩ := hi; simp at hx
  · refine ⟨fs e.1 + (lrSizes e.2.1).sum, lrLb fs e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 D hsv p M fp,
      _, [], ⟨rfl, rfl⟩, by simpa using hW, by simpa using hD,
      fun B' hB' ↦ by cases hB'; exact hsz,
      fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

end
end LeanVM.Guest.B1
