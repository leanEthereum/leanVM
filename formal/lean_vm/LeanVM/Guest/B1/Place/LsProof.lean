/-
  LeanVM.Guest.B1.Place.LsProof

  `level_residual_slow` is complete placed at every specialization `open_stacked` dispatches into,
  at no bound and within every words bound of its trees.
-/

module

public import LeanVM.Guest.B1.Place.LsKey
public import LeanVM.Guest.B1.Place.Ls
public import LeanVM.Guest.B1.Place.LsTable
public import LeanVM.Guest.B1.Place.Fresh

/-!
# `level_residual_slow`, placed and bounded

`lsKey` places the helper at every flag `z ∈ {0, 1}`. Within a words bound `B` of its trees:
on an instance some memory holds, the placed tree's words are at most `B` (`relAtIn_le`); on any
other the relation is vacuous and the words are the frames and buffers, at most `B` by a fresh
instance at the flag `1` (`ls_size_le`). `lsIn_of` finds each level's specialization in
`lrsTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **A words bound of `level_residual_slow`'s trees is at least its frames and its sum's
buffers**, frames below `2^32`. -/
theorem ls_size_le {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String} (he : e ∈ lrsTable)
    (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (hfs : ∀ f, fs f < 2 ^ 32) {B : ℕ}
    (hT : TotalLe coreProgram fs e.1 (fun _ ↦ B)) : lsN fs e.1 e.2.2.2.2.2.1 e.2.1 1 ≤ B := by
  obtain ⟨hQ, hQb, -⟩ := lrsTable_shapes e he
  have hsm := lrsTable_small e he
  set Q := e.2.1 with hQd
  set pre := e.2.2.1 with hpre
  set yr := e.2.2.2.1 with hyr
  set posW : List E := List.replicate Q 0 with hposW
  set fW : List E := List.replicate pre 0 with hfW
  set tW : List E := List.replicate yr 0 with htW
  set Lin0 : Layout := [(0, posW), (Q, fW), (Q + pre, tW)] with hLin0
  set fp0 := Q + pre + yr with hfp0
  have hlP : posW.length = Q := by simp [hposW]
  have hlF : fW.length = pre := by simp [hfW]
  have hlT : tW.length = yr := by simp [htW]
  have hLW : Within Lin0 0 fp0 := by
    intro q hq
    simp only [hLin0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simp only [hlP]; omega
    · simp only [hlF]; omega
    · simp only [hlT]; omega
  have hLD : DisjL Lin0 := by
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons
      (fun _ h ↦ absurd h List.not_mem_nil) .nil))
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · left; simp only [hlP]; omega
      · left; simp only [hlP]; omega
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      left; simp only [hlF]; omega
  have hreg : RegPtrs [(0, Q), (1, pre), (2, yr)]
      [ofK (addressOfIndex 0), ofK (addressOfIndex Q), ofK (addressOfIndex (Q + pre)), 0, 1]
      (RegionL Lin0) := by
    intro q hq t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨0 + t, Main.addr_ofK _ _, (0, posW), by simp [hLin0], by omega, by simp only [hlP]; omega⟩
    · exact ⟨Q + t, Main.addr_ofK _ _, (Q, fW), by simp [hLin0], by omega, by simp only [hlF]; omega⟩
    · exact ⟨Q + pre + t, Main.addr_ofK _ _, (Q + pre, tW), by simp [hLin0], by omega,
        by simp only [hlT]; omega⟩
  have hmem : ∀ rd, LowDef κ rd → MemL rd Lin0 →
      (∀ k < Q, LoadHolds rd (ofK (addressOfIndex 0)) k ((fun _ ↦ (0 : E)) k)) ∧
      (∀ t < pre, LoadHolds rd (ofK (addressOfIndex Q)) t ((fun _ ↦ (0 : E)) t)) ∧
      ∀ j < yr, LoadHolds rd (ofK (addressOfIndex (Q + pre))) j ((fun _ ↦ (0 : E)) (pre + j)) := by
    intro rd _ hm
    have h0 := hm (0, posW) (by simp [hLin0])
    have h1 := hm (Q, fW) (by simp [hLin0])
    have h2 := hm (Q + pre, tW) (by simp [hLin0])
    refine ⟨fun i hi ↦ ?_, fun s hs ↦ ?_, fun c hc ↦ ?_⟩
    · have := h0 i (by rw [hlP]; exact hi); simpa [hposW] using this
    · have := h1 s (by rw [hlF]; exact hs); simpa [hfW] using this
    · have := h2 c (by rw [hlT]; exact hc); simpa [htW] using this
  obtain ⟨m, hm⟩ := lsKey (p := fun _ ↦ 0) (cs := fun _ ↦ 0) he fs cert κ (Or.inr rfl) hreg hmem fp0
  have hN : lsN fs e.1 e.2.2.2.2.2.1 Q 1 = fs e.1 + (fs e.2.2.2.2.2.1 + 2 * (Q + 1)) := by
    rw [lsN, ite_eq_right one_ne_zero]
  have hlt : fp0 + lsN fs e.1 e.2.2.2.2.2.1 Q 1 < 2 ^ 64 - 1 := by
    have := hfs e.1
    have := hfs e.2.2.2.2.2.1
    rw [hN]; omega
  obtain ⟨rd, hlow, hmm⟩ := fresh_pair κ
    (lsLb_disj fs e.1 e.2.2.2.2.2.1 Q (pre + yr) e.2.2.2.2.1 (fun _ ↦ 0) (fun _ ↦ 0) 0 1 fp0)
    (lsLb_within fs e.1 e.2.2.2.2.2.1 Q (pre + yr) e.2.2.2.2.1 (fun _ ↦ 0) (fun _ ↦ 0) 0 1 fp0) hLD hLW hlt
  exact (Nat.le_add_right _ m).trans (relAtIn_le (hm rd hlow hmm) hT)

theorem lsN_le (fs : String → ℕ) (name sum : String) (Q : ℕ) (z : E) :
    lsN fs name sum Q z ≤ lsN fs name sum Q 1 := by
  rw [lsN, lsN, ite_eq_right one_ne_zero]
  split <;> omega

/-- **`level_residual_slow` at an entry of `lrsTable` is `LsAtO`**, at every optional bound of its
trees, frames below `2^32` when bounded. -/
theorem lsAtO_of {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String} (he : e ∈ lrsTable)
    (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bd : Option ℕ)
    (hBd : ∀ B ∈ Bd, (∀ f, fs f < 2 ^ 32) ∧ TotalLe coreProgram fs e.1 (fun _ ↦ B)) :
    LsAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 Bd := by
  intro Lin P F T lam z p cs hz hreg hmem fp
  classical
  obtain ⟨m, hm⟩ := lsKey he fs cert κ hz hreg hmem fp
  set Lb := lsLb fs e.1 e.2.2.2.2.2.1 e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 p cs lam z fp with hLb
  set N := lsN fs e.1 e.2.2.2.2.2.1 e.2.1 z with hN
  have hW : Within Lb fp N :=
    lsLb_within fs e.1 e.2.2.2.2.2.1 e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 p cs lam z fp
  have hD : DisjL Lb :=
    lsLb_disj fs e.1 e.2.2.2.2.2.1 e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 p cs lam z fp
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (Lb ++ Lin)
  · obtain ⟨rd0, hl0, hm0⟩ := hex
    refine ⟨N + m, Lb, _, [], ⟨rfl, rfl⟩, by simpa using hW.mono le_rfl (by omega), by simpa using hD,
      fun B hB ↦ relAtIn_le (hm rd0 hl0 hm0) (hBd B hB).2,
      fun rd hl hL ↦ relAtIn_dmono (hm rd hl (by simpa using hL)) (fun i hi ↦ ?_)⟩
    obtain ⟨x, hx, _⟩ := hi; simp at hx
  · refine ⟨N, Lb, _, [], ⟨rfl, rfl⟩, by simpa using hW, by simpa using hD, fun B hB ↦ ?_,
      fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
    obtain ⟨hfs, hT⟩ := hBd B hB
    exact (lsN_le fs _ _ _ z).trans (ls_size_le he fs cert κ hfs hT)

/-- **`level_residual_slow` is complete placed at every specialization `open_stacked` dispatches
into**, at no bound and, frames below `2^32`, within every bound of its trees. -/
theorem level_residual_slow_completeAt : level_residual_slow_completeAt_Spec := by
  intro fs cert κ _ _ _ m hm ri hri l hl Bd hBd
  obtain ⟨e, he, h1, h2, h3, h4, h5⟩ := lsIn_of (lsIn_all m hm ri hri) hl
  rw [← h1, ← h2, ← h3, ← h4, ← h5]
  exact lsAtO_of he fs cert κ Bd fun B hB ↦ by rw [h1]; exact hBd B hB

end
end LeanVM.Guest.B1
