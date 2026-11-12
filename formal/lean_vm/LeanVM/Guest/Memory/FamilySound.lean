/-
  LeanVM.Guest.Memory.FamilySound

  A family whose ranges pass covers the guest's core IR, and its checks give a checked program:
  every coordinate of a vector family (`checked_of_chkV`), and a scalar one (`checked_of_chkS`).
-/

module

public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.Memory.GuestCalleesOk
public import LeanVM.Guest.Memory.StaticVecSound
public import LeanVM.Guest.Memory.GuestIdx

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-! ## Callees -/

/-- **A callee's index names it.** -/
theorem calleeIdx_spec {j k : ℕ} {g : String} (h : calleeIdx j g = some k) :
    (coreProgram[k]?).map Fn.name = some g := by
  unfold calleeIdx at h
  have hm := List.mem_of_find?_eq_some h
  have hn := List.find?_some h
  simp only [decide_eq_true_eq] at hn
  have hk : k < coreProgram.length := by
    unfold Data.calleesJ at hm
    rcases hf : Data.calleeT.find j with _ | l
    · rw [hf] at hm; simp at hm
    · rw [hf] at hm
      have := NTree.find_all Data.calleeT_lt hf
      have := List.all_eq_true.mp this k hm
      simpa [coreProgram_length] using this
  exact Data.nameT_spec hk hn

theorem lookV_ok (cert : ℕ → CertV) (i j : ℕ) :
    LookOk (fun g => (lookV cert j g).proj i) (fun g => (cert (coreIdx g)).proj i) := by
  intro g hg
  dsimp only at hg ⊢
  unfold lookV at hg ⊢
  rcases hk : calleeIdx j g with _ | k
  · simp only [hk] at hg; exact absurd rfl hg
  · rw [coreIdx_of_name (calleeIdx_spec hk)]

theorem lookS_ok (cert : ℕ → Cert) (j : ℕ) : LookOk (lookS cert j) fun g => cert (coreIdx g) := by
  intro g hg
  dsimp only
  unfold lookS at hg ⊢
  rcases hk : calleeIdx j g with _ | k
  · simp only [hk] at hg; exact absurd rfl hg
  · rw [coreIdx_of_name (calleeIdx_spec hk)]

theorem omLookS_ok {om : ℕ → ℕ} {ω : String → ℕ}
    (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = om j) (j : ℕ) :
    WlOk (omLookS om j) ω := by
  intro g n hg
  unfold omLookS at hg
  rcases hk : calleeIdx j g with _ | k
  · rw [hk] at hg; cases hg
  · rw [hk, Option.map_some, Option.some.injEq] at hg
    have hs := calleeIdx_spec hk
    rcases hj : coreProgram[k]? with _ | fn
    · rw [hj] at hs; cases hs
    · rw [hj, Option.map_some, Option.some.injEq] at hs
      obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
      rw [← hs, ← hfn, hω k hlt, hg]

/-! ## Checked families -/

/-- **Coordinate `i` of a vector family whose ranges pass checks**, at frame weights `ω` agreeing
with the family's on the functions it certifies. -/
theorem checked_of_chkV {cert : ℕ → CertV} {om : ℕ → Vec}
    (h : RangeOk (chkV cert om) 0 coreProgram.length) (i : ℕ) {ω : String → ℕ}
    (hω : ∀ j (hj : j < coreProgram.length), cert j ≠ .none → ω coreProgram[j].name = (om j).getD i 0) :
    Checked coreProgram false (fun g => (cert (coreIdx g)).proj i) ω := by
  intro fn hfn _
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  refine ⟨fun g => (lookV cert j g).proj i, fun _ => none, lookV_ok cert i j,
    fun _ _ h => by simp at h, ?_⟩
  dsimp only
  rw [coreIdx_getElem hj]
  by_cases hn : cert j = .none
  · rw [hn]; rfl
  · rw [hω j hj hn]
    exact chkFnV_proj i (RangeOk.all h hj) _

/-- **A scalar family whose ranges pass checks**, at frame weights `ω` agreeing with the
family's. -/
theorem checked_of_chkS {α : Bool} {cert : ℕ → Cert} {om : ℕ → ℕ}
    (h : RangeOk (chkS α cert om) 0 coreProgram.length) {ω : String → ℕ}
    (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = om j) :
    Checked coreProgram α (fun g => cert (coreIdx g)) ω := by
  intro fn hfn _
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  refine ⟨lookS cert j, omLookS om j, lookS_ok cert j, omLookS_ok hω j, ?_⟩
  dsimp only
  rw [coreIdx_getElem hj, hω j hj]
  exact RangeOk.all h hj

end
end LeanVM.Guest.Memory
