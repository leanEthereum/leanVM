/-
  LeanVM.Guest.Memory.GuestStatic

  The guest's static weight certificates, checked: `coreProgram_checked`.
-/

module

public import LeanVM.Guest.Memory.GuestStatic.All
public import LeanVM.Guest.CoreNames

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The index of a function of the guest by name. -/
noncomputable def coreIdx (g : String) : ℕ := (coreProgram.map (·.name)).idxOf g

/-- The guest's weight certificates by name. -/
noncomputable def staticCertOf (g : String) : Cert := certJ (coreIdx g)

/-- The weight of a frame of each of the guest's functions. -/
noncomputable def omegaOf (g : String) : ℕ := omegaJ (coreIdx g)

theorem coreIdx_getElem {j : ℕ} (h : j < coreProgram.length) : coreIdx coreProgram[j].name = j := by
  have h' : j < (coreProgram.map (·.name)).length := by rwa [List.length_map]
  have := coreProgram_names_nodup.idxOf_getElem j h'
  rwa [List.getElem_map] at this

theorem coreIdx_of_name {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    coreIdx g = j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; exact absurd h (by simp)
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn, coreIdx_getElem hlt]

/-- A certificate by index: `h` by `decide +kernel`, then `certJ j` by `rfl`. -/
theorem certOf_of_idx {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    staticCertOf g = certJ j := by
  rw [staticCertOf, coreIdx_of_name h]

theorem omegaOf_of_idx {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    omegaOf g = omegaJ j := by
  rw [omegaOf, coreIdx_of_name h]

theorem lookJ_ok {j : ℕ} (hl : (lnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true) :
    LookOk (lookJ j) staticCertOf := by
  intro g hg
  unfold lookJ at hg ⊢
  rcases hf : (lnkJ j).find (nameKey g) with _ | q
  · rw [hf] at hg; exact absurd rfl hg
  · rw [hf] at hg
    dsimp only at hg ⊢
    by_cases hq : g = q.1
    · have hp := NTree.find_all hl hf
      simp only [decide_eq_true_eq] at hp
      rw [ite_eq_left (c := g = q.1) hq, certOf_of_idx (hq ▸ hp)]
    · rw [ite_eq_right (c := g = q.1) hq] at hg; exact absurd rfl hg

theorem omLookJ_ok {j : ℕ}
    (hl : (lnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true) :
    WlOk (omLookJ j) omegaOf := by
  intro g n hg
  unfold omLookJ at hg
  rcases hf : (lnkJ j).find (nameKey g) with _ | q
  · rw [hf] at hg; cases hg
  · rw [hf] at hg
    dsimp only at hg
    by_cases hq : g = q.1
    · rw [ite_eq_left (c := g = q.1) hq, Option.some.injEq] at hg
      have hp := NTree.find_all hl hf
      simp only [decide_eq_true_eq] at hp
      rw [omegaOf_of_idx (hq ▸ hp), hg]
    · rw [ite_eq_right (c := g = q.1) hq] at hg; cases hg

/-- **The guest's certificates check.** -/
theorem coreProgram_checked : Checked coreProgram false staticCertOf omegaOf := by
  intro fn hfn _
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hc := chkIdx_all j (by rw [coreProgram_length] at hj; exact hj)
  unfold chkIdx at hc
  rw [List.getElem?_eq_getElem hj] at hc
  simp only [handJ, List.any_nil, Bool.false_or, Bool.and_eq_true] at hc
  refine ⟨lookJ j, omLookJ j, lookJ_ok hc.1, omLookJ_ok hc.1, ?_⟩
  rw [staticCertOf, omegaOf, coreIdx_getElem hj]
  exact hc.2

/-- A function of the guest with a constant certificate. -/
theorem core_weightLe {f : String} {B : ℕ} {ks : List (V × ℕ)}
    (hcf : staticCertOf f = .stat [] ⟨B, []⟩ ks) : WeightLe coreProgram omegaOf f fun _ => B :=
  weightLe_of_stat coreProgram_checked hcf

end
end LeanVM.Guest
