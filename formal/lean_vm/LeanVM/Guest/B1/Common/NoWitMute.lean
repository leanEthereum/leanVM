/-
  LeanVM.Guest.B1.Common.NoWitMute

  The functions passing `noWitness` form a mute set (`noWitS_mute`), and a block of function `j` with no witness hint whose callees pass the check is mute in it (`noWitBlock_mute`, decided by the kernel).
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.Memory.NoWitness

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

theorem atomMute_eq (a : Atom) : atomMute a = atomNoWit a := by
  cases a with
  | hint x => cases x <;> rfl
  | _ => rfl

mutual
theorem Stmt.mute_of_noWit {S : String → Bool} : ∀ (s : Stmt), Stmt.noWit s = true →
    (∀ g ∈ Stmt.callees s, S g = true) → Stmt.mute S s = true
  | .atom a, h, _ => by rw [Stmt.mute, atomMute_eq]; exact h
  | .ite _ z n, h, hc => by
      simp only [Stmt.noWit, Bool.and_eq_true] at h
      simp only [Stmt.callees, List.mem_append] at hc
      simp only [Stmt.mute, Bool.and_eq_true]
      exact ⟨Stmt.muteList_of_noWit z h.1 fun g hg => hc g (.inl hg),
        Stmt.muteList_of_noWit n h.2 fun g hg => hc g (.inr hg)⟩
  | .match_ _ arms, h, hc => by
      rw [Stmt.mute]
      exact Stmt.muteArms_of_noWit arms h hc
  | .call f _ _, _, hc => hc f (by simp [Stmt.callees])
  | .callIf _ f _, _, hc => hc f (by simp [Stmt.callees])
  | .dispatch _ fs _ _, _, hc => List.all_eq_true.mpr fun g hg => hc g (by simpa [Stmt.callees] using hg)
  | .ret _, _, _ => rfl

theorem Stmt.muteList_of_noWit {S : String → Bool} : ∀ (ss : List Stmt), Stmt.noWitList ss = true →
    (∀ g ∈ Stmt.blockCallees ss, S g = true) → Stmt.muteList S ss = true
  | [], _, _ => rfl
  | s :: ss, h, hc => by
      simp only [Stmt.noWitList, Bool.and_eq_true] at h
      simp only [Stmt.blockCallees, List.mem_append] at hc
      simp only [Stmt.muteList, Bool.and_eq_true]
      exact ⟨Stmt.mute_of_noWit s h.1 fun g hg => hc g (.inl hg),
        Stmt.muteList_of_noWit ss h.2 fun g hg => hc g (.inr hg)⟩

theorem Stmt.muteArms_of_noWit {S : String → Bool} : ∀ (as : List (List Stmt)), Stmt.noWitArms as = true →
    (∀ g ∈ Stmt.armsCallees as, S g = true) → Stmt.muteArms S as = true
  | [], _, _ => rfl
  | a :: as, h, hc => by
      simp only [Stmt.noWitArms, Bool.and_eq_true] at h
      simp only [Stmt.armsCallees, List.mem_append] at hc
      simp only [Stmt.muteArms, Bool.and_eq_true]
      exact ⟨Stmt.muteList_of_noWit a h.1 fun g hg => hc g (.inl hg),
        Stmt.muteArms_of_noWit as h.2 fun g hg => hc g (.inr hg)⟩
end

/-- The functions passing `noWitness`. -/
noncomputable def noWitS (g : String) : Bool := by classical exact decide (NoWitG g)

theorem noWitS_iff {g : String} : noWitS g = true ↔ NoWitG g := by
  classical
  unfold noWitS
  exact decide_eq_true_iff

/-- **The functions passing `noWitness` are a mute set.** -/
theorem noWitS_mute : MuteIn coreProgram noWitS := fun g hg fn hf => by
  obtain ⟨hb, hc⟩ := coreProgram_noWitIn g (noWitS_iff.mp hg) fn hf
  exact Stmt.muteList_of_noWit fn.body hb fun g' hg' => noWitS_iff.mpr (hc g' hg')

/-- Function `j`'s callee `g` has no witness hint in its subtree. -/
noncomputable def noWitCallee (j : ℕ) (g : String) : Bool :=
  match calleeIdx j g with
  | some k => noWitJ 8 k
  | none => false

theorem noWitG_of_callee {j : ℕ} {g : String} (h : noWitCallee j g = true) : NoWitG g := by
  unfold noWitCallee at h
  split at h
  · next k hk => exact ⟨8, k, calleeIdx_spec hk, h⟩
  · exact absurd h Bool.false_ne_true

/-- **A block of function `j` with no witness hint, nor any in its callees' subtrees.** -/
noncomputable def noWitBlock (j : ℕ) (l : List Stmt) : Bool :=
  Stmt.noWitList l && (Stmt.blockCallees l).all (noWitCallee j)

theorem noWitBlock_mute {j : ℕ} {l : List Stmt} (h : noWitBlock j l = true) : Stmt.muteList noWitS l = true := by
  simp only [noWitBlock, Bool.and_eq_true, List.all_eq_true] at h
  exact Stmt.muteList_of_noWit l h.1 fun g hg => noWitS_iff.mpr (noWitG_of_callee (h.2 g hg))

end
end LeanVM.Guest.Memory
