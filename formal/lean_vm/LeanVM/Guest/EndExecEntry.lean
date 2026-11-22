/-
  LeanVM.Guest.EndExecEntry

  Compiled functions' entries are distinct.
-/

module

public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.SoundFacts
public import LeanVM.Guest.CheckSound
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# Distinct entries

The compiled functions sit one after another (`functions_consecutive`), each with an instruction
(`functions_pos`), so two of them with one entry are one (`fnOf_entry_inj`): an instance at a function's
entry is that function's.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest

@[expose] public section

theorem consecutive_bounds : ∀ {s e : ℕ} {fns : List CompiledFunction}, consecutive s fns e = true →
    ∀ f ∈ fns, s ≤ f.entryPc ∧ f.entryPc + f.instructionCount ≤ e
  | _, _, [], _, _, hf => absurd hf List.not_mem_nil
  | _, _, f0 :: gs, h, f, hf => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hg, hgs⟩ := h
    have := consecutive_le hgs
    rcases List.mem_cons.mp hf with rfl | hf
    · omega
    · have := consecutive_bounds hgs f hf
      omega

/-- Every compiled function has an instruction. -/
theorem functions_pos : Data.functions.all (fun f ↦ decide (0 < f.instructionCount)) = true := by
  decide +kernel

theorem entry_inj_list : ∀ {s e : ℕ} {fns : List CompiledFunction}, consecutive s fns e = true →
    fns.all (fun f ↦ decide (0 < f.instructionCount)) = true → ∀ {i j : ℕ} (hi : i < fns.length)
      (hj : j < fns.length), fns[i].entryPc = fns[j].entryPc → i = j
  | _, _, [], _, _, _, _, hi, _, _ => absurd hi (by simp)
  | s, e, f :: fs, h, hp, i, j, hi, hj, hij => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hf, hfs⟩ := h
    have hb : ∀ k (hk : k < fs.length), s + f.instructionCount ≤ fs[k].entryPc :=
      fun k hk ↦ (consecutive_bounds hfs _ (List.getElem_mem hk)).1
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have := hb j (by simp at hj; omega)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
        omega
    | succ i =>
      cases j with
      | zero =>
        have := hb i (by simp at hi; omega)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
        omega
      | succ j =>
        simp only [List.getElem_cons_succ] at hij
        exact congrArg (· + 1) (entry_inj_list hfs hp.2 (by simp at hi; omega) (by simp at hj; omega) hij)

/-- **Compiled functions' entries are distinct.** -/
theorem fnOf_entry_inj {j j' : ℕ} (hj : j < nFns) (hj' : j' < nFns)
    (h : (fnOf j).entryPc = (fnOf j').entryPc) : j = j' := by
  have hl := End.functions_length
  unfold fnOf at h
  rw [Check.nth_eq (hl ▸ hj), Check.nth_eq (hl ▸ hj')] at h
  exact entry_inj_list functions_consecutive functions_pos _ _ h

end

end LeanVM.Guest.EndExec
