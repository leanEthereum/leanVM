/-
  LeanVM.Guest.B1.Common.Find

  A core function found by its position, its name read off its data.
-/

module

public import LeanVM.Guest.CoreNames

/-!
# Functions by position

The names being distinct (`coreProgram_names_nodup`), the function at position `j` is the one its
name finds (`coreProgram_find?_at`) and its name's first index is `j` (`coreProgram_indexOf?_at`):
both from `coreProgram[j]? = some f` and `f.name = n` (by `rfl`, after `n` is known), and for a run of functions
(`coreProgram_indexOf?_run`) from one kernel evaluation comparing each name with its function's: no
proof compares a name with the names before it in the kernel.
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- **The function at position `j` is found by its name.** -/
theorem coreProgram_find?_at {n : String} {j : ℕ} {f : Fn} (hj : coreProgram[j]? = some f)
    (hn : f.name = n := by rfl) : coreProgram.find? n = some f := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  subst hn
  exact coreProgram_find_getElem h

/-- **The function at position `j` is the first of its name.** -/
theorem coreProgram_indexOf?_at {n : String} {j : ℕ} {f : Fn} (hj : coreProgram[j]? = some f)
    (hn : f.name = n := by rfl) : coreProgram.indexOf? n = some j := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  subst hn
  unfold Program.indexOf?
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨h, by simp, fun i hij ↦ ?_⟩
  simp only [beq_iff_eq]
  intro he
  have := (List.Nodup.getElem_inj_iff coreProgram_names_nodup (i := i) (j := j)
    (hi := by simp; omega) (hj := by simp; omega)).mp (by simpa using he)
  omega

/-- **Function `j`, named `n`, is the first of its name.** -/
theorem coreProgram_indexOf?_of_name {n : String} {j : ℕ}
    (h : coreProgram[j]?.map (·.name) = some n) : coreProgram.indexOf? n = some j := by
  obtain ⟨f, hf, hn⟩ := Option.map_eq_some_iff.mp h
  exact coreProgram_indexOf?_at hf hn

/-- **Functions `j0 .. j0 + n - 1` are the first of their names `name k`**, from one kernel
evaluation that compares each name with its function's only. -/
theorem coreProgram_indexOf?_run {name : ℕ → String} {j0 n : ℕ}
    (h : (List.range n).all (fun k ↦ coreProgram[j0 + k]?.map (·.name) == some (name k)) = true) :
    ∀ k < n, coreProgram.indexOf? (name k) = some (j0 + k) := fun k hk ↦
  coreProgram_indexOf?_of_name (beq_iff_eq.mp (List.all_eq_true.mp h k (List.mem_range.mpr hk)))

/-- `some j` if function `j` is named `n`: `coreProgram.indexOf? n` where `j` is known, for a
kernel evaluation (`coreIdx?_eq`). -/
noncomputable def coreIdx? (n : String) (j : ℕ) : Option ℕ :=
  if coreProgram[j]?.map (·.name) = some n then some j else none

theorem coreIdx?_eq {n : String} {j j' : ℕ} (h : coreIdx? n j = some j') :
    coreProgram.indexOf? n = some j' := by
  unfold coreIdx? at h
  split at h
  · rename_i hn
    cases h
    exact coreProgram_indexOf?_of_name hn
  · cases h

end
end LeanVM.Guest
