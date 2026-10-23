/-
  LeanVM.Guest.B1.Sig.SphincsFk0

  The forest-key specializations `sp_forest_key__L{t}`, 0 ≤ t < 64, in the guest's core IR are the
  templates `fkBody t`, found by their names (in groups of eight, each name compared with all
  before it).
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem fk_data_0 : ∀ t < 64, (coreProgram[205 + (0 + t)]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn (0 + t)).name, (fkFn (0 + t)).params, (fkFn (0 + t)).body) := by
  decide +kernel

theorem fk_index_0 : ∀ t < 8, coreProgram.indexOf? (fkFn (0 + t)).name = some (205 + (0 + t)) := by
  decide +kernel

theorem fk_index_8 : ∀ t < 8, coreProgram.indexOf? (fkFn (8 + t)).name = some (205 + (8 + t)) := by
  decide +kernel

theorem fk_index_16 : ∀ t < 8, coreProgram.indexOf? (fkFn (16 + t)).name = some (205 + (16 + t)) := by
  decide +kernel

theorem fk_index_24 : ∀ t < 8, coreProgram.indexOf? (fkFn (24 + t)).name = some (205 + (24 + t)) := by
  decide +kernel

theorem fk_index_32 : ∀ t < 8, coreProgram.indexOf? (fkFn (32 + t)).name = some (205 + (32 + t)) := by
  decide +kernel

theorem fk_index_40 : ∀ t < 8, coreProgram.indexOf? (fkFn (40 + t)).name = some (205 + (40 + t)) := by
  decide +kernel

theorem fk_index_48 : ∀ t < 8, coreProgram.indexOf? (fkFn (48 + t)).name = some (205 + (48 + t)) := by
  decide +kernel

theorem fk_index_56 : ∀ t < 8, coreProgram.indexOf? (fkFn (56 + t)).name = some (205 + (56 + t)) := by
  decide +kernel

/-- Forest keys `0 + t` are found by name at `205 + 0 + t`. -/
theorem fk_index_0_all : ∀ t < 64, coreProgram.indexOf? (fkFn (0 + t)).name = some (205 + (0 + t)) := by
  intro t ht
  obtain ⟨q, hq, r, hr, rfl⟩ : ∃ q < 8, ∃ r < 8, t = 8 * q + r := ⟨t / 8, by omega, t % 8, by omega, by omega⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show 0 + (8 * 0 + r) = 0 + r by omega]; exact fk_index_0 r hr
  · rw [show 0 + (8 * 1 + r) = 8 + r by omega]; exact fk_index_8 r hr
  · rw [show 0 + (8 * 2 + r) = 16 + r by omega]; exact fk_index_16 r hr
  · rw [show 0 + (8 * 3 + r) = 24 + r by omega]; exact fk_index_24 r hr
  · rw [show 0 + (8 * 4 + r) = 32 + r by omega]; exact fk_index_32 r hr
  · rw [show 0 + (8 * 5 + r) = 40 + r by omega]; exact fk_index_40 r hr
  · rw [show 0 + (8 * 6 + r) = 48 + r by omega]; exact fk_index_48 r hr
  · rw [show 0 + (8 * 7 + r) = 56 + r by omega]; exact fk_index_56 r hr

end
end LeanVM.Guest.B1.Sig
