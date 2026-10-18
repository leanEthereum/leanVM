/-
  LeanVM.Guest.B1.Sig.SphincsFk1

  The forest-key specializations `sp_forest_key__L{t}`, 64 ≤ t < 128, in the guest's core IR are
  the templates `fkBody t`, found by their names (in groups of eight, each name compared with all
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
theorem fk_data_64 : ∀ t < 64, (coreProgram[205 + (64 + t)]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn (64 + t)).name, (fkFn (64 + t)).params, (fkFn (64 + t)).body) := by
  decide +kernel

theorem fk_index_64 : ∀ t < 8, coreProgram.indexOf? (fkFn (64 + t)).name = some (205 + (64 + t)) := by
  decide +kernel

theorem fk_index_72 : ∀ t < 8, coreProgram.indexOf? (fkFn (72 + t)).name = some (205 + (72 + t)) := by
  decide +kernel

theorem fk_index_80 : ∀ t < 8, coreProgram.indexOf? (fkFn (80 + t)).name = some (205 + (80 + t)) := by
  decide +kernel

theorem fk_index_88 : ∀ t < 8, coreProgram.indexOf? (fkFn (88 + t)).name = some (205 + (88 + t)) := by
  decide +kernel

theorem fk_index_96 : ∀ t < 8, coreProgram.indexOf? (fkFn (96 + t)).name = some (205 + (96 + t)) := by
  decide +kernel

theorem fk_index_104 : ∀ t < 8, coreProgram.indexOf? (fkFn (104 + t)).name = some (205 + (104 + t)) := by
  decide +kernel

theorem fk_index_112 : ∀ t < 8, coreProgram.indexOf? (fkFn (112 + t)).name = some (205 + (112 + t)) := by
  decide +kernel

theorem fk_index_120 : ∀ t < 8, coreProgram.indexOf? (fkFn (120 + t)).name = some (205 + (120 + t)) := by
  decide +kernel

/-- Forest keys `64 + t` are found by name at `205 + 64 + t`. -/
theorem fk_index_64_all : ∀ t < 64, coreProgram.indexOf? (fkFn (64 + t)).name = some (205 + (64 + t)) := by
  intro t ht
  obtain ⟨q, hq, r, hr, rfl⟩ : ∃ q < 8, ∃ r < 8, t = 8 * q + r := ⟨t / 8, by omega, t % 8, by omega, by omega⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show 64 + (8 * 0 + r) = 64 + r by omega]; exact fk_index_64 r hr
  · rw [show 64 + (8 * 1 + r) = 72 + r by omega]; exact fk_index_72 r hr
  · rw [show 64 + (8 * 2 + r) = 80 + r by omega]; exact fk_index_80 r hr
  · rw [show 64 + (8 * 3 + r) = 88 + r by omega]; exact fk_index_88 r hr
  · rw [show 64 + (8 * 4 + r) = 96 + r by omega]; exact fk_index_96 r hr
  · rw [show 64 + (8 * 5 + r) = 104 + r by omega]; exact fk_index_104 r hr
  · rw [show 64 + (8 * 6 + r) = 112 + r by omega]; exact fk_index_112 r hr
  · rw [show 64 + (8 * 7 + r) = 120 + r by omega]; exact fk_index_120 r hr

end
end LeanVM.Guest.B1.Sig
