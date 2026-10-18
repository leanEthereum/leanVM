/-
  LeanVM.Guest.B1.Sig.SphincsFk2

  The forest-key specializations `sp_forest_key__L{t}`, 128 ≤ t < 192, in the guest's core IR are
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
theorem fk_data_128 : ∀ t < 64, (coreProgram[205 + (128 + t)]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn (128 + t)).name, (fkFn (128 + t)).params, (fkFn (128 + t)).body) := by
  decide +kernel

theorem fk_index_128 : ∀ t < 8, coreProgram.indexOf? (fkFn (128 + t)).name = some (205 + (128 + t)) := by
  decide +kernel

theorem fk_index_136 : ∀ t < 8, coreProgram.indexOf? (fkFn (136 + t)).name = some (205 + (136 + t)) := by
  decide +kernel

theorem fk_index_144 : ∀ t < 8, coreProgram.indexOf? (fkFn (144 + t)).name = some (205 + (144 + t)) := by
  decide +kernel

theorem fk_index_152 : ∀ t < 8, coreProgram.indexOf? (fkFn (152 + t)).name = some (205 + (152 + t)) := by
  decide +kernel

theorem fk_index_160 : ∀ t < 8, coreProgram.indexOf? (fkFn (160 + t)).name = some (205 + (160 + t)) := by
  decide +kernel

theorem fk_index_168 : ∀ t < 8, coreProgram.indexOf? (fkFn (168 + t)).name = some (205 + (168 + t)) := by
  decide +kernel

theorem fk_index_176 : ∀ t < 8, coreProgram.indexOf? (fkFn (176 + t)).name = some (205 + (176 + t)) := by
  decide +kernel

theorem fk_index_184 : ∀ t < 8, coreProgram.indexOf? (fkFn (184 + t)).name = some (205 + (184 + t)) := by
  decide +kernel

/-- Forest keys `128 + t` are found by name at `205 + 128 + t`. -/
theorem fk_index_128_all : ∀ t < 64, coreProgram.indexOf? (fkFn (128 + t)).name = some (205 + (128 + t)) := by
  intro t ht
  obtain ⟨q, hq, r, hr, rfl⟩ : ∃ q < 8, ∃ r < 8, t = 8 * q + r := ⟨t / 8, by omega, t % 8, by omega, by omega⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show 128 + (8 * 0 + r) = 128 + r by omega]; exact fk_index_128 r hr
  · rw [show 128 + (8 * 1 + r) = 136 + r by omega]; exact fk_index_136 r hr
  · rw [show 128 + (8 * 2 + r) = 144 + r by omega]; exact fk_index_144 r hr
  · rw [show 128 + (8 * 3 + r) = 152 + r by omega]; exact fk_index_152 r hr
  · rw [show 128 + (8 * 4 + r) = 160 + r by omega]; exact fk_index_160 r hr
  · rw [show 128 + (8 * 5 + r) = 168 + r by omega]; exact fk_index_168 r hr
  · rw [show 128 + (8 * 6 + r) = 176 + r by omega]; exact fk_index_176 r hr
  · rw [show 128 + (8 * 7 + r) = 184 + r by omega]; exact fk_index_184 r hr

end
end LeanVM.Guest.B1.Sig
