/-
  LeanVM.Guest.B1.Sig.SphincsFk3

  The forest-key specializations `sp_forest_key__L{t}`, 192 ≤ t < 256, in the guest's core IR are
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
theorem fk_data_192 : ∀ t < 64, (coreProgram[205 + (192 + t)]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn (192 + t)).name, (fkFn (192 + t)).params, (fkFn (192 + t)).body) := by
  decide +kernel

theorem fk_index_192 : ∀ t < 8, coreProgram.indexOf? (fkFn (192 + t)).name = some (205 + (192 + t)) := by
  decide +kernel

theorem fk_index_200 : ∀ t < 8, coreProgram.indexOf? (fkFn (200 + t)).name = some (205 + (200 + t)) := by
  decide +kernel

theorem fk_index_208 : ∀ t < 8, coreProgram.indexOf? (fkFn (208 + t)).name = some (205 + (208 + t)) := by
  decide +kernel

theorem fk_index_216 : ∀ t < 8, coreProgram.indexOf? (fkFn (216 + t)).name = some (205 + (216 + t)) := by
  decide +kernel

theorem fk_index_224 : ∀ t < 8, coreProgram.indexOf? (fkFn (224 + t)).name = some (205 + (224 + t)) := by
  decide +kernel

theorem fk_index_232 : ∀ t < 8, coreProgram.indexOf? (fkFn (232 + t)).name = some (205 + (232 + t)) := by
  decide +kernel

theorem fk_index_240 : ∀ t < 8, coreProgram.indexOf? (fkFn (240 + t)).name = some (205 + (240 + t)) := by
  decide +kernel

theorem fk_index_248 : ∀ t < 8, coreProgram.indexOf? (fkFn (248 + t)).name = some (205 + (248 + t)) := by
  decide +kernel

/-- Forest keys `192 + t` are found by name at `205 + 192 + t`. -/
theorem fk_index_192_all : ∀ t < 64, coreProgram.indexOf? (fkFn (192 + t)).name = some (205 + (192 + t)) := by
  intro t ht
  obtain ⟨q, hq, r, hr, rfl⟩ : ∃ q < 8, ∃ r < 8, t = 8 * q + r := ⟨t / 8, by omega, t % 8, by omega, by omega⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show 192 + (8 * 0 + r) = 192 + r by omega]; exact fk_index_192 r hr
  · rw [show 192 + (8 * 1 + r) = 200 + r by omega]; exact fk_index_200 r hr
  · rw [show 192 + (8 * 2 + r) = 208 + r by omega]; exact fk_index_208 r hr
  · rw [show 192 + (8 * 3 + r) = 216 + r by omega]; exact fk_index_216 r hr
  · rw [show 192 + (8 * 4 + r) = 224 + r by omega]; exact fk_index_224 r hr
  · rw [show 192 + (8 * 5 + r) = 232 + r by omega]; exact fk_index_232 r hr
  · rw [show 192 + (8 * 6 + r) = 240 + r by omega]; exact fk_index_240 r hr
  · rw [show 192 + (8 * 7 + r) = 248 + r by omega]; exact fk_index_248 r hr

end
end LeanVM.Guest.B1.Sig
