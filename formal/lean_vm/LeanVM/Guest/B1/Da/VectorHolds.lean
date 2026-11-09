/-
  LeanVM.Guest.B1.Da.VectorHolds

  `da_factors`, `da_expand`, `da_column_offsets` and `da_vector`: their core IR gives their
  meanings.
-/

module

public import LeanVM.Guest.B1.Da.FactorsChk
public import LeanVM.Guest.B1.Da.ExpandChk
public import LeanVM.Guest.B1.Da.OffsetsChk
public import LeanVM.Guest.B1.Da.VecFnChk

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core

@[expose] public section

/-- **`da_factors`' core IR gives its meaning**, at both specializations. -/
theorem da_factors_holds : da_factors_sound_Spec := by
  refine ⟨fun rd args rets hrel ↦ ?_, fun rd args rets hrel ↦ ?_⟩
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_factors_L14_L7_L0 _ _).mp hrel
    exact da_factors_val fac14_ok (by norm_num) hpar hb
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_factors_L7_L8_L128 _ _).mp hrel
    exact da_factors_val fac7_ok (by norm_num) hpar hb

/-- **`da_expand`'s core IR gives its meaning**, at both specializations. -/
theorem da_expand_holds : da_expand_sound_Spec := by
  refine ⟨fun rd args rets hrel ↦ ?_, fun rd args rets hrel ↦ ?_⟩
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_expand_L14_L7 _ _).mp hrel
    exact da_expand_val exp7_ok (by norm_num) (by norm_num) hpar hb
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_expand_L7_L8 _ _).mp hrel
    exact da_expand_val exp8_ok (by norm_num) (by norm_num) hpar hb

/-- **`da_column_offsets`' core IR gives its meaning.** -/
theorem da_column_offsets_holds : da_column_offsets_sound_Spec := fun rd args rets hrel ↦ by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_column_offsets _ _).mp hrel
  exact da_column_offsets_val off_ok offLoop_ok offLoop_idx hpar hb

/-- **`da_vector`'s core IR gives its meaning.** -/
theorem da_vector_holds : da_vector_sound_Spec :=
  da_vector_val vec_ok da_factors_holds da_expand_holds da_column_offsets_holds

end
end LeanVM.Guest.B1.Da
