module

public import LeanVM.Guest.Complete.Claims.Cover
public import LeanVM.Guest.Complete.RawFields

/-!
# The honest coverage table's raw marks

`rawMarks_honest`: `honestCover` holds the raw signatures' marks (`RawMarks`), so `rawx_field` and
`raws_field` hold at the shared cover.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem getElem?_of_getD {l : List E} {t : ℕ} {v : E} (ht : t < l.length) (h : l.getD t 0 = v) :
    l[t]? = some v := by
  rw [List.getD_eq_getElem _ _ ht] at h
  rw [List.getElem?_eq_getElem ht, h]

/-- **The honest coverage table holds the raw signatures' marks.** -/
theorem rawMarks_honest (s : NodeStatement) (w : NodeWitness) : RawMarks s w (honestCover s w) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : i < (xPlan s w).directSlots.length := by rw [xPlan_directSlots_length]; exact hi
    obtain ⟨hlt, h⟩ := honestCover_rawx s w hi'
    rw [List.getD_eq_getElem _ _ hi']
    exact getElem?_of_getD (by rw [honestCover_length]; omega) h
  · have hi' : i < (sPlan s w).directSlots.length := by rw [sPlan_directSlots_length]; exact hi
    obtain ⟨hlt, h⟩ := honestCover_raws s w hi'
    rw [List.getD_eq_getElem _ _ hi']
    rw [← pow_add] at h
    exact getElem?_of_getD (by rw [honestCover_length]; omega) h

end
end LeanVM.Guest.Complete
