/-
  LeanVM.Guest.B1.Whir.CapDepthOk

  Every level's cap depth (`LIG_CAP_DEPTH`) is the hint generator's (`Hints.capDepthOf` of its query count and depth), at every size and rate.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import LeanVM.Guest.Hints

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Every level's cap depth is the generator's, at every size and rate. -/
def capDepthB : Bool :=
  (List.range ligNSizes).all fun m => (List.range 4).all fun ri =>
    (osLevelsR m ri).all fun lv => lv.capDepth == Hints.capDepthOf lv.queries lv.depth

theorem capDepthB_ok : capDepthB = true := by decide +kernel

/-- **A level's cap depth is the generator's.** -/
theorem capDepth_eq {m ri : ℕ} (hm : m < ligNSizes) (hr : ri < 4) {lv : OsLv} (hl : lv ∈ osLevelsR m ri) :
    lv.capDepth = Hints.capDepthOf lv.queries lv.depth := by
  have h := capDepthB_ok
  simp only [capDepthB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h m hm ri hr lv hl

end
end LeanVM.Guest.B1.Whir
