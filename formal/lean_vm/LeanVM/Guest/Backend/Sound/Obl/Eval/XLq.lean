/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XLq

  The `level_queries` specializations pass `lqOk`, by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Lq
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `0` to `47` of `lqTab` pass their check.** -/
theorem evalLq_0 : ((lqTab.drop 0).take 48).all (fun e => lqOk e.1 e.2.1 e.2.2) = true := by
  decide +kernel

/-- **Entries `48` to `95` of `lqTab` pass their check.** -/
theorem evalLq_48 : ((lqTab.drop 48).take 48).all (fun e => lqOk e.1 e.2.1 e.2.2) = true := by
  decide +kernel

/-- **Entries `96` to `143` of `lqTab` pass their check.** -/
theorem evalLq_96 : ((lqTab.drop 96).take 48).all (fun e => lqOk e.1 e.2.1 e.2.2) = true := by
  decide +kernel

/-- **Entries `144` to `190` of `lqTab` pass their check.** -/
theorem evalLq_144 : ((lqTab.drop 144).take 47).all (fun e => lqOk e.1 e.2.1 e.2.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
