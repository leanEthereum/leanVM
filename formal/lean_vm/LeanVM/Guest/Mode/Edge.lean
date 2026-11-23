module

public import LeanVM.Guest.Mode.Step
/-!
# The program's view and a return's registers

`EnvSmall`: the program's pcs are small, its signatures' and its jump table's. `ret_regs`: a return
from a frame whose header names `r` and `fp` goes there.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- The program's pcs are small: its signatures' and its jump table's. -/
def EnvSmall (En : Env) : Prop :=
  (∀ t G, En.sigs.get t = some G → t < 2 ^ 62) ∧ ∀ d e, En.jt.get d = some e → e < 2 ^ 62

/-- **A return's registers**: a frame whose header names `r` and `fp` returns there. -/
theorem ret_regs {s s' : St} {r fp : ℕ} (hr : r < 2 ^ 62) (hfp : fp < maxCells)
    (h0 : s.mem.get (s.fp + 0) = some (ofK (g ^ r))) (h1 : s.mem.get (s.fp + 1) = some (ofK (g ^ fp)))
    (hpc' : s'.pc < 2 ^ 62) (hfp' : s'.fp < maxCells)
    (hd : s.mem.get (s.fp + 0) = some (ofK (g ^ s'.pc)))
    (hf : s.mem.get (s.fp + 1) = some (ofK (g ^ s'.fp))) : s'.pc = r ∧ s'.fp = fp := by
  rw [h0] at hd
  rw [h1] at hf
  exact ⟨gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hd)).symm,
    gpow_inj (by unfold maxCells at hfp'; omega) (by unfold maxCells at hfp; omega)
      (ofK_injective (Option.some.inj hf)).symm⟩

end

end LeanVM.Guest.Mode
