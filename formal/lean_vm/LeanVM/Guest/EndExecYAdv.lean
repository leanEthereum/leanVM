/-
  LeanVM.Guest.EndExecYAdv

  Facts of the guest's advice the hint track reads, decided by the kernel: every heap witness run's
  offset and length are small, and every run a hint writes or reads is nonempty.
-/

module

public import Statement.Data.AdviceHints
import all Statement.Data.AdviceHints
public import LeanVM.Guest.Hints
public import LeanVM.Guest.Mode.HintsCtx

/-!
# The advice's streams

`advHintOk h`: a heap witness run's offset and length are below `2^30`. `adviceHints_ok`: every hint of the advice passes it. `posHintOk h`: the run a hint writes or
reads is nonempty, so its last cell bounds it (`runAt`); `hints_pos`: every hint the executor runs
passes it.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Prover.Exec

@[expose] public section

/-- What the hint track reads of an advice hint's constants. -/
def advHintOk : Hint → Bool
  | .witnessHeap _ _ lo len => Nat.blt (lo + len) (2 ^ 30)
  | _ => true

/-- The run a hint writes or reads is nonempty. -/
def posHintOk : Hint → Bool
  | .witnessStack _ _ len | .witnessHeap _ _ _ len | .fieldLimbs _ _ len => Nat.blt 0 len
  | .log2Ceil _ _ nbits _ | .bitDecompose _ _ nbits | .bitDecomposeExp _ _ nbits => Nat.blt 0 nbits
  | .digitDecomposeExp _ _ _ ndigits _ _ _ => Nat.blt 0 ndigits
  | .windowsExp _ _ _ _ _ count => Nat.blt 0 count
  | _ => true

end

public section

theorem adviceHints_ok : Data.adviceHints.all (fun p ↦ p.2.all advHintOk) = true := by decide +kernel

theorem adviceHints_pos : Data.adviceHints.all (fun p ↦ p.2.all posHintOk) = true := by decide +kernel

/-- **Every hint the executor runs on the guest's advice has a nonempty run.** -/
theorem hints_pos {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints)
    {pc : ℕ} (hpc : pc < 2 ^ guestProgram.logSize) : ∀ h ∈ (C.hints[pc]?).getD [], posHintOk h = true := by
  intro h hh
  rw [Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpc, ha] at hh
  unfold Mode.hintsAt at hh
  split at hh
  · rename_i p hp
    exact List.all_eq_true.mp (List.all_eq_true.mp adviceHints_pos p (List.mem_of_find?_eq_some hp)) h hh
  · cases hh

end

end LeanVM.Guest.EndExec
