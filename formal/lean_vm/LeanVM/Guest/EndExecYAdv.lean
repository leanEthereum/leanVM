/-
  LeanVM.Guest.EndExecYAdv

  Two facts of the guest's advice the hint track reads, decided by the kernel: every advised size is
  popped from `heap_sizes`, and every heap witness run's offset and length are small.
-/

module

public import LeanVM.Guest.Data.AdviceHints
public import LeanVM.Guest.Hints

/-!
# The advice's streams

`advHintOk h`: an `allocAdvice` pops `heap_sizes`, a heap witness run's offset and length are below
`2^30`. `adviceHints_ok`: every hint of the advice passes it.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Prover.Exec

@[expose] public section

/-- What the hint track reads of an advice hint's constants. -/
def advHintOk : Hint → Bool
  | .allocAdvice _ S => S == Hints.heapSizeStream
  | .witnessHeap _ _ lo len => Nat.blt (lo + len) (2 ^ 30)
  | _ => true

end

public section

theorem adviceHints_ok : Data.adviceHints.all (fun p ↦ p.2.all advHintOk) = true := by decide +kernel

end

end LeanVM.Guest.EndExec
