/-
  LeanVM.Guest.B1.VsC.Os.Left

  What is left of `open_stacked`'s placed completeness, stated.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LqMain
public import LeanVM.Guest.B1.VsC.Oq.LqHints
public import LeanVM.Guest.B1.VsC.OpenStackedA
public import LeanVM.Guest.B2C.Defs

/-!
# `open_stacked`: what is left

`level_queries` is complete at any second argument (`LqAG`, `LqAllG`, `lqAG_all` in
`Oq/LqMain.lean`), and the body's honest data is proved (`os_honest_proved`,
`Os/CHonest.lean`; at a call, `osHonest_of_open`, `Os/LeftPre.lean`).

`OsLeft al k`: the lift, `open_stacked__L{m}` complete placed at every `m ≤ 14` from `level_queries`'
completeness; `osLeft_of_c`: it follows from `OsLeftC al k`, the lift from the honest cap of
`level_queries` (`LqCapHonest`, which a sibling proves), since `LqAllG` holds (`lqAG_all`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **What is left of `open_stacked`**: placed at every size from `level_queries`' completeness. -/
def OsLeft (al : String → Bool) (k : ℕ) : Prop :=
  LqAllG B2C.fs al B2C.cert k → ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs al B2C.cert k m

/-- **What is left of `open_stacked`, `level_queries` discharged**: placed at every size from the
honest cap of `level_queries`. -/
def OsLeftC (al : String → Bool) (k : ℕ) : Prop :=
  LqCapHonest → ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs al B2C.cert k m

theorem osLeft_of_c {al : String → Bool} {k : ℕ} (h : OsLeftC al k) (hc : LqCapHonest) : OsLeft al k :=
  fun _ => h hc

end
end LeanVM.Guest.B1.VsC
