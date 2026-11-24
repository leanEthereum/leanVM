/-
  LeanVM.Guest.B1.Place.KidsE

  Callees complete by trees of exactly given words, placed in sequence: their total is the sum.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt

/-!
# Exact callees in sequence

`kidsN fs ns ks`: the total of callees each complete at `ns k` words (an entered callee's `ns k`, a skipped one's
tail frame, `fs (tailKey f)`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The callees' total: an entered callee's `ns k` words, a skipped one's tail frame. -/
def kidsN (fs : String → ℕ) (ns : Kid → ℕ) (ks : List Kid) : ℕ :=
  (ks.map fun k ↦ if k.taken then ns k else fs (tailKey k.f)).sum

end
end LeanVM.Guest.B1
