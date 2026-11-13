/-
  LeanVM.Guest.B1.Whir.RoundFind

  `opening_round` in the guest: found in `coreProgram`, and `Round.lean`'s soundness there.
-/

module

public import LeanVM.Guest.B1.Whir.RoundSound
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_opening_round : coreProgram.find? "opening_round" = some Fn.«opening_round».core :=
  coreProgram_find?_at (j := idx% «opening_round») rfl

instance finds_opening_round : Finds coreProgram "opening_round" Fn.«opening_round».core := ⟨find_opening_round⟩

/-- **`opening_round`'s core IR gives its meaning** (`opening_round_soundP`). -/
theorem opening_round_sound (hg : grind_check_Spec 7) {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ)
    (L : MemoryImage κ) (args rets : List E) (ht : WinTabs L.read (args.getD 7 0))
    (h : coreProgram.Rel L.read "opening_round" args rets) : MeaningOpeningRound L.read args rets :=
  opening_round_soundP coreProgram hg hκ hw L args rets ht h

end
end LeanVM.Guest.B1.Whir
