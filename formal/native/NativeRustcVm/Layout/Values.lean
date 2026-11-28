module

public import NativeRustcVm.Layout.Rep
public import NativeRustcVm.Rodata
public import NativeRustcVm.Whir.Rep

/-!
# The values the layout's functions hand back

- `formAt form`: the form `form_terms(form)` returns, the `form`th of the data's forms
  (`Data.allForms`, the statement's tables' tuples, form by form) as `FormW`, empty past them.
- `sortLt size`: `stack_offsets`'s order, largest first, ties by index (`stackOffsets`' `lt`).
- `OffsetsFit sizes`: `stack_offsets` lays the blocks out in a `u64`: every size below `64`, the
  total below `2 ^ 64`.
- `OodAt d a c`: the `EqClaimW` at `a` holds the stack claim `c`, an equality claim.
- `LadderAt d a r`: the `Option<([Level; 6], usize)>` at `a` (160 bytes: tag word, the levels
  from byte `8`, the count at byte `152`) holds `r`, `Whir.ladder`'s levels.
-/

namespace NativeRustcVm.Layout

open NativeVm.Model LeanVM.Parameters
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The `form`th form of the data (`FORMS`, `TERMS`), empty past them. -/
def formAt (form : Nat) : FormW := ((Data.allForms[form]?).map FormW.ofForm).getD #[]

/-- `stack_offsets`'s order on block indices, `size` their log-sizes. -/
def sortLt (size : Nat → Nat) (i j : Nat) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i < j))

/-- Blocks of these log-sizes fit a `u64` end to end. -/
def OffsetsFit (sizes : Array Nat) : Prop :=
  (∀ s ∈ sizes, s < 64) ∧ (sizes.toList.map (2 ^ ·)).sum < 2 ^ 64

instance (sizes : Array Nat) : Decidable (OffsetsFit sizes) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The `EqClaimW` at `a` holds the equality claim `c`. -/
def OodAt (d : Mem 64) (a : BitVec 64) (c : StackClaimW) : Prop :=
  ∃ z, c.weight = .eq z ∧ EqClaimAt d a z c.value

/-- `LEVEL_CAP`: the longest ladder. -/
def levelCap : Nat := 6

/-- `ladder`'s result's bytes. -/
def ladderBytes : Nat := 160

/-- **`ladder`'s result** at `a`: tag word `0` for `none`; `1`, at most `levelCap` levels from
byte `8` and their count at byte `152` for `some`. -/
def LadderAt (d : Mem 64) (a : BitVec 64) : Option (List Whir.Level) → Prop
  | none => WordAt d a 0
  | some ls => WordAt d a 1 ∧ ls.length ≤ levelCap ∧
      WordAt d (off a 152) ls.length.toUInt64 ∧ NativeRustcVm.Whir.LevelsAt d (off a 8) ls

end

end NativeRustcVm.Layout
