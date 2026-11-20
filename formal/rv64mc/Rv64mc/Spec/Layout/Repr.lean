/-
  Rv64mc.Spec.Layout.Repr

  How `layout.rs`'s values sit in memory, each at the offsets of `Gen/Layouts.lean`:

  * `ElemsAt size P`: consecutive elements of `size` bytes, element `k` at `a + size k` read by `P`;
  * `OptPlacementAt`: an `Option<Placement>` (its tag, then the placement's `variables` and `index`);
  * `ResultPlacementAt`: the `Result<Placement, VerifierError>` a function returns through `sret`, `Err` being
    `CommittedSize`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout

open RiscvZkvm.Rv64

/-- **The elements `xs` from `a`**, each of `size` bytes, element `k` at `a + size k` read by `P`. -/
def ElemsAt {α : Type} (size : Nat) (P : MachineState → Word → α → Prop) (m : MachineState) (a : Word)
    (xs : List α) : Prop :=
  a.toNat + size * xs.length < 2 ^ 64 ∧ ∀ k (h : k < xs.length), P m (a + BitVec.ofNat 64 (size * k)) xs[k]

/-- The `Option<Placement>` `o` at `a`: tag `0` for `None`, else tag `1` and the placement's two words. -/
def OptPlacementAt (m : MachineState) (a : Word) : Option Model.PlacementRust → Prop
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.OptionPlacement.tagOffset) =
      BitVec.ofNat 64 Layouts.OptionPlacement.None.tag
  | some p => m.getMem (a + BitVec.ofNat 64 Layouts.OptionPlacement.tagOffset) =
        BitVec.ofNat 64 Layouts.OptionPlacement.Some.tag ∧
      m.getMem (a + BitVec.ofNat 64 (Layouts.OptionPlacement.Some.f0 + Layouts.Placement.variables)) =
        BitVec.ofNat 64 p.variableCount ∧
      m.getMem (a + BitVec.ofNat 64 (Layouts.OptionPlacement.Some.f0 + Layouts.Placement.index)) = p.index

/-- **The `Result<Placement, VerifierError>` at `a`**: `Ok` with the placement, or `Err(CommittedSize)` where
    there is none. -/
def ResultPlacementAt (m : MachineState) (a : Word) : Option Model.PlacementRust → Prop
  | some p => m.getMem (a + BitVec.ofNat 64 Layouts.ResultPlacement.tagOffset) =
        BitVec.ofNat 64 Layouts.ResultPlacement.Ok.tag ∧
      m.getMem (a + BitVec.ofNat 64 (Layouts.ResultPlacement.Ok.f0 + Layouts.Placement.variables)) =
        BitVec.ofNat 64 p.variableCount ∧
      m.getMem (a + BitVec.ofNat 64 (Layouts.ResultPlacement.Ok.f0 + Layouts.Placement.index)) = p.index
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultPlacement.tagOffset) =
        BitVec.ofNat 64 Layouts.ResultPlacement.Err.tag ∧
      m.getMem (a + BitVec.ofNat 64 Layouts.ResultPlacement.Err.f0) =
        BitVec.ofNat 64 Layouts.VerifierError.CommittedSize.tag

end Rv64mc.Spec.Layout
