/-
  Rv64mc.Spec.Layout.Repr

  How `layout.rs`'s values sit in memory, each at the offsets of `Gen/Layouts.lean`:

  * `ElemsAt size P`: consecutive elements of `size` bytes, element `k` at `a + size k` read by `P`;
  * `OptPlacementAt`: an `Option<Placement>` (its tag, then the placement's `variables` and `index`);
  * `ResultPlacementAt`: the `Result<Placement, VerifierError>` a function returns through `sret`, `Err` being
    `CommittedSize`;
  * `FormIn`: a `Form` (`Vec<(Vec<usize>, E)>`) whose buffers all lie in `[lo, hi)` (`Region`), so that it is kept
    by whatever keeps that region and its header (`FormIn.keep`). The bump allocator never frees, so what one call
    allocates is such a region (`[NEXT before, NEXT after)`), apart from everything older.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier

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

/-! ## `Form` -/

/-- `[q, q + n)` lies in `[lo, hi)`. -/
def Region (lo hi q : Word) (n : Nat) : Prop := lo.toNat ≤ q.toNat ∧ q.toNat + n ≤ hi.toNat

/-- `[a, a + n)` lies outside `[lo, hi)`. -/
def Apart (lo hi a : Word) (n : Nat) : Prop := a.toNat + n ≤ lo.toNat ∨ hi.toNat ≤ a.toNat

/-- The `usize`s `ns` from `a`. -/
def UsizesAt (m : MachineState) (a : Word) (ns : List Nat) : Prop := WordsAt m a (ns.map (BitVec.ofNat 64))

/-- A buffer of `cap` elements of `size` bytes at `q`, in `[lo, hi)` unless it holds none. -/
def BufIn (lo hi q : Word) (cap size : Nat) : Prop := cap = 0 ∨ Region lo hi q (size * cap)

/-- **The term `t` at `a`**: its monomial's `Vec` and its coefficient's limbs, the monomial's buffer in
    `[lo, hi)`. -/
def TermIn (lo hi : Word) (m : MachineState) (a : Word) (t : List Nat × E) : Prop :=
  ∃ q cap, VecAt UsizesAt m a q cap t.1 ∧ BufIn lo hi q cap 8 ∧
    EAt m (a + BitVec.ofNat 64 Layouts.VecUsizeE.f1) (Model.limbs t.2)

/-- **The `Form` `f` at `a`**: its terms in order, every buffer in `[lo, hi)`. -/
def FormIn (lo hi : Word) (m : MachineState) (a : Word) (f : Form) : Prop :=
  ∃ q cap, VecAt (ElemsAt Layouts.VecUsizeE.byteSize (TermIn lo hi)) m a q cap f.terms ∧
    BufIn lo hi q cap Layouts.VecUsizeE.byteSize

end Rv64mc.Spec.Layout
