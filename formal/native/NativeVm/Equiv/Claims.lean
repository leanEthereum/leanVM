module

public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Field

/-!
# Column claims on the stack

`ColumnClaimW.onStack_toSpec`: a column claim's stack claim is the statement's
(`StackClaimW.Rel`), `none` exactly where the statement's is: the placement read from the same
array, the point on the stack `stackPoint_toSpec`, the weight `eqEval` of it (`toE_eqEval`).
-/

@[expose] public section

namespace NativeVm.Model

open NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol

/-- `Placement::stack_point`. -/
theorem stackPoint_toSpec (p : Verifier.Placement) (point : Array EW) (stackLog : ℕ) :
    (stackPoint p point stackLog).toList.map EW.toE =
      p.stackPoint (point.toList.map EW.toE) stackLog := by
  simp [stackPoint, Verifier.Placement.stackPoint, toList_map_selectorPoint]

/-- `ColumnClaim::on_stack`: the claim on the stack is the statement's. -/
theorem ColumnClaimW.onStack_toSpec (c : ColumnClaimW) (layout : LayoutW) :
    Option.Rel StackClaimW.Rel (c.onStack layout) (c.toSpec.onStack layout.toSpec) := by
  unfold ColumnClaimW.onStack Verifier.ColumnClaim.onStack
  simp only [LayoutW.toSpec, ColumnClaimW.toSpec, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rcases (layout.placements[c.column]?).getD none with _ | p
  · exact .none
  · refine .some ⟨fun x ↦ ?_, rfl⟩
    simp only [StackWeight.eval]
    rw [toE_eqEval, stackPoint_toSpec]

end NativeVm.Model
