import SphincsSecurity.Proof.Ots.OtsTraceRows
import SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
namespace SphincsSecurity.Concrete.PartialChainEndpoint

set_option backward.isDefEq.respectTransparency false

theorem twoEdgeEvent_iff_rows {State : Type} {depth : Nat} (observed : Fin depth → State → Option State) (endpoint : State) :
    TwoEdgeEvent observed endpoint ↔ ∃ first last : Fin depth × State,
      first.1.val + 2 = depth ∧ last.1.val + 1 = depth ∧
        observed first.1 first.2 = some last.2 ∧ observed last.1 last.2 = some endpoint := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, Prod.exists, Fin.exists_fin_zero]
  | succ depth =>
      cases depth with
      | zero =>
          constructor
          · exact False.elim
          · rintro ⟨first, _, hf, _⟩
            omega
      | succ depth =>
          constructor
          · rintro ⟨start, middle, hf, hl⟩
            exact ⟨⟨(Fin.last depth).castSucc, start⟩, ⟨Fin.last (depth + 1), middle⟩, rfl, rfl, hf, hl⟩
          · rintro ⟨⟨first, start⟩, ⟨last, middle⟩, hf, hl, hfirst, hlast⟩
            change first.val + 2 = depth + 2 at hf
            change last.val + 1 = depth + 2 at hl
            have hfi : first = (Fin.last depth).castSucc := by
              apply Fin.ext
              simp only [Fin.val_castSucc, Fin.val_last]
              omega
            have hla : last = Fin.last (depth + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            subst first last
            exact ⟨start, middle, hfirst, hlast⟩

end SphincsSecurity.Concrete.PartialChainEndpoint

namespace SphincsSecurity.Concrete.OtsContactTrace

set_option backward.isDefEq.respectTransparency false

def SeenTwoEdge (segment : OtsPrefix) (endpoint : Digest) (trace : Trace) : Prop :=
  ∃ first last : segment.Query, first.1.val + 2 = segment.digit.val ∧ last.1.val + 1 = segment.digit.val ∧
    SeenRow segment first last.2 trace ∧ SeenRow segment last endpoint trace

theorem RowsObserved.twoEdge_iff {segment : OtsPrefix} {trace : Trace} {observed : Fin segment.digit.val → Digest → Option Digest}
    (h : RowsObserved segment trace observed) (endpoint : Digest) :
    SeenTwoEdge segment endpoint trace ↔ PartialChainEndpoint.TwoEdgeEvent observed endpoint := by
  dsimp only [RowsObserved] at h
  simp only [SeenTwoEdge, h, PartialChainEndpoint.twoEdgeEvent_iff_rows]

end SphincsSecurity.Concrete.OtsContactTrace
