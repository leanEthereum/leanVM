/-
  LeanVM.Guest.B1.Digest.LoopAtB

  A loop of atoms placing nothing, complete within a bound before the memory: its frame once per
  iteration and once for the phantom tail (`loopA_stepAt` with the bound).
-/

module

public import LeanVM.Guest.B1.Digest.LoopAt
public import LeanVM.Guest.Budget.Bounded

/-!
# Loops of atoms, placed within bounds

`loopA_completeAtB`: `loopA_completeAt` within `(m - k + 1) · fs f` words: one frame per
iteration from `g^k`, one for the call not entered at the end (`loopA_stepAt` with the bound).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtD CompleteAtDTB CompleteAtL Returns DisjL Within disj_append
  within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **A loop of atoms is complete, placed**, from every counter below its end, within one frame
per iteration and one for the phantom (`loopA_stepAt` with the bound). -/
theorem loopA_completeAtB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34)
    (hblk : ∀ k < m, LoopBlockIn κ fn Lin k N rest) :
    ∀ k < m, CompleteAtDTB fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) (fun _ => True)
      ((m - k + 1) * fs f) := by
  have key : ∀ t k, k + 1 + t = m → CompleteAtL fs cert κ f Lin (gen ^ k :: N :: rest)
      (Returns []) (fun _ => True) (· ≤ (t + 2) * fs f) := by
    intro t
    induction t with
    | zero => intro k hk
              exact loopA_stepAt fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                (Bd' := fun _ => True) (fun x _ hx => by rw [hx (by omega)]; omega)
                fun h => absurd h (by omega)
    | succ t ih => intro k hk
                   refine loopA_stepAt fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                     (fun x hx _ => ?_) fun _ => ih (k + 1) (by omega)
                   have := hx (by omega)
                   rw [show (t + 1 + 2) * fs f = (t + 2) * fs f + fs f by ring]
                   omega
  intro k hk
  rw [show m - k + 1 = m - k - 1 + 2 by omega]
  exact (key (m - k - 1) k (by omega)).toDTB

end
end LeanVM.Guest.B1.Digest
