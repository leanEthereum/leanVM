module

public import XmssSecurity.Proof.RevealProbeOracleSimulation

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def CausalRevealTransition {Index : Type}
    (before : Index → Option Digest) (index : Index) (value : Digest)
    (after : Index → Option Digest) : Prop :=
  after index = some value ∧
    ∀ candidate, candidate ≠ index → after candidate = before candidate

inductive ReplaysCausalReveals {Index : Type} :
    (Index → Option Digest) →
      RevealProbeOracleSimulation.ActionTrace Index →
        (Index → Option Digest) → Prop
  | nil (revealed) : ReplaysCausalReveals revealed [] revealed
  | probe (initial final) (index : Index) (target : Digest) (trace)
      (hrest : ReplaysCausalReveals initial trace final) :
      ReplaysCausalReveals initial
        (.probe index target :: trace) final
  | reveal (initial final) (index : Index) (value : Digest) (trace)
      (changed : Index → Option Digest)
      (hchange : CausalRevealTransition initial index value changed)
      (hrest : ReplaysCausalReveals changed trace final) :
      ReplaysCausalReveals initial
        (.reveal index value :: trace) final

theorem ReplaysCausalReveals.append
    {Index : Type}
    {initial middle final : Index → Option Digest}
    {left right : RevealProbeOracleSimulation.ActionTrace Index}
    (hleft : ReplaysCausalReveals initial left middle)
    (hright : ReplaysCausalReveals middle right final) :
    ReplaysCausalReveals initial (left ++ right) final := by
  induction hleft with
  | nil => exact hright
  | probe initial middle index target trace _ ih =>
      exact .probe initial final index target (trace ++ right) (ih hright)
  | reveal initial middle index value trace changed hchange _ ih =>
      exact .reveal initial final index value (trace ++ right) changed hchange
        (ih hright)

end XmssSecurity

