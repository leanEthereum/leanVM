/-
  LeanVM.Protocol.EndToEnd.Front.FlockArk

  What the security of a single-challenge or single-message component on ArkLib's typed
  framework gives the verifier program's specification, whatever its extractor: a challenge's
  escape average, and a message's reflection of the output relation into the input relation.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.PubEscape
public import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanVM.Protocol.ToArkLib.Typed.SendChecked

/-!
# Component securities, read off

The front phases are built from two shapes of typed component with a trivial witness:

* a checked challenge (`Typed.sampleChallenge O E check f`): `sample_escape` turns any
  `Typed.Security` of it at the error `e` into "from a statement outside the input relation that
  passes the check, the challenge carries it into the output relation with average at most
  `e`". It is the security's local bound at the challenge (`Typed.sample_escape`): the state
  before the challenge is the input relation, and after it the output relation at the verdict;
* a checked message (`Typed.sendChecked O M honest check out`): `sendChecked_reflect` turns any
  security of it into "a message passing the check with its verdict in the output relation comes
  from a statement in the input relation" (`Typed.sendChecked_reflect`: the terminal relation,
  then prover preservation).

These are the only facts the specifications of the verifier program use of the phases, so they
rest on the components' proved securities and nothing else.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol OracleComp OracleSpec
open scoped ENNReal NNReal

@[expose] public section

variable {ι : Type} {O : ι → Type} {StmtIn StmtOut : Type}

/-- **A challenge's escape, from a component's security.** From a statement outside the input
relation that passes the check, the challenge carries it into the output relation with average at
most the component's error. -/
theorem sample_escape {check : StmtIn → Bool} {f : StmtIn → E → StmtOut}
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    {e : ℝ≥0}
    (S : Typed.Security (Typed.sampleChallenge (W := Unit) O E check f) relIn relOut
      (Typed.drawErrors E e))
    (s : StmtIn) (o : ∀ i, O i) (hin : ((s, o), ()) ∉ relIn) (hc : check s = true) :
    avgE (fun c ↦ indE (((f s c, o), ()) ∈ relOut)) ≤ e := by
  rw [avgE_indE_eq_prEvent]
  exact le_trans (prEvent_mono _ _ _ fun c hc' ↦ ⟨(), hc'⟩)
    (Typed.sample_escape S s o (fun w hw ↦ by cases w; exact hin hw) hc)

/-- **A message's reflection, from a component's security.** A message passing the check whose
verdict is in the output relation comes from a statement in the input relation. -/
theorem sendChecked_reflect {M : Type} {honest : (StmtIn × ∀ i, O i) × Unit → M}
    {check : StmtIn → M → Bool} {out : StmtIn → M → StmtOut}
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    {err : Typed.Errors (Typed.sayTree M) (Typed.sayRoles M)}
    (S : Typed.Security (Typed.sendChecked (W := Unit) O M honest check out) relIn relOut err)
    (s : StmtIn) (o : ∀ i, O i) (msg : M) (hc : check s msg = true)
    (hout : ((out s msg, o), ()) ∈ relOut) : ((s, o), ()) ∈ relIn := by
  obtain ⟨w, hw⟩ := Typed.sendChecked_reflect S s o msg hc () hout
  cases w
  exact hw

end
end LeanVM.Protocol.EndToEnd.Front
