/-
  LeanVM.Protocol.ToArkLib.Typed.SendChecked

  The typed component with one round, a prover message: the verifier reads the message, rejects
  unless the statement and the message pass a check, and outputs a function of both, leaving the
  oracles and the witness alone. Both halves. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component

/-!
# The send-checked component

`Typed.sendChecked O M honest check out` is the one-message tree `sayTree M`: the prover sends
`honest` of its input (the statement, the oracles' contents and the witness), the verifier reads
the message `msg`, rejects unless `check s msg` passes, and outputs `out s msg`; the oracles and
the witness are handed on.

Completeness (`sendCheckedComplete`): on the input relation the honest message passes the check
and `out` of it lands in the output relation. Knowledge soundness (`sendCheckedSecurity`): a
message has no challenge, so it is secure at no error whenever the check and the output relation
together imply the input relation; the extractor keeps the witness. Conversely every security of
it gives that implication (`sendChecked_reflect`), and none exists when a message passing the
check carries a statement with no witness into the output relation
(`sendChecked_no_security`).
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## The one-message tree -/

/-- The tree of one prover message. -/
abbrev sayTree (M : Type) : Oracle.TypeTree.{0} := .public M fun _ ↦ .done

/-- The prover sends it. -/
abbrev sayRoles (M : Type) : (sayTree M).RoleDecoration := ⟨.sender, fun _ ↦ ⟨⟩⟩

/-- No error: a message has no challenge. -/
abbrev sayErrors (M : Type) : Errors (sayTree M) (sayRoles M) := fun _ ↦ PUnit.unit

/-- The slot of one prover message. -/
abbrev saySlot (M : Type) : Slot :=
  ⟨sayTree M, sayRoles M, ⟨PUnit.unit, fun _ ↦ ⟨⟩⟩, fun _ ↦ PUnit.unit⟩

/-- The execution path of one message. -/
abbrev sayPath {M : Type} (m : M) : (sayTree M).ExecutionPath := ⟨m, PUnit.unit⟩

variable {ι : Type} (O : ι → Type) {StmtIn StmtOut W : Type} (M : Type)
  (honest : (StmtIn × ∀ i, O i) × W → M) (check : StmtIn → M → Bool)
  (out : StmtIn → M → StmtOut)

/-- The verdict of a checked message: `out` of the statement and the message, if they pass the
check. -/
def sendCheckedVerdict (s : StmtIn) (p : (sayTree M).BranchPath) : Option StmtOut :=
  if check s p.1 then some (out s p.1) else none

/-- The send-checked component. -/
def sendChecked : Def O StmtIn W StmtOut W (saySlot M) where
  verdict := sendCheckedVerdict M check out
  prover := fun so w ↦ pure ⟨honest (so, w), ((out so.1 (honest (so, w)), so.2), w)⟩

/-! ## Completeness -/

variable {O M honest check out}
variable {relIn : Set ((StmtIn × ∀ i, O i) × W)} {relOut : Set ((StmtOut × ∀ i, O i) × W)}

/-- **Completeness**, whenever on the input relation the honest message passes the check and
`out` of it lands in the output relation. -/
theorem sendCheckedComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (honest ((s, o), w)) = true ∧ ((out s (honest ((s, o), w)), o), w) ∈ relOut) :
    Complete (sendChecked O M honest check out) relIn relOut := by
  rintro s o w hin ⟨m, ⟨⟩⟩ a ⟨rest, hrest, rfl⟩
  simp only [sendChecked, support_pure, Set.mem_singleton_iff] at hrest
  obtain ⟨rfl, rfl⟩ := hrest
  obtain ⟨hc, hout⟩ := h s o w hin
  refine ⟨?_, rfl, hout⟩
  change sendCheckedVerdict M check out s ⟨honest ((s, o), w), PUnit.unit⟩ = _
  simp only [sendCheckedVerdict, hc, ite_true]

/-! ## Knowledge soundness -/

/-- The extractor of a checked message: the input relation before the message; after it, that
the message passes the check and its verdict, with the oracles and the same witness, is in the
output relation. -/
def sendCheckedExtractor (s : StmtIn) (o : ∀ i, O i) :
    RoundExtractor (sayTree M) (inState O relIn s o) :=
  fun msg ↦ ⟨⟨W, fun w ↦ check s msg = true ∧ ((out s msg, o), w) ∈ relOut⟩, id, PUnit.unit⟩

/-- The state after the message is the output relation at the verdict. -/
def sendCheckedTerminal (s : StmtIn) (o : ∀ i, O i) :
    TerminalRelation (sendCheckedExtractor (M := M) (check := check) (out := out)
      (relIn := relIn) (relOut := relOut) s o) (outProblem O relOut o) (fun _ ↦ ())
      fun path ↦ sendCheckedVerdict M check out s path.toBranchPath where
  witnessEquiv _ := Equiv.refl W
  knowledge_iff path w := by
    change (check s path.1 = true ∧ ((out s path.1, o), w) ∈ relOut) ↔
      ∃ t, sendCheckedVerdict M check out s ⟨path.1, PUnit.unit⟩ = some t ∧ ((t, o), w) ∈ relOut
    simp only [sendCheckedVerdict]
    by_cases hc : check s path.1 = true
    · simp [hc]
    · simp [hc]

/-- **Knowledge soundness at no error**, whenever the check and the output relation together
imply the input relation; the extractor keeps the witness. -/
def sendCheckedSecurity
    (h : ∀ s o w msg, check s msg = true → ((out s msg, o), w) ∈ relOut → ((s, o), w) ∈ relIn) :
    Security (sendChecked O M honest check out) relIn relOut (sayErrors M) where
  extractor := sendCheckedExtractor
  prover_preserving s o := ⟨fun msg _ w hw ↦ h s o w msg hw.1 hw.2, fun _ ↦ trivial⟩
  local_bound _ _ := fun _ ↦ trivial
  terminal := sendCheckedTerminal

/-- **Every security of a checked message reflects the output relation**: a message passing the
check whose verdict, with a witness, is in the output relation comes from a statement in the
input relation, at the extracted witness. -/
theorem sendChecked_reflect {err : Errors (sayTree M) (sayRoles M)}
    (S : Security (sendChecked O M honest check out) relIn relOut err) (s : StmtIn)
    (o : ∀ i, O i) (msg : M) (hc : check s msg = true) (w : W)
    (hout : ((out s msg, o), w) ∈ relOut) : ∃ w', ((s, o), w') ∈ relIn := by
  let path : (sendChecked O M honest check out).tree.ExecutionPath := ⟨msg, PUnit.unit⟩
  have hv : sendCheckedVerdict M check out s ⟨msg, PUnit.unit⟩ = some (out s msg) := by
    simp [sendCheckedVerdict, hc]
  exact ⟨_, (S.prover_preserving s o).1 msg rfl _
    (terminal_holds_of_rel (S.terminal s o) path w ⟨out s msg, hv, hout⟩)⟩

/-- **No security** of a checked message exists when some message that passes the check carries
a statement with no witness into the output relation. -/
theorem sendChecked_no_security {err : Errors (sayTree M) (sayRoles M)}
    (S : Security (sendChecked O M honest check out) relIn relOut err) (s : StmtIn)
    (o : ∀ i, O i) (hin : ∀ w, ((s, o), w) ∉ relIn) (msg : M) (hc : check s msg = true) (w : W)
    (hout : ((out s msg, o), w) ∈ relOut) : False :=
  have ⟨w', hw'⟩ := sendChecked_reflect S s o msg hc w hout
  hin w' hw'

end
end LeanVM.Protocol.Typed
