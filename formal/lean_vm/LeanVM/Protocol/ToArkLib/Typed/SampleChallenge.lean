/-
  LeanVM.Protocol.ToArkLib.Typed.SampleChallenge

  The typed component with one round, a verifier challenge: the verifier checks the statement,
  draws the challenge uniformly and maps the statement by it, leaving the oracles and the witness
  alone. Both halves. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# The sample-challenge component

`Typed.sampleChallenge O C check f` is the one-challenge tree `drawTree C`: the verifier
rejects unless the input statement `s` passes `check`, draws `c : C` uniformly, and outputs
`f s c`; the oracles and the witness are handed on.

Completeness (`sampleChallengeComplete`): on the input relation the check passes and `f`
carries the relation into the output relation at every challenge. Knowledge soundness
(`sampleChallengeSecurity`): at `N / |C|`, with the extractor that keeps the witness, when a
statement passing the check has at most `N` bad challenges, those that carry it from outside the
input relation into the output relation. Conversely every security of it bounds the challenges
that carry a statement with no witness into the output relation (`sample_escape`), so none is
below error one from a statement with no witness that every challenge carries into it
(`sampleChallenge_one_le`).
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## The one-challenge tree -/

/-- The tree of one verifier challenge. -/
abbrev drawTree (C : Type) : Oracle.TypeTree.{0} := .public C fun _ ↦ .done

/-- The verifier draws it. -/
abbrev drawRoles (C : Type) : (drawTree C).RoleDecoration := ⟨.receiver, fun _ ↦ ⟨⟩⟩

/-- The error `e` at the challenge. -/
abbrev drawErrors (C : Type) (e : ℝ≥0) : Errors (drawTree C) (drawRoles C) :=
  (e, fun _ ↦ PUnit.unit)

/-- The slot of one uniform challenge. -/
abbrev drawSlot (C : Type) [SampleableType C] : Slot :=
  ⟨drawTree C, drawRoles C, ⟨PUnit.unit, fun _ ↦ ⟨⟩⟩, ($ᵗ C, fun _ ↦ PUnit.unit)⟩

/-- The execution path of one challenge. -/
abbrev drawPath {C : Type} (c : C) : (drawTree C).ExecutionPath := ⟨c, PUnit.unit⟩

variable {ι : Type} (O : ι → Type) {StmtIn StmtOut W : Type} (C : Type) [SampleableType C]
  (check : StmtIn → Bool) (f : StmtIn → C → StmtOut)

/-- The verdict of a checked challenge: the statement mapped by the challenge, if it passes the
check. -/
def sampleVerdict (s : StmtIn) (p : (drawTree C).BranchPath) : Option StmtOut :=
  if check s then some (f s p.1) else none

/-- The sample-challenge component. -/
def sampleChallenge : Def O StmtIn W StmtOut W (drawSlot C) where
  verdict := sampleVerdict C check f
  prover := fun so w c ↦ pure ((f so.1 c, so.2), w)

/-! ## Completeness -/

variable {O C check f}
variable {relIn : Set ((StmtIn × ∀ i, O i) × W)} {relOut : Set ((StmtOut × ∀ i, O i) × W)}

/-- **Completeness**, whenever on the input relation the check passes and `f` carries the
relation into the output relation at every challenge. -/
theorem sampleChallengeComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → check s = true ∧ ∀ c, ((f s c, o), w) ∈ relOut) :
    Complete (sampleChallenge O C check f) relIn relOut := by
  rintro s o w hin ⟨c, ⟨⟩⟩ a ⟨-, rest, hrest, rfl⟩
  simp only [sampleChallenge, support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  obtain ⟨hc, hout⟩ := h s o w hin
  refine ⟨?_, rfl, hout c⟩
  change sampleVerdict C check f s ⟨c, PUnit.unit⟩ = _
  simp only [sampleVerdict, hc, ite_true]

/-! ## Knowledge soundness -/

/-- The extractor of a checked challenge: the input relation before the challenge; after it,
that the statement passed the check and its image, with the oracles and the same witness, is in
the output relation. -/
def sampleExtractor (s : StmtIn) (o : ∀ i, O i) :
    RoundExtractor (drawTree C) (inState O relIn s o) :=
  fun c ↦ ⟨⟨W, fun w ↦ check s = true ∧ ((f s c, o), w) ∈ relOut⟩, id, PUnit.unit⟩

/-- The state after the challenge is the output relation at the verdict. -/
def sampleTerminal (s : StmtIn) (o : ∀ i, O i) :
    TerminalRelation (sampleExtractor (C := C) (check := check) (f := f) (relIn := relIn)
      (relOut := relOut) s o) (outProblem O relOut o) (fun _ ↦ ())
      fun path ↦ sampleVerdict C check f s path.toBranchPath where
  witnessEquiv _ := Equiv.refl W
  knowledge_iff path w := by
    change (check s = true ∧ ((f s path.1, o), w) ∈ relOut) ↔
      ∃ t, sampleVerdict C check f s ⟨path.1, PUnit.unit⟩ = some t ∧ ((t, o), w) ∈ relOut
    simp only [sampleVerdict]
    by_cases hc : check s = true
    · simp [hc]
    · simp [hc]

/-- A bad challenge: some witness fails the input relation at the statement and meets the output
relation at the mapped statement. -/
def badChallenge (s : StmtIn) (o : ∀ i, O i) (c : C) : Prop :=
  ∃ w, ((s, o), w) ∉ relIn ∧ ((f s c, o), w) ∈ relOut

omit [SampleableType C] in
/-- With a trivial witness, the bad challenges are those carrying a statement outside the input
relation into the output relation. -/
theorem card_badChallenge_le_of_unit {relIn : Set ((StmtIn × ∀ i, O i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, O i) × Unit)} [Finite C] (N : ℕ) (s : StmtIn) (o : ∀ i, O i)
    (h : ((s, o), ()) ∉ relIn → Nat.card {c // ((f s c, o), ()) ∈ relOut} ≤ N) :
    Nat.card {c // badChallenge (f := f) (relIn := relIn) (relOut := relOut) s o c} ≤ N := by
  by_cases hin : ((s, o), ()) ∈ relIn
  · refine le_trans (le_of_eq ?_) (Nat.zero_le N)
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun ⟨_, w, hw, _⟩ ↦ hw (by cases w; exact hin)⟩
  · refine le_trans (Nat.card_mono (Set.toFinite _) fun c ⟨w, _, hw⟩ ↦ ?_) (h hin)
    cases w
    exact hw

variable [Finite C]

/-- **Knowledge soundness at `N / |C|`**, with the extractor that keeps the witness, when a
statement passing the check has at most `N` bad challenges. -/
def sampleChallengeSecurity (N : ℕ)
    (hN : ∀ s o, check s = true →
      Nat.card {c // badChallenge (f := f) (relIn := relIn) (relOut := relOut) s o c} ≤ N) :
    Security (sampleChallenge O C check f) relIn relOut
      (drawErrors C ((N : ℝ≥0) / (Nat.card C : ℝ≥0))) where
  extractor := sampleExtractor
  prover_preserving _ _ := ⟨fun _ hrole ↦ (nomatch hrole), fun _ ↦ trivial⟩
  local_bound s o := by
    refine ⟨?_, fun _ ↦ trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    have := Fintype.ofFinite C
    classical
    change Pr{let c ← $ᵗ C}[∃ w, ¬ ((s, o), w) ∈ relIn ∧
      (check s = true ∧ ((f s c, o), w) ∈ relOut)] ≤
        (((N : ℝ≥0) / (Nat.card C : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
    rw [Nat.card_eq_fintype_card, ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      ENNReal.coe_natCast, ENNReal.coe_natCast]
    by_cases hc : check s = true
    · have hcard : (Finset.univ.filter fun c ↦
          badChallenge (f := f) (relIn := relIn) (relOut := relOut) s o c).card ≤ N := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact hN s o hc
      refine le_trans (prEvent_mono _ _ _ ?_)
        ((SampleableType.prEvent_uniformSample_le_div_iff
          (p := fun c ↦ badChallenge (f := f) (relIn := relIn) (relOut := relOut) s o c)).mpr
          hcard)
      rintro c ⟨w, hin, -, hout⟩
      exact ⟨w, hin, hout⟩
    · refine le_trans (le_of_eq ?_) zero_le
      refine (OracleComp.prEvent_eq_zero_iff _ _).mpr ?_
      rintro c - ⟨w, -, hcheck, -⟩
      exact hc hcheck
  terminal := sampleTerminal

omit [Finite C] in
/-- **Every security of a checked challenge bounds the escape**: from a statement with no
witness that passes the check, the challenges carrying it into the output relation, with some
witness, have probability at most the error. -/
theorem sample_escape {e : ℝ≥0}
    (S : Security (sampleChallenge O C check f) relIn relOut (drawErrors C e)) (s : StmtIn)
    (o : ∀ i, O i) (hin : ∀ w, ((s, o), w) ∉ relIn) (hc : check s = true) :
    Pr{let c ← $ᵗ C}[∃ w, ((f s c, o), w) ∈ relOut] ≤ e := by
  have hb := (S.local_bound s o).1
  rw [_root_.RoundByRound.GameFamily.isBounded_iff] at hb
  refine le_trans (prEvent_mono _ _ _ fun c ⟨w, hout⟩ ↦ ?_) (hb () ())
  let path : (sampleChallenge (W := W) O C check f).tree.ExecutionPath := ⟨c, PUnit.unit⟩
  have hv : sampleVerdict C check f s ⟨c, PUnit.unit⟩ = some (f s c) := by
    simp [sampleVerdict, hc]
  exact ⟨_, hin _, terminal_holds_of_rel (S.terminal s o) path w ⟨f s c, hv, hout⟩⟩

omit [Finite C] in
/-- **No security below error one** from a statement with no witness that passes the check and
that every challenge carries into the output relation. -/
theorem sampleChallenge_one_le {e : ℝ≥0}
    (S : Security (sampleChallenge O C check f) relIn relOut (drawErrors C e)) (s : StmtIn)
    (o : ∀ i, O i) (hin : ∀ w, ((s, o), w) ∉ relIn) (hc : check s = true)
    (hesc : ∀ c, ∃ w, ((f s c, o), w) ∈ relOut) : 1 ≤ e := by
  have h := sample_escape S s o hin hc
  rw [show Pr{let c ← $ᵗ C}[∃ w, ((f s c, o), w) ∈ relOut] = 1 from
    (OracleComp.prEvent_eq_one_iff _ _).mpr fun c _ ↦ hesc c] at h
  exact_mod_cast h

end
end LeanVM.Protocol.Typed
