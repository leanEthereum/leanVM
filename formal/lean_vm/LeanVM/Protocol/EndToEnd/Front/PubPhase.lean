/-
  LeanVM.Protocol.EndToEnd.Front.PubPhase

  The public-input phase of the verifier program, specified in the calculus of verifier programs
  from the knowledge soundness of the ArkLib public-input phase over the leanISA instance.
-/

module

public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.EndToEnd.Claims
public import LeanVM.Protocol.EndToEnd.Front.PubEscape
public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.PublicInput
public import LeanVM.Protocol.LeanIsa
public import LeanVM.Protocol.EndToEnd.Front.InstanceWith
public import Statement.LeanVm

/-!
# The public-input phase as a specification

Step 5 of `verify_execution` (`publicInputPhase`, `crates/verifier/src/lib.rs:268-281` at leanVM
`40f877dc`): sample `r`, and claim for each memory column `ℓ`
the line through limb `ℓ` of the public-input digest's two halves `(h₀, h₁)` at `r`,
`(1 + r)·h₀,ℓ + r·h₁,ℓ` (`pubLimb`), at `(r, 0, …, 0)`. The prover sends nothing. It is a sample
followed by a return (`publicInputPhase_eq`).

**The fidelity check.** On the leanISA instance no public line is sent (`unsentLines`): the ArkLib
phase (`publicInputPhase`) reads an empty message and pools, for every line, the value it computes
from the statement, the line through its two cells. When the instance's statement is the digest's
(`digestHalves publicInput = (input.word0, input.word1)`, `PublicInput.ofDigest`), those values
are the program's limbs (`lineValue_eq_pubLimb`): the program's three claims are the phase's three
line claims (`lineClaim_eq`). No mismatch.

**The specification** (`pubPhaseSpec`). Doom quantifies over the candidates `C h₀` bound by the
history (for the leanVM program, the candidates of the level-0 commitment, `Candidates`); `toI`
reads a candidate as a stack of the instance:

* `PubPre`: no candidate satisfies the earlier claims, the public lines and the Keccak predicate
  at the table sumcheck's point `pt` (`M3Instance.auxAt`);
* `PubPost`: no candidate satisfies the earlier claims with the public claims appended and the
  Keccak predicate at `pt` (the reading of `Seam.pub`).

The challenge escapes with average at most `L₀ · 1/|E|` (`pub_escape`) for at most `L₀`
candidates: for each candidate satisfying the earlier claims, the phase's statement whose
received claims are true of it (`trueStmt`) is outside the table seam, and the phase's
round-by-round knowledge soundness on ArkLib's typed framework (`PublicInput.security`, its
local bound at the challenge) bounds by `1/|E|` the challenges at which its pool is in the
public seam; a good challenge of the program makes it so (`good_imp_state`).
The phase makes no prover move, so its challenge joins the group of the challenges after it:
the specification's lead is `L₀/|E|` plus the follower's.

**What the layout must give** (bridge A, `pubLayoutHyp`): a claim of the program on memory
column `j < 3` at the public point `(r, 0, …, 0)` holds of a candidate only if the instance's claim
on `MEM_j` at `linePoint r` holds of its reading `toI`.

**At every Keccak region.** The fidelity and the specification are stated at
`leanIsaWith prog s fl` (`Front.InstanceWith`): `PubPreWith`, `PubPostWith`, `pubLayoutHypWith`,
`pubPhaseSpecWith`; `PubPre`, `PubPost`, `pubLayoutHyp`, `trueClaim`, `stackOracle` and
`pubPhaseSpec` are them at the deployed instance. Without a region (`fl = none`) the Keccak
predicate holds of every stack (`aux_none`).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash OracleComp CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-! ## The program -/

/-- The point of the public claims, `(r, 0, …, 0)` on the memory's variables
(`lib.rs:272-273`). -/
def pubPoint (layout : Verifier.Layout) (r : E) : List E :=
  r :: List.replicate ((layout.placement memory0).variableCount - 1) 0

/-- The program's value of memory limb `ℓ` at the challenge: the line through limb `ℓ` of the
digest's two halves, `multilinear_eval([first.c_ℓ, second.c_ℓ], [r])` (`lib.rs:274-279`). -/
def pubLimb (publicInput : Digest) (r : E) (ℓ : Fin 3) : E :=
  multilinearEval [ofK ((digestHalves publicInput).1.limb ℓ),
    ofK ((digestHalves publicInput).2.limb ℓ)] [r]

/-- The program's claims: the three limbs on the three memory columns at the public point
(`lib.rs:275-281`). -/
def pubClaims (layout : Verifier.Layout) (publicInput : Digest) (r : E) :
    List Verifier.ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, pubPoint layout r, value⟩)
    [memory0, memory1, memory2] (([0, 1, 2] : List (Fin 3)).map (pubLimb publicInput r))

/-- The public-input phase is a challenge, then the claims. -/
theorem publicInputPhase_eq (layout : Verifier.Layout) (publicInput : Digest) :
    Verifier.publicInputPhase layout publicInput =
      VerifierProgram.sampleChallenge >>= fun r ↦ VerifierProgram.ret (pubClaims layout publicInput
          r) := rfl

/-- The limb, computed: `(1 + r)·h₀,ℓ + r·h₁,ℓ`. -/
theorem pubLimb_eq (publicInput : Digest) (r : E) (ℓ : Fin 3) :
    pubLimb publicInput r ℓ =
      (1 + r) * ofK ((digestHalves publicInput).1.limb ℓ) +
        r * ofK ((digestHalves publicInput).2.limb ℓ) := by
  simp only [pubLimb, multilinearEval, List.foldl, foldPairs, List.headD]
  ring

/-! ## The statement of the instance -/

/-! ## The fidelity of the claims -/

section Fidelity

variable (prog : LeanIsaProgram) (s : LeanIsa.Sizes)
  {fl : Option (KeccakRegion (LeanIsa.shape prog s))}

/-- **The phase's line values are the program's limbs.** When the statement is the digest's, the
value the ArkLib phase computes for line `j` (`MEM_LO, MEM_HI, MEM_TOP`) is the program's limb
`j`. -/
theorem lineValue_eq_pubLimb {publicInput : Digest} {input : PublicInput}
    (hinput : digestHalves publicInput = (input.word0, input.word1)) (r : E) (j : Fin 3) :
    PublicInput.lineValue (leanIsaWith prog s fl) r
      ((leanIsaWith prog s fl).publicLines input)[j] = pubLimb publicInput r j := by
  rw [pubLimb_eq, hinput]
  fin_cases j <;>
    simp [PublicInput.lineValue, LeanIsa.publicLines, PublicInput.word0, PublicInput.word1]

/-- The phase's claim on line `j` is the program's claim on memory column `j`, read on the
instance: `MEM_j` at `linePoint r`, at the program's limb. -/
theorem lineClaim_eq {publicInput : Digest} {input : PublicInput}
    (hinput : digestHalves publicInput = (input.word0, input.word1)) (r : E) (j : Fin 3) :
    PublicInput.lineClaim (leanIsaWith prog s fl) r
      ((leanIsaWith prog s fl).publicLines input)[j] =
      ⟨LeanIsa.memCol j.castSucc, PublicInput.linePoint s.logMem_pos r,
        pubLimb publicInput r j⟩ := by
  rw [PublicInput.lineClaim, lineValue_eq_pubLimb prog s (fl := fl) hinput]
  fin_cases j <;> rfl

end Fidelity

/-! ## Pre, post and the layout -/

section Spec

variable (prog : LeanIsaProgram) (s : LeanIsa.Sizes)
  (fl : Option (KeccakRegion (LeanIsa.shape prog s))) (layout : Verifier.Layout)
  (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (leanIsaWith prog s fl).μ)
  (H : Verifier.ColumnClaim → Column layout.stackLog → Prop)
  (claims : List Verifier.ColumnClaim) (input : PublicInput)
  (pt : Vector E (leanIsaWith prog s fl).τmax)

/-- **The public-input phase's precondition**: no candidate satisfies the earlier claims, the public
lines and the Keccak predicate at the table sumcheck's point `pt`. -/
def PubPreWith (h : List Ev) : Prop :=
  ∀ q ∈ C h, ¬ (ClaimsHoldBy H claims q ∧
    (leanIsaWith prog s fl).PublicLinesHold input (toI q) ∧
      (leanIsaWith prog s fl).auxAt pt.toList (toI q))

/-- **The public-input phase's postcondition** (the reading of `Seam.pub`): no candidate satisfies
the earlier claims with the public claims appended and the Keccak predicate at `pt`. -/
def PubPostWith (publicClaims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∀ q ∈ C h, ¬ (ClaimsHoldBy H (claims ++ publicClaims) q ∧
    (leanIsaWith prog s fl).auxAt pt.toList (toI q))

/-- **What the public-input phase needs of the layout** (bridge A): the program's claim on memory
column `j < 3` at the public point holds of a candidate only if the instance's claim on `MEM_j` at
`(r, 0, …, 0)` holds of its reading. -/
def pubLayoutHypWith : Prop :=
  ∀ (j : Fin 3) (r v : E) (q : Column layout.stackLog),
    H ⟨j.val, pubPoint layout r, v⟩ q →
      Protocol.ColumnClaim.Holds (toI q)
        (⟨LeanIsa.memCol j.castSucc, PublicInput.linePoint s.logMem_pos r, v⟩ :
          Protocol.ColumnClaim (leanIsaWith prog s fl))

/-- A good challenge of the program: some candidate satisfies the earlier claims, the public
claims and the Keccak predicate at `pt`. -/
def PubGoodWith (publicInput : Digest) (h₀ : List Ev) (r : E) : Prop :=
  ∃ q ∈ C h₀, ClaimsHoldBy H (claims ++ pubClaims layout publicInput r) q ∧
    (leanIsaWith prog s fl).auxAt pt.toList (toI q)

/-! ## The ArkLib statement of a candidate -/

/-- A claim true of a stack: `MEM_LO` at the origin, at its value there. -/
def trueClaimWith (q : Column (leanIsaWith prog s fl).μ) :
    Protocol.ColumnClaim (leanIsaWith prog s fl) :=
  ⟨LeanIsa.memCol 0, Vector.replicate _ 0,
    eval₂Mle ((leanIsaWith prog s fl).column q (LeanIsa.memCol 0)).values (algebraMap K E)
      (Vector.replicate _ 0)⟩

/-- The statement the phase starts from for a candidate: the public input, and received claims
all true of it. The phase's relations read the received claims only as a conjunct, which the
program's own claims replace. -/
def trueStmtWith (q : Column (leanIsaWith prog s fl).μ) :
    (leanIsaWith prog s fl).Stmt × TableOut (leanIsaWith prog s fl) :=
  (input, ⟨Vector.replicate _ (trueClaimWith prog s fl q), pt⟩)

/-- The stack as the phase's oracle. -/
def stackOracleWith (q : Column (leanIsaWith prog s fl).μ) :
    ∀ i, TheOracle (leanIsaWith prog s fl) i := fun _ ↦ q

/-- A candidate satisfying the earlier claims but not the public lines and the Keccak predicate at
`pt` is, with its true statement, outside the table seam. -/
theorem trueStmt_not_table (q : Column (leanIsaWith prog s fl).μ)
    (h : ¬ ((leanIsaWith prog s fl).PublicLinesHold input q ∧
      (leanIsaWith prog s fl).auxAt pt.toList q)) :
    ((trueStmtWith prog s fl input pt q, stackOracleWith prog s fl q), ()) ∉
      Seam.table (leanIsaWith prog s fl) := by
  rintro ⟨-, hl, ha⟩
  exact h ⟨hl, ha⟩

/-- **A good challenge is in the phase's state after the challenge.** If the candidate satisfies
the public claims at `r` and the Keccak predicate at `pt`, the phase's pool at `r` is in the
public seam. -/
theorem good_imp_state (hlayout : pubLayoutHypWith prog s fl layout toI H)
    {publicInput : Digest} (hinput : digestHalves publicInput = (input.word0, input.word1))
    {q : Column layout.stackLog} {r : E}
    (hcl : ClaimsHoldBy H (pubClaims layout publicInput r) q)
    (haux : (leanIsaWith prog s fl).auxAt pt.toList (toI q)) :
    ((PublicInput.pooled (leanIsaWith prog s fl) (trueStmtWith prog s fl input pt (toI q)) r,
      stackOracleWith prog s fl (toI q)), ()) ∈ Seam.pub (leanIsaWith prog s fl) := by
  refine ⟨?_, haux⟩
  intro c hc
  simp only [PublicInput.pooled, trueStmtWith, Vector.toList_append, Vector.toList_map,
    Vector.toList_replicate, List.mem_append, List.mem_replicate, List.mem_map] at hc
  rcases hc with ⟨-, rfl⟩ | ⟨l, hl, rfl⟩
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 3, ((leanIsaWith prog s fl).publicLines input)[j] = l := by
      obtain ⟨j, hj, hjl⟩ := List.mem_iff_getElem.mp hl
      exact ⟨⟨j, by simpa using hj⟩, by simpa using hjl⟩
    rw [lineClaim_eq prog s (fl := fl) hinput r j]
    refine hlayout j r _ q (hcl _ ?_)
    fin_cases j <;> simp [pubClaims, memory0, memory1, memory2]

/-! ## The escape -/

/-- **The challenge's escape.** Under `PubPre`, the average over the challenge of "the challenge is
good" is at most `L₀ / |E|`, `L₀` bounding the number of candidates: per candidate, the phase's
round-by-round knowledge soundness at the slot's error `1/|E|`, and the union bound. -/
theorem pub_escape (hlayout : pubLayoutHypWith prog s fl layout toI H)
    {publicInput : Digest} (hinput : digestHalves publicInput = (input.word0, input.word1))
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {h₀ : List Ev}
    (hpre : PubPreWith prog s fl layout C toI H claims input pt h₀) :
    avgE (fun r ↦ indE (PubGoodWith prog s fl layout C toI H claims pt publicInput h₀ r)) ≤
      L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  have := finite_column layout.stackLog
  have hfin : (C h₀).Finite := Set.toFinite _
  let P : Column layout.stackLog → E → Prop := fun q r ↦ ClaimsHoldBy H claims q ∧
    ((PublicInput.pooled (leanIsaWith prog s fl) (trueStmtWith prog s fl input pt (toI q)) r,
      stackOracleWith prog s fl (toI q)), ()) ∈ Seam.pub (leanIsaWith prog s fl)
  refine (avgE_mono fun r ↦ indE_mono ?_).trans
    (avgE_indE_exists_le hfin (hcard h₀) (P := P) fun q hq ↦ ?_)
  · rintro ⟨q, hq, hcl, haux⟩
    refine ⟨q, hq, fun c hc ↦ hcl c (List.mem_append_left _ hc), ?_⟩
    exact good_imp_state prog s fl layout toI H input pt hlayout hinput
      (fun c hc ↦ hcl c (List.mem_append_right _ hc)) haux
  · by_cases hcl : ClaimsHoldBy H claims q
    · have hnot := trueStmt_not_table prog s fl input pt (toI q)
        fun h ↦ hpre q hq ⟨hcl, h⟩
      refine (avgE_mono fun r ↦ indE_mono fun hP ↦ hP.2).trans ?_
      rw [avgE_indE_eq_prEvent]
      have hb := ((PublicInput.security (leanIsaWith prog s fl)).local_bound
        (trueStmtWith prog s fl input pt (toI q)) (stackOracleWith prog s fl (toI q))).1
      rw [_root_.RoundByRound.GameFamily.isBounded_iff] at hb
      exact le_trans (prEvent_mono _ _ _ fun r hr ↦ ⟨(), hnot, hr⟩) (hb () ())
    · refine (avgE_mono fun r ↦ indE_mono (q := False) fun hP ↦ absurd hP.1 hcl).trans ?_
      refine (avgE_le_of_le fun r ↦ (indE_of_not not_false).le).trans ?_
      exact zero_le

/-! ## The specification -/

/-- The candidates a history binds do not change along a run with no commitment. -/
def CandsStable : Prop := ∀ h₀ l, commits l = [] → C (h₀ ++ l) = C h₀

/-- The challenges outside a postcondition are counted by the indicator of a property every one
of them has. -/
theorem card_filter_le_sum_indE {p q : E → Prop} [DecidablePred p] (h : ∀ c, p c → q c) :
    ((Finset.univ.filter p).card : ℝ≥0∞) ≤ ∑ c, indE (q c) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun c _ ↦ ?_
  by_cases hp : p c
  · rw [ite_eq_left hp, indE_of (h c hp)]
  · rw [ite_eq_right hp]
    exact zero_le

open Classical in
/-- **The public-input phase's specification.** The program's public-input phase, from `PubPre` to
`PubPost`, with lead `L₀ / |E|` (`L₀` bounding the number of candidates, `1/|E|` the slot's error
`pubError`) plus the follower's `T`, given the layout's reading of the memory claims
(`pubLayoutHyp`), the instance's statement read off the digest, and candidates stable along the
phase. -/
noncomputable def pubPhaseSpecWith (hlayout : pubLayoutHypWith prog s fl layout toI H)
    {publicInput : Digest} (hinput : digestHalves publicInput = (input.word0, input.word1))
    (hstable : CandsStable layout C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} :
    Spec (Verifier.publicInputPhase layout publicInput)
      (PubPreWith prog s fl layout C toI H claims input pt)
      (PubPostWith prog s fl layout C toI H claims pt) εmax (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) + T) T :=
  Spec.congr (publicInputPhase_eq layout publicInput).symm
    ((Spec.sampleE (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞))
      (Post := fun r h ↦
        PubPostWith prog s fl layout C toI H claims pt (pubClaims layout publicInput r) h)
      fun h₀ hpre ↦ by
        refine le_trans ?_
          (pub_escape prog s fl layout C toI H claims input pt hlayout hinput hcard hpre)
        unfold avgE
        gcongr
        refine card_filter_le_sum_indE fun r hr ↦ ?_
        by_contra hg
        refine hr fun q hq hq' ↦ hg ⟨q, ?_, hq'⟩
        rwa [hstable h₀ [Ev.sample r] rfl] at hq).bind' fun r ↦
      Spec.ret (Post := PubPostWith prog s fl layout C toI H claims pt)
        (pubClaims layout publicInput r))

end Spec

/-! ## At the deployed instance -/

section Deployed

variable (prog : LeanIsaProgram) (s : LeanIsa.Sizes) (layout : Verifier.Layout)
  (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (leanIsaInstance prog s).μ)
  (H : Verifier.ColumnClaim → Column layout.stackLog → Prop)
  (claims : List Verifier.ColumnClaim) (input : PublicInput)
  (pt : Vector E (leanIsaInstance prog s).τmax)

/-- `PubPreWith` at the deployed instance. -/
abbrev PubPre : List Ev → Prop :=
  PubPreWith prog s (some (LeanIsa.keccakRegion prog s)) layout C toI H claims input pt

/-- `PubPostWith` at the deployed instance. -/
abbrev PubPost : List Verifier.ColumnClaim → List Ev → Prop :=
  PubPostWith prog s (some (LeanIsa.keccakRegion prog s)) layout C toI H claims pt

/-- `pubLayoutHypWith` at the deployed instance. -/
abbrev pubLayoutHyp : Prop :=
  pubLayoutHypWith prog s (some (LeanIsa.keccakRegion prog s)) layout toI H

/-- `trueClaimWith` at the deployed instance. -/
abbrev trueClaim :
    Column (leanIsaInstance prog s).μ → Protocol.ColumnClaim (leanIsaInstance prog s) :=
  trueClaimWith prog s (some (LeanIsa.keccakRegion prog s))

/-- `stackOracleWith` at the deployed instance. -/
abbrev stackOracle :
    Column (leanIsaInstance prog s).μ → ∀ i, TheOracle (leanIsaInstance prog s) i :=
  stackOracleWith prog s (some (LeanIsa.keccakRegion prog s))

open Classical in
/-- **The public-input phase's specification** at the deployed instance (`pubPhaseSpecWith`). -/
noncomputable def pubPhaseSpec (hlayout : pubLayoutHyp prog s layout toI H)
    {publicInput : Digest} (hinput : digestHalves publicInput = (input.word0, input.word1))
    (hstable : CandsStable layout C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} :
    Spec (Verifier.publicInputPhase layout publicInput)
      (PubPre prog s layout C toI H claims input pt)
      (PubPost prog s layout C toI H claims pt) εmax (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) + T) T :=
  pubPhaseSpecWith prog s _ layout C toI H claims input pt hlayout hinput hstable hcard

end Deployed

end
end LeanVM.Protocol.EndToEnd.Front
