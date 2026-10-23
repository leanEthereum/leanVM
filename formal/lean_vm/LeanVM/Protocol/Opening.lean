/-
  LeanVM.Protocol.Opening

  The opening phase: the verifier draws the batching challenge, combines the pooled claims by
  its powers into one weighted claim on the stack, and the protocol asks the stack that one
  question. Both halves, at the slot and its error.
-/

module

public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.ToArkLib.WeightBatch
public import LeanVM.Protocol.ToArkLib.Typed.Batch
public import LeanVM.Protocol.Spine.Slots
import LeanVM.Protocol.ClaimWeights

/-!
# The opening phase

Specification §8.5, the paragraph "Opening" of the unrolled protocol
(`doc/leanvm/body/08-end-to-end-protocol.tex:98-105` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): every pooled claim is a weighted claim on the stack
`⟨W_j, q⟩ = c_j`, a column claim through the stacking selectors (`ColumnClaim.holds_iff_weighted`)
and the ring-switched claim as it arrives; the verifier sends one batching challenge `λ`; claim
`j` takes the weight `λ^j`, counting from zero, the ring-switched claims first and the column
claims after; the verifier forms `W_λ = Σ_j λ^j·W_j` and `C_λ = Σ_j λ^j·c_j`, asks the stack
`⟨W_λ, q⟩`, and accepts when the answer is `C_λ`. There is no reduction sumcheck: the
inner-product oracle answers the one question, and the compilation replaces the question by an
opening of the commitment.

The phase is batching by powers (`opening`, `Typed.batch`) at the slot `openingSlot`, one
challenge: it draws `ρ` (the specification's `λ`, a keyword in Lean) and combines the pooled
values into the batched claim `⟨W_ρ, C_ρ⟩` (`batched`). The question is the spine's
(`stackQuestion`): at the protocol's leaf the verifier asks the stack the batched claim's weight
and accepts when the answer is its value, so the phase ends in `Seam.opened`, the batched claim
holding of the stack. The
claim values were sent by the earlier phases, so they are in the statement before `ρ` is drawn.
The pool's order (`pool_weighted`, `pool_column`) is the deployed verifiers': the ring-switched
claims take the first powers (`crates/verifier/src/lib.rs:118-142, 272-289`,
`python-verifier/verifier.py:1403-1407`).

Completeness (`openingComplete`): on the Flock seam every pooled claim holds, so the batched
claim holds at every challenge (`Weight.pair_batch`), and the stack's answer is its value.
Knowledge soundness (`openingSecurity`) at the slot's error `(J - 1)/|E|`, `J = I.poolSize`,
with the extractor that keeps the trivial witness, since the stack is the oracle: before the
challenge, every pooled claim holds; after it, the batched claim holds (`Seam.opened`). The stack's answers to the pooled weights are
fixed before the challenge; outside the Flock seam they differ from the claimed values, and the
batched claim holds only at a root of their difference, a nonzero polynomial of degree less
than `J` in `ρ` (`batchSecurity`).

Written from the specification; the Rust and Python verifiers were read afterwards for the
order of the powers.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly OracleComp OracleSpec
open scoped NNReal

@[expose] public section

namespace Opening

variable (I : M3Instance)

/-! ## The pool and the batched claim -/

/-- A column claim as the weighted claim on the stack at the equality kernel of its point
lifted through the layout. -/
def columnWeighted (c : ColumnClaim I) : WeightedClaim I :=
  ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩

/-- The pool in the order of the powers of the challenge: the weighted claims, then the column
claims as weighted claims. -/
def poolList (s : FlockOut I) : List (WeightedClaim I) :=
  s.weighted.toList ++ s.columns.toList.map (columnWeighted I)

/-- The pool has `I.poolSize` claims. -/
theorem length_poolList (s : FlockOut I) : (poolList I s).length = I.poolSize := by
  simp only [poolList, List.length_append, Vector.length_toList, List.length_map,
    M3Instance.poolSize]
  omega

/-- Claim `j` of the pool, the one the `j`-th power of the challenge weighs. -/
def pool (s : FlockOut I) (j : Fin I.poolSize) : WeightedClaim I :=
  (poolList I s)[j.val]'((length_poolList I s).symm ▸ j.isLt)

/-- The pool's claimed values. -/
def values (s : I.Stmt × FlockOut I) (j : Fin I.poolSize) : E := (pool I s.2 j).value

/-- The pool's weights combined by the powers of `ρ`. -/
def weight (s : I.Stmt × FlockOut I) (ρ : E) : Weight E I.μ :=
  Weight.batch (fun j ↦ (pool I s.2 j).weight) ρ

/-- The batched claim at `ρ`: the combined weight, claimed to answer `c`, the combined value
batching by powers computes. -/
def batched (s : I.Stmt × FlockOut I) (ρ c : E) : WeightedClaim I := ⟨weight I s ρ, c⟩

/-- After the challenge: the batched claim holds of the stack. -/
def BatchedHolds : Set ((WeightedClaim I × ∀ i, TheOracle I i) × Unit) :=
  {p | p.1.1.Holds (theStack p.1.2)}

/-- The question that asks the stack for its inner product with `W`. -/
def ask (W : Weight E I.μ) : [TheOracle I]ₒ.Domain := ⟨0, W⟩

/-- The question a weighted claim asks the stack: its weight. -/
def question (c : WeightedClaim I) : [TheOracle I]ₒ.Domain := ask I c.weight

/-- An answer is accepted when it is the claim's value. -/
def accepts (c : WeightedClaim I) (a : E) : Bool := decide (a = c.value)

/-- The acceptance is the equality. -/
theorem accepts_iff (c : WeightedClaim I) (a : E) : accepts I c a = true ↔ a = c.value :=
  decide_eq_true_iff

/-- The check on the stack's answer to a claim's weight. -/
def check (c : WeightedClaim I) (a : [TheOracle I]ₒ.Range (question I c)) : Bool :=
  accepts I c a

/-! ## The order of the powers -/

/-- The weighted claims take the first powers. -/
theorem pool_weighted (s : FlockOut I) (j : Fin I.flockClaims) :
    pool I s ⟨j.val, by have := j.isLt; simp only [M3Instance.poolSize]; omega⟩ =
      s.weighted[j.val] := by
  simp only [pool, poolList]
  rw [List.getElem_append_left (by simp)]
  simp

/-- The column claims take the powers after them, in their order. -/
theorem pool_column (s : FlockOut I) (j : Fin I.pubClaims) :
    pool I s ⟨I.flockClaims + j.val, by have := j.isLt; simp only [M3Instance.poolSize]; omega⟩ =
      columnWeighted I s.columns[j.val] := by
  simp only [pool, poolList]
  rw [List.getElem_append_right (by simp)]
  simp

/-! ## What the claims say -/

/-- A column claim's weighted claim holds exactly when the column claim does. -/
theorem columnWeighted_holds_iff (q : Column I.μ) (c : ColumnClaim I) :
    (columnWeighted I c).Holds q ↔ c.Holds q :=
  (ColumnClaim.holds_iff_weighted q c).symm

/-- Every claim of the pool holds of the stack exactly when every claim the Flock seam carries
does. -/
private theorem pool_holds_iff (s : FlockOut I) (q : Column I.μ) :
    (∀ j, (pool I s j).Holds q) ↔
      (∀ c ∈ s.columns.toList, c.Holds q) ∧ ∀ c ∈ s.weighted.toList, c.Holds q := by
  have hpool : (∀ j, (pool I s j).Holds q) ↔ ∀ c ∈ poolList I s, c.Holds q := by
    rw [List.forall_mem_iff_getElem]
    refine ⟨fun h i hi ↦ h ⟨i, length_poolList I s ▸ hi⟩, fun h j ↦ h j.val _⟩
  rw [hpool, poolList, List.forall_mem_append, List.forall_mem_map, and_comm]
  simp only [columnWeighted, ← ColumnClaim.holds_iff_weighted]

/-- The batched claim holds exactly when the stack's answers to the pooled weights, combined by
the powers of `ρ`, are the claimed combination. -/
theorem batched_holds_iff (s : I.Stmt × FlockOut I) (ρ c : E) (q : Column I.μ) :
    (batched I s ρ c).Holds q ↔
      powerBatch (fun j ↦ (pool I s.2 j).weight.pair (algebraMap K E) q.values) ρ = c := by
  unfold batched weight WeightedClaim.Holds
  rw [Weight.pair_batch]

/-- On the Flock seam the batched claim holds at every challenge. -/
theorem batched_of_flock {s : I.Stmt × FlockOut I} {o : ∀ i, TheOracle I i}
    (h : ((s, o), ()) ∈ Seam.flock I) (ρ : E) :
    (batched I s ρ (powerBatch (values I s) ρ)).Holds (theStack o) :=
  (batched_holds_iff I s ρ _ _).mpr
    (congrArg (powerBatch · ρ) (funext ((pool_holds_iff I s.2 (theStack o)).mpr h)))

/-- The stack's answers to the pooled weights, fixed before the challenge: outside the Flock
seam they are not the claimed values, and the batched claim holds only where their combination
is the claimed one. -/
theorem answers_of_not_flock (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) :
    ∃ a : Fin I.poolSize → E, ∀ w ρ, ((s, o), w) ∉ Seam.flock I →
      ((batched I s ρ (powerBatch (values I s) ρ), o), w) ∈ BatchedHolds I →
        a ≠ values I s ∧ powerBatch (values I s) ρ = powerBatch a ρ := by
  refine ⟨fun j ↦ (pool I s.2 j).weight.pair (algebraMap K E) (theStack o).values,
    fun w ρ hin hb ↦ ⟨fun ha ↦ hin ?_, ((batched_holds_iff I s ρ _ _).mp hb).symm⟩⟩
  cases w
  exact (pool_holds_iff I s.2 (theStack o)).mp (congrFun ha)

end Opening

/-! ## The phase

The opening phase as a typed component is the batching alone, at the opening's slot: the question
to the stack is the spine's (`stackQuestion`), asked at the protocol's leaf, so the phase reaches
`Seam.opened`, the batched claim holding of the stack. -/

variable (I : M3Instance)

/-- The opening phase, typed: batching by powers into the batched claim. -/
def opening : Typed.Def (TheOracle I) (I.Stmt × FlockOut I) Unit (WeightedClaim I) Unit
    openingSlot :=
  Typed.batch (TheOracle I) E (Opening.values I) (Opening.batched I)

/-- The typed completeness half. -/
theorem openingComplete : Typed.Complete (opening I) (Seam.flock I) (Seam.opened I) :=
  Typed.batchComplete fun _ o w h ρ ↦ (Seam.opened_iff I _ o w).mpr (Opening.batched_of_flock I h ρ)

/-- The typed security half, at the slot's error, with the extractor that keeps the trivial
witness. -/
def openingSecurity :
    Typed.Security (opening I) (Seam.flock I) (Seam.opened I) (openingErrors I) :=
  Typed.Security.mono (by exact ⟨le_of_eq (natCast_div_card_eq_overE _), fun _ ↦ trivial⟩)
    (Typed.batchSecurity fun s o ↦
      have ⟨a, ha⟩ := Opening.answers_of_not_flock I s o
      ⟨a, fun w ρ hin hout ↦ ha w ρ hin ((Seam.opened_iff I _ o w).mp hout)⟩)

end
end LeanVM.Protocol
