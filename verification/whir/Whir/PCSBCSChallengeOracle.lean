import Whir.PCSBCSRoundsAdapter
import Whir.PCSBCSRoundsByteHistory
import Whir.RawOracleCoupling
import Whir.PublicCompressionCouplingActualCausalBound

/-! Literal #552 challenge packets. A packet consists of all continuation blocks
of one normalized source history, not a hash of the preceding verifier answer.
The unused suffix of its last 256-bit block is retained. Programming is globally
memoized; a repeated query is not a new random experiment. -/
set_option autoImplicit false
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame TypedOracleCompiler
open scoped BigOperators

private def concatenate (a b : Nat) :
    ((Fin a → E) × (Fin b → E)) ≃ (Fin (a+b) → E) :=
  (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) E).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl E))

/-- Componentwise, source-ordered representation; no cardinality-chosen bijection. -/
def rawVector {c : Config} (q : CausalProbability.Coordinate c) :
    Raw q ≃ (Fin (rawWidth q) → E) := by
  cases q with
  | initial => exact initialEight
  | query i => exact ((Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) E).symm).trans
      (concatenate (queryChunks c i.val) 1))
  | fold i j => exact (Equiv.funUnique (Fin 1) E).symm
  | ood i j => exact Equiv.refl _
  | tail j => exact (Equiv.funUnique (Fin 1) E).symm

def blocks (width : Nat) : Nat := (24*width+31)/32

def unused (width : Nat) : Nat := 32*blocks width-24*width

theorem packet_length (width : Nat) :
    24*width + unused width = blocks width * 32 := by
  have bound : 24*width ≤ 32*blocks width := by
    unfold blocks
    omega
  unfold unused
  omega

def scalarBytesEquiv : E ≃ Scalar24 where
  toFun := ByteCodec.encodeE
  invFun := ByteCodec.decodeE
  left_inv := ByteCodec.decodeE_encodeE
  right_inv := ByteCodec.encodeE_decodeE

/-- Flattening follows the byte cursor: block j, byte i is byte 32*j+i. -/
def flatten (n size : Nat) : (Fin n → Fin size → Byte) ≃ (Fin (n*size) → Byte) :=
  (Equiv.curry (Fin n) (Fin size) Byte).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte))

def vectorBytes (width : Nat) : (Fin width → E) ≃ (Fin (width*24) → Byte) :=
  (Equiv.arrowCongr (Equiv.refl (Fin width)) scalarBytesEquiv).trans (flatten width 24)

/-- All bytes are accounted for: full E vector and the unused output suffix. -/
def packetEquiv (width : Nat) :
    (Fin (blocks width) → Digest32) ≃ ((Fin width → E) × (Fin (unused width) → Byte)) :=
  (flatten (blocks width) 32).trans
    ((Equiv.arrowCongr (finCongr (by have h := packet_length width; omega))
      (Equiv.refl Byte)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Byte)).trans
        ((Equiv.sumArrowEquivProdArrow (Fin (width*24)) (Fin (unused width)) Byte).trans
          (Equiv.prodCongr (vectorBytes width).symm (Equiv.refl _)))))

def grouped {c : Config} (q : CausalProbability.Coordinate c)
    (packet : Fin (blocks (rawWidth q)) → Digest32) : Raw q :=
  (rawVector q).symm ((packetEquiv (rawWidth q) packet).1)

/-- The payload is the actual contiguous prefix of the concatenated output
blocks. The equivalence does not choose a representation by cardinality. -/
theorem grouped_payload_bytes {c : Config} (q : CausalProbability.Coordinate c)
    (packet : Fin (blocks (rawWidth q)) → Digest32) (j : Fin (rawWidth q*24)) :
    vectorBytes (rawWidth q) (rawVector q (grouped q packet)) j =
      packet ⟨j.val/32, by
        have h := packet_length (rawWidth q)
        have hj := j.isLt
        omega⟩ ⟨j.val%32, Nat.mod_lt _ (by decide)⟩ := by
  simp only [grouped, Equiv.apply_symm_apply]
  simp [packetEquiv, flatten, vectorBytes, Equiv.arrowCongr, finProdFinEquiv,
    Nat.mod_add_div]
  rfl

private theorem product_probability {A B : Type*} [Fintype A] [Fintype B]
    (P : A → Prop) (R : B → Prop) :
    SamplingProbability.probability (fun x : A × B => P x.1 ∧ R x.2) =
      SamplingProbability.probability P * SamplingProbability.probability R := by
  classical
  let e : {x : A × B // P x.1 ∧ R x.2} ≃ {a : A // P a} × {b : B // R b} :=
    { toFun := fun x => (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
      invFun := fun x => ⟨(x.1.val,x.2.val),x.1.property,x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold SamplingProbability.probability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Uniform full-E message, independently of every predicate of the retained
suffix. In particular a 256-bit output is not silently counted as 256 E bits. -/
theorem grouped_uniform_independent {c : Config} (q : CausalProbability.Coordinate c)
    (P : Raw q → Prop) (S : (Fin (unused (rawWidth q)) → Byte) → Prop) :
    SamplingProbability.probability (fun packet : Fin (blocks (rawWidth q)) → Digest32 =>
      P (grouped q packet) ∧ S (packetEquiv (rawWidth q) packet).2) =
      SamplingProbability.probability P * SamplingProbability.probability S := by
  unfold grouped
  rw [SamplingProbability.probability_equiv (packetEquiv (rawWidth q))
    (fun x => P ((rawVector q).symm x.1) ∧ S x.2)]
  rw [product_probability (fun v => P ((rawVector q).symm v)) S,
    SamplingProbability.probability_equiv (rawVector q).symm P]

theorem grouped_uniform {c : Config} (q : CausalProbability.Coordinate c) (P : Raw q → Prop) :
    SamplingProbability.probability (fun packet : Fin (blocks (rawWidth q)) → Digest32 =>
      P (grouped q packet)) = SamplingProbability.probability P := by
  have h := grouped_uniform_independent q P (fun _ => True)
  have : Nonempty (Fin (unused (rawWidth q)) → Byte) := ⟨fun _ => ⟨0,by decide⟩⟩
  have ht : SamplingProbability.probability (fun _ : Fin (unused (rawWidth q)) → Byte => True) = 1 := by
    classical
    simp [SamplingProbability.probability]
  simpa only [and_true, ht, mul_one] using h

/-- Exact stratified query projection jointly with lambda, from complete
continuation blocks. Unused high query bits and final output bytes are retained. -/
theorem grouped_query_projection {c : Config} (i : Fin c.folds.size)
    (positive : 0 < remaining c i.val + c.rates[i.val]!)
    (bounded : remaining c i.val + c.rates[i.val]! ≤ 64)
    (P : Fin c.queries[i.val]! → Nat → Prop) (L : E → Prop) :
    SamplingProbability.probability
      (fun packet : Fin (blocks (rawWidth (.query i))) → Digest32 =>
        let x := grouped (.query i) packet
        (∃ qs, deriveQueries (remaining c i.val + c.rates[i.val]!) c.queries[i.val]!
          (Array.ofFn x.1) = some qs ∧ ∀ j : Fin c.queries[i.val]!, P j qs[j.val]!) ∧ L x.2) =
      (∏ j, SamplingProbability.probability (fun raw :
        Fin (2^(remaining c i.val + c.rates[i.val]!)) =>
        P j (SamplingProbability.concretePlace c.queries[i.val]!
          (remaining c i.val + c.rates[i.val]!) j.val raw.val))) *
          SamplingProbability.probability L := by
  let event : Raw (.query i) → Prop := fun x =>
    (∃ qs, deriveQueries (remaining c i.val + c.rates[i.val]!) c.queries[i.val]!
      (Array.ofFn x.1) = some qs ∧ ∀ j : Fin c.queries[i.val]!, P j qs[j.val]!) ∧ L x.2
  exact (grouped_uniform (.query i) event).trans
    (query_lambda_joint_law _ _ positive bounded P L)

/-- Literal finite RO keys can be restricted to any finite collection of
histories, including observer requests. No observer-class exclusion is used. -/
noncomputable def restrictionEquiv {K I D : Type*} (key : I → K)
    (injective : Function.Injective key) :
    (K → D) ≃ ((I → D) × ({k : K // k ∉ Set.range key} → D)) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun k => k ∈ Set.range key) (fun _ => D)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective key injective).symm (Equiv.refl D))
      (Equiv.refl _))

theorem restriction_first {K I D : Type*} (key : I → K)
    (injective : Function.Injective key) (table : K → D) :
    (restrictionEquiv key injective table).1 = fun i => table (key i) := by
  funext i
  rfl

open Classical in
/-- Freshness means absence of every requested continuation block from the
shared cache, not merely resetting the source byte cursor. Arbitrary events of
all other oracle entries factor from the complete grouped message. -/
theorem fresh_group_independent {K : Type*} [Fintype K] {c : Config}
    (q : CausalProbability.Coordinate c) (key : Fin (blocks (rawWidth q)) → K)
    (injective : Function.Injective key) (cache : K → Option Digest32)
    (fresh : ∀ i, cache (key i) = none) (P : Raw q → Prop)
    (R : ({k : K // k ∉ Set.range key} → Digest32) → Prop) :
    SamplingProbability.probability (fun table : K → Digest32 =>
      P (grouped q (fun i => RawOracleCoupling.overlay cache table (key i))) ∧
      R (restrictionEquiv key injective table).2) =
      SamplingProbability.probability P * SamplingProbability.probability R := by
  classical
  have overlay (table : K → Digest32) :
      (fun i => RawOracleCoupling.overlay cache table (key i)) = fun i => table (key i) := by
    funext i; simp [RawOracleCoupling.overlay, fresh]
  simp only [overlay]
  change SamplingProbability.probability (fun table : K → Digest32 =>
    P (grouped q (restrictionEquiv key injective table).1) ∧
      R (restrictionEquiv key injective table).2) = _
  rw [SamplingProbability.probability_equiv (restrictionEquiv key injective)
    (fun x => P (grouped q x.1) ∧ R x.2),
      product_probability (fun packet => P (grouped q packet)) R,
        grouped_uniform]

/-- Programming and repeated-query behavior are the existing checked globally
memoized finite oracle semantics, for all adaptive continuations and payoffs. -/
theorem programmable_table {K R : Type*} [Fintype K] [DecidableEq K]
    {n : Nat} (p : Sampling K (fun _ => Digest32) R n)
    (cache : K → Option Digest32) (payoff : R → ℚ) :
    average (fun table => payoff (Sampling.eval (RawOracleCoupling.overlay cache table) p)) =
      Sampling.expectation (fun result => payoff result.1) (RawOracleCoupling.memo p cache) :=
  RawOracleCoupling.table_eq_memo p cache payoff

#print axioms grouped_uniform_independent
#print axioms fresh_group_independent
#print axioms programmable_table
end Whir.PCSBCSChallengeOracle
