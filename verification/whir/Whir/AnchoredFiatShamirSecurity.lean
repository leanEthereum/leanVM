import Whir.CommitmentAnchor
import Whir.AnchoredFiatShamirSecurityCodec

/-! Finite deferred-sampling anchored game. Roots and shapes are chosen from the
completed public cache, not from the unanswered point. A repeated key returns
its entire immutable record; it is not a new chance to choose a root or value.
This is the byte-stream anchor reference game, not a native verifier body theorem. -/
namespace Whir.AnchoredFiatShamirSecurity
open Concrete Protocol CausalGame ParameterBounds CommitmentAnchor
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Point (p : Profile) := Fin (config p).logN → E

/-- The complete retained suffix of the final 32-byte output block is public. -/
abbrev Tail (p : Profile) := AnchoredFiatShamirSecurityCodec.Residual (config p).logN
abbrev Answer (p : Profile) := Point p × Tail p

def Samples (p : Profile) : Nat → Type
  | 0 => Unit
  | n+1 => Answer p × Samples p n

noncomputable instance samplesFintype (p : Profile) : (n : Nat) → Fintype (Samples p n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := samplesFintype p n
    exact inferInstanceAs (Fintype (Answer p × Samples p n))

instance samplesNonempty (p : Profile) : (n : Nat) → Nonempty (Samples p n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => by
    let := samplesNonempty p n
    exact inferInstanceAs (Nonempty (Answer p × Samples p n))

/-- The concrete grouped answer space consists of exactly ceil(24*logN/32)
output blocks from one contiguous run, starting at cursor zero. -/
def DigestSamples (p : Profile) : Nat → Type
  | 0 => Unit
  | n+1 => AnchoredFiatShamirSecurityCodec.Blocks (config p).logN × DigestSamples p n

instance digestSamplesFintype (p : Profile) : (n : Nat) → Fintype (DigestSamples p n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := digestSamplesFintype p n
    exact inferInstanceAs (Fintype (AnchoredFiatShamirSecurityCodec.Blocks (config p).logN ×
      DigestSamples p n))

def digestSamplesCodec (p : Profile) : (n : Nat) → DigestSamples p n ≃ Samples p n
  | 0 => Equiv.refl Unit
  | n+1 => Equiv.prodCongr
      (AnchoredFiatShamirSecurityCodec.vectorParts (config p).logN) (digestSamplesCodec p n)

private theorem uniform_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun a : A => P (e a)) =
      Soundness.uniformProb (Finset.univ.filter P) := by
  classical
  have h := RawOracleCoupling.average_equiv e (fun b => if P b then (1 : ℚ) else 0)
  simpa only [FiatShamirGame.average, Soundness.uniformProb, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h

/-- This record is supplied BEFORE the fresh answer. -/
structure PreAnchor (p : Profile) where
  lanes : Nat
  root : BaseOracle
  occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!

structure Entry (p : Profile) (Key : Type) where
  key : Key
  commitment : Commitment p
  discarded : Tail p

abbrev Cache (p : Profile) (Key : Type) := List (Entry p Key)

/-- All adaptive decisions see completed cache entries only. The advertised
value can depend on the newly returned point; the root and shape cannot. -/
structure Policy (p : Profile) (Key : Type) where
  choose : Cache p Key → Key
  prepare : Cache p Key → Key → PreAnchor p
  advertise : Cache p Key → Key → Answer p → E

noncomputable def lookup {p : Profile} {Key : Type} (cache : Cache p Key) (key : Key) :=
  cache.find? (fun e => decide (e.key = key))

noncomputable def advance {p : Profile} {Key : Type} (policy : Policy p Key)
    (cache : Cache p Key) (answer : Answer p) : Cache p Key :=
  let key := policy.choose cache
  match lookup cache key with
  | some e => e :: cache
  | none =>
    let pre := policy.prepare cache key
    ⟨key, ⟨pre.lanes,pre.root,answer.1,policy.advertise cache key answer,pre.occupied⟩,
      answer.2⟩ :: cache

/-- Unused coordinates at repeated keys are ignored, not reprogrammed. Every
fresh coordinate is independent uniform; the experiment has at most n queries. -/
noncomputable def run {p : Profile} {Key : Type} (policy : Policy p Key) :
    (n : Nat) → Cache p Key → Samples p n → Cache p Key
  | 0, cache, _ => cache
  | n+1, cache, sample => run policy n (advance policy cache sample.1) sample.2

def Dirty {p : Profile} {Key : Type} (cache : Cache p Key) : Prop :=
  ∃ e ∈ cache, Ambiguous p e.commitment.lanes e.commitment.root e.commitment.point

/-- A hit returns the same entire record and discarded public words. Logging
the repeat permits arbitrary subsequent adaptive decisions, without resampling. -/
theorem repeated_key {p : Profile} {Key : Type} (policy : Policy p Key)
    (cache : Cache p Key) (e : Entry p Key)
    (hit : lookup cache (policy.choose cache) = some e) (answer : Answer p) :
    advance policy cache answer = e :: cache := by
  simp [advance, hit]

private theorem clean_advance {p : Profile} {Key : Type} (policy : Policy p Key)
    (cache : Cache p Key) (clean : ¬ Dirty cache) (answer : Answer p)
    (separated : ¬ Ambiguous p (policy.prepare cache (policy.choose cache)).lanes
      (policy.prepare cache (policy.choose cache)).root answer.1) :
    ¬ Dirty (advance policy cache answer) := by
  classical
  unfold advance
  dsimp only
  cases hit : lookup cache (policy.choose cache) with
  | none =>
    simp only [Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨separated, clean⟩
  | some e =>
    have member : e ∈ cache := List.mem_of_find?_eq_some hit
    simp only [Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨fun bad => clean ⟨e,member,bad⟩,clean⟩

private theorem projection_probability {A B : Type} [Fintype A] [Fintype B]
    [Nonempty B] (P : A → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun x : A × B => P x.1) =
      Soundness.uniformProb (Finset.univ.filter P) := by
  classical
  have sets : (Finset.univ.filter fun x : A × B => P x.1) =
      (Finset.univ.filter P) ×ˢ (Finset.univ : Finset B) := by ext x; simp
  rw [sets]
  simp only [Soundness.uniformProb, Finset.card_product, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by positivity)

/-- Actual finite adaptive union/fiber bound. Preparation at round i can depend
on every previous root, point and advertised value. No independence of an
adversarially selected final root from the points is postulated. -/
theorem adaptive_ambiguity_probability {p : Profile} {Key : Type}
    (policy : Policy p Key) (n : Nat) (cache : Cache p Key) (clean : ¬ Dirty cache) :
    Soundness.uniformProb (Finset.univ.filter fun samples : Samples p n =>
      Dirty (run policy n cache samples)) ≤ (n : ℚ) / 2^124 := by
  classical
  induction n generalizing cache with
  | zero => simp [run, clean, Soundness.uniformProb]
  | succ n ih =>
    change Soundness.uniformProb (Finset.univ.filter fun samples : Answer p × Samples p n =>
      Dirty (run policy n (advance policy cache samples.1) samples.2)) ≤ _
    have bound := RingMapBatching.conditional_error (A := Answer p) (B := Samples p n)
      (fun answer => Ambiguous p (policy.prepare cache (policy.choose cache)).lanes
        (policy.prepare cache (policy.choose cache)).root answer.1)
      (fun sample : Answer p × Samples p n =>
        Dirty (run policy n (advance policy cache sample.1) sample.2))
      ((1 : ℚ)/2^124) ((n : ℚ)/2^124)
      (div_nonneg (Nat.cast_nonneg n) (pow_nonneg (by norm_num) _))
      (by
        rw [projection_probability]
        exact ambiguity_probability_numeric p _ _
          (policy.prepare cache (policy.choose cache)).occupied.2)
      (by
        intro answer separated
        exact ih (advance policy cache answer)
          (clean_advance policy cache clean answer separated))
    convert bound using 1
    push_cast
    ring

/-- With the compression cap also bounding fresh anchor-key attempts, adaptive
root grinding costs at most 2^-64, not the one-root 2^-124 term. -/
theorem adaptive_ambiguity_numeric {p : Profile} {Key : Type}
    (policy : Policy p Key) (n : Nat) (attempts : n ≤ 2^60) :
    Soundness.uniformProb (Finset.univ.filter fun samples : Samples p n =>
      Dirty (run policy n [] samples)) ≤ (1 : ℚ)/2^64 := by
  apply (adaptive_ambiguity_probability policy n [] (by simp [Dirty])).trans
  have h : (n : ℚ) ≤ 2^60 := by exact_mod_cast attempts
  exact (div_le_div_of_nonneg_right h (by positivity)).trans (by norm_num)

/-- The final root/shape/point must be an actual immutable cache entry. Selection
may inspect ALL completed attempts, including failed ones. -/
abbrev Selector {p : Profile} {Key : Type} (policy : Policy p Key) (n : Nat) :=
  (samples : Samples p n) → Option {e : Entry p Key // e ∈ run policy n [] samples}

/-- The final advertised value may be chosen after all point grinding. It then
belongs to the immutable commitment identity used in every opening session. -/
def chosenCommitment {p : Profile} {Key : Type} (e : Entry p Key) (v : E) : Commitment p :=
  {e.commitment with value := v}

noncomputable def Failure {p : Profile} {Key : Type} (policy : Policy p Key)
    (n : Nat) (select : Selector policy n)
    (advertised : Samples p n → E)
    (opening : Samples p n → Array Claim) (strategy : Samples p n → Strategy)
    (sample : Samples p n × Tape (config p)) : Prop :=
  match select sample.1 with
  | none => False
  | some e => openingFailure p (chosenCommitment e.val (advertised sample.1))
      (opening sample.1) (strategy sample.1) sample.2

/-- One fresh causal opening tape is composed with a fully adaptive chosen
anchor. Its selector is CommitmentAnchor.boundWitness of that immutable record;
the anchor claim is included in the opening/resource cap. This is binding,
not an efficient extractor and not a native Fiat--Shamir transport theorem. -/
theorem adaptive_unique_opening_probability {p : Profile} {Key : Type}
    (policy : Policy p Key) (n : Nat) (select : Selector policy n)
    (advertised : Samples p n → E)
    (opening : Samples p n → Array Claim) (strategy : Samples p n → Strategy)
    (opening_cap : ∀ samples, (opening samples).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter (Failure policy n select advertised opening strategy)) ≤
      (n : ℚ)/2^124 + (1 : ℚ)/2^73 := by
  classical
  apply RingMapBatching.conditional_error
    (fun samples => Dirty (run policy n [] samples)) _ _ _ (by positivity)
    (adaptive_ambiguity_probability policy n [] (by simp [Dirty]))
  intro samples clean
  cases h : select samples with
  | none => simp [Failure, h, Soundness.uniformProb]
  | some e =>
    have separated : ¬ Ambiguous p e.val.commitment.lanes e.val.commitment.root
        e.val.commitment.point := fun bad => clean ⟨e.val,e.property,bad⟩
    simpa only [Failure, h] using
      (unique_opening_probability p (chosenCommitment e.val (advertised samples))
        separated (opening samples)
        (strategy samples)).trans (production_interactive p _ (opening_cap samples))

theorem adaptive_unique_opening_numeric {p : Profile} {Key : Type}
    (policy : Policy p Key) (n : Nat) (attempts : n ≤ 2^60) (select : Selector policy n)
    (advertised : Samples p n → E)
    (opening : Samples p n → Array Claim) (strategy : Samples p n → Strategy)
    (opening_cap : ∀ samples, (opening samples).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter (Failure policy n select advertised opening strategy)) ≤
      (1 : ℚ)/2^64 + (1 : ℚ)/2^73 := by
  apply (adaptive_unique_opening_probability policy n select advertised opening strategy opening_cap).trans
  apply add_le_add _ le_rfl
  have h : (n : ℚ) ≤ 2^60 := by exact_mod_cast attempts
  exact (div_le_div_of_nonneg_right h (by positivity)).trans (by norm_num)

/-- Finite byte-stream grouped-digest reference experiment, retaining all public
bytes and consistent cached repeats. Exact raw-key causal grouping is supplied
by AnchoredByteStreamCausal and AnchoredByteStreamPrepared. This opening term
still uses an independent causal tape, not the deployed byte-stream body. -/
theorem grouped_digest_unique_opening_numeric {p : Profile} {Key : Type}
    (policy : Policy p Key) (n : Nat) (attempts : n ≤ 2^60) (select : Selector policy n)
    (advertised : Samples p n → E)
    (opening : Samples p n → Array Claim) (strategy : Samples p n → Strategy)
    (opening_cap : ∀ samples, (opening samples).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter fun raw :
        DigestSamples p n × Tape (config p) =>
      Failure policy n select advertised opening strategy
        (digestSamplesCodec p n raw.1,raw.2)) ≤
      (1 : ℚ)/2^64 + (1 : ℚ)/2^73 := by
  have transport := uniform_equiv
    (Equiv.prodCongr (digestSamplesCodec p n) (Equiv.refl (Tape (config p))))
    (Failure policy n select advertised opening strategy)
  have same :
      Soundness.uniformProb (Finset.univ.filter fun raw :
        DigestSamples p n × Tape (config p) =>
        Failure policy n select advertised opening strategy
          (digestSamplesCodec p n raw.1,raw.2)) =
      Soundness.uniformProb (Finset.univ.filter
        (Failure policy n select advertised opening strategy)) := by
    simpa only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply] using transport
  rw [same]
  exact adaptive_unique_opening_numeric policy n attempts select advertised opening strategy opening_cap

end Whir.AnchoredFiatShamirSecurity

#print axioms Whir.AnchoredFiatShamirSecurity.repeated_key
#print axioms Whir.AnchoredFiatShamirSecurity.adaptive_ambiguity_probability
#print axioms Whir.AnchoredFiatShamirSecurity.adaptive_ambiguity_numeric
#print axioms Whir.AnchoredFiatShamirSecurity.adaptive_unique_opening_probability
#print axioms Whir.AnchoredFiatShamirSecurity.adaptive_unique_opening_numeric
#print axioms Whir.AnchoredFiatShamirSecurity.grouped_digest_unique_opening_numeric
