import Whir.InteractiveSoundness
import Whir.RingMapBatchingConcrete
import Whir.ByteCodec

/-! Ordinary interactive ring-family openings. The commitment determines the K candidate list before the caller supplies any statements. Caller binding of the slice tables, points and values is an external context boundary, not a transcript guarantee. Gamma and six map draws precede the actual WHIR initial lambda.

The executable transformation is the flattened, statement-checked semantics of `stack_open.rs` and `ring_switch.rs`: region order then claim order, gamma scales inside the six-stage additive map, family at lambda power zero, and points at succeeding powers. Source statement rejection can only restrict the accepted event bounded here. Dense transparent weights are passed to the actual causal WHIR experiment, not to a replacement dot-product acceptance predicate.

The checked word-polynomial embedding proves the bridge from literal padded K witnesses to binary slices. The end-to-end loss is `2^32 * ((m-1)/2^192 + 2^-160)` plus the actual WHIR interactive ledger. `InitialEvent` instead groups all eight initial scalars for the eventual ROM adapter. No grinding amplification, unique binding, caller transcript binding, or Fiat-Shamir conclusion is asserted here. -/
namespace Whir.RingPCSGame
open Concrete Protocol CausalGame ParameterBounds
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

abbrev Prefix := E × (Fin 6 → E)

/-- The source squares exactly shift times, rather than evaluating a unary power. -/
def squareIter (x : E) : Nat → E
  | 0 => x
  | n + 1 => let y := squareIter x n; y * y

theorem squareIter_eq (x : E) (n : Nat) : squareIter x n = x ^ (2 ^ n) := by
  induction n with
  | zero => simp [squareIter]
  | succ n ih => simp [squareIter, ih, pow_succ, pow_mul]

def mapStage (f : E) (shift : Nat) : E →+ E where
  toFun x := x + f * squareIter x shift
  map_zero' := by simp [squareIter_eq]
  map_add' a b := by
    simp only [squareIter_eq, add_pow_char_pow, mul_add]
    abel

theorem mapStage_eq (f : E) (shift : Nat) : mapStage f shift = RingSwitch.stage f shift := by
  ext x
  exact congrArg (fun y => x + f * y) (squareIter_eq x shift)

def executableMap (challenges : Fin 6 → E) : E →+ E :=
  (List.finRange 6).foldl
    (fun φ p => (mapStage (challenges p) (2 ^ (5 - p.val))).comp φ)
    (AddMonoidHom.id E)

@[simp] theorem executableMap_eq (challenges : Fin 6 → E) :
    executableMap challenges = RingSwitch.composedMap challenges := by
  simp only [executableMap, mapStage_eq, RingSwitch.composedMap]

def basis (i : Fin 64) : E := (E.ofK 2) ^ i.val

def wordBit (a : K) (i : Fin 64) : Bool := a.toBitVec.getLsbD i.val

/-- The literal machine word is its binary polynomial, not an assumed encoding. -/
theorem word_packed (a : K) :
    E.ofK a = ∑ i : Fin 64, RingSwitch.bit (wordBit a i) * basis i := by
  rw [← FieldModel.baseEmbedding_word]
  unfold FieldModel.toBaseQuotient FieldModel.wordPoly FieldModel.bitPoly
  rw [map_sum, map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
  change FieldModel.baseEmbedding (AdjoinRoot.mk FieldModel.baseModulus
    (Polynomial.C (if a.toBitVec.getLsbD i.val then 1 else 0))) *
      FieldModel.baseEmbedding (AdjoinRoot.root FieldModel.baseModulus) ^ i.val = _
  rw [FieldModel.baseEmbedding_root]
  cases h : a.toBitVec.getLsbD i.val <;>
    simp only [wordBit, RingSwitch.bit, basis, h, Bool.false_eq_true, ↓reduceIte,
      map_zero, map_one, zero_mul, one_mul]

/-- The byte codec reconstructs precisely the word used by the slice bridge. -/
theorem decoded_word_packed (bytes : Fin 8 → FiatShamirGame.Byte) :
    E.ofK (ByteCodec.decodeK bytes) =
      ∑ i : Fin 64, RingSwitch.bit (wordBit (ByteCodec.decodeK bytes) i) * basis i :=
  word_packed _

/-- A flattened ring claim, in region order then claim order as in Rust. -/
structure FamilyClaim where
  offset : Nat
  point : Array E
  slices : Fin 64 → E

/-- Both source point forms, with their exact stack placement. -/
inductive PointClaim where
  | point (offset : Nat) (point : Array E) (value : E)
  | strided (offset slot strideLog : Nat) (point : Array E) (value : E)

def eqWeight (point : Array E) (u : Nat) : E :=
  ∏ i : Fin point.size, if u.testBit i.val then point[i] else 1 + point[i]

def regionWeight (offset : Nat) (point : Array E) (v : Nat) : E :=
  if offset ≤ v ∧ v < offset + 2 ^ point.size then eqWeight point (v - offset) else 0

def pointWeight : PointClaim → Nat → E
  | .point offset point _, v => regionWeight offset point v
  | .strided offset slot strideLog point _, v =>
    if offset + slot ≤ v ∧ v < offset + 2 ^ (strideLog + point.size) ∧
        (v - offset) % 2 ^ strideLog = slot then
      eqWeight point ((v - offset) / 2 ^ strideLog) else 0

def pointValue : PointClaim → E
  | .point _ _ value => value
  | .strided _ _ _ _ value => value

def publicPoint (width : Nat) (claim : PointClaim) : Claim :=
  ⟨tab width (pointWeight claim), pointValue claim⟩

def familyTarget {m : Nat} (sent : Fin m → Fin 64 → E) (r : Prefix) : E :=
  RingSwitch.familyTarget (executableMap r.2) basis (fun j => r.1 ^ j.val) sent

/-- Each gamma power stays inside the additive, generally non-E-linear map. -/
def transparentWeight {m : Nat} (family : Fin m → FamilyClaim) (r : Prefix) (v : Nat) : E :=
  ∑ j, executableMap r.2 (r.1 ^ j.val * regionWeight (family j).offset (family j).point v)

def familyPublic {m : Nat} (width : Nat) (family : Fin m → FamilyClaim) (r : Prefix) : Claim :=
  ⟨tab width (transparentWeight family r), familyTarget (fun j => (family j).slices) r⟩

/-- Family first, then point claims. Actual batchClaims therefore uses lambda^0
for the family and lambda^(i+1) for point i, including the empty family. -/
def transformedClaims {m : Nat} (width : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (r : Prefix) : Array Claim :=
  #[familyPublic width family r] ++ points.map (publicPoint width)

@[simp] theorem transformedClaims_size {m : Nat} (width : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (r : Prefix) :
    (transformedClaims width family points r).size = 1 + points.size := by
  simp [transformedClaims]

def paddedWord (c : Config) (lanes : Nat) (w : Witness c lanes) (v : Nat) : K :=
  (Array.ofFn w)[v]?.getD 0

def honestSlices {m : Nat} (c : Config) (lanes : Nat) (family : Fin m → FamilyClaim)
    (w : Witness c lanes) : Fin m → Fin 64 → E := fun j =>
  RingSwitch.slice (fun v : Fin (2 ^ c.logN) => regionWeight (family j).offset (family j).point v.val)
    (fun i v => wordBit (paddedWord c lanes w v.val) i)

/-- Honesty is stated about the original slices and every original point value. -/
def Honest {m : Nat} (c : Config) (lanes : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (w : Witness c lanes) : Prop :=
  (fun j => (family j).slices) = honestSlices c lanes family w ∧
  ∀ point ∈ points.toList,
    dot (paddedWitness c lanes w) (publicPoint (2 ^ c.logN) point).weight = pointValue point

theorem dot_family {m : Nat} (c : Config) (lanes : Nat) (family : Fin m → FamilyClaim)
    (w : Witness c lanes) (r : Prefix) :
    dot (paddedWitness c lanes w) (familyPublic (2 ^ c.logN) family r).weight =
      familyTarget (honestSlices c lanes family w) r := by
  unfold familyTarget honestSlices
  rw [RingSwitch.honest_family]
  simp only [RingSwitch.packed, ← word_packed]
  rw [ArrayAlgebra.dot_eq_sum]
  simp only [paddedWitness, familyPublic, ArrayLayout.size_tab, min_self]
  rw [← Fin.sum_univ_eq_sum_range, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [ArrayLayout.getElem!_tab _ _ _ v.isLt, transparentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The actual batching polynomial assigns the family its constant term. -/
theorem initial_polynomial_constant {m : Nat} (c : Config) (lanes : Nat)
    (family : Fin m → FamilyClaim) (points : Array PointClaim)
    (w : Witness c lanes) (r : Prefix) :
    (InitialBatching.errorPolynomial (paddedWitness c lanes w)
      (transformedClaims (2 ^ c.logN) family points r)).coeff 0 =
      familyTarget (honestSlices c lanes family w) r -
        familyTarget (fun j => (family j).slices) r := by
  rw [InitialBatching.errorPolynomial_coeff _ _ 0 (by simp)]
  simp [InitialBatching.claimError, transformedClaims, familyPublic]
  exact dot_family c lanes family w r

/-- Original point i occupies exactly lambda^(i+1), not lambda^i. -/
theorem initial_polynomial_point {m : Nat} (width : Nat)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (f : Array E)
    (r : Prefix) (i : Fin points.size) :
    (InitialBatching.errorPolynomial f (transformedClaims width family points r)).coeff (i.val + 1) =
      dot f (publicPoint width points[i]).weight - pointValue points[i] := by
  rw [InitialBatching.errorPolynomial_coeff _ _ _ (by simp; omega)]
  rw [getElem!_pos _ _ (by simp; omega)]
  unfold transformedClaims
  rw [Array.getElem_append_right (by simp)]
  simp [InitialBatching.claimError, publicPoint]

open Classical

/-- The only ring escape charged: unequal fixed slice tables collide under the
sampled actual family map. The image list is derived from the commitment K list. -/
def Escape {m : Nat} (c : Config) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) (r : Prefix) : Prop :=
  ∃ w ∈ InitialCandidates.witnesses c lanes root,
    (fun j => (family j).slices) ≠ honestSlices c lanes family w ∧
    familyTarget (fun j => (family j).slices) r = familyTarget (honestSlices c lanes family w) r

/-- A false original statement is either a real fixed-list ring escape or a
false transformed public opening. No target-error premise is supplied. -/
theorem false_or_escape {m : Nat} (c : Config) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (r : Prefix)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses c lanes root, Honest c lanes family points w)
    (outside : ¬ Escape c lanes root family r) :
    ¬ ∃ w ∈ InitialCandidates.witnesses c lanes root,
      ∀ claim ∈ (transformedClaims (2 ^ c.logN) family points r).toList,
        dot (paddedWitness c lanes w) claim.weight = claim.value := by
  rintro ⟨w, hw, claims⟩
  have hf := claims (familyPublic (2 ^ c.logN) family r) (by simp [transformedClaims])
  rw [dot_family] at hf
  have hs : (fun j => (family j).slices) = honestSlices c lanes family w := by
    by_contra ne
    exact outside ⟨w, hw, ne, hf.symm⟩
  apply hfalse
  refine ⟨w, hw, hs, ?_⟩
  intro point hp
  apply claims (publicPoint (2 ^ c.logN) point)
  simp only [transformedClaims, Array.toList_append, Array.toList_map,
    List.mem_append, List.mem_map]
  exact Or.inr ⟨point, hp, rfl⟩

theorem escape_probability {m : Nat} (p : Profile) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) :
    Soundness.uniformProb (Finset.univ.filter (Escape (config p) lanes root family)) ≤
      (2 ^ 32 : ℚ) * (((m - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) := by
  let candidates := (InitialCandidates.witnesses (config p) lanes root).image
    (honestSlices (config p) lanes family)
  have h := RingMapBatchingConcrete.family_fixed_list (fun j => (family j).slices) candidates
  have heq : (Finset.univ.filter (Escape (config p) lanes root family)) =
      (Finset.univ.filter fun r : Prefix => ∃ honest ∈ candidates,
        (fun j => (family j).slices) ≠ honest ∧
        familyTarget (fun j => (family j).slices) r = familyTarget honest r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Escape, candidates, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, ne, he⟩
      exact ⟨_, ⟨w, hw, rfl⟩, ne, he⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, ne, he⟩
      exact ⟨w, hw, ne, he⟩
  rw [heq]
  simp only [familyTarget, executableMap_eq]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_image_le.trans (InitialCandidates.production_witnesses_card p lanes root))

/-- Executable experiment: expose gamma and six map scalars, then run the actual
causal WHIR verifier, whose first draw is lambda. The strategy may depend on the
whole ring prefix but never on a future WHIR challenge. -/
def experiment {m : Nat} (p : Profile) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) (points : Array PointClaim)
    (strategy : Prefix → Strategy) (randomness : Prefix × Tape (config p)) : Bool :=
  CausalGame.experiment (ExecutionShapes.Input p lanes root
    (transformedClaims (2 ^ (config p).logN) family points randomness.1))
    (strategy randomness.1) randomness.2

private theorem probability_mono {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ ω, P ω → Q ω) :
    Soundness.uniformProb (Finset.univ.filter P) ≤
      Soundness.uniformProb (Finset.univ.filter Q) := by
  unfold Soundness.uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    fun ω hω => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩)

/-- Ordinary interactive ring plus actual PCS accepted-false bound, with no
independence restriction on the post-prefix causal strategy. -/
theorem opening_probability {m : Nat} (p : Profile) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (strategy : Prefix → Strategy) :
    Soundness.uniformProb (Finset.univ.filter fun randomness : Prefix × Tape (config p) =>
      experiment p lanes root family points strategy randomness = true ∧
      ¬ ∃ w ∈ InitialCandidates.witnesses (config p) lanes root,
        Honest (config p) lanes family points w) ≤
      (2 ^ 32 : ℚ) * (((m - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) +
      GroupedChallenges.interactiveError (config p) (estimates (config p)) (1 + points.size) := by
  classical
  simp only [experiment]
  apply RingMapBatching.conditional_error (Escape (config p) lanes root family) _ _ _
    (InteractiveSoundness.error_nonneg _ _) (escape_probability p lanes root family)
  intro r outside
  have h := InteractiveSoundness.opening_probability p lanes root
    (transformedClaims (2 ^ (config p).logN) family points r) (strategy r)
  rw [transformedClaims_size] at h
  apply (probability_mono _ _ ?_).trans h
  intro t ht
  exact ⟨ht.1, false_or_escape (config p) lanes root family points r ht.2 outside⟩

/-- The list quantifier is outside every family, point and adaptive strategy. -/
theorem adaptive_list_binding (p : Profile) (lanes : Nat) (root : BaseOracle) :
    ∃ candidates : Finset (Witness (config p) lanes), candidates.card ≤ 2 ^ 32 ∧
      ∀ (m : Nat) (family : Fin m → FamilyClaim) (points : Array PointClaim) (strategy : Prefix → Strategy),
      Soundness.uniformProb (Finset.univ.filter fun randomness : Prefix × Tape (config p) =>
        experiment p lanes root family points strategy randomness = true ∧
        ¬ ∃ w ∈ candidates, Honest (config p) lanes family points w) ≤
        (2 ^ 32 : ℚ) * (((m - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) +
        GroupedChallenges.interactiveError (config p) (estimates (config p)) (1 + points.size) :=
  ⟨InitialCandidates.witnesses (config p) lanes root,
    InitialCandidates.production_witnesses_card p lanes root,
    fun _ family points strategy => opening_probability p lanes root family points strategy⟩

theorem transformedClaims_shapes {m : Nat} (width : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (r : Prefix)
    (j : Fin (transformedClaims width family points r).size) :
    (transformedClaims width family points r)[j].weight.size = width := by
  have all : ∀ claim ∈ (transformedClaims width family points r).toList,
      claim.weight.size = width := by
    intro claim hc
    simp only [transformedClaims, Array.toList_append, Array.toList_map,
      List.mem_append, List.mem_map] at hc
    rcases hc with hc | ⟨point, _, rfl⟩
    · have eq : claim = familyPublic width family r := by simpa using hc
      simp [eq, familyPublic, ArrayLayout.size_tab]
    · simp [publicPoint, ArrayLayout.size_tab]
  exact all _ (by simp)

/-- One uninterrupted source squeeze run is gamma, six map draws, then lambda.
This is the grouped bad relation for the eventual ROM adapter, not eight
independently selectable random-oracle opportunities. -/
def InitialEvent {m : Nat} (p : Profile) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (r : Prefix × E) : Prop :=
  Escape (config p) lanes root family r.1 ∨
    r.2 ∈ InitialBatching.candidateEscape (InitialCandidates.extensionCandidates (config p) lanes root)
      (transformedClaims (2 ^ (config p).logN) family points r.1)

theorem initial_event_probability {m : Nat} (p : Profile) (lanes : Nat) (root : BaseOracle)
    (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) :
    Soundness.uniformProb (Finset.univ.filter (InitialEvent p lanes root family points)) ≤
      (2 ^ 32 : ℚ) * (((m - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) +
      (points.size : ℚ) / 2 ^ 160 := by
  apply RingMapBatching.conditional_error (Escape (config p) lanes root family) _ _ _
    (by positivity) (escape_probability p lanes root family)
  intro r outside
  have h := InitialSoundness.initial_escape_probability p lanes root lane_bound
    (transformedClaims (2 ^ (config p).logN) family points r)
    (transformedClaims_shapes _ _ _ _)
  simpa only [InitialEvent, outside, false_or, Finset.filter_mem_eq_inter,
    Finset.univ_inter, transformedClaims_size, Nat.add_sub_cancel_left] using h

end Whir.RingPCSGame
