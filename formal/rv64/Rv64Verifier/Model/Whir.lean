import Rv64Verifier.Model.Transcript
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Model.FieldAlg

/-!
# The polynomial-commitment opening as the Rust runs it

`crates/verifier/src/whir.rs`, `ring_switch.rs` and `lib.rs`'s `verify_stacked_opening`, mirrored
in `TM` and proved to run the statement's programs (`Sim`). Arithmetic is in `E` and `K` (the
limb-level algorithms are `FieldAlg`'s), `field::powers` is the statement's `powers`
(`powersM_eq`), `E::pow` is `^` (`epow_eq`), and the multilinear helpers are `Multilinear`'s
mirrors. A `u64` is a `BitVec 64`, a shift by a `usize` amount masked to six bits.

A function the Rust can panic in returns an `Option` (a panic, like an `Err`, gives no result).
A weight the Rust evaluates at the terminal point is an `Option`-valued function here, and the
statement's closure is related to it by `WeightRel`: wherever the Rust's evaluation returns, it
returns the statement's value.
-/

namespace Rv64Verifier.Model.Pcs

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The WHIR parameters (`whir.rs:12-63`) -/

/-- `INITIAL_FOLDING_FACTOR`. -/
def initialFoldingFactor : ℕ := 6
/-- `SUBSEQUENT_FOLDING_FACTOR`. -/
def subsequentFoldingFactor : ℕ := 4
/-- `RS_DOMAIN_INITIAL_REDUCTION_FACTOR`. -/
def rsDomainInitialReductionFactor : ℕ := 3
/-- `RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`. -/
def rsDomainSubsequentReductionFactor : ℕ := 1
/-- `RESIDUAL_MAX_LOG`. -/
def residualMaxLogRust : ℕ := 5
/-- `QUERY_GRINDING_BITS`. -/
def queryGrindingBitsRust : ℕ := 17
/-- `MIN_STACKED_LOG` (`layout.rs`). -/
def minStackedLog : ℕ := 15
/-- `MAX_STACKED_LOG` (`layout.rs`). -/
def maxStackedLog : ℕ := 28

theorem whir_constants :
    initialFoldingFactor = Whir.initialFold ∧ subsequentFoldingFactor = Whir.subsequentFold ∧
      rsDomainInitialReductionFactor = Whir.initialReduction ∧
      rsDomainSubsequentReductionFactor = Whir.subsequentReduction ∧
      residualMaxLogRust = Whir.residualMaxLog ∧ queryGrindingBitsRust = Whir.queryGrindingBits ∧
      minStackedLog = Whir.minLogStack ∧ maxStackedLog = Whir.maxLogStack :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `WHIR_QUERIES`, verbatim. -/
def whirQueriesTable : List (List (List ℕ)) := [
    [[222,55], [223,56,30], [223,56,31], [223,56,32], [223,56,32], [223,56,32,22], [223,56,32,22], [224,56,32,23], [224,56,32,23], [224,56,32,23,17], [224,56,32,23,17], [224,56,32,23,18], [225,56,32,23,18], [225,56,32,23,18,14]],
    [[111,45], [112,45,27], [112,45,28], [112,45,28], [112,45,28], [112,45,28,20], [112,45,28,20], [112,45,28,21], [112,45,28,21], [112,45,28,21,16], [112,45,28,21,16], [112,45,28,21,16], [112,45,28,21,16], [112,45,28,21,16,13]],
    [[75,37], [75,37,24], [75,37,25], [75,38,25], [75,38,25], [75,38,25,18], [75,38,25,19], [75,38,25,19], [75,38,25,19], [75,38,25,19,15], [75,38,25,19,15], [75,38,25,19,15], [75,38,25,19,15], [75,38,25,19,15,13]],
    [[56,32], [56,32,22], [56,32,22], [56,32,23], [56,32,23], [56,32,23,17], [56,32,23,17], [56,32,23,18], [56,32,23,18], [56,32,23,18,14], [56,32,23,18,14], [56,32,23,18,14], [56,32,23,18,15], [56,32,23,18,15,12]]]

theorem whirQueriesTable_eq : whirQueriesTable = Whir.queryTable := by decide +kernel

/-- `usize::checked_sub`. -/
def checkedSub (a b : ℕ) : Option ℕ := if b ≤ a then some (a - b) else none

/-- `whir_queries`: `WHIR_QUERIES.get(log_inv_rate.checked_sub(1)?)?.get(log_n.checked_sub(MIN_STACKED_LOG)?)`. -/
def whirQueriesRust (logN logInvRate : ℕ) : Option (List ℕ) := do
  let row ← whirQueriesTable[← checkedSub logInvRate 1]?
  row[← checkedSub logN minStackedLog]?

/-- `WhirConfig`. -/
structure WhirConfigRust where
  logInvRates : List ℕ
  folds : List ℕ
  queries : List ℕ
  deriving DecidableEq

/-- `derive_config`'s `while remaining > RESIDUAL_MAX_LOG` loop on `(folds, log_inv_rates)`.
`fuel` bounds it: every iteration folds at least one variable. -/
def configLoop : (fuel remaining : ℕ) → List ℕ → List ℕ → List ℕ × List ℕ
  | 0, _, folds, rates => (folds, rates)
  | fuel + 1, remaining, folds, rates =>
    if remaining > residualMaxLogRust then
      let reduction := if folds.length = 1 then rsDomainInitialReductionFactor
        else rsDomainSubsequentReductionFactor
      let rates := rates ++ [rates.getLastD 0 + folds.getLastD 0 - reduction]
      let fold := min subsequentFoldingFactor remaining
      configLoop fuel (remaining - fold) (folds ++ [fold]) rates
    else (folds, rates)

/-- `derive_config`. -/
def deriveConfigRust (logN logInvRate : ℕ) : Option WhirConfigRust := do
  let queries ← whirQueriesRust logN logInvRate
  let (folds, rates) :=
    configLoop logN (logN - initialFoldingFactor) [initialFoldingFactor] [logInvRate]
  if queries.length = folds.length then some ⟨rates, folds, queries⟩ else none

/-- The Rust's configuration of a ladder. -/
def configOfLadder (ls : List Whir.Level) : WhirConfigRust :=
  ⟨ls.map (·.logInvRate), ls.map (·.fold), ls.map (·.queries)⟩

theorem whirQueriesRust_none {logN logInvRate : ℕ} (h : ¬ Whir.Admissible logN logInvRate) :
    whirQueriesRust logN logInvRate = none := by
  have hrows : ∀ row ∈ whirQueriesTable, row.length = 14 := by decide +kernel
  have hlen : whirQueriesTable.length = 4 := rfl
  unfold Whir.Admissible Whir.minLogStack Whir.maxLogStack at h
  unfold whirQueriesRust checkedSub
  by_cases h1 : 1 ≤ logInvRate
  · by_cases h15 : minStackedLog ≤ logN
    · simp only [h1, h15, ite_true]
      by_cases h4 : logInvRate ≤ 4
      · have hl : logInvRate - 1 < whirQueriesTable.length := by omega
        have hr := hrows _ (List.getElem_mem hl)
        have hn : (whirQueriesTable[logInvRate - 1])[logN - minStackedLog]? = none := by
          apply List.getElem?_eq_none
          simp only [minStackedLog] at h15 ⊢
          omega
        simp [List.getElem?_eq_getElem hl, hn]
      · have hn : whirQueriesTable[logInvRate - 1]? = none := List.getElem?_eq_none (by omega)
        simp [hn]
    · simp [h15]
  · simp [h1]

/-- The finite window, decided. -/
theorem deriveConfigRust_window :
    ∀ μ < 29, ∀ r < 5, Whir.Admissible μ r →
      deriveConfigRust μ r = (Whir.ladder μ r).map configOfLadder := by
  decide +kernel

/-- **`derive_config` is `ladder`.** -/
theorem deriveConfigRust_eq (logN logInvRate : ℕ) :
    deriveConfigRust logN logInvRate = (Whir.ladder logN logInvRate).map configOfLadder := by
  by_cases h : Whir.Admissible logN logInvRate
  · have h' := h
    unfold Whir.Admissible Whir.minLogStack Whir.maxLogStack at h'
    exact deriveConfigRust_window logN (by omega) logInvRate (by omega) h
  · rw [Whir.ladder, ite_eq_right h, deriveConfigRust, whirQueriesRust_none h]
    rfl

/-- `whir_queries` is the statement's table at the window. -/
theorem whirQueriesRust_eq (logN logInvRate : ℕ) :
    whirQueriesRust logN logInvRate = if Whir.Admissible logN logInvRate then
      some ((Whir.queryTable.getD (logInvRate - 1) []).getD (logN - Whir.minLogStack) [])
    else none := by
  by_cases h : Whir.Admissible logN logInvRate
  · rw [ite_eq_left h]
    have h' := h
    unfold Whir.Admissible Whir.minLogStack Whir.maxLogStack at h'
    have : ∀ μ < 29, ∀ r < 5, Whir.Admissible μ r → whirQueriesRust μ r =
        some ((Whir.queryTable.getD (r - 1) []).getD (μ - Whir.minLogStack) []) := by
      decide +kernel
    exact this logN (by omega) logInvRate (by omega) h
  · rw [ite_eq_right h, whirQueriesRust_none h]

/-- What the opening uses of a ladder, decided on the window. -/
def LadderFacts (μ : ℕ) (ls : List Whir.Level) : Prop :=
  μ ≤ 28 ∧ ls.head?.map (·.fold) = some initialFoldingFactor ∧
    (ls.map (·.fold)).sum + 2 ≤ μ ∧ ∀ l ∈ ls, l.logInvRate ≤ 20

instance (μ : ℕ) (ls : List Whir.Level) : Decidable (LadderFacts μ ls) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `LadderFacts` of the ladder, where there is one. -/
def ladderFactsB (μ r : ℕ) : Bool :=
  match Whir.ladder μ r with
  | some ls => decide (LadderFacts μ ls)
  | none => true

theorem ladder_facts_window : ∀ μ < 29, ∀ r < 5, ladderFactsB μ r = true := by
  decide +kernel

theorem ladder_facts {μ r : ℕ} {ls : List Whir.Level} (h : Whir.ladder μ r = some ls) :
    LadderFacts μ ls := by
  have ha : Whir.Admissible μ r := by
    by_contra hn
    rw [Whir.ladder, ite_eq_right hn] at h
    cases h
  unfold Whir.Admissible Whir.minLogStack Whir.maxLogStack at ha
  have := ladder_facts_window μ (by omega) r (by omega)
  rw [ladderFactsB, h] at this
  exact of_decide_eq_true this

/-! ## Ring switching (`ring_switch.rs`) -/

/-- The Rust's weight `w` (`None` where it panics) returns the statement's `f` wherever it
returns. -/
def WeightRel (w : List E → Option E) (f : List E → E) : Prop := ∀ x v, w x = some v → v = f x

/-- `RING_MAP_SHIFTS`. -/
def ringMapShiftsRust : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `K_BITS` (`layout.rs`). -/
def kBitsRust : ℕ := 64

/-- `ring_map`: `value += challenge * value.pow(1 << shift)` over the zipped stages. -/
def ringMapRust (value : E) (challenges : List E) : E :=
  (challenges.zip ringMapShiftsRust).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

theorem ringMapRust_eq (value : E) (challenges : List E) :
    ringMapRust value challenges = phiMap value challenges := rfl

/-- One coefficient of `ring_weight`: over `frobenius.iter_mut().zip(r_prime)`,
`product *= ONE + *value + challenge` and `*value = value.square()`. -/
def ringWeightPass (rPrime : List E) (c : E) (frobenius : List E) : E × List E :=
  ((frobenius.zip rPrime).foldl (fun product (value, challenge) ↦ product * (1 + value + challenge)) c,
    (frobenius.zip rPrime).map (fun p ↦ p.1 * p.1) ++ frobenius.drop rPrime.length)

/-- `ring_weight`: `assert_eq!(r.len(), r_prime.len())`, then `total += product` per
coefficient, `frobenius` starting at `r`. -/
def ringWeightRust (r rPrime coefficients : List E) : Option E :=
  if r.length = rPrime.length then
    some (coefficients.foldl (fun (acc : E × List E) c ↦
      let pass := ringWeightPass rPrime c acc.2
      (acc.1 + pass.1, pass.2)) (0, r)).1
  else none

theorem ringWeightPass_snd (rPrime : List E) (c : E) :
    ∀ frobenius : List E, frobenius.length = rPrime.length →
      (ringWeightPass rPrime c frobenius).2 = frobenius.map (· ^ 2) := by
  induction rPrime with
  | nil => intro f hf; rw [List.length_eq_zero_iff.mp hf]; rfl
  | cons x xs ih =>
    intro f hf
    cases f with
    | nil => cases hf
    | cons v vs =>
      have := ih vs (by simpa using hf)
      simp only [ringWeightPass, List.zip_cons_cons, List.map_cons, List.length_cons,
        List.drop_succ_cons, List.cons_append] at this ⊢
      rw [this, sq]

theorem ringWeightRust_eq (r rPrime coefficients : List E) (h : r.length = rPrime.length) :
    ringWeightRust r rPrime coefficients = some (ringWeight r rPrime coefficients) := by
  rw [ringWeightRust, ite_eq_left h, ringWeight]
  congr 1
  suffices ∀ (cs : List E) (acc : E × List E), acc.2.length = rPrime.length →
      cs.foldl (fun (acc : E × List E) c ↦
        let pass := ringWeightPass rPrime c acc.2
        (acc.1 + pass.1, pass.2)) acc =
      cs.foldl (fun (acc : E × List E) c ↦
        let product := (List.zip acc.2 rPrime).foldl
          (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
        (acc.1 + product, acc.2.map (· ^ 2))) acc by
    rw [this coefficients (0, r) h]
  intro cs
  induction cs with
  | nil => intro acc _; rfl
  | cons c cs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    rw [ringWeightPass_snd rPrime c acc.2 hacc]
    exact ih _ (by simpa using hacc)

/-- **`ring_weight`, wherever it returns, is `ringWeight`.** -/
theorem ringWeightRust_rel (r coefficients : List E) :
    WeightRel (fun rPrime ↦ ringWeightRust r rPrime coefficients)
      (fun rPrime ↦ ringWeight r rPrime coefficients) := by
  intro x v hv
  dsimp only at hv ⊢
  by_cases h : r.length = x.length
  · rw [ringWeightRust_eq r x coefficients h] at hv
    exact (Option.some.inj hv).symm
  · simp only [ringWeightRust, ite_eq_right h] at hv
    cases hv

/-- The Frobenius coefficients: `(0..K_BITS).map(coefficient)`. -/
def ringCoefficientsRust (challenges : List E) : List E :=
  (List.range kBitsRust).map fun k ↦
    ((challenges.zip ringMapShiftsRust).filter fun (_, shift) ↦ k &&& shift ≠ 0).foldl
      (fun acc (f, shift) ↦ acc * f ^ (2 ^ (k % shift))) 1

theorem ringCoefficientsRust_eq (challenges : List E) :
    ringCoefficientsRust challenges = ringCoefficients challenges := rfl

/-- `RingWeight`: the claim's point and the map's Frobenius coefficients. -/
structure RingWeightRust where
  point : List E
  coefficients : List E

/-- `RingWeight::evaluate`. -/
def RingWeightRust.evaluate (w : RingWeightRust) (rPrime : List E) : Option E :=
  ringWeightRust w.point rPrime w.coefficients

/-- `ring_switch`. -/
def ringSwitchRust (point s : List E) : TM (E × RingWeightRust) := do
  let challenges ← TM.samples ringMapShiftsRust.length
  let coefficients := ringCoefficientsRust challenges
  let images := s.map fun value ↦ ringMapRust value challenges
  let target := polyEvalRust images gen
  pure (target, ⟨point, coefficients⟩)

/-- **`ring_switch` runs `ringSwitch`**: the same target, and a weight that, wherever it
returns, is the statement's. -/
theorem ringSwitchRust_sim (point s : List E) :
    SimR (ringSwitchRust point s) (ringSwitch point s)
      (fun a b ↦ a.1 = b.1 ∧ WeightRel a.2.evaluate b.2) := by
  refine SimR.bind (SimR.of_sim (Sim.samples _)) fun a b hab ↦ ?_
  subst hab
  refine SimR.pure ⟨?_, ?_⟩
  · simp only [polyEvalRust_eq, ringMapRust_eq]
  · simp only [ringCoefficientsRust_eq]
    exact ringWeightRust_rel point (ringCoefficients a)

/-! ## Transcript helpers -/

/-- `for _ in 0..n`. -/
def TM.loopN {σ : Type} (f : σ → TM σ) : ℕ → σ → TM σ
  | 0, s => pure s
  | n + 1, s => do
    let s ← f s
    TM.loopN f n s

/-- `for i in start..start + n`. -/
def TM.forRange {σ : Type} (f : ℕ → σ → TM σ) (start : ℕ) : ℕ → σ → TM σ
  | 0, s => pure s
  | n + 1, s => do
    let s ← f start s
    TM.forRange f (start + 1) n s

/-- `Transcript::merkle(root, block_length, queries, leaf_words)` on commitment `i`: `TM.merkle`
authenticates the phase against the shape recorded with the root, and the Rust's own check that
every leaf has `leaf_words` words is kept. -/
def TM.merkleLeaves (i : ℕ) (queries : List (BitVec 64)) (leafWords : ℕ) : TM (List (List K)) := do
  let rows ← TM.merkle i (queries.map BitVec.toNat)
  TM.require (∀ row ∈ rows, row.length = leafWords)
  pure rows

/-- `&slice[start..]`, a panic past the end. -/
def sliceFrom {α : Type} (start : ℕ) (l : List α) : Option (List α) :=
  if start ≤ l.length then some (l.drop start) else none

/-- `&slice[..stop]`, a panic past the end. -/
def sliceTo {α : Type} (stop : ℕ) (l : List α) : Option (List α) :=
  if stop ≤ l.length then some (l.take stop) else none

/-! ## The WHIR opening's pure parts (`whir.rs:65-155`) -/

/-- `ext_row`: the full chunks of three words (`as_chunks`), each `E::new(c0, c1, c2)`. -/
def extRowRust : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRowRust rest
  | _ => []

/-- The `depth` bits at `chunk * depth` of the 192-bit integer `bits`, which may straddle two
limbs, masked by `block_length - 1`. -/
def queryWindow (bits : List (BitVec 64)) (blockLength : BitVec 64) (depth chunk : ℕ) :
    BitVec 64 :=
  let limb := chunk * depth / 64
  let shift := chunk * depth % 64
  let window : BitVec 128 :=
    ((bits.getD limb 0).setWidth 128 ||| (bits.getD (limb + 1) 0).setWidth 128 <<< 64) >>> shift
  window.setWidth 64 &&& (blockLength - 1)

/-- `sample_queries`' loop, `while result.len() < count`. `fuel` bounds it: every iteration adds
at least one position. -/
def sampleQueriesLoop (blockLength : BitVec 64) (depth count : ℕ) :
    ℕ → List (BitVec 64) → TM (List (BitVec 64))
  | 0, result => pure result
  | fuel + 1, result =>
    if result.length < count then do
      let sample ← TM.sample
      let bits := [(sample.limb 0).toBitVec, (sample.limb 1).toBitVec, (sample.limb 2).toBitVec,
        0#64]
      let chunks := (List.range (min (192 / depth) (count - result.length))).map
        (queryWindow bits blockLength depth)
      sampleQueriesLoop blockLength depth count fuel (result ++ chunks)
    else pure result

/-- `sample_queries`. -/
def sampleQueriesRust (blockLength : BitVec 64) (count : ℕ) : TM (List (BitVec 64)) := do
  let depth ← TM.ofOption (log2StrictRust blockLength)
  sampleQueriesLoop blockLength depth count count []

/-- One iteration of `subspace_roots`: the layer square-and-shifted by the last root, then its
first value moved to the roots (`layer.remove(0)`, a panic on an empty layer). -/
def subspaceRootsStep (st : List K × List K) : Option (List K × List K) :=
  let root := st.1.getLastD 0
  match st.2.map fun value ↦ value * value + root * value with
  | [] => none
  | first :: rest => some (st.1 ++ [first], rest)

/-- `subspace_roots`' loop. -/
def subspaceRootsLoop : ℕ → List K × List K → Option (List K × List K)
  | 0, st => some st
  | n + 1, st => do
    let st ← subspaceRootsStep st
    subspaceRootsLoop n st

/-- `subspace_roots`: from `[K(1)]` and the layer `(1..=log_n).map(|i| K(1 << i))`. -/
def subspaceRootsRust (logN : ℕ) : Option (List K) :=
  (subspaceRootsLoop logN
    ([1], (List.range' 1 logN).map fun i ↦ BF64.ofBitVec (1#64 <<< (i % 64)))).map (·.1)

/-- `induced_weight`. -/
def inducedWeightRust (messageLog : ℕ) (queries : List (BitVec 64)) (queryWeights point : List E) :
    Option E :=
  if point.length = messageLog then do
    let roots ← subspaceRootsRust messageLog
    let inverses := roots.map (·⁻¹)
    some ((queryWeights.zip queries).foldl (fun total (weight, query) ↦
      let acc := point.zipIdx.foldl (fun (acc : E × K) (challenge, coordinate) ↦
        (acc.1 * (1 + challenge * ofK (1 + acc.2 * inverses.getD coordinate 0)),
          acc.2 * acc.2 + roots.getD coordinate 0 * acc.2)) (weight, BF64.ofBitVec query)
      total + acc.1) 0)
  else none

/-- `GluedWeight`. -/
inductive GluedWeightRust where
  | ood (point : List E)
  | queries (messageLog : ℕ) (queries : List (BitVec 64)) (queryWeights : List E)

/-- `GluedWeight::evaluate`. -/
def GluedWeightRust.evaluate : GluedWeightRust → List E → Option E
  | .ood point, x => some (eqEvalRust point x)
  | .queries messageLog positions queryWeights, x =>
    inducedWeightRust messageLog positions queryWeights x

/-- `GluedClaim`. -/
structure GluedClaimRust where
  scalar : E
  foldStart : ℕ
  weight : GluedWeightRust

/-- `verify_whir`'s locals that live across levels: `running_quad`, `folds`, `glued`. -/
structure WhirLocals where
  runningQuad : List E
  folds : List E
  glued : List GluedClaimRust

/-- `for (q, i) in running_quad.iter_mut().zip(intro) { *q += scalar * i }`. -/
def zipAddScaled (quad intro : List E) (scalar : E) : List E :=
  (quad.zip intro).map (fun p ↦ p.1 + scalar * p.2) ++ quad.drop intro.length

/-- One pending claim glued: `scalar *= lam`, the intro added to the running quadratic, the
claim pushed. -/
def glueStepRust (lam : E) (acc : WhirLocals × E) (p : List E × GluedWeightRust) : WhirLocals × E :=
  let scalar := acc.2 * lam
  ({ acc.1 with
      runningQuad := zipAddScaled acc.1.runningQuad p.1 scalar,
      glued := acc.1.glued ++ [⟨scalar, acc.1.folds.length, p.2⟩] }, scalar)

/-- The level's pending claims glued with powers of `lam` (`whir.rs:221-232`). -/
def glueRust (lam : E) (s : WhirLocals) (pending : List (List E × GluedWeightRust)) :
    WhirLocals :=
  (pending.foldl (glueStepRust lam) (s, 1)).1

/-- `base_dot`: `E::sum(row.iter().rev().zip(&lane_weights).map(|(&word, &weight)| weight * word))`. -/
def baseDot (laneWeights : List E) (row : List K) : E :=
  ((row.reverse.zip laneWeights).map fun p ↦ p.2 * ofK p.1).foldl (· + ·) 0

/-- `row_values`: level 0's rows by `base_dot`, a deeper level's by `dot(ext_row(row), _)`. -/
def rowValuesRust (level : ℕ) (words : List (List K)) (laneWeights : List E) : List E :=
  if level = 0 then words.map (baseDot laneWeights)
  else words.map fun row ↦ dotRust (extRowRust row) laneWeights

/-! ## `verify_whir` (`whir.rs:158-265`) -/

/-- One fold round: sample, push it to `folds` and `level_folds`, read the next quadratic. -/
def foldRoundRust (st : WhirLocals × List E) : TM (WhirLocals × List E) := do
  let challenge ← TM.sample
  let quad ← TM.sumcheckRoundPoly 3 (polyEvalRust st.1.runningQuad challenge) none
  pure ({ st.1 with folds := st.1.folds ++ [challenge], runningQuad := quad }, st.2 ++ [challenge])

/-- One tail round, on `(running_quad, tail_folds, running_target)`. -/
def tailRoundRust (messageLog roundIndex : ℕ) (st : List E × List E × E) :
    TM (List E × List E × E) := do
  let challenge ← TM.sample
  let runningTarget := polyEvalRust st.1 challenge
  let tailFolds := st.2.1 ++ [challenge]
  if roundIndex + 1 < messageLog then do
    let quad ← TM.sumcheckRoundPoly 3 runningTarget none
    pure (quad, tailFolds, runningTarget)
  else pure (st.1, tailFolds, runningTarget)

/-- The terminal weight (`whir.rs:252-257`): the basis at the point rotated by the lane folds,
then every glued claim at its suffix of the point. -/
def terminalWeightRust (basis : List E → Option E) (laneFolds : ℕ) (glued : List GluedClaimRust)
    (point : List E) : Option E := do
  let high ← sliceFrom laneFolds point
  let low ← sliceTo laneFolds point
  let weight ← basis (high ++ low)
  glued.foldlM (fun weight claim ↦ do
    let x ← sliceFrom claim.foldStart point
    let value ← claim.weight.evaluate x
    pure (weight + claim.scalar * value)) weight

/-- The level loop of `verify_whir`, from level `level` on, over the zipped `(fold, rate)` pairs
left. The root a level opens is commitment `level`: the stack's root is commitment `0`, and the
root read at level `ℓ` is commitment `ℓ + 1`. The height and width given to `TM.commit` are the
ghost shape the root is opened at a level later. -/
def whirLevelsRust (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E) :
    ℕ → List (ℕ × ℕ) → WhirLocals → TM Unit
  | _, [], _ => TM.fail
  | level, (foldCount, levelRate) :: rest, s => do
    let (s, levelFolds) ← TM.loopN foldRoundRust foldCount (s, [])
    let messageLog := logN - s.folds.length
    let finalLevel := level = config.folds.length - 1
    let (residual, pending) ← if finalLevel then do
        let residual ← TM.nextScalars (2 ^ (messageLog % 64))
        pure (residual, ([] : List (List E × GluedWeightRust)))
      else do
        let shape := match rest with
          | (nextFold, nextRate) :: _ => (messageLog - nextFold + nextRate, 3 * 2 ^ nextFold)
          | [] => (0, 0)
        let _ ← TM.commit shape.1 shape.2
        let oodPoint ← TM.samples messageLog
        let oodValue ← TM.nextScalar
        let intro ← TM.sumcheckRoundPoly 3 oodValue none
        pure ([], [(intro, GluedWeightRust.ood oodPoint)])
    TM.grind queryGrindingBitsRust
    let blockLength : BitVec 64 := 1#64 <<< ((messageLog + levelRate) % 64)
    let count ← TM.ofOption config.queries[level]?
    let queries ← sampleQueriesRust blockLength count
    let lam ← TM.sample
    let queryWeights := powers lam queries.length
    let lanes := 2 ^ (foldCount % 64)
    let leafWords := if level = 0 then lanes else 3 * lanes
    let words ← TM.merkleLeaves level queries leafWords
    let laneWeights := eqKernelRust levelFolds
    let enforced := dotRust (rowValuesRust level words laneWeights) queryWeights
    let intro ← TM.sumcheckRoundPoly 3 enforced none
    let pending := pending ++ [(intro, GluedWeightRust.queries messageLog queries queryWeights)]
    let s := glueRust lam s pending
    if finalLevel then do
      let (_, tailFolds, runningTarget) ←
        TM.forRange (tailRoundRust messageLog) 0 messageLog (s.runningQuad, [], 0)
      let point := s.folds ++ tailFolds
      let laneFolds ← TM.ofOption config.folds[0]?
      let weight ← TM.ofOption (terminalWeightRust basis laneFolds s.glued point)
      let residualValue ← TM.ofOption (multilinearEvalRust residual tailFolds)
      TM.require (weight * residualValue = runningTarget)
    else whirLevelsRust logN config basis (level + 1) rest s

/-- `verify_whir` in checked mode, the root being commitment `0`; `basis` is the batched basis's
`evaluate`. -/
def verifyWhirRust (logN logInvRate : ℕ) (target : E) (basis : List E → Option E) : TM Unit := do
  let config ← TM.ofOption (deriveConfigRust logN logInvRate)
  let runningQuad ← TM.sumcheckRoundPoly 3 target none
  whirLevelsRust logN config basis 0 (config.folds.zip config.logInvRates) ⟨runningQuad, [], []⟩

/-! ## Simulation of the pieces -/

theorem SimR.map_right {α β γ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {Q : β → VerifierProgram γ} {r' : α → γ → Prop} (h : SimR m P r)
    (hk : ∀ a b, r a b → SimR (Pure.pure a : TM α) (Q b) r') : SimR m (P >>= Q) r' := by
  have := SimR.bind h hk
  simpa only [bind_pure] using this

theorem SimR.nextScalars_len : ∀ n, SimR (TM.nextScalars n) (VerifierProgram.readScalars n)
    (fun a b ↦ a = b ∧ a.length = n)
  | 0 => SimR.pure ⟨rfl, rfl⟩
  | n + 1 => by
    refine SimR.bind (SimR.of_sim Sim.nextScalar) ?_
    rintro x _ rfl
    refine SimR.bind (SimR.nextScalars_len n) ?_
    rintro xs _ ⟨rfl, hl⟩
    exact SimR.pure ⟨rfl, by simp [hl]⟩

theorem SimR.sumcheckRoundPoly3 (claim : E) :
    SimR (TM.sumcheckRoundPoly 3 claim none) (sumcheckRoundPoly 3 claim none)
      (fun a b ↦ a = b ∧ a.length = 3) := by
  rw [TM.sumcheckRoundPoly, sumcheckRoundPoly]
  refine SimR.bind (SimR.of_sim Sim.nextScalar) ?_
  rintro c _ rfl
  refine SimR.bind (SimR.nextScalars_len _) ?_
  rintro tail _ ⟨rfl, hl⟩
  exact SimR.pure ⟨rfl, by simp [hl]⟩

/-- A claim glued into the running sumcheck: the same power of `λ` and level, and a weight that,
wherever the Rust's returns, is the statement's. -/
def GluedRel (c : GluedClaimRust) (c' : GluedClaim) : Prop :=
  c.scalar = c'.scalar ∧ c.foldStart = c'.foldStart ∧ WeightRel c.weight.evaluate c'.weightAt

/-- The Rust's locals stand for the statement's `WhirState`, and what the Rust relies on holds:
the running quadratic has three coefficients and every claim's level precedes the folds. -/
def LocalsRel (s : WhirLocals) (s' : WhirState) : Prop :=
  s.runningQuad = s'.runningQuad ∧ s.folds = s'.folds ∧ s.runningQuad.length = 3 ∧
    List.Forall₂ GluedRel s.glued s'.glued ∧ ∀ c ∈ s.glued, c.foldStart ≤ s.folds.length

theorem foldLoop_sim : ∀ (n : ℕ) (sr : WhirLocals) (ss : WhirState) (lf : List E),
    LocalsRel sr ss →
    SimR (TM.loopN foldRoundRust n (sr, lf)) (foldRounds n ss lf)
      (fun a b ↦ LocalsRel a.1 b.1 ∧ a.2 = b.2 ∧ a.1.folds.length = sr.folds.length + n)
  | 0, sr, ss, lf, h => SimR.pure ⟨h, rfl, rfl⟩
  | n + 1, ⟨q, f, g⟩, ⟨q', f', g'⟩, lf, h => by
    obtain ⟨hq, hf, hl, hg, hs⟩ := h
    dsimp only at hq hf hl hg hs
    subst hq hf
    simp only [TM.loopN, foldRoundRust, bind_assoc, pure_bind]
    rw [foldRounds]
    refine SimR.bind (SimR.of_sim Sim.sample) ?_
    rintro c _ rfl
    rw [polyEvalRust_eq]
    refine SimR.bind (SimR.sumcheckRoundPoly3 _) ?_
    rintro quad _ ⟨rfl, hq3⟩
    refine SimR.mono (foldLoop_sim n _ _ _ ⟨rfl, rfl, hq3, hg, ?_⟩) ?_
    · intro c hc
      have := hs c hc
      simp only [List.length_append, List.length_singleton]
      omega
    · rintro a b ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [h3]
      simp only [List.length_append, List.length_singleton]
      omega

theorem tailLoop_sim (ml : ℕ) : ∀ (n i : ℕ) (quad tail : List E) (tgt : E), i + n = ml → 0 < n →
    SimR (TM.forRange (tailRoundRust ml) i n (quad, tail, tgt)) (tailRounds n quad)
      (fun a b ↦ a.2.1 = tail ++ b.1 ∧ a.2.2 = b.2 ∧ b.1.length = n)
  | 0, _, _, _, _, _, h0 => absurd h0 (Nat.lt_irrefl 0)
  | k + 1, i, quad, tail, tgt, hi, _ => by
    simp only [TM.forRange, tailRoundRust, bind_assoc]
    rw [tailRounds]
    refine SimR.bind (SimR.of_sim Sim.sample) ?_
    rintro c _ rfl
    rw [polyEvalRust_eq]
    by_cases hk : k = 0
    · subst hk
      have hlt : ¬ (i + 1 < ml) := by omega
      simp only [hlt, ↓reduceIte, pure_bind, TM.forRange]
      exact SimR.pure ⟨rfl, rfl, rfl⟩
    · have hlt : i + 1 < ml := by omega
      simp only [hlt, hk, ↓reduceIte, bind_assoc, pure_bind]
      refine SimR.bind (SimR.of_sim (Sim.sumcheckRoundPoly _ _ _)) ?_
      rintro quad' _ rfl
      refine SimR.map_right (tailLoop_sim ml k (i + 1) quad' _ _ (by omega) (by omega)) ?_
      rintro a ⟨rest, target⟩ ⟨h1, h2, h3⟩
      exact SimR.pure ⟨by rw [h1]; simp, h2, by simp [h3]⟩

theorem extRowRust_eq : ∀ row : List K, row.length % 3 = 0 → extRowRust row = extRow row
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | c0 :: c1 :: c2 :: rest, h => by
    rw [extRowRust, extRow, extRowRust_eq rest (by simp at h; omega)]

theorem dot_map_eq_foldl {α : Type} (f : α → E) : ∀ (rows : List α) (qw : List E) (acc : E),
    (List.zipWith (· * ·) (rows.map f) qw).foldl (· + ·) acc =
      (List.zip qw rows).foldl (fun total (p : E × α) ↦ total + p.1 * f p.2) acc
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | row :: rows, w :: qw, acc => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.foldl_cons, List.zip_cons_cons]
    rw [mul_comm]
    exact dot_map_eq_foldl f rows qw _

theorem baseDot_eq (laneWeights : List E) (row : List K) :
    baseDot laneWeights row = dot (row.reverse.map ofK) laneWeights := by
  rw [baseDot, dot]
  congr 1
  generalize row.reverse = l
  induction l generalizing laneWeights with
  | nil => simp
  | cons a l ih =>
    cases laneWeights with
    | nil => simp
    | cons w ws =>
      simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, ih, mul_comm]

theorem enforced_eq (level : ℕ) (words : List (List K)) (levelFolds queryWeights : List E)
    (hw : level ≠ 0 → ∀ row ∈ words, row.length % 3 = 0) :
    dotRust (rowValuesRust level words (eqKernelRust levelFolds)) queryWeights =
      enforcedSum (if level = 0 then words.map fun row ↦ row.reverse.map ofK
        else words.map extRow) levelFolds queryWeights := by
  rw [eqKernelRust_eq, dotRust_eq, enforcedSum, rowValuesRust]
  by_cases h0 : level = 0
  · simp only [h0, ↓reduceIte]
    rw [dot, dot_map_eq_foldl, List.zip_map_right, List.foldl_map]
    apply foldl_congr_mem
    intro total p _
    rw [baseDot_eq]
    rfl
  · simp only [h0, ↓reduceIte]
    rw [dot, dot_map_eq_foldl, List.zip_map_right, List.foldl_map]
    apply foldl_congr_mem
    intro total p hp
    have hrow : p.2 ∈ words := (List.of_mem_zip hp).2
    rw [dotRust_eq, extRowRust_eq _ (hw h0 _ hrow)]
    rfl

/-! ### `sample_queries` -/

theorem one_shiftLeft_toNat {d : ℕ} (hd : d < 64) : (1#64 <<< (d % 64)).toNat = 2 ^ d := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hd, BitVec.toNat_ofNat, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hd)

theorem log2StrictRust_one_shiftLeft {d : ℕ} (hd : d < 64) :
    log2StrictRust (1#64 <<< (d % 64)) = some d := by
  rw [log2StrictRust_eq, one_shiftLeft_toNat hd, log2Strict]
  have hp : 0 < 2 ^ d ∧ 2 ^ d &&& (2 ^ d - 1) = 0 := by
    refine ⟨Nat.two_pow_pos d, ?_⟩
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  rw [ite_eq_left hp, bitLength, ite_eq_right (Nat.two_pow_pos d).ne', Nat.log2_two_pow]
  rfl

theorem shiftRight_mod_high (Y C s d : ℕ) (h : s + d ≤ 128) :
    ((Y + 2 ^ 128 * C) >>> s) % 2 ^ d = (Y >>> s) % 2 ^ d := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h1 : 2 ^ 128 * C = 2 ^ s * (2 ^ d * (2 ^ (128 - s - d) * C)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.add_mul_mod_self_left]

theorem queryWindow_toNat (e : E) {d c : ℕ} (hd : d < 64) (hc : c * d < 192) :
    (queryWindow [(e.limb 0).toBitVec, (e.limb 1).toBitVec, (e.limb 2).toBitVec, 0#64]
      (1#64 <<< (d % 64)) d c).toNat = (eToNat e >>> (c * d)) % 2 ^ d := by
  set a0 := (e.limb 0).toBitVec
  set a1 := (e.limb 1).toBitVec
  set a2 := (e.limb 2).toBitVec
  have he : eToNat e = a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat := rfl
  have h0 := a0.isLt
  have h1 := a1.isLt
  have h2 := a2.isLt
  have hpow : 2 ^ d ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hd.le
  have hmask : ((1#64 <<< (d % 64)) - 1).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_sub, one_shiftLeft_toNat hd, show (1 : BitVec 64).toNat = 1 from rfl]
    have := Nat.two_pow_pos d
    have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    rw [h64] at hpow ⊢
    omega
  have hX : ∀ A B : BitVec 64, (A.setWidth 128 ||| B.setWidth 128 <<< 64).toNat =
      A.toNat + 2 ^ 64 * B.toNat := by
    intro A B
    have hA := A.isLt
    have hB := B.isLt
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : A.toNat < 2 ^ 128),
      Nat.mod_eq_of_lt (by omega : B.toNat < 2 ^ 128), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : B.toNat * 2 ^ 64 < 2 ^ 128), Nat.lor_comm, mul_comm,
      ← Nat.two_pow_add_eq_or_of_lt hA, add_comm]
  have hwin : ∀ (A B : BitVec 64) (s : ℕ),
      (((A.setWidth 128 ||| B.setWidth 128 <<< 64) >>> s).setWidth 64
        &&& ((1#64 <<< (d % 64)) - 1)).toNat = ((A.toNat + 2 ^ 64 * B.toNat) >>> s) % 2 ^ d := by
    intro A B s
    rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, hX, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hd.le)]
  simp only [queryWindow]
  rw [hwin]
  have hcd := (Nat.div_add_mod (c * d) 64).symm
  have hs : c * d % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hl : c * d / 64 = 0 ∨ c * d / 64 = 1 ∨ c * d / 64 = 2 := by omega
  conv_rhs => rw [hcd]
  generalize c * d / 64 = l at hl ⊢
  generalize c * d % 64 = s at hs ⊢
  rw [Nat.shiftRight_add]
  have hsd : s + d ≤ 128 := by omega
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have h128 : (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  rcases hl with rfl | rfl | rfl
  · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.shiftRight_zero]
    rw [he, shiftRight_mod_high _ _ _ _ hsd]
  · simp only [List.getD_cons_zero, List.getD_cons_succ]
    have : eToNat e >>> (64 * 1) = a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 128 * 0 := by
      rw [Nat.shiftRight_eq_div_pow, he]
      rw [h64, h128] at *
      omega
    rw [this, shiftRight_mod_high _ _ _ _ hsd]
  · simp only [List.getD_cons_zero, List.getD_cons_succ]
    have : eToNat e >>> (64 * 2) = a2.toNat + 2 ^ 64 * (0#64).toNat + 2 ^ 128 * 0 := by
      rw [Nat.shiftRight_eq_div_pow, he]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      rw [h64, h128] at *
      omega
    rw [this, shiftRight_mod_high _ _ _ _ hsd]

theorem sampleQueriesLoop_sim (d count : ℕ) (hd0 : 0 < d) (hd : d < 64) :
    ∀ (fuel : ℕ) (result : List (BitVec 64)) (remaining : ℕ), result.length ≤ count →
      remaining = count - result.length →
      SimR (sampleQueriesLoop (1#64 <<< (d % 64)) d count fuel result)
        (sampleQueriesAux d fuel remaining)
        (fun a b ↦ a.map BitVec.toNat = result.map BitVec.toNat ++ b)
  | 0, result, _, _, _ => SimR.pure (by simp)
  | fuel + 1, result, remaining, hr, hrem => by
    subst hrem
    rw [sampleQueriesLoop, sampleQueriesAux]
    by_cases h : result.length < count
    · have hne : ¬ (count - result.length = 0) := by omega
      simp only [h, hne, ↓reduceIte]
      refine SimR.bind (SimR.of_sim Sim.sample) ?_
      rintro x _ rfl
      have hn : min (192 / d) (count - result.length) ≤ count - result.length := min_le_right _ _
      refine SimR.map_right (sampleQueriesLoop_sim d count hd0 hd fuel _ _ ?_ ?_) ?_
      · simp only [List.length_append, List.length_map, List.length_range]
        omega
      · simp only [List.length_append, List.length_map, List.length_range]
        omega
      intro a b hab
      refine SimR.pure ?_
      rw [hab]
      simp only [List.map_append, List.map_map, List.append_assoc]
      congr 1
      congr 1
      apply List.map_congr_left
      intro c hc
      rw [List.mem_range] at hc
      have hc' : c * d < 192 := by
        have : c + 1 ≤ 192 / d := by omega
        have := (Nat.le_div_iff_mul_le hd0).mp this
        rw [Nat.add_mul, one_mul] at this
        omega
      exact queryWindow_toNat x hd hc'
    · have he : count - result.length = 0 := by omega
      simp only [h, he, ↓reduceIte]
      exact SimR.pure (by simp)

/-- **`sample_queries` at a block of `2^depth` positions is `sampleQueries`.** -/
theorem sampleQueriesRust_sim {d : ℕ} (count : ℕ) (hd0 : 0 < d) (hd : d < 64) :
    SimR (sampleQueriesRust (1#64 <<< (d % 64)) count) (sampleQueries d count)
      (fun a b ↦ b = a.map BitVec.toNat) := by
  rw [sampleQueriesRust]
  refine SimR.ofOption_bind ?_
  intro d' hd'
  rw [log2StrictRust_one_shiftLeft hd, Option.some.injEq] at hd'
  subst hd'
  have := sampleQueriesLoop_sim d count hd0 hd count [] count (Nat.zero_le _) rfl
  exact SimR.mono this (fun a b hab ↦ by simpa using hab.symm)

/-! ### `induced_weight` -/

theorem ofK_add_w (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul_w (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem ofK_one_w : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem ofK_zero_w : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem foldl_rel {α β γ : Type} {f : α → γ → α} {g : β → γ → β} (R : α → β → Prop)
    (h : ∀ a b c, R a b → R (f a c) (g b c)) :
    ∀ (l : List γ) (a : α) (b : β), R a b → R (l.foldl f a) (l.foldl g b)
  | [], _, _, hab => hab
  | c :: l, a, b, hab => foldl_rel R h l _ _ (h a b c hab)

theorem subspaceRootsLoop_spec : ∀ (n : ℕ) (roots layer : List K) (out : List K × List K),
    subspaceRootsLoop n (roots, layer) = some out →
      out.1.map ofK = roots.map ofK ++
        subspaceRootsAux n (ofK (roots.getLastD 0)) (layer.map ofK)
  | 0, roots, layer, out, h => by
    simp only [subspaceRootsLoop, Option.some.injEq] at h
    subst h
    simp [subspaceRootsAux]
  | n + 1, roots, layer, out, h => by
    have hmap : (layer.map ofK).map (fun value ↦ value ^ 2 + ofK (roots.getLastD 0) * value) =
        (layer.map fun value ↦ value * value + roots.getLastD 0 * value).map ofK := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      simp only [Function.comp, ofK_add_w, ofK_mul_w, sq]
    rw [subspaceRootsAux, hmap]
    simp only [subspaceRootsLoop, subspaceRootsStep] at h
    revert h
    generalize layer.map (fun value ↦ value * value + roots.getLastD 0 * value) = l
    intro h
    cases l with
    | nil => cases h
    | cons first rest =>
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      rw [List.map_cons, subspaceRootsLoop_spec n _ _ out h]
      simp

theorem shiftLeft_succ_eq {i : ℕ} (hi : i + 1 < 64) :
    BF64.ofBitVec (1#64 <<< ((1 + i) % 64)) = K.ofBits (2 ^ (i + 1)) := by
  rw [K.ofBits]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [one_shiftLeft_toNat (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi), add_comm]

theorem subspaceRootsRust_spec {n : ℕ} (hn : n < 64) {rs : List K}
    (h : subspaceRootsRust n = some rs) : rs.map ofK = subspaceRoots n := by
  rw [subspaceRootsRust, Option.map_eq_some_iff] at h
  obtain ⟨out, hout, rfl⟩ := h
  rw [subspaceRootsLoop_spec n _ _ out hout, subspaceRoots]
  have hlayer : ((List.range' 1 n).map fun i ↦ BF64.ofBitVec (1#64 <<< (i % 64))).map ofK =
      (List.range n).map fun i ↦ eOfNat (2 ^ (i + 1)) := by
    rw [List.range'_eq_map_range, List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, eOfNat]
    rw [shiftLeft_succ_eq (by omega)]
  rw [hlayer]
  simp

/-- **`induced_weight`, wherever it returns, is `inducedWeight`.** -/
theorem inducedWeightRust_rel {ml : ℕ} (hml : ml < 64) (qs : List (BitVec 64)) (qw : List E) :
    WeightRel (inducedWeightRust ml qs qw) (inducedWeight ml (qs.map BitVec.toNat) qw) := by
  intro x v hv
  simp only [inducedWeightRust] at hv
  split_ifs at hv with hx
  cases hr : subspaceRootsRust ml with
  | none => rw [hr] at hv; cases hv
  | some rs =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
    subst hv
    have hroots := subspaceRootsRust_spec hml hr
    rw [inducedWeight, ← hroots, List.zip_map_right, List.foldl_map]
    have hinv : (rs.map ofK).map (fun value ↦ if value = 0 then 0 else value⁻¹) =
        (rs.map (·⁻¹)).map ofK := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro a _
      simp only [Function.comp]
      split_ifs with h0
      · rw [ofK_inv, h0, inv_zero]
      · exact (ofK_inv a).symm
    rw [hinv]
    apply foldl_rel (fun a b ↦ a = b)
    · rintro total _ ⟨weight, query⟩ rfl
      simp only [Prod.map]
      congr 1
      have := foldl_rel (f := fun (acc : E × K) (p : E × ℕ) ↦
          (acc.1 * (1 + p.1 * ofK (1 + acc.2 * (rs.map (·⁻¹)).getD p.2 0)),
            acc.2 * acc.2 + rs.getD p.2 0 * acc.2))
        (g := fun (acc : E × E) (p : E × ℕ) ↦
          (acc.1 * (1 + p.1 * (1 + acc.2 * ((rs.map (·⁻¹)).map ofK).getD p.2 0)),
            acc.2 ^ 2 + (rs.map ofK).getD p.2 0 * acc.2))
        (fun a b ↦ b = (a.1, ofK a.2)) ?_ x.zipIdx (weight, BF64.ofBitVec query)
        (weight, eOfNat query.toNat) ?_
      · exact (congrArg Prod.fst this).symm
      · rintro ⟨a1, a2⟩ _ ⟨c, k⟩ rfl
        have h1 : ((rs.map (·⁻¹)).map ofK).getD k 0 = ofK ((rs.map (·⁻¹)).getD k 0) := by
          rw [← ofK_zero_w, List.getD_map]
        have h2 : (rs.map ofK).getD k 0 = ofK (rs.getD k 0) := by
          rw [← ofK_zero_w, List.getD_map]
        simp only [h1, h2, ofK_add_w, ofK_mul_w, ofK_one_w, sq]
      · simp only [eOfNat, K.ofBits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rfl

/-! ### Gluing, and the terminal weight -/

/-- A pending claim: the same intro message, of three coefficients, and related weights. -/
def PendingRel (p : List E × GluedWeightRust) (q : List E × (List E → E)) : Prop :=
  p.1 = q.1 ∧ p.1.length = 3 ∧ WeightRel p.2.evaluate q.2

theorem foldl_rel₂ {α β γ δ : Type} {f : α → γ → α} {g : β → δ → β} (R : α → β → Prop)
    (S : γ → δ → Prop) (h : ∀ a b c d, R a b → S c d → R (f a c) (g b d)) :
    ∀ {l : List γ} {l' : List δ}, List.Forall₂ S l l' → ∀ a b, R a b → R (l.foldl f a) (l'.foldl g b)
  | _, _, .nil, _, _, hab => hab
  | _, _, .cons hcd hl, a, b, hab => foldl_rel₂ R S h hl _ _ (h a b _ _ hab hcd)

theorem forall₂_append_single {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ R (l ++ [x]) (l' ++ [y])
  | _, _, .nil => .cons hxy .nil
  | _, _, .cons hab h => .cons hab (forall₂_append_single hxy h)

theorem zipAddScaled_eq (quad intro : List E) (scalar : E) (h : quad.length = intro.length) :
    zipAddScaled quad intro scalar = List.zipWith (fun q i ↦ q + scalar * i) quad intro := by
  rw [zipAddScaled, List.drop_eq_nil_of_le (by omega), List.append_nil,
    ← List.map_uncurry_zip_eq_zipWith]
  rfl

/-- The statement's step of `glue`. -/
def glueStep (lam : E) : WhirState × E → List E × (List E → E) → WhirState × E :=
  fun (acc : WhirState × E) (intro, weightAt) ↦
    let scalar := acc.2 * lam
    let state := acc.1
    ({ state with
        runningQuad := List.zipWith (fun q i ↦ q + scalar * i) state.runningQuad intro,
        glued := state.glued ++ [⟨scalar, state.folds.length, weightAt⟩] }, scalar)

theorem glue_eq (lam : E) (s : WhirState) (pending : List (List E × (List E → E))) :
    glue lam s pending = (pending.foldl (glueStep lam) (s, 1)).1 := rfl

theorem glue_rel (lam : E) {pr : List (List E × GluedWeightRust)}
    {ps : List (List E × (List E → E))} (hp : List.Forall₂ PendingRel pr ps) {sr : WhirLocals}
    {ss : WhirState} (h : LocalsRel sr ss) :
    LocalsRel (glueRust lam sr pr) (glue lam ss ps) ∧ (glueRust lam sr pr).folds = sr.folds := by
  have := foldl_rel₂ (f := glueStepRust lam) (g := glueStep lam)
    (fun (a : WhirLocals × E) (b : WhirState × E) ↦
      LocalsRel a.1 b.1 ∧ a.2 = b.2 ∧ a.1.folds = sr.folds) PendingRel ?_ hp (sr, 1) (ss, 1)
      ⟨h, rfl, rfl⟩
  · exact ⟨this.1, this.2.2⟩
  · unfold glueStepRust glueStep
    rintro ⟨⟨q, f, g⟩, sc⟩ ⟨⟨q', f', g'⟩, sc'⟩ ⟨i, w⟩ ⟨i', wf⟩ ⟨⟨hq, hf, hl, hg, hs⟩, hsc, hF⟩
      ⟨hi, hil, hw⟩
    dsimp only at hq hf hl hg hs hsc hF hi hil hw ⊢
    subst hq hf hsc hi
    refine ⟨⟨zipAddScaled_eq _ _ _ (by omega), rfl, ?_, ?_, ?_⟩, rfl, hF⟩
    · simp only [zipAddScaled, List.length_append, List.length_map, List.length_zip,
        List.length_drop]
      omega
    · exact forall₂_append_single ⟨rfl, rfl, hw⟩ hg
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hs c hc
      · rw [List.mem_singleton] at hc
        subst hc
        exact le_rfl

theorem terminalWeight_rel (basis : List E → Option E) (evaluateBasis : List E → E) (logN : ℕ)
    (hb : ∀ x v, x.length = logN → basis x = some v → v = evaluateBasis x) {sr : WhirLocals}
    {ss : WhirState} (h : LocalsRel sr ss) (tail : List E)
    (hlen : sr.folds.length + tail.length = logN) (laneFolds : ℕ) (w : E)
    (hw : terminalWeightRust basis laneFolds sr.glued (sr.folds ++ tail) = some w) :
    w = ss.glued.foldl (fun weight claim ↦
        weight + claim.scalar * claim.weightAt (ss.folds.drop claim.foldStart ++ tail))
      (evaluateBasis ((ss.folds ++ tail).drop laneFolds ++ (ss.folds ++ tail).take laneFolds)) := by
  obtain ⟨q, f, g⟩ := sr
  obtain ⟨q', f', g'⟩ := ss
  obtain ⟨-, hf, -, hg, hs⟩ := h
  dsimp only at hf hg hs hlen hw ⊢
  subst hf
  simp only [terminalWeightRust, sliceFrom, sliceTo] at hw
  split_ifs at hw with h1
  · simp only [Option.bind_eq_bind, Option.bind_some] at hw
    cases hbv : basis ((f ++ tail).drop laneFolds ++ (f ++ tail).take laneFolds) with
    | none => rw [hbv] at hw; cases hw
    | some w0 =>
      rw [hbv, Option.bind_some] at hw
      have hw0 := hb _ w0 (by simp only [List.length_append, List.length_drop,
        List.length_take] at h1 ⊢; omega) hbv
      rw [← hw0]
      clear hw0 hbv
      revert hw
      generalize w0 = acc
      induction hg generalizing acc with
      | nil => intro hw; exact (Option.some.inj hw).symm
      | @cons c c' gs gs' hcc hgs ih =>
        intro hw
        rw [List.foldlM_cons] at hw
        have hfs : c.foldStart ≤ (f ++ tail).length := by
          have := hs c (List.mem_cons_self ..)
          simp only [List.length_append]
          omega
        simp only [hfs, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hw
        cases hv : c.weight.evaluate ((f ++ tail).drop c.foldStart) with
        | none => rw [hv] at hw; cases hw
        | some v =>
          simp only [hv, Option.bind_some] at hw
          obtain ⟨hsc, hfs', hwr⟩ := hcc
          have hd : (f ++ tail).drop c.foldStart = f.drop c.foldStart ++ tail :=
            List.drop_append_of_le_length (hs c (List.mem_cons_self ..))
          rw [hd] at hv
          have hv' := hwr _ v hv
          rw [List.foldl_cons, ← hsc, ← hfs', ← hv']
          exact ih (fun c hc ↦ hs c (List.mem_cons_of_mem _ hc)) _ hw
  · simp only [Option.bind_eq_bind, Option.bind_none] at hw
    cases hw

/-! ### The level loop -/

theorem SimR.merkleLeaves (i : ℕ) (qs : List (BitVec 64)) (w : ℕ) :
    SimR (TM.merkleLeaves i qs w) (VerifierProgram.queryOpenings i (qs.map BitVec.toNat))
      (fun a b ↦ a = b ∧ ∀ row ∈ a, row.length = w) := by
  show SimR _ (VerifierProgram.queryOpenings i _ >>= fun rows ↦ VerifierProgram.ret rows) _
  refine SimR.bind (SimR.of_sim (Sim.merkle _ _)) ?_
  rintro rows _ rfl
  exact SimR.require_left fun hc ↦ SimR.pure ⟨rfl, hc⟩

theorem SimR.of_simUnit {α : Type} {m : TM α} {P : VerifierProgram Unit} (h : SimUnit m P) :
    SimR m P (fun _ _ ↦ True) := h

theorem multilinearEvalRust_rel {mle point : List E} {v : E}
    (h : multilinearEvalRust mle point = some v) : v = multilinearEval mle point := by
  by_cases hc : point.length < 64 ∧ mle.length = 2 ^ point.length
  · rw [multilinearEvalRust_eq mle point hc] at h
    exact (Option.some.inj h).symm
  · rw [multilinearEvalRust, ite_eq_right hc] at h
    cases h

theorem ood_rel (point : List E) :
    WeightRel (GluedWeightRust.ood point).evaluate (fun x ↦ eqEval point x) := by
  intro x v hv
  simp only [GluedWeightRust.evaluate, Option.some.injEq] at hv
  rw [← hv, eqEvalRust_eq]

theorem queries_rel {ml : ℕ} (hml : ml < 64) (qs : List (BitVec 64)) (qw : List E) :
    WeightRel (GluedWeightRust.queries ml qs qw).evaluate
      (fun x ↦ inducedWeight ml (qs.map BitVec.toNat) qw x) :=
  inducedWeightRust_rel hml qs qw

theorem getElem?_of_drop {α : Type} {l : List α} {i : ℕ} {a : α} {rest : List α}
    (h : l.drop i = a :: rest) : l[i]? = some a := by
  rw [← List.head?_drop, h]
  rfl

theorem length_of_drop {α : Type} {l : List α} {i : ℕ} {a : α} {rest : List α}
    (h : l.drop i = a :: rest) : l.length = i + rest.length + 1 := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_cons] at this
  have hlt : i < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  omega

theorem whirLevelsRust_sim (logN : ℕ) (ls : List Whir.Level) (basis : List E → Option E)
    (evaluateBasis : List E → E)
    (hb : ∀ x v, x.length = logN → basis x = some v → v = evaluateBasis x)
    (hN : logN ≤ 28) (hrate : ∀ l ∈ ls, l.logInvRate ≤ 20)
    (hhead : ls.head?.map (·.fold) = some initialFoldingFactor) :
    ∀ (rest : List Whir.Level) (index : ℕ) (sr : WhirLocals) (ss : WhirState),
      ls.drop index = rest → LocalsRel sr ss →
      (rest.map (·.fold)).sum + sr.folds.length + 2 ≤ logN →
      SimR (whirLevelsRust logN (configOfLadder ls) basis index
          (rest.map fun l ↦ (l.fold, l.logInvRate)) sr)
        (whirLevels logN initialFoldingFactor evaluateBasis index rest ss) (fun _ _ ↦ True)
  | [], index, sr, ss, _, _, _ => by
    rw [List.map_nil, whirLevelsRust]
    exact SimR.fail_left
  | l :: rest, index, sr, ss, hdrop, h, hsum => by
    have hl : l ∈ ls := List.mem_of_mem_drop (hdrop ▸ List.mem_cons_self ..)
    have hrl := hrate l hl
    have hlen := length_of_drop hdrop
    have hq : (configOfLadder ls).queries[index]? = some l.queries := by
      simp only [configOfLadder, List.getElem?_map, getElem?_of_drop hdrop, Option.map_some]
    have hf0 : (configOfLadder ls).folds[0]? = some initialFoldingFactor := by
      cases ls with
      | nil => cases hhead
      | cons a as => simpa [configOfLadder] using hhead
    have hflen : (configOfLadder ls).folds.length = ls.length := by
      simp [configOfLadder]
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    rw [whirLevelsRust, whirLevels]
    refine SimR.bind (foldLoop_sim l.fold sr ss [] h) ?_
    rintro ⟨sr1, lf⟩ ⟨ss1, lf'⟩ ⟨h1, rfl, hlen1⟩
    have hfolds1 : sr1.folds = ss1.folds := h1.2.1
    dsimp only
    rw [hfolds1]
    have hml : logN - ss1.folds.length + ss1.folds.length = logN := by
      rw [← hfolds1, hlen1]; omega
    have hml2 : 2 ≤ logN - ss1.folds.length := by rw [← hfolds1, hlen1]; omega
    have hml64 : logN - ss1.folds.length < 64 := by omega
    generalize hm : logN - ss1.folds.length = ml at hml hml2 hml64
    cases rest with
    | nil =>
      have hfin : index = (configOfLadder ls).folds.length - 1 := by
        rw [hflen]; simp only [List.length_nil] at hlen; omega
      simp only [eq_true hfin, ↓reduceIte, Nat.mod_eq_of_lt hml64]
      refine SimR.bind (SimR.of_sim (Sim.nextScalars _)) ?_
      rintro residual _ rfl
      refine SimR.bind (r := fun a b ↦ a.1 = b.1 ∧ List.Forall₂ PendingRel a.2 b.2)
        (SimR.pure ⟨rfl, .nil⟩) ?_
      rintro ⟨res, pend⟩ ⟨res', pend'⟩ ⟨hres, hpend⟩
      dsimp only at hres hpend ⊢
      subst hres
      refine SimR.bind (SimR.of_sim (Sim.grind _)) ?_
      rintro _ _ rfl
      refine SimR.ofOption_bind ?_
      intro count hcount
      rw [hq, Option.some.injEq] at hcount
      subst hcount
      refine SimR.bind (sampleQueriesRust_sim (d := ml + l.logInvRate) l.queries (by omega)
        (by omega)) ?_
      rintro qs _ rfl
      refine SimR.bind (SimR.of_sim Sim.sample) ?_
      rintro lam _ rfl
      refine SimR.bind (SimR.merkleLeaves _ _ _) ?_
      rintro words _ ⟨rfl, hwords⟩
      rw [enforced_eq index words lf _ ?_, List.length_map]
      swap
      · intro h0 row hrow
        rw [hwords row hrow, ite_eq_right h0]
        omega
      refine SimR.bind (SimR.sumcheckRoundPoly3 _) ?_
      rintro intro _ ⟨rfl, hintro⟩
      have hpend2 := forall₂_append_single (R := PendingRel)
        (⟨rfl, hintro, queries_rel hml64 qs (powers lam qs.length)⟩ :
          PendingRel (intro, GluedWeightRust.queries ml qs (powers lam qs.length))
            (intro, fun x ↦ inducedWeight ml (qs.map BitVec.toNat) (powers lam qs.length) x)) hpend
      obtain ⟨hg, hgf⟩ := glue_rel lam hpend2 h1
      generalize glueRust lam sr1 _ = s2 at hg hgf ⊢
      generalize glue lam ss1 _ = ss2 at hg ⊢
      rw [hg.1]
      refine SimR.bind (tailLoop_sim ml ml 0 _ [] 0 (by omega) (by omega)) ?_
      rintro ⟨_, tf, rt⟩ ⟨tf', tgt⟩ ⟨htf, hrt, htl⟩
      dsimp only at htf hrt htl ⊢
      rw [List.nil_append] at htf
      subst htf hrt
      refine SimR.ofOption_bind ?_
      intro lfd hlfd
      rw [hf0, Option.some.injEq] at hlfd
      subst hlfd
      refine SimR.ofOption_bind ?_
      intro w hw
      refine SimR.ofOption_bind ?_
      intro m hm
      refine SimR.require_iff ?_
      have hlenT : s2.folds.length + tf.length = logN := by
        rw [hgf, hfolds1, htl]; omega
      rw [terminalWeight_rel basis evaluateBasis logN hb hg tf hlenT _ w hw,
        multilinearEvalRust_rel hm]
    | cons next rest =>
      have hnfin : ¬ index = (configOfLadder ls).folds.length - 1 := by
        rw [hflen]; simp only [List.length_cons] at hlen; omega
      simp only [eq_false hnfin, ↓reduceIte, List.map_cons, levelShape]
      refine SimR.bind (SimR.of_simUnit (SimUnit.commit _ _)) ?_
      rintro _ ⟨⟩ _
      refine SimR.bind (SimR.of_sim (Sim.samples _)) ?_
      rintro p _ rfl
      refine SimR.bind (SimR.of_sim Sim.nextScalar) ?_
      rintro ov _ rfl
      refine SimR.bind (SimR.sumcheckRoundPoly3 _) ?_
      rintro intro0 _ ⟨rfl, hi0⟩
      refine SimR.bind (r := fun a b ↦ a.1 = b.1 ∧ List.Forall₂ PendingRel a.2 b.2)
        (SimR.pure ⟨rfl, .cons ⟨rfl, hi0, ood_rel _⟩ .nil⟩) ?_
      rintro ⟨res, pend⟩ ⟨res', pend'⟩ ⟨hres, hpend⟩
      dsimp only at hres hpend ⊢
      subst hres
      refine SimR.bind (SimR.of_sim (Sim.grind _)) ?_
      rintro _ _ rfl
      refine SimR.ofOption_bind ?_
      intro count hcount
      rw [hq, Option.some.injEq] at hcount
      subst hcount
      refine SimR.bind (sampleQueriesRust_sim (d := ml + l.logInvRate) l.queries (by omega)
        (by omega)) ?_
      rintro qs _ rfl
      refine SimR.bind (SimR.of_sim Sim.sample) ?_
      rintro lam _ rfl
      refine SimR.bind (SimR.merkleLeaves _ _ _) ?_
      rintro words _ ⟨rfl, hwords⟩
      rw [enforced_eq index words lf _ ?_, List.length_map]
      swap
      · intro h0 row hrow
        rw [hwords row hrow, ite_eq_right h0]
        omega
      refine SimR.bind (SimR.sumcheckRoundPoly3 _) ?_
      rintro intro _ ⟨rfl, hintro⟩
      have hpend2 := forall₂_append_single (R := PendingRel)
        (⟨rfl, hintro, queries_rel hml64 qs (powers lam qs.length)⟩ :
          PendingRel (intro, GluedWeightRust.queries ml qs (powers lam qs.length))
            (intro, fun x ↦ inducedWeight ml (qs.map BitVec.toNat) (powers lam qs.length) x)) hpend
      obtain ⟨hg, hgf⟩ := glue_rel lam hpend2 h1
      have hdrop' : ls.drop (index + 1) = next :: rest := by
        have := congrArg List.tail hdrop
        rwa [List.tail_drop] at this
      refine whirLevelsRust_sim logN ls basis evaluateBasis hb hN hrate hhead (next :: rest)
        (index + 1) _ _ hdrop' hg ?_
      rw [hgf, hlen1]
      simp only [List.map_cons, List.sum_cons] at hsum ⊢
      omega

theorem zip_map_pair (ls : List Whir.Level) :
    (ls.map (·.fold)).zip (ls.map (·.logInvRate)) = ls.map fun l ↦ (l.fold, l.logInvRate) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [List.map_cons, List.map_cons, List.zip_cons_cons, ih, List.map_cons]

/-- **`verify_whir` runs `verifyWhir`**, for a basis that, wherever it returns at a point of the
stack's size, returns the statement's. -/
theorem verifyWhirRust_sim (logN logInvRate : ℕ) (target : E) (basis : List E → Option E)
    (evaluateBasis : List E → E)
    (hb : ∀ x v, x.length = logN → basis x = some v → v = evaluateBasis x) :
    Sim (verifyWhirRust logN logInvRate target basis)
      (verifyWhir logN logInvRate target evaluateBasis) := by
  apply Sim.of_simR
  rw [verifyWhirRust, verifyWhir, deriveConfigRust_eq]
  cases hl : Whir.ladder logN logInvRate with
  | none => exact SimR.ofOption_bind fun a ha ↦ by cases ha
  | some ls =>
    obtain ⟨hN, hhead, hsum, hrate⟩ := ladder_facts hl
    rw [Option.map_some, TM.ofOption]
    simp only [LeanVM.Protocol.Verifier.liftOption]
    refine SimR.bind (r := fun a b ↦ a = configOfLadder b ∧ b = ls) (SimR.pure ⟨rfl, rfl⟩) ?_
    rintro _ b ⟨rfl, hbl⟩
    subst b
    refine SimR.bind (SimR.sumcheckRoundPoly3 target) ?_
    rintro quad _ ⟨rfl, hq3⟩
    rw [hhead, Option.getD_some]
    have := whirLevelsRust_sim logN ls basis evaluateBasis hb hN hrate hhead ls 0 ⟨quad, [], []⟩
      ⟨quad, [], []⟩ rfl ⟨rfl, rfl, hq3, .nil, fun c hc ↦ by cases hc⟩ (by simpa using hsum)
    simp only [configOfLadder] at this ⊢
    rw [zip_map_pair]
    exact this

/-! ## `verify_stacked_opening` (`lib.rs:119-205`) -/

/-- `StackWeight`. -/
inductive StackWeightRust where
  | eq (point : List E)
  | ring (weight : RingWeightRust)
  | placedRing (placement : PlacementRust) (weight : RingWeightRust)

/-- `StackWeight::evaluate`: `Placement::eq_above` and the slice `&x[..placement.variables]`
panic when the placement has more variables than the point. -/
def StackWeightRust.evaluate : StackWeightRust → List E → Option E
  | .eq point, x => some (eqEvalRust point x)
  | .ring weight, x => weight.evaluate x
  | .placedRing placement weight, x =>
    if placement.variableCount ≤ x.length then
      (weight.evaluate (x.take placement.variableCount)).map (placement.eqAbove x * ·)
    else none

/-- `StackClaim`. -/
structure StackClaimRust where
  weight : StackWeightRust
  value : E

/-- `StackBasis::evaluate`: every claim's weight at the point, then `dot(scales, weights)`. -/
def stackBasisEvaluate (claims : List StackClaimRust) (scales point : List E) : Option E := do
  let weights ← claims.mapM fun claim ↦ claim.weight.evaluate point
  pure (dotRust scales weights)

/-- `verify_stacked_opening`, the stack's root being commitment `0`. -/
def verifyStackedOpeningRust (stackLog logInvRate : ℕ) (claims : List StackClaimRust) :
    TM Unit := do
  let values := claims.map (·.value)
  let scales := powers (← TM.sample) claims.length
  let target := dotRust scales values
  verifyWhirRust stackLog logInvRate target (stackBasisEvaluate claims scales)

/-- A Rust stack claim stands for a statement's: the same value, and a weight that, wherever it
returns at a point of the stack's size, returns the statement's. -/
def StackClaimRel (stackLog : ℕ) (c : StackClaimRust) (c' : StackClaim) : Prop :=
  c.value = c'.2 ∧ ∀ x v, x.length = stackLog → c.weight.evaluate x = some v → v = c'.1 x

theorem stackClaimRel_eq (stackLog : ℕ) (point : List E) (value : E) :
    StackClaimRel stackLog ⟨.eq point, value⟩ (fun x ↦ eqEval point x, value) := by
  refine ⟨rfl, fun x v _ hv ↦ ?_⟩
  simp only [StackWeightRust.evaluate, Option.some.injEq] at hv
  rw [← hv, eqEvalRust_eq]

theorem stackClaimRel_ring (stackLog : ℕ) (weight : RingWeightRust) (f : List E → E) (value : E)
    (h : WeightRel weight.evaluate f) :
    StackClaimRel stackLog ⟨.ring weight, value⟩ (f, value) :=
  ⟨rfl, fun x v _ hv ↦ h x v hv⟩

theorem stackClaimRel_placedRing {stackLog : ℕ} (hs : stackLog ≤ 64) (placement : PlacementRust)
    (weight : RingWeightRust) (f : List E → E) (value : E) (h : WeightRel weight.evaluate f) :
    StackClaimRel stackLog ⟨.placedRing placement weight, value⟩
      (fun x ↦ placement.toSpec.eqAbove x * f (x.take placement.toSpec.variableCount), value) := by
  refine ⟨rfl, fun x v hx hv ↦ ?_⟩
  simp only [StackWeightRust.evaluate] at hv
  split_ifs at hv
  cases hw : weight.evaluate (x.take placement.variableCount) with
  | none => rw [hw] at hv; cases hv
  | some w =>
    rw [hw, Option.map_some, Option.some.injEq] at hv
    rw [← hv, PlacementRust.eqAbove_eq _ _ (by omega), h _ w hw]
    rfl

/-- The ring-switching claim of `walk` (`lib.rs:305-311`), its placement the layout's
`q_keccak` one. -/
theorem stackClaimRel_ringSwitchClaim {stackLog : ℕ} (hs : stackLog ≤ 64) (layout : Layout)
    (placement : PlacementRust) (hp : placement.toSpec = layout.placement qkeccak)
    (weight : RingWeightRust) (f : List E → E) (value : E) (h : WeightRel weight.evaluate f) :
    StackClaimRel stackLog ⟨.placedRing placement weight, value⟩
      (ringSwitchClaim layout value f) := by
  have := stackClaimRel_placedRing hs placement weight f value h
  rw [hp] at this
  exact this

theorem map_value_of_forall₂ {stackLog : ℕ} : ∀ {claims : List StackClaimRust}
    {claims' : List StackClaim}, List.Forall₂ (StackClaimRel stackLog) claims claims' →
      claims.map (·.value) = claims'.map (·.2)
  | _, _, .nil => rfl
  | _, _, .cons hc h => by rw [List.map_cons, List.map_cons, hc.1, map_value_of_forall₂ h]

theorem mapM_weights_of_forall₂ {stackLog : ℕ} (x : List E) (hx : x.length = stackLog) :
    ∀ {claims : List StackClaimRust} {claims' : List StackClaim},
      List.Forall₂ (StackClaimRel stackLog) claims claims' → ∀ ws,
      claims.mapM (fun claim ↦ claim.weight.evaluate x) = some ws →
      ws = claims'.map fun c ↦ c.1 x
  | _, _, .nil, ws, hws => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hws
    rw [← hws]
    rfl
  | c :: cs, c' :: cs', .cons hc h, ws, hws => by
    rw [List.mapM_cons] at hws
    cases hv : c.weight.evaluate x with
    | none => simp [hv] at hws
    | some v =>
      cases hvs : cs.mapM (fun claim ↦ claim.weight.evaluate x) with
      | none => simp [hv, hvs] at hws
      | some vs =>
        simp only [hv, hvs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hws
        rw [← hws, List.map_cons, hc.2 x v hx hv, mapM_weights_of_forall₂ x hx h vs hvs]

/-- **`verify_stacked_opening` runs `verifyStackedOpening`** on the statement's claims the
Rust's stand for. -/
theorem verifyStackedOpeningRust_sim (stackLog logInvRate : ℕ) (claims : List StackClaimRust)
    (claims' : List StackClaim) (h : List.Forall₂ (StackClaimRel stackLog) claims claims') :
    Sim (verifyStackedOpeningRust stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims') := by
  rw [verifyStackedOpeningRust, verifyStackedOpening]
  refine Sim.bind Sim.sample fun lam ↦ ?_
  dsimp only
  rw [h.length_eq, dotRust_eq, map_value_of_forall₂ h]
  refine verifyWhirRust_sim _ _ _ _ _ fun x v hx hv ↦ ?_
  simp only [stackBasisEvaluate] at hv
  cases hws : claims.mapM (fun claim ↦ claim.weight.evaluate x) with
  | none => rw [hws] at hv; cases hv
  | some ws =>
    rw [hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hv
    rw [← hv, dotRust_eq, mapM_weights_of_forall₂ x hx h ws hws]

/-! The axioms: Lean's three. -/

/-- info: 'Rv64Verifier.Model.Pcs.deriveConfigRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms deriveConfigRust_eq

/-- info: 'Rv64Verifier.Model.Pcs.whirQueriesRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whirQueriesRust_eq

/-- info: 'Rv64Verifier.Model.Pcs.whirQueriesTable_eq' does not depend on any axioms -/
#guard_msgs in #print axioms whirQueriesTable_eq

/-- info: 'Rv64Verifier.Model.Pcs.ringWeightRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ringWeightRust_eq

/-- info: 'Rv64Verifier.Model.Pcs.ringSwitchRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ringSwitchRust_sim

/-- info: 'Rv64Verifier.Model.Pcs.sampleQueriesRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sampleQueriesRust_sim

/-- info: 'Rv64Verifier.Model.Pcs.inducedWeightRust_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inducedWeightRust_rel

/-- info: 'Rv64Verifier.Model.Pcs.whirLevelsRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whirLevelsRust_sim

/-- info: 'Rv64Verifier.Model.Pcs.verifyWhirRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifyWhirRust_sim

/-- info: 'Rv64Verifier.Model.Pcs.verifyStackedOpeningRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifyStackedOpeningRust_sim

/-- info: 'Rv64Verifier.Model.Pcs.stackClaimRel_ringSwitchClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackClaimRel_ringSwitchClaim

end Rv64Verifier.Model.Pcs
