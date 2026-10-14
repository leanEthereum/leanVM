import Whir.OperationalRefinement
import Whir.SamplingProbability
import Whir.AdditiveColumn
import Whir.CausalGame

namespace Whir.CommitmentAmbiguity
open Concrete Protocol
private theorem except_pure {S : Type} (s : S) :
    (pure s : Except String S) = .ok s := rfl

private theorem except_bind_ok {S T : Type} (s : S) (f : S → Except String T) :
    (Except.ok s >>= f) = f s := rfl


/-- Changing an oracle does not affect any sumcheck fold, including malformed
messages. The oracle is consulted only by authentication. -/
theorem folds_change_oracle (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : CheckedState) (root : Oracle) :
    runSteps (foldStep block cs p) count start {s with oracle := root} =
      {runSteps (foldStep block cs p) count start s with oracle := root} := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [runSteps, foldStep]
    exact ih (start+1) (foldStep block cs p start s)

private theorem checked_congr {S : Type} (f g : Nat → S → Except String S)
    (count start : Nat) (s : S)
    (same : ∀ j, start ≤ j → j < start+count → ∀ t, f j t = g j t) :
    runChecked f count start s = runChecked g count start s := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [runChecked, same start (by omega) (by omega)]
    congr 1
    funext t
    exact ih (start+1) t (by intro j lo hi u; exact same j (by omega) (by omega) u)

/-- Exact authentication result, not just acceptance, depends only on queried
rows. This includes duplicate queries and error-short-circuit behavior. -/
theorem authentication_local (left right : Oracle) (qs : Array Nat) (p : LevelProof)
    (same : ∀ j, j < qs.size → left[qs[j]!]! = right[qs[j]!]!) :
    runChecked (authenticateRow left qs p) qs.size 0 () =
      runChecked (authenticateRow right qs p) qs.size 0 () := by
  apply checked_congr
  intro j _ hi u
  simp only [authenticateRow, same j (by omega)]

/-- After the first query authentication, the verifier discards the initial
oracle. Later OOD values bind later commitments, not unqueried initial rows. -/
theorem level_local (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s : CheckedState) (root : Oracle) (qs : Array Nat)
    (sampled : deriveQueries
      ((foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
        ch.levels[i]! proof.levels[i]! s).n + c.rates[i]!)
      c.queries[i]! ch.levels[i]!.querySqueezes = some qs)
    (same : ∀ j, j < qs.size → s.oracle[qs[j]!]! = root[qs[j]!]!) :
    verifyLevel c ch proof i s = verifyLevel c ch proof i {s with oracle := root} := by
  have folded : foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
      ch.levels[i]! proof.levels[i]! {s with oracle := root} =
      {foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
        ch.levels[i]! proof.levels[i]! s with oracle := root} :=
    folds_change_oracle _ _ _ _ _ _ _
  have auth := authentication_local s.oracle root qs proof.levels[i]! same
  unfold verifyLevel
  dsimp only
  simp only [folded, sampled, Option.elim_some]
  have ho : (foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
      ch.levels[i]! proof.levels[i]! s).oracle = s.oracle := by
    apply OperationalRefinement.runSteps_invariant
      (foldStep _ _ _) (fun _ t => t.oracle = s.oracle) _ _ s rfl
    intro j t _ _ ht
    exact ht
  simp only [ho, except_pure, except_bind_ok, auth]

/-- Full untrusted-verifier locality, with exactly its original rejection/error
result. No honesty assumption is imposed on the supplied opening. -/
theorem verify_local (c : Config) (ch : Challenges) (lanes : Nat)
    (left right : Oracle) (weight : Array E) (target : E) (proof : Opening)
    (nonempty : 0 < c.folds.size)
    (leftShape : oracleValid left (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (rightShape : oracleValid right (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (qs : Array Nat)
    (sampled : deriveQueries
      ((foldBlock (2^(c.logN-c.folds[0]!)) ch.levels[0]! proof.levels[0]!
        ⟨c.logN, ⟨weight,target,proof.initial⟩,left⟩).n + c.rates[0]!)
      c.queries[0]! ch.levels[0]!.querySqueezes = some qs)
    (same : ∀ j, j < qs.size → left[qs[j]!]! = right[qs[j]!]!) :
    verify c ch lanes left weight target proof = verify c ch lanes right weight target proof := by
  have first := level_local c ch proof 0
    ⟨c.logN, ⟨weight,target,proof.initial⟩,left⟩ right qs (by simpa using sampled) same
  obtain ⟨count, hc⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nonempty)
  simp only [verify, initializeVerifier, leftShape, rightShape, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · simp only [replayLevels, hc, runChecked, except_pure, except_bind_ok]
      rw [first]

/-- A spliced immutable commitment may support separate sessions using different
honest continuations. This theorem states the exact verifier mechanism; it does
not mistake a commitment-time list for one binding witness. -/
theorem splice_accepts (c : Config) (ch : Challenges) (lanes : Nat)
    (honest mixed : Oracle) (weight : Array E) (target : E) (proof : Opening)
    (nonempty : 0 < c.folds.size)
    (honestShape : oracleValid honest (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (mixedShape : oracleValid mixed (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (qs : Array Nat)
    (sampled : deriveQueries
      ((foldBlock (2^(c.logN-c.folds[0]!)) ch.levels[0]! proof.levels[0]!
        ⟨c.logN, ⟨weight,target,proof.initial⟩,honest⟩).n + c.rates[0]!)
      c.queries[0]! ch.levels[0]!.querySqueezes = some qs)
    (same : ∀ j, j < qs.size → honest[qs[j]!]! = mixed[qs[j]!]!)
    (accepted : verify c ch lanes honest weight target proof = .ok ()) :
    verify c ch lanes mixed weight target proof = .ok () := by
  rw [← verify_local c ch lanes honest mixed weight target proof nonempty
    honestShape mixedShape qs sampled same]
  exact accepted

/-- Small valid schedule for a fully kernel-evaluated counterexample. Production
profiles are analyzed separately; this is not a production probability claim. -/
def smallConfig : Config := ⟨3, #[1,1], #[1,1], #[1,1], #[0,1]⟩

def smallWeight : Array E := #[E.one,E.zero,E.zero,E.zero,E.zero,E.zero,E.zero,E.zero]

def smallRoot : Oracle :=
  #[#[E.zero],#[E.one],#[E.zero],#[E.one],#[E.zero],#[E.one],#[E.zero],#[E.one]]

def smallChallenges (branch : Bool) : Challenges :=
  ⟨#[⟨#[E.zero], #[#[E.zero,E.zero]], #[if branch then E.one else E.zero], E.one⟩,
     ⟨#[E.zero], #[], #[E.zero], E.one⟩], #[E.zero]⟩

def smallProof (branch : Bool) : Opening :=
  let t := if branch then E.one else E.zero
  ⟨⟨t,t⟩,
    #[⟨#[⟨t,t⟩], some #[#[t,E.zero],#[t,E.zero],#[t,E.zero],#[t,E.zero]],
        #[⟨t,⟨t,t⟩⟩], #[#[t]], ⟨t,if branch then E.zero else t⟩⟩,
      ⟨#[⟨t,t⟩], none, #[], #[#[t,E.zero]], ⟨t,t⟩⟩],
    #[t,E.zero], #[]⟩

def smallSession (branch : Bool) : Except String Unit :=
  verify smallConfig (smallChallenges branch) 1 smallRoot smallWeight
    (if branch then E.one else E.zero) (smallProof branch)

private theorem kmul_zero (a : K) : kmul a 0 = 0 := by
  apply FieldModel.toBaseQuotient_injective
  simp [FieldModel.toBaseQuotient_kmul]

private theorem zero_kmul (a : K) : kmul 0 a = 0 := by
  apply FieldModel.toBaseQuotient_injective
  simp [FieldModel.toBaseQuotient_kmul]

private theorem one_kmul (a : K) : kmul 1 a = a := by
  apply FieldModel.toBaseQuotient_injective
  simp [FieldModel.toBaseQuotient_kmul]

private theorem kmul_one (a : K) : kmul a 1 = a := by
  apply FieldModel.toBaseQuotient_injective
  simp [FieldModel.toBaseQuotient_kmul]

private theorem kinv_one : kinv 1 = 1 := by
  apply FieldModel.toBaseQuotient_injective
  simp [FieldModel.toBaseQuotient_kinv]

private theorem small_columns :
    column 1 0 = #[E.one,E.zero] ∧
    column 2 0 = #[E.one,E.zero,E.zero,E.zero] ∧
    column 2 1 = #[E.one,E.one,E.zero,E.zero] := by
  simp [column, normalizedSubspaces, subspaceRoots, tab, kmul_zero, zero_kmul,
    kmul_one, kinv_one, E.scale, E.one, E.zero,
    Std.Legacy.Range.forIn_eq_forIn_range', List.range',
    Array.forIn_pure_yield_eq_foldl]

private theorem column10 : column 1 0 = #[E.one,E.zero] := small_columns.1
private theorem column20 : column 2 0 = #[E.one,E.zero,E.zero,E.zero] := small_columns.2.1
private theorem column21 : column 2 1 = #[E.one,E.one,E.zero,E.zero] := small_columns.2.2

attribute [local cbv_opaque] column
attribute [local cbv_eval] column10 column20 column21 kmul_zero zero_kmul one_kmul kmul_one

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Two incompatible values of one public linear functional open against exactly
the same malicious immutable commitment, in two separate valid sessions. No
collision, mutable oracle, honest-root premise, or correctness axiom is used. -/
theorem small_two_sessions :
    smallConfig.valid = true ∧
    smallSession false = .ok () ∧ smallSession true = .ok () := by
  cbv

/-- The two accepted claims cannot be explained by any one witness. This rules
out zero-error uniqueness, not a specified probabilistic production bound. -/
theorem small_claims_incompatible :
    ¬ ∃ w : CausalGame.Witness smallConfig 1,
      dot (CausalGame.paddedWitness smallConfig 1 w) smallWeight = E.zero ∧
      dot (CausalGame.paddedWitness smallConfig 1 w) smallWeight = E.one := by
  rintro ⟨w,h0,h1⟩
  have bad : E.zero = E.one := h0.symm.trans h1
  have different : E.zero ≠ E.one := by decide
  exact different bad

private def parityEquiv (m : Nat) (b : Fin 2) :
    {x : Fin (2*m) // x.val % 2 = b.val} ≃ Fin m where
  toFun x := ⟨x.val.val / 2, by have h := x.val.isLt; omega⟩
  invFun y := ⟨⟨2*y.val+b.val, by have h := y.isLt; have hb := b.isLt; omega⟩,
    by simp [Nat.add_mod, Nat.mod_eq_of_lt b.isLt]⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have h := Nat.mod_add_div x.val.val 2
    have hp := x.property
    dsimp
    omega
  right_inv y := by
    apply Fin.ext
    have hb := b.isLt
    dsimp
    omega

private theorem raw_parity_probability (b : Fin 2) :
    SamplingProbability.probability (fun raw : Fin (2^13) => raw.val % 2 = b.val) =
      (1/2 : ℝ) := by
  classical
  unfold SamplingProbability.probability
  dsimp only
  have hc : Fintype.card {raw : Fin (2^13) // raw.val % 2 = b.val} = 4096 := by
    exact (Fintype.card_congr (parityEquiv 4096 b)).trans (by simp)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  norm_num

set_option maxRecDepth 100000 in
private theorem first_stratum_bits :
    ∀ i : Fin 56, (strata 56 13)[i.val]!.1 ≤ 5 := by
  decide +kernel

/-- Production top-bit replacement preserves the low bit in each of its 56
strata. A global-half splice would fail under stratification; a parity splice
does not. This is about the actual sampler, not an iid substitute. -/
theorem first_place_parity (i : Fin 56) (raw : Nat) :
    SamplingProbability.concretePlace 56 13 i.val raw % 2 = raw % 2 := by
  have hb := first_stratum_bits i
  have hd : 2 ∣ 2^(13-(strata 56 13)[i.val]!.1) :=
    dvd_pow_self 2 (by omega)
  unfold SamplingProbability.concretePlace
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd,
    Nat.mod_mod_of_dvd raw hd]
  simp

open scoped BigOperators in
/-- For the smallest rate-4 production profile, either parity branch contains
every first-level query with exact probability 2^-56. It is a sampler theorem;
the full-verifier bridge is `splice_accepts`, and grinding is not credited. -/
theorem production_first_queries_one_parity (b : Fin 2) :
    SamplingProbability.probability
      (fun t : Fin ((56 + 192/13 - 1)/(192/13)) → E =>
        ∃ qs, deriveQueries 13 56 (Array.ofFn t) = some qs ∧
          ∀ i : Fin 56, qs[i.val]! % 2 = b.val) = (1/2 : ℝ)^56 := by
  rw [SamplingProbability.deriveQueries_probability 13 56 (by decide) (by decide)
    (fun _ q => q % 2 = b.val)]
  simp only [first_place_parity, raw_parity_probability, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

set_option maxRecDepth 100000 in
/-- The sampler parameters above are read from the actual production generator. -/
theorem production_first_profile :
    let c := (productionConfig 15 4).getD default
    c.logN - c.folds[0]! + c.rates[0]! = 13 ∧ c.queries[0]! = 56 := by
  decide +kernel

end Whir.CommitmentAmbiguity
