import Whir.CandidateFolding
import Whir.ParameterBounds

/-! Actual novel-coefficient candidate lists satisfy the production Johnson
list cap for every lane count. Distinct matrices differ in some lane, so full
column agreement has the row-code distance, without a lane-count factor. -/
namespace Whir.ConcreteCandidates
open Whir.Concrete Whir.CandidateFolding

private theorem agreement_le_coordinate {I R F : Type*} [Fintype I]
    (u v : I → R → F) (lane : R) :
    CodingBounds.agreement u v ≤
      CodingBounds.agreement (fun i => u i lane) (fun i => v i lane) := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun (Finset.mem_filter.mp hi).2 lane⟩

private theorem arrayCandidates_card_le {F I : Type*} [Field F] [Fintype F]
    (top : Bool) {k lanes : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (oracle : Fin lanes → I → F) (threshold : ℕ) :
    (arrayCandidates top enc oracle threshold).card ≤
      (CandidateFolding.candidates enc oracle threshold).card := by
  classical
  exact Finset.card_image_le

/-- Same-set existential agreement equals the ordinary column-vector agreement
count; this identification concerns fixed lists, not the MCA exceptional event. -/
theorem candidates_eq_codingCandidates {F I : Type*} [Field F] [Fintype F] [Fintype I]
    {k lanes : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (oracle : Fin lanes → I → F) (threshold : ℕ) :
    CandidateFolding.candidates enc oracle threshold =
      CodingBounds.candidates (fun table i lane => enc (table lane) i)
        (fun i lane => oracle lane i) threshold := by
  classical
  ext table
  rw [CandidateFolding.mem_candidates]
  simp only [CodingBounds.candidates, Finset.mem_filter, Finset.mem_univ, true_and,
    CodingBounds.agreement]
  constructor
  · rintro ⟨T, hT, hagree⟩
    apply hT.trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext fun lane => hagree lane i hi⟩
  · intro hcount
    refine ⟨_, hcount, ?_⟩
    intro lane i hi
    exact congrFun (Finset.mem_filter.mp hi).2 lane

/-- No abstract encoding map replaces the actual dense array encoder. -/
theorem concreteEncoder_ofFn (n rate : ℕ) (a : Fin (2^n) → E)
    (q : Fin (2^(n+rate))) :
    concreteEncoder n rate a q = (encode n rate (Array.ofFn a))[q.val]! := by
  have h := AdditiveCode.concrete_encode_eval n rate (Array.ofFn a) (by simp) q.val q.isLt
  simpa [AdditiveCode.concretePolynomial, AdditiveCode.arrayPolynomial,
    AdditiveCode.concreteBaseRepresentation, QueryRefinement.concreteRepresentation,
    concreteEncoder, novelEncoder] using h.symm

/-- The complete matrix code inherits the distance of any differing row. -/
theorem concrete_interleaved_agreement (n rate : ℕ) (depth : n+rate ≤ 64)
    {lanes : ℕ} (u v : Fin lanes → Fin (2^n) → E) (hne : u ≠ v) :
    CodingBounds.agreement (fun q lane => concreteEncoder n rate (u lane) q)
      (fun q lane => concreteEncoder n rate (v lane) q) ≤ 2^n-1 := by
  classical
  obtain ⟨lane, hlane⟩ := Function.ne_iff.mp hne
  have harray : Array.ofFn (u lane) ≠ Array.ofFn (v lane) := by
    intro heq
    apply hlane
    funext j
    have hj := congrArg (fun a : Array E => a[j.val]!) heq
    simpa using hj
  have hrow := AdditiveCode.concrete_encode_agreement_bound n rate depth
    (Array.ofFn (u lane)) (Array.ofFn (v lane)) (by simp) (by simp) harray
  have hcard : CodingBounds.agreement (concreteEncoder n rate (u lane))
      (concreteEncoder n rate (v lane)) =
      ((Finset.range (2^(n+rate))).filter fun q =>
        (encode n rate (Array.ofFn (u lane)))[q]! =
        (encode n rate (Array.ofFn (v lane)))[q]!).card := by
    simp only [CodingBounds.agreement, concreteEncoder_ofFn, Finset.card_filter,
      Finset.sum_range]
  exact (agreement_le_coordinate _ _ lane).trans (hcard.trans_le hrow)

/-- Actual arrays have at most as many candidates as their coefficient tables. -/
theorem concrete_arrayCandidates_card (top : Bool) (n rate threshold : ℕ)
    (depth : n+rate ≤ 64) {lanes : ℕ}
    (oracle : Fin lanes → Fin (2^(n+rate)) → E)
    (hd : 2^n-1 ≤ 2^(n+rate))
    (hthreshold : ((2^(n+rate) : ℕ) : ℚ) * (2^n-1 : ℕ) < (threshold : ℚ)^2) :
    ((arrayCandidates top (concreteEncoder n rate) oracle threshold).card : ℚ) ≤
      (((2^(n+rate) : ℕ) : ℚ) * (((2^(n+rate) : ℕ) : ℚ) - (2^n-1 : ℕ))) /
        ((threshold : ℚ)^2 - ((2^(n+rate) : ℕ) : ℚ) * (2^n-1 : ℕ)) := by
  classical
  apply le_trans (Nat.cast_le.mpr
    (arrayCandidates_card_le top (concreteEncoder n rate) oracle threshold))
  rw [candidates_eq_codingCandidates]
  simpa only [Fintype.card_fin] using CodingBounds.candidates_card
    (fun (table : Fin lanes → Fin (2^n) → E) q lane =>
      concreteEncoder n rate (table lane) q)
    (fun q lane => oracle lane q) threshold (2^n-1) (by simpa using hd)
    (fun u v huv => concrete_interleaved_agreement n rate depth u v huv)
    (by simpa using hthreshold)

/-- The actual configured candidate list cap, for every oracle, layout and
remaining lane count. Neither a list-size nor an encoder-correctness assumption
is supplied: the production certificate and executable encoder prove both. -/
theorem production_arrayCandidates_card (top : Bool) (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) {lanes : ℕ}
    (oracle : Fin lanes → Fin (ParameterBounds.length (ParameterBounds.config p) i) → E) :
    (arrayCandidates top
      (concreteEncoder (CausalGame.remaining (ParameterBounds.config p) i)
        (ParameterBounds.config p).rates[i.val]!) oracle
      (ParameterBounds.threshold (ParameterBounds.config p) i)).card ≤ 2^32 := by
  obtain ⟨hd, hdn, hn, hr, hu, hup, ha, ha1, hgap, hq⟩ :=
    ParameterBounds.production_level_facts p i
  have hexp : CausalGame.remaining (ParameterBounds.config p) i +
      (ParameterBounds.config p).rates[i.val]! ≤ 26 := by
    apply (pow_le_pow_iff_right₀ (by decide : (1:ℕ) < 2)).mp
    exact hn
  have hnum := JohnsonListNumerics.johnson_bound_le_two_pow32
    (ParameterBounds.length (ParameterBounds.config p) i)
    (ParameterBounds.dimension (ParameterBounds.config p) i - 1)
    (ParameterBounds.threshold (ParameterBounds.config p) i) (by omega)
    (ParameterBounds.rho (ParameterBounds.config p) i)
    (ParameterBounds.alpha (ParameterBounds.config p).rates[i.val]!)
    rfl hr ha.le hgap (Nat.le_ceil _)
  have hlist := concrete_arrayCandidates_card top
    (CausalGame.remaining (ParameterBounds.config p) i)
    (ParameterBounds.config p).rates[i.val]!
    (ParameterBounds.threshold (ParameterBounds.config p) i)
    (by omega) oracle (by exact hdn.le) hnum.1
  have hfinal := hlist.trans hnum.2
  exact_mod_cast hfinal

end Whir.ConcreteCandidates
