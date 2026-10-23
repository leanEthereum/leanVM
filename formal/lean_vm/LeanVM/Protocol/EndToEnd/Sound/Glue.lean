/-
  LeanVM.Protocol.EndToEnd.Sound.Glue

  The seams between the front phases and the stacked opening of the deployed verifier: the
  candidates of the stack's commitment are few, ring switching's postcondition is the opening's
  precondition, the opening's claims are multiaffine, and every phase's error is at most
  `2^-128`.
-/

module

public import LeanVM.Protocol.Whir.Params.Deployed
public import LeanVM.Protocol.Whir.Sound.Candidates
public import LeanVM.Protocol.EndToEnd.Front.BusTable
public import LeanVM.Protocol.EndToEnd.Front.FlockBridge
public import LeanVM.Protocol.EndToEnd.Front.RingMultilinear

/-!
# The seams of the end-to-end specification

Facts that glue the phase specifications of the deployed verifier
(`LeanVM.Protocol.Verifier.verifyExecution`, leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
into one specification:

* `thrOf μ R`: the Johnson threshold of level `0` of the deployed ladder; the stack's doom
  (`CommitDoom`) and the opening's (`StackedPre`) are stated at it.
* `candidates_finite`, `candidates_ncard_le`: the candidates of a level-0 word are the level-0
  Johnson list (`mem_iList_of_candidate`), so there are at most `listMax ≤ 2^18` of them.
* `stackedPre_of_ringPost`: **ring switching's postcondition is the opening's precondition**.
  If no candidate of the stack's word satisfies the program's column claims and the ring claim,
  and the stack's commitment is the only one with level 0's shape, then every candidate violates
  one of the opening's claims `ringSwitchClaim … :: claims.map (·.onStack layout)`.
* `isMultiaffine_eqEval_any`: a column claim's weight `eq_eval(point, ·)` is multiaffine in any
  number of variables, whatever the point's length; with `isMultilinearFn_ringSwitchClaim`, the
  opening's claims are multiaffine.
* `le_eps_of_nat`, `coe_overE`: the error arithmetic. Every phase's error is a natural number
  over `|E| = 2^192`; it is at most `2^-128` when the number is at most `2^64`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal NNReal

@[expose] public section

/-! ## The threshold and the candidates -/

/-- The Johnson threshold of level `0` of the deployed ladder of `(μ, R)`. -/
noncomputable def thrOf (μ R : ℕ) : ℕ := (Whir.Params.deployedCodes μ R 0).thr

/-- The candidates of a level-0 word are finite. -/
theorem candidates_finite {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R)
    (hμ : laneBits ≤ μ) (W : Word) : (Candidates μ R P₀.thr W).Finite := by
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩
  refine Set.Finite.of_finite_image (f := encStack μ R') ?_
    ((encStack_injective hμ h64).injOn)
  refine (Whir.iList (ReedSolomon.code (Whir.domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits)))
    P₀.thr (laneWord μ R' W)).finite_toSet.subset ?_
  rintro _ ⟨q, hq, rfl⟩
  exact mem_iList_of_candidate h64 hq

/-- **The candidates of a level-0 word are at most `listMax`.** -/
theorem candidates_ncard_le {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) (W : Word) :
    (Candidates μ R P₀.thr W).ncard ≤ P₀.listMax := by
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩
  set L := Whir.iList (ReedSolomon.code (Whir.domain (μ - laneBits) R' h64)
    (2 ^ (μ - laneBits))) P₀.thr (laneWord μ R' W)
  calc (Candidates μ R' P₀.thr W).ncard ≤ (L : Set _).ncard :=
        Set.ncard_le_ncard_of_injOn (encStack μ R') (fun q hq ↦ mem_iList_of_candidate h64 hq)
          ((encStack_injective hμ h64).injOn) L.finite_toSet
    _ = L.card := Set.ncard_coe_finset L
    _ ≤ P₀.listMax := P₀.card_iList_le _

/-- A stack read on equal variables is a candidate exactly when it is one. -/
theorem mem_candidates_castColumn {a b : ℕ} (e : a = b) (R : ℕ) (W : Word) (q : Column a) :
    castColumn e q ∈ Candidates b R (thrOf b R) W ↔ q ∈ Candidates a R (thrOf a R) W := by
  subst e
  simp [castColumn]

/-! ## Ring switching to the stacked opening -/

/-- The first commitment's word of a history whose commitments are exactly level 0's. -/
theorem firstWord_of_shapeOK {P₀ : LevelCode} {h : List Ev}
    (hJ : ShapeOK 0 P₀ laneBits (commits h)) : firstWord h = some (wordOf (commits h) 0) := by
  obtain ⟨-, W, hW, -⟩ := hJ
  unfold firstWord wordOf
  rw [List.head?_eq_getElem?, hW]
  rfl

/-- **Ring switching's postcondition is the opening's precondition**: no candidate of the stack's
word satisfies the column claims and the ring claim, and the stack's commitment is the only one,
of level 0's shape; so every candidate violates one of the opening's claims. -/
theorem stackedPre_of_ringPost (prog : Program) (s : Sizes) (ρ : ℕ)
    (cl : List Verifier.ColumnClaim) (r : E × (List E → E)) (h : List Ev)
    (hpost : RingPost (verifierLayout prog s) (candsL prog s ρ thrOf) cl r h)
    (hJ : ShapeOK 0 (Whir.Params.deployedCodes (verifierLayout prog s).stackLog ρ 0) laneBits
      (commits h)) :
    StackedPre (verifierLayout prog s).stackLog ρ
      (Whir.Params.deployedCodes (verifierLayout prog s).stackLog ρ 0)
      (ringSwitchClaim (verifierLayout prog s) r.1 r.2 ::
        cl.map (·.onStack (verifierLayout prog s))) (commits h) := by
  refine ⟨hJ, fun q hq ↦ ?_⟩
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  refine hpost q ⟨wordOf (commits h) 0, firstWord_of_shapeOK hJ, ?_⟩
    ⟨fun c hc ↦ hall _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)),
      hall _ List.mem_cons_self⟩
  exact (mem_candidates_castColumn (stackLog_verifierLayout prog s) ρ _ q).2 hq

/-! ## Multiaffine claims -/

/-- `zipWith` reads only as much of its right list as its left list is long. -/
theorem zipWith_take_right (f : E → E → E) :
    ∀ (z m : List E), List.zipWith f z m = List.zipWith f z (m.take z.length)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: z, b :: m => by simp [List.zipWith_cons_cons, zipWith_take_right f z m]

/-- `zipWith` reads only as much of its left list as its right list is long. -/
theorem zipWith_take_left (f : E → E → E) :
    ∀ (z m : List E), List.zipWith f z m = List.zipWith f (z.take m.length) m
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: z, b :: m => by simp [List.zipWith_cons_cons, zipWith_take_left f z m]

/-- `eq_eval(z, ·)` is multiaffine in any number of variables. -/
theorem isMultiaffine_eqEval_any (z : List E) (n : ℕ) : IsMultiaffine n (eqEval z) := by
  intro l hl k hk X
  rcases le_or_gt z.length n with hz | hz
  · -- Only the first `|z|` coordinates are read.
    have hcut : ∀ m : List E, eqEval z m = eqEval z (m.take z.length) := fun m ↦ by
      unfold eqEval; rw [zipWith_take_right]
    rw [hcut, hcut (l.set k 0), hcut (l.set k 1)]
    rcases lt_or_ge k z.length with hkz | hkz
    · simp only [List.take_set]
      exact isMultiaffine_eqEval z _ (by simp [hl, hz]) k hkz X
    · have hset : ∀ Y, (l.set k Y).take z.length = l.take z.length := fun Y ↦
        List.take_set_of_le hkz
      rw [hset, hset, hset]
      ring
  · -- Only the first `n` coordinates of `z` are read.
    have hcut : ∀ m : List E, m.length = n → eqEval z m = eqEval (z.take n) m := fun m hm ↦ by
      unfold eqEval; rw [zipWith_take_left, hm]
    rw [hcut _ (by simp [hl]), hcut _ (by simp [hl]), hcut _ (by simp [hl])]
    have := isMultiaffine_eqEval (z.take n)
    rw [List.length_take_of_le hz.le] at this
    exact this l hl k hk X

/-- The weight of a column claim on the stack is multiaffine. -/
theorem isMultiaffine_onStack (layout : Verifier.Layout) (c : Verifier.ColumnClaim) :
    IsMultiaffine layout.stackLog (c.onStack layout).1 :=
  isMultiaffine_eqEval_any _ _

/-! ## The error arithmetic -/

/-- The cardinality of `E` in `ℝ≥0∞`. -/
theorem card_E_ennreal : (Fintype.card E : ℝ≥0∞) = ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [card_E]

/-- `c/|E|` in `ℝ≥0∞`. -/
theorem coe_overE (c : ℕ) :
    ((overE c : ℝ≥0) : ℝ≥0∞) = (c : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [overE, ENNReal.coe_div (by simp), ENNReal.coe_natCast, card_E,
    ENNReal.coe_natCast]

/-- `c/|E|` with the cardinality as `Nat.card`. -/
theorem coe_div_natCard (c : ℕ) :
    ((((c : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0)) : ℝ≥0∞) = (c : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [Nat.card_eq_fintype_card]
  exact coe_overE c

/-- `L · (c/|E|) = (L·c)/|E|`. -/
theorem mul_div_E (L c : ℕ) :
    (L : ℝ≥0∞) * ((c : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞)) =
      ((L * c : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [← mul_div_assoc, Nat.cast_mul]

/-- Sums of errors over `|E|`. -/
theorem div_E_add (a b : ℕ) :
    (a : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) =
      ((a + b : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [ENNReal.div_add_div_same, Nat.cast_add]

/-- **An error of at most `2^64` over `|E|` is at most `2^-128`.** -/
theorem le_eps_of_nat {x : ℝ≥0∞} {n : ℕ} (hx : x ≤ (n : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞))
    (hn : n ≤ 2 ^ 64) : x ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  refine hx.trans ?_
  calc (n : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞)
      ≤ ((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.2 hn) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
      rw [ENNReal.div_eq_inv_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        show (192 : ℕ) = 128 + 64 from rfl, pow_add, ENNReal.mul_inv (by simp) (by simp),
        mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- `2^-128 < 1`. -/
theorem eps_lt_one : (2 : ℝ≥0∞)⁻¹ ^ 128 < 1 :=
  pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.2 (by norm_num)) (by norm_num)

/-! ## The phases' errors at `L₀ = 2^18` -/

section PhaseErrors

/-- The number of candidates of the stack's word the phases are charged for. -/
abbrev L₀ : ℕ := 2 ^ 18

/-- `L·(c/|E|)` as a natural number over `|E|`. -/
theorem mul_overE (L c : ℕ) :
    (L : ℝ≥0∞) * ((overE c : ℝ≥0) : ℝ≥0∞) = ((L * c : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [coe_overE, mul_div_E]

/-- A sum of `n` copies of `L·(1/|E|)`. -/
theorem sum_mul_overE_one (n L : ℕ) :
    (∑ _i ∈ Finset.range n, (L : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) =
      ((n * L : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_overE, ← mul_div_assoc,
    ← Nat.cast_mul, mul_one]

theorem roundError_eq (L d : ℕ) :
    roundError L d = ((L * d : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [roundError, coe_div_natCard, mul_div_E]

theorem lambdaError_eq (L : ℕ) :
    lambdaError L = ((L * 2 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [lambdaError, coe_div_natCard, mul_div_E]

theorem unitError_eq (L : ℕ) :
    unitError L = ((L * 1 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [unitError, card_E_ennreal, mul_one, ENNReal.div_eq_inv_mul, mul_comm]

theorem xiError_eq (I : M3Instance) (L : ℕ) :
    xiError I L = ((L * (I.B + 3 - 1) : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [xiError, coe_div_natCard, mul_div_E]

theorem abError_eq (I : M3Instance) (L : ℕ) :
    abError I L = ((L * (4 * 2 ^ I.μBus) : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [abError, mul_overE]

theorem eBatch_le (J : ℕ) (P₀ : LevelCode) (hJ : J ≤ 231) (hL : P₀.listMax ≤ L₀) :
    eBatch J P₀ ≤ ((230 * L₀ : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [eBatch, card_E_ennreal]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  exact Nat.mul_le_mul (by omega) hL

/-- **The lead after the table sumcheck**: the public input's challenge, which makes no prover
move, and the at most `46` coordinates of Flock's point after it are one group, of at most
`L₀ · 47/|E|`. -/
theorem pubLead_le (L : ℕ) {n : ℕ} (hn : n ≤ 46) :
    (L : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞) +
        ((∑ _i ∈ Finset.range n, (L : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + 0) ≤
      (L : ℝ≥0∞) * ((overE 47 : ℝ≥0) : ℝ≥0∞) := by
  rw [add_zero, sum_mul_overE_one, mul_overE, mul_overE, div_E_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.2 (by nlinarith)) _

/-- **Every error hypothesis of the front phases**, at `L₀ = 2^18` candidates, `|E| = 2^192`,
a bus of depth at most `38`, `B ≤ 2^20`, at most `231` opening claims with a level-0 list of at
most `2^18`, and the lead after the table sumcheck at most `L₀ · 47/|E|` (the public input's
challenge and at most `46` Flock coordinates, `pubLead_le`): each is at most `2^-128`. -/
theorem phase_errors (I : M3Instance) (hμ : I.μBus ≤ 38) (hB : I.B ≤ 2 ^ 20) :
    abError I L₀ + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧ abError I L₀ < 1 ∧
    roundError L₀ 4 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    interpLead L₀ 2 (lambdaError L₀) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    lambdaError L₀ + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    roundError L₀ 3 + (L₀ : ℝ≥0∞) * ((overE 47 : ℝ≥0) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    (L₀ : ℝ≥0∞) * ((overE 47 : ℝ≥0) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    (∀ n, xiError I L₀ + sumcheckLead n ((L₀ : ℝ≥0∞) * ((overE 47 : ℝ≥0) : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128) ∧
    (∀ (J : ℕ) (P₀ : LevelCode), J ≤ 231 → P₀.listMax ≤ L₀ →
      (∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + eBatch J P₀ ≤
        (2 : ℝ≥0∞)⁻¹ ^ 128) ∧
    (L₀ : ℝ≥0∞) * ((overE 127 : ℝ≥0) : ℝ≥0∞) + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 ∧
    (L₀ : ℝ≥0∞) * ((overE 3 : ℝ≥0) : ℝ≥0∞) + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have hp : 2 ^ I.μBus ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) hμ
  have hab : abError I L₀ + 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
    rw [add_zero, abError_eq]
    exact le_eps_of_nat le_rfl (by simp only [L₀]; nlinarith)
  refine ⟨hab, ((add_zero (abError I L₀)).symm.le.trans hab).trans_lt eps_lt_one, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [roundError_eq]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [interpLead_eq, unitError_eq, lambdaError_eq, mul_div_E, div_E_add]
    exact le_eps_of_nat le_rfl (by norm_num)
  · rw [add_zero, lambdaError_eq]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [roundError_eq, mul_overE, div_E_add]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)
  · intro n
    refine le_eps_of_nat (n := L₀ * (I.B + 3 - 1) + L₀ * 47)
      ((add_le_add le_rfl (sumcheckLead_le _ _)).trans (le_of_eq ?_)) ?_
    · rw [xiError_eq, mul_overE, div_E_add]
    · simp only [L₀]; omega
  · intro J P₀ hJ hL
    refine le_eps_of_nat (n := 6 * L₀ + 230 * L₀)
      ((add_le_add le_rfl (eBatch_le J P₀ hJ hL)).trans (le_of_eq ?_)) ?_
    · rw [sum_mul_overE_one, div_E_add]
    · norm_num
  · rw [add_zero, mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [add_zero, mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [add_zero, mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)

end PhaseErrors

end
end LeanVM.Protocol.EndToEnd.Sound
