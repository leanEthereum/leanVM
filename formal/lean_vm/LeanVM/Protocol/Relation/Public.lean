/-
  LeanVM.Protocol.Relation.Public

  Binding the public input, round by round: a memory that does not hold the public input leaves a
  false claim on a memory column, except for one challenge.
-/

module

public import LeanVM.Protocol.Relation.Stack
public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Compile.SpecRules.Bind
import LeanVM.Protocol.Field

/-!
# Binding the public input

`bindPublicInput` (`walk` step 4, `lib.rs`) samples one challenge `c` and leaves, per memory limb,
the claim that the limb's column at `(c, 0, …, 0)` is the line through that limb of the public
input's two halves at `c`. On a column the claim reads `f(0)·(1 + c) + f(1)·c` (`rowMle_line`),
so where the memory's words `0` and `1` are not the public input's (`PubRel` fails) the failing
limb's claim is a nonzero affine function of `c`, false but at one challenge
(`card_line_eq_le_one`). **`pubSpec`**: from `PubRel` failing on every candidate of a subsingleton
`S`, the claims fail on it, error `1/|E|`, which needs no grind.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The line a claim reads -/

theorem length_foldPairs (r : E) : ∀ l : List E, (foldPairs r l).length = l.length / 2
  | [] => by simp [foldPairs]
  | [_] => by simp [foldPairs]
  | _ :: _ :: rest => by
    simp only [foldPairs, List.length_cons, length_foldPairs r rest]
    omega

/-- Folding a table of `2^k` entries at `k` zeros keeps its first entry. -/
theorem headD_foldl_zeros : ∀ (k : ℕ) (l : List E), l.length = 2 ^ k →
    ((List.replicate k (0 : E)).foldl (fun cur r ↦ foldPairs r cur) l).headD 0 = l.headD 0
  | 0, _, _ => rfl
  | k + 1, l, hl => by
    match l, hl with
    | a :: b :: rest, hl =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [headD_foldl_zeros k _ (by
        rw [length_foldPairs]
        simp only [List.length_cons] at hl ⊢
        rw [pow_succ] at hl
        omega)]
      simp [foldPairs]
    | [], hl => exact absurd hl (by positivity)
    | [_], hl => exact absurd hl (by rw [pow_succ]; simp; omega)

/-- **A claim at `(c, 0, …, 0)` reads a line**: `f(0)·(1 + c) + f(1)·c`. -/
theorem rowMle_line (c : E) (k : ℕ) (f : ℕ → E) :
    rowMle (c :: List.replicate k 0) f = f 0 * (1 + c) + f 1 * c := by
  unfold rowMle multilinearEval
  simp only [List.length_cons, List.length_replicate, List.foldl_cons]
  have hl : (List.range (2 ^ (k + 1))).map f = f 0 :: f 1 :: (List.range' 2 (2 ^ (k + 1) - 2)).map f := by
    have h2 : 2 ^ (k + 1) = 2 + (2 ^ (k + 1) - 2) := by
      have : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [List.range_eq_range', h2, ← List.range'_append, List.map_append]
    simp [List.range'_succ]
  rw [hl]
  simp only [foldPairs]
  rw [headD_foldl_zeros k]
  · rfl
  · rw [List.length_cons, length_foldPairs, List.length_map, List.length_range', pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

/-- The line through `x` at `0` and `y` at `1`, at `c`. -/
theorem multilinearEval_line (x y c : E) : multilinearEval [x, y] [c] = x * (1 + c) + y * c := by
  simp [multilinearEval, foldPairs]

/-- **A nonzero line has at most one root.** -/
theorem card_line_eq_le_one {x y : E} (h : x ≠ 0 ∨ y ≠ 0) :
    (Finset.univ.filter fun c : E ↦ x * (1 + c) + y * c = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hab : (a - b) * (x + y) = 0 := by linear_combination ha - hb
  rcases mul_eq_zero.mp hab with h1 | h1
  · exact sub_eq_zero.mp h1
  · have hx : x = 0 := by linear_combination ha - a * h1
    have hy : y = 0 := by linear_combination h1 - hx
    rcases h with h | h
    · exact absurd hx h
    · exact absurd hy h

/-! ## The phase -/

/-- The public input's limb `limb` of its half `half`, as the claims read it. -/
theorem digestHalves_limbs (input : PublicInput) :
    (digestHalves (publicInputDigest input)).1.limb 0 = input.lanes 0 ∧
      (digestHalves (publicInputDigest input)).1.limb 1 = input.lanes 1 ∧
      (digestHalves (publicInputDigest input)).2.limb 0 = input.lanes 2 ∧
      (digestHalves (publicInputDigest input)).2.limb 1 = input.lanes 3 := by
  simp only [digestHalves, publicInputDigest, E.ofLimbs, E.limb]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The claims `bindPublicInput` leaves at the challenge `c`, the memory placed at `m`. -/
def publicClaims (input : PublicInput) (m : Placement) (c : E) : List ColumnClaim :=
  let halves := digestHalves (publicInputDigest input)
  let publicPoint := c :: List.replicate (m.variableCount - 1) 0
  let publicLimbs := ([0, 1] : List (Fin 2)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [c]
  List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩) [memory0, memory1] publicLimbs

theorem bindPublicInput_eq (layout : Layout) (input : PublicInput) :
    bindPublicInput layout (publicInputDigest input) =
      VerifierProgram.sampleChallenge.bind fun c ↦
        (liftOption (layout.placements.getD memory0 none)).bind fun m ↦
          VerifierProgram.ret (publicClaims input m c) := rfl

/-- The claims hold at `c` only on the lines' common roots. -/
theorem claims_hold_iff (layout : Layout) {μ : ℕ} (q : Column μ) (input : PublicInput)
    (m : Placement) (c : E) :
    (∀ cl ∈ publicClaims input m c, ColumnClaimHolds layout q cl) ↔
      (ofK (columnRow layout q memory0 0) - ofK (input.lanes 0)) * (1 + c) +
          (ofK (columnRow layout q memory0 1) - ofK (input.lanes 2)) * c = 0 ∧
        (ofK (columnRow layout q memory1 0) - ofK (input.lanes 1)) * (1 + c) +
          (ofK (columnRow layout q memory1 1) - ofK (input.lanes 3)) * c = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := digestHalves_limbs input
  have hv : ∀ c' i, keccakOutputLane c' = none → columnValue layout q c' i =
      ofK (columnRow layout q c' i) := fun c' i h ↦ by simp [columnValue, h]
  have hm0 : keccakOutputLane memory0 = none := by decide
  have hm1 : keccakOutputLane memory1 = none := by decide
  simp only [publicClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ColumnClaimHolds, rowMle_line, multilinearEval_line, h1, h2, h3, h4,
    hv _ _ hm0, hv _ _ hm1]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · linear_combination -ha
    · linear_combination -hb
  · rintro ⟨ha, hb⟩
    constructor
    · linear_combination -ha
    · linear_combination -hb

open Classical in
/-- The challenges at which the claims hold on a stack failing `PubRel`: at most one. -/
theorem card_claims_hold_le (layout : Layout) {μ : ℕ} (q : Column μ) (input : PublicInput)
    (m : Placement) (hq : ¬ PubRel layout input q) :
    (Finset.univ.filter fun c : E ↦
      ∀ cl ∈ publicClaims input m c, ColumnClaimHolds layout q cl).card ≤ 1 := by
  have hinj : ∀ a b : K, ofK a - ofK b = 0 → a = b := fun a b h ↦ by
    have := congrArg (fun z : E ↦ z.limb 0) (sub_eq_zero.mp h)
    simpa [E.limb] using this
  by_cases h0 : columnRow layout q memory0 0 = input.lanes 0 ∧ columnRow layout q memory0 1 = input.lanes 2
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans (card_line_eq_le_one
      (x := ofK (columnRow layout q memory1 0) - ofK (input.lanes 1))
      (y := ofK (columnRow layout q memory1 1) - ofK (input.lanes 3)) ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ((claims_hold_iff layout q input m c).mp hc).2
    · by_contra hne
      push Not at hne
      exact hq ⟨h0.1, hinj _ _ hne.1, h0.2, hinj _ _ hne.2⟩
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans (card_line_eq_le_one
      (x := ofK (columnRow layout q memory0 0) - ofK (input.lanes 0))
      (y := ofK (columnRow layout q memory0 1) - ofK (input.lanes 2)) ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ((claims_hold_iff layout q input m c).mp hc).1
    · by_contra hne
      push Not at hne
      exact h0 ⟨hinj _ _ hne.1, hinj _ _ hne.2⟩

open Classical in
/-- **Binding the public input, round by round**: from `PubRel` failing on every candidate of a
subsingleton `S`, the claims it leaves fail on it; one challenge, error `1/|E|`. -/
noncomputable def pubSpec (layout : Layout) (input : PublicInput) {μ : ℕ} (S : Set (Column μ))
    (hS : S.Subsingleton) {εmax T : ENNReal} :
    Spec (bindPublicInput layout (publicInputDigest input))
      (fun _ ↦ ∀ q ∈ S, ¬ PubRel layout input q)
      (fun cs _ ↦ ∀ q ∈ S, ¬ ∀ cl ∈ cs, ColumnClaimHolds layout q cl) εmax
      ((Fintype.card E : ENNReal)⁻¹ + T) T := by
  rw [bindPublicInput_eq]
  refine Spec.bind (Spec.sampleE (Post := fun c _ ↦ ∀ q ∈ S, ¬ ∀ cl ∈ publicClaims input
    (((layout.placements.getD memory0 none)).getD default) c, ColumnClaimHolds layout q cl)
    (Fintype.card E : ENNReal)⁻¹ ?_) fun c ↦ ?_
  · intro h₀ hpre
    have hle : (Finset.univ.filter fun c : E ↦ ¬ ∀ q ∈ S, ¬ ∀ cl ∈ publicClaims input
        (((layout.placements.getD memory0 none)).getD default) c,
          ColumnClaimHolds layout q cl).card ≤ 1 := by
      rcases S.eq_empty_or_nonempty with hE | ⟨q, hq⟩
      · subst hE; simp
      · refine (Finset.card_le_card fun c hc ↦ ?_).trans
          (card_claims_hold_le layout q input
            ((layout.placements.getD memory0 none).getD default) (hpre q hq))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        by_contra hn
        exact hc fun q' hq' ↦ by rw [← hS hq hq']; exact hn
    calc (Fintype.card E : ENNReal)⁻¹ * _ ≤ (Fintype.card E : ENNReal)⁻¹ * 1 := by
          gcongr; exact_mod_cast hle
      _ = _ := mul_one _
  · rcases hm : layout.placements.getD memory0 none with _ | m
    · exact (Spec.fail.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)
    · exact (Spec.ret (Post := fun cs _ ↦ ∀ q ∈ S, ¬ ∀ cl ∈ cs, ColumnClaimHolds layout q cl)
        (publicClaims input m c)).mono (fun _ h ↦ by simpa [hm] using h) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl

end

end LeanVM.Protocol.Relation
