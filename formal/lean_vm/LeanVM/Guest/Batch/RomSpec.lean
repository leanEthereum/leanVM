/-
  LeanVM.Guest.Batch.RomSpec

  The doom specification of the batching after its children: children with a false claim leave
  the prover doomed, and each challenge escapes with probability at most
  `max(2M - 3, 8) · 2^-130`, for fewer than `M` children, `λ` after its proof of work.
-/

module

public import LeanVM.Guest.Batch.Prog
public import LeanVM.Protocol.Compile.SpecRules.Cert
public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.ToCompPoly.PowerBatching
public import LeanVM.Guest.AcceptableChild

/-!
# The batching's doom specification

For children `cs` of the bytecode's shapes with some nonzero gap (`SomeGap`), `restSpec` is a
specification (`LeanVM.Protocol.Compile.Spec`) of `batchingAfterChildren bytecode cs` from the empty history,
with doom at the start, rejection at the end, and every challenge escaping doom with
probability at most `batchε M = max(2M - 3, 8) · 2^-130`, for `n < M` children, discounted by the
proof of work before it:

* **the challenge `λ`**: the gaps' combination by the lambdas, the powers `λ^0, …, λ^(2n-1)`, is
  the gaps' polynomial at `λ`, nonzero of degree below `2n` (`card_false_batch_le`): `λ` escapes
  at at most `2n - 1 ≤ 2M - 3` of its values, `(2M - 3)/|E|`, and its proof of work of
  `batchLambdaGrindBits = 2` bits brings that to `(2M - 3) · 2^-130`;
* **a round**: the claim is not the cube sum after the earlier challenges (`cubeSum`); the
  round's messages keep it, and its challenge breaks it at a root of the round's gap, a nonzero
  quadratic: at most `2/|E| = 8 · 2^-130` (`quadratic_roots`);
* **the final value and the check**: the final claim, not the polynomial at the challenges,
  contradicts the check and the deferred claim's truth, so the program rejects.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node
open scoped ENNReal

@[expose] public section

/-- The batching's escape bound per challenge, for fewer than `M` children:
`max(2M - 3, 8) · 2^-130` (a round's `2/|E| = 8 · 2^-130`; `λ`'s `(2M - 3)/|E|`, discounted by its
proof of work of `2` bits). -/
noncomputable def batchε (M : ℕ) : ℝ≥0∞ := (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130

/-- Some child's claim leaves a nonzero gap. -/
def SomeGap (bytecode : List K) (cs : List ChildClaims) : Prop :=
  ∃ g ∈ gapsB bytecode cs, g ≠ 0

-- Two enumerations of `K` are in scope here (`LeanVM.Parameters`' and `LeanDa`'s); the
-- calculus (`Spec.sampleE`, `Spec.sample`) counts `E` with the first.
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-- `|E|⁻¹`, one challenge's share. -/
noncomputable abbrev invE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹

/-- `|E|⁻¹ = 2^-128`. -/
theorem invE_eq : invE = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have hc : Fintype.card E = 2 ^ 128 := by convert card_E
  rw [invE, hc, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- A round's bound, `2/|E| = 8 · 2^-130`, is within `batchε M`. -/
theorem invE_two_le_batchε (M : ℕ) : invE * 2 ≤ batchε M := by
  have h4 : (2 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc invE * 2 = (2 : ℝ≥0∞)⁻¹ ^ 128 * 2 * ((2 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 2) := by
        rw [invE_eq, h4, mul_one]
    _ = ((8 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 130 := by push_cast; ring
    _ ≤ batchε M := by
        unfold batchε
        gcongr
        exact le_max_right _ _

/-- **`λ`'s bound through its proof of work**: `(2M - 3)/|E|` discounted by `2⁻¹ ^ 2` is within
`batchε M`. -/
theorem grind_lam_le_batchε (M : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ batchLambdaGrindBits * (invE * (2 * M - 3 : ℕ)) ≤ batchε M := by
  calc (2 : ℝ≥0∞)⁻¹ ^ batchLambdaGrindBits * (invE * (2 * M - 3 : ℕ))
      = ((2 * M - 3 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 130 := by
        rw [invE_eq, show batchLambdaGrindBits = 2 from rfl]
        ring
    _ ≤ batchε M := by
        unfold batchε
        gcongr
        exact le_max_left _ _

/-- The average of a constant over the challenges is the constant. -/
theorem avg_const (v : ℝ≥0∞) : invE * ∑ _c : E, v = v := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- A fraction of the challenges from a bound on the set they form. -/
theorem card_filter_le {p : E → Prop} {_ : DecidablePred p} {m : ℕ} (h : {c | p c}.ncard ≤ m) :
    invE * ((Finset.univ.filter p).card : ℝ≥0∞) ≤ invE * m := by
  gcongr
  rw [← Set.ncard_coe_finset]
  simpa using h

/-! ## Constant doom -/

open Classical in
/-- **Constant doom**: any program keeps a doom that ignores the history, at the potential the
follower's lead. -/
noncomputable def constSpec {α : Type} (p : VerifierProgram α) (φ : Prop) {εmax T : ℝ≥0∞}
    (hT : T ≤ εmax) : Spec p (fun _ ↦ φ) (fun _ _ ↦ φ) εmax T T where
  D _ _ := φ
  V _ _ := if φ then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [h]
  read := fun _ _ _ h ↦ h
  grind := fun _ _ h ↦ h
  commit := fun _ _ _ _ h ↦ h
  sample := fun _ _ ↦ (avg_const _).le
  query := fun _ _ _ ↦ le_rfl
  moveEnd := fun _ _ _ hD ↦ by simp [hD]
  retEnd := fun _ _ hD ↦ by simp [hD]
  retDoom := fun _ _ hD ↦ by simp [hD]
  post := fun _ _ hD ↦ hD
  bound := fun _ _ _ hD ↦ by
    simp only [hD, ite_true]
    calc _ ≤ 1 * min 1 T := by
          gcongr; exact pow_le_one₀ (zero_le) (ENNReal.inv_le_one.2 one_le_two)
      _ ≤ εmax := by rw [one_mul]; exact (min_le_right _ _).trans hT

/-! ## The challenge `λ` -/

/-- The lambdas of `λ`, flattened, are its first `2n` powers. -/
theorem flat2_lambdaPowers (lam : E) : ∀ n, flat2 (lambdaPowers lam n) =
    (List.range (2 * n)).map (lam ^ ·)
  | 0 => rfl
  | n + 1 => by
    have ih := flat2_lambdaPowers lam n
    simp only [flat2, lambdaPowers] at ih ⊢
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
      List.map_append, List.append_assoc]
    simp

/-- The gaps combined by the powers of `λ` are the gaps' power batch at `λ`. -/
theorem dot_powers_eq {G : List E} {n : ℕ} (hG : G.length = 2 * n) (lam : E) :
    dot (flat2 (lambdaPowers lam n)) G =
      LeanVM.Protocol.powerBatch (fun j : Fin (2 * n) ↦ G.getD j 0) lam := by
  rw [flat2_lambdaPowers, Whir.Complete.dot_eq_sum _ _ (by simp [hG]), LeanVM.Protocol.powerBatch,
    Fin.sum_univ_eq_sum_range (fun j ↦ G.getD j 0 * lam ^ j), List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    mul_comm]

/-- **`λ` is bad at fewer than `2n` values**: the gaps' polynomial, nonzero, has at most
`2n - 1` roots. -/
theorem lam_bad_card {G : List E} {n : ℕ} (hG : G.length = 2 * n) (hg : ∃ g ∈ G, g ≠ 0) :
    {c | ¬ dot (flat2 (lambdaPowers c n)) G ≠ 0}.ncard ≤ 2 * n - 1 := by
  classical
  have ha : ∃ j : Fin (2 * n), G.getD j 0 ≠ (fun _ ↦ (0 : E)) j := by
    obtain ⟨g, hgm, hne⟩ := hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgm
    refine ⟨⟨i, hG ▸ hi⟩, ?_⟩
    show G.getD i 0 ≠ 0
    rw [List.getD_eq_getElem _ _ hi]
    exact hne
  have h := LeanVM.Protocol.card_false_batch_le _ _ ha
  rw [← Set.ncard_coe_finset] at h
  refine le_of_eq_of_le (congrArg Set.ncard ?_) h
  ext c
  simp [dot_powers_eq hG, LeanVM.Protocol.powerBatch]

/-- **The challenge `λ`**, for `n < M` children whose `2n` gaps are not all zero: doom kept, the
gaps' combination by `λ`'s powers nonzero, but for a fraction `(2M - 3)/|E|` of its values. -/
noncomputable def lamSpec (G : List E) {n M : ℕ} (hG : G.length = 2 * n) (hn : n < M) :
    Spec VerifierProgram.sampleChallenge (fun _ ↦ ∃ g ∈ G, g ≠ 0)
      (fun c _ ↦ dot (flat2 (lambdaPowers c n)) G ≠ 0) (batchε M) (invE * (2 * M - 3 : ℕ)) 0 :=
  (Spec.sampleE (Pre := fun _ ↦ ∃ g ∈ G, g ≠ 0)
      (Post := fun c _ ↦ dot (flat2 (lambdaPowers c n)) G ≠ 0) (T := 0) (invE * (2 * M - 3 : ℕ))
      fun _ hg ↦ by
        exact (card_filter_le (lam_bad_card hG hg)).trans
          (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (show 2 * n - 1 ≤ 2 * M - 3 by omega))
            zero_le)).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (add_zero _).le le_rfl

/-- A flat map of blocks of `m` entries has `m` entries per element. -/
theorem length_flatMap_const {α β : Type} (f : α → List β) (m : ℕ) (hf : ∀ a, (f a).length = m) :
    ∀ l : List α, (l.flatMap f).length = m * l.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f m hf l,
      List.length_cons]
    ring

/-! ## The rounds -/

/-- A round's challenge breaks doom at a root of its gap: at most two. -/
theorem round_bad {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) {claim : E} {pre : List E}
    (hl : pre.length < n) (g : E × E) (hc : claim ≠ cubeSum n f pre) :
    {r | ¬ sumcheckRoundPolynomial claim g r ≠ cubeSum n f (pre ++ [r])}.ncard ≤ 2 := by
  have hq : Quadratic fun x ↦ sumcheckRoundPolynomial claim g x - cubeSum n f (pre ++ [x]) :=
    Quadratic.sub ⟨g.2, claim + g.1 + g.1 + g.2, claim + g.1, fun x ↦ by
      simp only [sumcheckRoundPolynomial]; ring⟩ (quadratic_cubeSum hf hl)
  have hne : ∃ x, sumcheckRoundPolynomial claim g x - cubeSum n f (pre ++ [x]) ≠ 0 := by
    by_contra hz'
    have hz : ∀ x, sumcheckRoundPolynomial claim g x - cubeSum n f (pre ++ [x]) = 0 := fun x ↦
      by_contra fun hx ↦ hz' ⟨x, hx⟩
    apply hc
    have h0 := hz 0
    have h1 := hz 1
    simp only [sumcheckRoundPolynomial, sub_eq_zero] at h0 h1
    rw [cubeSum_split hl, ← h0, ← h1]
    linear_combination (-(claim + g.2 + 2 * g.1)) * Whir.Complete.two_eq_zero_E
  simpa [sub_eq_zero] using quadratic_roots hq hne

/-- **The rounds** from `claim`, after the challenges `pre`: a claim that is not the cube sum
leaves a final claim that is not `f` at the challenges, each challenge escaping at most `2/|E|`
of the time. -/
noncomputable def roundsSpec (M : ℕ) {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) :
    (k : ℕ) → (claim : E) → (pre : List E) → pre.length + k = n →
    Spec (sumcheckRoundsProgram claim k) (fun _ ↦ claim ≠ cubeSum n f pre)
      (fun r _ ↦ r.2 ≠ f (pre ++ r.1)) (batchε M) 0 0
  | 0, claim, pre, hk => (Spec.ret (Post := fun r _ ↦ r.2 ≠ f (pre ++ r.1)) ([], claim)).mono
      (fun _ h ↦ by simpa [cubeSum_full (f := f) (by simpa using hk)] using h) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  | k + 1, claim, pre, hk =>
    (Spec.readE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
        (Post := fun _ _ ↦ claim ≠ cubeSum n f pre) (T := 0) (fun _ _ h ↦ h)
        (zero_le)).bind' fun g1 ↦
      (Spec.readE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
          (Post := fun _ _ ↦ claim ≠ cubeSum n f pre) (T := batchε M + 0) (fun _ _ h ↦ h)
          (add_zero _).le).bind' fun gInf ↦
        (Spec.sampleE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
            (Post := fun r _ ↦ sumcheckRoundPolynomial claim (g1, gInf) r ≠ cubeSum n f (pre ++ [r]))
            (T := 0) (batchε M) fun _ h ↦ by
              refine (card_filter_le (round_bad hf (by omega) (g1, gInf) h)).trans ?_
              exact le_of_eq_of_le (by simp) (invE_two_le_batchε M)).bind' fun r ↦
          (roundsSpec M hf k _ (pre ++ [r]) (by simp; omega)).bind' fun rest ↦
            (Spec.ret (r :: rest.1, rest.2)).mono (fun _ h ↦ by simpa using h)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The claims -/

/-- Children of the bytecode's shapes have points of `log₂` of its length. -/
theorem bytecodePoints {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c) : ∀ c ∈ cs,
      c.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length ∧
        c.carriedClaim.bytecodePoint.length = Nat.log2 bytecode.length :=
  fun c hc ↦ ⟨(hs c hc).1, (hs c hc).2⟩

/-- Lambdas whose combination of the gaps is nonzero leave a claim that is not the cube sum. -/
theorem claimB_ne {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims} (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c) {l : List (E × E)}
    (hl : l.length = cs.length) (hd : dot (flat2 l) (gapsB bytecode cs) ≠ 0) :
    batchedClaim cs l ≠ cubeSum (Nat.log2 bytecode.length) (bytecodePoly bytecode cs l) [] := by
  rw [bytecode_cubeSum hb (bytecodePoints hs) l]
  intro heq
  exact hd ((claimB_sub bytecode cs l hl).symm.trans (sub_eq_zero.2 heq))

/-- The gaps are two per child. -/
theorem length_gapsB (bytecode : List K) (cs : List ChildClaims) :
    (gapsB bytecode cs).length = 2 * cs.length :=
  length_flatMap_const _ 2 (fun _ ↦ rfl) cs

/-- **The final value and the check**: a fixed doom, which contradicts the check. -/
noncomputable def endSpec (M : ℕ) (φ : Prop) (C : E → Prop) {_ : ∀ a, Decidable (C a)}
    (h : ∀ a, φ → C a → False) :
    Spec (do
        let a ← VerifierProgram.readScalar
        VerifierProgram.require (C a)
        return true) (fun _ ↦ φ) (fun b _ ↦ b = false) (batchε M) 0 0 :=
  (constSpec _ φ zero_le).bind' fun a ↦
    (Spec.require (Post := fun _ _ ↦ False) fun _ hφ hc ↦ h a hφ hc).bind' fun _ ↦
      Spec.dead

/-- **The batching's doom specification** after `n < M` children with a nonzero gap: the proof of
work, whose discount takes `λ`'s `(2M - 3)/|E|` within `batchε M`, the challenge `λ` and the rounds
tracked, then a fixed fact. -/
noncomputable def restSpec {M : ℕ} {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {cs : List ChildClaims}
    (hn : cs.length < M) (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c) (hg : SomeGap bytecode cs) :
    Spec (batchingAfterChildren (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs) (fun h ↦ h = [])
      (fun b _ ↦ b = false) (batchε M) (batchε M) 0 :=
  ((Spec.grindPos (Post := fun _ _ ↦ ∃ g ∈ gapsB bytecode cs, g ≠ 0) (by decide) (fun _ h ↦ h)
      (grind_lam_le_batchε M)).bind'
    fun _ ↦
  (lamSpec (gapsB bytecode cs) (length_gapsB bytecode cs) hn).bind' fun lam ↦
    ((roundsSpec M (bytecode_quadraticIn hb (bytecodePoints hs) (lambdaPowers lam cs.length)) _
        (batchedClaim cs (lambdaPowers lam cs.length)) [] (by simp)).mono
        (fun _ h ↦ claimB_ne hb hs (length_lambdaPowers _ _) h) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl).bind' fun rb ↦
      endSpec M _ _ fun bv hφ hc ↦ by
        obtain ⟨-, -, hv⟩ := hc.2
        apply hφ
        rw [hc.1, List.nil_append, bytecodePoly, hv]).mono
    (fun _ _ ↦ hg) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end
end LeanVM.Guest.Batch
