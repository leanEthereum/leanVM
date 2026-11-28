/-
  LeanVM.Guest.Batch.RomSpec

  The doom specification of the batching after its children: children with a false claim leave
  the prover doomed, and each group of challenges escapes with probability at most
  `max(2M + 2, 16) · 2^-131`, for fewer than `M` children, the group `(λ, column)` after its proof
  of work.
-/

module

public import LeanVM.Guest.Batch.Sound
public import LeanVM.Protocol.Compile.SpecRules.Cert
public import LeanVM.Guest.BatchConsts
import LeanVM.Protocol.Field

/-!
# The batching's doom specification

For children `cs` of the split program's shapes one of whose claims is false (`BatchBad`),
`restSpec` is a specification (`LeanVM.Protocol.Compile.Spec`) of
`batchingAfterChildren bytecode cs` from the empty history, with doom at the start, rejection at
the end, and every group of challenges escaping doom with probability at most
`batchε M = max(2M + 2, 16) · 2^-131`, for `n < M` children, discounted by the proof of work before
it:

* **the group `λ`, then the `splitLog` column challenges `column`** (`groupBlock`, no prover move
  between them): the batched claim is the true one, the table's values at the claims' points, only
  at a fraction `(2n + 4)/|E| ≤ (2M + 2)/|E|` of them (`avg_gap_le`: the gaps' polynomial, of total
  degree `2(n − 1) + splitLog`), and the proof of work of `batchLambdaGrindBits = 3` bits before
  them brings that to `(2M + 2) · 2^-131`;
* **a round**: the claim is not the cube sum after the earlier challenges (`cubeSum`); the
  round's messages keep it, and its challenge breaks it at a root of the round's gap, a nonzero
  quadratic: at most `2/|E| = 16 · 2^-131` (`quadratic_roots`);
* **the final value and the check**: the final claim, not the polynomial at the challenges,
  contradicts the check and the deferred claim's truth, so the program rejects.

Where the split table is not of `2^deferredVariableCount` entries, no deferred claim of the
program's shape holds (`HoldsWithShape`), and doom is that fact, constant, until the final check
refutes it.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Node
open scoped ENNReal

@[expose] public section

attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-- The batching's escape bound per group of challenges, for fewer than `M` children:
`max(2M + 2, 16) · 2^-131` (a round's `2/|E| = 16 · 2^-131`; the group `(λ, column)`'s
`(2M + 2)/|E|`, discounted by its proof of work of `3` bits). -/
noncomputable def batchε (M : ℕ) : ℝ≥0∞ := (max (2 * M + 2) 16 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 131

/-- `|E|⁻¹ = 2^-128`. -/
theorem invE_eq : invE = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have hc : Fintype.card E = 2 ^ 128 := by convert card_E
  rw [invE, hc, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- A round's bound, `2/|E| = 16 · 2^-131`, is within `batchε M`. -/
theorem invE_two_le_batchε (M : ℕ) : invE * 2 ≤ batchε M := by
  have h8 : (2 : ℝ≥0∞) ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc invE * 2 = (2 : ℝ≥0∞)⁻¹ ^ 128 * 2 * ((2 : ℝ≥0∞) ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ 3) := by
        rw [invE_eq, h8, mul_one]
    _ = ((16 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 131 := by push_cast; ring
    _ ≤ batchε M := by
        unfold batchε
        gcongr
        exact le_max_right _ _

/-- **The group's bound through its proof of work**: `(2M + 2)/|E|` discounted by `2⁻¹ ^ 3` is
`batchε M`'s first term. -/
theorem grind_group_le_batchε (M : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ batchLambdaGrindBits * (invE * (2 * M + 2 : ℕ) + 0) ≤ batchε M := by
  calc (2 : ℝ≥0∞)⁻¹ ^ batchLambdaGrindBits * (invE * (2 * M + 2 : ℕ) + 0)
      = ((2 * M + 2 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
        rw [invE_eq, show batchLambdaGrindBits = 3 by decide, add_zero]
        ring
    _ ≤ batchε M := by
        unfold batchε
        gcongr
        exact le_max_left _ _

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
  readPacked := fun _ _ _ _ h ↦ h
  grind := fun _ _ h ↦ h
  commit := fun _ _ _ _ h ↦ h
  sample := fun _ _ ↦ (avg_const _).le
  samplePacked := fun _ _ ↦ (avgPk_const _ _).le
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

/-! ## The group `(λ, column)` -/

/-- **The batching's group of challenges**: `λ`, then the `splitLog` column challenges. -/
def groupBlock : VerifierProgram (E × List E) := do
  let lam ← VerifierProgram.sampleChallenge
  let column ← VerifierProgram.sampleChallenges splitLog
  return (lam, column)

theorem onlySamples_groupBlock : OnlySamples groupBlock := fun lam ↦
  onlySamples_sampleChallenges (fun column ↦ VerifierProgram.ret (lam, column)) (fun _ ↦ trivial)
    splitLog

/-- The group's escape: over `λ`, then `splitLog` challenges, the fraction breaking `Q`. -/
theorem escRet_groupBlock (Q : E × List E → Prop) (h₀ : List Ev) :
    VerifierProgram.escRet (fun r _ ↦ Q r) h₀ [] groupBlock =
      invE * ∑ lam : E, avgL splitLog fun column ↦ ind (¬ Q (lam, column)) := by
  have e : groupBlock = VerifierProgram.sample fun lam ↦
      VerifierProgram.sampleChallenges splitLog >>= fun column ↦ VerifierProgram.ret (lam, column) := by
    simp only [groupBlock, VerifierProgram.sampleChallenge, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq]
    rfl
  classical
  rw [VerifierProgram.escRet, e, VerifierProgram.retExp]
  refine congrArg _ (Finset.sum_congr rfl fun lam _ ↦ ?_)
  rw [retExp_sampleChallenges]
  congr 1
  funext column
  by_cases hq : Q (lam, column) <;> simp [VerifierProgram.retExp, hq, ind]

/-- **The group**: from `P`, the fraction of `(λ, column)` breaking `Q` at most `e < 1` gives the
lead `e`. -/
noncomputable def groupSpec {P : Prop} {Q : E × List E → Prop} {εmax e : ℝ≥0∞} (he : e < 1)
    (hesc : P → invE * ∑ lam : E, avgL splitLog (fun column ↦ ind (¬ Q (lam, column))) ≤ e) :
    Spec groupBlock (fun _ ↦ P) (fun r _ ↦ Q r) εmax (e + 0) 0 :=
  Spec.ofNoMove (fun _ ha ↦ (onlySamples_groupBlock.after ha).not_isMove) he
    fun h₀ hP ↦ by rw [escRet_groupBlock]; exact hesc hP

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
    linear_combination (-(claim + g.2 + 2 * g.1)) * Tables.two_eq_zero_E
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
  | k + 1, claim, pre, hk => by
    rw [sumcheckRoundsProgram_succ]
    exact (Spec.readE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
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

/-! ## The final value and the check -/

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

/-! ## The batching after its children -/

/-- The table the batching sums: the split program's, in `E`. -/
abbrev splitTableE (bytecode : List K) : List E := (splitTable bytecode).map ofK

/-- **Some child's claim is false** on the split table: a fresh claim's values (`FreshClaim.Holds`)
or a carried claim's value. -/
def SomeFalse (bytecode : List K) (cs : List ChildClaims) : Prop :=
  ∃ c ∈ cs, ¬ c.freshClaim.Holds bytecode ∨
    c.carriedClaim.bytecodeValue ≠ multilinearEval (splitTableE bytecode) c.carriedClaim.bytecodePoint

/-- **A batching's bad children**: the split table is not of the deferred claim's size, so no
deferred claim of the program's shape holds, or some child's claim is false. -/
def BatchBad (bytecode : List K) (cs : List ChildClaims) : Prop :=
  (splitTable bytecode).length ≠ 2 ^ deferredVariableCount bytecode ∨ SomeFalse bytecode cs

open Classical in
/-- The batching after its children, its group of challenges a block. -/
theorem batchingAfterChildren_eq (check : DeferredBytecodeClaim → Prop) (bytecode : List K)
    (cs : List ChildClaims) :
    batchingAfterChildren check bytecode cs =
      VerifierProgram.grindProofOfWork batchLambdaGrindBits >>= fun _ ↦ groupBlock >>= fun r ↦
        sumcheckRoundsProgram (batchedClaim cs (lambdaPowers r.1 cs.length) r.2)
            (deferredVariableCount bytecode) >>= fun rounds ↦ do
          let finalValue ← VerifierProgram.readScalar
          VerifierProgram.require
            (rounds.2 = finalValue * batchedBytecodeWeight cs (lambdaPowers r.1 cs.length) r.2
                rounds.1 ∧ check ⟨rounds.1, finalValue⟩)
          return true := by
  simp only [batchingAfterChildren, groupBlock, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.pure_eq, VerifierProgram.ret_bind]

/-- The instructions are `2^kbc` where the split table is `2^deferredVariableCount` entries. -/
theorem instructions_of_table {bytecode : List K}
    (hT : (splitTable bytecode).length = 2 ^ deferredVariableCount bytecode) :
    bytecode.length >>> bytecodeSlotBits = 2 ^ instructionVariableCount bytecode := by
  rw [length_splitTable, deferredVariableCount, pow_add] at hT
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hT

/-- The group's doom: the column challenges of `splitLog` coordinates, and the batched claim
not the cube sum of the batching's polynomial. -/
def GroupDoom (bytecode : List K) (cs : List ChildClaims) (r : E × List E) : Prop :=
  r.2.length = splitLog ∧ batchedClaim cs (lambdaPowers r.1 cs.length) r.2 ≠
    cubeSum (deferredVariableCount bytecode)
      (splitPoly (splitTableE bytecode) cs (lambdaPowers r.1 cs.length) r.2) []

/-- `(2M + 2)/|E| < 1`, for `M ≤ 2^64 - 1`. -/
theorem invE_group_lt_one {M : ℕ} (hM : M ≤ 2 ^ 64 - 1) : invE * (2 * M + 2 : ℕ) < 1 := by
  rw [invE_eq]
  calc (2 : ℝ≥0∞)⁻¹ ^ 128 * ((2 * M + 2 : ℕ) : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 * ((2 ^ 66 : ℕ) : ℝ≥0∞) := by gcongr; omega
    _ = (2 : ℝ≥0∞)⁻¹ ^ 62 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show 128 = 62 + 66 by rfl, pow_add, mul_assoc,
        ← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
    _ < 1 := pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) (by norm_num)

/-- **The group's escape**: from children with a false claim, the split table of the deferred
claim's size, the fraction of `(λ, column)` leaving the group's doom is at most `(2M + 2)/|E|`. -/
theorem group_escape {M : ℕ} {bytecode : List K} {cs : List ChildClaims}
    (hT : (splitTable bytecode).length = 2 ^ deferredVariableCount bytecode) (hn : cs.length < M)
    (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c) (hf : SomeFalse bytecode cs) :
    invE * ∑ lam : E, avgL splitLog (fun column ↦ ind (¬ GroupDoom bytecode cs (lam, column))) ≤
      invE * (2 * M + 2 : ℕ) := by
  refine le_trans ?_ ((avg_gap_le (instructions_of_table hT) hs hf).trans ?_)
  · gcongr with lam
    refine avgL_mono splitLog fun column hcol ↦ ind_mono fun h ↦ ?_
    have hpts : PointsOf (deferredVariableCount bytecode) cs column := fun c hc ↦
      ⟨by rw [List.length_append, (hs c hc).1, hcol]; rfl, (hs c hc).2.2⟩
    rw [GroupDoom, not_and, split_cubeSum (by rw [List.length_map]; exact hT) hpts] at h
    exact not_not.mp (h hcol)
  · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (by omega))

/-- The batching after the group: the rounds, the final value and the check. -/
noncomputable def afterGroup (bytecode : List K) (cs : List ChildClaims) (r : E × List E) :
    VerifierProgram Bool := by
  classical
  exact sumcheckRoundsProgram (batchedClaim cs (lambdaPowers r.1 cs.length) r.2)
      (deferredVariableCount bytecode) >>= fun rounds ↦ do
    let finalValue ← VerifierProgram.readScalar
    VerifierProgram.require
      (rounds.2 = finalValue * batchedBytecodeWeight cs (lambdaPowers r.1 cs.length) r.2
          rounds.1 ∧ DeferredBytecodeClaim.HoldsWithShape bytecode ⟨rounds.1, finalValue⟩)
    return true

/-- **The batching after the group**, from its doom: the rounds keep doom to the final claim,
which the check refutes. -/
noncomputable def afterGroupSpec (M : ℕ) {bytecode : List K} {cs : List ChildClaims}
    (hT : (splitTable bytecode).length = 2 ^ deferredVariableCount bytecode)
    (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c) (r : E × List E) :
    Spec (afterGroup bytecode cs r) (fun _ ↦ GroupDoom bytecode cs r) (fun b _ ↦ b = false)
      (batchε M) 0 0 :=
  if hl : r.2.length = splitLog then
    have hpts : PointsOf (deferredVariableCount bytecode) cs r.2 := fun c hc ↦
      ⟨by rw [List.length_append, (hs c hc).1, hl]; rfl, (hs c hc).2.2⟩
    ((roundsSpec M (split_quadraticIn (t := splitTableE bytecode)
        (by rw [List.length_map]; exact hT) hpts (lambdaPowers r.1 cs.length))
        (deferredVariableCount bytecode) _ [] (by simp)).bind' fun rb ↦
      endSpec M _ _ fun fv hφ hc ↦ by
        obtain ⟨hcheck, -, hv⟩ := hc
        apply hφ
        rw [hcheck, List.nil_append, splitPoly, hv]).mono (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl
  else Spec.dead.mono (fun _ h ↦ hl h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

theorem batchingAfterChildren_eq' (bytecode : List K) (cs : List ChildClaims) :
    batchingAfterChildren (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs =
      VerifierProgram.grindProofOfWork batchLambdaGrindBits >>= fun _ ↦ groupBlock >>= fun r ↦
        afterGroup bytecode cs r := by
  rw [batchingAfterChildren_eq]
  rfl

/-- **The batching's doom specification** after `n < M` children of the split program's shapes
with a false claim, the split table of the deferred claim's size: the proof of work, whose
discount takes the group's `(2M + 2)/|E|` within `batchε M`, the group and the rounds tracked,
then a fixed fact. -/
noncomputable def goodSpec {M : ℕ} {bytecode : List K} {cs : List ChildClaims}
    (hT : (splitTable bytecode).length = 2 ^ deferredVariableCount bytecode) (hM : M ≤ 2 ^ 64 - 1)
    (hn : cs.length < M) (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (hf : SomeFalse bytecode cs) :
    Spec (batchingAfterChildren (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs)
      (fun h ↦ h = []) (fun b _ ↦ b = false) (batchε M) (batchε M) 0 :=
  (((Spec.grindPos (Post := fun _ _ ↦ SomeFalse bytecode cs) (b := batchLambdaGrindBits)
      (by decide) (fun _ hp ↦ hp) (grind_group_le_batchε M)).bind' fun _ ↦
    (groupSpec (P := SomeFalse bytecode cs) (Q := GroupDoom bytecode cs)
      (invE_group_lt_one hM) fun _ ↦ group_escape hT hn hs hf).bind' fun r ↦
        afterGroupSpec M hT hs r).congr (batchingAfterChildren_eq' bytecode cs).symm).mono
    (fun _ _ ↦ hf) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **The batching's doom specification** where the split table is not of the deferred claim's
size: no deferred claim of the program's shape holds, a constant doom the final check refutes. -/
noncomputable def badSpec {M : ℕ} {bytecode : List K} {cs : List ChildClaims}
    (hT : (splitTable bytecode).length ≠ 2 ^ deferredVariableCount bytecode) :
    Spec (batchingAfterChildren (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs)
      (fun h ↦ h = []) (fun b _ ↦ b = false) (batchε M) (batchε M) 0 :=
  let φ := (splitTable bytecode).length ≠ 2 ^ deferredVariableCount bytecode
  (((Spec.grindPos (Post := fun _ _ ↦ φ) (b := batchLambdaGrindBits) (T := 0) (by decide)
      (fun _ hp ↦ hp) (by simp)).bind' fun _ ↦
    (constSpec groupBlock φ (T := 0) zero_le).bind' fun r ↦
      (constSpec (sumcheckRoundsProgram (batchedClaim cs (lambdaPowers r.1 cs.length) r.2)
          (deferredVariableCount bytecode)) φ (T := 0) zero_le).bind' fun rb ↦
        endSpec M φ _ fun fv hφ hc ↦ by
          obtain ⟨-, hs⟩ := hc
          exact hφ (by rw [← hs.1]; exact congrArg (2 ^ ·) hs.hasBytecodeShape)).congr
    (batchingAfterChildren_eq _ bytecode cs).symm).mono
    (fun _ _ ↦ hT) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **The batching's doom specification** after `n < M` children of the split program's shapes,
bad (`BatchBad`). -/
noncomputable def restSpec {M : ℕ} {bytecode : List K} {cs : List ChildClaims}
    (hM : M ≤ 2 ^ 64 - 1) (hn : cs.length < M) (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (hb : BatchBad bytecode cs) :
    Spec (batchingAfterChildren (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs)
      (fun h ↦ h = []) (fun b _ ↦ b = false) (batchε M) (batchε M) 0 :=
  if hT : (splitTable bytecode).length = 2 ^ deferredVariableCount bytecode then
    goodSpec hT hM hn hs (hb.resolve_left (not_not.mpr hT))
  else badSpec hT

end
end LeanVM.Guest.Batch
