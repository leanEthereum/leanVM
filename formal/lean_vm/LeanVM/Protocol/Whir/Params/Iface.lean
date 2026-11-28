/-
  LeanVM.Protocol.Whir.Params.Iface

  Ring switching and the stacked opening as the interface the soundness assembly takes: the ring
  claims merged into one stack claim, batched with the others at the challenge ring switching
  draws in the same packed message, and opened by WHIR, every group within `2^-125` after its
  grind.
-/

module

public import LeanVM.Protocol.Whir.Params.Deployed
public import LeanVM.Protocol.Compile.SpecRules.Packed
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom
public import LeanVM.Protocol.Whir.Sound.Descent

/-!
# The opening's interface

`ringSwitch rings` (`ring_switch.rs`) grinds `batchGrindingBits = 13` bits and draws one packed
message: the map's sixteen challenges, `ρ` when it merges two claims, then the stacked opening's
batching challenge `λ`. The ring claim it returns (`ringClaimAt rings pre`, at the first
`ringChallengeCount rings` challenges `pre`) joins the others first, and the stacked opening
batches them at `λ` (`ringResult_eq`).

**What ring switching gives** (`RingFacts μ rings`): the merged claim's weight is multiaffine on
the stack, and a stack failing one of the ring claims satisfies the merged claim at a fraction at
most `3/|E|` of the challenges (`RING_SWITCH_ERROR_NUMERATOR`: `2/|E|` for the map, `1/|E|` for
`ρ`). `Ring/Merge.lean` proves it from the claims' shapes.

**The group** (`card_ringOpen_le`): every bad candidate of the stack's word at level 0's threshold
fails a ring claim (it is then the one candidate `S` the out-of-domain sample leaves) or a claim
of `others`; the batched claim holds of it at a fraction at most `(J + 2)/|E|` of the packed
challenges, `J = |others| + 1`: `3/|E|` for the merged claim, `(J − 1)/|E|` for `λ`. Over the at
most `L₀` candidates, `(maxStackedClaims + 2)·L₀/|E|`, which the parameter check's batching row
grinds (`lambda_row`).

* `ringOpenSpec`: the specification of `ringSwitch rings >>= fun (ring, λ) ↦
  verifyStackedOpeningG μ R (ring :: others) λ` from `RingOpenPre` to a good trace.
* `OpeningIface` and its instance `openingIface`: what the assembly takes.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal

@[expose] public section

/-! ## Ring switching's draw -/

/-- The challenges ring switching draws before `λ`: the map's sixteen, and `ρ` when merging. -/
def ringChallengeCount (rings : List RingClaim) : ℕ :=
  2 * ringMapWidth + if 1 < rings.length then 1 else 0

/-- The merged ring claim at the challenges `pre` before `λ`. -/
def ringClaimAt (rings : List RingClaim) (pre : List E) : StackClaim :=
  ringMerge rings (pre.take ringMapWidth) ((pre.drop ringMapWidth).take ringMapWidth)
    (if 1 < rings.length then pre.getD (2 * ringMapWidth) 0 else 1)

/-- What `ringSwitch` returns at its packed challenges. -/
def ringResult (rings : List RingClaim) (challenges : List E) : StackClaim × E :=
  let merging := decide (1 < rings.length)
  let f := challenges.take ringMapWidth
  let g := (challenges.drop ringMapWidth).take ringMapWidth
  let rest := challenges.drop (2 * ringMapWidth)
  let (rho, batching) := if merging then (rest.getD 0 0, rest.getD 1 0) else (1, rest.getD 0 0)
  (ringMerge rings f g rho, batching)

/-- **`ringSwitch` is the grind, the packed draw, then its result.** -/
theorem ringSwitch_eq (rings : List RingClaim) :
    ringSwitch rings =
      (VerifierProgram.grindProofOfWork Whir.batchGrindingBits >>= fun _ ↦
        VerifierProgram.sampleChallengesPacked (ringChallengeCount rings + 1)) >>= fun ch ↦
          VerifierProgram.ret (ringResult rings ch) := by
  unfold ringSwitch ringChallengeCount ringResult
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.pure_eq,
    decide_eq_true_eq]

/-- The result is the merged claim at the first challenges, and `λ` the next. -/
theorem ringResult_eq (rings : List RingClaim) (ch : List E) :
    ringResult rings ch =
      (ringClaimAt rings (ch.take (ringChallengeCount rings)),
        ch.getD (ringChallengeCount rings) 0) := by
  unfold ringResult ringClaimAt ringChallengeCount
  by_cases hm : 1 < rings.length <;>
    simp [hm, ringMapWidth, List.take_take, List.drop_take, List.getD_eq_getElem?_getD,
      List.getElem?_drop]

/-! ## What ring switching gives -/

open Classical in
/-- **Ring switching's facts** on the ring claims `rings`: the merged claim's weight is multiaffine
on the stack's `μ` variables, and for a stack failing one of the claims the merged claim holds at
a fraction at most `3/|E|` of the challenges before `λ`. -/
structure RingFacts (μ : ℕ) (rings : List RingClaim) : Prop where
  multiaffine : ∀ pre : List E, IsMultiaffine μ (ringClaimAt rings pre).1
  sound : ∀ q : Column μ, (∃ rc ∈ rings, ¬ Relation.RingClaimHolds q rc) →
    avgPk (ringChallengeCount rings)
        (fun pre ↦ if StackClaim.Holds μ (ringClaimAt rings pre) q then 1 else 0) ≤
      (3 : ℝ≥0∞) / Fintype.card E

/-! ## Averages -/

theorem avgPk_finset_sum {ι : Type} (s : Finset ι) (n : ℕ) (f : ι → List E → ℝ≥0∞) :
    avgPk n (fun l ↦ ∑ i ∈ s, f i l) = ∑ i ∈ s, avgPk n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using avgPk_const n 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [avgPk_add, ih]

theorem avgPk_one (f : List E → ℝ≥0∞) :
    avgPk 1 f = (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, f [c] := by
  rw [avgPk_succ]
  rfl

open Classical in
/-- **The batching challenge**: for a stack failing one of the claims, the batched claim holds at
no more than `J − 1` of the challenges. -/
theorem avg_batch_le {μ : ℕ} (claims : List StackClaim) (q : Column μ)
    (hq : ∃ c ∈ claims, ¬ StackClaim.Holds μ c q) :
    avgPk 1 (fun l ↦ if StackClaim.Holds μ (batchedClaim claims (l.getD 0 0)) q then 1 else 0) ≤
      ((claims.length - 1 : ℕ) : ℝ≥0∞) / Fintype.card E := by
  have hc := card_batch_bad_le claims {q} (Set.finite_singleton q) (fun q' hq' ↦ by
    rw [Set.mem_singleton_iff.mp hq']; exact hq)
  rw [Set.ncard_singleton, one_mul] at hc
  rw [avgPk_one, ENNReal.div_eq_inv_mul]
  gcongr
  have hsum : (∑ c : E, (if StackClaim.Holds μ (batchedClaim claims ([c].getD 0 0)) q then
      (1 : ℝ≥0∞) else 0)) =
      ((univ.filter fun c : E ↦ StackClaim.Holds μ (batchedClaim claims c) q).card : ℝ≥0∞) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [List.getD_cons_zero]
    split_ifs <;> simp
  rw [hsum]
  refine Nat.cast_le.mpr ((Finset.card_le_card fun c hc' ↦ ?_).trans hc)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff,
    exists_eq_left] at hc' ⊢
  exact hc'

/-! ## The specification -/

/-- **The opening's relation before ring switching**: the commitments have level 0's shape, and
every bad candidate of the stack's word at level 0's threshold is in `S` and fails a ring claim,
or fails a claim of `others`. -/
def RingOpenPre (μ R : ℕ) (S : Set (Column μ)) (rings : List RingClaim)
    (others : List StackClaim) (Bad : Column μ → Prop) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK₀ μ R cs ∧ ∀ q ∈ Candidates μ R (thr0Of μ R) (wordOf cs 0), Bad q →
    (q ∈ S ∧ ∃ rc ∈ rings, ¬ Relation.RingClaimHolds q rc) ∨
      ∃ c ∈ others, ¬ Relation.StackClaimHolds c q

/-- `N/|E|` ground by `b` bits, `N ≤ 2^(b+3)`, is within `2^-125`. -/
theorem discount_le (b N : ℕ) (hN : N ≤ 2 ^ (b + 3)) :
    (2 : ℝ≥0∞)⁻¹ ^ b * ((N : ℝ≥0∞) / Fintype.card E) ≤ εmsg := by
  have hN' : (N : ℝ≥0∞) ≤ 2 ^ (b + 3) := by exact_mod_cast hN
  rw [Protocol.card_E, εmsg, securityBits, Nat.cast_pow, Nat.cast_ofNat]
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ b * 2 ^ b = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ b * ((N : ℝ≥0∞) / 2 ^ 128)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ b * (2 ^ (b + 3) / 2 ^ 128) := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ b * 2 ^ b * (2 ^ 3 / 2 ^ 128) := by
        rw [pow_add, mul_div_assoc, mul_assoc]
    _ = 2 ^ 3 / 2 ^ 128 := by rw [h2, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ ^ 125 := by
        rw [show (2 : ℝ≥0∞) ^ 128 = 2 ^ 3 * 2 ^ 125 by rw [← pow_add],
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
          mul_comm ((2 : ℝ≥0∞) ^ 3)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
          mul_one, ENNReal.inv_pow]

theorem commits_grind_sample (h₀ : List Ev) (b : ℕ) (cs : List E) :
    commits (h₀ ++ Spec.grindEvs b ++ [Ev.samplePacked cs]) = commits h₀ := by
  rw [commits_append, commits_append]
  unfold Spec.grindEvs
  split_ifs <;> simp [commits]

open Classical in
/-- **One candidate's share of the group**: a stack failing one of the ring claims or one of the
others satisfies the batched claim at a fraction at most `(J + 2)/|E|` of the packed draw. -/
theorem avg_candidate_le {μ : ℕ} {rings : List RingClaim} (hrf : RingFacts μ rings)
    (others : List StackClaim) (q : Column μ)
    (hq : (∃ rc ∈ rings, ¬ Relation.RingClaimHolds q rc) ∨
      ∃ c ∈ others, ¬ Relation.StackClaimHolds c q) :
    avgPk (ringChallengeCount rings + 1) (fun ch ↦
      if StackClaim.Holds μ (batchedClaim ((ringResult rings ch).1 :: others)
        (ringResult rings ch).2) q then 1 else 0) ≤
      ((others.length + 3 : ℕ) : ℝ≥0∞) / Fintype.card E := by
  set m := ringChallengeCount rings
  rw [avgPk_append]
  have hin : ∀ pre : List E, pre.length = m →
      avgPk 1 (fun l ↦ if StackClaim.Holds μ (batchedClaim ((ringResult rings (pre ++ l)).1 ::
        others) (ringResult rings (pre ++ l)).2) q then 1 else 0) =
      avgPk 1 (fun l ↦ if StackClaim.Holds μ (batchedClaim (ringClaimAt rings pre :: others)
        (l.getD 0 0)) q then 1 else 0) := by
    intro pre hpre
    refine avgPk_congr fun l hl ↦ ?_
    rw [ringResult_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hpre, Nat.sub_self]
  rw [avgPk_congr hin]
  have hJ : ((ringClaimAt rings [] :: others).length - 1 : ℕ) = others.length := by simp
  rcases hq with hr | ho
  · -- The merged claim holds, or it fails and `λ` batches it away.
    have hbound : ∀ pre : List E,
        avgPk 1 (fun l ↦ if StackClaim.Holds μ (batchedClaim (ringClaimAt rings pre :: others)
          (l.getD 0 0)) q then 1 else 0) ≤
        (if StackClaim.Holds μ (ringClaimAt rings pre) q then 1 else 0) +
          ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E := by
      intro pre
      by_cases hh : StackClaim.Holds μ (ringClaimAt rings pre) q
      · simp only [hh, ↓reduceIte]
        exact le_add_right (avgPk_le_of_le fun l _ ↦ by split_ifs <;> simp)
      · simp only [hh, ↓reduceIte, zero_add]
        have := avg_batch_le (ringClaimAt rings pre :: others) q ⟨_, List.mem_cons_self, hh⟩
        simpa using this
    calc avgPk m _ ≤ avgPk m (fun pre ↦ (if StackClaim.Holds μ (ringClaimAt rings pre) q then 1
            else 0) + ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E) :=
          avgPk_mono fun pre _ ↦ hbound pre
      _ = avgPk m (fun pre ↦ if StackClaim.Holds μ (ringClaimAt rings pre) q then 1 else 0) +
            ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E := by rw [avgPk_add, avgPk_const]
      _ ≤ 3 / Fintype.card E + ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E := by
          gcongr; exact hrf.sound q hr
      _ = _ := by
          rw [← ENNReal.add_div]
          congr 1
          push_cast
          ring
  · obtain ⟨c, hc, hnc⟩ := ho
    calc avgPk m _ ≤ avgPk m (fun _ ↦ ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E) :=
          avgPk_mono fun pre _ ↦ by
            have := avg_batch_le (ringClaimAt rings pre :: others) q
              ⟨c, List.mem_cons_of_mem _ hc, hnc⟩
            simpa using this
      _ = ((others.length : ℕ) : ℝ≥0∞) / Fintype.card E := avgPk_const _ _
      _ ≤ _ := by gcongr; omega

open Classical in
/-- **The group of the packed draw**: at most `(maxStackedClaims + 2)·L₀/|E|`. -/
theorem avg_ringOpen_le {μ R : ℕ} (h : Whir.Admissible μ R) {S : Set (Column μ)}
    {rings : List RingClaim} (hrf : RingFacts μ rings) {others : List StackClaim}
    (hJ : others.length + 1 ≤ maxStackedClaims) {Bad : Column μ → Prop} (h₀ : List Ev)
    (hp : RingOpenPre μ R S rings others Bad (commits h₀)) :
    avgPk (ringChallengeCount rings + 1) (fun ch ↦
      if StackedPre μ R (thr0Of μ R) ((ringResult rings ch).1 :: others) (ringResult rings ch).2
        Bad (commits (h₀ ++ Spec.grindEvs Whir.batchGrindingBits ++ [Ev.samplePacked ch]))
      then 0 else 1) ≤
      (((maxStackedClaims + 2) * listMax₀ μ R : ℕ) : ℝ≥0∞) / Fintype.card E := by
  obtain ⟨hfin, hcard⟩ := candidates_facts h (wordOf (commits h₀) 0)
  set C := {q ∈ Candidates μ R (thr0Of μ R) (wordOf (commits h₀) 0) | Bad q}
  have hCfin : C.Finite := hfin.subset (Set.sep_subset _ _)
  have hCcard : hCfin.toFinset.card ≤ listMax₀ μ R := by
    rw [← Set.ncard_eq_toFinset_card C hCfin]
    exact (Set.ncard_le_ncard (Set.sep_subset _ _) hfin).trans hcard
  have hcover : ∀ ch : List E,
      (if StackedPre μ R (thr0Of μ R) ((ringResult rings ch).1 :: others) (ringResult rings ch).2
        Bad (commits (h₀ ++ Spec.grindEvs Whir.batchGrindingBits ++ [Ev.samplePacked ch]))
        then 0 else 1 : ℝ≥0∞) ≤
      ∑ q ∈ hCfin.toFinset, (if StackClaim.Holds μ (batchedClaim ((ringResult rings ch).1 ::
        others) (ringResult rings ch).2) q then 1 else 0) := by
    intro ch
    split_ifs with hpre
    · exact zero_le
    · rw [StackedPre, commits_grind_sample] at hpre
      simp only [hp.1, true_and, not_forall, not_not, exists_prop] at hpre
      obtain ⟨q, hq, hb, hh⟩ := hpre
      refine le_trans ?_ (Finset.single_le_sum (f := fun q ↦ (if StackClaim.Holds μ
        (batchedClaim ((ringResult rings ch).1 :: others) (ringResult rings ch).2) q then
          (1 : ℝ≥0∞) else 0)) (fun _ _ ↦ zero_le) (hCfin.mem_toFinset.mpr ⟨hq, hb⟩))
      simp [hh]
  calc avgPk _ _ ≤ avgPk (ringChallengeCount rings + 1) (fun ch ↦ ∑ q ∈ hCfin.toFinset,
        (if StackClaim.Holds μ (batchedClaim ((ringResult rings ch).1 :: others)
          (ringResult rings ch).2) q then (1 : ℝ≥0∞) else 0)) := avgPk_mono fun ch _ ↦ hcover ch
    _ = ∑ q ∈ hCfin.toFinset, avgPk (ringChallengeCount rings + 1) (fun ch ↦
        if StackClaim.Holds μ (batchedClaim ((ringResult rings ch).1 :: others)
          (ringResult rings ch).2) q then (1 : ℝ≥0∞) else 0) := avgPk_finset_sum _ _ _
    _ ≤ ∑ _q ∈ hCfin.toFinset, ((others.length + 3 : ℕ) : ℝ≥0∞) / Fintype.card E := by
        refine Finset.sum_le_sum fun q hq ↦ avg_candidate_le hrf others q ?_
        obtain ⟨hqc, hb⟩ := hCfin.mem_toFinset.mp hq
        rcases hp.2 q hqc hb with ⟨-, hr⟩ | ho
        · exact .inl hr
        · exact .inr ho
    _ = (hCfin.toFinset.card : ℝ≥0∞) * (((others.length + 3 : ℕ) : ℝ≥0∞) / Fintype.card E) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (listMax₀ μ R : ℝ≥0∞) * (((maxStackedClaims + 2 : ℕ) : ℝ≥0∞) / Fintype.card E) := by
        refine mul_le_mul' (by exact_mod_cast hCcard) (ENNReal.div_le_div_right ?_ _)
        exact_mod_cast (show others.length + 3 ≤ maxStackedClaims + 2 by omega)
    _ = _ := by
        rw [← mul_div_assoc]
        congr 1
        push_cast
        ring

/-- **Ring switching, then the stacked opening**: from `RingOpenPre`, the packed draw's group
within `2^-125` after the `13`-bit grind (`lambda_row`), then WHIR at the drawn `λ`
(`deployedStackedSpec`); an accepting return's trace is good. -/
noncomputable def ringOpenSpec {μ R : ℕ} (h : Whir.Admissible μ R) (S : Set (Column μ))
    (rings : List RingClaim) (hrf : RingFacts μ rings) (others : List StackClaim)
    (hJ : others.length + 1 ≤ maxStackedClaims) (hoth : ∀ c ∈ others, IsMultiaffine μ c.1)
    (Bad : Column μ → Prop) :
    Spec (ringSwitch rings >>= fun rb ↦ verifyStackedOpeningG μ R (rb.1 :: others) rb.2)
      (fun h ↦ RingOpenPre μ R S rings others Bad (commits h))
      (fun tr h ↦ traceGood (codesOf μ R) 0 (lvl0Pred μ Bad) tr (commits h)) εmsg 0 0 := by
  have hprog : (ringSwitch rings >>= fun rb ↦ verifyStackedOpeningG μ R (rb.1 :: others) rb.2) =
      (VerifierProgram.grindProofOfWork Whir.batchGrindingBits >>= fun _ ↦
        VerifierProgram.sampleChallengesPacked (ringChallengeCount rings + 1)) >>= fun ch ↦
          verifyStackedOpeningG μ R ((ringResult rings ch).1 :: others) (ringResult rings ch).2 := by
    rw [ringSwitch_eq]
    simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine Spec.congr hprog.symm ?_
  have hN := lambda_row h
  have hT : (2 : ℝ≥0∞)⁻¹ ^ Whir.batchGrindingBits *
      ((((maxStackedClaims + 2) * listMax₀ μ R : ℕ) : ℝ≥0∞) / Fintype.card E + 0) ≤ εmsg := by
    rw [add_zero]
    exact discount_le _ _ (by rw [← countBits_eq]; exact hN)
  have S1 := Spec.bind' (Post := fun _ h' ↦ ∃ h₀,
      RingOpenPre μ R S rings others Bad (commits h₀) ∧
        h' = h₀ ++ Spec.grindEvs Whir.batchGrindingBits)
    (Spec.grindP Whir.batchGrindingBits (fun h₀ hp ↦ ⟨h₀, hp, rfl⟩) hT) fun _ ↦
      Spec.samplePackedE (Post := fun ch h' ↦ StackedPre μ R (thr0Of μ R)
        ((ringResult rings ch).1 :: others) (ringResult rings ch).2 Bad (commits h'))
        (ringChallengeCount rings + 1) _ fun _ ⟨h₀, hp, he⟩ ↦ by
          subst he
          exact avg_ringOpen_le h hrf hJ h₀ hp
  refine Spec.bind' (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
      (by simp [Whir.batchGrindingBits]) le_rfl) fun ch ↦
    deployedStackedSpec h _ (fun c hc ↦ by
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [ringResult_eq]; exact hrf.multiaffine _
      · exact hoth c hc) _ Bad

/-! ## The stack's root -/

/-- A sequence equal to a return starts with a return. -/
theorem bind_eq_ret_iff {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β}
    (h : p.bind f = .ret b) : ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- **A return of a sequence** is a return of its first part followed by a return of the
second. -/
theorem after_bind_ret {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {l : List Ev} {b : β} (h : (p.bind f).after l = some (.ret b)) :
    ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (.ret a) ∧ (f a).after l₂ = some (.ret b) := by
  rcases VerifierProgram.after_bind_cases f h with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, rfl, h1, -, h3⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret_iff hr.symm
    exact ⟨a, l, [], by simp, hq, by simp [VerifierProgram.after, hfa]⟩
  · exact ⟨a, l₁, l₂, rfl, h1, h3⟩

/-- **The stack's root returns after exactly one commitment**, of the shape of the ladder's first
level. -/
theorem commitStack_after_ret {logN logInvRate : ℕ} {m : List Ev}
    (h : (commitStack logN logInvRate).after m = some (.ret ())) :
    ∃ level rest W, Whir.ladder logN logInvRate = some (level :: rest) ∧
      m = [Ev.commit (levelShape logN level (2 ^ level.fold)).1
        (levelShape logN level (2 ^ level.fold)).2 W] := by
  obtain ⟨cfg, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  rcases hc : Whir.ladder logN logInvRate with _ | c
  · rw [hc] at h1
    cases l₁ with
    | nil => simp [Verifier.liftOption, VerifierProgram.after] at h1
    | cons e es => cases e <;> simp [Verifier.liftOption, VerifierProgram.after] at h1
  · rw [hc] at h1
    obtain rfl : l₁ = [] := by
      cases l₁ with
      | nil => rfl
      | cons e es => cases e <;> simp [Verifier.liftOption, VerifierProgram.after] at h1
    simp only [Verifier.liftOption, VerifierProgram.after, Option.some.injEq,
        VerifierProgram.ret.injEq] at h1
    subst h1
    rcases c with _ | ⟨level, rest⟩
    · cases l₂ with
      | nil => simp [VerifierProgram.after] at h2
      | cons e es => cases e <;> simp [VerifierProgram.after] at h2
    · refine ⟨level, rest, ?_⟩
      cases l₂ with
      | nil => simp [VerifierProgram.after, VerifierProgram.readCommitment] at h2
      | cons e es =>
        cases e with
        | commit ht w W =>
          simp only [VerifierProgram.readCommitment, VerifierProgram.after] at h2
          split_ifs at h2 with hs
          · cases es with
            | nil => exact ⟨W, rfl, by simp [hs.1, hs.2]⟩
            | cons e' es' => cases e' <;> simp [VerifierProgram.after] at h2
        | _ => simp [VerifierProgram.after, VerifierProgram.readCommitment] at h2

/-- The stack's root, as `commitStack` reads it, has level 0's shape. -/
theorem shape_commitStack {μ R : ℕ} (h : Whir.Admissible μ R) {e : Ev}
    (hw : ∀ ht w W, e = Ev.commit ht w W → WellShaped w W)
    (ha : (commitStack μ R).after [e] = some (.ret ())) : ShapeOK₀ μ R (commits [e]) := by
  obtain ⟨level, rest, W, hc, he⟩ := commitStack_after_ret ha
  obtain ⟨level', rest', F⟩ := level0Facts (shapeOK_of_admissible h)
  have heq := F.hc
  rw [hc, Option.some.injEq, List.cons.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hfold := F.hℓ
  have hrate : level.logInvRate = R := by rw [F.hA.head.2, F.hR₀]
  obtain rfl : e = Ev.commit (levelShape μ level (2 ^ level.fold)).1
      (levelShape μ level (2 ^ level.fold)).2 W := by simpa using he
  refine ⟨rfl, W, ?_, ?_⟩
  · simp only [commits, List.getElem?_cons_zero, levelShape, hfold, hrate]
  · have := hw _ _ _ rfl
    rwa [levelShape, hfold] at this

/-! ## The interface -/

/-- **What the assembly takes of ring switching and the stacked opening.** -/
structure OpeningIface : Type where
  /-- Level 0's agreement threshold `A₀`. -/
  thr₀ : ℕ → ℕ → ℕ
  /-- Level 0's list bound. -/
  listMax₀ : ℕ → ℕ → ℕ
  /-- The commitments are exactly the stack's, of level 0's shape. -/
  ShapeOK₀ : ℕ → ℕ → List (ℕ × ℕ × Word) → Prop
  /-- The stack's word. -/
  word₀ : List (ℕ × ℕ × Word) → Word
  shape_word : ∀ {μ R cs}, ShapeOK₀ μ R cs → firstWordC cs = some (word₀ cs)
  /-- The stack's root, as `commitStack` reads it, has level 0's shape. -/
  shape_commitStack : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ {e : Ev},
    (∀ ht w W, e = Ev.commit ht w W → WellShaped w W) →
    (commitStack μ R).after [e] = some (.ret ()) → ShapeOK₀ μ R (commits [e])
  candidates_finite : ∀ {μ R : ℕ} (W : Word), Whir.Admissible μ R →
    (Candidates μ R (thr₀ μ R) W).Finite
  card_candidates_le : ∀ {μ R : ℕ} (W : Word), Whir.Admissible μ R →
    (Candidates μ R (thr₀ μ R) W).ncard ≤ listMax₀ μ R
  /-- The OOD row: `C(L₀, 2)·μ ≤ 2^(g + 3)`, `g = Whir.oodGrindingBits`. -/
  ood_row : ∀ {μ R : ℕ}, Whir.Admissible μ R →
    (listMax₀ μ R).choose 2 * μ ≤ 2 ^ (Whir.oodGrindingBits + 3)
  /-- **A good trace ends on a candidate that is not bad.** -/
  TraceGood : ∀ μ : ℕ, ℕ → (Column μ → Prop) → WhirTrace → List (ℕ × ℕ × Word) → Prop
  traceGood_cands : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (Bad : Column μ → Prop)
    (tr : WhirTrace) (cs : List (ℕ × ℕ × Word)), TraceGood μ R Bad tr cs →
    ∃ W, firstWordC cs = some W ∧ ∃ q ∈ Candidates μ R (thr₀ μ R) W, ¬ Bad q
  /-- **Ring switching and the stacked opening**: from every bad candidate failing a ring claim
  (then in `S`) or a claim of `others`, every group within `εmsg` after its grind, and an
  accepting return's trace good. -/
  stackedSpec : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (S : Set (Column μ))
    (rings : List RingClaim), RingFacts μ rings → ∀ (others : List StackClaim),
    others.length + 1 ≤ maxStackedClaims → (∀ c ∈ others, IsMultiaffine μ c.1) →
    ∀ Bad : Column μ → Prop,
    Spec (ringSwitch rings >>= fun rb ↦ verifyStackedOpeningG μ R (rb.1 :: others) rb.2)
      (fun h ↦ ShapeOK₀ μ R (commits h) ∧
        ∀ q ∈ Candidates μ R (thr₀ μ R) (word₀ (commits h)), Bad q →
          (q ∈ S ∧ ∃ rc ∈ rings, ¬ Relation.RingClaimHolds q rc) ∨
            ∃ c ∈ others, ¬ Relation.StackClaimHolds c q)
      (fun tr h ↦ TraceGood μ R Bad tr (commits h)) εmsg 0 0

/-- The stack's word is the first commitment's. -/
theorem shape_word {μ R : ℕ} {cs : List (ℕ × ℕ × Word)} (h : ShapeOK₀ μ R cs) :
    firstWordC cs = some (wordOf cs 0) := by
  obtain ⟨-, W, hW, -⟩ := h
  rw [firstWordC, wordOf, List.head?_eq_getElem?, hW]
  rfl

/-- **The deployed opening's interface.** -/
noncomputable def openingIface : OpeningIface where
  thr₀ := thr0Of
  listMax₀ := listMax₀
  ShapeOK₀ := ShapeOK₀
  word₀ cs := wordOf cs 0
  shape_word h := shape_word h
  shape_commitStack h := shape_commitStack h
  candidates_finite W h := (candidates_facts h W).1
  card_candidates_le W h := (candidates_facts h W).2
  ood_row h := countBits_eq Whir.oodGrindingBits ▸ ood_row h
  TraceGood μ R Bad tr cs := traceGood (codesOf μ R) 0 (lvl0Pred μ Bad) tr cs
  traceGood_cands h Bad tr cs hg := by
    obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil (traceGood_ne_nil _ cs tr 0 _ hg)
    exact ⟨wordOf (c :: rest) 0, rfl, traceGood_cands h Bad tr _ hg⟩
  stackedSpec h S rings hrf others hJ hoth Bad := ringOpenSpec h S rings hrf others hJ hoth Bad

end
end LeanVM.Protocol.Whir.Params
