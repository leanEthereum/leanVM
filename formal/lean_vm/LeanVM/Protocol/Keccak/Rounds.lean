/-
  LeanVM.Protocol.Keccak.Rounds

  Sumcheck rounds of the verifier program as specifications over doom "no candidate is alive":
  the round polynomial's reads, Schwartz–Zippel for its challenge, the plain rounds
  (`sumcheck … none`) and the equality-mode rounds of `keccakPackRounds`.
-/

module

public import LeanVM.Protocol.Keccak.Multilinear
public import LeanVM.Protocol.EndToEnd.Front.FlockMech

/-!
# Sumcheck rounds as specifications

A sumcheck is stated for a family `F q acc` of claims, one per candidate `q` and per list `acc`
of challenges drawn so far: the running claim should be `F q acc`. The family is a valid
sumcheck family when, for each `acc`, `x ↦ F q (acc ++ [x])` is a polynomial of degree `d`
(`PolyLE`) and splits `F q acc` as the round's check reads it.

* `sz_escape`: two distinct polynomials of degree `d` agree at `d` points at most:
  `avgE [p(c) = q(c)] ≤ d/|E|` (`errE d`).
* `roundSpec`: the reads of `sumcheckRoundPoly` keep doom and return a message that passes
  the round's check (`RoundSplit`, by construction: the derived coefficient).
* `sumcheckSpec` (plain rounds, `crates/verifier/src/transcript.rs:219-233`): from doom of
  `claim = F q acc`, to doom
  of `final = F q (acc ++ point)`; each challenge escapes at `L₀ · d/|E|`.
* `packSpec` (`keccakPackRounds`, `crates/verifier/src/keccak.rs:152-161`): the equality-mode
  rounds, the value
  scaled by `1 + r + c` each round: from doom of `value = scale · F q acc` to doom of
  `value' = scale' · F q (acc ++ point)`; each challenge escapes at `L₀ · (d + 1)/|E|`, the
  scale `1 + r + c` adding a root.

A candidate alive after a round's message is one whose message is its true round polynomial;
the check then makes the claim before the message true, which is the contrapositive the reads
need.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Polynomial
open scoped ENNReal

@[expose] public section

/-! ## Schwartz–Zippel -/

/-- The error of a degree-`d` check: `d/|E|`. -/
noncomputable def errE (d : ℕ) : ℝ≥0∞ := d * (Fintype.card E : ℝ≥0∞)⁻¹

theorem errE_mono {d d' : ℕ} (h : d ≤ d') : errE d ≤ errE d' := by
  unfold errE; gcongr

/-- **Schwartz–Zippel** in one variable: distinct polynomials of degree `d` agree at a fraction
`d/|E|` of the points at most. -/
theorem sz_escape {p q : E[X]} (hne : p ≠ q) {d : ℕ} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    avgE (fun c ↦ indE (p.eval c = q.eval c)) ≤ errE d := by
  classical
  rw [← card_filter_eq_avgE, errE, mul_comm]
  gcongr
  have hsub : p - q ≠ 0 := sub_ne_zero.2 hne
  have hdeg : (p - q).natDegree ≤ d := (natDegree_sub_le p q).trans (max_le hp hq)
  have hcard : (Finset.univ.filter fun c ↦ p.eval c = q.eval c).card ≤ (p - q).natDegree := by
    refine card_le_degree_of_subset_roots fun z hz ↦ ?_
    rw [mem_roots hsub, IsRoot, eval_sub, sub_eq_zero]
    exact (Finset.mem_filter.1 hz).2
  exact_mod_cast hcard.trans hdeg

/-- A message as a polynomial. -/
noncomputable def listPoly (l : List E) : E[X] :=
  ∑ c ∈ Finset.range l.length, C (l.getD c 0) * X ^ c

theorem eval_listPoly (l : List E) (x : E) : (listPoly l).eval x = polyEval l x := by
  rw [polyEval_eq_sum, listPoly, eval_finsetSum]
  simp

theorem natDegree_listPoly (l : List E) : (listPoly l).natDegree ≤ l.length - 1 := by
  unfold listPoly
  refine natDegree_sum_le_of_forall_le _ _ fun c hc ↦ ?_
  have := Finset.mem_range.1 hc
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- A message that agrees with a polynomial of degree at most `d` at every point, and the
escape of its challenge when it does not. -/
theorem msg_escape {msg : List E} {d : ℕ} (hd : msg.length - 1 ≤ d) {f : E → E}
    (hf : PolyLE d f) (hne : ¬ ∀ x, polyEval msg x = f x) (g : E → E) {k : ℕ} (hg : PolyLE k g)
    (hg0 : ∃ x, g x ≠ 0) :
    avgE (fun c ↦ indE (g c * polyEval msg c = g c * f c)) ≤ errE (d + k) := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hg0
    exact hx (by simp [hgQ])
  have hne' : listPoly msg ≠ P := by
    rintro h
    exact hne fun x ↦ by rw [← eval_listPoly, h, hfP]
  have hne'' : Q * listPoly msg ≠ Q * P := fun h ↦ hne' (mul_left_cancel₀ hQ0 h)
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans (sz_escape hne'' (d := d + k) ?_ ?_)
  · rw [eval_mul, eval_mul, eval_listPoly, ← hgQ, ← hfP]; exact hc
  · exact (natDegree_mul_le).trans (by have := natDegree_listPoly msg; omega)
  · exact (natDegree_mul_le).trans (by omega)

/-! ## The round polynomial's reads -/

variable {β : Type} {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-- `n` reads keep doom; lead `T` (the reads' own lead is `0` when `n > 0`). -/
noncomputable def readNSpec (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (VerifierProgram.readScalars n) (Doomed C A) (fun xs h ↦ xs.length = n ∧ Doomed C A h) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ Doomed C A h) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => (doomReadN hst A hT n).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

theorem split_none (c0 claim : E) (tail : List E) :
    RoundSplit none claim (polyEval (c0 :: (claim + sumE tail) :: tail) 0)
      (polyEval (c0 :: (claim + sumE tail) :: tail) 1) := by
  rw [RoundSplit, polyEval_zero_cons, polyEval_one, sumE_eq_sum]
  simp only [List.sum_cons]
  linear_combination (CharTwo.two_eq_zero (R := E)) * (c0 + tail.sum)

theorem split_some (r claim : E) (tail : List E) :
    RoundSplit (some r) claim (polyEval ((claim + r * sumE tail) :: tail) 0)
      (polyEval ((claim + r * sumE tail) :: tail) 1) := by
  rw [RoundSplit, polyEval_zero_cons, polyEval_one, sumE_eq_sum]
  simp only [List.sum_cons]
  linear_combination (CharTwo.two_eq_zero (R := E)) * (r * claim + r * r * tail.sum + r * tail.sum)

/-- A grind adds no commitment. -/
theorem commits_grindEvs (b : ℕ) : commits (Spec.grindEvs b) = [] := by
  unfold Spec.grindEvs
  split <;> rfl

/-- **A grind keeps doom**, and what else the history carries; the lead is the follower's at
zero bits, `0` otherwise. -/
noncomputable def doomGrind (hst : Stable C) (A : β → Prop) (Q : Prop) (b : ℕ) (hT : T ≤ εmax) :
    Spec (VerifierProgram.grindProofOfWork b) (fun h ↦ Q ∧ Doomed C A h)
      (fun _ h ↦ Q ∧ Doomed C A h) εmax (if b = 0 then T else 0) T :=
  Spec.grindP b (fun h₀ hp ↦ ⟨hp.1, (Doomed.append hst (commits_grindEvs b)).mpr hp.2⟩)
    (le_trans (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (by norm_num))) hT)

theorem grindLead_le' (b : ℕ) (hT : T ≤ εmax) : (if b = 0 then T else 0) ≤ εmax := by
  split
  · exact hT
  · exact zero_le

/-- **A round's message**: the reads keep doom, and the message the program builds passes the
round's check; the grind for the round's degree that follows (zero bits at every round the
verifier runs) keeps it. Lead `0`. -/
noncomputable def roundSpec (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) (count : ℕ)
    (hc : 2 ≤ count) (claim : E) (mode : Option E) :
    Spec (sumcheckRoundPoly count claim mode) (Doomed C A)
      (fun msg h ↦ msg.length = count ∧
        RoundSplit mode claim (polyEval msg 0) (polyEval msg 1) ∧ Doomed C A h) εmax 0 T :=
  match mode with
  | none =>
    (doomRead hst A (grindLead_le' _ hT)).bind' fun c0 ↦
      (readNSpec hst A (grindLead_le' _ hT) (count - 2)).bind' fun tail ↦
      (doomGrind hst A (tail.length = count - 2) (grindingBits (count - 1)) hT).bind' fun _ ↦
      (Spec.ret (c0 :: (claim + sumE tail) :: tail)).mono
        (fun _ h ↦ ⟨by simp [h.1]; omega, split_none c0 claim tail, h.2⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl
  | some r =>
    Spec.congr (p := VerifierProgram.readScalars (count - 2 + 1) >>= fun tail ↦
        VerifierProgram.grindProofOfWork (grindingBits (count - 1 + 1)) >>= fun _ ↦
        VerifierProgram.ret ((claim + r * sumE tail) :: tail)) (by
          simp only [sumcheckRoundPoly, show count - 2 + 1 = count - 1 by omega]; rfl) <|
      (doomReadN hst A (grindLead_le' _ hT) (count - 2)).bind' fun tail ↦
      (doomGrind hst A (tail.length = count - 2 + 1) (grindingBits (count - 1 + 1)) hT).bind'
        fun _ ↦
        (Spec.ret ((claim + r * sumE tail) :: tail)).mono
          (fun _ h ↦ ⟨by simp [h.1]; omega, split_some r claim tail, h.2⟩) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl

/-! ## Plain rounds -/

/-- A family of plain sumcheck claims, valid below `N` challenges: in each round the next claim
is a polynomial of degree `d` in the challenge, and its values at `0` and `1` add to the
current one. -/
def PlainFamily (F : β → List E → E) (d N : ℕ) : Prop :=
  ∀ q acc, acc.length < N →
    PolyLE d (fun x ↦ F q (acc ++ [x])) ∧ F q acc = F q (acc ++ [0]) + F q (acc ++ [1])

/-- The escape of a plain round's challenge. -/
theorem plain_escape {F : β → List E → E} {d N : ℕ} (hF : PlainFamily F d N) (R : β → Prop)
    {acc msg : List E} (hacc : acc.length < N) (hd : msg.length - 1 ≤ d) (q : β)
    (hq : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE (polyEval msg c = F q (acc ++ [c]) ∧ R q)) ≤ errE d := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEval msg x = F q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
      (msg_escape hd (hF q acc hacc).1 hne (fun _ ↦ 1) (PolyLE.const 0 1) ⟨0, one_ne_zero⟩)
    simp only [one_mul]
    exact hc.1
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

variable [Finite β] {L₀ : ℕ}

/-- **Plain sumcheck rounds** as a specification: from doom of `claim = F q acc` to doom of
`final = F q (acc ++ point)`, each challenge escaping at `L₀ · d/|E|`. Lead `T` (`0` when a
round is left, the follower's otherwise). -/
noncomputable def sumcheckSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) {F : β → List E → E} {d N : ℕ} (hF : PlainFamily F d N) {count : ℕ}
    (hc : 2 ≤ count) (hcd : count - 1 ≤ d) (hT : T ≤ εmax)
    (he : (L₀ : ℝ≥0∞) * errE d + T ≤ εmax) :
    (n : ℕ) → (acc : List E) → (claim : E) → acc.length + n ≤ N →
      Spec (sumcheck claim count (List.replicate n none))
        (Doomed C (fun q ↦ claim = F q acc ∧ R q))
        (fun res h ↦ res.1.length = n ∧ Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ R q) h)
        εmax T T
  | 0, acc, claim, _ =>
    (Spec.ret (Post := fun (res : List E × E) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ R q) h) ([], claim)).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, acc, claim, hN => by
    refine ((roundSpec (T := (L₀ : ℝ≥0∞) * errE d + T) hst _ he count hc claim none).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomSample (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEval msg x = F q (acc ++ [x])) ∧ R q)
        (fun c q ↦ polyEval msg c = F q (acc ++ [c]) ∧ R q) (errE d)
        (fun q hq ↦ plain_escape hF R (by omega) (by omega) q hq)).mono
          (fun h (hh : msg.length = count ∧
              RoundSplit none claim (polyEval msg 0) (polyEval msg 1) ∧
              Doomed C (fun q ↦ claim = F q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplit, hall, hall] at hs
              rw [← hs]
              exact (hF q acc (by omega)).2.symm, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      · refine (sumcheckSpec hst hcard R hF hc hcd hT he n (acc ++ [c]) (polyEval msg c)
          (by simp; omega)).bind' fun res ↦ ?_
        exact (Spec.ret (c :: res.1, res.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## Equality-mode rounds (`keccakPackRounds`) -/

/-- A family of equality-mode claims at the point `r`: the next claim is a polynomial of degree
`d` in the challenge, and the claim is its `(1 + r_k)·F(0) + r_k·F(1)`. -/
def EqFamily (F : β → List E → E) (r : List E) (d : ℕ) : Prop :=
  ∀ q acc, (h : acc.length < r.length) →
    PolyLE d (fun x ↦ F q (acc ++ [x])) ∧
      F q acc = (1 + r[acc.length]) * F q (acc ++ [0]) + r[acc.length] * F q (acc ++ [1])

omit [Finite β] in
/-- The escape of an equality-mode round's challenge: the value `(1 + r + c)·msg(c)` against
`(1 + r + c)·scale·F(acc ++ [c])`, a polynomial identity of degree `d + 1`. -/
theorem eq_escape {F : β → List E → E} {r : List E} {d : ℕ} (hF : EqFamily F r d) (R : β → Prop)
    {acc msg : List E} (hacc : acc.length < r.length) (hd : msg.length - 1 ≤ d) (scale : E)
    (q : β) (hq : ¬ ((∀ x, polyEval msg x = scale * F q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE ((1 + r[acc.length] + c) * polyEval msg c =
      (scale * (1 + r[acc.length] + c)) * F q (acc ++ [c]) ∧ R q)) ≤ errE (d + 1) := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEval msg x = scale * F q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
      (msg_escape hd (PolyLE.const_mul (hF q acc hacc).1 scale) hne
        (fun c ↦ 1 + r[acc.length] + c) ((PolyLE.affine (1 + r[acc.length]) 1).congr
          fun x ↦ by ring) ⟨r[acc.length], by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]; exact one_ne_zero⟩)
    rw [hc.1]; ring
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

/-- **The equality-mode rounds** of `keccakPackRounds` at the point `r`, from the challenges
`acc` drawn (`rs = r.drop acc.length` left): from doom of `value = scale · F q acc` to doom of
`value' = scale' · F q (acc ++ point)`, each challenge escaping at `L₀ · (d + 1)/|E|`. Lead `0`
when a round is left. -/
noncomputable def packSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) {F : β → List E → E} {r : List E} {d : ℕ} (hF : EqFamily F r d)
    (hd : 2 ≤ d) (hT : T ≤ εmax) (he : (L₀ : ℝ≥0∞) * errE (d + 1) + T ≤ εmax) :
    (rs : List E) → (acc : List E) → (value scale : E) → rs = r.drop acc.length →
      Spec (keccakPackRounds rs value scale)
        (Doomed C (fun q ↦ value = scale * F q acc ∧ R q))
        (fun res h ↦ res.2.2.length = rs.length ∧
          Doomed C (fun q ↦ res.1 = res.2.1 * F q (acc ++ res.2.2) ∧ R q) h)
        εmax T T
  | [], acc, value, scale, _ =>
    (Spec.ret (Post := fun (res : E × E × List E) h ↦ res.2.2.length = 0 ∧
        Doomed C (fun q ↦ res.1 = res.2.1 * F q (acc ++ res.2.2) ∧ R q) h)
      (value, scale, [])).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | rk :: rs, acc, value, scale, hrs => by
    have hlt : acc.length < r.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hrs
      exact List.cons_ne_nil _ _ hrs
    have hrk : r[acc.length] = rk := by
      have := congrArg List.head? hrs
      rw [List.head?_drop, List.getElem?_eq_getElem hlt] at this
      simpa using this.symm
    refine ((roundSpec (T := (L₀ : ℝ≥0∞) * errE (d + 1) + T) hst _ he 3 (by norm_num) value
      (some rk)).mono (fun _ h ↦ h) (fun msg h (hm : msg.length = 3 ∧ _ ∧ _) ↦ hm) le_rfl
      zero_le le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = 3
    · refine ((doomSample (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEval msg x = scale * F q (acc ++ [x])) ∧ R q)
        (fun c q ↦ (1 + r[acc.length] + c) * polyEval msg c =
          (scale * (1 + r[acc.length] + c)) * F q (acc ++ [c]) ∧ R q) (errE (d + 1))
        (fun q hq ↦ eq_escape hF R hlt (by omega) scale q hq)).mono
          (fun h (hh : msg.length = 3 ∧
              RoundSplit (some rk) value (polyEval msg 0) (polyEval msg 1) ∧
              Doomed C (fun q ↦ value = scale * F q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplit, hall, hall, ← hrk] at hs
              rw [← hs, (hF q acc hlt).2]
              ring, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      · refine (packSpec hst hcard R hF hd hT he rs (acc ++ [c])
          ((1 + rk + c) * polyEval msg c) (scale * (1 + rk + c)) ?_).mono
          (fun _ h ↦ by rw [hrk] at h; exact h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
          |>.bind' fun res ↦ ?_
        · rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
          rfl
        · exact (Spec.ret (res.1, res.2.1, c :: res.2.2)).mono
            (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.KeccakGkr
