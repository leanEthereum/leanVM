/-
  LeanVM.Protocol.Whir.Sound.Folds

  The specification of a WHIR level's fold rounds: the invariant `A(i, j)` (every member of the
  list of the level's oracle folded by its first `j` challenges violates the running claim) is
  kept by each round except at `2·L + 2^(ℓ−j)·E_mca` challenges.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Whir.Sound.Generic

/-!
# The fold rounds

`foldRounds b ℓ s []` (`LeanVM.Protocol.Verifier.foldRounds`, `verify_whir`'s inner loop,
`crates/verifier/src/whir.rs:183-194`) checks a proof of work of `b` bits unless `b = 0`, samples
a challenge `c`, moves the running claim to `q(c)` and reads the next round polynomial.

`FoldInv` is the doom of the design note's `A(i, j)`, together with the bookkeeping the step needs:
the state has `pre + j` folds, `j ≤ ℓ`, the level's code has `κ = μ − pre − ℓ` message variables,
the glued claims are well formed (`GluedOK`), the round polynomial sums to the target
(`QuadOK`), and every member of the list of the level's oracle `laneO i cs` folded by the level's
`j` challenges (`foldsN lf`, `ℓ − j` lanes left) violates the running claim
`(runW w ℓ₀ s, s.target)`.

* `card_foldBad_le_eFold`: one round's escape count, `2·listMax + 2^(ℓ−j−1)·mcaMax`
  (`card_foldStep_bad_le`), at most `eFold P ℓ · |E|`.
* `foldRoundsSpec`: the rounds keep `FoldInv` with lead `foldLead b (eFold P ℓ)` (the first
  round's escape, or `0` when a proof of work of `b` bits precedes each challenge and discounts
  it), and return in `FoldInv` with all `ℓ` challenges.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

@[expose] public section

/-- The fold rounds' escape bound at a level with `ℓ` folds:
`(2·listMax + 2^(ℓ−1)·mcaMax) / |E|`. -/
noncomputable def eFold (P : LevelCode) (ℓ : ℕ) : ENNReal :=
  ((2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax : ℕ) : ENNReal) / Fintype.card E

section

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ)

/-- **The fold invariant `A(i, j)`** after the challenges `lf` of level `i`. -/
def FoldInv (s : WhirStateT) (lf : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length ≤ ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    QuadOK s.quad s.target ∧
    Viol P (rowsOf (ℓ - lf.length) (foldsN lf (laneO i cs P.n))) (runW w ℓ₀ s) s.target

/-- The doom right after a fold challenge, before the next round polynomial. -/
def FoldMid (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length < ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    Viol P (rowsOf (ℓ - (lf.length + 1)) (foldsN (lf ++ [c]) (laneO i cs P.n)))
      (fun r ↦ runW w ℓ₀ s (c :: r)) (polyEval s.quad c)

variable {μ ℓ₀ w i P ℓ pre}

open Classical in
/-- One round's escape: at most `2·listMax + 2^(ℓ−1)·mcaMax` challenges break the invariant. -/
theorem card_foldBad_le_eFold (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInv μ ℓ₀ w i P ℓ pre s lf cs) :
    (univ.filter fun c ↦ ¬ FoldMid μ ℓ₀ w i P ℓ pre s lf c cs).card ≤
      2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax := by
  obtain ⟨hlen, -, hκ, hg, ⟨c₀, c₁, c₂, hq, hσ⟩, hviol⟩ := hI
  set m := ℓ - (lf.length + 1) with hm
  have hm1 : ℓ - lf.length = m + 1 := by omega
  have hma : IsMultiaffine (m + 1 + P.κ) (runW w ℓ₀ s) := by
    have := isMultiaffine_runW hw hℓ₀ s (by omega) hg
    rwa [show μ - s.folds.length = m + 1 + P.κ by omega] at this
  rw [hm1] at hviol
  rw [hq] at hσ
  have hstep := card_foldStep_bad_le P (runW w ℓ₀ s) hma (foldsN lf (laneO i cs P.n)) s.target
    c₀ c₁ c₂ hσ hviol
  refine (Finset.card_le_card fun c hc ↦ ?_).trans (hstep.trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, FoldMid, not_and] at hc ⊢
    intro hv
    refine hc hlen hlf hκ hg ?_
    rw [hq]
    rwa [foldsN, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (by omega))) _

open Classical in
/-- The escape count as the calculus averages it. -/
theorem avg_foldBad_le (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInv μ ℓ₀ w i P ℓ pre s lf cs) :
    (Fintype.card E : ENNReal)⁻¹ *
      ((univ.filter fun c ↦ ¬ FoldMid μ ℓ₀ w i P ℓ pre s lf c cs).card : ENNReal) ≤
        eFold P ℓ := by
  rw [eFold, ENNReal.div_eq_inv_mul]
  gcongr
  exact_mod_cast card_foldBad_le_eFold hw hℓ₀ s lf hlf cs hI

/-- After the round polynomial: the invariant with one more challenge. -/
theorem foldInv_step (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word))
    (quad : List E) (hmid : FoldMid μ ℓ₀ w i P ℓ pre s lf c cs)
    (hq : QuadOK quad (polyEval s.quad c)) :
    FoldInv μ ℓ₀ w i P ℓ pre
      { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
      (lf ++ [c]) cs := by
  obtain ⟨hlen, hlf, hκ, hg, hviol⟩ := hmid
  refine ⟨by simp [hlen]; omega, by simp; omega, hκ, fun g hgm ↦ ?_, hq, ?_⟩
  · obtain ⟨h1, h2⟩ := hg g hgm
    exact ⟨by simp; omega, h2⟩
  · have hfun := funext (runW_fold w ℓ₀ s c (polyEval s.quad c) quad
      fun g hgm ↦ (hg g hgm).1)
    rw [hfun, List.length_append, List.length_singleton]
    exact hviol

variable (μ ℓ₀ w i P ℓ pre)

/-- The fold rounds' lead: a fold challenge's escape `x` when the level grinds nothing before it,
and `0`, a proof of work's, when it does. -/
def foldLead (b : ℕ) (x : ENNReal) : ENNReal := if b = 0 then x else 0

omit μ ℓ₀ w i P ℓ pre in
/-- The lead is at most `εmax` once the discounted escape is. -/
theorem foldLead_le {b : ℕ} {x εmax : ENNReal} (h : (2 : ENNReal)⁻¹ ^ b * x ≤ εmax) :
    foldLead b x ≤ εmax := by
  unfold foldLead
  split
  · subst b; simpa using h
  · exact zero_le

/-- **The fold rounds' specification**: from `FoldInv` with `n` rounds left (and an extra
invariant `X` of the commitments, which the rounds do not touch), the rounds keep the invariant
(each challenge escaping at most `eFold P ℓ`, discounted by the `b` bits ground before it) and
return it with all `ℓ` challenges. -/
noncomputable def foldRoundsSpec {εmax : ENNReal} (X : CInv) (b : ℕ) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (hε : (2 : ENNReal)⁻¹ ^ b * eFold P ℓ ≤ εmax) :
    (n : ℕ) → (s : WhirStateT) → (lf : List E) →
      Spec (foldRoundsT b n s lf)
        (fun h ↦ (FoldInv μ ℓ₀ w i P ℓ pre s lf (commits h) ∧ X (commits h)) ∧
          lf.length + n = ℓ)
        (fun r h ↦ (FoldInv μ ℓ₀ w i P ℓ pre r.1 r.2 (commits h) ∧ X (commits h)) ∧
          r.2.length = ℓ)
        εmax (foldLead b (eFold P ℓ)) 0
  | 0, s, lf => (Spec.ret (s, lf)).mono (fun _ h ↦ ⟨h.1, by simpa using h.2⟩)
      (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | n + 1, s, lf =>
    ((foldPowInv (T := eFold P ℓ) (fun cs ↦ (FoldInv μ ℓ₀ w i P ℓ pre s lf cs ∧ X cs) ∧
          lf.length + (n + 1) = ℓ) b hε).bind' fun _ ↦
    ((Spec.sampleE (Pre := fun h ↦ (FoldInv μ ℓ₀ w i P ℓ pre s lf (commits h) ∧ X (commits h)) ∧
          lf.length + (n + 1) = ℓ)
        (Post := fun c h ↦ (FoldMid μ ℓ₀ w i P ℓ pre s lf c (commits h) ∧ X (commits h)) ∧
          lf.length + (n + 1) = ℓ) (εmax := εmax) (T := 0) (eFold P ℓ) fun h₀ hp ↦ by
        refine le_trans ?_ (avg_foldBad_le hw hℓ₀ s lf (by omega) (commits h₀) hp.1.1)
        gcongr with c
        intro hm
        simp only [commits_sample]
        exact ⟨⟨hm, hp.1.2⟩, hp.2⟩).bind' fun c ↦
      (roundPolyInv (fun cs ↦ (FoldMid μ ℓ₀ w i P ℓ pre s lf c cs ∧ X cs) ∧
          lf.length + (n + 1) = ℓ) (polyEval s.quad c) (T := foldLead b (eFold P ℓ))
          (foldLead_le hε)).bind' fun quad ↦
        (foldRoundsSpec X b hw hℓ₀ hε n
          { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
          (lf ++ [c])).mono
          (fun h hp ↦ ⟨⟨foldInv_step s lf c (commits h) quad hp.2.1.1 hp.1, hp.2.1.2⟩, by
            simp; omega⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
end

end
end LeanVM.Protocol.Whir.Sound
