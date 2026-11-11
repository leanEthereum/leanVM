/-
  LeanVM.Protocol.Whir.Sound.Folds

  The specification of a WHIR level's affine fold rounds: the invariant (every tuple close to the
  level's oracle folded by its rounds so far violates the running claim) is kept by each round,
  the challenges `(α, β)` escaping at most `N / |E|²` after their grind.
-/

module

public import LeanVM.Protocol.Whir.Sound.Generic
public import LeanVM.Protocol.Whir.Sound.Code
public import LeanVM.Protocol.Whir.Sound.Group

/-!
# The fold rounds

`foldRounds ℓ s` (`LeanVM.Protocol.Verifier.foldRounds`, `crates/verifier/src/whir.rs:232-241`)
runs the level's affine fold rounds (`foldRound`): four scalars, a grind and `(α, β)`, the claim
folded at `α` (`foldClaim`).

* `RoundInv`: the doom of Annex B's round-by-round argument after `j` rounds of level `i`
  (`thm:rbr`, "after the batching challenge and after each fold message"): the state has
  `pre + j` `α`s, the level's code has `κ = μ − pre − ℓ`, the glued claims are well formed, and
  every tuple of degree at most the level's `d` agreeing with the oracle of commitment `i` folded
  by the level's `j` rounds (`foldsA`, `ℓ − j` lane variables left) on at least `A_j` columns
  violates the running claim `(runW w ℓ₀ s, s.claim)`.
* `RoundBounds P εmax`: the fold-round lemma at each round of the level with its escape count
  `N j`, within `εmax` after the `8`-bit grind.
* `foldRoundSpec`, `foldRoundsSpec`: the rounds keep `RoundInv` and return in it with all `ℓ`
  rounds, the commitments' extra invariant `X` untouched.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

@[expose] public section

/-! ## Two challenges -/

/-- Two challenges and a value of them. -/
def pairP {β : Type} (F : E → E → β) : VerifierProgram β :=
  sampleChallenge >>= fun α ↦ sampleChallenge >>= fun b ↦ VerifierProgram.ret (F α b)

theorem noMoves_pairP {β : Type} (F : E → E → β) : NoMoves (pairP F) :=
  noMoves_sampleE.bind fun _ ↦ noMoves_sampleE.bind fun _ ↦ NoMoves.ret _

open Classical in
/-- **Two challenges' escape**: the fraction of pairs whose value breaks a predicate of the
commitments. -/
theorem escRet_pairP {β : Type} (F : E → E → β) (Q : β → List (ℕ × ℕ × Word) → Prop)
    (h₀ : List Ev) :
    escRet (fun a h ↦ Q a (commits h)) h₀ [] (pairP F) =
      (Fintype.card E : ENNReal)⁻¹ ^ 2 *
        ((univ.filter fun t : E × E ↦ ¬ Q (F t.1 t.2) (commits h₀)).card : ENNReal) := by
  unfold escRet
  have hc := retExp_commits (fun a cs ↦ if Q a cs then (0 : ENNReal) else 1) (pairP F) h₀ []
  rw [hc, List.append_nil]
  unfold pairP
  simp only [bind_eq]
  rw [retExp_bind, retExp_sampleE]
  simp only [retExp_bind, retExp_sampleE, retExp, ← Finset.mul_sum]
  rw [← Finset.sum_boole, ← mul_assoc, ← pow_two]
  congr 1
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  split_ifs <;> simp_all

/-! ## The invariant -/

section

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (pre : ℕ)

/-- **The fold invariant** after the rounds `rounds` of level `i`. -/
def RoundInv (s : WhirState) (rounds : List FoldRound) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.alphas.length = pre + rounds.length ∧ rounds.length ≤ P.ℓ ∧ P.κ + pre + P.ℓ = μ ∧
    GluedOK μ s ∧
    TViol P.κ P.dom (rowsOf (P.ℓ - rounds.length) (foldsA P.dom rounds (laneO i cs P.n)))
      (runW w ℓ₀ s) s.claim (P.thr rounds.length) P.deg

end

/-- **The fold-round lemma at every round of a level**, with its escape counts within `εmax`
after the `8`-bit grinds. -/
structure RoundBounds (P : LevelCode) (εmax : ENNReal) where
  /-- The escape count of `(α, β)` of round `j + 1`. -/
  N : ℕ → ℕ
  /-- The last round's threshold exceeds the folds. -/
  hA : P.ℓ < P.A
  /-- The fold-round lemma. -/
  bound : ∀ j < P.ℓ, FoldRoundBound P.dom P.deg (P.thr (j + 1)) (N j)
  /-- The escape of `(α, β)` after its grind. -/
  eF : ∀ j < P.ℓ, (2 : ENNReal)⁻¹ ^ Whir.foldGrindingBits *
    ((N j : ENNReal) / Fintype.card E ^ 2) ≤ εmax
  /-- The escape of `(α, β)` is below one. -/
  eF1 : ∀ j < P.ℓ, (N j : ENNReal) / Fintype.card E ^ 2 < 1

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {pre : ℕ}

theorem tviol_rowsOf_congr {n m m' κ : ℕ} {dom : Fin n ↪ E} {O : ℕ → Fin n → E}
    {Φ : List E → E} {σ : E} {a d : ℕ} (h : m = m') :
    TViol κ dom (rowsOf m O) Φ σ a d ↔ TViol κ dom (rowsOf m' O) Φ σ a d := by
  subst h; rfl

open Classical in
/-- **A round's escapes**: from the invariant, every table leaves at most `N` pairs `(α, β)`
after which the invariant fails with one more round. -/
theorem card_foldEsc_round_le (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) {N : ℕ} (s : WhirState)
    (rounds : List FoldRound) (hj : rounds.length < P.ℓ) (cs : List (ℕ × ℕ × Word))
    (hB : FoldRoundBound P.dom P.deg (P.thr (rounds.length + 1)) N)
    (hI : RoundInv μ ℓ₀ w i P pre s rounds cs) (u₀ w₁ c₀ c₁ : E) :
    (foldEsc P.κ P.dom (rowsOf (P.ℓ - (rounds.length + 1) + 1)
      (foldsA P.dom rounds (laneO i cs P.n))) (runW w ℓ₀ s) s.claim
      (P.thr (rounds.length + 1)) P.deg u₀ w₁ c₀ c₁).card ≤ N := by
  obtain ⟨hlen, -, hκ, hg, hv⟩ := hI
  set m := P.ℓ - (rounds.length + 1) with hm
  have hma : IsMultiaffine (m + 1 + P.κ) (runW w ℓ₀ s) := by
    have := isMultiaffine_runW hw hℓ₀ s (by omega) hg
    rwa [show μ - s.alphas.length = m + 1 + P.κ by omega] at this
  have hv' : TViol P.κ P.dom (rowsOf (m + 1) (foldsA P.dom rounds (laneO i cs P.n)))
      (runW w ℓ₀ s) s.claim (P.thr (rounds.length + 1) - 1) P.deg := by
    have ha : P.thr (rounds.length + 1) - 1 = P.thr rounds.length := by
      simp only [LevelCode.thr]; omega
    rw [ha, ← tviol_rowsOf_congr (show P.ℓ - rounds.length = m + 1 by omega)]
    exact hv
  exact card_foldEsc_le P.κ P.dom _ _ s.claim _ _ hB hma hv' u₀ w₁ c₀ c₁

/-! ## The rounds -/

/-- The state and the round after a round's challenges. -/
def roundOut (s : WhirState) (u₀ w₁ c₀ c₁ α b : E) : WhirState × FoldRound :=
  ({ s with claim := foldClaim s.claim α b u₀ w₁ c₀ c₁, alphas := s.alphas ++ [α] },
    ⟨α, b⟩)

/-- `foldRound` as the moves the specification composes. -/
theorem foldRound_eq (s : WhirState) :
    foldRound s = readScalar >>= fun u₀ ↦ readScalar >>= fun w₁ ↦
      readScalar >>= fun c₀ ↦ readScalar >>= fun c₁ ↦
      grindProofOfWork Whir.foldGrindingBits >>= fun _ ↦
      pairP fun α b ↦ roundOut s u₀ w₁ c₀ c₁ α b :=
  rfl

/-- After an escaping-free pair, the invariant with one more round. -/
theorem roundInv_step (s : WhirState) (rounds : List FoldRound) (u₀ w₁ c₀ c₁ α b : E)
    (t : E × E) (cs : List (ℕ × ℕ × Word)) (hlen : s.alphas.length = pre + rounds.length)
    (hj : rounds.length < P.ℓ) (hκ : P.κ + pre + P.ℓ = μ) (hg : GluedOK μ s)
    (hT : t ∉ foldEsc P.κ P.dom (rowsOf (P.ℓ - (rounds.length + 1) + 1)
      (foldsA P.dom rounds (laneO i cs P.n))) (runW w ℓ₀ s) s.claim
      (P.thr (rounds.length + 1)) P.deg u₀ w₁ c₀ c₁)
    (ht : t = (α, b)) :
    RoundInv μ ℓ₀ w i P pre (roundOut s u₀ w₁ c₀ c₁ α b).1
      (rounds ++ [(roundOut s u₀ w₁ c₀ c₁ α b).2]) cs := by
  subst ht
  simp only [foldEsc, mem_filter, mem_univ, true_and, not_not] at hT
  refine ⟨by simp [roundOut, hlen]; omega, by simp; omega, hκ, fun g hgm ↦ ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hg g hgm
    exact ⟨by simp [roundOut]; omega, h2⟩
  · have hfun : runW w ℓ₀ (roundOut s u₀ w₁ c₀ c₁ α b).1 = fun r ↦ runW w ℓ₀ s (α :: r) :=
      funext (runW_fold w ℓ₀ s _ α fun g hgm ↦ (hg g hgm).1)
    rw [hfun, List.length_append, List.length_singleton, rowsOf_foldsA_concat]
    exact hT

variable (μ ℓ₀ w i P pre) in
open Classical in
/-- **One fold round's specification**: from the invariant after `j < ℓ` rounds (and an extra
invariant `X` of the commitments), the invariant after `j + 1`, `(α, β)` escaping at most
`N j / |E|²` after its grind. -/
noncomputable def foldRoundSpec {εmax : ENNReal} (X : CInv) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (B : RoundBounds P εmax) (s : WhirState) (rounds : List FoldRound)
    (hj : rounds.length < P.ℓ) :
    Spec (foldRound s) (fun h ↦ RoundInv μ ℓ₀ w i P pre s rounds (commits h) ∧ X (commits h))
      (fun r h ↦ RoundInv μ ℓ₀ w i P pre r.1 (rounds ++ [r.2]) (commits h) ∧ X (commits h))
      εmax 0 0 :=
  let j := rounds.length
  let N := B.N j
  let I : CInv := fun cs ↦ RoundInv μ ℓ₀ w i P pre s rounds cs ∧ X cs
  Spec.congr (foldRound_eq s).symm <|
  (readInv I (T := 0) zero_le).bind' fun u₀ ↦ (readInv I (T := 0) zero_le).bind' fun w₁ ↦
  (readInv I (T := 0) zero_le).bind' fun c₀ ↦ (readInv I (T := 0) zero_le).bind' fun c₁ ↦
  (grindInv I (b := Whir.foldGrindingBits) (by decide)
      (T := (N : ENNReal) / Fintype.card E ^ 2 + 0) (by simpa using B.eF j hj)).bind' fun _ ↦
  Spec.ofNoMove (noMoves_pairP _).noMove (B.eF1 j hj) fun h₀ hp ↦ by
    have h := escRet_pairP (fun α b ↦ roundOut s u₀ w₁ c₀ c₁ α b)
      (fun r cs ↦ RoundInv μ ℓ₀ w i P pre r.1 (rounds ++ [r.2]) cs ∧ X cs) h₀
    refine h.le.trans ?_
    rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
    refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun t ht ↦ ?_).trans
      (card_foldEsc_round_le hw hℓ₀ s rounds hj _ (B.bound j hj) hp.1 u₀ w₁ c₀ c₁)))
    obtain ⟨⟨hlen, hj', hκ, hg, -⟩, hX⟩ := hp
    simp only [mem_filter, mem_univ, true_and] at ht
    by_contra hT
    exact ht ⟨roundInv_step s rounds u₀ w₁ c₀ c₁ t.1 t.2 t _ hlen (by omega) hκ hg hT rfl, hX⟩

theorem foldRounds_succ (n : ℕ) (s : WhirState) :
    foldRounds (n + 1) s = foldRound s >>= fun r ↦ foldRounds n r.1 >>= fun rr ↦
      VerifierProgram.ret (rr.1, r.2 :: rr.2) := by
  rw [foldRounds]
  simp only [bind_eq]
  congr 1

variable (μ ℓ₀ w i P pre) in
/-- **The fold rounds' specification**: from the invariant after `rounds`, `n` more rounds keep it
and return it with their rounds appended. -/
noncomputable def foldRoundsSpec {εmax : ENNReal} (X : CInv) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (B : RoundBounds P εmax) :
    (n : ℕ) → (s : WhirState) → (rounds : List FoldRound) → rounds.length + n = P.ℓ →
      Spec (foldRounds n s)
        (fun h ↦ RoundInv μ ℓ₀ w i P pre s rounds (commits h) ∧ X (commits h))
        (fun r h ↦ (RoundInv μ ℓ₀ w i P pre r.1 (rounds ++ r.2) (commits h) ∧ X (commits h)) ∧
          r.2.length = n) εmax 0 0
  | 0, s, rounds, _ => (Spec.ret (s, [])).mono (fun _ h ↦ ⟨by simpa using h, rfl⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, s, rounds, hn => Spec.congr (foldRounds_succ n s).symm <|
    (foldRoundSpec μ ℓ₀ w i P pre X hw hℓ₀ B s rounds (by omega)).bind' fun r ↦
      (foldRoundsSpec X hw hℓ₀ B n r.1 (rounds ++ [r.2]) (by simp; omega)).bind' fun rr ↦
        (Spec.ret (rr.1, r.2 :: rr.2)).mono
          (fun _ h ↦ ⟨by simpa using h.1, by simp [h.2]⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.Whir.Sound
