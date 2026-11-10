/-
  LeanVM.Protocol.Whir.Sound.Folds

  The specification of a WHIR level's affine fold rounds: the invariant (every tuple close to the
  level's oracle folded by its rounds so far violates the running claim) is kept by each round,
  the premix escaping at most `Lθ / |E|` and the challenges `(γ, α, β)` at most `N / |E|³`, each
  after its grind.
-/

module

public import LeanVM.Protocol.Whir.Sound.Generic
public import LeanVM.Protocol.Whir.Sound.Code
public import LeanVM.Protocol.Whir.Sound.Group

/-!
# The fold rounds

`foldRounds ℓ s` (`LeanVM.Protocol.Verifier.foldRounds`, `crates/verifier/src/whir.rs:240-254`)
runs the level's affine fold rounds (`foldRound`): a grind and the premix `θ`, five scalars, a
grind and `(γ, α, β)`, the claim folded (`foldClaim`).

* `RoundInv`: the doom of Annex B's round-by-round argument after `j` rounds of level `i`
  (`thm:rbr`, "after the batching challenge and after each fold message"): the state has
  `pre + j` `γ`s, the level's code has `κ = μ − pre − ℓ`, the glued claims are well formed, and
  every tuple of degree at most `d_j` agreeing with the oracle of commitment `i` folded by the
  level's `j` rounds (`foldsA`, `ℓ − j` lane variables left) on at least `A_j` columns violates the
  running claim `(runW w ℓ₀ s, s.claim)`.
* `RoundMid`: the doom after the premix: as above, and every table leaves at most `N` escaping
  triples (`PremixOK`).
* `RoundBounds P εmax`: the fold-round lemma at each round of the level with its escape counts
  `Lθ j` and `N j`, each within `εmax` after the `9`-bit grind.
* `foldRoundSpec`, `foldRoundsSpec`: the rounds keep `RoundInv` and return in it with all `ℓ`
  rounds, the commitments' extra invariant `X` untouched.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

@[expose] public section

/-! ## Three challenges -/

/-- Three challenges and a value of them. -/
def tripleP {β : Type} (F : E → E → E → β) : VerifierProgram β :=
  sampleChallenge >>= fun γ ↦ sampleChallenge >>= fun α ↦ sampleChallenge >>= fun b ↦
    VerifierProgram.ret (F γ α b)

theorem noMoves_tripleP {β : Type} (F : E → E → E → β) : NoMoves (tripleP F) :=
  noMoves_sampleE.bind fun _ ↦ noMoves_sampleE.bind fun _ ↦ noMoves_sampleE.bind fun _ ↦
    NoMoves.ret _

open Classical in
/-- **Three challenges' escape**: the fraction of triples whose value breaks a predicate of the
commitments. -/
theorem escRet_tripleP {β : Type} (F : E → E → E → β) (Q : β → List (ℕ × ℕ × Word) → Prop)
    (h₀ : List Ev) :
    escRet (fun a h ↦ Q a (commits h)) h₀ [] (tripleP F) =
      (Fintype.card E : ENNReal)⁻¹ ^ 3 *
        ((univ.filter fun t : E × E × E ↦ ¬ Q (F t.1 t.2.1 t.2.2) (commits h₀)).card : ENNReal) := by
  unfold escRet
  have hc := retExp_commits (fun a cs ↦ if Q a cs then (0 : ENNReal) else 1) (tripleP F) h₀ []
  rw [hc, List.append_nil]
  unfold tripleP
  simp only [bind_eq]
  rw [retExp_bind, retExp_sampleE]
  simp only [retExp_bind, retExp_sampleE, retExp, ← Finset.mul_sum]
  rw [← Finset.sum_boole, ← mul_assoc, ← mul_assoc, ← pow_two, ← pow_succ]
  congr 1
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun γ _ ↦ Finset.sum_congr rfl fun α _ ↦
    Finset.sum_congr rfl fun b _ ↦ ?_
  split_ifs <;> simp_all

/-! ## The invariant -/

section

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (pre : ℕ)

/-- **The fold invariant** after the rounds `rounds` of level `i`. -/
def RoundInv (s : WhirState) (rounds : List FoldRound) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.gammas.length = pre + rounds.length ∧ rounds.length ≤ P.ℓ ∧ P.κ + pre + P.ℓ = μ ∧
    GluedOK μ s ∧
    TViol P.κ P.dom (rowsOf (P.ℓ - rounds.length) (foldsA P.dom rounds (laneO i cs P.n)))
      (runW w ℓ₀ s) s.claim (P.thr rounds.length) (P.deg rounds.length)

/-- The doom right after a round's premix `θ`: every table leaves at most `N` escaping triples. -/
def RoundMid (N : ℕ) (s : WhirState) (rounds : List FoldRound) (θ : E)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.gammas.length = pre + rounds.length ∧ rounds.length < P.ℓ ∧ P.κ + pre + P.ℓ = μ ∧
    GluedOK μ s ∧
    PremixOK P.κ P.dom (rowsOf (P.ℓ - (rounds.length + 1) + 1)
      (foldsA P.dom rounds (laneO i cs P.n))) (runW w ℓ₀ s) s.claim
      (P.thr (rounds.length + 1)) (P.deg (rounds.length + 1)) N θ

end

/-- **The fold-round lemma at every round of a level**, with its escape counts within `εmax`
after the `9`-bit grinds. -/
structure RoundBounds (P : LevelCode) (εmax : ENNReal) where
  /-- The premix's escape count of round `j + 1`. -/
  Lθ : ℕ → ℕ
  /-- The escape count of `(γ, α, β)` of round `j + 1`. -/
  N : ℕ → ℕ
  /-- The last round's threshold exceeds the folds. -/
  hA : P.ℓ < P.A
  /-- The fold-round lemma. -/
  bound : ∀ j < P.ℓ, FoldRoundBound P.dom (P.deg (j + 1)) (P.thr (j + 1)) (Lθ j) (N j)
  /-- The premix's escape after its grind. -/
  eθ : ∀ j < P.ℓ, (2 : ENNReal)⁻¹ ^ Whir.foldGrindingBits *
    ((Lθ j : ENNReal) / Fintype.card E) ≤ εmax
  /-- The escape of `(γ, α, β)` after its grind. -/
  eF : ∀ j < P.ℓ, (2 : ENNReal)⁻¹ ^ Whir.foldGrindingBits *
    ((N j : ENNReal) / Fintype.card E ^ 3) ≤ εmax
  /-- The escape of `(γ, α, β)` is below one. -/
  eF1 : ∀ j < P.ℓ, (N j : ENNReal) / Fintype.card E ^ 3 < 1

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {pre : ℕ}

theorem tviol_rowsOf_congr {n m m' κ : ℕ} {dom : Fin n ↪ E} {O : ℕ → Fin n → E}
    {Φ : List E → E} {σ : E} {a d : ℕ} (h : m = m') :
    TViol κ dom (rowsOf m O) Φ σ a d ↔ TViol κ dom (rowsOf m' O) Φ σ a d := by
  subst h; rfl

open Classical in
/-- **The premix's escape**: at most `Lθ` values of `θ` leave `RoundMid`. -/
theorem card_premix_le (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) {Lθ N : ℕ} (s : WhirState)
    (rounds : List FoldRound) (hj : rounds.length < P.ℓ) (cs : List (ℕ × ℕ × Word))
    (hB : FoldRoundBound P.dom (P.deg (rounds.length + 1)) (P.thr (rounds.length + 1)) Lθ N)
    (hI : RoundInv μ ℓ₀ w i P pre s rounds cs) :
    (univ.filter fun θ ↦ ¬ RoundMid μ ℓ₀ w i P pre N s rounds θ cs).card ≤ Lθ := by
  obtain ⟨hlen, -, hκ, hg, hv⟩ := hI
  set m := P.ℓ - (rounds.length + 1) with hm
  have hma : IsMultiaffine (m + 1 + P.κ) (runW w ℓ₀ s) := by
    have := isMultiaffine_runW hw hℓ₀ s (by omega) hg
    rwa [show μ - s.gammas.length = m + 1 + P.κ by omega] at this
  have hv' : TViol P.κ P.dom (rowsOf (m + 1) (foldsA P.dom rounds (laneO i cs P.n)))
      (runW w ℓ₀ s) s.claim (P.thr (rounds.length + 1) - 1) (P.deg (rounds.length + 1) - 1) := by
    have ha : P.thr (rounds.length + 1) - 1 = P.thr rounds.length := by
      simp only [LevelCode.thr]; omega
    have hd : P.deg (rounds.length + 1) - 1 = P.deg rounds.length := by
      simp only [LevelCode.deg]; omega
    rw [ha, hd, ← tviol_rowsOf_congr (show P.ℓ - rounds.length = m + 1 by omega)]
    exact hv
  refine (card_le_card fun θ hθ ↦ ?_).trans
    (card_premix_bad_le P.κ P.dom _ _ s.claim _ _ hB hma hv')
  simp only [mem_filter, mem_univ, true_and, RoundMid, not_and] at hθ ⊢
  exact hθ hlen hj hκ hg

/-! ## The rounds -/

/-- The state and the round after a round's challenges. -/
def roundOut (s : WhirState) (θ u₀ v₀ c₀ v₁ c₁ γ α b : E) : WhirState × FoldRound :=
  ({ s with claim := foldClaim s.claim θ γ α b u₀ v₀ c₀ v₁ c₁, gammas := s.gammas ++ [γ] },
    ⟨θ, α, b⟩)

/-- `foldRound` as the moves the specification composes. -/
theorem foldRound_eq (s : WhirState) :
    foldRound s = grindProofOfWork Whir.foldGrindingBits >>= fun _ ↦
      sampleChallenge >>= fun θ ↦ readScalar >>= fun u₀ ↦ readScalar >>= fun v₀ ↦
      readScalar >>= fun c₀ ↦ readScalar >>= fun v₁ ↦ readScalar >>= fun c₁ ↦
      grindProofOfWork Whir.foldGrindingBits >>= fun _ ↦
      tripleP fun γ α b ↦ roundOut s θ u₀ v₀ c₀ v₁ c₁ γ α b :=
  rfl

/-- After an escaping-free triple, the invariant with one more round. -/
theorem roundInv_step (s : WhirState) (rounds : List FoldRound) (θ u₀ v₀ c₀ v₁ c₁ γ α b : E)
    (t : E × E × E) (cs : List (ℕ × ℕ × Word)) (hlen : s.gammas.length = pre + rounds.length)
    (hj : rounds.length < P.ℓ) (hκ : P.κ + pre + P.ℓ = μ) (hg : GluedOK μ s)
    (hT : t ∉ foldEsc P.κ P.dom (rowsOf (P.ℓ - (rounds.length + 1) + 1)
      (foldsA P.dom rounds (laneO i cs P.n))) (runW w ℓ₀ s) s.claim
      (P.thr (rounds.length + 1)) (P.deg (rounds.length + 1)) θ u₀ v₀ c₀ v₁ c₁)
    (ht : t = (γ, α, b)) :
    RoundInv μ ℓ₀ w i P pre (roundOut s θ u₀ v₀ c₀ v₁ c₁ γ α b).1
      (rounds ++ [(roundOut s θ u₀ v₀ c₀ v₁ c₁ γ α b).2]) cs := by
  subst ht
  simp only [foldEsc, mem_filter, mem_univ, true_and, not_not] at hT
  refine ⟨by simp [roundOut, hlen]; omega, by simp; omega, hκ, fun g hgm ↦ ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hg g hgm
    exact ⟨by simp [roundOut]; omega, h2⟩
  · have hfun : runW w ℓ₀ (roundOut s θ u₀ v₀ c₀ v₁ c₁ γ α b).1 = fun r ↦ runW w ℓ₀ s (γ :: r) :=
      funext (runW_fold w ℓ₀ s _ γ fun g hgm ↦ (hg g hgm).1)
    rw [hfun, List.length_append, List.length_singleton, rowsOf_foldsA_concat]
    exact hT

variable (μ ℓ₀ w i P pre) in
open Classical in
/-- **One fold round's specification**: from the invariant after `j < ℓ` rounds (and an extra
invariant `X` of the commitments), the invariant after `j + 1`, the premix escaping at most
`Lθ j / |E|` and `(γ, α, β)` at most `N j / |E|³`, each after its grind. -/
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
  (grindInv I (b := Whir.foldGrindingBits) (by decide) (T := (B.Lθ j : ENNReal) / Fintype.card E + 0)
      (by simpa using B.eθ j hj)).bind' fun _ ↦
  (Spec.sampleE (Pre := fun h ↦ I (commits h))
      (Post := fun θ h ↦ RoundMid μ ℓ₀ w i P pre N s rounds θ (commits h) ∧ X (commits h))
      (T := 0) ((B.Lθ j : ENNReal) / Fintype.card E) fun h₀ hp ↦ by
        rw [ENNReal.div_eq_inv_mul]
        refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun θ hθ ↦ ?_).trans
          (card_premix_le hw hℓ₀ s rounds hj _ (B.bound j hj) hp.1)))
        simp only [mem_filter, mem_univ, true_and, commits_sample] at hθ ⊢
        exact fun hm ↦ hθ ⟨hm, hp.2⟩).bind' fun θ ↦
  let I' : CInv := fun cs ↦ RoundMid μ ℓ₀ w i P pre N s rounds θ cs ∧ X cs
  (readInv I' (T := 0) zero_le).bind' fun u₀ ↦ (readInv I' (T := 0) zero_le).bind' fun v₀ ↦
  (readInv I' (T := 0) zero_le).bind' fun c₀ ↦ (readInv I' (T := 0) zero_le).bind' fun v₁ ↦
  (readInv I' (T := 0) zero_le).bind' fun c₁ ↦
  (grindInv I' (b := Whir.foldGrindingBits) (by decide)
      (T := (N : ENNReal) / Fintype.card E ^ 3 + 0) (by simpa using B.eF j hj)).bind' fun _ ↦
  Spec.ofNoMove (noMoves_tripleP _).noMove (B.eF1 j hj) fun h₀ hp ↦ by
    have h := escRet_tripleP (fun γ α b ↦ roundOut s θ u₀ v₀ c₀ v₁ c₁ γ α b)
      (fun r cs ↦ RoundInv μ ℓ₀ w i P pre r.1 (rounds ++ [r.2]) cs ∧ X cs) h₀
    refine h.le.trans ?_
    rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
    refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun t ht ↦ ?_).trans
      (hp.1.2.2.2.2 u₀ v₀ c₀ v₁ c₁)))
    obtain ⟨⟨hlen, hj', hκ, hg, -⟩, hX⟩ := hp
    simp only [mem_filter, mem_univ, true_and] at ht
    by_contra hT
    exact ht ⟨roundInv_step s rounds θ u₀ v₀ c₀ v₁ c₁ t.1 t.2.1 t.2.2 t _ hlen hj' hκ hg hT rfl, hX⟩

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
