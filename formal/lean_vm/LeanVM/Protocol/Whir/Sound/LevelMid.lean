/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  The specification of a WHIR level with a next one: the fold rounds, the next commitment and the
  folded lane's high part, the out-of-domain group, the query group after its grind, the batching
  challenge after its grind with the openings, and the glued claim handed to the next level.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelFacts

/-!
# A level with a next one

`whirLevels` on `level :: next :: rest` (`crates/verifier/src/whir.rs:240-341`): the level's fold
rounds (`foldRoundsSpec`), then `midTail`: the next commitment, the high part, the two
out-of-domain points (one group, no grind, `eOod`), their values, a `17`-bit grind and the
positions (`eQuery`), a `14`-bit grind and `λ` with the openings (`eLam`), the glued claim, and
the next level.

`LevelPre μ ℓ₀ w i P pre s cs`: the doom at the start of level `i`: the invariant with no round,
and the level's commitment is the last, of the level's shape. `MidOK P P' t εmax`: the level's
code relations and its groups' escapes within `εmax` after their grinds.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

@[expose] public section

/-! ## The program -/

/-- The rest of a level with a next one, after its fold rounds. -/
def midTail (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level next : Whir.Level)
    (rest : List Whir.Level) (s : WhirState) (rounds : List FoldRound) : VerifierProgram Unit :=
  readCommitment (logN - s.gammas.length - next.fold + next.logInvRate) (2 * 2 ^ next.fold) >>=
    fun _ ↦ readScalars level.fold >>= fun high ↦
  sampleOodPoints (logN - s.gammas.length) Whir.oodSamples >>= fun pts ↦
  readScalars Whir.oodSamples >>= fun ys ↦
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  sampleQueries (logN - s.gammas.length + level.logInvRate) level.queries >>= fun qs ↦
  grindProofOfWork Whir.batchGrindingBits >>= fun _ ↦
  sampleChallenge >>= fun lam ↦
  queryOpenings index qs >>= fun words ↦
  whirLevels logN laneFolds eb (index + 1) (next :: rest)
    (glueLevel s lam (logN - s.gammas.length) pts ys qs (powers lam qs.length)
      (batchedOf index (logN - s.gammas.length) rounds high qs (powers lam qs.length) words))

theorem whirLevels_mid (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ)
    (level next : Whir.Level) (rest : List Whir.Level) (s : WhirState) :
    whirLevels logN laneFolds eb index (level :: next :: rest) s =
      foldRounds level.fold s >>= fun r ↦ midTail logN laneFolds eb index level next rest r.1 r.2 :=
  rfl

/-! ## The doom and the hypotheses -/

/-- **The doom at the start of level `i`**: the invariant with no round, and commitment `i` is the
last, of the level's shape. -/
def LevelPre (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (pre : ℕ) (s : WhirState)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  RoundInv μ ℓ₀ w i P pre s [] cs ∧ ShapeOK i P cs ∧ cs.length = i + 1

/-- The out-of-domain group's escape: `L'² (κ |E|^(κ−1))² / |E|^(2κ)`. -/
noncomputable def eOod (P P' : LevelCode) : ENNReal :=
  (Fintype.card E : ENNReal)⁻¹ ^ P.κ * (Fintype.card E : ENNReal)⁻¹ ^ P.κ *
    ((P'.listMax ^ 2 * (P.κ * Fintype.card E ^ (P.κ - 1)) ^ 2 : ℕ) : ENNReal)

/-- The query group's escape: `((A − 1)/n)^t`. -/
noncomputable def eQuery (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.A - 1 : ℕ) : ENNReal) / ((2 ^ (P.κ + P.R) : ℕ) : ENNReal)) ^ t

/-- The batching group's escape: `(t + 2) L' / |E|`. -/
noncomputable def eLam (P' : LevelCode) (t : ℕ) : ENNReal :=
  (((t + 2) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- **A level with a next one**: the codes' relations and the groups' escapes within `εmax`
after their grinds. -/
structure MidOK (P P' : LevelCode) (t : ℕ) (εmax : ENNReal) : Prop where
  hκ : P.κ = P'.ℓ + P'.κ
  hℓ : 1 ≤ P.ℓ
  hℓκ : P.ℓ ≤ 2 ^ P.κ
  hA : 1 ≤ P.A
  gap : P'.n * P'.deg 0 < P'.thr 0 * P'.thr 0
  eO : eOod P P' ≤ εmax
  eO1 : eOod P P' < 1
  eQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P t ≤ εmax
  eQ1 : eQuery P t < 1
  eL : (2 : ENNReal)⁻¹ ^ Whir.batchGrindingBits * eLam P' t ≤ εmax

/-! ## The steps -/

section Steps

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

/-- The commitment appends the next level's word, of its shape. -/
theorem mid_commit {logN : ℕ} {next : Whir.Level} (hκ : P.κ = P'.ℓ + P'.κ)
    (hnext : next.fold = P'.ℓ ∧ next.logInvRate = P'.R) (s : WhirState)
    (rounds : List FoldRound) (cs : List (ℕ × ℕ × Word))
    (hI : RoundInv μ ℓ₀ w i P pre s rounds cs) (hS : ShapeOK i P cs) (hlen : cs.length = i + 1)
    (hmu : logN - s.gammas.length = P.κ) (W : Word) (hW : WellShaped (2 * 2 ^ next.fold) W) :
    RoundInv μ ℓ₀ w i P pre s rounds
        (cs ++ [(logN - s.gammas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      ShapeOK i P
        (cs ++ [(logN - s.gammas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      ShapeOK (i + 1) P'
        (cs ++ [(logN - s.gammas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      (cs ++ [(logN - s.gammas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]).length =
        i + 2 := by
  have hi : i < cs.length := by omega
  refine ⟨?_, ?_, ?_, by simp [hlen]⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    exact ⟨h1, h2, h3, h4, by rw [laneO_append _ _ hi]; exact h5⟩
  · obtain ⟨W₀, hW₀, hl⟩ := hS
    exact ⟨W₀, by rw [List.getElem?_append_left hi]; exact hW₀, hl⟩
  · refine ⟨W, ?_, fun v ↦ ?_⟩
    · rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]
      refine ⟨by rw [hmu, hnext.1, hnext.2, hκ]; omega, by simp [wdOf, hnext.1]⟩
    · rw [hW v]; simp [wdOf, hnext.1]

end Steps

/-! ## The interface's doom -/

section Interface

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (pre : ℕ)

/-- After the next commitment. -/
def MidI1 (s : WhirState) (rounds : List FoldRound) (cs : List (ℕ × ℕ × Word)) : Prop :=
  RoundInv μ ℓ₀ w i P pre s rounds cs ∧ ShapeOK i P cs ∧ ShapeOK (i + 1) P' cs ∧
    cs.length = i + 2 ∧ rounds.length = P.ℓ

/-- After the out-of-domain points. -/
def MidI2 (s : WhirState) (rounds : List FoldRound) (high : List E) (pts : List (List E))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidI1 μ ℓ₀ w i P P' pre s rounds cs ∧ high.length = P.ℓ ∧
    pts = [pts.getD 0 [], pts.getD 1 []] ∧ (pts.getD 0 []).length = P.κ ∧
    (pts.getD 1 []).length = P.κ ∧
    OodSep2 P' (rowsOf P'.ℓ (laneO (i + 1) cs P'.n)) (pts.getD 0 []) (pts.getD 1 [])

/-- After the query positions. -/
def MidI3 (hκ : P.κ = P'.ℓ + P'.κ) (s : WhirState) (rounds : List FoldRound) (high : List E)
    (pts : List (List E)) (ys : List E) (qs : List ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidI2 μ ℓ₀ w i P P' pre s rounds high pts cs ∧ ys = [ys.getD 0 0, ys.getD 1 0] ∧
    (∀ q ∈ qs, q < P.n) ∧
    QDoom P P' hκ (rowsOf P'.ℓ (laneO (i + 1) cs P'.n)) (runW w ℓ₀ s) s.claim (pts.getD 0 [])
      (pts.getD 1 []) (ys.getD 0 0) (ys.getD 1 0) (cOf P i cs rounds high) qs

end Interface

section Escapes

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

open Classical in
/-- **The out-of-domain group's escape** is at most `eOod`. -/
theorem escRet_mid_ood_le (hκ : P.κ = P'.ℓ + P'.κ) (gap : P'.n * P'.deg 0 < P'.thr 0 * P'.thr 0)
    (s : WhirState) (rounds : List FoldRound) (high : List E) (h₀ : List Ev) (hhigh : high.length = P.ℓ)
    (hI : MidI1 μ ℓ₀ w i P P' pre s rounds (commits h₀)) :
    escRet (fun pts h ↦ MidI2 μ ℓ₀ w i P P' pre s rounds high pts (commits h)) h₀ []
      (sampleOodPoints P.κ 2) ≤ eOod P P' := by
  set Q' := rowsOf P'.ℓ (laneO (i + 1) (commits h₀) P'.n)
  refine (escRet_oodPoints_le _ P.κ h₀ (univ.filter fun zz : (Fin P.κ → E) × (Fin P.κ → E) ↦
    ¬ OodSep2 P' Q' (List.ofFn zz.1) (List.ofFn zz.2)) fun f₁ f₂ hf ↦ ?_).trans ?_
  · simp only [mem_filter, mem_univ, true_and]
    intro hsep
    exact hf ⟨hI, hhigh, rfl, by simp, by simp, by simpa using hsep⟩
  · rw [eOod]
    gcongr
    refine (card_oodSep2_bad_le P' hκ Q').trans ?_
    gcongr
    exact card_tlist_le_jl _ _ _ _ gap

open Classical in
/-- **The query group's escape** is at most `eQuery`. -/
theorem escRet_mid_queries_le (hκ : P.κ = P'.ℓ + P'.κ) (hA : 1 ≤ P.A) (hℓ : 1 ≤ P.ℓ)
    (hℓκ : P.ℓ ≤ 2 ^ P.κ) (s : WhirState) (rounds : List FoldRound) (high : List E)
    (pts : List (List E)) (ys : List E) (t : ℕ) (h₀ : List Ev)
    (hI : MidI2 μ ℓ₀ w i P P' pre s rounds high pts (commits h₀))
    (hys : ys = [ys.getD 0 0, ys.getD 1 0]) :
    escRet (fun qs h ↦ MidI3 μ ℓ₀ w i P P' pre hκ s rounds high pts ys qs (commits h)) h₀ []
      (sampleQueries (P.κ + P.R) t) ≤ eQuery P t := by
  obtain ⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hpts, hz₁, hz₂, hsep⟩ := hI
  set C : Fin P.n → E := fun v ↦ foldsA P.dom rounds (laneO i (commits h₀) P.n) 0 v
  have hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) (runW w ℓ₀ s) s.claim (P.thr P.ℓ)
      (P.deg P.ℓ) := by
    have h5 := hR.2.2.2.2
    rw [tviol_rowsOf_congr (show P.ℓ - rounds.length = 0 by omega), hr] at h5
    have hrow : rowsOf 0 (foldsA P.dom rounds (laneO i (commits h₀) P.n)) =
        fun _ : Fin 0 → Bool ↦ C := by
      funext u v
      simp [rowsOf, C, bitsToNat]
    rwa [hrow] at h5
  have hH : (polyOf high).natDegree + 1 ≤ P.ℓ := by
    have h64 : 2 ^ P.κ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (le_of_lt P.κ_lt)
    have := natDegree_polyOf_le high (by rw [hhigh]; exact hℓκ.trans h64)
    rw [hhigh, max_eq_left hℓ] at this
    exact this
  obtain ⟨S, hScard, hSq⟩ := exists_agreeSet P P' hκ hA (rowsOf P'.ℓ (laneO (i + 1) (commits h₀) P'.n))
    C (runW w ℓ₀ s) s.claim (pts.getD 0 []) (pts.getD 1 []) (ys.getD 0 0) (ys.getD 1 0)
    (polyOf high) hH (cOf P i (commits h₀) rounds high) (fun q h ↦ by simp [cOf, h, C]) hviol hsep
  have hdepth : 1 ≤ P.κ + P.R := by have := P.hR; omega
  refine (escRet_queries_le _ (P.κ + P.R) t hdepth (by have := P.h64; omega) h₀
    (fun j ↦ ∃ h : j < P.n, (⟨j, h⟩ : Fin P.n) ∈ S) fun qs hqs _ hQ q hq ↦ ?_).trans ?_
  · refine ⟨hqs q hq, hSq qs (fun hD ↦ hQ ⟨⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hpts, hz₁, hz₂, hsep⟩,
      hys, hqs, hD⟩) q hq (hqs q hq)⟩
  · rw [eQuery, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    have : (univ.filter fun j : Fin (2 ^ (P.κ + P.R)) ↦
        ∃ h : (j : ℕ) < P.n, (⟨j, h⟩ : Fin P.n) ∈ S).card ≤ P.A - 1 := by
      refine le_trans (card_le_card fun j hj ↦ ?_) (by omega : S.card ≤ P.A - 1)
      obtain ⟨-, h, hjS⟩ := mem_filter.mp hj
      exact hjS
    exact_mod_cast this

end Escapes

/-! ## The batching challenge -/

section Lambda

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

open Classical in
/-- **The batching challenge's escape**: at most `(t + 2) L'` values of `λ` leave the next
level's doom, the rows being the words' at the positions. -/
theorem card_mid_lambda_le (hκ : P.κ = P'.ℓ + P'.κ) (hℓκ : P.ℓ ≤ 2 ^ P.κ)
    (gap : P'.n * P'.deg 0 < P'.thr 0 * P'.thr 0) (s : WhirState) (rounds : List FoldRound)
    (high : List E) (pts : List (List E)) (ys : List E) (qs : List ℕ)
    (cs : List (ℕ × ℕ × Word)) (hI : MidI3 μ ℓ₀ w i P P' pre hκ s rounds high pts ys qs cs) :
    (univ.filter fun lam ↦ ¬ LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam P.κ pts ys qs (powers lam qs.length)
        (batchedOf i P.κ rounds high qs (powers lam qs.length) (qs.map (wordOf cs i)))) cs).card ≤
      (qs.length + 2) * P'.listMax := by
  obtain ⟨⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hpts, hz₁, hz₂, hsep⟩, hys, hqs, hQ⟩ := hI
  have hb := fun lam ↦ batchedOf_eq P i cs hS rounds hr high
    (by rw [hhigh]; exact hℓκ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))) qs hqs lam
  refine (card_le_card fun lam hlam ↦ ?_).trans ((card_lambda_bad_le P P' hκ _ (runW w ℓ₀ s)
    s.claim (pts.getD 0 []) (pts.getD 1 []) (ys.getD 0 0) (ys.getD 1 0) (cOf P i cs rounds high) qs
    hqs hQ).trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (card_tlist_le_jl _ _ _ _ gap)))
  simp only [mem_filter, mem_univ, true_and] at hlam ⊢
  by_contra hno
  refine hlam ⟨?_, hS', hlen⟩
  rw [hpts, hys]
  exact nextInv_of hκ s rounds cs hR hr _ _ hz₁ hz₂ _ _ qs (cOf P i cs rounds high) lam _
    (hb lam) hno

end Lambda

/-! ## The specification -/

theorem noMoves_sampleOodPoints (mu : ℕ) : ∀ n, NoMoves (sampleOodPoints mu n)
  | 0 => NoMoves.ret []
  | n + 1 => (noMoves_sampleN mu).bind fun _ ↦ (noMoves_sampleOodPoints mu n).bind fun _ ↦
      NoMoves.ret _

end
end LeanVM.Protocol.Whir.Sound
