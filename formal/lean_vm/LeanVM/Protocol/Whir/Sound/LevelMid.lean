/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  The specification of a WHIR level with a next one: the fold rounds, the next commitment and the
  folded lane's high part, the out-of-domain point after its grind, the query message (positions
  and the batching challenge) after its grind, the openings, and the glued claim handed to the
  next level.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelFacts

/-!
# A level with a next one

`whirLevels` on `level :: next :: rest` (`crates/verifier/src/whir.rs:230-327`): the level's fold
rounds (`foldRoundsSpec`), then `midTail`: the next commitment, the high part, a `17`-bit grind and
the out-of-domain point (`eOod`), its value, a `17`-bit grind, then the positions (`eQuery`) and
`λ` (`eLam`) in one message after that grind, the openings, the glued claim, and the next level.

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
  readCommitment (logN - s.alphas.length - next.fold + next.logInvRate) (2 * 2 ^ next.fold) >>=
    fun _ ↦ readScalars level.fold >>= fun high ↦
  grindProofOfWork Whir.levelOodGrindingBits >>= fun _ ↦
  sampleChallenges (logN - s.alphas.length) >>= fun z ↦
  readScalar >>= fun y ↦
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  sampleQueries (logN - s.alphas.length + level.logInvRate) level.queries >>= fun qs ↦
  sampleChallenge >>= fun lam ↦
  queryOpenings index qs >>= fun words ↦
  whirLevels logN laneFolds eb (index + 1) (next :: rest)
    (glueLevel s lam (logN - s.alphas.length) z y qs (powers lam qs.length)
      (batchedOf index (logN - s.alphas.length) rounds high qs (powers lam qs.length) words))

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

/-- The out-of-domain point's escape: `C(L', 2) κ |E|^(κ−1) / |E|^κ`, i.e. `C(L', 2) κ / |E|`. -/
noncomputable def eOod (P P' : LevelCode) : ENNReal :=
  (Fintype.card E : ENNReal)⁻¹ ^ P.κ *
    ((P'.listMax.choose 2 * (P.κ * Fintype.card E ^ (P.κ - 1)) : ℕ) : ENNReal)

/-- The query group's escape: `((A − 1)/n)^t`. -/
noncomputable def eQuery (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.A - 1 : ℕ) : ENNReal) / ((2 ^ (P.κ + P.R) : ℕ) : ENNReal)) ^ t

/-- The batching challenge's escape: `(t + 1) L' / |E|`, over the `t + 2` claims it batches
(the running claim, the out-of-domain claim, the `t` queries). -/
noncomputable def eLam (P' : LevelCode) (t : ℕ) : ENNReal :=
  (((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- **A level with a next one**: the codes' relations and the groups' escapes within `εmax`
after their grinds. -/
structure MidOK (P P' : LevelCode) (t : ℕ) (εmax : ENNReal) : Prop where
  hκ : P.κ = P'.ℓ + P'.κ
  hℓ : 1 ≤ P.ℓ
  hℓκ : P.ℓ ≤ 2 ^ P.κ
  hA : 1 ≤ P.A
  gap : P'.n * P'.deg < P'.thr 0 * P'.thr 0
  eO : (2 : ENNReal)⁻¹ ^ Whir.levelOodGrindingBits * eOod P P' ≤ εmax
  eO1 : eOod P P' < 1
  eQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * (eQuery P t + eLam P' t) ≤ εmax
  eQ1 : eQuery P t < 1

/-! ## The steps -/

section Steps

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

/-- The commitment appends the next level's word, of its shape. -/
theorem mid_commit {logN : ℕ} {next : Whir.Level} (hκ : P.κ = P'.ℓ + P'.κ)
    (hnext : next.fold = P'.ℓ ∧ next.logInvRate = P'.R) (s : WhirState)
    (rounds : List FoldRound) (cs : List (ℕ × ℕ × Word))
    (hI : RoundInv μ ℓ₀ w i P pre s rounds cs) (hS : ShapeOK i P cs) (hlen : cs.length = i + 1)
    (hmu : logN - s.alphas.length = P.κ) (W : Word) (hW : WellShaped (2 * 2 ^ next.fold) W) :
    RoundInv μ ℓ₀ w i P pre s rounds
        (cs ++ [(logN - s.alphas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      ShapeOK i P
        (cs ++ [(logN - s.alphas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      ShapeOK (i + 1) P'
        (cs ++ [(logN - s.alphas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]) ∧
      (cs ++ [(logN - s.alphas.length - next.fold + next.logInvRate, 2 * 2 ^ next.fold, W)]).length =
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

/-- After the out-of-domain point. -/
def MidI2 (s : WhirState) (rounds : List FoldRound) (high : List E) (z : List E)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidI1 μ ℓ₀ w i P P' pre s rounds cs ∧ high.length = P.ℓ ∧ z.length = P.κ ∧
    OodSep P' (rowsOf P'.ℓ (laneO (i + 1) cs P'.n)) z

/-- After the query positions. -/
def MidI3 (hκ : P.κ = P'.ℓ + P'.κ) (s : WhirState) (rounds : List FoldRound) (high : List E)
    (z : List E) (y : E) (qs : List ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidI2 μ ℓ₀ w i P P' pre s rounds high z cs ∧ (∀ q ∈ qs, q < P.n) ∧
    QDoom P P' hκ (rowsOf P'.ℓ (laneO (i + 1) cs P'.n)) (runW w ℓ₀ s) s.claim z y
      (cOf P i cs rounds high) qs

end Interface

section Escapes

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

open Classical in
/-- **The out-of-domain point's escape** is at most `eOod`. -/
theorem escRet_mid_ood_le (hκ : P.κ = P'.ℓ + P'.κ) (gap : P'.n * P'.deg < P'.thr 0 * P'.thr 0)
    (s : WhirState) (rounds : List FoldRound) (high : List E) (h₀ : List Ev) (hhigh : high.length = P.ℓ)
    (hI : MidI1 μ ℓ₀ w i P P' pre s rounds (commits h₀)) :
    escRet (fun z h ↦ MidI2 μ ℓ₀ w i P P' pre s rounds high z (commits h)) h₀ []
      (sampleChallenges P.κ) ≤ eOod P P' := by
  set Q' := rowsOf P'.ℓ (laneO (i + 1) (commits h₀) P'.n)
  refine (escRet_oodPoint_le _ P.κ h₀ (univ.filter fun f : Fin P.κ → E ↦
    ¬ OodSep P' Q' (List.ofFn f)) fun f hf ↦ ?_).trans ?_
  · simp only [mem_filter, mem_univ, true_and]
    intro hsep
    exact hf ⟨hI, hhigh, by simp, hsep⟩
  · rw [eOod]
    gcongr
    exact (card_oodSep_bad_le P' hκ Q').trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (card_tlist_le_jl _ _ _ _ gap)))

open Classical in
/-- **The query group's escape** is at most `eQuery`. -/
theorem escRet_mid_queries_le (hκ : P.κ = P'.ℓ + P'.κ) (hA : 1 ≤ P.A) (hℓ : 1 ≤ P.ℓ)
    (hℓκ : P.ℓ ≤ 2 ^ P.κ) (s : WhirState) (rounds : List FoldRound) (high : List E)
    (z : List E) (y : E) (t : ℕ) (h₀ : List Ev)
    (hI : MidI2 μ ℓ₀ w i P P' pre s rounds high z (commits h₀)) :
    escRet (fun qs h ↦ MidI3 μ ℓ₀ w i P P' pre hκ s rounds high z y qs (commits h) ∧
      qs.length = t) h₀ [] (sampleQueries (P.κ + P.R) t) ≤ eQuery P t := by
  obtain ⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hz, hsep⟩ := hI
  set C : Fin P.n → E := fun v ↦ foldsA P.dom rounds (laneO i (commits h₀) P.n) 0 v
  have hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) (runW w ℓ₀ s) s.claim (P.thr P.ℓ)
      P.deg := by
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
    C (runW w ℓ₀ s) s.claim z y
    (polyOf high) hH (cOf P i (commits h₀) rounds high) (fun q h ↦ by simp [cOf, h, C]) hviol hsep
  have hdepth : 1 ≤ P.κ + P.R := by have := P.hR; omega
  refine (escRet_queries_le (fun qs cs ↦ MidI3 μ ℓ₀ w i P P' pre hκ s rounds high z y qs cs ∧
      qs.length = t) (P.κ + P.R) t hdepth (by have := P.h64; omega) h₀
    (fun j ↦ ∃ h : j < P.n, (⟨j, h⟩ : Fin P.n) ∈ S) fun qs hqs hl hQ q hq ↦ ?_).trans ?_
  · refine ⟨hqs q hq, hSq qs (fun hD ↦ hQ ⟨⟨⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hz, hsep⟩,
      hqs, hD⟩, hl⟩) q hq (hqs q hq)⟩
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
/-- **The batching challenge's escape**: at most `(t + 1) L'` values of `λ` leave the next
level's doom, the rows being the words' at the positions. -/
theorem card_mid_lambda_le (hκ : P.κ = P'.ℓ + P'.κ) (hℓκ : P.ℓ ≤ 2 ^ P.κ)
    (gap : P'.n * P'.deg < P'.thr 0 * P'.thr 0) (s : WhirState) (rounds : List FoldRound)
    (high : List E) (z : List E) (y : E) (qs : List ℕ)
    (cs : List (ℕ × ℕ × Word)) (hI : MidI3 μ ℓ₀ w i P P' pre hκ s rounds high z y qs cs) :
    (univ.filter fun lam ↦ ¬ LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam P.κ z y qs (powers lam qs.length)
        (batchedOf i P.κ rounds high qs (powers lam qs.length) (qs.map (wordOf cs i)))) cs).card ≤
      (qs.length + 1) * P'.listMax := by
  obtain ⟨⟨⟨hR, hS, hS', hlen, hr⟩, hhigh, hz, hsep⟩, hqs, hQ⟩ := hI
  have hb := fun lam ↦ batchedOf_eq P i cs hS rounds hr high
    (by rw [hhigh]; exact hℓκ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))) qs hqs lam
  refine (card_le_card fun lam hlam ↦ ?_).trans ((card_lambda_bad_le P P' hκ _ (runW w ℓ₀ s)
    s.claim z y (cOf P i cs rounds high) qs
    hqs hQ).trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (card_tlist_le_jl _ _ _ _ gap)))
  simp only [mem_filter, mem_univ, true_and] at hlam ⊢
  by_contra hno
  refine hlam ⟨?_, hS', hlen⟩
  exact nextInv_of hκ s rounds cs hR hr z hz y qs (cOf P i cs rounds high) lam _
    (hb lam) hno

end Lambda

/-! ## The specification -/

section Spec

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (pre : ℕ)

open Classical in
/-- **The rest of a level with a next one**: from the invariant after all its rounds, the
groups escape within `εmax` after their grinds and the next level starts in its doom. -/
noncomputable def midTailSpec {εmax T : ENNReal} (logN laneFolds : ℕ) (eb : List E → E)
    (level next : Whir.Level) (rest : List Whir.Level) (hlogN : logN = μ)
    (hlev : level.fold = P.ℓ ∧ level.logInvRate = P.R)
    (hnext : next.fold = P'.ℓ ∧ next.logInvRate = P'.R) (M : MidOK P P' level.queries εmax)
    (cont : ∀ s', Spec (whirLevels logN laneFolds eb (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ) s' (commits h)) (fun _ _ ↦ False) εmax 0 T)
    (s : WhirState) (rounds : List FoldRound) :
    Spec (midTail logN laneFolds eb i level next rest s rounds)
      (fun h ↦ (RoundInv μ ℓ₀ w i P pre s rounds (commits h) ∧
        (ShapeOK i P (commits h) ∧ (commits h).length = i + 1)) ∧ rounds.length = P.ℓ)
      (fun _ _ ↦ False) εmax 0 T :=
  if hmu : logN - s.alphas.length = P.κ ∧ rounds.length = P.ℓ then
  (commitInv (T := 0)
      (fun cs ↦ (RoundInv μ ℓ₀ w i P pre s rounds cs ∧ (ShapeOK i P cs ∧ cs.length = i + 1)) ∧
        rounds.length = P.ℓ)
      (MidI1 μ ℓ₀ w i P P' pre s rounds) _ _ (fun cs W hI hW ↦ by
        obtain ⟨h1, h2, h3, h4⟩ := mid_commit (logN := logN) M.hκ hnext s rounds cs hI.1.1
          hI.1.2.1 hI.1.2.2 hmu.1 W hW
        exact ⟨h1, h2, h3, h4, hI.2⟩) zero_le).bind' fun _ ↦
  (readNInv (MidI1 μ ℓ₀ w i P P' pre s rounds) (T := 0) zero_le level.fold).bind' fun high ↦
  (grindInv (fun cs ↦ high.length = level.fold ∧ MidI1 μ ℓ₀ w i P P' pre s rounds cs)
    (b := Whir.levelOodGrindingBits) (by decide) (T := eOod P P' + 0)
    (by simpa using M.eO)).bind' fun _ ↦
  (Spec.ofNoMove (Pre := fun h ↦ high.length = level.fold ∧
      MidI1 μ ℓ₀ w i P P' pre s rounds (commits h))
    (Post := fun z h ↦ MidI2 μ ℓ₀ w i P P' pre s rounds high z (commits h)) (T := 0)
    (noMoves_sampleN _).noMove M.eO1 fun h₀ hp ↦ by
      rw [hmu.1]
      exact escRet_mid_ood_le M.hκ M.gap s rounds high h₀ (hp.1.trans hlev.1) hp.2).bind'
    fun z ↦
  (readInv (MidI2 μ ℓ₀ w i P P' pre s rounds high z) (T := 0) zero_le).bind' fun y ↦
  (grindInv (MidI2 μ ℓ₀ w i P P' pre s rounds high z)
    (b := Whir.queryGrindingBits) (by decide)
    (T := eQuery P level.queries + (eLam P' level.queries + 0))
    (by simpa using M.eQ)).bind' fun _ ↦
  (Spec.ofNoMove (Pre := fun h ↦ MidI2 μ ℓ₀ w i P P' pre s rounds high z (commits h))
    (Post := fun qs h ↦ MidI3 μ ℓ₀ w i P P' pre M.hκ s rounds high z y qs (commits h) ∧
      qs.length = level.queries) (T := eLam P' level.queries + 0)
    (noMoves_sampleQueriesAux _ _ _).noMove M.eQ1 fun h₀ hp ↦ by
      rw [hmu.1, hlev.2]
      exact escRet_mid_queries_le M.hκ M.hA M.hℓ M.hℓκ s rounds high z y _ h₀ hp).bind' fun qs ↦
  (Spec.sampleE (Pre := fun h ↦ MidI3 μ ℓ₀ w i P P' pre M.hκ s rounds high z y qs (commits h) ∧
      qs.length = level.queries)
    (Post := fun lam h ↦ (LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam (logN - s.alphas.length) z y qs (powers lam qs.length)
        (batchedOf i (logN - s.alphas.length) rounds high qs (powers lam qs.length)
          (qs.map (wordOf (commits h) i)))) (commits h)) ∧
      ShapeOK i P (commits h) ∧ ∀ q ∈ qs, q < P.n) (T := 0) (eLam P' level.queries)
    fun h₀ hp ↦ by
      rw [eLam, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun lam hlam ↦ ?_).trans
        ((card_mid_lambda_le M.hκ M.hℓκ M.gap s rounds high z y qs _ hp.1).trans
          (by rw [hp.2]))))
      simp only [mem_filter, mem_univ, true_and, commits_sample, hmu.1, not_and] at hlam ⊢
      exact fun h ↦ hlam h hp.1.1.1.2.1 hp.1.2.1).bind' fun lam ↦
  (Spec.queryP (Pre := fun h ↦ (LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam (logN - s.alphas.length) z y qs (powers lam qs.length)
        (batchedOf i (logN - s.alphas.length) rounds high qs (powers lam qs.length)
          (qs.map (wordOf (commits h) i)))) (commits h)) ∧
      ShapeOK i P (commits h) ∧ ∀ q ∈ qs, q < P.n)
    (Post := fun words h ↦ LevelPre μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam (logN - s.alphas.length) z y qs (powers lam qs.length)
        (batchedOf i (logN - s.alphas.length) rounds high qs (powers lam qs.length) words))
        (commits h)) (T := 0) i qs fun h₀ rows hp hans ↦ by
      obtain ⟨hpre, ⟨W, hW, -⟩, hq⟩ := hp
      have hrows : rows = qs.map (wordOf (commits h₀) i) := by
        simp only [answer, hW, Option.map_some, Option.some.injEq] at hans
        rw [← hans, wordOf_eq hW]
        exact List.map_congr_left fun q hqm ↦ by rw [Nat.mod_eq_of_lt (hq q hqm)]
      rw [hrows]
      simpa [commits_append, commits] using hpre).bind' fun words ↦
  cont _
  else Spec.dead.mono (fun h hp ↦ hmu ⟨by
      obtain ⟨⟨⟨hlen, -, hκ, -⟩, -⟩, hr⟩ := hp
      omega, hp.2⟩) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Spec

end
end LeanVM.Protocol.Whir.Sound
