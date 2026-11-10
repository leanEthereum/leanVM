/-
  LeanVM.Protocol.Whir.Sound.LevelFacts

  What a WHIR level's interface reads from the history: the shape of a level's commitment, the
  values the verifier derives from the opened rows, the next level's invariant after `λ`, and the
  escape expectations of the out-of-domain points and of the query positions.
-/

module

public import LeanVM.Protocol.Whir.Sound.Folds
public import LeanVM.Protocol.Whir.Sound.Novel
public import LeanVM.Protocol.Whir.Sound.Queries

/-!
# The level interface's facts

For a level `i` with code `P` and the next level's code `P'` (`P.κ = P'.ℓ + P'.κ`):

* `ShapeOK i P cs`: commitment `i` has the level's height `κ + R` and leaves of `wdOf i ℓ` words.
* `cOf P i cs rounds high q`: the value the verifier derives from the opened row at `q` (`batched`
  in `whirLevels`): the folded oracle at `x_q` plus `Ŵ_κ(x_q) H(x_q)`, `H` the high part
  (`batchedOf_eq`).
* `nextInv_of`: after `λ`, if no member of the next list satisfies the glued claim, the next
  level's invariant `RoundInv` holds with no round.
* `escRet_ood_le`, `escRet_queries_le`: the out-of-domain points escape `OodSep2` with
  probability at most `|list|² (κ|E|^(κ−1))² / |E|^(2κ)`, the query positions escape `QDoom` with
  probability at most `((A − 1)/n)^t`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset Polynomial

@[expose] public section

/-- Commitment `i` has the level's shape. -/
def ShapeOK (i : ℕ) (P : LevelCode) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ W, cs[i]? = some (P.κ + P.R, wdOf i P.ℓ, W) ∧ ∀ v, (W v).length = wdOf i P.ℓ

/-- The value the verifier derives from the opened row at `q`. -/
noncomputable def cOf (P : LevelCode) (i : ℕ) (cs : List (ℕ × ℕ × Word))
    (rounds : List FoldRound) (high : List E) (q : ℕ) : E :=
  if h : q < P.n then foldsA P.dom rounds (laneO i cs P.n) 0 ⟨q, h⟩ +
    (hatE P.κ * polyOf high).eval (P.dom ⟨q, h⟩) else 0

/-- The verifier's batch of the opened rows (`batched` in `whirLevels`). -/
def batchedOf (index mu : ℕ) (rounds : List FoldRound) (high : List E) (queries : List ℕ)
    (queryWeights : List E) (words : List (List K)) : E :=
  sumE (List.zipWith (fun (qq, row) queryWeight ↦
    let what := subspaceAt mu (K.ofBits qq)
    queryWeight * (foldRow (lanesOf index row) (K.ofBits qq) rounds +
      novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_eq, zero_add]

/-- A batch over zipped queries and rows as a batch over the queries. -/
theorem sumE_zipWith_zip (G : ℕ × List K → E → E) (F : ℕ → List K → E)
    (hG : ∀ q row w, G (q, row) w = w * F q row) (W : ℕ → List K) :
    ∀ (qs : List ℕ) (ws : List E), ws.length = qs.length →
      sumE (List.zipWith G (List.zip qs (qs.map W)) ws) =
        ((ws.zip qs).map fun wq ↦ wq.1 * F wq.2 (W wq.2)).sum
  | [], [], _ => rfl
  | q :: qs, w :: ws, h => by
    have := sumE_zipWith_zip G F hG W qs ws (by simpa using h)
    rw [sumE_eq_sum] at this ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, List.sum_cons, hG] at this ⊢
    rw [this]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The verifier's batch** is `Σ_k λ^k c'(q_k)` with `c' = cOf`. -/
theorem batchedOf_eq (P : LevelCode) (i : ℕ) (cs : List (ℕ × ℕ × Word)) (hS : ShapeOK i P cs)
    (rounds : List FoldRound) (hr : rounds.length = P.ℓ) (high : List E)
    (hhigh : high.length ≤ 2 ^ (P.κ + 1)) (qs : List ℕ) (hq : ∀ q ∈ qs, q < P.n) (lam : E) :
    batchedOf i P.κ rounds high qs (powers lam qs.length) (qs.map (wordOf cs i)) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * cOf P i cs rounds high qs[k] := by
  rw [← sum_zip_powers]
  unfold batchedOf
  rw [sumE_zipWith_zip _ (fun q row ↦ foldRow (lanesOf i row) (K.ofBits q) rounds +
    novelEval high (subspaceAt P.κ (K.ofBits q)) * ofK ((subspaceAt P.κ (K.ofBits q)).getD P.κ 0))
    (fun _ _ _ ↦ rfl) (wordOf cs i) qs _ (length_powers _ _)]
  refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
  have hlt := hq _ (List.of_mem_zip hwq).2
  obtain ⟨W, hW, hlen⟩ := hS
  have hrow : (lanesOf i (wordOf cs i wq.2)).length = 2 ^ rounds.length := by
    rw [hr]; exact length_lanesOf _ (by rw [wordOf_eq hW]; exact hlen _)
  simp only [cOf, hlt, ↓reduceDIte]
  congr 1
  rw [foldRow_eq _ rounds _ hrow, novelEval_eq P.κ_lt high hhigh, subspaceAt_eq,
    List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, eval_mul,
    show P.dom ⟨wq.2, hlt⟩ = ofK (K.ofBits wq.2) from rfl, eval_hatE, mul_comm (ofK _)]
  rfl

/-! ## The next level's invariant -/

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {pre : ℕ}

/-- The running weight of a glued state. -/
theorem runW_glueLevel (s : WhirState) (lam : E) (mu : ℕ) (z₁ z₂ : List E) (y₁ y₂ : E)
    (qs : List ℕ) (batched : E) (x : List E) :
    runW w ℓ₀ (glueLevel s lam mu [z₁, z₂] [y₁, y₂] qs (powers lam qs.length) batched) x =
      gluedW (runW w ℓ₀ s) z₁ z₂ mu qs lam x := by
  rw [glueLevel_eq, gluedW, runW_eq, runW_eq]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.drop_length, List.nil_append, add_zero]
  ring

/-- **After `λ`**: if no member of the next list satisfies the glued claim, the next level's
invariant holds with no round. -/
theorem nextInv_of (hκ : P.κ = P'.ℓ + P'.κ) (s : WhirState) (rounds : List FoldRound)
    (cs : List (ℕ × ℕ × Word)) (hI : RoundInv μ ℓ₀ w i P pre s rounds cs)
    (hr : rounds.length = P.ℓ) (z₁ z₂ : List E) (hz₁ : z₁.length = P.κ) (hz₂ : z₂.length = P.κ)
    (y₁ y₂ : E) (qs : List ℕ) (c' : ℕ → E) (lam batched : E)
    (hb : batched = ∑ k : Fin qs.length, lam ^ (k : ℕ) * c' qs[k])
    (hlam : ¬ ∃ U ∈ tlist P'.dom (rowsOf P'.ℓ (laneO (i + 1) cs P'.n)) (P'.thr 0) (P'.deg 0),
      ∑ x, gluedW (runW w ℓ₀ s) z₁ z₂ P.κ qs lam (bitsL x) * joinMsg hκ (msgT P'.κ U) x =
        gluedV s.claim y₁ y₂ qs c' lam) :
    RoundInv μ ℓ₀ w (i + 1) P' (pre + P.ℓ)
      (glueLevel s lam P.κ [z₁, z₂] [y₁, y₂] qs (powers lam qs.length) batched) [] cs := by
  obtain ⟨hlen, -, hκ₀, hg, -⟩ := hI
  have hgl := glueLevel_eq s lam P.κ z₁ z₂ y₁ y₂ qs (powers lam qs.length) batched
  refine ⟨by rw [hgl]; simp [hlen, hr], by simp, by omega, ?_, ?_⟩
  · intro c hc
    rw [hgl] at hc ⊢
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with hc | rfl | rfl | rfl
    · exact hg c hc
    · refine ⟨le_rfl, ?_⟩
      rw [show μ - s.gammas.length = z₁.length by omega]
      exact isMultiaffine_eqEval z₁
    · refine ⟨le_rfl, ?_⟩
      rw [show μ - s.gammas.length = z₂.length by omega]
      exact isMultiaffine_eqEval z₂
    · refine ⟨le_rfl, ?_⟩
      rw [show μ - s.gammas.length = P.κ by omega]
      exact isMultiaffine_inducedWeight P.κ qs _ (length_powers _ _)
  · intro U hU hag heq
    refine hlam ⟨U, (mem_tlist _ _ _ _ _).mpr ⟨hU, by simpa [foldsA_nil] using hag⟩, ?_⟩
    change claimSum _ (msgT P'.κ U) = _ at heq
    rw [← sum_joinMsg hκ] at heq
    simp only [runW_glueLevel] at heq
    rw [heq, hgl, hb, gluedV]

/-! ## The groups' escapes -/

/-- The two out-of-domain points as two tuples. -/
theorem sampleOodPoints_two (mu : ℕ) :
    sampleOodPoints mu 2 = (sampleChallenges mu).bind fun p₁ ↦
      (sampleChallenges mu).bind fun p₂ ↦ VerifierProgram.ret [p₁, p₂] := by
  simp only [sampleOodPoints, bind_eq, pure_eq, VerifierProgram.bind_assoc, ret_bind]

/-- **The out-of-domain group's expectation**, for a function of the points alone. -/
theorem retExp_oodPoints (G : List (List E) → ENNReal) (mu : ℕ) (h₀ : List Ev) :
    retExp (fun pts _ ↦ G pts) h₀ [] (sampleOodPoints mu 2) =
      (Fintype.card E : ENNReal)⁻¹ ^ mu * ∑ f₁ : Fin mu → E,
        (Fintype.card E : ENNReal)⁻¹ ^ mu * ∑ f₂ : Fin mu → E, G [List.ofFn f₁, List.ofFn f₂] := by
  rw [sampleOodPoints_two, retExp_bind]
  have hin : ∀ (p₁ : List E) (h : List Ev),
      retExp (fun pts _ ↦ G pts) h [] ((sampleChallenges mu).bind fun p₂ ↦
        VerifierProgram.ret [p₁, p₂]) =
      (Fintype.card E : ENNReal)⁻¹ ^ mu * ∑ f₂ : Fin mu → E, G [p₁, List.ofFn f₂] := by
    intro p₁ h
    rw [retExp_bind]
    have : (fun a (h' : List Ev) ↦ retExp (fun pts _ ↦ G pts) h' [] (VerifierProgram.ret [p₁, a])) =
        fun a _ ↦ G [p₁, a] := by
      funext a h'; simp [retExp]
    rw [this]
    exact retExp_sampleN (fun v ↦ G [p₁, v]) mu h []
  simp only [hin]
  exact retExp_sampleN (fun v ↦ (Fintype.card E : ENNReal)⁻¹ ^ mu *
    ∑ f₂ : Fin mu → E, G [v, List.ofFn f₂]) mu h₀ []

open Classical in
/-- **The out-of-domain group's escape**: a predicate of the points and the commitments breaks
at most on the pairs of `bad`. -/
theorem escRet_oodPoints_le (Q : List (List E) → List (ℕ × ℕ × Word) → Prop) (mu : ℕ)
    (h₀ : List Ev) (bad : Finset ((Fin mu → E) × (Fin mu → E)))
    (hbad : ∀ f₁ f₂, ¬ Q [List.ofFn f₁, List.ofFn f₂] (commits h₀) → (f₁, f₂) ∈ bad) :
    escRet (fun pts h ↦ Q pts (commits h)) h₀ [] (sampleOodPoints mu 2) ≤
      (Fintype.card E : ENNReal)⁻¹ ^ mu * (Fintype.card E : ENNReal)⁻¹ ^ mu * bad.card := by
  unfold escRet
  have hc := retExp_commits (fun a cs ↦ if Q a cs then (0 : ENNReal) else 1)
    (sampleOodPoints mu 2) h₀ []
  rw [hc, List.append_nil, retExp_oodPoints (fun pts ↦ if Q pts (commits h₀) then 0 else 1)]
  simp only [← Finset.mul_sum, ← mul_assoc]
  gcongr
  rw [← Fintype.sum_prod_type' (f := fun f₁ f₂ ↦
    if Q [List.ofFn f₁, List.ofFn f₂] (commits h₀) then (0 : ENNReal) else 1)]
  calc ∑ p : (Fin mu → E) × (Fin mu → E),
        (if Q [List.ofFn p.1, List.ofFn p.2] (commits h₀) then (0 : ENNReal) else 1)
      ≤ ∑ p : (Fin mu → E) × (Fin mu → E), (if p ∈ bad then (1 : ENNReal) else 0) :=
        Finset.sum_le_sum fun p _ ↦ by
          by_cases hq : Q [List.ofFn p.1, List.ofFn p.2] (commits h₀)
          · simp [hq]
          · simp [hq, hbad p.1 p.2 hq]
    _ = bad.card := by rw [Finset.sum_boole]; simp

open Classical in
/-- **The query group's escape**: if the positions breaking a predicate (in range, `t` of
them) all lie in `S`, its escape is at most `(|S| / 2^depth)^t`. -/
theorem escRet_queries_le (Q : List ℕ → List (ℕ × ℕ × Word) → Prop) (depth t : ℕ)
    (h1 : 1 ≤ depth) (h128 : depth ≤ 128) (h₀ : List Ev) (S : ℕ → Prop) [DecidablePred S]
    (hS : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ depth) → qs.length = t → ¬ Q qs (commits h₀) →
      ∀ q ∈ qs, S q) :
    escRet (fun qs h ↦ Q qs (commits h)) h₀ [] (sampleQueries depth t) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t := by
  unfold escRet
  have hc := retExp_commits (fun a cs ↦ if Q a cs then (0 : ENNReal) else 1)
    (sampleQueries depth t) h₀ []
  rw [hc, List.append_nil, sampleQueries,
    retExp_sampleQueriesAux_restrict_len depth h1 h128 _ t t le_rfl]
  refine le_trans (retExp_mono (g' := fun qs _ ↦ allIn S qs) (fun qs _ ↦ ?_) _ _ _)
    (retExp_sampleQueries_le depth t h1 h128 S h₀ [])
  split_ifs with hr hQ <;> simp only [allIn, zero_le]
  · split_ifs with hall
    · exact le_rfl
    · exact absurd (hS qs hr.1 hr.2 hQ) hall

end
end LeanVM.Protocol.Whir.Sound
