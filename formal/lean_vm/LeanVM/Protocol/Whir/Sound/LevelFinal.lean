/-
  LeanVM.Protocol.Whir.Sound.LevelFinal

  The specification of the final WHIR level: the fold rounds, the folded lane in the clear, the
  query group after its grind (positions, openings, the check of each row against the lane), the
  tail sumcheck and the terminal check.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelMid
public import LeanVM.Protocol.Whir.Sound.Tail

/-!
# The final level

`whirLevels` on `[level]` (`crates/verifier/src/whir.rs:273-301`): the level's fold rounds, then
`finalTail`: the folded lane's `2^μ + ℓ` coefficients, a `17`-bit grind, the positions, their
rows and the check that each row folds to the lane's value at its point (one group, `eQuery`),
the tail sumcheck on the lane's low part (`tailSpec`), and the terminal check, which fails.

The query group's doom is `TailInv` with no tail challenge: if the lane `P` agrees with the folded
word on at least `A` columns it violates the running claim, and so does its low part; otherwise a
position off their agreement set fails the check.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset Polynomial

@[expose] public section

/-! ## The query group -/

open Classical in
/-- **A group of positions, openings and a check**: if every position list (in range, `t` of
them) whose rows pass the check while the commitments break `Post` lies in `S`, the group
escapes `Post` with probability at most `(|S| / 2^depth)^t`. -/
theorem escRet_queryCheck_le (Post : List (ℕ × ℕ × Word) → Prop) (i depth t : ℕ)
    (h1 : 1 ≤ depth) (h128 : depth ≤ 128) (h₀ : List Ev) {wd : ℕ} {W : Word}
    (hc : (commits h₀)[i]? = some (depth, wd, W))
    (check : List ℕ → List (List K) → Prop) [∀ qs words, Decidable (check qs words)]
    (S : ℕ → Prop) [DecidablePred S]
    (hS : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ depth) → qs.length = t → check qs (qs.map W) →
      ¬ Post (commits h₀) → ∀ q ∈ qs, S q) :
    escRet (fun _ h ↦ Post (commits h)) h₀ []
      (sampleQueries depth t >>= fun qs ↦ queryOpenings i qs >>= fun words ↦
        VerifierProgram.require (check qs words)) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t := by
  unfold escRet
  rw [bind_eq, retExp_bind]
  let G : List ℕ → List (ℕ × ℕ × Word) → ENNReal := fun qs cs ↦
    match cs[i]?.map fun c ↦ qs.map fun p ↦ c.2.2 (p % 2 ^ c.1) with
    | some rows => if check qs rows then (if Post cs then 0 else 1) else 0
    | none => 0
  have hin : ∀ qs h, retExp (fun _ h ↦ if Post (commits h) then (0 : ENNReal) else 1) h []
      (queryOpenings i qs >>= fun words ↦ VerifierProgram.require (check qs words)) =
      G qs (commits h) := by
    intro qs h
    rw [bind_eq, retExp_bind, retExp_queryP, List.append_nil]
    simp only [answer, G]
    split
    · rename_i rows hr
      rw [hr]
      simp only [VerifierProgram.require]
      split_ifs <;> simp_all [retExp, commits_append_query]
    · rename_i hr
      rw [hr]
  simp only [hin]
  rw [retExp_commits G, List.append_nil, sampleQueries,
    retExp_sampleQueriesAux_restrict_len depth h1 h128 _ t t le_rfl]
  refine le_trans (retExp_mono (g' := fun qs _ ↦ allIn S qs) (fun qs _ ↦ ?_) _ _ _)
    (retExp_sampleQueries_le depth t h1 h128 S h₀ [])
  split_ifs with hr
  · simp only [G, hc, Option.map_some]
    have hmap : (qs.map fun p ↦ W (p % 2 ^ depth)) = qs.map W :=
      List.map_congr_left fun q hq ↦ by rw [Nat.mod_eq_of_lt (hr.1 q hq)]
    rw [hmap]
    split_ifs with hch hP <;> simp only [allIn, zero_le]
    split_ifs with hall
    · exact le_rfl
    · exact absurd (hS qs hr.1 hr.2 hch hP) hall
  · exact zero_le

/-! ## The program -/

/-- The final level after its fold rounds. -/
def finalTail (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) : VerifierProgram Unit :=
  readScalars (2 ^ (logN - s.gammas.length) + level.fold) >>= fun folded ↦
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  (sampleQueries (logN - s.gammas.length + level.logInvRate) level.queries >>= fun qs ↦
    queryOpenings index qs >>= fun words ↦
    VerifierProgram.require ((List.zip qs words).all fun (qq, row) ↦
      foldRow (lanesOf index row) (K.ofBits qq) rounds =
        novelEval folded (subspaceAt (logN - s.gammas.length) (K.ofBits qq)))) >>= fun _ ↦
  sumcheck s.claim 3 (List.replicate (logN - s.gammas.length) none) >>= fun r ↦
  VerifierProgram.require (s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.gammas ++ r.1).drop glued.foldStart))
      (eb ((s.gammas ++ r.1).drop laneFolds ++ (s.gammas ++ r.1).take laneFolds)) *
    multilinearEval (folded.take (2 ^ (logN - s.gammas.length))) r.1 = r.2)

theorem whirLevels_final (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ)
    (level : Whir.Level) (s : WhirState) :
    whirLevels logN laneFolds eb index [level] s =
      foldRounds level.fold s >>= fun r ↦ finalTail logN laneFolds eb index level r.1 r.2 := by
  simp only [whirLevels, finalTail, bind_eq, VerifierProgram.bind_assoc]
  rfl

/-! ## The terminal weight -/

/-- The verifier's terminal weight is the running weight at the tail point. -/
theorem terminal_weight (eb : List E → E) (laneFolds : ℕ) (s : WhirState)
    (hg : ∀ g ∈ s.glued, g.foldStart ≤ s.gammas.length) (tail : List E) :
    s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.gammas ++ tail).drop glued.foldStart))
      (eb ((s.gammas ++ tail).drop laneFolds ++ (s.gammas ++ tail).take laneFolds)) =
    runW eb laneFolds s tail := by
  rw [runW_eq, foldl_add_map]
  refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun g hgm ↦ ?_))
  rw [List.drop_append_of_le_length (hg g hgm)]

/-! ## The final query step -/

/-- **The final query step**: unless the lane's low part violates the running claim, the lane
agrees with the folded word on fewer than `A` columns. -/
theorem final_agree (P : LevelCode) (hA : 1 ≤ P.A) (hℓκ : P.ℓ ≤ 2 ^ P.κ) (C : Fin P.n → E)
    (Φ : List E → E) (σ : E) (folded : List E) (hlen : folded.length = 2 ^ P.κ + P.ℓ)
    (hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) Φ σ (P.thr P.ℓ) (P.deg P.ℓ)) :
    ∃ S : Finset (Fin P.n), S.card + 1 ≤ P.A ∧
      (∑ x : Fin P.κ → Bool, Φ (bitsL x) * folded.getD (bitsToNat x) 0 = σ →
        ∀ v : Fin P.n, (polyOf folded).eval (P.dom v) = C v → v ∈ S) := by
  classical
  have h64 := P.κ_lt
  have hlow : lowMsg P.κ (polyOf folded) = fun u ↦ folded.getD (bitsToNat u) 0 := by
    rw [polyOf_split h64 folded hlen hℓκ, lowMsg_msgPoly_add_hat (by omega)]
  have hdeg : DegLE (P.deg P.ℓ) (fun _ : Fin 0 → Bool ↦ polyOf folded) := fun _ ↦ by
    have := natDegree_polyOf_le folded (by
      rw [hlen]
      calc 2 ^ P.κ + P.ℓ ≤ 2 ^ P.κ + 2 ^ P.κ := by omega
        _ = 2 ^ (P.κ + 1) := by ring
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 := Nat.one_le_two_pow (n := P.κ)
    rw [hlen, max_eq_left (by omega)] at this
    simp only [LevelCode.deg]
    omega
  set S := agreeT P.dom (fun _ : Fin 0 → Bool ↦ polyOf folded) (fun _ ↦ C)
  by_cases hS : P.A ≤ S.card
  · refine ⟨∅, by simpa using hA, fun heq ↦ absurd ?_ (hviol _ hdeg (by simpa [LevelCode.thr] using hS))⟩
    rw [tclaim, claimSum_zero, hlow]
    exact heq
  · refine ⟨S, by omega, fun _ v hv ↦ ?_⟩
    rw [mem_agreeT]
    exact fun _ ↦ hv

end
end LeanVM.Protocol.Whir.Sound
