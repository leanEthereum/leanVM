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

`whirLevels` on `[level]` (`crates/verifier/src/whir.rs:273-299`): the level's fold rounds, then
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
  readScalars (2 ^ (logN - s.alphas.length) + level.fold) >>= fun folded ↦
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  (sampleQueries (logN - s.alphas.length + level.logInvRate) level.queries >>= fun qs ↦
    queryOpenings index qs >>= fun words ↦
    VerifierProgram.require ((List.zip qs words).all fun (qq, row) ↦
      foldRow (lanesOf index row) (K.ofBits qq) rounds =
        novelEval folded (subspaceAt (logN - s.alphas.length) (K.ofBits qq)))) >>= fun _ ↦
  sumcheck s.claim 3 (List.replicate (logN - s.alphas.length) none) >>= fun r ↦
  VerifierProgram.require (s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.alphas ++ r.1).drop glued.foldStart))
      (eb ((s.alphas ++ r.1).drop laneFolds ++ (s.alphas ++ r.1).take laneFolds)) *
    multilinearEval (folded.take (2 ^ (logN - s.alphas.length))) r.1 = r.2)

theorem whirLevels_final (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ)
    (level : Whir.Level) (s : WhirState) :
    whirLevels logN laneFolds eb index [level] s =
      foldRounds level.fold s >>= fun r ↦ finalTail logN laneFolds eb index level r.1 r.2 := by
  simp only [whirLevels, finalTail, bind_eq, VerifierProgram.bind_assoc]
  rfl

/-! ## The terminal weight -/

/-- The verifier's terminal weight is the running weight at the tail point. -/
theorem terminal_weight (eb : List E → E) (laneFolds : ℕ) (s : WhirState)
    (hg : ∀ g ∈ s.glued, g.foldStart ≤ s.alphas.length) (tail : List E) :
    s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.alphas ++ tail).drop glued.foldStart))
      (eb ((s.alphas ++ tail).drop laneFolds ++ (s.alphas ++ tail).take laneFolds)) =
    runW eb laneFolds s tail := by
  rw [runW_eq, foldl_add_map]
  refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun g hgm ↦ ?_))
  rw [List.drop_append_of_le_length (hg g hgm)]

/-! ## The final query step -/

/-- **The final query step**: unless the lane's low part violates the running claim, the lane
agrees with the folded word on fewer than `A` columns. -/
theorem final_agree (P : LevelCode) (hA : 1 ≤ P.A) (hℓκ : P.ℓ ≤ 2 ^ P.κ) (C : Fin P.n → E)
    (Φ : List E → E) (σ : E) (folded : List E) (hlen : folded.length = 2 ^ P.κ + P.ℓ)
    (hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) Φ σ (P.thr P.ℓ) P.deg) :
    ∃ S : Finset (Fin P.n), S.card + 1 ≤ P.A ∧
      (∑ x : Fin P.κ → Bool, Φ (bitsL x) * folded.getD (bitsToNat x) 0 = σ →
        ∀ v : Fin P.n, (polyOf folded).eval (P.dom v) = C v → v ∈ S) := by
  classical
  have h64 := P.κ_lt
  have hlow : lowMsg P.κ (polyOf folded) = fun u ↦ folded.getD (bitsToNat u) 0 := by
    rw [polyOf_split h64 folded hlen hℓκ, lowMsg_msgPoly_add_hat (by omega)]
  have hdeg : DegLE P.deg (fun _ : Fin 0 → Bool ↦ polyOf folded) := fun _ ↦ by
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

/-! ## The specification -/

/-- A specification whose program never returns in doom admits any follower's allowance. -/
def anyT {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {εmax L T : ENNReal}
    (S : Spec p Pre (fun _ _ ↦ False) εmax L T) (T' : ENNReal) :
    Spec p Pre (fun _ _ ↦ False) εmax L T' :=
  { S with retDoom := fun hl ha hD ↦ (S.post hl ha hD).elim }

/-- A claim on no message bits is a sum over the lanes. -/
theorem claimSum_msg0 {n : ℕ} (Φ : List E → E) (g : (Fin n → Bool) → (Fin 0 → Bool) → E) :
    claimSum Φ g = ∑ u, Φ (bitsL u) * g u Fin.elim0 := by
  rw [claimSum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Fintype.sum_eq_single (Fin.elim0 : Fin 0 → Bool) fun x hx ↦
    absurd (_root_.funext fun i ↦ Fin.elim0 i) hx]
  simp

theorem mem_zip_map_self {α β : Type} (W : α → β) {qs : List α} {q : α} (hq : q ∈ qs) :
    (q, W q) ∈ List.zip qs (qs.map W) := by
  induction qs with
  | nil => simp at hq
  | cons a qs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · exact Or.inr (ih hq)

/-- **The final level**: the code relations and the groups' escapes within `εmax`. -/
structure FinalOK (P : LevelCode) (t : ℕ) (εmax : ENNReal) : Prop where
  hℓκ : P.ℓ ≤ 2 ^ P.κ
  hA : 1 ≤ P.A
  eQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P t ≤ εmax
  eQ1 : eQuery P t < 1
  eT : eTail ≤ εmax

section Spec

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (pre : ℕ)

open Classical in
/-- **The final level after its fold rounds**: the query group escapes within `εmax` after its
grind, each tail round within `εmax`, and the terminal check fails. -/
noncomputable def finalTailSpec {εmax : ENNReal} (level : Whir.Level) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (hlev : level.fold = P.ℓ ∧ level.logInvRate = P.R)
    (F : FinalOK P level.queries εmax) (s : WhirState) (rounds : List FoldRound) :
    Spec (finalTail μ ℓ₀ w i level s rounds)
      (fun h ↦ (RoundInv μ ℓ₀ w i P pre s rounds (commits h) ∧
        (ShapeOK i P (commits h) ∧ (commits h).length = i + 1)) ∧ rounds.length = P.ℓ)
      (fun _ _ ↦ False) εmax 0 0 :=
  if hmu : μ - s.alphas.length = P.κ ∧ rounds.length = P.ℓ ∧ GluedOK μ s ∧
      s.alphas.length ≤ μ then
  let I : CInv := fun cs ↦ (RoundInv μ ℓ₀ w i P pre s rounds cs ∧
    (ShapeOK i P cs ∧ cs.length = i + 1)) ∧ rounds.length = P.ℓ
  let res := fun folded : List E ↦ folded.take (2 ^ (μ - s.alphas.length))
  (readNInv I (T := 0) zero_le (2 ^ (μ - s.alphas.length) + level.fold)).bind' fun folded ↦
  (grindInv (fun cs ↦ folded.length = 2 ^ (μ - s.alphas.length) + level.fold ∧ I cs)
    (b := Whir.queryGrindingBits) (by decide) (T := eQuery P level.queries + 0)
    (by simpa using F.eQ)).bind' fun _ ↦
  (Spec.ofNoMove (Pre := fun h ↦ folded.length = 2 ^ (μ - s.alphas.length) + level.fold ∧
      I (commits h))
    (Post := fun _ _ ↦ TailInv (runW w ℓ₀ s) (res folded) [] (μ - s.alphas.length) s.claim)
    (T := 0)
    ((noMoves_sampleQueriesAux _ _ _).bind fun _ ↦ (noMoves_queryP _ _).bind fun _ ↦ by
      unfold VerifierProgram.require; split
      · exact NoMoves.ret _
      · exact NoMoves.fail).noMove F.eQ1 fun h₀ hp ↦ by
      obtain ⟨hfl, ⟨hR, ⟨W, hW, hWl⟩, hlen⟩, hr⟩ := hp
      have hκ := hmu.1
      have hres : (res folded).length = 2 ^ (([] : List E).length + (μ - s.alphas.length)) := by
        simp only [res, List.length_take, hfl, List.length_nil, zero_add]; omega
      have hma : IsMultiaffine (([] : List E).length + (μ - s.alphas.length)) (runW w ℓ₀ s) := by
        simpa using isMultiaffine_runW hw hℓ₀ s hmu.2.2.2 hmu.2.2.1
      set C : Fin P.n → E := fun v ↦ foldsA P.dom rounds (laneO i (commits h₀) P.n) 0 v
      have hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) (runW w ℓ₀ s) s.claim
          (P.thr P.ℓ) P.deg := by
        have h5 := hR.2.2.2.2
        rw [tviol_rowsOf_congr (show P.ℓ - rounds.length = 0 by omega), hr] at h5
        have hrow : rowsOf 0 (foldsA P.dom rounds (laneO i (commits h₀) P.n)) =
            fun _ : Fin 0 → Bool ↦ C := by
          funext u v
          simp [rowsOf, C, bitsToNat]
        rwa [hrow] at h5
      obtain ⟨S, hScard, hSq⟩ := final_agree P F.hA F.hℓκ C (runW w ℓ₀ s) s.claim folded
        (by rw [hfl, hκ, hlev.1]) hviol
      have hdepth : 1 ≤ P.κ + P.R := by have := P.hR; omega
      have hW' : (commits h₀)[i]? = some (P.κ + P.R, wdOf i P.ℓ, W) := hW
      rw [hκ, hlev.2]
      refine (escRet_queryCheck_le (fun _ ↦ TailInv (runW w ℓ₀ s) (res folded) [] P.κ s.claim)
        i (P.κ + P.R) level.queries hdepth (by have := P.h64; omega) h₀ hW' _
        (fun j ↦ ∃ h : j < P.n, (⟨j, h⟩ : Fin P.n) ∈ S) fun qs hqs _ hch hT q hq ↦ ?_).trans ?_
      · refine ⟨hqs q hq, hSq ?_ ⟨q, hqs q hq⟩ ?_⟩
        · by_contra hne
          refine hT ⟨by rw [← hκ]; exact hres, by rw [← hκ]; exact hma, ?_⟩
          rw [claimSum_msg0]
          intro heq
          apply hne
          rw [← heq]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          simp only [List.nil_append, tailMsg, foldsN, List.foldl_nil, resO, res, hκ]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt (bitsToNat_lt u)]
        · have hrow := (List.all_eq_true.mp hch) (q, W q) (mem_zip_map_self W hq)
          have hlanes : (lanesOf i (W q)).length = 2 ^ rounds.length := by
            rw [hr]; exact length_lanesOf _ (hWl q)
          simp only [decide_eq_true_eq] at hrow
          rw [foldRow_eq _ rounds _ hlanes, novelEval_eq P.κ_lt folded (by
            have := F.hℓκ; rw [hfl, hκ, hlev.1, pow_succ]; omega)] at hrow
          show (polyOf folded).eval (ofK (K.ofBits q)) = C ⟨q, hqs q hq⟩
          rw [← hrow]
          simp only [C, foldsA, laneO, wordOf_eq hW']
          rfl
      · rw [eQuery, Nat.cast_pow, Nat.cast_ofNat]
        gcongr
        have : (univ.filter fun j : Fin (2 ^ (P.κ + P.R)) ↦
            ∃ h : (j : ℕ) < P.n, (⟨j, h⟩ : Fin P.n) ∈ S).card ≤ P.A - 1 := by
          refine le_trans (card_le_card fun j hj ↦ ?_) (by omega : S.card ≤ P.A - 1)
          obtain ⟨-, h, hjS⟩ := mem_filter.mp hj
          exact hjS
        exact_mod_cast this).bind' fun _ ↦
  (tailSpec (runW w ℓ₀ s) (res folded) F.eT (μ - s.alphas.length) [] s.claim).bind' fun x ↦
  Spec.require fun _ hp hc ↦ by
    rw [terminal_weight w ℓ₀ s (fun g hg ↦ (hmu.2.2.1 g hg).1)] at hc
    exact tailDone_ne _ _ hp (by simpa using hc)
  else Spec.dead.mono (fun h hp ↦ hmu ⟨by
      obtain ⟨⟨⟨hlen, -, hκ, -⟩, -⟩, hr⟩ := hp
      omega, hp.2, hp.1.1.2.2.2.1, by
      obtain ⟨⟨⟨hlen, -, hκ, -⟩, -⟩, hr⟩ := hp
      omega⟩) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Spec

end
end LeanVM.Protocol.Whir.Sound
