/-
  LeanVM.Protocol.Whir.Sound.LevelFinal

  The specification of the final WHIR level: the fold rounds, the residual, the proof of work,
  the query group with `λ`, the tail rounds and the terminal check.
-/

module

public import LeanVM.Protocol.Whir.Sound.Tail

/-!
# The final level

`whirLevels μ ℓ₀ w i [level] s` is, definitionally, `finProg`: the fold rounds, the residual
`f_final` (`2^κ` scalars), the proof of work, positions, `λ`, opening, the query intro
polynomial, the glue (`λ^(1+q)` for the consistency claims), the tail rounds and the terminal
check `weight · multilinear_eval(f_final, tail) = target` (`verifier.py:1039-1086` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`).

Doom: `AfterFold` after the fold rounds (`A(r−1, ℓ)`); with the residual's length; after the query
group `GlueFinC`: `f_final` violates the glued claim (`escRet_queryFrag_le_final`); then the tail
invariant (`TailInv`, `tailSpec`) and the failing terminal check (`tailDone_ne`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Prog Finset

@[expose] public section

section Program

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (level : Whir.Level)

/-- The state glued on the final level. -/
def glueFin (r : WhirState × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) : WhirState :=
  glue lam r.1 ([] ++ [(enfOf i r.2 qs lam words, hq,
    fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x)])

/-- After the query group of the final level. -/
def finFinish (r : WhirState × List E) (residual : List E) (qs : List ℕ) (lam : E)
    (words : List (List K)) : Prog Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    (tailRounds (μ - r.1.folds.length) (glueFin μ i r qs lam words hq).target
      (glueFin μ i r qs lam words hq).quad).bind fun x ↦
      Prog.require (runW w ℓ₀ (glueFin μ i r qs lam words hq) x.1 *
        multilinearEval residual x.1 = x.2)

/-- After the fold rounds of the final level. -/
def finTail (r : WhirState × List E) : Prog Unit :=
  (readN (2 ^ (μ - r.1.folds.length))).bind fun residual ↦
  (grindP Whir.queryGrindingBits).bind fun _ ↦
  (sampleQueries (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleE.bind fun lam ↦ (queryP i qs).bind fun words ↦
    finFinish μ ℓ₀ w i r residual qs lam words

/-- The final level, unfolded. -/
def finProg (s : WhirState) : Prog Unit :=
  (foldRounds level.fold s []).bind fun r ↦ finTail μ ℓ₀ w i level r

/-- **`whirLevels` on the final level is `finProg`.** -/
theorem whirLevels_fin (s : WhirState) :
    whirLevels μ ℓ₀ w i [level] s = finProg μ ℓ₀ w i level s := rfl

end Program

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ)

/-- After the query group of the final level: the residual violates the glued claim. -/
def GlueFinC (r : WhirState × List E) (res : List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  (res.length = 2 ^ (μ - r.1.folds.length) ∧ AfterFold μ ℓ₀ w i P ℓ pre r cs) ∧
    ∑ x : Fin P.κ → Bool, runW w ℓ₀ (glueFin μ i r g.1 g.2.1 g.2.2 []) (bitsL x) * resMsg res x ≠
      (glueFin μ i r g.1 g.2.1 g.2.2 []).target

end Doom

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {ℓ pre : ℕ}

theorem glueFin_runW (r : WhirState × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    runW w ℓ₀ (glueFin μ i r qs lam words hq) = fun x ↦ runW w ℓ₀ r.1 x +
      1 * lam * Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x := by
  funext x
  rw [glueFin, List.nil_append, glue_one]
  have := runW_glue w ℓ₀ r.1 [⟨1 * lam, r.1.folds.length, fun x ↦ Verifier.inducedWeight
    (μ - r.1.folds.length) qs (powers lam qs.length) x⟩] (by simp) x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  exact this

theorem glueFin_target (r : WhirState × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    (glueFin μ i r qs lam words hq).target = r.1.target + 1 * lam * enfOf i r.2 qs lam words := by
  rw [glueFin, List.nil_append, glue_one]

/-- The tail's starting claim is the residual's inner product on the message cube. -/
theorem claimSum_tailMsg_nil {n κ : ℕ} (h : n = κ) (Φ : List E → E) (res : List E) :
    claimSum (fun r ↦ Φ ([] ++ r)) (tailMsg [] res n) =
      ∑ x : Fin κ → Bool, Φ (bitsL x) * resMsg res x := by
  subst h
  simp only [claimSum, List.nil_append, Fintype.sum_unique, bitsL_zero, List.append_nil]
  rfl

/-- **The tail invariant at the start of the tail.** -/
theorem tailInv_start (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (r : WhirState × List E)
    (res : List E) (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueFinC μ ℓ₀ w i P ℓ pre r res g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    TailInv ℓ₀ w (glueFin μ i r g.1 g.2.1 g.2.2 hq) res [] (μ - r.1.folds.length)
      (glueFin μ i r g.1 g.2.1 g.2.2 hq).target (glueFin μ i r g.1 g.2.1 g.2.2 hq).quad := by
  obtain ⟨⟨hres, haf⟩, hviol⟩ := hglue
  have hlen := afterFold_len haf
  have hκm := afterFold_κ haf
  obtain ⟨⟨⟨-, -, hκ, hg, hquad, -⟩, -⟩, -⟩ := haf
  have hgl : GluedOK μ (glueFin μ i r g.1 g.2.1 g.2.2 hq) := by
    intro c hc
    rw [glueFin, List.nil_append, glue_one] at hc ⊢
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with hc | rfl
    · exact hg c hc
    · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩
  have hfl : (glueFin μ i r g.1 g.2.1 g.2.2 hq).folds = r.1.folds := by
    rw [glueFin, List.nil_append, glue_one]
  refine ⟨by simpa using hres, ?_, ?_, ?_⟩
  · have := isMultiaffine_runW hw hℓ₀ _ (by rw [hfl]; omega) hgl
    rwa [hfl, List.length_nil, Nat.zero_add] at *
  · rw [glueFin, List.nil_append, glue_one]
    exact quadOK_zipWith hquad hhq _
  · rw [claimSum_tailMsg_nil hκm]
    have hr : runW w ℓ₀ (glueFin μ i r g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueFin μ i r g.1 g.2.1 g.2.2 []) := by rw [glueFin_runW, glueFin_runW]
    have ht : (glueFin μ i r g.1 g.2.1 g.2.2 hq).target =
        (glueFin μ i r g.1 g.2.1 g.2.2 []).target := by rw [glueFin_target, glueFin_target]
    rw [hr, ht]
    exact hviol

end Lemmas

/-! ## The specification -/

/-- The arithmetic of the final level. -/
structure FinHyp (μ ℓ₀ : ℕ) (w : List E → E) (P : LevelCode) (level : Whir.Level) (pre : ℕ) :
    Prop where
  hw : IsMultiaffine μ w
  hℓ₀ : ℓ₀ ≤ μ
  hP : P.κ + pre + level.fold = μ
  hR : P.R = level.logInvRate

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {level : Whir.Level} {pre : ℕ}
  {εmax : ENNReal}

/-- The query group of the final level, the tail and the terminal check. -/
noncomputable def finQuerySpec (H : FinHyp μ ℓ₀ w P level pre)
    (hQlt : eQueryFinal P level.queries < 1) (hεT : eTail ≤ εmax)
    (r : WhirState × List E) (res : List E) :
    Spec ((queryFrag (μ - r.1.folds.length + level.logInvRate) level.queries i).bind fun g ↦
        finFinish μ ℓ₀ w i r res g.1 g.2.1 g.2.2)
      (fun h ↦ res.length = 2 ^ (μ - r.1.folds.length) ∧
        AfterFold μ ℓ₀ w i P level.fold pre r (commits h))
      (fun _ _ ↦ False) εmax (eQueryFinal P level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFrag (μ - r.1.folds.length + level.logInvRate) level.queries i)
      (Pre := fun h ↦ res.length = 2 ^ (μ - r.1.folds.length) ∧
        AfterFold μ ℓ₀ w i P level.fold pre r (commits h))
      (Post := fun g h ↦ GlueFinC μ ℓ₀ w i P level.fold pre r res g (commits h))
      (εmax := εmax) (T := 0) (noMoves_queryFrag _ _ _).noMove hQlt fun h₀ hp ↦ by
        have haf := hp.2
        have hκm := afterFold_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hlf : r.2.length = level.fold := haf.2
        have hviol : Viol P (fun _ : Fin 0 → Bool ↦
            fun v ↦ foldsN r.2 (laneO i (commits h₀) P.n) 0 v) (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        rw [hd]
        refine escRet_queryFrag_le_final P level.queries i h₀ (shapeOK_word haf.1.2).1 _
          (runW w ℓ₀ r.1) r.1.target hviol (resMsg res) _ fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueFin_runW, glueFin_target, enfOf_eq haf.1.2 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun g ↦
    (roundPolyInv (GlueFinC μ ℓ₀ w i P level.fold pre r res g)
        (enfOf i r.2 g.1 g.2.1 g.2.2) (T := eTail) hεT).bind' fun hq ↦
      ((tailSpec ℓ₀ w (glueFin μ i r g.1 g.2.1 g.2.2 hq) res hεT (μ - r.1.folds.length) []
          (glueFin μ i r g.1 g.2.1 g.2.2 hq).target (glueFin μ i r g.1 g.2.1 g.2.2 hq).quad).mono
        (fun h hp ↦ tailInv_start H.hw H.hℓ₀ r res g hq (commits h) hp.2 hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun x ↦
        Spec.require fun _ hd hc ↦ tailDone_ne ℓ₀ w _ res (by simpa using hd) hc

/-- After the fold rounds of the final level. -/
noncomputable def finTailSpec (H : FinHyp μ ℓ₀ w P level pre)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (r : WhirState × List E) :
    Spec (finTail μ ℓ₀ w i level r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (commits h)) (fun _ _ ↦ False) εmax 0 0 :=
  (readNInv (AfterFold μ ℓ₀ w i P level.fold pre r) (T := 0) zero_le
      (2 ^ (μ - r.1.folds.length))).bind' fun res ↦
  (grindInv (fun cs ↦ res.length = 2 ^ (μ - r.1.folds.length) ∧
      AfterFold μ ℓ₀ w i P level.fold pre r cs) Whir.queryGrindingBits
      (T := eQueryFinal P level.queries) hεQ).bind' fun _ ↦
  (finQuerySpec H hQlt hεT r res).congr
    (query_bind i (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ finFinish μ ℓ₀ w i r res qs lam words).symm

/-- **The specification of the final level.** -/
noncomputable def finSpec (H : FinHyp μ ℓ₀ w P level pre)
    (hεF : eFold P level.fold ≤ εmax) (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (s : WhirState) :
    Spec (whirLevels μ ℓ₀ w i [level] s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (commits h)) (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (ShapeOK i P level.fold) H.hw H.hℓ₀ hεF
      level.fold s []).bind' fun r ↦ finTailSpec H hQlt hεQ hεT r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevels_fin μ ℓ₀ w i level s).symm

end
end LeanVM.Protocol.Whir.Sound
