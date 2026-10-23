/-
  LeanVM.Protocol.Whir.Sound.LevelMidSpec

  The doom-calculus specification of a WHIR level with a next commitment.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelMid

/-!
# The specification of a level with a next commitment

`midSpec`: from `LevelPre` of level `i` (`A(i, 0)` for the running claim against the list of the
level's oracle), the level's groups escape with probability at most

* `eFold P ℓ` at each fold challenge,
* `eOod P' κ` at the out-of-domain point,
* `eQuery P P' t`, discounted by the proof of work `2^-17`, at the query group,

and the level hands `LevelPre` of level `i + 1` to the next level's specification `K`. The
hypotheses `MidHyp` are the arithmetic of the ladder: the level's code has the message variables
left after its folds, and the next code those after the next level's.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Prog Finset

@[expose] public section

/-- The arithmetic of a level with a next level. -/
structure MidHyp (μ ℓ₀ : ℕ) (w : List E → E) (P P' : LevelCode) (level next : Whir.Level)
    (pre : ℕ) : Prop where
  hw : IsMultiaffine μ w
  hℓ₀ : ℓ₀ ≤ μ
  hP : P.κ + pre + level.fold = μ
  hP' : P'.κ + (pre + level.fold) + next.fold = μ
  hR : P.R = level.logInvRate
  hR' : P'.R = next.logInvRate

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {level next : Whir.Level}
  {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, followed by the query intro polynomial and
the next level. -/
noncomputable def midQuerySpec (H : MidHyp μ ℓ₀ w P P' level next pre)
    (hQlt : eQuery P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevels μ ℓ₀ w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s' (commits h))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirState × List E) (z : List E) (y : E) (hy : List E) :
    Spec ((queryFrag (μ - r.1.folds.length + level.logInvRate) level.queries i).bind fun g ↦
        midFinish μ ℓ₀ w i next rest r z y hy g.1 g.2.1 g.2.2)
      (fun h ↦ QuadOK hy y ∧ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (commits h))
      (fun _ _ ↦ False) εmax (eQuery P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFrag (μ - r.1.folds.length + level.logInvRate) level.queries i)
      (Pre := fun h ↦ QuadOK hy y ∧ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (commits h))
      (Post := fun g h ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r z y hy g (commits h))
      (εmax := εmax) (T := 0) (noMoves_queryFrag _ _ _).noMove hQlt fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, hlo, haf⟩ := midC_word hp.2.1
        have hκm := afterFold_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hκ' : P.κ = next.fold + P'.κ := by have := H.hP; have := H.hP'; omega
        have hlf : r.2.length = level.fold := haf.2
        have hviol : Viol P (fun _ : Fin 0 → Bool ↦ fun v ↦ foldsN r.2 (laneO i cs₀ P.n) 0 v)
            (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        rw [hd]
        refine escRet_queryFrag_le P P' hκ' level.queries i h₀ hW
          (rowsOf next.fold (laneO (i + 1) (commits h₀) P'.n)) _ (runW w ℓ₀ r.1) r.1.target z y
          hviol hp.2.2.2 _ fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueMid_runW, glueMid_target, enfOf_eq haf.1.2 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun g ↦
    (roundPolyInv (GlueC μ ℓ₀ w i P P' level.fold next.fold pre r z y hy g)
        (enfOf i r.2 g.1 g.2.1 g.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq)).mono
        (fun h hp ↦ levelPre_next H.hP' r z y hy g hq (commits h) hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level. -/
noncomputable def midTailSpec (H : MidHyp μ ℓ₀ w P P' level next pre)
    (hεO : eOod P' P.κ ≤ εmax) (hOlt : eOod P' P.κ < 1) (hQlt : eQuery P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevels μ ℓ₀ w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s' (commits h))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirState × List E) :
    Spec (midTail μ ℓ₀ w i level next rest r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (commits h)) (fun _ _ ↦ False) εmax 0 0 :=
  (commitInv (AfterFold μ ℓ₀ w i P level.fold pre r)
      (MidC μ ℓ₀ w i P P' level.fold next.fold pre r)
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun _ _ h hW ↦ midC_of_commit next rfl H.hP' H.hR' h hW) (T := eOod P' P.κ) hεO).bind'
    fun _ ↦
  ((Spec.ofNoMove (p := sampleN (μ - r.1.folds.length))
      (Pre := fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (commits h))
      (Post := fun z h ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (commits h))
      (εmax := εmax) (T := 0) (noMoves_sampleN _).noMove hOlt fun h₀ hp ↦ by
        obtain ⟨cs₀, -, -, -, haf⟩ := midC_word hp
        have hκm := afterFold_κ haf
        have hκ : μ - r.1.folds.length = next.fold + P'.κ := by
          rw [hκm]; have := H.hP; have := H.hP'; omega
        have hκ1 : 1 ≤ μ - r.1.folds.length := by rw [hκm]; exact P.hκ
        refine (escRet_sampleN_le P' hκ hκ1 (rowsOf next.fold (laneO (i + 1) (commits h₀) P'.n))
          (fun z cs ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z cs) h₀
          fun z hz hsep ↦ ⟨hp, hz.trans hκm, hsep⟩).trans (by rw [hκm])).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun z ↦
  (readInv (OodC μ ℓ₀ w i P P' level.fold next.fold pre r z) (T := 0) zero_le).bind' fun y ↦
  (roundPolyInv (OodC μ ℓ₀ w i P P' level.fold next.fold pre r z) y (T := 0) zero_le).bind'
    fun hy ↦
  (grindInv (fun cs ↦ QuadOK hy y ∧ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z cs)
      Whir.queryGrindingBits (T := eQuery P P' level.queries) hεQ).bind' fun _ ↦
  (midQuerySpec H hQlt K r z y hy).congr
    (query_bind i (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinish μ ℓ₀ w i next rest r z y hy qs lam words).symm

/-- **The specification of a level with a next level.** -/
noncomputable def midSpec (H : MidHyp μ ℓ₀ w P P' level next pre)
    (hεF : eFold P level.fold ≤ εmax)
    (hεO : eOod P' P.κ ≤ εmax) (hOlt : eOod P' P.κ < 1) (hQlt : eQuery P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevels μ ℓ₀ w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s' (commits h))
      (fun _ _ ↦ False) εmax εmax 0)
    (s : WhirState) :
    Spec (whirLevels μ ℓ₀ w i (level :: next :: rest) s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (commits h)) (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (ShapeOK i P level.fold) H.hw H.hℓ₀ hεF
      level.fold s []).bind' fun r ↦ midTailSpec H hεO hOlt hQlt hεQ K r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevels_mid μ ℓ₀ w i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
