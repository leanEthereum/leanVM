/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  The specification of a WHIR level with a next commitment: the fold rounds, the commitment of
  the next oracle, the out-of-domain group, the proof of work, the query group with `λ`, and the
  glued claim handed to the next level.
-/

module

public import LeanVM.Protocol.Whir.Sound.GroupEscape

/-!
# A level with a next commitment

`whirLevels μ ℓ₀ w i (level :: next :: rest) s` (`verify_whir`'s loop body,
`python-verifier/verifier.py:1018-1086` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is,
definitionally, `midProg`: the fold rounds, then `midTail` (commitment, out-of-domain point and
value with its intro polynomial, proof of work, positions, `λ`, opening, query intro polynomial,
glue, next level).

Doom along the level (all functions of the commitments `cs` of the history and of the values in
scope):

* `AfterFold r cs`: `A(i, ℓ)` for the state and challenges `r` returned by the fold rounds;
* `MidC r cs`: after the commitment of the next oracle (`cs = cs₀ ++ [next word]`);
* `OodC r z cs`: and the members of the next list are separated at `z`;
* `GlueC r z y hy g cs`: after the query group `g = (positions, λ, rows)`: every member of the next
  list violates the glued claim; with the query intro polynomial this is `LevelPre` of the next
  level (`levelPre_next`).

`midSpec` assembles the level from the fold rounds (`foldRoundsSpec`), the moves
(`LeanVM.Protocol.Whir.Sound.Generic`), the out-of-domain group (`escRet_sampleN_le`) and the
query group (`escRet_queryFrag_le`), given a specification of the next level.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Prog Finset

@[expose] public section

/-! ## The program -/

section Program

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- The enforced sum of a level's opened rows. -/
def enfOf (lf : List E) (qs : List ℕ) (lam : E) (words : List (List K)) : E :=
  enforcedSum (if i = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) lf
    (powers lam qs.length)

/-- The state glued at the end of a level with a next commitment. -/
def glueMid (r : WhirState × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ) (lam : E)
    (words : List (List K)) (hq : List E) : WhirState :=
  glue lam r.1 [(y, hy, fun x ↦ eqEval z x), (enfOf i r.2 qs lam words, hq,
    fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x)]

/-- After the query group: the query intro polynomial, then the next level. -/
def midFinish (r : WhirState × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ) (lam : E)
    (words : List (List K)) : Prog Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    whirLevels μ ℓ₀ w (i + 1) (next :: rest) (glueMid μ i r z y hy qs lam words hq)

/-- After the fold rounds. -/
def midTail (r : WhirState × List E) : Prog Unit :=
  (commitP (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)).bind fun _ ↦
  (sampleN (μ - r.1.folds.length)).bind fun z ↦ readE.bind fun y ↦
  (sumcheckRoundPoly 3 y none).bind fun hy ↦
  (grindP Whir.queryGrindingBits).bind fun _ ↦
  (sampleQueries (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleE.bind fun lam ↦ (queryP i qs).bind fun words ↦
    midFinish μ ℓ₀ w i next rest r z y hy qs lam words

/-- The level, unfolded. -/
def midProg (s : WhirState) : Prog Unit :=
  (foldRounds level.fold s []).bind fun r ↦ midTail μ ℓ₀ w i level next rest r

/-- **`whirLevels` on a level with a next commitment is `midProg`.** -/
theorem whirLevels_mid (s : WhirState) :
    whirLevels μ ℓ₀ w i (level :: next :: rest) s = midProg μ ℓ₀ w i level next rest s := rfl

/-- The query group as one fragment. -/
theorem query_bind (d t : ℕ) (K : List ℕ → E → List (List K) → Prog Unit) :
    ((sampleQueries d t).bind fun qs ↦ sampleE.bind fun lam ↦ (queryP i qs).bind fun words ↦
      K qs lam words) = (queryFrag d t i).bind fun g ↦ K g.1 g.2.1 g.2.2 := by
  simp only [queryFrag, bind_eq, Prog.bind_assoc, Prog.ret_bind]

end Program

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)

/-- After the fold rounds. -/
def AfterFold (r : WhirState × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (FoldInv μ ℓ₀ w i P ℓ pre r.1 r.2 cs ∧ ShapeOK i P ℓ cs) ∧ r.2.length = ℓ

/-- After the commitment of the next oracle. -/
def MidC (r : WhirState × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    AfterFold μ ℓ₀ w i P ℓ pre r cs₀

/-- After the out-of-domain point: the next list is separated at `z`. -/
def OodC (r : WhirState × List E) (z : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs ∧ z.length = P.κ ∧
    OodSep P' (rowsOf ℓ' (laneO (i + 1) cs P'.n)) z

/-- After the query group: every member of the next list violates the glued claim. -/
def GlueC (r : WhirState × List E) (z : List E) (y : E) (hy : List E)
    (g : List ℕ × E × List (List K)) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (QuadOK hy y ∧ OodC μ ℓ₀ w i P P' ℓ ℓ' pre r z cs) ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []))
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}

theorem afterFold_len {r : WhirState × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : r.1.folds.length = pre + ℓ := by
  obtain ⟨⟨⟨hl, -⟩, -⟩, hr⟩ := h
  omega

theorem afterFold_κ {r : WhirState × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : μ - r.1.folds.length = P.κ := by
  have := afterFold_len h
  obtain ⟨⟨⟨-, -, hκ, -⟩, -⟩, -⟩ := h
  omega

/-- The glued state's weight and target. -/
theorem glueMid_runW (r : WhirState × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    runW w ℓ₀ (glueMid μ i r z y hy qs lam words hq) = fun x ↦ runW w ℓ₀ r.1 x +
      1 * lam * eqEval z x + 1 * lam * lam *
        Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x := by
  funext x
  rw [glueMid, glue_two]
  have := runW_glue w ℓ₀ r.1 [⟨1 * lam, r.1.folds.length, fun x ↦ eqEval z x⟩,
    ⟨1 * lam * lam, r.1.folds.length, fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs
      (powers lam qs.length) x⟩] (by simp) x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  rw [← add_assoc] at this
  exact this

theorem glueMid_target (r : WhirState × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    (glueMid μ i r z y hy qs lam words hq).target =
      r.1.target + 1 * lam * y + 1 * lam * lam * enfOf i r.2 qs lam words := by
  rw [glueMid, glue_two]

/-- The enforced sum of the rows of commitment `i` at in-range positions. -/
theorem enfOf_eq {cs : List (ℕ × ℕ × Word)} (hshape : ShapeOK i P ℓ cs) (lf : List E)
    (hlf : lf.length = ℓ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n) (lam : E) :
    enfOf i lf qs lam (qs.map (wordOf cs i)) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) *
        wordAt (fun v : Fin P.n ↦ foldsN lf (laneO i cs P.n) 0 v) qs[k] := by
  rw [enfOf, rows_eq]
  exact enforcedSum_eq i cs lf hlf qs hqs lam fun q _ ↦ length_wordOf hshape q

/-- **The next level's doom** from the glued doom and the query intro polynomial. -/
theorem levelPre_next (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirState × List E) (z : List E)
    (y : E)
    (hy : List E) (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueC μ ℓ₀ w i P P' ℓ ℓ' pre r z y hy g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨hhy, ⟨cs₀, W', rfl, hW', haf⟩, hz, -⟩, hviol⟩ := hglue
  have hlen := afterFold_len haf
  have hκm := afterFold_κ haf
  obtain ⟨⟨⟨-, -, hκ, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', ?_, ?_, ?_⟩, ?_⟩
  · rw [glueMid, glue_two]; simp [hlen]
  · intro c hc
    rw [glueMid, glue_two] at hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rw [glueMid, glue_two]
    rcases hc with hc | rfl | rfl
    · exact hg c hc
    · refine ⟨le_rfl, ?_⟩
      rw [hκm, ← hz]
      exact isMultiaffine_eqEval z
    · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩
  · rw [glueMid, glue_two]
    exact quadOK_zipWith (quadOK_zipWith hquad hhy _) hhq _
  · have hr : runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []) := by
      rw [glueMid_runW, glueMid_runW]
    have ht : (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).target =
        (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target := by
      rw [glueMid_target, glueMid_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht]
    exact hviol
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

/-- After the commitment: the next oracle's word is appended. -/
theorem midC_of_commit {r : WhirState × List E} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (next : Whir.Level) (hℓ' : next.fold = ℓ') (hP' : P'.κ + (pre + ℓ) + ℓ' = μ)
    (hR' : P'.R = next.logInvRate) (h : AfterFold μ ℓ₀ w i P ℓ pre r cs)
    (hW : WellShaped (3 * 2 ^ next.fold) W) :
    MidC μ ℓ₀ w i P P' ℓ ℓ' pre r
      (cs ++ [(μ - r.1.folds.length - next.fold + next.logInvRate, 3 * 2 ^ next.fold, W)]) := by
  have hlen := afterFold_len h
  subst hℓ'
  refine ⟨cs, W, ?_, hW, h⟩
  congr 3
  omega

/-- The commitments after the next commitment, at index `i`. -/
theorem midC_word {r : WhirState × List E} {cs : List (ℕ × ℕ × Word)}
    (h : MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ wordOf cs i = wordOf cs₀ i ∧
      laneO i cs P.n = laneO i cs₀ P.n ∧ AfterFold μ ℓ₀ w i P ℓ pre r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, haf⟩ := h
  have hsh := haf.1.2
  have hi : i < cs₀.length := by rw [hsh.1]; omega
  exact ⟨cs₀, shapeOK_append hsh _, wordOf_append _ _ hi, laneO_append _ _ hi _, haf⟩

end Lemmas

end
end LeanVM.Protocol.Whir.Sound
