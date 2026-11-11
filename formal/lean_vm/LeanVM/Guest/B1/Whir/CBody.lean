/-
  LeanVM.Guest.B1.Whir.CBody

  The body of open_stacked before its ret, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CHead
public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.CFinish

/-!
# The body, honestly

`osBodyA_complete`: the head, the levels, the tail and the finish in sequence, on honest data for
each, at the values `bodyF`; the returns are the tail's claim, the point's two buffers, the inner
sum plus the out-of-domain sum, and the final message's value.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The state the levels leave. -/
abbrev osLvSt (c : OsCfg) : OsSt := (osLevels c 0 c.levels (osHead c).2).2

/-- The tail's statements, state and challenges' pointer. -/
abbrev osTlSt (c : OsCfg) : List Stmt × OsSt × ℕ := osTail c (osLvSt c)

/-- The body before its `ret`. -/
def osBodyAc (c : OsCfg) : List Stmt :=
  (osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++ (osTlSt c).1 ++
    osFinA c (osTlSt c).2.1 (osTlSt c).2.2

theorem osBody_splitC (c : OsCfg) :
    osBody c = osBodyAc c ++ [.ret (osFinRet c (osTlSt c).2.1 (osTlSt c).2.2)] := by
  simp only [osBody, osBodyAc, osFinish_splitC, List.append_assoc]

theorem osLvB_pad (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    ∃ p, (osLvB c lvl lv st).2.pad = some p := by
  unfold osLvB
  split_ifs <;> exact ⟨_, rfl⟩

theorem osLevels_padC (c : OsCfg) : ∀ (lvs : List OsLv) (lvl : ℕ) (s : OsSt), lvs ≠ [] →
    ∃ p, (osLevels c lvl lvs s).2.pad = some p
  | [], _, _, h => absurd rfl h
  | [lv], lvl, s, _ => by
    simp only [osLevels]
    rw [osLevel_splitC]; exact osLvB_pad _ _ _ _
  | lv :: lv' :: rest, lvl, s, _ => by
    simp only [osLevels]
    exact osLevels_padC c (lv' :: rest) (lvl + 1) _ (by simp)

/-- The sponge the head leaves. -/
def headSponge (σ : Val) (c0 c2 : E) : Fs :=
  ⟨[σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)], [(c0, dsObserve), (c2, dsObserve)]⟩

/-- What the levels leave, from the head's. -/
def bodyLvs (c : OsCfg) (σ : Val) (c0 c2 : E) (Ds : List LvDat) : Fs × List E × E × E :=
  lvsOut c 0 c.levels Ds (headSponge σ c0 c2) [c0, σ (.n 6) + c2, c2] (σ (.n 6))
    (σ (.n 9) * gen ^ 2)

theorem osTail_bounds (c : OsCfg) (st : OsSt) (hk : 161 ≤ st.k) :
    st.k ≤ (osTail c st).2.1.k ∧ 161 ≤ (osTail c st).2.1.k ∧
      (osTail c st).2.2 < (osTail c st).2.1.k ∧ (osTail c st).2.1.t < (osTail c st).2.1.k := by
  rw [osTail_eq]
  dsimp only
  have h : st.k + 2 ≤ (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k :=
    osFolds_k (st.k + 1) (c.yrLog - 1) 0 { st with k := st.k + 2 }
  omega

/-- The values of the body. -/
def bodyF (c : OsCfg) (σ : Val) (P : OsPtrs) (c0 c2 : E) (Ds : List LvDat) (T : E) (xs : List E)
    (Y PT PT1 BD LS ICH In : E) (Pp β : ℕ → E) (X : ℕ → ℕ → E) (M h I L : ℕ → E)
    (Λ : ℕ → E) (Z Yo : ℕ → ℕ → E) : ℕ → E :=
  seqF σ 10 161 (headF c σ P c0 c2) fun σ1 ↦
  seqF σ1 161 (osLvSt c).k (lvsF c 0 c.levels Ds (osHead c).2 σ1) fun σ2 ↦
  seqF σ2 (osLvSt c).k (osTlSt c).2.1.k (tailF c (osLvSt c) σ2 T xs) fun σ3 ↦
  finishF c (osTlSt c).2.1 (osTlSt c).2.2 Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ3

/-- **The body before its `ret`, honestly.** -/
theorem osBodyA_complete {c : OsCfg} (σ : Val) (P : OsPtrs) {c0 c2 : E} {Ds : List LvDat}
    {T : E} {xs : List E} {Y PT PT1 BD LS ICH In : E} {Pp β : ℕ → E} {X : ℕ → ℕ → E}
    {M h I L : ℕ → E} {Λ : ℕ → E} {Z Yo : ℕ → ℕ → E}
    (htail : c.levels.tail ≠ []) {R : E} (hR : σ (.n osRate) = R)
    -- the head
    (h0 : LoadHolds rd (σ (.n 9)) 0 c0) (h2 : LoadHolds rd (σ (.n 9)) 1 c2)
    (hr0 : LoadHolds rd P.roots 0 (σ (.n 7))) (hr1 : LoadHolds rd P.roots 1 (σ (.n 8)))
    (hwin : ∀ i < 128, LoadHolds rd P.win i (word i 0 0))
    (hcan : AllCanonical [σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)])
    -- the levels
    (hlv : LvsH C rd P R c 0 c.levels Ds (headSponge σ c0 c2) [c0, σ (.n 6) + c2, c2] (σ (.n 6))
      (σ (.n 9) * gen ^ 2))
    -- the tail
    (hF : FoldCallC C rd)
    (hxl : xs.length = 2 * (c.yrLog - 1))
    (hrd : ReadsAt rd (bodyLvs c σ c0 c2 Ds).2.2.2 xs)
    (hT : ∀ j, j < c.yrLog - 1 → LoadHolds rd T j ((foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1
      (bodyLvs c σ c0 c2 Ds).2.1 (bodyLvs c σ c0 c2 Ds).2.2.1 xs).2.1.getD j 0))
    (hlast : LoadHolds rd T (c.yrLog - 1) (foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1
      (bodyLvs c σ c0 c2 Ds).2.1 (bodyLvs c σ c0 c2 Ds).2.2.1 xs).1.squeeze.1)
    (hzero : ∀ i < yrLogCap - c.yrLog, LoadHolds rd T (c.yrLog + i) 0)
    -- the finish
    (hC : C ("fold_final_msg__L" ++ natStr c.yrLog) [P.fmsg, T] [Y])
    (hpt : ∀ j < pointCap, PtSrcP rd P T c j (Pp j) ∧ LoadHolds rd PT j (Pp j) ∧
      LoadHolds rd PT1 j (1 + Pp j))
    (hbs : ∀ i (hi : i < c.levels.length), BasisMemP rd P T BD LS c i c.levels[i] (β i) (X i))
    (hich0 : LoadHolds rd ICH 0 0)
    (hrs : ∀ i (hi : i < c.levels.length), ResMemP C rd P R BD ICH LS c i c.levels[i]
      (M i) (h i) (I i) (L i))
    (hIn : LoadHolds rd ICH c.levels.length In)
    (hood : OodAllP rd P T c Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail) :
    BlkF C rd σ 10 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2)
      (bodyF c σ P c0 c2 Ds T xs Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo)
      (osBodyAc c)
      (fun σ' ↦ (osFinRet c (osTlSt c).2.1 (osTlSt c).2.2).map σ' =
        [polyEval (foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1 (bodyLvs c σ c0 c2 Ds).2.1
          (bodyLvs c σ c0 c2 Ds).2.2.1 xs).2.2.1 (foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1
          (bodyLvs c σ c0 c2 Ds).2.1 (bodyLvs c σ c0 c2 Ds).2.2.1 xs).1.squeeze.1, PT, PT1,
        In + oodSum c Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail, Y] ∧
        AgreeBelow 10 σ σ') := by
  have hne : c.levels ≠ [] := fun h ↦ htail (by rw [h]; rfl)
  obtain ⟨p, hp⟩ := osLevels_padC c c.levels 0 (osHead c).2 hne
  have eB : osBodyAc c = (osHead c).1 ++ ((osLevels c 0 c.levels (osHead c).2).1 ++
      ((osTlSt c).1 ++ osFinA c (osTlSt c).2.1 (osTlSt c).2.2)) := by
    simp only [osBodyAc, List.append_assoc]
  rw [eB]
  unfold bodyF
  obtain ⟨-, hs10, hP10, -⟩ := osHead_complete (C := C) σ P h0 h2 hr0 hr1 hwin hcan _
    (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hR10 : fill σ 10 161 (headF c σ P c0 c2) (.n osRate) = R := by
    rw [fill_lt (by unfold osRate; omega), hR]
  have hlk : 161 ≤ (osLvSt c).k := ((osLevels_complete c.levels Ds 0 (osHead c).2 _ _ _ _ _ hs10
    hP10 hR10 hlv) _ (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.2.1
  have b5 : (osTlSt c).2.1.k + 6 ≤ osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 := osFinEnd_ge _ _ _
  have hb := osTail_bounds c (osLvSt c) hlk
  have b1 : (osLvSt c).k ≤ (osTlSt c).2.1.k := hb.1
  have b2 : 161 ≤ (osTlSt c).2.1.k := hb.2.1
  have b3 : (osTlSt c).2.2 < (osTlSt c).2.1.k := hb.2.2.1
  have b4 : (osTlSt c).2.1.t < (osTlSt c).2.1.k := hb.2.2.2
  -- the head
  refine BlkF.then (k1 := 161) (by omega) (by omega)
    (osHead_complete (C := C) σ P h0 h2 hr0 hr1 hwin hcan) fun σ1 ha1 hO1 ↦ ?_
  obtain ⟨hs1, hP1, -⟩ := hO1
  have hR1 : σ1 (.n osRate) = R := by rw [ha1 _ (by unfold osRate; omega), hR]
  -- the levels
  refine BlkF.then (k1 := (osLvSt c).k) hlk (by omega)
    (osLevels_complete c.levels Ds 0 (osHead c).2 σ1 _ _ _ _ hs1 hP1 hR1 hlv) fun σ2 ha2 hO2 ↦ ?_
  obtain ⟨hs2, -, -⟩ := hO2
  have hP2 : ptrsOf σ2 = P := (ptrsOf_agree (le_refl 161) ha2).trans hP1
  have hR2 : σ2 (.n osRate) = R := by rw [ha2 _ (by unfold osRate; omega), hR1]
  -- the tail
  refine BlkF.then (k1 := (osTlSt c).2.1.k) b1 (by omega)
    (osTail_complete σ2 hF hs2 hp T hxl hrd hT hlast hzero) fun σ3 ha3 hO3 ↦ ?_
  obtain ⟨hT3, ht3, -⟩ := hO3
  have hP3 : ptrsOf σ3 = P := (ptrsOf_agree hlk ha3).trans hP2
  have hR3 : σ3 (.n osRate) = R := by rw [ha3 _ (by unfold osRate; omega), hR2]
  have hmT : (osTlSt c).2.1.mats = (osLvSt c).mats := by
    show (osTail c (osLvSt c)).2.1.mats = _
    rw [osTail_eq]; exact osFolds_mats _ _ _ _
  -- the finish
  refine BlkF.mono (osFinA_complete (C := C) (rd := rd) σ3 b2 b3 b4 htail hR3
    (by rw [hmT]; exact matsOk_agree hs2.mats hs2.matsB ha3)
    (by rw [hmT]; exact matsBelow_mono hs2.matsB b1)
    (by rw [show σ3 (.n osFmsg) = (ptrsOf σ3).fmsg from rfl, hP3, hT3]; exact hC)
    (by rw [hP3, hT3]; exact hpt) (by rw [hP3, hT3]; exact hbs) hich0 (by rw [hP3]; exact hrs) hIn
    (by rw [hP3, hT3]; exact hood)) fun σ' hO ↦ ?_
  obtain ⟨hr, ha⟩ := hO
  refine ⟨by rw [hr, ht3]; rfl, ?_⟩
  exact (((ha1.trans (ha2.mono (by omega))).trans (ha3.mono (by omega))).trans (ha.mono (by omega)))

end
end LeanVM.Guest.B1.Whir
