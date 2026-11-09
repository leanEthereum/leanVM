/-
  LeanVM.Guest.B1.Whir.CBody

  The body of open_stacked before its ret, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CHead
public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.CFinish
public import LeanVM.Guest.B1.Whir.OpenAux
public import LeanVM.Guest.B1.Whir.Flatness

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

/-- The sponge the head leaves. -/
def headSponge (σ : Val) (c0 c2 : E) : Fs :=
  ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(c0, dsObserve), (c2, dsObserve)]⟩

/-- What the levels leave, from the head's. -/
def bodyLvs (c : OsCfg) (σ : Val) (c0 c2 : E) (Ds : List LvDat) : Fs × List E × E × E :=
  lvsOut c 0 c.levels Ds (headSponge σ c0 c2) [c0, σ (.n 5) + c2, c2] (σ (.n 5))
    (σ (.n 8) * gen ^ 2)

theorem osTail_bounds (c : OsCfg) (st : OsSt) (hk : 164 ≤ st.k) :
    st.k ≤ (osTail c st).2.1.k ∧ 164 ≤ (osTail c st).2.1.k ∧
      (osTail c st).2.2 < (osTail c st).2.1.k ∧ (osTail c st).2.1.t < (osTail c st).2.1.k := by
  rw [osTail_eq]
  dsimp only
  have h : st.k + 2 ≤ (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k :=
    osFolds_k (st.k + 1) (c.yrLog - 1) 0 { st with k := st.k + 2 }
  omega

/-- The values of the body. -/
def bodyF (c : OsCfg) (σ : Val) (P : OsPtrs) (c0 c2 : E) (Ds : List LvDat) (T : E) (xs : List E)
    (Y PT PT1 BD LS ICH In : E) (Pp β : ℕ → E) (X : ℕ → ℕ → E) (RC acc M I L : ℕ → E)
    (Pq D : ℕ → ℕ → E) (Λ : ℕ → E) (Z Yo : ℕ → ℕ → E) : ℕ → E :=
  seqF σ 9 164 (headF c σ P c0 c2) fun σ1 ↦
  seqF σ1 164 (osLvSt c).k (lvsF c 0 c.levels Ds (osHead c).2 σ1) fun σ2 ↦
  seqF σ2 (osLvSt c).k (osTlSt c).2.1.k (tailF c (osLvSt c) σ2 T xs) fun σ3 ↦
  finishF c (osTlSt c).2.1 (osTlSt c).2.2 Y PT PT1 BD LS ICH In Pp β X RC acc M I L Pq D Λ Z Yo σ3

/-- **The body before its `ret`, honestly.** -/
theorem osBodyA_complete {c : OsCfg} (σ : Val) (P : OsPtrs) {c0 c2 : E} {Ds : List LvDat}
    {T : E} {xs : List E} {Y PT PT1 BD LS ICH In : E} {Pp β : ℕ → E} {X : ℕ → ℕ → E}
    {RC acc M I L : ℕ → E} {Pq D : ℕ → ℕ → E} {Λ : ℕ → E} {Z Yo : ℕ → ℕ → E}
    (htail : c.levels.tail ≠ [])
    -- the head
    (h0 : LoadHolds rd (σ (.n 8)) 0 c0) (h2 : LoadHolds rd (σ (.n 8)) 1 c2)
    (hr0 : LoadHolds rd P.roots 0 (σ (.n 6))) (hr1 : LoadHolds rd P.roots 1 (σ (.n 7)))
    (hwin : ∀ i < 128, LoadHolds rd P.win i (word i 0 0))
    (hcan : AllCanonical [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)])
    -- the levels
    (hlv : LvsH C rd P c 0 c.levels Ds (headSponge σ c0 c2) [c0, σ (.n 5) + c2, c2] (σ (.n 5))
      (σ (.n 8) * gen ^ 2))
    -- the tail
    (hF : ∀ args rets, MeaningOpeningFold rd args rets → C "opening_fold" args rets)
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
    (hrs : ∀ i (hi : i < c.levels.length), ResMemP C rd P BD ICH LS c i c.levels[i]
      (RC i) (acc i) (M i) (I i) (L i) (Pq i) (D i))
    (hIn : LoadHolds rd ICH c.levels.length In)
    (hood : OodAllP rd P T c Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail) :
    BlkF C rd σ 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2)
      (bodyF c σ P c0 c2 Ds T xs Y PT PT1 BD LS ICH In Pp β X RC acc M I L Pq D Λ Z Yo)
      (osBodyA c)
      (fun σ' ↦ (osFinishRet c (osTlSt c).2.1 (osTlSt c).2.2).map σ' =
        [polyEval (foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1 (bodyLvs c σ c0 c2 Ds).2.1
          (bodyLvs c σ c0 c2 Ds).2.2.1 xs).2.2.1 (foldsTr (c.yrLog - 1) (bodyLvs c σ c0 c2 Ds).1
          (bodyLvs c σ c0 c2 Ds).2.1 (bodyLvs c σ c0 c2 Ds).2.2.1 xs).1.squeeze.1, PT, PT1,
        In + oodSum c Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail, Y] ∧
        AgreeBelow 9 σ σ') := by
  have hne : c.levels ≠ [] := fun h ↦ htail (by rw [h]; rfl)
  obtain ⟨p, hp⟩ := osLevels_pad c c.levels 0 (osHead c).2 hne
  have eB : osBodyA c = (osHead c).1 ++ ((osLevels c 0 c.levels (osHead c).2).1 ++
      ((osTlSt c).1 ++ osFinishA c (osTlSt c).2.1 (osTlSt c).2.2)) := by
    simp only [osBodyA, List.append_assoc]
  rw [eB]
  unfold bodyF
  obtain ⟨-, hs10, hP10, -⟩ := osHead_complete (C := C) σ P h0 h2 hr0 hr1 hwin hcan _
    (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hlk : 164 ≤ (osLvSt c).k := ((osLevels_complete c.levels Ds 0 (osHead c).2 _ _ _ _ _ hs10
    hP10 hlv) _ (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.2.1
  have b5 : (osTlSt c).2.1.k + 6 ≤ osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 := osFinEnd_ge _ _ _
  have hb := osTail_bounds c (osLvSt c) hlk
  have b1 : (osLvSt c).k ≤ (osTlSt c).2.1.k := hb.1
  have b2 : 164 ≤ (osTlSt c).2.1.k := hb.2.1
  have b3 : (osTlSt c).2.2 < (osTlSt c).2.1.k := hb.2.2.1
  have b4 : (osTlSt c).2.1.t < (osTlSt c).2.1.k := hb.2.2.2
  -- the head
  refine BlkF.then (k1 := 164) (by omega) (by omega)
    (osHead_complete (C := C) σ P h0 h2 hr0 hr1 hwin hcan) fun σ1 ha1 hO1 ↦ ?_
  obtain ⟨hs1, hP1, -⟩ := hO1
  -- the levels
  refine BlkF.then (k1 := (osLvSt c).k) hlk (by omega)
    (osLevels_complete c.levels Ds 0 (osHead c).2 σ1 _ _ _ _ hs1 hP1 hlv) fun σ2 ha2 hO2 ↦ ?_
  obtain ⟨hs2, -, -⟩ := hO2
  have hP2 : ptrsOf σ2 = P := (ptrsOf_agree (le_refl 164) ha2).trans hP1
  -- the tail
  refine BlkF.then (k1 := (osTlSt c).2.1.k) b1 (by omega)
    (osTail_complete σ2 hF hs2 hp T hxl hrd hT hlast hzero) fun σ3 ha3 hO3 ↦ ?_
  obtain ⟨hT3, ht3, -⟩ := hO3
  have hP3 : ptrsOf σ3 = P := (ptrsOf_agree hlk ha3).trans hP2
  -- the finish
  refine BlkF.mono (osFinishA_complete (C := C) (rd := rd) σ3 b2 b3 b4 htail
    (by rw [show σ3 (.n osFmsg) = (ptrsOf σ3).fmsg from rfl, hP3, hT3]; exact hC)
    (by rw [hP3, hT3]; exact hpt) (by rw [hP3, hT3]; exact hbs) hich0 (by rw [hP3]; exact hrs) hIn
    (by rw [hP3, hT3]; exact hood)) fun σ' hO ↦ ?_
  obtain ⟨hr, ha⟩ := hO
  refine ⟨by rw [hr, ht3]; rfl, ?_⟩
  exact (((ha1.trans (ha2.mono (by omega))).trans (ha3.mono (by omega))).trans (ha.mono (by omega)))

end
end LeanVM.Guest.B1.Whir
