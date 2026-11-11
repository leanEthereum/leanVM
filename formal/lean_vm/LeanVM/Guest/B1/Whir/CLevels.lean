/-
  LeanVM.Guest.B1.Whir.CLevels

  The levels, honestly: each level's data and hypotheses on the sponge, the quadratic, the claim
  and the cursor the previous one leaves.
-/

module

public import LeanVM.Guest.B1.Whir.CLevel

/-!
# The levels, honestly

A level's honest data (`LvDat`) and its hypotheses on the sponge `F`, the quadratic `q`, the claim
`t` and the cursor `cur` it starts from (`LvHN`, `LvHF`, by the composites' hypotheses); what it
leaves (`lvOut`); the levels threaded (`LvsHyps`). `osLevels_complete`: the levels' statements hold
at the values `lvsF`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- A level's honest data: its rounds' words, its final message (the last level) or its next
commitment's words (root, out-of-domain value and intro, nonce), its row weights' buffer, its root's
cells, its queries' sum and its intro's words. -/
structure LvDat where
  xs : List E
  ms : List E
  ra : E
  rb : E
  y : E
  c0 : E
  c2 : E
  nonce : E
  d : Digest
  wp : E
  r0 : E
  r1 : E
  sum : E
  ic0 : E
  ic2 : E
  deriving Inhabited

/-- The rounds of a level from `F`, `q`, `t`. -/
def lvR (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : Fs × List E × List E × E :=
  foldsTr lv.folds F q t D.xs

/-- The capacity after the last level's grinding check. -/
def capFin (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : List E :=
  ((((lvR lv D F q t).1.absorbAll D.ms dsObserve).absorb D.nonce dsPowNonce).squeeze.2.cap)

/-- The capacity after the grinding check of a level that is not the last. -/
def capNon (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : List E :=
  capOf (cF2 (lvR lv D F q t).1 D.ra D.rb lv.logCols D.y D.c0 D.c2 D.nonce).perm

/-- The capacity a level's positions leave: its squeezes from `cap`. -/
def sqLast (lv : OsLv) (cap : List E) : List E := sqCaps cap lv.squeezes

/-- The batching challenge squeezed after the positions from the capacity `cap`. -/
def lamOf (lv : OsLv) (cap : List E) : E := (⟨sqLast lv cap, []⟩ : Fs).squeeze.1

/-- The capacity after a level's grinding check. -/
def lvCap (c : OsCfg) (lvl : ℕ) (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : List E :=
  if lvl = c.yrLevel then capFin lv D F q t else capNon lv D F q t

/-- The sponge after a level's squeezes. -/
def lvFq (c : OsCfg) (lvl : ℕ) (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : Fs :=
  ⟨sqLast lv (lvCap c lvl lv D F q t), []⟩

/-- A level's batching challenge. -/
def lvLam (c : OsCfg) (lvl : ℕ) (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) : E :=
  lamOf lv (lvCap c lvl lv D F q t)

theorem lvFq_squeezeN (c : OsCfg) (lvl : ℕ) (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) :
    lvFq c lvl lv D F q t = ((⟨lvCap c lvl lv D F q t, []⟩ : Fs).squeezeN lv.squeezes).2 :=
  (squeezeN_sqCaps _ _).1.symm

/-- The words a level reads. -/
def lvWords (c : OsCfg) (lvl : ℕ) (lv : OsLv) : ℕ :=
  2 * lv.folds + (if lvl = c.yrLevel then c.yrLen + 1 else 6) + 2

/-- What a level leaves: the sponge, the quadratic, the claim. -/
def lvOut (c : OsCfg) (lvl : ℕ) (lv : OsLv) (D : LvDat) (F : Fs) (q : List E) (t : E) :
    Fs × List E × E :=
  let L := lvLam c lvl lv D F q t
  let Q := (lvR lv D F q t).2.2.1
  let T := (lvR lv D F q t).2.2.2
  (⟨(lvFq c lvl lv D F q t).squeeze.2.cap, [(D.ic0, dsObserve), (D.ic2, dsObserve)]⟩,
    if lvl = c.yrLevel then
      ([Q.getD 0 0 + L * D.ic0, Q.getD 1 0 + L * (D.sum + D.ic2), Q.getD 2 0 + L * D.ic2],
        T + L * D.sum)
    else
      ([Q.getD 0 0 + L * D.c0 + L * L * D.ic0,
          Q.getD 1 0 + L * (D.y + D.c2) + L * L * (D.sum + D.ic2),
          Q.getD 2 0 + L * D.c2 + L * L * D.ic2],
        T + L * D.y + L * L * D.sum))


variable {C : CallRel} {rd : Reader}

/-- The fixed buffers' pointers. -/
structure OsPtrs where
  fmsg : E
  roots : E
  fch : E
  betas : E
  mus : E
  qpos : E
  qbp : E
  win : E
  oodz : E
  ood : E

/-- The fixed buffers' pointers of a valuation. -/
def ptrsOf (σ : Val) : OsPtrs :=
  ⟨σ (.n osFmsg), σ (.n osRoots), σ (.n osFch), σ (.n osBetas),
    σ (.n osMus), σ (.n osQpos), σ (.n osQbp), σ (.n osWin), σ (.n osOodz), σ (.n osOod)⟩

theorem ptrsOf_agree {σ σ' : Val} {k : ℕ} (hk : 161 ≤ k) (h : AgreeBelow k σ σ') :
    ptrsOf σ' = ptrsOf σ := by
  simp only [ptrsOf, h _ (show osFmsg < k by unfold osFmsg; omega),
    h _ (show osRoots < k by unfold osRoots; omega), h _ (show osFch < k by unfold osFch; omega),
    h _ (show osBetas < k by unfold osBetas; omega), h _ (show osMus < k by unfold osMus; omega),
    h _ (show osQpos < k by unfold osQpos; omega), h _ (show osQbp < k by unfold osQbp; omega),
    h _ (show osWin < k by unfold osWin; omega),
    h _ (show osOodz < k by unfold osOodz; omega), h _ (show osOod < k by unfold osOod; omega)]

/-- **A level that is not the last, its hypotheses** on the honest data `D` from `F`, `q`, `t`,
`cur`, the buffers' pointers `P`, at the rate's selector `R`. -/
structure LvHN (C : CallRel) (rd : Reader) (P : OsPtrs) (R : E) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (D : LvDat) (F : Fs) (q : List E) (t cur : E) : Prop where
  nf : lvl ≠ c.yrLevel
  f1 : 1 ≤ lv.folds
  hC : FoldCallC C rd
  hCan : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets
  hOod : ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
    C ("opening_ood_point__L" ++ natStr lv.logCols) args rets
  hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
    C ("grind_check__L" ++ natStr lv.grind) args rets
  hlvl : (lvl + 1) * ligColsCap < u128Bound
  hxl : D.xs.length = 2 * lv.folds
  hrd : ReadsAt rd cur D.xs
  hst : ∀ j, j < lv.folds → LoadHolds rd (P.fch) (lv.foldsOff + j)
    ((lvR lv D F q t).2.1.getD j 0)
  hd : (D.ra, D.rb) = digestHalves D.d
  hrd2 : ReadsAt rd (cur * gen ^ (2 * lv.folds)) [D.ra, D.rb, D.y, D.c0, D.c2, D.nonce]
  hr0' : LoadHolds rd (P.roots) (2 * lvl + 2) D.ra
  hr1' : LoadHolds rd (P.roots) (2 * lvl + 3) D.rb
  hz : ReadsAt rd (P.oodz * gen ^ ((lvl + 1) * ligColsCap))
    (challengeOf (cF1 (lvR lv D F q t).1 D.ra D.rb).perm ::
      (cRest (lvR lv D F q t).1 D.ra D.rb lv.logCols).1)
  hy : LoadHolds rd (P.ood) ((lvl + 1) * oodSlots + 1) D.y
  hc0 : LoadHolds rd (P.ood) ((lvl + 1) * oodSlots + 2) D.c0
  hc2 : LoadHolds rd (P.ood) ((lvl + 1) * oodSlots + 3) D.c2
  hpow : powOk Whir.queryGrindingBits
    (cF2 (lvR lv D F q t).1 D.ra D.rb lv.logCols D.y D.c0 D.c2 D.nonce).squeeze.1 = true
  hD : DispC C rd R ((c.lvAt lvl).map osPositionsName)
    (capNon lv D F q t ++ [P.qpos * gen ^ lv.posOff, P.qbp * gen ^ lv.posOff, P.win])
    (sqLast lv (capNon lv D F q t))
  hl0 : lamOf lv (capNon lv D F q t) ≠ 0
  hmu : LoadHolds rd P.mus lvl (lamOf lv (capNon lv D F q t))⁻¹
  hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound
  hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
    [P.fch * gen ^ lv.foldsOff, D.wp] []
  hQ : DispC C rd R ((c.lvAt lvl).map (osQueriesName lvl))
    [lamOf lv (capNon lv D F q t), P.qbp * gen ^ lv.posOff, D.wp]
    [D.r0, D.r1, D.sum, lamOf lv (capNon lv D F q t) ^ lv.queries]
  hr0 : LoadHolds rd (P.roots) (2 * lvl) D.r0
  hr1 : LoadHolds rd (P.roots) (2 * lvl + 1) D.r1
  hi : ReadsAt rd (cur * gen ^ (2 * lv.folds + 6)) [D.ic0, D.ic2]
  hlo : LoadHolds rd (P.ood) ((lvl + 1) * oodSlots) (lamOf lv (capNon lv D F q t))
  hbeta : LoadHolds rd (P.betas) lvl (lamOf lv (capNon lv D F q t) * lamOf lv (capNon lv D F q t) *
    lamOf lv (capNon lv D F q t) ^ lv.queries)

/-- **The last level, its hypotheses.** -/
structure LvHF (C : CallRel) (rd : Reader) (P : OsPtrs) (R : E) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (D : LvDat) (F : Fs) (q : List E) (t cur : E) : Prop where
  fin : lvl = c.yrLevel
  hC : FoldCallC C rd
  hFm : ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets → args.getD 8 0 = P.fmsg →
    C ("opening_final_message__L" ++ natStr c.yrLen) args rets
  hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
    C ("grind_check__L" ++ natStr lv.grind) args rets
  hxl : D.xs.length = 2 * lv.folds
  hrd : ReadsAt rd cur D.xs
  hst : ∀ j, j < lv.folds → LoadHolds rd (P.fch) (lv.foldsOff + j)
    ((lvR lv D F q t).2.1.getD j 0)
  hml : D.ms.length = c.yrLen
  hrd2 : ReadsAt rd (cur * gen ^ (2 * lv.folds)) (D.ms ++ [D.nonce])
  hout : ReadsAt rd (P.fmsg) D.ms
  hpow : powOk Whir.queryGrindingBits
    ((((lvR lv D F q t).1.absorbAll D.ms dsObserve).absorb D.nonce dsPowNonce).squeeze.1) = true
  hD : DispC C rd R ((c.lvAt lvl).map osPositionsName)
    (capFin lv D F q t ++ [P.qpos * gen ^ lv.posOff, P.qbp * gen ^ lv.posOff, P.win])
    (sqLast lv (capFin lv D F q t))
  hl0 : lamOf lv (capFin lv D F q t) ≠ 0
  hmu : LoadHolds rd P.mus lvl (lamOf lv (capFin lv D F q t))⁻¹
  hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound
  hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
    [P.fch * gen ^ lv.foldsOff, D.wp] []
  hQ : DispC C rd R ((c.lvAt lvl).map (osQueriesName lvl))
    [lamOf lv (capFin lv D F q t), P.qbp * gen ^ lv.posOff, D.wp]
    [D.r0, D.r1, D.sum, lamOf lv (capFin lv D F q t) ^ lv.queries]
  hr0 : LoadHolds rd (P.roots) (2 * lvl) D.r0
  hr1 : LoadHolds rd (P.roots) (2 * lvl + 1) D.r1
  hi : ReadsAt rd (cur * gen ^ (2 * lv.folds + c.yrLen + 1)) [D.ic0, D.ic2]
  hbeta : LoadHolds rd (P.betas) lvl (lamOf lv (capFin lv D F q t) *
    lamOf lv (capFin lv D F q t) ^ lv.queries)

theorem LvOut.congr_cur {σ' : Val} {st st' : OsSt} {F : Fs} {q : List E} {t cur cur' : E} {co : ℕ}
    (h : LvOut σ' st st' F q t cur co) (e : cur = cur') : LvOut σ' st st' F q t cur' co := by
  subst e; exact h

/-- A level's hypotheses. -/
def LvH (C : CallRel) (rd : Reader) (P : OsPtrs) (R : E) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (D : LvDat) (F : Fs) (q : List E) (t cur : E) : Prop :=
  if lvl = c.yrLevel then LvHF C rd P R c lvl lv D F q t cur else LvHN C rd P R c lvl lv D F q t cur

/-- The values of a level. -/
def lvF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat) : ℕ → E :=
  if lvl = c.yrLevel then
    lvFinF c lvl lv st σ D.xs D.ms D.nonce (sqLast lv (capFin lv D (st.F σ) (st.quad σ) (σ (.n st.t))))
      D.wp D.r0 D.r1 D.sum
      (lamOf lv (capFin lv D (st.F σ) (st.quad σ) (σ (.n st.t))) ^ lv.queries) D.ic0 D.ic2
  else lvNonF c lvl lv st σ D.xs D.ra D.rb D.y D.c0 D.c2 D.nonce
    (sqLast lv (capNon lv D (st.F σ) (st.quad σ) (σ (.n st.t)))) D.wp D.r0 D.r1 D.sum
    (lamOf lv (capNon lv D (st.F σ) (st.quad σ) (σ (.n st.t))) ^ lv.queries) D.ic0 D.ic2

/-- **A level, honestly**, on the sponge, quadratic, claim and cursor it starts from. -/
theorem osLevel_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) {D : LvDat}
    {F : Fs} {q : List E} {t cur : E} (hF : st.F σ = F) (hq : st.quad σ = q) (ht : σ (.n st.t) = t)
    (hcur : st.cur σ = cur)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below) (hk : 161 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hpad : PadOk σ st.pad)
    (hpk : ∀ p, st.pad = some p → p + 4 < st.k) (hmo : MatsOk σ st.mats)
    (hmob : MatsBelow st.k st.mats) {P : OsPtrs} (hP : ptrsOf σ = P) {R : E}
    (hR : σ (.n osRate) = R) (h : LvH C rd P R c lvl lv D F q t cur) :
    BlkF C rd σ st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ D) (osLevel c lvl lv st).1
      (fun σ' ↦ LvOut σ' st (osLevel c lvl lv st).2 (lvOut c lvl lv D F q t).1
        (lvOut c lvl lv D F q t).2.1 (lvOut c lvl lv D F q t).2.2
        (cur * gen ^ (lvWords c lvl lv)) (if lvl = c.yrLevel then 2 else 8) ∧
        AgreeBelow st.k σ σ') := by
  subst hF hq ht hcur hP
  unfold LvH at h
  by_cases hfin : lvl = c.yrLevel
  · have hc : (lvl = c.yrLevel) = True := eq_true hfin
    simp only [hc, ↓reduceIte] at h
    simp only [lvF, lvOut, lvWords, lvLam, lvFq, lvCap, hc, ↓reduceIte]
    refine BlkF.mono (osLevel_final_complete (C := C) (rd := rd) σ hfin hR h.hC
      (fun a r hm h8 ↦ h.hFm a r hm (by rw [h8]; rfl)) h.hGr hfs hco hb hk
      hcan hpad hpk hmo hmob h.hxl h.hrd h.hst h.hml h.hrd2 h.hout h.hpow
      (sqCaps_length _ (by simp [capOf]) _)
      (sqCaps_canonical _ (capOf_canonical _) _) h.hD h.hl0 h.hmu h.hbo D.wp D.r0 D.r1 D.sum
      _ D.ic0 D.ic2 h.hRW h.hQ h.hr0 h.hr1 h.hi h.hbeta) fun σ' ⟨ho, ha⟩ ↦ ⟨LvOut.congr_cur ho (by
        rw [show 2 * lv.folds + (c.yrLen + 1) + 2 =
          2 * lv.folds + c.yrLen + 3 by omega]), ha⟩
  · have hc : (lvl = c.yrLevel) = False := eq_false hfin
    simp only [hc, ↓reduceIte] at h
    simp only [lvF, lvOut, lvWords, lvLam, lvFq, lvCap, hc, ↓reduceIte]
    exact osLevel_nonfinal_complete (C := C) (rd := rd) σ hfin h.f1 hR h.hC h.hCan h.hOod h.hGr hfs
      hco hb hk hcan hpad hpk hmo hmob h.hlvl h.hxl h.hrd h.hst h.hd h.hrd2 h.hr0' h.hr1' h.hz
      h.hy h.hc0 h.hc2 h.hpow (sqCaps_length _ (by simp [capOf]) _)
      (sqCaps_canonical _ (capOf_canonical _) _) h.hD h.hl0 h.hmu h.hbo D.wp D.r0 D.r1 D.sum _
      D.ic0 D.ic2 h.hRW h.hQ h.hr0 h.hr1 h.hi h.hlo h.hbeta

/-- The values of the levels `lvl ..`. -/
def lvsF (c : OsCfg) : ℕ → List OsLv → List LvDat → OsSt → Val → ℕ → E
  | lvl, lv :: rest, D :: Ds, st, σ =>
    seqF σ st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ D)
      fun σ1 ↦ lvsF c (lvl + 1) rest Ds (osLevel c lvl lv st).2 σ1
  | _, _, _, _, _ => fun _ ↦ 0

/-- The levels' hypotheses, threaded. -/
def LvsH (C : CallRel) (rd : Reader) (P : OsPtrs) (R : E) (c : OsCfg) :
    ℕ → List OsLv → List LvDat → Fs → List E → E → E → Prop
  | _, [], [], _, _, _, _ => True
  | lvl, lv :: rest, D :: Ds, F, q, t, cur =>
    LvH C rd P R c lvl lv D F q t cur ∧
      LvsH C rd P R c (lvl + 1) rest Ds (lvOut c lvl lv D F q t).1 (lvOut c lvl lv D F q t).2.1
        (lvOut c lvl lv D F q t).2.2 (cur * gen ^ lvWords c lvl lv)
  | _, _, _, _, _, _, _ => False

/-- What the levels leave: the sponge, the quadratic, the claim and the cursor. -/
def lvsOut (c : OsCfg) : ℕ → List OsLv → List LvDat → Fs → List E → E → E → Fs × List E × E × E
  | lvl, lv :: rest, D :: Ds, F, q, t, cur =>
    lvsOut c (lvl + 1) rest Ds (lvOut c lvl lv D F q t).1 (lvOut c lvl lv D F q t).2.1
      (lvOut c lvl lv D F q t).2.2 (cur * gen ^ lvWords c lvl lv)
  | _, _, _, F, q, t, cur => (F, q, t, cur)

/-- A state of the levels' run: its sponge, quadratic, claim and cursor, and the invariants. -/
structure LvsSt (σ : Val) (st : OsSt) (F : Fs) (q : List E) (t cur : E) : Prop where
  F : st.F σ = F
  quad : st.quad σ = q
  t : σ (.n st.t) = t
  cur : st.cur σ = cur
  fs : st.fs.length = 5
  co : st.co ≤ 8
  below : st.Below
  k : 161 ≤ st.k
  can : AllCanonical (st.fsv σ)
  pad : PadOk σ st.pad
  pk : ∀ p, st.pad = some p → p + 4 < st.k
  mats : MatsOk σ st.mats
  matsB : MatsBelow st.k st.mats

/-- **The levels, honestly.** -/
theorem osLevels_complete {c : OsCfg} {P : OsPtrs} {R : E} :
    ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ) (st : OsSt) (σ : Val) (F : Fs) (q : List E)
      (t cur : E), LvsSt σ st F q t cur → ptrsOf σ = P → σ (.n osRate) = R →
      LvsH C rd P R c lvl lvs Ds F q t cur →
      BlkF C rd σ st.k (osLevels c lvl lvs st).2.k (lvsF c lvl lvs Ds st σ) (osLevels c lvl lvs st).1
        (fun σ' ↦ LvsSt σ' (osLevels c lvl lvs st).2 (lvsOut c lvl lvs Ds F q t cur).1
          (lvsOut c lvl lvs Ds F q t cur).2.1 (lvsOut c lvl lvs Ds F q t cur).2.2.1
          (lvsOut c lvl lvs Ds F q t cur).2.2.2 ∧ st.k ≤ (osLevels c lvl lvs st).2.k ∧
          AgreeBelow st.k σ σ')
  | [], [], lvl, st, σ, F, q, t, cur, hs, _, _, _ => by
    simp only [osLevels, lvsOut]
    refine BlkF.nil fun σ' ha ↦ ⟨?_, le_rfl, ha⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := OsSt.agree hs.below ha
    refine ⟨by rw [e2, hs.F], by rw [e3, hs.quad], by rw [e4, hs.t], by rw [e5, hs.cur], hs.fs,
      hs.co, hs.below, hs.k, by rw [e1]; exact hs.can, ?_, hs.pk,
      matsOk_agree hs.mats hs.matsB ha, hs.matsB⟩
    have hpd := hs.pad
    cases hp : st.pad with
    | none => trivial
    | some p =>
      rw [hp] at hpd
      have := hs.pk p hp
      obtain ⟨z1, z2, z3, z4⟩ := hpd
      exact ⟨by rw [ha _ (by omega)]; exact z1, by rw [ha _ (by omega)]; exact z2,
        by rw [ha _ (by omega)]; exact z3, by rw [ha _ (by omega)]; exact z4⟩
  | lv :: rest, D :: Ds, lvl, st, σ, F, q, t, cur, hs, hP, hR, hH => by
    obtain ⟨h1, h2⟩ := hH
    have e : osLevels c lvl (lv :: rest) st = ((osLevel c lvl lv st).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).1,
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2) := rfl
    rw [e]
    dsimp only
    have hA := osLevel_complete (C := C) (rd := rd) σ hs.F hs.quad hs.t hs.cur hs.fs
      (by have := hs.co; unfold u128Bound; omega) hs.below hs.k hs.can hs.pad hs.pk hs.mats hs.matsB hP hR h1
    have hk1 : st.k ≤ (osLevel c lvl lv st).2.k :=
      (hA _ (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.1.k
    have mk : ∀ σ1, AgreeBelow st.k σ σ1 → LvOut σ1 st (osLevel c lvl lv st).2
        (lvOut c lvl lv D F q t).1 (lvOut c lvl lv D F q t).2.1 (lvOut c lvl lv D F q t).2.2
        (cur * gen ^ lvWords c lvl lv) (if lvl = c.yrLevel then 2 else 8) →
        LvsSt σ1 (osLevel c lvl lv st).2 (lvOut c lvl lv D F q t).1 (lvOut c lvl lv D F q t).2.1
          (lvOut c lvl lv D F q t).2.2 (cur * gen ^ lvWords c lvl lv) ∧ ptrsOf σ1 = P ∧
          σ1 (.n osRate) = R :=
      fun σ1 ha1' lo ↦ ⟨⟨lo.F, lo.quad, lo.t, lo.cur, lo.fs, by rw [lo.co]; split_ifs <;> omega,
        lo.below, by have := lo.k; have := hs.k; omega, lo.can, lo.pad,
        fun p hp ↦ by obtain ⟨p', hp', h4⟩ := lo.padSome; rw [hp'] at hp; cases hp; exact h4,
        lo.mats, lo.matsB⟩,
        by rw [ptrsOf_agree (by have := hs.k; omega) ha1', hP],
        by rw [ha1' _ (by unfold osRate; have := hs.k; omega), hR]⟩
    have hk2 : (osLevel c lvl lv st).2.k ≤ (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2.k := by
      obtain ⟨-, lo, ha⟩ := hA _ (agree_fill _ _ _ _) (range_fill _ _ _ _)
      obtain ⟨hs1, hP1, hR1⟩ := mk _ ha lo
      exact ((osLevels_complete rest Ds (lvl + 1) _ _ _ _ _ _ hs1 hP1 hR1 h2) _ (agree_fill _ _ _ _)
        (range_fill _ _ _ _)).2.2.1
    refine BlkF.then (k1 := (osLevel c lvl lv st).2.k) hk1 hk2 hA fun σ1 ha1 ⟨lo, ha1'⟩ ↦ ?_
    obtain ⟨hs1, hP1, hR1⟩ := mk σ1 ha1' lo
    refine BlkF.mono (osLevels_complete rest Ds (lvl + 1) _ σ1 _ _ _ _ hs1 hP1 hR1 h2)
      fun σ' ⟨ho, hk, ha⟩ ↦ ⟨ho, le_trans hk1 hk, fun i hi ↦ (ha i (by omega)).trans (ha1' i hi)⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, hH => by simp [LvsH] at hH
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hH => by simp [LvsH] at hH

end
end LeanVM.Guest.B1.Whir
