/-
  LeanVM.Guest.B1.Whir.CLevel

  One level, honestly: up to its grinding check, then the rest.
-/

module

public import LeanVM.Guest.B1.Whir.CLevelA

/-!
# One level, honestly

`osLevel_nonfinal_complete`, `osLevel_final_complete`: `osLevelA_*_complete` then
`osLvB_*_complete` on the state it leaves (`osLevel_splitC`), every hypothesis on the honest
data, the level leaving `LvOut`: the sponge after the batching challenge with the intro's words
waiting, the glued quadratic and claim, the cursor past the level's words.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What a level leaves for the next: the sponge, the quadratic, the claim, the cursor. -/
structure LvOut (σ' : Val) (st st' : OsSt) (F : Fs) (quad : List E) (t cur : E) (co : ℕ) :
    Prop where
  F : st'.F σ' = F
  quad : st'.quad σ' = quad
  t : σ' (.n st'.t) = t
  cur : st'.cur σ' = cur
  co : st'.co = co
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ')
  below : st'.Below
  pad : PadOk σ' st'.pad
  padSome : ∃ p, st'.pad = some p ∧ p + 4 < st'.k
  k : st.k ≤ st'.k
  mats : MatsOk σ' st'.mats
  matsB : MatsBelow st'.k st'.mats

theorem loads_of_readsAt {rd : Reader} {cb : E} {co : ℕ} {a b : E}
    (h : ReadsAt rd (cb * gen ^ co) [a, b]) :
    LoadHolds rd cb co a ∧ LoadHolds rd cb (co + 1) b := by
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  rw [loadHolds_mul_gen_pow] at h0 h1
  exact ⟨by simpa using h0, by simpa using h1⟩

/-- The values of a level that is not the last. -/
def lvNonF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (xs : List E)
    (ra rb y c0 c2 nonce : E) (last : List E) (wp r0 r1 sum lamN ic0 ic2 : E) : ℕ → E :=
  seqF σ st.k (osLvA c lvl lv st).2.1.k
    (seqF σ st.k (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k
      (foldsF (osFoldNames c lvl lv) lv.foldGrind osFch lv.folds lv.foldsOff st σ xs)
      fun σ1 ↦ fun j ↦ segLookup (commitSegs c.plan σ1 (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 lvl
        lv.logCols ra rb y c0 c2 nonce) (j - (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k))
    fun σ2 ↦ lvBNonF c lvl lv (osLvA c lvl lv st).2.1 σ2 last wp r0 r1 sum lamN ic0 ic2 y c0 c2

/-- **A level that is not the last, honestly.** -/
theorem osLevel_nonfinal_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hnf : lvl ≠ c.yrLevel) (h1 : 1 ≤ lv.folds)
    {Rs : E} (hRs : σ (.n osRate) = Rs) (hC : FoldCallC C rd (osFoldNames c lvl lv) lv.foldGrind Rs)
    (hCan : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets)
    (hOod : ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
      C ("opening_ood_point__L" ++ natStr lv.logCols) args rets)
    (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr lv.grind) args rets)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below) (hk : 161 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats)
    (hlvl : (lvl + 1) * ligColsCap < u128Bound)
    {xs : List E} (hxl : xs.length = roundLen lv.foldGrind * lv.folds) (hrd : ReadsAt rd (st.cur σ) xs)
    (hpw : FoldsPow lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs)
    (hst : ∀ j, j < lv.folds → LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j)
      ((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.1.getD j 0))
    {ra rb y c0 c2 nonce : E} {d : Digest} (hd : (ra, rb) = digestHalves d)
    (hrd2 : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds)) [ra, rb, y, c0, c2, nonce])
    (hr0' : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) ra)
    (hr1' : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) rb)
    (hz : ReadsAt rd (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap))
      (challengeOf (cF1 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb).perm ::
        (cRest (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb lv.logCols).1))
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2)
    (hpow : powOk Whir.queryGrindingBits nonce
      (cF2 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb lv.logCols y c0 c2
        nonce).squeeze.1 = true)
    {last : List E} (hll : last.length = 5) (hlc : AllCanonical last)
    (hD : DispC C rd Rs ((c.lvAt lvl).map osPositionsName)
      ((capOf (cF2 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb
        lv.logCols y c0 c2 nonce).perm) ++ [σ (.n osQpos) * gen ^ lv.posOff,
        σ (.n osQbp) * gen ^ lv.posOff, σ (.n osWin)]) last)
    (hl0 : (⟨last, []⟩ : Fs).squeeze.1 ≠ 0)
    (hmu : LoadHolds rd (σ (.n osMus)) lvl ((⟨last, []⟩ : Fs).squeeze.1)⁻¹)
    (hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound)
    (wp r0 r1 sum lamN ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hQ : DispC C rd Rs ((c.lvAt lvl).map (osQueriesName lvl))
      [(⟨last, []⟩ : Fs).squeeze.1, σ (.n osQbp) * gen ^ lv.posOff, wp] [r0, r1, sum, lamN])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hi : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + 6)) [ic0, ic2])
    (hlo : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) (⟨last, []⟩ : Fs).squeeze.1)
    (hbeta : LoadHolds rd (σ (.n osBetas)) lvl ((⟨last, []⟩ : Fs).squeeze.1 * (⟨last, []⟩ : Fs).squeeze.1 * lamN)) :
    BlkF C rd σ st.k (osLevel c lvl lv st).2.k
      (lvNonF c lvl lv st σ xs ra rb y c0 c2 nonce last wp r0 r1 sum lamN ic0 ic2)
      (osLevel c lvl lv st).1
      (fun σ' ↦ LvOut σ' st (osLevel c lvl lv st).2
        ⟨(⟨last, []⟩ : Fs).squeeze.2.cap, [(ic0, dsObserve), (ic2, dsObserve)]⟩
        (let L := (⟨last, []⟩ : Fs).squeeze.1;
          let Q := (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.1;
          [Q.getD 0 0 + L * c0 + L * L * ic0, Q.getD 1 0 + L * (y + c2) + L * L * (sum + ic2),
            Q.getD 2 0 + L * c2 + L * L * ic2])
        (let L := (⟨last, []⟩ : Fs).squeeze.1;
          (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.2 + L * y + L * L * sum)
        (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + 8)) 8 ∧ AgreeBelow st.k σ σ') := by
  set R := foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs with hR
  set S := cF2 R.1 ra rb lv.logCols y c0 c2 nonce with hS
  set stA := (osLvA c lvl lv st).2.1 with hstA
  have e : osLevel c lvl lv st = ((osLvA c lvl lv st).1 ++ (osLvB c lvl lv stA).1,
      (osLvB c lvl lv stA).2) := osLevel_splitC c lvl lv st
  rw [e]
  dsimp only
  have hA := osLevelA_nonfinal_complete (C := C) (rd := rd) (c := c) σ hnf h1 hRs hC hCan hOod hGr hfs
    hco hb hk hcan hlvl hmo hmob hxl hrd hpw hst hd hrd2 hr0' hr1' hz hy hc0 hc2 hpow
  have hkA : st.k ≤ stA.k := by
    have hc : (lvl = c.yrLevel) = False := eq_false hnf
    have := osFolds_k (osFoldNames c lvl lv) osFch lv.folds lv.foldsOff st
    simp only [hstA, osLvA, hc, ↓reduceIte, osCommit]
    omega
  have hkB : stA.k ≤ (osLvB c lvl lv stA).2.k := osLvB_k_le c lvl lv stA
  refine BlkF.then (k1 := stA.k) (k2 := (osLvB c lvl lv stA).2.k) hkA hkB hA
    fun σ2 ha2 ⟨ao, ha2'⟩ ↦ ?_
  have e2 : ∀ v, v < st.k → σ2 (.n v) = σ (.n v) := fun v hv ↦ ha2' v hv
  have hfsvA : stA.fsv σ2 = capOf S.perm := ao.fsv
  have hpadA : PadOk σ2 stA.pad := by
    rw [ao.pad]
    cases hp : st.pad with
    | none => trivial
    | some p =>
      rw [hp] at hpad
      have := hpk p hp
      obtain ⟨z1, z2, z3, z4⟩ := hpad
      exact ⟨by rw [e2 _ (by omega)]; exact z1, by rw [e2 _ (by omega)]; exact z2,
        by rw [e2 _ (by omega)]; exact z3, by rw [e2 _ (by omega)]; exact z4⟩
  have hcurA : stA.cur σ2 = st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + 6) := ao.cur
  have hi' : ReadsAt rd (σ2 (.n stA.cb) * gen ^ stA.co) [ic0, ic2] := by
    rw [show σ2 (.n stA.cb) * gen ^ stA.co = stA.cur σ2 from rfl, hcurA]; exact hi
  obtain ⟨hi0, hi2⟩ := loads_of_readsAt hi'
  have hB := osLvB_nonfinal_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (st := stA)
    σ2 hnf (by rw [e2 _ (by unfold osRate; omega), hRs]) ao.fs ao.below (by have := ao.k; omega)
    hpadA (fun p hp ↦ by rw [ao.pad] at hp; have := hpk p hp; have := ao.k; omega) ao.mats ao.matsB
    hbo hll hlc
    (by rw [hfsvA, e2 osQpos (by unfold osQpos; omega), e2 osQbp (by unfold osQbp; omega),
          e2 osWin (by unfold osWin; omega)]; exact hD)
    hl0 (by rw [e2 osMus (by unfold osMus; omega)]; exact hmu)
    wp r0 r1 sum lamN ic0 ic2
    (by rw [e2 osFch (by unfold osFch; omega)]; exact hRW)
    (by rw [e2 osQbp (by unfold osQbp; omega)]; exact hQ)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr0)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr1) hi0 hi2
    (by rw [e2 osOod (by unfold osOod; omega)]; exact hy)
    (by rw [e2 osOod (by unfold osOod; omega)]; exact hc0)
    (by rw [e2 osOod (by unfold osOod; omega)]; exact hc2)
    (by rw [e2 osOod (by unfold osOod; omega)]; exact hlo)
    (by rw [e2 osBetas (by unfold osBetas; omega)]; exact hbeta)
  have hqA : [σ2 (.n stA.c), σ2 (.n stA.b), σ2 (.n stA.a)] = R.2.2.1 := ao.quad
  have htA := ao.t
  refine BlkF.mono hB fun σ' ⟨bo, ha3⟩ ↦ ⟨⟨?_, ?_, ?_, ?_, ?_, bo.fs, bo.can, bo.below, bo.pad,
    bo.padSome, by have := bo.k; have := ao.k; omega, bo.mats, bo.matsB⟩, fun i hi ↦ (ha3 i (by have := ao.k; omega)).trans
      (ha2' i hi)⟩
  · show (⟨_, [(σ' (.n _), dsObserve), (σ' (.n _), dsObserve)]⟩ : Fs) = _
    rw [bo.fsv, bo.w0, bo.w1]
  · rw [bo.quad, ← hqA]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · rw [bo.t, htA]
  · show σ' (.n _) * gen ^ _ = _
    rw [bo.cb, bo.co, ha3 _ ao.below.cb, pow_add, ← mul_assoc]
    show stA.cur σ2 * gen ^ 2 = _
    rw [hcurA, mul_assoc, ← pow_add]
  · rw [bo.co, ao.co]

/-- The values of the last level. -/
def lvFinF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (xs ms : List E)
    (nonce : E) (last : List E) (wp r0 r1 sum lamN ic0 ic2 : E) : ℕ → E :=
  seqF σ st.k (osLvA c lvl lv st).2.1.k
    (seqF σ st.k (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k
      (foldsF (osFoldNames c lvl lv) lv.foldGrind osFch lv.folds lv.foldsOff st σ xs)
      fun σ1 ↦ osFinalF σ1 (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 ms nonce)
    fun σ2 ↦ lvBFinF c lvl lv (osLvA c lvl lv st).2.1 σ2 last wp r0 r1 sum lamN ic0 ic2

/-- **The last level, honestly.** -/
theorem osLevel_final_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hfin : lvl = c.yrLevel)
    {Rs : E} (hRs : σ (.n osRate) = Rs) (hC : FoldCallC C rd (osFoldNames c lvl lv) lv.foldGrind Rs)
    (hFm : ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets →
      args.getD 8 0 = σ (.n osFmsg) → C ("opening_final_message__L" ++ natStr c.yrLen) args rets)
    (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr lv.grind) args rets)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below) (hk : 161 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats)
    {xs : List E} (hxl : xs.length = roundLen lv.foldGrind * lv.folds) (hrd : ReadsAt rd (st.cur σ) xs)
    (hpw : FoldsPow lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs)
    (hst : ∀ j, j < lv.folds → LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j)
      ((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.1.getD j 0))
    {ms : List E} {nonce : E} (hml : ms.length = c.yrLen)
    (hrd2 : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds)) (ms ++ [nonce]))
    (hout : ReadsAt rd (σ (.n osFmsg)) ms)
    (hpow : powOk Whir.queryGrindingBits nonce
      ((((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1.absorbAll ms dsObserve).absorb
        nonce dsPowNonce).squeeze.1) = true)
    {last : List E} (hll : last.length = 5) (hlc : AllCanonical last)
    (hD : DispC C rd Rs ((c.lvAt lvl).map osPositionsName)
      (((((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1.absorbAll ms
        dsObserve).absorb nonce dsPowNonce).squeeze.2.cap) ++ [σ (.n osQpos) * gen ^ lv.posOff,
        σ (.n osQbp) * gen ^ lv.posOff, σ (.n osWin)]) last)
    (hl0 : (⟨last, []⟩ : Fs).squeeze.1 ≠ 0)
    (hmu : LoadHolds rd (σ (.n osMus)) lvl ((⟨last, []⟩ : Fs).squeeze.1)⁻¹)
    (hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound)
    (wp r0 r1 sum lamN ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hQ : DispC C rd Rs ((c.lvAt lvl).map (osQueriesName lvl))
      [(⟨last, []⟩ : Fs).squeeze.1, σ (.n osQbp) * gen ^ lv.posOff, wp] [r0, r1, sum, lamN])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hi : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + c.yrLen + 1)) [ic0, ic2])
    (hbeta : LoadHolds rd (σ (.n osBetas)) lvl ((⟨last, []⟩ : Fs).squeeze.1 * lamN)) :
    BlkF C rd σ st.k (osLevel c lvl lv st).2.k
      (lvFinF c lvl lv st σ xs ms nonce last wp r0 r1 sum lamN ic0 ic2)
      (osLevel c lvl lv st).1
      (fun σ' ↦ LvOut σ' st (osLevel c lvl lv st).2
        ⟨(⟨last, []⟩ : Fs).squeeze.2.cap, [(ic0, dsObserve), (ic2, dsObserve)]⟩
        (let L := (⟨last, []⟩ : Fs).squeeze.1;
          let Q := (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.1;
          [Q.getD 0 0 + L * ic0, Q.getD 1 0 + L * (sum + ic2), Q.getD 2 0 + L * ic2])
        (let L := (⟨last, []⟩ : Fs).squeeze.1;
          (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.2 + L * sum)
        (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + c.yrLen + 3)) 2 ∧ AgreeBelow st.k σ σ') := by
  set R := foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs with hR
  set capA := ((R.1.absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.2.cap with hcapA
  set stA := (osLvA c lvl lv st).2.1 with hstA
  have hc : (lvl = c.yrLevel) = True := eq_true hfin
  have e : osLevel c lvl lv st = ((osLvA c lvl lv st).1 ++ (osLvB c lvl lv stA).1,
      (osLvB c lvl lv stA).2) := osLevel_splitC c lvl lv st
  rw [e]
  dsimp only
  have hA := osLevelA_final_complete (C := C) (rd := rd) (c := c) σ hfin hRs hC hFm hGr hfs hco
    hb hk hcan hmo hmob hxl hrd hpw hst hml hrd2 hout hpow
  have hkA : st.k ≤ stA.k := by
    have := osFolds_k (osFoldNames c lvl lv) osFch lv.folds lv.foldsOff st
    have := osMat_next (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.cb
      (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.co (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k
    simp only [hstA, osLvA, hc, ↓reduceIte, osFinal]
    omega
  have hkB : stA.k ≤ (osLvB c lvl lv stA).2.k := osLvB_k_le c lvl lv stA
  refine BlkF.then (k1 := stA.k) (k2 := (osLvB c lvl lv stA).2.k) hkA hkB hA
    fun σ2 ha2 ⟨ao, ha2'⟩ ↦ ?_
  have e2 : ∀ v, v < st.k → σ2 (.n v) = σ (.n v) := fun v hv ↦ ha2' v hv
  have hfsvA : stA.fsv σ2 = capA := ao.fsv
  have hpadA : PadOk σ2 stA.pad := by
    rw [ao.pad]
    cases hp : st.pad with
    | none => trivial
    | some p =>
      rw [hp] at hpad
      have := hpk p hp
      obtain ⟨z1, z2, z3, z4⟩ := hpad
      exact ⟨by rw [e2 _ (by omega)]; exact z1, by rw [e2 _ (by omega)]; exact z2,
        by rw [e2 _ (by omega)]; exact z3, by rw [e2 _ (by omega)]; exact z4⟩
  have hcurA : stA.cur σ2 = st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + c.yrLen + 1) := ao.cur
  have hi' : ReadsAt rd (σ2 (.n stA.cb) * gen ^ stA.co) [ic0, ic2] := by
    rw [show σ2 (.n stA.cb) * gen ^ stA.co = stA.cur σ2 from rfl, hcurA]; exact hi
  obtain ⟨hi0, hi2⟩ := loads_of_readsAt hi'
  have hB := osLvB_final_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (st := stA)
    σ2 hfin (by rw [e2 _ (by unfold osRate; omega), hRs]) ao.fs ao.below (by have := ao.k; omega)
    hpadA (fun p hp ↦ by rw [ao.pad] at hp; have := hpk p hp; have := ao.k; omega) ao.mats ao.matsB
    hbo hll hlc
    (by rw [hfsvA, e2 osQpos (by unfold osQpos; omega), e2 osQbp (by unfold osQbp; omega),
          e2 osWin (by unfold osWin; omega)]; exact hD)
    hl0 (by rw [e2 osMus (by unfold osMus; omega)]; exact hmu)
    wp r0 r1 sum lamN ic0 ic2
    (by rw [e2 osFch (by unfold osFch; omega)]; exact hRW)
    (by rw [e2 osQbp (by unfold osQbp; omega)]; exact hQ)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr0)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr1) hi0 hi2
    (by rw [e2 osBetas (by unfold osBetas; omega)]; exact hbeta)
  have hqA : [σ2 (.n stA.c), σ2 (.n stA.b), σ2 (.n stA.a)] = R.2.2.1 := ao.quad
  have htA := ao.t
  refine BlkF.mono hB fun σ' ⟨bo, ha3⟩ ↦ ⟨⟨?_, ?_, ?_, ?_, ?_, bo.fs, bo.can, bo.below, bo.pad,
    bo.padSome, by have := bo.k; have := ao.k; omega, bo.mats, bo.matsB⟩, fun i hi ↦ (ha3 i (by have := ao.k; omega)).trans
      (ha2' i hi)⟩
  · show (⟨_, [(σ' (.n _), dsObserve), (σ' (.n _), dsObserve)]⟩ : Fs) = _
    rw [bo.fsv, bo.w0, bo.w1]
  · rw [bo.quad, ← hqA]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · rw [bo.t, htA]
  · show σ' (.n _) * gen ^ _ = _
    rw [bo.cb, bo.co, ha3 _ ao.below.cb, pow_add, ← mul_assoc]
    show stA.cur σ2 * gen ^ 2 = _
    rw [hcurA, mul_assoc, ← pow_add]
  · rw [bo.co, ao.co]

end
end LeanVM.Guest.B1.Whir
