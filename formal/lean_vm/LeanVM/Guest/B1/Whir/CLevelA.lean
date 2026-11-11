/-
  LeanVM.Guest.B1.Whir.CLevelA

  A level up to its grinding check, honestly: its fold rounds, then its next commitment (or the
  final message) and the proof of work.
-/

module

public import LeanVM.Guest.B1.Whir.CLevelBN
public import LeanVM.Guest.B1.Whir.CCommit
public import LeanVM.Guest.B1.Whir.SpecLevel

/-!
# A level up to its grinding check, honestly

`osLevelA_final_complete`, `osLevelA_nonfinal_complete`: the rounds (`osFolds_complete`, at the
rate's fold grinding) on the words `xs`, then the final message (`osFinal_complete`) or the next commitment
(`osCommit_complete`), the sponges named from the rounds' (`cF1`, `cRest`, `cF2`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem osFolds_co (fr : Option (List String)) (p : ℕ) :
    ∀ (n off : ℕ) (st : OsSt), 0 < n → (osFolds fr p off n st).2.co = 0
  | 0, _, _, h => absurd h (by omega)
  | 1, _, _, _ => rfl
  | n + 2, off, st, _ => osFolds_co fr p (n + 1) (off + 1) _ (by omega)

/-- What a level leaves up to its grinding check. -/
structure LvAOut (σ' : Val) (st st2 : OsSt) (cap quad : List E) (t cur : E) (co : ℕ) : Prop where
  fsv : st2.fsv σ' = cap
  quad : st2.quad σ' = quad
  t : σ' (.n st2.t) = t
  cur : st2.cur σ' = cur
  fs : st2.fs.length = 5
  can : AllCanonical (st2.fsv σ')
  co : st2.co = co
  below : st2.Below
  pad : st2.pad = st.pad
  k : st.k ≤ st2.k
  mats : MatsOk σ' st2.mats
  matsB : MatsBelow st2.k st2.mats

/-- **The last level up to its grinding check, honestly.** -/
theorem osLevelA_final_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hfin : lvl = c.yrLevel)
    {Rs : E} (hRs : σ (.n osRate) = Rs) (hC : FoldCallC C rd (osFoldNames c lvl lv) lv.foldGrind Rs)
    (hFm : ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets →
      args.getD 8 0 = σ (.n osFmsg) → C ("opening_final_message__L" ++ natStr c.yrLen) args rets)
    (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr lv.grind) args rets)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below) (hk : 161 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats) {xs : List E} (hxl : xs.length = roundLen lv.foldGrind * lv.folds)
    (hrd : ReadsAt rd (st.cur σ) xs)
    (hpw : FoldsPow lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs)
    (hst : ∀ j, j < lv.folds → LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j)
      ((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.1.getD j 0))
    {ms : List E} {nonce : E} (hml : ms.length = c.yrLen)
    (hrd2 : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds)) (ms ++ [nonce]))
    (hout : ReadsAt rd (σ (.n osFmsg)) ms)
    (hpow : powOk Whir.queryGrindingBits nonce
      ((((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1.absorbAll ms dsObserve).absorb
        nonce dsPowNonce).squeeze.1) = true) :
    BlkF C rd σ st.k (osLvA c lvl lv st).2.1.k
      (seqF σ st.k (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k
        (foldsF (osFoldNames c lvl lv) lv.foldGrind osFch lv.folds lv.foldsOff st σ xs)
        fun σ1 ↦ osFinalF σ1 (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 ms nonce)
      (osLvA c lvl lv st).1
      (fun σ' ↦ LvAOut σ' st (osLvA c lvl lv st).2.1
        ((((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1.absorbAll ms
          dsObserve).absorb nonce dsPowNonce).squeeze.2.cap)
        (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.1
        (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.2
        (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + c.yrLen + 1)) 0 ∧ AgreeBelow st.k σ σ') := by
  set R := foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs with hR
  set st1 := (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 with hst1
  have e : osLvA c lvl lv st = ((osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).1 ++ ((osFinal c st1).1 ++
      [.call ("grind_check__L" ++ natStr lv.grind) [.n (osFinal c st1).2.2] []]),
      (osFinal c st1).2.1, (osFinal c st1).2.2) := by
    have hc : (lvl = c.yrLevel) = True := eq_true hfin
    simp only [osLvA, hc, ↓reduceIte, List.append_assoc]
    rfl
  rw [e]
  dsimp only
  have hA := osFolds_complete (C := C) (rd := rd) hC osFch lv.folds lv.foldsOff st σ xs hRs
    (by unfold osRate; omega) hfs hco hb (by unfold osFch; omega) hcan hxl hrd hpw hst
  have hk1 : st.k ≤ st1.k := osFolds_k (osFoldNames c lvl lv) osFch lv.folds lv.foldsOff st
  have hk2 : st1.k ≤ (osFinal c st1).2.1.k := by
    have := osMat_next st1.cb st1.co st1.k
    show st1.k ≤ (osMat st1.cb st1.co st1.k).2.2 + 8; omega
  refine BlkF.then (k1 := st1.k) (k2 := (osFinal c st1).2.1.k) hk1 hk2 hA
    fun σ1 ha1 ⟨fo, ha1'⟩ ↦ ?_
  have eF : σ1 (.n osFmsg) = σ (.n osFmsg) := ha1' _ (by unfold osFmsg; omega)
  have ecur : st.cur σ1 = st.cur σ := (OsSt.agree hb ha1').2.2.2.2
  have hrd1 : ReadsAt rd (st1.cur σ1) (ms ++ [nonce]) := by rw [fo.cur, ecur]; exact hrd2
  have hout1 : ReadsAt rd (σ1 (.n osFmsg)) ms := by rw [eF]; exact hout
  have hpow1 : powOk Whir.queryGrindingBits nonce
      (((st1.F σ1).absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.1 = true := by
    rw [fo.F]; exact hpow
  have hB := osFinal_complete (C := C) (rd := rd) (c := c) hFm hGr (st := st1) σ1 fo.fs fo.co fo.below
    fo.can (by unfold osFmsg; omega) eF hml hrd1 hout1 hpow1
  rw [fo.F] at hB
  refine BlkF.mono hB fun σ' ⟨fi, ha2⟩ ↦ ⟨⟨fi.F, ?_, ?_, ?_, fi.fs, fi.can, fi.co, fi.below, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · have := (OsSt.agree fo.below ha2).2.2.1
    show st1.quad σ' = _
    rw [this, fo.quad]
  · have := (OsSt.agree fo.below ha2).2.2.2.1
    show σ' (.n st1.t) = _
    rw [this, fo.t]
  · rw [fi.cur, (OsSt.agree fo.below ha2).2.2.2.2, fo.cur, ecur, mul_assoc, ← pow_add]
    ring_nf
  · rw [fi.pad, fo.pad]
  · omega
  · show MatsOk σ' (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.mats
    rw [osFolds_mats]
    exact matsOk_agree hmo hmob fun i hi ↦ (ha2 i (by omega)).trans (ha1' i hi)
  · show MatsBelow (osFinal c st1).2.1.k (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.mats
    rw [osFolds_mats]
    exact matsBelow_mono hmob (by omega)
  · intro i hi
    exact (ha2 i (by omega)).trans (ha1' i hi)

/-- **A level that is not the last, up to its grinding check, honestly.** -/
theorem osLevelA_nonfinal_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hnf : lvl ≠ c.yrLevel) (h1 : 1 ≤ lv.folds)
    {Rs : E} (hRs : σ (.n osRate) = Rs) (hC : FoldCallC C rd (osFoldNames c lvl lv) lv.foldGrind Rs)
    (hCan : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets)
    (hOod : ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
      C ("opening_ood_point__L" ++ natStr lv.logCols) args rets)
    (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr lv.grind) args rets)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below) (hk : 161 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hlvl : (lvl + 1) * ligColsCap < u128Bound)
    (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats)
    {xs : List E} (hxl : xs.length = roundLen lv.foldGrind * lv.folds)
    (hrd : ReadsAt rd (st.cur σ) xs)
    (hpw : FoldsPow lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs)
    (hst : ∀ j, j < lv.folds → LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j)
      ((foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.1.getD j 0))
    {ra rb y c0 c2 nonce : E} {d : Digest} (hd : (ra, rb) = digestHalves d)
    (hrd2 : ReadsAt rd (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds)) [ra, rb, y, c0, c2, nonce])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) ra)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) rb)
    (hz : ReadsAt rd (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap))
      (challengeOf (cF1 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb).perm ::
        (cRest (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb lv.logCols).1))
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2)
    (hpow : powOk Whir.queryGrindingBits nonce
      (cF2 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb lv.logCols y c0 c2
        nonce).squeeze.1 = true) :
    BlkF C rd σ st.k (osLvA c lvl lv st).2.1.k
      (seqF σ st.k (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k
        (foldsF (osFoldNames c lvl lv) lv.foldGrind osFch lv.folds lv.foldsOff st σ xs)
        fun σ1 ↦ fun j ↦ segLookup (commitSegs c.plan σ1 (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 lvl
          lv.logCols ra rb y c0 c2 nonce) (j - (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2.k))
      (osLvA c lvl lv st).1
      (fun σ' ↦ LvAOut σ' st (osLvA c lvl lv st).2.1
        (capOf (cF2 (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).1 ra rb lv.logCols y c0
          c2 nonce).perm)
        (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.1
        (foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.2.2
        (st.cur σ * gen ^ (roundLen lv.foldGrind * lv.folds + 6)) 6 ∧ AgreeBelow st.k σ σ') := by
  set R := foldsTr lv.foldGrind lv.folds (st.F σ) (st.quad σ) (σ (.n st.t)) xs with hR
  set st1 := (osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).2 with hst1
  have e : osLvA c lvl lv st = ((osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds st).1 ++
      ((osCommit c.plan lvl lv st1).1 ++
        [.call ("grind_check__L" ++ natStr lv.grind) [.n (osCommit c.plan lvl lv st1).2.2] []]),
      (osCommit c.plan lvl lv st1).2.1, (osCommit c.plan lvl lv st1).2.2) := by
    have hc : (lvl = c.yrLevel) = False := eq_false hnf
    simp only [osLvA, hc, ↓reduceIte, List.append_assoc]
    rfl
  rw [e]
  dsimp only
  have hA := osFolds_complete (C := C) (rd := rd) hC osFch lv.folds lv.foldsOff st σ xs hRs
    (by unfold osRate; omega) hfs hco hb (by unfold osFch; omega) hcan hxl hrd hpw hst
  have hk1 : st.k ≤ st1.k := osFolds_k (osFoldNames c lvl lv) osFch lv.folds lv.foldsOff st
  have hk2 : st1.k ≤ (osCommit c.plan lvl lv st1).2.1.k := by
    show st1.k ≤ st1.k + 110; omega
  refine BlkF.then (k1 := st1.k) (k2 := (osCommit c.plan lvl lv st1).2.1.k) hk1 hk2 hA
    fun σ1 ha1 ⟨fo, ha1'⟩ ↦ ?_
  have ecur : st.cur σ1 = st.cur σ := (OsSt.agree hb ha1').2.2.2.2
  have e1 : ∀ v, v < st.k → σ1 (.n v) = σ (.n v) := fun v hv ↦ ha1' v hv
  have hrd1 : ReadsAt rd (st1.cur σ1) [ra, rb, y, c0, c2, nonce] := by
    rw [fo.cur, ecur]; exact hrd2
  have hz1 : ReadsAt rd (σ1 (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap))
      (challengeOf (commitF1 σ1 st1 ra rb).perm :: (commitRest σ1 st1 ra rb lv.logCols).1) := by
    rw [commitF1_eq, commitRest_eq, fo.F, e1 osOodz (by unfold osOodz; omega)]; exact hz
  have hpow1 : powOk Whir.queryGrindingBits nonce
      (commitF2 σ1 st1 ra rb lv.logCols y c0 c2 nonce).squeeze.1 = true := by
    rw [commitF2_eq, fo.F]; exact hpow
  have hB := osCommit_complete (C := C) (rd := rd) (plan := c.plan) (lvl := lvl) (lv := lv) hCan hOod hGr (st := st1)
    σ1 fo.fs fo.below (by omega) fo.can hlvl
    (by rw [hst1, osFolds_mats]; exact matsOk_agree hmo hmob ha1')
    (by rw [hst1, osFolds_mats]; exact matsBelow_mono hmob hk1) hd hrd1
    (by rw [e1 osRoots (by unfold osRoots; omega)]; exact hr0)
    (by rw [e1 osRoots (by unfold osRoots; omega)]; exact hr1) hz1
    (by rw [e1 osOod (by unfold osOod; omega)]; exact hy)
    (by rw [e1 osOod (by unfold osOod; omega)]; exact hc0)
    (by rw [e1 osOod (by unfold osOod; omega)]; exact hc2) hpow1
  rw [commitF2_eq, fo.F] at hB
  refine BlkF.mono hB fun σ' ⟨co, ha2⟩ ↦ ⟨⟨co.fsv, ?_, ?_, ?_, co.fs, co.can, ?_, co.below, ?_, ?_,
    co.mats, co.matsB⟩, ?_⟩
  · have := (OsSt.agree fo.below ha2).2.2.1
    show st1.quad σ' = _
    rw [this, fo.quad]
  · have := (OsSt.agree fo.below ha2).2.2.2.1
    show σ' (.n st1.t) = _
    rw [this, fo.t]
  · rw [co.cur, (OsSt.agree fo.below ha2).2.2.2.2, fo.cur, ecur, mul_assoc, ← pow_add]
  · rw [co.co, osFolds_co (osFoldNames c lvl lv) osFch lv.folds lv.foldsOff st h1]
  · rw [co.pad, fo.pad]
  · show st.k ≤ st1.k + 110; omega
  · intro i hi
    exact (ha2 i (by omega)).trans (ha1' i hi)

end
end LeanVM.Guest.B1.Whir
