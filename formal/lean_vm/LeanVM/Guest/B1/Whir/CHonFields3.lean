/-
  LeanVM.Guest.B1.Whir.CHonFields3

  The honest data's point buffers, squeeze capacities, rounds, final lane and positions: OsHonest's
  simpler fields.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields2
public import LeanVM.Guest.B1.Whir.CHonStaticAll
public import LeanVM.Guest.B1.Whir.CHonMemFin

/-!
# OsHonest's simpler fields

On `hR : HonRun μ r … cfg Ls`, `h := hdOf μ r Ls`: the point buffers are the run's point
zero-padded and one plus it one-padded (`fld_own_pt`, `fld_own_pt1`), the squeezes' capacities
have five cells and squeeze to the samples (`fld_cap_len`, `fld_cap_word`), each level's rounds
are its `opening_queries`' folds (`fld_rounds_len`), the final lane is its coefficients
(`fld_hsv_len`), and the positions are the samples' windows (`fld_qs_eq`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The closing rounds' challenges do not depend on the claim. -/
theorem tailRun_fst (p : List (E × E)) (cap : List E) (a b : E) :
    (tailRun p cap a).1 = (tailRun p cap b).1 := by
  have := (tailRun_add p cap a (a + b)).2.1
  rw [show a + (a + b) = b by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]] at this
  exact this.symm

theorem fld_cap_len (Ls : List LvAt) (logN : ℕ) :
    ∀ l j, ((Ls.getD l default).capSq logN j).length = 5 :=
  fun _ _ ↦ capSq_length _ _ _

theorem fld_cap_word (Ls : List LvAt) (logN : ℕ) :
    ∀ l j, 1 ≤ j → (⟨(Ls.getD l default).capSq logN j, []⟩ : Fs).squeeze.1 =
      (Ls.getD l default).word logN j :=
  fun _ _ hj ↦ capSq_word _ _ hj

theorem oq_folds (sh : OqShape) : sh.oq.folds = sh.folds := rfl
theorem oq_final (sh : OqShape) : sh.oq.final = sh.final := rfl
theorem oq_nHs (sh : OqShape) : sh.oq.nHs = sh.nHs := rfl
theorem oq_base (sh : OqShape) : sh.oq.base = sh.base := rfl
theorem oq_pd (sh : OqShape) : sh.oq.pd = sh.depth - sh.cd := rfl
theorem oq_cd (sh : OqShape) : sh.oq.cd = sh.cd := rfl
theorem oq_vs (sh : OqShape) : sh.oq.vs = sh.vs := rfl
theorem oq_hsBits (sh : OqShape) : sh.oq.hsBits = sh.hsBits := rfl

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The final level's terminal point**: the fold challenges, the tail challenges, rotated. -/
theorem finPt :
    (hdOf μ r Ls).G.length = (osCfg (candidate μ r)).nFolds ∧
      (hdOf μ r Ls).T.length = (osCfg (candidate μ r)).yrLog ∧
      w.point = rotPt (hdOf μ r Ls).G (hdOf μ r Ls).T ((osCfg (candidate μ r)).levels.headD default).folds ∧
      (osCfg (candidate μ r)).nFolds + (osCfg (candidate μ r)).yrLog = μ ∧
      ((osCfg (candidate μ r)).levels.headD default).folds ≤ (osCfg (candidate μ r)).nFolds ∧
      (osCfg (candidate μ r)).nFolds + (osCfg (candidate μ r)).yrLog ≤ pointCap := by
  have hS : HonStatic (osCfg (candidate μ r)) := honStatic_all _ hR.m28
  have hy := hR.yr
  obtain ⟨hmu, -, -, hlane, -, -, -, -, -, hla, h40, -⟩ := hR.cand
  have hB := hR.lvb (l := (osCfg (candidate μ r)).yrLevel) (by omega)
  obtain ⟨rw, W, hd, -, -, -, -, hfin, hw⟩ := hR.last
  have hfw : (Ls.getD (osCfg (candidate μ r)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  have hrw : (Ls.getD (osCfg (candidate μ r)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hF3 : (Ls.getD (osCfg (candidate μ r)).yrLevel default).F3 μ =
      W.F3 (Ls.getD (osCfg (candidate μ r)).yrLevel default).F
        ((Ls.getD (osCfg (candidate μ r)).yrLevel default).dp μ)
        (Ls.getD (osCfg (candidate μ r)).yrLevel default).level.queries := by
    unfold LvAt.F3; rw [hd]
  have hG : (hdOf μ r Ls).G = (Ls.getD (osCfg (candidate μ r)).yrLevel default).s1.gammas := rfl
  have hT : (hdOf μ r Ls).T = (tailRun W.pairs ((Ls.getD (osCfg (candidate μ r)).yrLevel default).F3 μ).cap
      (Ls.getD (osCfg (candidate μ r)).yrLevel default).s1.claim).1 := by
    show (tailRun (Ls.getD (osCfg (candidate μ r)).yrLevel default).fw.pairs _ _).1 = _
    rw [hfw]; exact tailRun_fst _ _ _ _
  have hpl := hfin.plen2
  rw [← hrw] at hpl
  have hGl : (hdOf μ r Ls).G.length = (osCfg (candidate μ r)).nFolds := by
    rw [hG, hB.g1, hB.fold.symm.trans hB.fold, ← HonStatic.foT hS]
  refine ⟨hGl, ?_, ?_, hmu, hla, h40⟩
  · rw [hT, tailRun_length, hpl]
    have := hB.mu
    simp only [LvAt.mu] at this
    rw [this]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlc, -⟩ := hR.fin
    exact hlc
  · subst hw
    rw [← hrw] at *
    simp only [FinW.wend, FinW.tail, rotPt, hlane]
    rw [hT, hF3, hG]

/-- **`point`'s buffer** is the run's point zero-padded. -/
theorem fld_own_pt :
    (hdOf μ r Ls).own.getD (osIxPT (hdOf μ r Ls).c) [] = w.point ++ List.replicate (pointCap - μ) 0 := by
  have hS : HonStatic (osCfg (candidate μ r)) := honStatic_all _ hR.m28
  obtain ⟨hGl, hTl, hpt, hmu, hla, h40⟩ := hR.finPt
  have e : osIxPT (hdOf μ r Ls).c = 13 + 2 * (osCfg (candidate μ r)).levels.length + 1 := by
    show 14 + 2 * (osCfg (candidate μ r)).levels.length = _; ring
  have hsz := HonStatic.fin hS (k := 1) (by omega)
  have hown := OsHD.own_getD (hdOf μ r Ls) (HonStatic.finLt hS (k := 1) (by omega))
  have hw : (hdOf μ r Ls).ownW (13 + 2 * (osCfg (candidate μ r)).levels.length + 1) =
      finPtC (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T :=
    OsHD.ownW_fin (hdOf μ r Ls) (k := 1) (by omega)
  have e1 : ([yrLogCap, pointCap, pointCap, (osCfg (candidate μ r)).levels.length * ligColsCap,
      (osCfg (candidate μ r)).levels.length, (osCfg (candidate μ r)).levels.length,
      2 * (osCfg (candidate μ r)).levels.length] : List ℕ).getD 1 0 = pointCap := rfl
  rw [e1] at hsz
  have hlen : (finPtC (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T).length = pointCap := by
    unfold finPtC rotPt
    simp only [List.length_append, List.length_replicate, List.length_drop, List.length_take, hGl, hTl]
    omega
  rw [e, hown, OsHD.ownAt, hw]
  change fitTo ((osSizesF (osCfg (candidate μ r))).getD (13 + 2 * (osCfg (candidate μ r)).levels.length + 1) 0)
    (finPtC (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T) = _
  rw [hsz, fitTo_eq hlen]
  unfold finPtC
  rw [← hpt, hmu]

/-- **`point1`'s buffer** is one plus the run's point, one-padded. -/
theorem fld_own_pt1 :
    (hdOf μ r Ls).own.getD (osIxPT1 (hdOf μ r Ls).c) [] =
      w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1 := by
  have hS : HonStatic (osCfg (candidate μ r)) := honStatic_all _ hR.m28
  obtain ⟨hGl, hTl, hpt, hmu, hla, h40⟩ := hR.finPt
  have e : osIxPT1 (hdOf μ r Ls).c = 13 + 2 * (osCfg (candidate μ r)).levels.length + 2 := by
    show 15 + 2 * (osCfg (candidate μ r)).levels.length = _; ring
  have hsz := HonStatic.fin hS (k := 2) (by omega)
  have hown := OsHD.own_getD (hdOf μ r Ls) (HonStatic.finLt hS (k := 2) (by omega))
  have hw : (hdOf μ r Ls).ownW (13 + 2 * (osCfg (candidate μ r)).levels.length + 2) =
      finPt1C (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T :=
    OsHD.ownW_fin (hdOf μ r Ls) (k := 2) (by omega)
  have e1 : ([yrLogCap, pointCap, pointCap, (osCfg (candidate μ r)).levels.length * ligColsCap,
      (osCfg (candidate μ r)).levels.length, (osCfg (candidate μ r)).levels.length,
      2 * (osCfg (candidate μ r)).levels.length] : List ℕ).getD 2 0 = pointCap := rfl
  rw [e1] at hsz
  have hlen : (finPt1C (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T).length = pointCap := by
    unfold finPt1C rotPt
    simp only [List.length_append, List.length_replicate, List.length_map, List.length_drop,
      List.length_take, hGl, hTl]
    omega
  rw [e, hown, OsHD.ownAt, hw]
  change fitTo ((osSizesF (osCfg (candidate μ r))).getD (13 + 2 * (osCfg (candidate μ r)).levels.length + 2) 0)
    (finPt1C (osCfg (candidate μ r)) (hdOf μ r Ls).G (hdOf μ r Ls).T) = _
  rw [hsz, fitTo_eq hlen]
  unfold finPt1C
  rw [← hpt, hmu]

/-- **Each level's rounds** are its `opening_queries`' folds. -/
theorem fld_rounds_len : ∀ l < (osCfg (candidate μ r)).levels.length,
    (Ls.getD l default).rounds.length = (oqS (osCfg (candidate μ r)) l).folds := by
  intro l hl
  have hB := hR.lvb hl
  obtain ⟨-, -, -, hfolds, -⟩ := hB.qsh
  rw [oqS, oq_folds, hfolds, LvAt.rounds, roundsSpec_rounds_length, hB.fold]

/-- **The final lane** has the final level's coefficients' count. -/
theorem fld_hsv_len : ∀ l < (osCfg (candidate μ r)).levels.length,
    (oqS (osCfg (candidate μ r)) l).final = 1 →
      (if l = (osCfg (candidate μ r)).yrLevel then (hdOf μ r Ls).hsFC else []).length =
        (oqS (osCfg (candidate μ r)) l).nHs := by
  intro l hl hf
  have hB := hR.lvb hl
  obtain ⟨-, -, -, -, -, -, hfinal, -⟩ := hB.qsh
  rw [oqS, oq_final, hfinal] at hf
  rw [oqS, oq_nHs]
  by_cases he : l = (osCfg (candidate μ r)).yrLevel
  · subst he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnHs, -⟩ := hR.fin
    simp only [↓reduceIte]
    rw [hnHs, OsHD.hsFC, List.length_map, List.length_range]
    rfl
  · simp [he] at hf

/-- **The positions are the samples' windows.** -/
theorem fld_qs_eq : ∀ l < (osCfg (candidate μ r)).levels.length, ∀ k < oqQ (osCfg (candidate μ r)) l,
    ((Ls.getD l default).qs μ).getD k 0 =
      qwPosOf (osLvAt (osCfg (candidate μ r)) l).depth
        ((Ls.getD l default).word μ (k / sqPer (osLvAt (osCfg (candidate μ r)) l)))
        (k % sqPer (osLvAt (osCfg (candidate μ r)) l)) := by
  intro l hl k hk
  have hB := hR.lvb hl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcount⟩ := hB.qsh
  rw [oqQ, oqOdd, oqS, oq_base, oqN, hcount] at hk
  exact (Ls.getD l default).qs_getD_eq μ hB.dep hB.q k hk

end HonRun

end
end LeanVM.Guest.B1.Whir
