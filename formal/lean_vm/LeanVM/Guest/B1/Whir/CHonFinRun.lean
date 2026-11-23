/-
  LeanVM.Guest.B1.Whir.CHonFinRun

  What `fin_of` takes of the run, from an accepting run's honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CHonInv
public import LeanVM.Guest.B1.Whir.CHonFin
public import LeanVM.Guest.B1.Whir.CHonStaticAll
public import LeanVM.Guest.B1.Whir.CHonAllocAll
public import LeanVM.Guest.B1.Whir.Vanish
public import LeanVM.Guest.B1.Whir.HsScale
public import LeanVM.Guest.B1.Whir.CHonFields0

/-!
# The finish's run facts

On `hR : HonRun μ r … cfg Ls`, at `h := hdOf μ r Ls`: the finish's static facts
(`HonRun.finStatic_run`), each non-final level's record facts (`HonRun.recRun_run`), the final
lane's length (`HonRun.hylen`, `HonRun.hfold`) and `fold_final_msg`'s kind (`HonRun.hffm`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem osCfgR_len (m ri : ℕ) : (osCfgR m ri).levels.length = osNLevels m := by
  simp [osCfgR, osLevelsR]

theorem osCfgR_getD {m ri l : ℕ} (hl : l < osNLevels m) :
    (osCfgR m ri).levels.getD l default = osLvR m ri l := by
  simp [osCfgR, osLevelsR, List.getD_eq_getElem?_getD, hl]

theorem osNLevels_le : ∀ m < 11, osNLevels m ≤ 6 := by decide +kernel

/-- A level's rate-free columns are every rate's. -/
theorem osLvR_rateFree (m ri l : ℕ) : (osLvR m ri l).folds = (osLv m l).folds ∧
    (osLvR m ri l).vanish = (osLv m l).vanish ∧ (osLvR m ri l).highBits = (osLv m l).highBits ∧
    (osLvR m ri l).logCols = (osLv m l).logCols := by
  unfold osLvR; exact ⟨rfl, rfl, rfl, rfl⟩

theorem sqCount_mul {P q : ℕ} (hP : 1 ≤ P) : q ≤ sqCount P q * P := by
  unfold sqCount
  have h1 := Nat.div_add_mod (q + P - 1) P
  have h2 := Nat.mod_lt (q + P - 1) (show 0 < P by omega)
  generalize (q + P - 1) / P = d at h1 ⊢
  generalize (q + P - 1) % P = e at h1 h2
  rw [Nat.mul_comm] at h1
  omega

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- The final level's folds end at `nFolds`. -/
theorem fin_s1 : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas.length =
    (osCfgR (μ - minOpenLog) (r - 1)).nFolds := by
  have hy := hR.yr
  obtain ⟨cF, -, -, -, -, -, cyl, -⟩ := hR.cand
  obtain ⟨-, ffold, flog, -⟩ := hR.fin
  rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas _ (by omega), ffold]
  omega

/-- A non-final level's record. -/
theorem rec_eq {i : ℕ} (hi : i < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    ∃ rw W, (Ls.getD i default).d = .next rw W ∧ (Ls.getD i default).rw = rw ∧
      (Ls.getD i default).osRec μ = W.osRec μ (Ls.getD i default).level (Ls.getD i default).s1
        (Ls.getD i default).F ∧
      NextOk μ i (Ls.getD i default).level (Ls.getD i default).s1 (Ls.getD i default).F
        (Ls.getD i default).R W := by
  obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := hR.step hi
  have hrw : (Ls.getD i default).rw = rw := by unfold LvAt.rw; rw [hd]
  refine ⟨rw, W, hd, hrw, by unfold LvAt.osRec; rw [hd], ?_⟩
  rw [LvAt.s1, LvAt.F, hrw]
  exact hok

theorem rec_F {i : ℕ} (hi : i < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    ((Ls.getD i default).osRec μ).F =
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).foldsOff + (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).folds := by
  have hy := hR.yr
  obtain ⟨rw, W, -, -, he, -⟩ := hR.rec_eq hi
  obtain ⟨-, hf, -⟩ := hR.mid hi
  rw [he]
  show (Ls.getD i default).s1.alphas.length = _
  rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas _ (by omega), hf]

theorem rec_mu {i : ℕ} (hi : i < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    μ - (Ls.getD i default).s1.alphas.length = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).logCols := by
  have hy := hR.yr
  obtain ⟨-, hf, hm, -⟩ := hR.mid hi
  rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas _ (by omega), hf]
  exact hm

/-- A non-final level's `LvFin`. -/
theorem lvFin {i : ℕ} (hi : i < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    LvFin (osCfgR (μ - minOpenLog) (r - 1)) (finLv (osCfgR (μ - minOpenLog) (r - 1)) i) (finLv (osCfgR (μ - minOpenLog) (r - 1)) (i + 1)) := by
  have hy := hR.yr
  have hm : μ - minOpenLog < ligNSizes := hR.m11
  have hn : i < osNLevels (μ - minOpenLog) := by rw [← osCfgR_len _ (r - 1)]; omega
  have hv := vanish_allR (ri := r - 1) hm hn
  have hs : ∀ c' < (osLvR (μ - minOpenLog) (r - 1) i).folds,
      K.ofBits (hsScale (osLvR (μ - minOpenLog) (r - 1) i).vanish (osLvR (μ - minOpenLog) (r - 1) i).highBits c'
        (vanishInv ((osLvR (μ - minOpenLog) (r - 1) i).vanish + (osLvR (μ - minOpenLog) (r - 1) i).logCols))) =
      ((Verifier.subspaceRoots (osLvR (μ - minOpenLog) (r - 1) i).logCols).getD
        (osLvR (μ - minOpenLog) (r - 1) i).logCols 0)⁻¹ *
        hsNorm (osLvR (μ - minOpenLog) (r - 1) i).logCols (osLvR (μ - minOpenLog) (r - 1) i).highBits c' := by
    intro c' hc
    obtain ⟨e1, e2, e3, e4⟩ := osLvR_rateFree (μ - minOpenLog) (r - 1) i
    rw [e1] at hc
    rw [e2, e3, e4]
    exact hsScale_mid hm hn hc
  have e : finLv (osCfgR (μ - minOpenLog) (r - 1)) i = osLvR (μ - minOpenLog) (r - 1) i := osCfgR_getD hn
  obtain ⟨-, -, -, h1, -, -, -, -, -, -, -, -, h2, -, -, -, -, -, -, -, h3, -, -, -, -, -, -, -, -, -, -,
    -, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hR.mid hi
  rw [← e] at hv hs
  exact ⟨h4, h5, h6, h7, h3, h1, h8, h9, h10, h11, h12, h2, h13, vanish_val hv, vanish_inv hv, hs⟩

/-- **The finish's static facts.** -/
theorem finStatic_run :
    FinStatic (hdOf μ r Ls).c (hdOf μ r Ls).G (hdOf μ r Ls).T (hdOf μ r Ls).recs := by
  show FinStatic (osCfgR (μ - minOpenLog) (r - 1)) (hdOf μ r Ls).G (hdOf μ r Ls).T (hdOf μ r Ls).recs
  have hy := hR.yr
  have hL := hR.len
  obtain ⟨cF, -, -, -, cn2, cyr, cyl, -, -, clane, cmu, -, -⟩ := hR.cand
  obtain ⟨rw, W, hd, -, hrok, -, -, hok, -⟩ := hR.last
  have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hfw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  rw [← hrw] at hrok hok
  have hs1 := hR.fin_s1
  have hm11 : μ - minOpenLog < 11 := hR.m11
  have hHS := honStatic_all _ _ hm11 hR.r4
  set Lf := Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default
  refine ⟨cn2, by rw [osCfgR_len]; exact osNLevels_le _ hm11, cyr, cyl, ?_, fun i hi ↦ hR.lvFin hi,
    hs1, ?_, clane, cmu, fun i hi ↦ ?_, fun i hi ↦ (hHS.mid hi).1⟩
  · show (lvsRecs μ Ls (osCfgR (μ - minOpenLog) (r - 1)).yrLevel).length = _
    simp only [lvsRecs, List.length_map, List.length_take]; omega
  · show (tailRun Lf.fw.pairs (Lf.F3 μ).cap (hdOf μ r Ls).cl1F).1.length = _
    rw [tailRun_length, hfw, hok.plen2]
    show μ - Lf.s1.alphas.length = _
    rw [hs1]; omega
  · rw [(hdOf μ r Ls).recs_getD hL hy hi]
    exact hR.rec_F hi

/-- **Each non-final level's record facts.** -/
theorem recRun_run : ∀ i < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel, RecRun (hdOf μ r Ls) i := by
  intro i hi
  obtain ⟨rw, W, hd, -, he, hok⟩ := hR.rec_eq hi
  obtain ⟨-, hf, -, -, hdep, hq, -, -, hP, hsq, -⟩ := hR.mid hi
  have hmu := hR.rec_mu hi
  have hdep' : (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).depth = (Ls.getD i default).dp μ := by
    rw [hdep]; show _ = μ - (Ls.getD i default).s1.alphas.length + _; rw [hmu]
  refine ⟨hR.rec_F hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((Ls.getD i default).osRec μ).mu = _
    rw [he]; exact hmu
  · show ((Ls.getD i default).osRec μ).qs.length = _
    rw [LvAt.osRec_qs _ _ hd, LvAt.qs_length, hq]; rfl
  · show ((Ls.getD i default).osRec μ).high.length = _
    rw [he]; show W.high.length = _; rw [hok.hlen, hf]; rfl
  · show ((Ls.getD i default).osRec μ).z0.length = _
    rw [he]
    show (W.ood (Ls.getD i default).F (μ - (Ls.getD i default).s1.alphas.length)).length =
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).logCols
    rw [NextW.ood, oodPt_eq, List.length_cons, squeezeN_length, hmu]
    have := hok.mu1
    omega
  · show (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).queries ≤
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).squeezes * sqPer (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default))
    rw [hsq]; exact sqCount_mul hP
  · intro k hk
    show ((Ls.getD i default).osRec μ).qs.getD k 0 = _
    rw [LvAt.osRec_qs _ _ hd]
    exact LvAt.qs_getD_eq _ _ hdep' hq k hk

/-- `2 ^ yrLog = yrLen`. -/
theorem hylen : 2 ^ (hdOf μ r Ls).c.yrLog = (hdOf μ r Ls).c.yrLen := hR.cand.2.2.2.2.2.2.2.1

/-- The final lane holds `yrLen` words at least. -/
theorem hfold : (hdOf μ r Ls).c.yrLen ≤ (hdOf μ r Ls).Lf.fw.fold.length := by
  obtain ⟨cF, -, -, -, -, -, cyl, cylen, -⟩ := hR.cand
  obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := hR.last
  have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hfw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  rw [← hrw] at hok
  show _ ≤ (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw.fold.length
  rw [hfw, hok.flen]
  show _ ≤ 2 ^ (μ - (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas.length) + _
  rw [hR.fin_s1, show μ - (osCfgR (μ - minOpenLog) (r - 1)).nFolds = (osCfgR (μ - minOpenLog) (r - 1)).yrLog by omega, cylen]
  show (osCfgR (μ - minOpenLog) (r - 1)).yrLen ≤ _
  omega

/-- `fold_final_msg`'s kind. -/
theorem hffm : osKindOf ("fold_final_msg__L" ++ natStr (hdOf μ r Ls).c.yrLog) =
    some (.ffm (hdOf μ r Ls).c.yrLog) := by
  have hm := hR.cand.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [foldFinalMsgNames, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  show osKindOf ("fold_final_msg__L" ++ natStr (osCfgR (μ - minOpenLog) (r - 1)).yrLog) =
    some (.ffm (osCfgR (μ - minOpenLog) (r - 1)).yrLog)
  rcases hm with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> decide

end HonRun

end
end LeanVM.Guest.B1.Whir
