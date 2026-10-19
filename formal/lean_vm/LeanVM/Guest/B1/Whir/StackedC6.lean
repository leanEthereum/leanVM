/-
  LeanVM.Guest.B1.Whir.StackedC6

  A level of `open_stacked` at its honest values: its folds, its residual or next commitment,
  its nonce.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC5

/-!
# A level, honestly: the first part (TRIAGE #36)

`osLevelA_complete`: from the level's data (`OsLvOk`), the fold rounds, the residual's message or
the next commitment with its out-of-domain sample, and the query nonce hold at the values
`osLvValsA`, and the guest's state after them is at the specification's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The level's fold rounds. -/
def osLvF (cfg : OsCfg) (lvl : ℕ) (s : OsSt) : List Stmt × OsSt :=
  osFolds osFch (cfg.lv lvl).foldsOff (cfg.lv lvl).folds s

/-- The level's residual message or next commitment. -/
def osLvM (cfg : OsCfg) (lvl : ℕ) (s : OsSt) : List Stmt × OsSt :=
  if lvl = cfg.yrLevel then osFinal cfg.finalMsg osFmsg (osLvF cfg lvl s).2
  else osCommit lvl (cfg.lv lvl).logCols (cfg.lv lvl).oodNext osRoots osOodz osOod (osLvF cfg lvl s).2

/-- The level's query nonce. -/
def osLvG (cfg : OsCfg) (lvl : ℕ) (s : OsSt) : List Stmt × OsSt :=
  osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2

/-- The values of the level's first part from its first: the folds' (the cursor's base at `cur`),
the residual's or the next commitment's, the nonce's. -/
def osLvValsA (cfg : OsCfg) (lvl : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (w : WhirState) (H : OsLvH)
    (co : ℕ) (cur oodzv : E) : List E :=
  osFoldsVals xs (cfg.lv lvl).folds cv p w.quad (cur * gen ^ (p - co)) co ++
    (if lvl = cfg.yrLevel then osFinalVals H.cv1 (osHMs cfg lvl xs p) (cur * gen ^ osHP1 cfg lvl p) 0 cfg.yrLen
    else osCommitVals lvl (cfg.lv lvl).logCols oodzv H.cv1 (osHW cfg lvl xs p 0) (osHW cfg lvl xs p 1)
      (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4)) ++
    osGrindVals (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2 cfg lvl xs p H.cv1)

theorem os_cb_of_at {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p) (h : s.co ≤ p) :
    σ (.n s.cb) = cur * gen ^ (p - s.co) := by
  have hc := hat.cursor
  rw [show p = p - s.co + s.co by omega, pow_add, ← mul_assoc] at hc
  exact mul_right_cancel₀ (gen_pow_ne_zero _) hc

/-- **A level's first part** at its honest values (G:1096-1142). -/
theorem osLevelA_complete {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {cv : Digest} {p : ℕ} {w : WhirState}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH}
    (hok : OsLvOk cfg lvl xs p μ L cv w osp roots H) {s : OsSt} {cur oodzv : E}
    (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco8 : s.co ≤ 8)
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) (hoz : σ (.n osOodz) = oodzv)
    (hxs : ∀ j < xs.length, LoadHolds rd cur j (xs.getD j 0))
    (hfch : ∀ j < (cfg.lv lvl).folds, LoadHolds rd (σ (.n osFch)) ((cfg.lv lvl).foldsOff + j) (H.chs.getD j 0))
    (hrt2 : lvl ≠ cfg.yrLevel → LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) (osHW cfg lvl xs p 0) ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) (osHW cfg lvl xs p 1))
    (hood : lvl ≠ cfg.yrLevel → LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 1) (osHW cfg lvl xs p 2) ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 2) (osHW cfg lvl xs p 3) ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 3) (osHW cfg lvl xs p 4))
    {kret : List E → Prop}
    (hcf : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p')))
    (hcm : lvl = cfg.yrLevel → C cfg.finalMsg [(digestScalars H.cv1).1, (digestScalars H.cv1).2,
      cur * gen ^ osHP1 cfg lvl p, σ (.n osFmsg)]
      [(digestScalars (osHCv2 cfg lvl xs p H.cv1)).1, (digestScalars (osHCv2 cfg lvl xs p H.cv1)).2,
        cur * gen ^ osHP2 cfg lvl p])
    (hca : lvl ≠ cfg.yrLevel → C "assert_canonical" [osHW cfg lvl xs p 0] [0] ∧
      C "assert_canonical" [osHW cfg lvl xs p 1] [0] ∧
      C "opening_ood_point" [(digestScalars (osHCv12 cfg lvl xs p H.cv1)).1,
        (digestScalars (osHCv12 cfg lvl xs p H.cv1)).2, oodzv * osGw ((lvl + 1 + 0) * 22), osGw (cfg.lv lvl).logCols]
        [(digestScalars (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p H.cv1)).2).1,
          (digestScalars (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p H.cv1)).2).2])
    (hcg : C "grind_check" [(digestScalars (osHCv2 cfg lvl xs p H.cv1)).1,
      (digestScalars (osHCv2 cfg lvl xs p H.cv1)).2, osHNonce cfg lvl xs p, osGw (cfg.lv lvl).grindBits] [])
    (hv : ∀ j < (osLvValsA cfg lvl xs cv p w H s.co cur oodzv).length,
      σ (.n (s.k + j)) = (osLvValsA cfg lvl xs cv p w H s.co cur oodzv).getD j 0) :
    Stmt.HoldsList C rd σ ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) True kret ∧
      OsAt σ (osLvG cfg lvl s).2 (osHCv3 cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p + 1) ∧
      (osLvG cfg lvl s).2.co = (if lvl = cfg.yrLevel then 1 else 6) ∧
      H.w1.quad = [σ (.n (osLvG cfg lvl s).2.c), σ (.n (osLvG cfg lvl s).2.b), σ (.n (osLvG cfg lvl s).2.a)] ∧
      H.w1.target = σ (.n (osLvG cfg lvl s).2.t) ∧
      (osLvG cfg lvl s).2.k = s.k + (osLvValsA cfg lvl xs cv p w H s.co cur oodzv).length := by
  obtain ⟨hf, hf0, hqq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  have hcb := os_cb_of_at hat hcop
  set Vf := osFoldsVals xs (cfg.lv lvl).folds cv p w.quad (cur * gen ^ (p - s.co)) s.co with hVf
  set Vm := (if lvl = cfg.yrLevel then osFinalVals H.cv1 (osHMs cfg lvl xs p) (cur * gen ^ osHP1 cfg lvl p) 0
      cfg.yrLen
    else osCommitVals lvl (cfg.lv lvl).logCols oodzv H.cv1 (osHW cfg lvl xs p 0) (osHW cfg lvl xs p 1)
      (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4)) with hVm
  set Vg := osGrindVals (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2 cfg lvl xs p H.cv1) with hVg
  have hVA : osLvValsA cfg lvl xs cv p w H s.co cur oodzv = Vf ++ Vm ++ Vg := rfl
  rw [hVA] at hv ⊢
  have hlg : Vg.length = 16 := by simp [hVg, osGrindVals]
  -- the folds
  have hvf : ∀ j < (osFoldsVals xs (cfg.lv lvl).folds cv p w.quad (σ (.n s.cb)) s.co).length,
      σ (.n (s.k + j)) = (osFoldsVals xs (cfg.lv lvl).folds cv p w.quad (σ (.n s.cb)) s.co).getD j 0 := by
    rw [hcb]
    intro j hj
    have hj' : j < Vf.length := hj
    rw [hv j (by simp only [List.length_append]; omega), List.append_assoc, oq_getD_app_lt hj']
  have hrunF : Runs (foldRounds (cfg.lv lvl).folds w []) ⟨cv, xs.drop p, osp, roots⟩ (H.w1, H.chs)
      ⟨H.cv1, xs.drop (p + 2 * (cfg.lv lvl).folds), osp, roots⟩ := by
    rw [hf]; have := hok.folds; rw [osHP1, hf] at this; exact this
  obtain ⟨hF, hatF, hsp, hqF, htF, -, -, -, hcoF, hkF⟩ := osFolds_complete (σ := σ) (rd := rd) (fch := osFch)
    (kret := kret) hcf (cfg.lv lvl).folds (cfg.lv lvl).foldsOff s cv p w [] osp roots (H.w1, H.chs) _ hat
    (by omega) hq hrunF hvf (fun j hj => by
      rw [hok.chs.1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      exact hfch j hj)
  simp only at hatF hqF htF hcoF hkF
  rw [hcb, ← hVf] at hkF
  rw [ite_neg' (by omega)] at hcoF htF
  set sF := (osLvF cfg lvl s).2 with hsF
  have hsF' : (osFolds osFch (cfg.lv lvl).foldsOff (cfg.lv lvl).folds s).2 = sF := rfl
  rw [hsF'] at hatF hqF htF hcoF hkF
  have hcbF : σ (.n sF.cb) = cur * gen ^ osHP1 cfg lvl p := by
    rw [os_cb_of_at hatF (by omega), hcoF, Nat.sub_zero, osHP1]
  have hlen := hok.len
  have hP2 : osHP2 cfg lvl p + 3 ≤ xs.length := hlen
  have hvm : ∀ j < Vm.length, σ (.n (sF.k + j)) = Vm.getD j 0 := fun j hj => by
    rw [hkF, Nat.add_assoc, hv _ (by simp only [List.length_append]; omega), List.append_assoc, os_skip,
      oq_getD_app_lt hj]
  have hg0 : (cfg.lv lvl).grindBits ≠ 0 := by rw [hgr]; decide
  have hnonce : LoadHolds rd cur (osHP2 cfg lvl p) (osHNonce cfg lvl xs p) := hxs _ (by omega)
  have hsplit : (osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1 =
      (osLvF cfg lvl s).1 ++ ((osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) := by rw [List.append_assoc]
  by_cases hl : lvl = cfg.yrLevel
  · have hVm' : Vm = osFinalVals H.cv1 (osHMs cfg lvl xs p) (σ (.n sF.cb)) sF.co cfg.yrLen := by
      rw [hVm, ite_pos' hl, hcbF, hcoF]
    rw [hVm'] at hvm
    have hM := osFinal_complete (rd := rd) (name := cfg.finalMsg) (n := cfg.yrLen) (fmsg := osFmsg) (kret := kret)
      (ms := osHMs cfg lvl xs p) hatF (by rw [hcoF]; omega)
      (by have := hcm hl; simp only [osHCv2, osHP2, ite_pos' hl] at this; exact this) hvm
    have eM : osLvM cfg lvl s = osFinal cfg.finalMsg osFmsg sF := by rw [osLvM, ite_pos' hl]
    rw [← eM, ← hVm'] at hM
    obtain ⟨hMh, hatM, hcoM, -, hkM⟩ := hM
    have eP : H.cv1 = H.cv1 := rfl
    have hatM' : OsAt σ (osLvM cfg lvl s).2 (osHCv2 cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p) := by
      rw [osHCv2, ite_pos' hl, osHP2, ite_pos' hl, osHP1]; exact hatM
    have hvg : ∀ j < 16, σ (.n ((osLvM cfg lvl s).2.k + j)) =
        (osGrindVals (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2 cfg lvl xs p H.cv1)).getD j 0 :=
      fun j hj => by
        rw [hkM, hkF, show s.k + Vf.length + Vm.length + j = s.k + ((Vf ++ Vm).length + j) by simp; ring,
          hv _ (by simp only [List.length_append]; omega), os_skip]
    obtain ⟨hG, hatG, hcoG, -, hkG⟩ := osGrind_complete (kret := kret) hg0 hatM' hnonce hcg hvg
    refine ⟨?_, hatG, ?_, ?_, ?_, ?_⟩
    · rw [hsplit, holdsList_append]
      refine (holdsList_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hF, ?_⟩
      rw [holdsList_append]
      refine (holdsList_noRet _ (by rw [eM]; exact osFinal_noRet _ _ _) _ _).mpr ⟨hMh, hG⟩
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.co = _
      rw [hcoG, hcoM, ite_pos' hl]
    · have kG : (osLvG cfg lvl s).2.c = sF.c ∧ (osLvG cfg lvl s).2.b = sF.b ∧ (osLvG cfg lvl s).2.a = sF.a := by
        rw [osLvG, eM]; exact ⟨rfl, rfl, rfl⟩
      rw [hqF, kG.1, kG.2.1, kG.2.2]
    · have kG : (osLvG cfg lvl s).2.t = sF.t := by rw [osLvG, eM]; rfl
      rw [htF, kG]
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.k = _
      rw [hkG, hkM, hkF]; simp only [List.length_append, hlg]; ring
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hood1 := (hnext next rfl).1
    have hVm' : Vm = osCommitVals lvl (cfg.lv lvl).logCols (σ (.n osOodz)) H.cv1 (osHW cfg lvl xs p 0)
        (osHW cfg lvl xs p 1) (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) := by
      rw [hVm, ite_neg' hl, hoz]
    have hlm : Vm.length = 84 := by
      rw [hVm']; simp [osCommitVals, os_length_fsNextVals, os_length_oodSampleVals]
    rw [hlm] at hvm
    rw [hVm'] at hvm
    have hw : ∀ i < 5, LoadHolds rd cur (p + 2 * (cfg.lv lvl).folds + i) (osHW cfg lvl xs p i) := fun i hi => by
      have := hxs (osHP1 cfg lvl p + i) (by simp only [osHP2, ite_neg' hl] at hP2; omega)
      rwa [osHW, osHP1]
    obtain ⟨r0, r1⟩ := hrt2 hl
    obtain ⟨o1, o2, o3⟩ := hood hl
    have hM := osCommit_complete (rd := rd) (roots := osRoots) (oodz := osOodz) (ood := osOod) (lvl := lvl)
      (logCols := (cfg.lv lvl).logCols) (kret := kret) hatF (hw 0 (by omega)) (hw 1 (by omega))
      (by have := hw 2 (by omega); rwa [show p + 2 * (cfg.lv lvl).folds + 2 = p + 2 * (cfg.lv lvl).folds + 2 from rfl] at this)
      (hw 3 (by omega)) (hw 4 (by omega)) r0 r1 o1 o2 o3 (hca hl).1 (hca hl).2.1
      (by rw [hoz]; exact (hca hl).2.2) hvm
    have eM : osLvM cfg lvl s = osCommit lvl (cfg.lv lvl).logCols 1 osRoots osOodz osOod sF := by
      rw [osLvM, ite_neg' hl, hood1]
    rw [← eM] at hM
    obtain ⟨hMh, hatM, hcoM, -, hkM⟩ := hM
    have hatM' : OsAt σ (osLvM cfg lvl s).2 (osHCv2 cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p) := by
      rw [osHCv2, ite_neg' hl, osHP2, ite_neg' hl, osHP1, osHCv12]; exact hatM
    have hvg : ∀ j < 16, σ (.n ((osLvM cfg lvl s).2.k + j)) =
        (osGrindVals (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2 cfg lvl xs p H.cv1)).getD j 0 :=
      fun j hj => by
        rw [hkM, hkF, ← hlm, show s.k + Vf.length + Vm.length + j = s.k + ((Vf ++ Vm).length + j) by simp; ring,
          hv _ (by simp only [List.length_append]; omega), os_skip]
    obtain ⟨hG, hatG, hcoG, -, hkG⟩ := osGrind_complete (kret := kret) hg0 hatM' hnonce hcg hvg
    refine ⟨?_, hatG, ?_, ?_, ?_, ?_⟩
    · rw [hsplit, holdsList_append]
      refine (holdsList_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hF, ?_⟩
      rw [holdsList_append]
      refine (holdsList_noRet _ (by rw [eM]; exact osCommit_noRet _ _ _ _ _ _) _ _).mpr ⟨hMh, hG⟩
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.co = _
      rw [hcoG, hcoM, hcoF, ite_neg' hl]
    · have kG : (osLvG cfg lvl s).2.c = sF.c ∧ (osLvG cfg lvl s).2.b = sF.b ∧ (osLvG cfg lvl s).2.a = sF.a := by
        rw [osLvG, eM]; exact ⟨rfl, rfl, rfl⟩
      rw [hqF, kG.1, kG.2.1, kG.2.2]
    · have kG : (osLvG cfg lvl s).2.t = sF.t := by rw [osLvG, eM]; rfl
      rw [htF, kG]
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.k = _
      rw [hkG, hkM, hkF]; simp only [List.length_append, hlg, hlm]; ring

end
end LeanVM.Guest.B1
