/-
  LeanVM.Guest.B1.Whir.OsKidsLv

  Each level's callees of `open_stacked`, complete on its honest words: the level's call
  hypotheses `OsLvCallH` under the placed call relations.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsF

/-!
# A level's callees, placed (TRIAGE #36)

The callees `open_stacked` takes per configuration (`OsKidsAt`), the caller's words `osLk` (its
own words and buffers, the decoders' pointers left out), the level's decoders' pointers `osW` at
the loop's frame and the decoders' frame runs `osS`; the level's callees before its positions
complete on `osLk`, its loop at `p` on `osLk ++ osW p` returning `osS p`, those after on
`osLk ++ osW p ++ osS p`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

/-- A level's callees, placed. -/
structure OsLvKidsAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (cfg : OsCfg) (l : ℕ) : Prop where
  rw : OsRowWeightsAtD fs cert κ (cfg.lv l).rowWeights (cfg.lv l).folds (if l = 0 then 1 else 0)
  cap : VmcCompleteAt fs cert κ (cfg.lv l).capDepth (cfg.lv l).verifyCap
  queries : OqCompleteAt fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
    (cfg.lv l).capDepth (cfg.lv l).queriesFn
  decode : OsDecodeAtD fs cert κ (cfg.lv l).depth (cfg.lv l).decode
  sqPlace : SqPlace (cfg.lv l)
  sqFn : ∃ fn, coreProgram.find? (cfg.lv l).sqLoop = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧
    fn.body = sqLoopOf (cfg.lv l)
  sqLoop : coreProgram.loop (cfg.lv l).sqLoop = true
  resPure : coreProgram.PureIn [(cfg.lv l).resLoop]
  resFn : ∃ fn, coreProgram.find? (cfg.lv l).resLoop = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
    fn.body = resLoopOf cfg l (cfg.lv l)

/-- **`open_stacked`'s callees, placed**, at a configuration. -/
structure OsKidsAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (cfg : OsCfg) : Prop where
  fold : OsFoldAtD fs cert κ
  canonical : OsAssertCanonicalAtD fs cert κ
  ood : OsOodPointAtD fs cert κ
  grind : OsGrindAtD fs cert κ
  finalMsg : OsFinalMsgAtD fs cert κ cfg.finalMsg cfg.yrLen
  foldFinal : OsFoldFinalAtD fs cert κ cfg.foldFinal cfg.yrLog
  lv : ∀ l < cfg.levels.length, OsLvKidsAt fs cert κ cfg l

/-- The caller's words: its own and its buffers', the decoders' pointers left out. -/
def osLk (cfg : OsCfg) (d : OsData) (Lin : Main.Layout) (b : ℕ) : Main.Layout :=
  Lin ++ bufL b (osSizes cfg) (d.ownQ cfg [])

/-- Level `l`'s decoders' pointers, its loop entered at `p`. -/
def osW (fs : String → ℕ) (cert : String → V → ℕ) (cfg : OsCfg) (b l p : ℕ) : Main.Layout :=
  [((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff, OsData.qbpSeg cfg fs cert l p)]

/-- Level `l`'s decoders' frame runs, its loop entered at `p`. -/
def osS (fs : String → ℕ) (cert : String → V → ℕ) (cfg : OsCfg) (d : OsData) (l p : ℕ) : Main.Layout :=
  sqRuns fs cert (cfg.lv l) (cfg.lv l).squeezes p (sqW (d.cv3 cfg l)) 0

/-- The level's call relations: before the positions, the loop, after. -/
def osCA (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Main.Layout) : CallRel := osKC fs cert κ Lk

def osCsq (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Main.Layout) (W S : ℕ → Main.Layout) : CallRel :=
  fun f a r => OsCompleteAtP fs cert κ f (fun p => Lk ++ W p) a r S

def osCB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Main.Layout) (W S : ℕ → Main.Layout) : CallRel :=
  fun f a r => ∀ p, osKC fs cert κ (Lk ++ W p ++ S p) f a r

/-- **A window of a buffer of windows, at its pointer.** -/
theorem os_seg_readsAt {rd : Reader} {ptr : E} {size n : ℕ} {off : ℕ → ℕ} {c : ℕ → List E}
    (hr : ReadsAt rd ptr (osSegC size ((List.range n).map fun l => (off l, c l))))
    (hd : ∀ i j, i < j → j < n → off i + (c i).length ≤ off j) (hfit : ∀ l < n, off l + (c l).length ≤ size)
    {l : ℕ} (hl : l < n) : ReadsAt rd (ptr * gen ^ off l) (c l) := by
  intro k hk
  rw [loadHolds_mul_gen_pow]
  have := os_seg_at hr hd hfit hl k hk
  rwa [List.getD_eq_getElem _ _ hk] at this

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData}

theorem oodz_readsAt (hlay : OsLayoutOk cfg) {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.oodzC cfg)) {l : ℕ}
    (hl : l + 1 < cfg.levels.length) : ReadsAt rd (ptr * gen ^ ((l + 1) * 22)) (d.oodPt cfg l) := by
  have hlen : ∀ i, (d.oodPt cfg i).length = (cfg.lv i).logCols := fun i => length_sqAll _ _
  refine os_seg_readsAt (n := cfg.levels.length - 1) (off := fun l => (l + 1) * 22) (c := fun l => d.oodPt cfg l) hr
    (fun i j hij hj => ?_) (fun i hi => ?_) (by omega)
  · rw [hlen]; have := hlay.cols i (by omega)
    have : (i + 1) * 22 + 22 ≤ (j + 1) * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hlen]; have := hlay.cols i (by omega)
    have : (i + 1) * 22 + 22 ≤ cfg.levels.length * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- **A level's callees before its positions.** -/
theorem lvCallA {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAt fs cert κ cfg) {Lin : Main.Layout} {b : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b [])
    {Q : List (ℕ × List (ℕ × Opening))} {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFacts cfg μ d.xs Lall Q (d.lv cfg l)) (hlv : (d.lv cfg l).lvl = l) :
    (∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ d.xs.length →
      osCA fs cert κ (osLk cfg d Lin b) "opening_fold" [(digestScalars cv').1, (digestScalars cv').2,
        cur * gen ^ p', q'.getD 0 0, q'.getD 1 0, q'.getD 2 0] (osFoldRets d.xs cv' p' q' (cur * gen ^ p'))) ∧
    (l = cfg.yrLevel → osCA fs cert κ (osLk cfg d Lin b) cfg.finalMsg
      [(digestScalars (d.lv cfg l).H.cv1).1, (digestScalars (d.lv cfg l).H.cv1).2,
        cur * gen ^ osHP1 cfg l (d.lv cfg l).p, (osPtrsOf cfg b).fmsg]
      [(digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
        (digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2,
        cur * gen ^ osHP2 cfg l (d.lv cfg l).p]) ∧
    (l ≠ cfg.yrLevel → osCA fs cert κ (osLk cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lv cfg l).p 0] [0] ∧
      osCA fs cert κ (osLk cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lv cfg l).p 1] [0] ∧
      osCA fs cert κ (osLk cfg d Lin b) "opening_ood_point"
        [(digestScalars (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
          (digestScalars (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2,
          (osPtrsOf cfg b).oodz * osGw ((l + 1 + 0) * 22), osGw (cfg.lv l).logCols]
        [(digestScalars (sqAll (cfg.lv l).logCols (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2).1,
          (digestScalars (sqAll (cfg.lv l).logCols (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2).2]) ∧
    osCA fs cert κ (osLk cfg d Lin b) "grind_check"
      [(digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
        (digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2, osHNonce cfg l d.xs (d.lv cfg l).p,
        osGw (cfg.lv l).grindBits] [] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, hml0, hml1, hlc, -, hgr, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -, -, -⟩ := hspec
  have hokL := hF.ok
  rw [hlv] at hokL
  have hLinN : ∀ rd, MemL rd (osLk cfg d Lin b) → ReadsAt rd cur d.xs := fun rd hm =>
    os_reads_noLow hLin (Main.memL_append.mp hm).1
  refine ⟨fun cv' p' q' hq hp => os_kid_fold hk.fold (fun rd hlw hm => hLin rd hlw (Main.memL_append.mp hm).1)
    cv' p' q' hq hp, fun hy => ?_, fun hy => ⟨?_, ?_, ?_⟩, ?_⟩
  · have hlen := hokL.len
    unfold osHPEnd osHP2 at hlen
    rw [ite_pos' hy] at hlen
    have h := os_kid_final (fs := fs) (cert := cert) (κ := κ) hk.finalMsg (Lk := osLk cfg d Lin b) (xs := d.xs)
      (cur := cur) (out := (osPtrsOf cfg b).fmsg) (P1 := osHP1 cfg l (d.lv cfg l).p) (by omega) (fun rd hm => by
        refine ⟨hLinN rd hm, ?_⟩
        have := (hbuf rd hm).fmsg
        rw [fmsgC, ← hy] at this
        exact this) (d.lv cfg l).H.cv1
    unfold osHCv2 osHP2
    rw [ite_pos' hy, ite_pos' hy]
    exact h
  · exact os_kid_canonical hk.canonical _ (os_canonical_of_digest (hokL.root hy)).1
  · exact os_kid_canonical hk.canonical _ (os_canonical_of_digest (hokL.root hy)).2
  · have hl1 : l + 1 < cfg.levels.length := by have := hok.yrLevel; omega
    rw [Nat.add_zero, os_gw_eq (by omega), os_gw_eq (by omega)]
    exact os_kid_ood hk.ood (by omega) (by simp only [ordG]; omega) fun rd _ hm =>
      oodz_readsAt hlay (hbuf rd hm).oodz hl1
  · rw [hgr, os_gw_eq (by decide)]
    exact os_kid_grind hk.grind _ _ _ (by decide) hokL.pow

end OsData

end
end LeanVM.Guest.B1
