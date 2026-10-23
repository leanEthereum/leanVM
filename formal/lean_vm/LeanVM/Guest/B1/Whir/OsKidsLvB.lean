/-
  LeanVM.Guest.B1.Whir.OsKidsLvB

  `open_stacked`'s callees at each level, placed at their honest words, by bounded trees.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsLv
public import LeanVM.Guest.B1.Whir.OsKidsAB

/-!
# Each level's callees by bounded trees (TRIAGE #36)

`OsKidsLv`'s `lvCallA` … `lvsCallH` under `OsKidsAtB`, each callee's tree at most `bd f` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData} {bd : String → ℕ}

/-- **A level's callees before its positions, bounded.** -/
theorem lvCallAB {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b [])
    {Q : List (ℕ × List (ℕ × Opening))} {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFacts cfg μ d.xs Lall Q (d.lv cfg l)) (hlv : (d.lv cfg l).lvl = l) :
    (∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ d.xs.length →
      osKCB fs cert κ bd (osLk cfg d Lin b) "opening_fold" [(digestScalars cv').1, (digestScalars cv').2,
        cur * gen ^ p', q'.getD 0 0, q'.getD 1 0, q'.getD 2 0] (osFoldRets d.xs cv' p' q' (cur * gen ^ p'))) ∧
    (l = cfg.yrLevel → osKCB fs cert κ bd (osLk cfg d Lin b) cfg.finalMsg
      [(digestScalars (d.lv cfg l).H.cv1).1, (digestScalars (d.lv cfg l).H.cv1).2,
        cur * gen ^ osHP1 cfg l (d.lv cfg l).p, (osPtrsOf cfg b).fmsg]
      [(digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
        (digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2,
        cur * gen ^ osHP2 cfg l (d.lv cfg l).p]) ∧
    (l ≠ cfg.yrLevel → osKCB fs cert κ bd (osLk cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lv cfg l).p 0] [0] ∧
      osKCB fs cert κ bd (osLk cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lv cfg l).p 1] [0] ∧
      osKCB fs cert κ bd (osLk cfg d Lin b) "opening_ood_point"
        [(digestScalars (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
          (digestScalars (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2,
          (osPtrsOf cfg b).oodz * osGw ((l + 1 + 0) * 22), osGw (cfg.lv l).logCols]
        [(digestScalars (sqAll (cfg.lv l).logCols (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2).1,
          (digestScalars (sqAll (cfg.lv l).logCols (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2).2]) ∧
    osKCB fs cert κ bd (osLk cfg d Lin b) "grind_check"
      [(digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1,
        (digestScalars (osHCv2 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).2, osHNonce cfg l d.xs (d.lv cfg l).p,
        osGw (cfg.lv l).grindBits] [] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, hml0, hml1, hlc, -, hgr, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -, -, -⟩ := hspec
  have hokL := hF.ok
  rw [hlv] at hokL
  have hLinN : ∀ rd, MemL rd (osLk cfg d Lin b) → ReadsAt rd cur d.xs := fun rd hm =>
    os_reads_noLow hLin (Main.memL_append.mp hm).1
  refine ⟨fun cv' p' q' hq hp => os_kid_foldB hk.fold (fun rd hlw hm => hLin rd hlw (Main.memL_append.mp hm).1)
    cv' p' q' hq hp, fun hy => ?_, fun hy => ⟨?_, ?_, ?_⟩, ?_⟩
  · have hlen := hokL.len
    unfold osHPEnd osHP2 at hlen
    rw [ite_pos' hy] at hlen
    have h := os_kid_finalB (fs := fs) (cert := cert) (κ := κ) hk.finalMsg (Lk := osLk cfg d Lin b) (xs := d.xs)
      (cur := cur) (out := (osPtrsOf cfg b).fmsg) (P1 := osHP1 cfg l (d.lv cfg l).p) (by omega) (fun rd hm => by
        refine ⟨hLinN rd hm, ?_⟩
        have := (hbuf rd hm).fmsg
        rw [fmsgC, ← hy] at this
        exact this) (d.lv cfg l).H.cv1
    unfold osHCv2 osHP2
    rw [ite_pos' hy, ite_pos' hy]
    exact h
  · exact os_kid_canonicalB hk.canonical _ (os_canonical_of_digest (hokL.root hy)).1
  · exact os_kid_canonicalB hk.canonical _ (os_canonical_of_digest (hokL.root hy)).2
  · have hl1 : l + 1 < cfg.levels.length := by have := hok.yrLevel; omega
    rw [Nat.add_zero, os_gw_eq (by omega), os_gw_eq (by omega)]
    exact os_kid_oodB hk.ood (by omega) (hlay.cols l hl) (by simp only [ordG]; omega) fun rd _ hm =>
      oodz_readsAt hlay (hbuf rd hm).oodz hl1
  · rw [hgr, os_gw_eq (by decide)]
    exact os_kid_grindB hk.grind _ _ _ hokL.pow

/-- **A level's query-position loop, placed, bounded.** -/
theorem lvCallSqB {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b []) {l : ℕ} (hl : l < cfg.levels.length) :
    1 + osGw (cfg.lv l).squeezes ≠ 0 →
    osCsqB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l) (cfg.lv l).sqLoop
      [1, osGw (cfg.lv l).squeezes, osPtrAt cfg b (11 + 2 * l), (osPtrsOf cfg b).qpos, (osPtrsOf cfg b).qbp] [] := by
  intro _
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, hper, hqs, -, -, hsq62, hdig, -, -, -, -, -, hpo, -, -, -, -, -⟩ := hspec
  have hq0 := hlay.queries l hl
  have hn : 0 < (cfg.lv l).squeezes := by
    rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
    · rw [h, Nat.zero_mul] at hqs; omega
    · exact h
  obtain ⟨fn, hfind, hp, hb⟩ := (hk.lv l hl).sqFn
  rw [os_gw_eq (by omega)]
  refine os_kid_sqB (hk.lv l hl).sqPlace hfind hp hb (hk.lv l hl).sqLoop hpo hdig (hk.lv l hl).decode hn
    (by simp only [ordG]; omega) (cv := d.cv3 cfg l) (fun rd _ hm j hj => ?_) (fun p rd _ hm j hj i hi => ?_)
    (fun j hj t ht => ?_) (hk.lv l hl).sqLe
  · have h1 := sqz_at ((hbuf rd hm).sqz l hl) (j := j) (by omega)
    have h2 := sqz_at ((hbuf rd hm).sqz l hl) (j := j + 1) (by omega)
    rw [sqAll_succ_snd] at h2
    exact ⟨h1.1, h1.2, by simpa [Nat.mul_add] using h2.1, by simpa [Nat.mul_add, Nat.add_assoc] using h2.2⟩
  · obtain ⟨hm1, hm2⟩ := Main.memL_append.mp hm
    have hqp := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
      (c := fun l => (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
        eOfNat (osPosOf (cfg.lv l).depth (d.cv3 cfg l) i)) (hbuf rd hm1).qpos
      (fun a c hac hc => by simp only [List.length_map, List.length_range]; exact hlay.pos a c hac hc)
      (fun a ha => by simp only [List.length_map, List.length_range]; exact hlay.posFit a ha) hl
    have hidx : j * (192 / (cfg.lv l).depth) + i < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) := by
      have : (j + 1) * (192 / (cfg.lv l).depth) ≤ (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) :=
        Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega
    have hw := hm2 _ (List.mem_singleton.mpr rfl)
    refine ⟨?_, ?_⟩
    · have := hqp (j * (192 / (cfg.lv l).depth) + i) (by simpa using hidx)
      rw [loadHolds_mul_gen_pow] at this ⊢
      simp only [List.getElem_map, List.getElem_range] at this
      rw [osPosOf_split hper _ hi] at this
      rw [Nat.add_assoc]; exact this
    · have e1 : (osPtrsOf cfg b).qbp * gen ^ ((cfg.lv l).posOff + j * (192 / (cfg.lv l).depth)) =
          ofK (Parameters.gpow ((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff)) *
            gen ^ (j * (192 / (cfg.lv l).depth)) := by
        show osPtrAt cfg b 8 * _ = _
        unfold osPtrAt; rw [ofK_gpow_mul, ofK_gpow_mul, Nat.add_assoc]
      rw [e1, loadHolds_mul_gen_pow]
      have := hw (j * (192 / (cfg.lv l).depth) + i) (by simpa [qbpSeg] using hidx)
      simp only [qbpSeg, List.getElem_map, List.getElem_range] at this
      rw [show (j * (192 / (cfg.lv l).depth) + i) / (192 / (cfg.lv l).depth) = j by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hper, Nat.div_eq_of_lt hi, Nat.zero_add],
        show (j * (192 / (cfg.lv l).depth) + i) % (192 / (cfg.lv l).depth) = i by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]] at this
      exact this
  · refine ⟨(bases b (osSizes cfg)).getD (11 + 2 * l) 0 + (2 * j + t), ?_, _,
      List.mem_append_right _ (os_bufL_mem (ownQ_length []) (j := 11 + 2 * l)
        (by rw [os_length_osSizes]; omega)), ?_, ?_⟩
    · unfold osPtrAt; rw [Main.addr_ofK]
    · simp
    · rw [os_ownQ_getD_sqz hl]
      simp only [sqzC, List.length_flatMap, List.length_cons, List.length_nil, List.map_const', List.length_range,
        List.sum_replicate, smul_eq_mul]
      omega

/-- **A level's row weights, placed, bounded.** -/
theorem lvCallRwB (hlay : OsLayoutOk cfg) (hrun : RunOk cfg d) (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b []) {l : ℕ} (hl : l < cfg.levels.length) :
    osCBB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l) (cfg.lv l).rowWeights
      [(osPtrsOf cfg b).fch * gen ^ (cfg.lv l).foldsOff, osPtrAt cfg b (11 + 2 * l + 1)] [] := fun _ =>
  os_kid_rwB (hk.lv l hl).rw (hrun.chs l hl) fun rd hm =>
    ⟨fch_readsAt hlay hrun (hbuf rd (memL_lk hm)).fch hl, (hbuf rd (memL_lk hm)).rew l hl⟩

/-- **A level's cap, placed, bounded.** -/
theorem lvCallCapB {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgrees x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFacts cfg μ d.xs Lall Q (d.lv cfg l)) (hlv : (d.lv cfg l).lvl = l) :
    osCBB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l) (cfg.lv l).verifyCap
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff]
      [(digestScalars (d.rt cfg l)).1, (digestScalars (d.rt cfg l)).2] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcd1, hcd2, -, -, -, -, -, -, -, -, -⟩ := hspec
  have hst := hF.step
  rw [hlv] at hst
  have hcap := os_capOk_of (lv_open hF hlv) (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  intro p
  refine os_kid_capB (hk.lv l hl).cap hcap fun rd hm => ⟨?_, ?_⟩
  · exact os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
      (c := fun l => osCapCells (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)) (hbuf rd (memL_lk hm)).caps
      (fun a c hac hc => by rw [os_capCells_length]; exact hlay.caps a c hac hc)
      (fun a ha => by rw [os_capCells_length]; exact hlay.capsFit a ha) hl
  · exact os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
      (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)) (hbuf rd (memL_lk hm)).flags
      (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
      (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl

/-- **A level's queries, placed, bounded.** -/
theorem lvCallQB {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hrun : RunOk cfg d) (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgrees x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFacts cfg μ d.xs Lall Q (d.lv cfg l)) (hlv : (d.lv cfg l).lvl = l) :
    osCBB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l) (cfg.lv l).queriesFn
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff,
        (osPtrsOf cfg b).qw * gen ^ (l * cfg.maxQ), (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff,
        osPtrAt cfg b (11 + 2 * l + 1), osGw (cfg.lv l).queries]
      [osHEnf cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, hper, hqs, -, -, -, -, hcd1, hcd2, -, -, -, -, hq62, -, -, -, -⟩ := hspec
  set L := d.lv cfg l with hL
  set rev : ℕ := if l = 0 then 1 else 0
  have hst := hF.step
  rw [hlv] at hst
  have hoa := lv_open hF hlv
  have hcap := os_capOk_of hoa (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  obtain ⟨os1, hosp, hl1, hrows, hj⟩ := os_openAll_inv _ _ _ _ hoa
  have hqsl : (osHQs cfg l d.xs L.p L.H.cv1).length = (cfg.lv l).queries := by simp [osHQs]
  rw [hqsl] at hl1
  set leaf : ℕ → List K := fun j => (os1.getD j ⟨[], []⟩).leaf
  set wts : ℕ → E := fun jw => (eqKernel L.H.chs).getD (orwSlot (cfg.lv l).folds rev jw) 0
  set qwV : ℕ → E := fun j => d.lam cfg l ^ j
  have hE : osHEnf cfg l d.xs L.p L.H = oqSum rev (2 ^ (cfg.lv l).folds) wts qwV leaf (cfg.lv l).queries := by
    have h := os_oqSum_eq (l := l) (hrun.chs l hl) (d.lam cfg l) (os1 := os1) (fun j hj' => by
      rw [(hj j hj').1])
    rw [hl1] at h
    rw [h]
    unfold osHEnf
    rw [hqsl, hrows]
    rfl
  intro p
  rw [hE, os_gw_eq (by omega)]
  have hmemq : ∀ j < (cfg.lv l).queries, ((osHQs cfg l d.xs L.p L.H.cv1).getD j 0, os1.getD j ⟨[], []⟩) ∈
      (osHQs cfg l d.xs L.p L.H.cv1).zip L.osp := by
    intro j hj'
    rw [hosp]
    refine List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip, List.length_append, hqsl]; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  obtain ⟨Bq, hqB, hqle⟩ := (hk.lv l hl).queries
  refine CompleteAtB.mono (os_kid_queriesB hqB (n := (cfg.lv l).queries) (by simp only [ordG]; omega) (leaf := leaf)
    (pos := fun j => (osHQs cfg l d.xs L.p L.H.cv1).getD j 0)
    (sibs := fun j => (os1.getD j ⟨[], []⟩).path.take ((cfg.lv l).depth - (cfg.lv l).capDepth)) (wts := wts) (qwV := qwV)
    (dbpV := fun j => (qbpSeg cfg fs cert l p).getD j 0)
    (fun j hj' => by simp only [leaf]; rw [List.getD_eq_getElem _ _ (by omega)]; exact (hj j (by omega)).1)
    (fun j hj' => (hcap.pos _ (hmemq j hj')))
    (fun j hj' => by
      simp only [List.length_take]
      rw [List.getD_eq_getElem _ _ (by omega), (hj j (by omega)).2.1]; omega)
    (fun rd _ hm => ?_)) le_rfl hqle
  obtain ⟨hm12, hmS⟩ := Main.memL_append.mp hm
  obtain ⟨hmk, hmW⟩ := Main.memL_append.mp hm12
  have hb := hbuf rd hmk
  have hcells := os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
    (c := fun l => osCapCells (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)) hb.caps
    (fun a c hac hc => by rw [os_capCells_length]; exact hlay.caps a c hac hc)
    (fun a ha => by rw [os_capCells_length]; exact hlay.capsFit a ha) hl
  have hflags := os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
    (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)) hb.flags
    (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
    (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl
  have hW := hmW _ (List.mem_singleton.mpr rfl)
  refine ⟨fun jw hjw => ?_, fun j hj' => ?_, fun j hj' => ?_, fun j hj' l' hl' => ?_, fun j hj' => ?_,
    fun j hj' => ?_⟩
  · have := os_readsAt_getD (hb.rew l hl) (k := jw) (by simpa [rewC] using hjw)
    rw [rewC, os_getD_map_range _ hjw] at this
    exact this
  · rw [loadHolds_mul_gen_pow]; exact qw_at hlay hb.qw hl j hj'
  · have e1 : (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff =
        ofK (Parameters.gpow ((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff)) := by
      show osPtrAt cfg b 8 * _ = _
      unfold osPtrAt; rw [ofK_gpow_mul]
    rw [e1]
    have hsq1 : 1 ≤ (cfg.lv l).squeezes := by
      rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
      · rw [h, Nat.zero_mul] at hqs; omega
      · exact h
    have := Nat.mul_le_mul_right (192 / (cfg.lv l).depth) hsq1
    exact os_readsAt_getD hW (by simp only [qbpSeg, List.length_map, List.length_range]; omega)
  · have hjs : j < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) := by omega
    have hdiv : j / (192 / (cfg.lv l).depth) < (cfg.lv l).squeezes := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hjs)
    have hmod : j % (192 / (cfg.lv l).depth) < (192 / (cfg.lv l).depth) := Nat.mod_lt _ hper
    have hpd : (192 / (cfg.lv l).depth) * (cfg.lv l).depth ≤ 192 := Nat.div_mul_le_self 192 (cfg.lv l).depth
    have hl'd : l' < (cfg.lv l).depth := by omega
    have hc : j % (192 / (cfg.lv l).depth) * (cfg.lv l).depth + l' < 192 := by
      have : (j % (192 / (cfg.lv l).depth) + 1) * (cfg.lv l).depth ≤ (192 / (cfg.lv l).depth) * (cfg.lv l).depth := Nat.mul_le_mul_right _ hmod
      rw [Nat.succ_mul] at this; omega
    simp only
    rw [List.getD_eq_getElem _ _ (by simp [qbpSeg]; exact hjs)]
    simp only [qbpSeg, List.getElem_map, List.getElem_range]
    rw [loadHolds_mul_gen_pow]
    have hpos : (osHQs cfg l d.xs L.p L.H.cv1).getD j 0 = osPosOf (cfg.lv l).depth (d.cv3 cfg l) j := by
      unfold osHQs; rw [os_getD_map_range _ hj']; rfl
    rw [hpos, osPosOf_testBit _ _ hl'd]
    exact sqRuns_bit hmS hdiv hc
  · have := osCap_parent hcap hflags (hmemq j hj')
    exact this
  · have := osCap_leaf hcap hcells (hmemq j hj')
    exact this

/-- **Every level's callees, placed, bounded.** -/
theorem lvsCallHB {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hrun : RunOk cfg d) (hk : OsKidsAtB fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLk cfg d Lin b) → OsBufReads rd cfg d b []) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hQ : ∀ x ∈ Q, BatchAgrees x.1 x.2)
    (hch : OsChain cfg μ (cfg.lv 0).folds d.xs Lall e sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    OsLvsCallH (fun _ => osKCB fs cert κ bd (osLk cfg d Lin b))
      (fun l => osCBB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l))
      (fun l => osCsqB fs cert κ bd (osLk cfg d Lin b) (osW fs cert cfg b l) (osS fs cert cfg d l)) cfg d.xs cur
      (osPtrsOf cfg b) (fun l => osPtrAt cfg b (11 + 2 * l)) (fun l => osPtrAt cfg b (11 + 2 * l + 1)) 0 2
      (osW0 d.target d.xs) (d.roots0 cfg) d.Hs := by
  refine os_lvsCallH_mem d.Hs 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) fun L hL => ?_
  obtain ⟨hg, hlt⟩ := os_lvs_get cfg d.xs d.Hs _ _ _ _ _ L hL
  have hl : L.lvl < cfg.levels.length := by rw [os_lvsList_length, hrun.len] at hlt; exact hlt
  have hF := os_chain_mem d.Hs 0 _ _ _ _ _ hch L hL
  have e : d.lv cfg L.lvl = L := hg
  have hF' : OsLvFacts cfg μ d.xs Lall Q (d.lv cfg L.lvl) := by rw [e]; exact hF
  have hlv : (d.lv cfg L.lvl).lvl = L.lvl := by rw [e]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := lvCallAB (fs := fs) (cert := cert) (κ := κ) hok hlay hk hLin hbuf hl hF' hlv
  have hSq := lvCallSqB (fs := fs) (cert := cert) (κ := κ) (d := d) hok hlay hk hbuf hl
  have hRw := lvCallRwB (fs := fs) (cert := cert) (κ := κ) hlay hrun hk hbuf hl
  have hCap := lvCallCapB (fs := fs) (cert := cert) (κ := κ) hok hlay hk hbuf hQ hl hF' hlv
  have hQr := lvCallQB (fs := fs) (cert := cert) (κ := κ) hok hlay hrun hk hbuf hQ hl hF' hlv
  have ert : d.rt cfg L.lvl = (L.roots.getD L.lvl default).1 := by unfold rt; rw [e]
  rw [e] at hA2 hA3 hA4 hQr
  rw [ert] at hCap
  exact ⟨hA1, hA2, hA3, hA4, hSq, hRw, hCap, hQr⟩

end OsData

end
end LeanVM.Guest.B1
