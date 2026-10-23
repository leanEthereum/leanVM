/-
  LeanVM.Guest.B1.Whir.OsKidsAB

  `open_stacked`'s callees complete on the caller's words, by bounded trees.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsF
public import LeanVM.Guest.B1.Whir.OsKidsBd
public import LeanVM.Guest.Memory.Size

/-!
# The callees by bounded trees (TRIAGE #36)

`OsKidsA`, `OsKidsB` and `OsKidsF` with each callee's tree at most `bd f` words, `bd` a bound by
name (`osKCB`). `OsKidsAtB`: the callees' bounded forms at a configuration, group 1's at the
argument shapes `open_stacked` calls them with (`opening_ood_point` at `g^m`, `m ≤ 22`;
`grind_check` at `g^17`), the pure ones' (`verify_merkle_cap`, the residual loops) by their trees'
sizes (`completeAt_of_rel_pureBat`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- A callee complete on the words `Lk` by a tree of at most `bd f` words. -/
def osKCB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (bd : String → ℕ) (Lk : Main.Layout) : CallRel :=
  fun f a r => CompleteAtB fs cert κ f Lk a (Returns r) (bd f)

/-- `osCsq` by bounded trees. -/
def osCsqB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (bd : String → ℕ) (Lk : Main.Layout)
    (W S : ℕ → Main.Layout) : CallRel :=
  fun f a r => OsCompleteAtPB fs cert κ f (fun p => Lk ++ W p) a r S (bd f)

/-- `osCB` by bounded trees. -/
def osCBB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (bd : String → ℕ) (Lk : Main.Layout)
    (W S : ℕ → Main.Layout) : CallRel :=
  fun f a r => ∀ p, osKCB fs cert κ bd (Lk ++ W p ++ S p) f a r

/-- `opening_ood_point` by trees of at most `B` words, at the counts `open_stacked` samples. -/
def OsOodAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (B : ℕ) : Prop :=
  ∀ m, m ≤ 22 → ∀ (args rets : List E) (Lin : Main.Layout), args.getD 3 0 = gen ^ m →
    (∀ rd, LowDef k rd → MemL rd Lin → OodPointPre rd args rets) →
    CompleteAtB fs cert k "opening_ood_point" Lin args (Returns rets) B

/-- `grind_check` by trees of at most `B` words, at the bits `open_stacked` checks. -/
def OsGrindAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (B : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), args.getD 3 0 = gen ^ Whir.queryGrindingBits →
    (∀ rd, LowDef k rd → MemL rd Lin → GrindPre rd args rets) →
    CompleteAtB fs cert k "grind_check" Lin args (Returns rets) B

/-- **A level's callees, placed, by trees of at most `bd f` words.** -/
structure OsLvKidsAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (cfg : OsCfg) (bd : String → ℕ) (l : ℕ) :
    Prop where
  rw : OsRowWeightsAtB fs cert κ (cfg.lv l).rowWeights (cfg.lv l).folds (if l = 0 then 1 else 0)
    fun _ => bd (cfg.lv l).rowWeights
  cap : VmcCompleteAtB fs cert κ (cfg.lv l).capDepth (cfg.lv l).verifyCap (bd (cfg.lv l).verifyCap)
  queries : ∃ B, OqCompleteAtB fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
    (cfg.lv l).capDepth (cfg.lv l).queriesFn B ∧ B (cfg.lv l).queries ≤ bd (cfg.lv l).queriesFn
  decode : OsDecodeAtD fs cert κ (cfg.lv l).depth (cfg.lv l).decode
  sqPlace : SqPlace (cfg.lv l)
  sqFn : ∃ fn, coreProgram.find? (cfg.lv l).sqLoop = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧
    fn.body = sqLoopOf (cfg.lv l)
  sqLoop : coreProgram.loop (cfg.lv l).sqLoop = true
  sqLe : sqTot fs (cfg.lv l) (cfg.lv l).squeezes 0 ≤ bd (cfg.lv l).sqLoop
  resPure : coreProgram.PureIn [(cfg.lv l).resLoop]
  resFn : ∃ fn, coreProgram.find? (cfg.lv l).resLoop = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
    fn.body = resLoopOf cfg l (cfg.lv l)
  resTot : ∀ rd (t : Tree) (args rets : List E), t.name = (cfg.lv l).resLoop →
    args.take 2 = [1, gen ^ (cfg.lv l).queries] → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ bd (cfg.lv l).resLoop

/-- **`open_stacked`'s callees, placed, by trees of at most `bd f` words**, at a configuration. -/
structure OsKidsAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (cfg : OsCfg) (bd : String → ℕ) : Prop where
  fold : CompleteRelB fs cert κ "opening_fold" MeaningOpeningFold (bd "opening_fold")
  canonical : CompleteRelB fs cert κ "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets)
    (bd "assert_canonical")
  ood : OsOodAtB fs cert κ (bd "opening_ood_point")
  grind : OsGrindAtB fs cert κ (bd "grind_check")
  finalMsg : OsFinalMsgAtB fs cert κ cfg.finalMsg cfg.yrLen fun _ => bd cfg.finalMsg
  foldFinal : OsFoldFinalAtB fs cert κ cfg.foldFinal cfg.yrLog fun _ => bd cfg.foldFinal
  lv : ∀ l < cfg.levels.length, OsLvKidsAtB fs cert κ cfg bd l

variable {bd : String → ℕ}

/-- **`opening_fold`** at the cursor's words, bounded. -/
theorem os_kid_foldB (hf : CompleteRelB fs cert κ "opening_fold" MeaningOpeningFold (bd "opening_fold"))
    {Lk : Main.Layout} {xs : List E} {cur : E}
    (hM : ∀ rd, LowDef κ rd → MemL rd Lk → ReadsAt rd cur xs) (cv' : Digest) (p' : ℕ) (q' : List E)
    (hq : q'.length = 3) (hp : p' + 2 ≤ xs.length) :
    osKCB fs cert κ bd Lk "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0,
      q'.getD 1 0, q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p')) := by
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, q' = [c0, c1, c2] := by
    match q', hq with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  refine hf _ _ Lk fun rd hl hm => ?_
  have hr := os_readsAt_shift (hM rd hl hm) (p := p') (n := 2) hp
  have e : (xs.drop p').take 2 = [xs.getD p' 0, xs.getD (p' + 1) 0] := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p' < xs.length by omega),
      List.getElem?_eq_getElem (show p' + 1 < xs.length by omega)]
  rw [e] at hr
  exact ⟨cv', _, _, _, _, _, _, rfl, hr, runsTo_foldStep cv' c0 c1 c2 (xs.getD p' 0) (xs.getD (p' + 1) 0), rfl⟩

/-- **The final message**, bounded. -/
theorem os_kid_finalB {name : String} {n : ℕ} (hfm : OsFinalMsgAtB fs cert κ name n fun _ => bd name)
    {Lk : Main.Layout} {xs : List E} {cur out : E} {P1 : ℕ} (hn : P1 + n ≤ xs.length)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd cur xs ∧ ReadsAt rd out ((xs.drop P1).take n))
    (cv1 : Digest) :
    osKCB fs cert κ bd Lk name [(digestScalars cv1).1, (digestScalars cv1).2, cur * gen ^ P1, out]
      [(digestScalars (obsAll cv1 ((xs.drop P1).take n))).1, (digestScalars (obsAll cv1 ((xs.drop P1).take n))).2,
        cur * gen ^ (P1 + n)] := by
  have hl : ((xs.drop P1).take n).length = n := by simp; omega
  refine hfm _ _ Lk fun rd hm => ?_
  obtain ⟨hx, ho⟩ := hM rd hm
  refine ⟨cv1, _, obsAll cv1 ((xs.drop P1).take n), rfl, hl, os_readsAt_shift hx hn, ho, ?_, ?_⟩
  · have := runsTo_readN cv1 ((xs.drop P1).take n)
    rwa [hl] at this
  · rw [mul_assoc, ← pow_add]

/-- **`assert_canonical`** on a canonical word, bounded. -/
theorem os_kid_canonicalB (hc : CompleteRelB fs cert κ "assert_canonical"
      (fun _ args rets => MeaningAssertCanonical args rets) (bd "assert_canonical"))
    (Lk : Main.Layout) {w : E} (hw : IsCanonical128 w) : osKCB fs cert κ bd Lk "assert_canonical" [w] [0] :=
  hc _ _ Lk fun _ _ _ => ⟨hw, rfl⟩

/-- **`opening_ood_point`**, bounded. -/
theorem os_kid_oodB (ho : OsOodAtB fs cert κ (bd "opening_ood_point")) {Lk : Main.Layout} {cv : Digest} {point : E}
    {m : ℕ} (hm0 : 0 < m) (hm22 : m ≤ 22) (hm : 2 * m + 2 < ordG)
    (hM : ∀ rd, LowDef κ rd → MemL rd Lk → ReadsAt rd point (sqAll m cv).1) :
    osKCB fs cert κ bd Lk "opening_ood_point" [(digestScalars cv).1, (digestScalars cv).2, point, gen ^ m]
      [(digestScalars (sqAll m cv).2).1, (digestScalars (sqAll m cv).2).2] :=
  ho m hm22 _ _ Lk rfl fun rd hl hmm => ⟨m, by omega, hm, rfl,
    Or.inr ⟨hm0, cv, _, _, rfl, runsTo_sampleN m cv, hM rd hl hmm, rfl⟩⟩

/-- **`grind_check`**, bounded. -/
theorem os_kid_grindB (hg : OsGrindAtB fs cert κ (bd "grind_check")) (Lk : Main.Layout) (cv : Digest) (nonce : E)
    (hp : powOk Whir.queryGrindingBits nonce (gcDigest cv nonce) = true) :
    osKCB fs cert κ bd Lk "grind_check" [(digestScalars cv).1, (digestScalars cv).2, nonce,
      gen ^ Whir.queryGrindingBits] [] :=
  hg _ _ Lk rfl fun _ _ _ => ⟨rfl, Whir.queryGrindingBits, by simp only [ordG, Whir.queryGrindingBits]; omega,
    by simp only [Whir.queryGrindingBits]; omega, rfl, cv, rfl, hp⟩

/-- **The row weights**, bounded. -/
theorem os_kid_rwB {name : String} {folds rev : ℕ} (hr : OsRowWeightsAtB fs cert κ name folds rev fun _ => bd name)
    {Lk : Main.Layout} {point out : E} {rs : List E} (hl : rs.length = folds)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd point rs ∧
      ReadsAt rd out ((List.range (2 ^ folds)).map fun i => (eqKernel rs).getD (orwSlot folds rev i) 0)) :
    osKCB fs cert κ bd Lk name [point, out] [] :=
  hr _ _ Lk fun rd hm => ⟨rfl, rs, hl, (hM rd hm).1, fun i hi => by
    have := os_readsAt_getD (hM rd hm).2 (k := i) (by simpa using hi)
    rwa [os_getD_map_range _ hi] at this⟩

/-- **The cap**, bounded. -/
theorem os_kid_capB {name : String} {cd depth : ℕ} (hv : VmcCompleteAtB fs cert κ cd name (bd name)) {Lk : Main.Layout}
    {rt : Digest} {qs : List (ℕ × Opening)} (hok : OsCapOk depth cd rt qs) {cap flags : E}
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd cap (osCapCells depth cd qs) ∧ ReadsAt rd flags (osCapFlags depth cd qs)) :
    osKCB fs cert κ bd Lk name [cap, flags] [(digestScalars rt).1, (digestScalars rt).2] :=
  hv Lk cap flags _ fun rd hm => osCap_meaning hok (hM rd hm).1 (hM rd hm).2

/-- `os_completeAt_of_nonempty` by bounded trees. -/
theorem os_completeAtB_of_nonempty {f : String} {Lin : Main.Layout} {args rets : List E} {B : ℕ}
    (h : ∀ rd0, LowDef κ rd0 → MemL rd0 Lin → CompleteAtB fs cert κ f Lin args (Returns rets) B) :
    CompleteAtB fs cert κ f Lin args (Returns rets) B := by
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  · obtain ⟨rd0, h1, h2⟩ := hex; exact h rd0 h1 h2
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **The queries**, bounded. -/
theorem os_kid_queriesB {base I depth cd : ℕ} {name : String} {B : ℕ → ℕ}
    (hq : OqCompleteAtB fs cert κ base I depth cd name B) {Lin : Main.Layout} {cap flags qw qbp rew : E} {n : ℕ}
    (hn : n + 1 < ordG) {leaf : ℕ → List K} {pos : ℕ → ℕ}
    {sibs : ℕ → List Digest} {wts qwV dbpV : ℕ → E} (hleaf : ∀ j < n, (leaf j).length = oqR base I)
    (hpos : ∀ j < n, pos j < 2 ^ depth) (hsl : ∀ j < n, (sibs j).length = depth - cd)
    (hlin : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqTopMem rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) :
    CompleteAtB fs cert κ name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n]) (B n) :=
  os_completeAtB_of_nonempty fun _ h1 h2 =>
    hq n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hpos hsl hlin (os_oqTopReg_of hlin h1 h2)

/-- **A level's query-position loop**, entered at `p`, by its frame runs' tree. -/
theorem os_kid_sqB {lv : OsLvl} (hpl : SqPlace lv) {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hdec : OsDecodeAtD fs cert κ lv.depth lv.decode) {n : ℕ} (hn : 0 < n) (hn' : n + 1 < ordG)
    {sqz qpos qbp : E} {cv : Digest} {Lk : Main.Layout} {W : ℕ → Main.Layout}
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lk → ∀ j < n,
      LoadHolds rd sqz (2 * j) (digestScalars (sqAll j cv).2).1 ∧
        LoadHolds rd sqz (2 * j + 1) (digestScalars (sqAll j cv).2).2 ∧
        LoadHolds rd sqz (2 * j + 2) (digestScalars (sqCv (sqAll j cv).2)).1 ∧
        LoadHolds rd sqz (2 * j + 3) (digestScalars (sqCv (sqAll j cv).2)).2)
    (hdmem : ∀ p rd, LowDef κ rd → MemL rd (Lk ++ W p) → ∀ j < n, ∀ i < 192 / lv.depth,
      LoadHolds rd (qpos * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (eOfNat ((eToNat (sqW cv j) >>> (i * lv.depth)) % 2 ^ lv.depth)) ∧
        LoadHolds rd (qbp * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (ofK (Parameters.gpow (sqDecAt fs lv n p j + cert lv.decode (.n 3))) * gen ^ (i * lv.depth)))
    (hreg : ∀ j < n, ∀ t < 4, OqIn (RegionL Lk) (sqz.limb 0 * Parameters.gpow (2 * j + t))) {B : ℕ}
    (hB : sqTot fs lv n 0 ≤ B) :
    OsCompleteAtPB fs cert κ lv.sqLoop (fun p => Lk ++ W p) [1, gen ^ n, sqz, qpos, qbp] []
      (fun p => sqRuns fs cert lv n p (sqW cv) 0) B := by
  intro p
  obtain ⟨Lown, hW, hD, hrel⟩ := sqLoop_relAtIn fs cert κ hpl hfind hp hb hlp hpo hdig hdec hn hn' (sqz := sqz)
    (qpos := qpos) (qbp := qbp) (cv := cv) (Lin := Lk ++ W p) p
    (fun rd hl hm => hmem rd hl (Main.memL_append.mp hm).1) (hdmem p)
    (fun j hj t ht => oq_in_mono (fun _ ⟨q, hq, h⟩ => ⟨q, List.mem_append_left _ hq, h⟩) (hreg j hj t ht))
  exact ⟨sqTot fs lv n 0, Lown, hW, hD, hB, hrel⟩

/-- **`fold_final_msg`**, bounded. -/
theorem os_kid_ffB {name : String} {n : ℕ} (hff : OsFoldFinalAtB fs cert κ name n fun _ => bd name)
    {Lk : Main.Layout} {msg point : E} {m ps : List E} (hm : m.length = 2 ^ n) (hps : ps.length = n)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd msg m ∧ ReadsAt rd point ps) :
    osKCB fs cert κ bd Lk name [msg, point] [multilinearEval m ps] :=
  hff _ _ Lk fun rd hmm => ⟨m, ps, hm, hps, (hM rd hmm).1, (hM rd hmm).2, rfl⟩

/-- **A residual chain loop**, bounded by its trees' size. -/
theorem os_kid_resB {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hS : coreProgram.PureIn [loop]) (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) (hb : fn.body = resLoopBody posOff row cols qo vals loop)
    (hc : 1 ≤ cols) {n : ℕ} (hn : n < ordG) (hn0 : 0 < n) {qpos ba bb rc qw : E} {ch0 r wq A B : ℕ → E}
    {Lk : Main.Layout}
    (hM : ∀ rd, MemL rd Lk → (∀ i < n, LoadHolds rd (qpos * gen ^ i) posOff (ch0 i)) ∧
      (∀ t < cols, LoadHolds rd ba (row + t) (A t)) ∧ (∀ t < cols, LoadHolds rd bb (row + t) (B t)) ∧
      (∀ i < n, LoadHolds rd (rc * gen ^ i) 0 (r i)) ∧ (∀ i < n, LoadHolds rd (qw * gen ^ i) qo (wq i)) ∧
      (∀ i < n, LoadHolds rd (rc * gen ^ i) 1 (r i + wq i * resProd A B vals (ch0 i) cols)))
    (hT : ∀ rd (t : Tree) (args rets : List E), t.name = loop → args.take 2 = [1, gen ^ n] →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → t.total fs ≤ bd loop) :
    osKCB fs cert κ bd Lk loop [1, gen ^ n, qpos, ba, bb, rc, qw] [] :=
  completeAt_of_rel_pureBat hS (by simp) (fun rd hm => by
    obtain ⟨lp, la, lb, lr, lw, lr1⟩ := hM rd hm
    have := resLoop_rel hfind hp hb hc hn lp la lb lr lw lr1 0 hn0
    simpa using this) κ fun rd t hn' hv hbo => hT rd t _ _ hn' rfl hv hbo

end
end LeanVM.Guest.B1
