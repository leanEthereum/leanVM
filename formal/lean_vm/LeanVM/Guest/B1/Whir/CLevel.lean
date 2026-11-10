/-
  LeanVM.Guest.B1.Whir.CLevel

  A level of open_stacked honestly on f128: its blocks composed, at its honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CLvB
public import LeanVM.Guest.B1.Whir.CLvLam
public import LeanVM.Guest.B1.Whir.CRoundsA

/-!
# A level, honestly

* `BlkA.of_ne`: a block needs to be built only where `H` holds somewhere.
* `MidW`: a non-final level's data (round words, the next root's cells and high part, the
  out-of-domain values, the nonces, the cap's root cells, the batch, the pointers of `sent` and the
  squeeze run); its honest values (`cap1`, `cl1`, `cur1`, `S2`, `cap3`, `SL`, `lam`, `claimOut`).
* `MidC C rd σ …`: the level's calls and memory at those values; `osLevelMid_complete`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **A block is needed only where `H` holds somewhere.** -/
theorem BlkA.of_ne {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop}
    (h : (∃ C rd, H C rd) → BlkA H σ k k' ss Out) : BlkA H σ k k' ss Out := by
  by_cases hne : ∃ C rd, H C rd
  · exact h hne
  · exact ⟨fun _ ↦ 0, fun C rd hH ↦ absurd ⟨C, rd, hH⟩ hne⟩

/-- **Two blocks in sequence**, their bounds read off their outcomes. -/
theorem BlkA.seqK {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (hA : BlkA H σ k k1 A OutA) (hkA : ∀ σ', OutA σ' → k ≤ k1)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → (∀ C rd, H C rd → OutA σ1) → BlkA H σ1 k1 k2 B OutB)
    (hkB : ∀ σ', OutB σ' → k1 ≤ k2) :
    BlkA H σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  refine BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ ?_
  obtain ⟨fA, hfA⟩ := hA
  have hO1 := (hfA C0 rd0 hH0 (fill σ k k1 fA) (agree_fill _ _ _ _) (range_fill _ _ _ _)).2
  have h1 := hkA _ hO1
  obtain ⟨fB, hfB⟩ := hB (fill σ k k1 fA) (agree_fill _ _ _ _) fun C rd hH ↦
    (hfA C rd hH _ (agree_fill _ _ _ _) (range_fill _ _ _ _)).2
  have h2 := hkB _ (hfB C0 rd0 hH0 (fill (fill σ k k1 fA) k1 k2 fB) (agree_fill _ _ _ _)
    (range_fill _ _ _ _)).2
  exact BlkA.seq h1 h2 ⟨fA, hfA⟩ hB

/-! ## A non-final level's data -/

/-- A non-final level's data. -/
structure MidW where
  rw : List E
  x0 : E
  x1 : E
  high : List E
  y0 : E
  y1 : E
  nq : E
  n2 : E
  r0 : E
  r1 : E
  batched : E
  pS : E
  pZ : E

namespace MidW

variable (lv : OsLv) (cap : List E) (cl cur : E) (W : MidW)

/-- The next commitment's message. -/
def msg : List E := W.x0 :: W.x1 :: W.high

/-- The capacity, claim and cursor after the rounds. -/
def cap1 : List E := (roundsTr lv.folds cap cl W.rw).1
def cl1 : E := (roundsTr lv.folds cap cl W.rw).2
def cur1 : E := cur * gen ^ (7 * lv.folds)

/-- The query nonce's permutation. -/
def S2 : KeccakState := commitS (W.cap1 lv cap cl) W.msg lv.logCols W.y0 W.y1 W.nq

/-- The capacity after the squeezes. -/
def cap3 : List E := sqCap (capOf (W.S2 lv cap cl)) (lv.squeezes - 1)

/-- The batching nonce's permutation, `λ`. -/
def SL : KeccakState := lamS (W.cap3 lv cap cl) W.n2
def lam : E := rdCell (W.SL lv cap cl) 0

/-- The claim after the glue. -/
def claimOut : E :=
  W.cl1 lv cap cl + W.lam lv cap cl * W.y0 + W.lam lv cap cl * W.lam lv cap cl * W.y1 +
    W.lam lv cap cl * W.lam lv cap cl * W.lam lv cap cl * W.lam lv cap cl ^ lv.queries * W.batched

end MidW

/-- **A non-final level's calls and memory** at its honest values (the fixed buffers' pointers
read from `σ`). -/
structure MidC (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (cap : List E) (cl cur : E) (W : MidW) : Prop where
  rounds : RoundsC C (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) lv.folds lv.foldsOff cap cl cur W.rw
  om : C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L0")
    (W.cap1 lv cap cl ++ [MidW.cur1 lv cur, W.pS])
    (omRets (W.cap1 lv cap cl) W.msg none (MidW.cur1 lv cur) (2 + lv.folds))
  sent : LoadHolds rd W.pS 0 W.x0 ∧ LoadHolds rd W.pS 1 W.x1 ∧
    LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) W.x0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) W.x1
  spf : C ("squeeze_point_from__L" ++ natStr lv.logCols)
    (capOf (omState (W.cap1 lv cap cl) W.msg none) ++
      [cellsOfState (omState (W.cap1 lv cap cl) W.msg none) false 0,
        σ (.n osOodz) * gen ^ (oodSamples * (lvl + 1) * ligColsCap)])
    (spfRets (W.cap1 lv cap cl) W.msg lv.logCols)
  sp : C ("squeeze_point__L" ++ natStr lv.logCols)
    (spfRets (W.cap1 lv cap cl) W.msg lv.logCols ++
      [σ (.n osOodz) * gen ^ ((oodSamples * (lvl + 1) + 1) * ligColsCap)])
    (spRets (W.cap1 lv cap cl) W.msg lv.logCols)
  ys : ReadsAt rd (MidW.cur1 lv cur * gen ^ (2 + lv.folds)) [W.y0, W.y1, W.nq]
  g17 : C ("grind_check__L" ++ natStr queryGrind) [rdCell (W.S2 lv cap cl) 1, σ (.n osTabs)] []
  rows : (∀ i < 5, LoadHolds rd W.pZ (5 + i) ((capOf (W.S2 lv cap cl)).getD i 0)) ∧
    ∀ i < 5, LoadHolds rd W.pZ (lv.squeezes * 5 + i) ((W.cap3 lv cap cl).getD i 0)
  dec : C ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
    [rdCell (W.S2 lv cap cl) 0, σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
      σ (.n osTabs)] []
  loop : gen + gen ^ lv.squeezes ≠ 0 → C (c.sqLoop lvl)
    [gen, gen ^ lv.squeezes, W.pZ, σ (.n osQpos), σ (.n osQbp), σ (.n osTabs)] []
  nb : LoadHolds rd (MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3) 0 W.n2
  g14 : C ("grind_check__L" ++ natStr batchGrind) [rdCell (W.SL lv cap cl) 1, σ (.n osTabs)] []
  mcap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
    [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [W.r0, W.r1]
  roots : LoadHolds rd (σ (.n osRoots)) (2 * lvl) W.r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) W.r1
  hs : ∀ j < lv.folds, LoadHolds rd W.pS (2 + j) (W.high.getD j 0) ∧
    LoadHolds rd (σ (.n osHs)) (lvl * hsStride + j) (W.high.getD j 0 *
      word (hsScale lv.vanish lv.highBits j (vanishInv (lv.vanish + lv.logCols))) 0)
  q : C (osQueriesName c lvl lv)
    [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff, (W.lam lv cap cl)⁻¹,
      σ (.n osCoefs) * gen ^ (3 * lv.foldsOff), σ (.n osHs) * gen ^ (lvl * hsStride),
      σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
      gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)] [W.batched]
  glue : LoadHolds rd (σ (.n osOodSc)) (oodSamples * (lvl + 1)) (W.lam lv cap cl) ∧
    LoadHolds rd (σ (.n osOodSc)) (oodSamples * (lvl + 1) + 1) (W.lam lv cap cl * W.lam lv cap cl) ∧
    LoadHolds rd (σ (.n osBetas)) lvl (W.lam lv cap cl * W.lam lv cap cl * W.lam lv cap cl *
      W.lam lv cap cl ^ lv.queries) ∧
    LoadHolds rd (σ (.n osMus)) lvl (W.lam lv cap cl)⁻¹

/-! ## Static facts of the blocks' states -/

theorem osCommit_word0_lt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osCommit c lvl lv s).2.word0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.pow0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.ys.getD 0 0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.ys.getD 1 0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.co = 3 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> unfold osCommit <;> dsimp only <;>
    (try simp only [List.getD_cons_zero, List.getD_cons_succ]) <;> omega

theorem osCommit_sent (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osCommit c lvl lv s).2.sent = s.k + 1 := rfl

theorem osCommit_k2 (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    s.k + 2 ≤ (osCommit c lvl lv s).2.k := by
  set cu := osCurS { s with k := s.k + 2 } with hcu
  set o0 := osMatS c.plan osOodz (oodSamples * (lvl + 1) * ligColsCap) { cu.2.2 with k := cu.2.2.k + 10 }
  set o1 := osMatS c.plan osOodz ((oodSamples * (lvl + 1) + 1) * ligColsCap) { o0.2.2 with k := o0.2.2.k + 5 }
  have a : s.k + 2 ≤ cu.2.2.k := osCurS_k { s with k := s.k + 2 }
  have b : cu.2.2.k + 10 ≤ o0.2.2.k := osMatS_k c.plan osOodz (oodSamples * (lvl + 1) * ligColsCap)
    { cu.2.2 with k := cu.2.2.k + 10 }
  have d : o0.2.2.k + 5 ≤ o1.2.2.k := osMatS_k c.plan osOodz ((oodSamples * (lvl + 1) + 1) * ligColsCap)
    { o0.2.2 with k := o0.2.2.k + 5 }
  show s.k + 2 ≤ o1.2.2.k + 10 + 26
  omega

theorem osLam_lt (s : OsSt) : (osLam s).2.lam < (osLam s).2.k ∧ (osLam s).2.lamInv < (osLam s).2.k := by
  simp only [osLam]; omega

theorem osQueries_fields (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).2.lam = s.lam ∧ (osQueries c lvl lv s).2.lamInv = s.lamInv ∧
      (osQueries c lvl lv s).2.ys = s.ys ∧ (osQueries c lvl lv s).2.claim = s.claim ∧
      (osQueries c lvl lv s).2.fs = s.fs ∧ (osQueries c lvl lv s).2.cb = s.cb ∧
      (osQueries c lvl lv s).2.co = s.co ∧ (osQueries c lvl lv s).2.pad = s.pad := by
  unfold osQueries
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem osQueries_batched_lt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).2.batched < (osQueries c lvl lv s).2.k := by
  simp only [osQueries]; omega

/-- **A non-final level, honestly** (G:1576-1744). -/
theorem osLevelMid_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hfin : lvl ≠ c.yrLevel) (W : MidW)
    (hr3 : 3 * (lv.foldsOff + lv.folds) < u128Bound)
    (hoff : (oodSamples * (lvl + 1) + 1) * ligColsCap < u128Bound) (hpo : lv.posOff < u128Bound)
    (hS5 : lv.squeezes * 5 < u128Bound) (hS : lv.squeezes < u128Bound)
    (hc4 : 4 * lv.capOff < u128Bound) (h3 : 3 * lv.foldsOff < u128Bound)
    (hh8 : lvl * hsStride < u128Bound)
    (hpq : (if lvl = 0 then lv.queries / 2 else lv.queries) < u128Bound)
    (hpw : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hlam : W.lam lv (st.fsv σ) (σ (.n st.claim)) ≠ 0)
    (hC : ∀ C rd, H C rd → MidC C rd σ c lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W) :
    BlkA H σ st.k (osLevel c lvl lv st).2.k (osLevel c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osLevel c lvl lv st).2 ∧
      (osLevel c lvl lv st).2.F σ' = ⟨capOf (W.SL lv (st.fsv σ) (σ (.n st.claim))), []⟩ ∧
      (osLevel c lvl lv st).2.cur σ' = MidW.cur1 lv (st.cur σ) * gen ^ (2 + lv.folds) * gen ^ 3 * gen ∧
      σ' (.n (osLevel c lvl lv st).2.claim) = W.claimOut lv (st.fsv σ) (σ (.n st.claim)) ∧
      σ' (.n (lvF c lv st).2.k) = gw (2 + lv.folds) ∧ σ' (.n ((lvF c lv st).2.k + 1)) = W.pS ∧
      σ' (.n (lvM c lvl lv st).2.k) = gw ((c.maxSq + 1) * 5) ∧
      σ' (.n ((lvM c lvl lv st).2.k + 1)) = W.pZ ∧
      (osDecCallAt c lv (lvM c lvl lv st).2).2.2.1.map σ' =
        [rdCell (W.S2 lv (st.fsv σ) (σ (.n st.claim))) 0, σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osSqCallAt c lvl lv (lvM c lvl lv st).2).1.map σ' = some (gen + gen ^ lv.squeezes) ∧
      (osSqCallAt c lvl lv (lvM c lvl lv st).2).2.2.1.map σ' =
        [gen, gen ^ lv.squeezes, W.pZ, σ (.n osQpos), σ (.n osQbp), σ (.n osTabs)] ∧
      (osQCallAt c lvl lv (lvH c lvl lv st).2).2.2.1.map σ' =
        [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
          (W.lam lv (st.fsv σ) (σ (.n st.claim)))⁻¹, σ (.n osCoefs) * gen ^ (3 * lv.foldsOff),
          σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff, gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)] ∧
      (osQCallAt c lvl lv (lvH c lvl lv st).2).2.2.2.map σ' = [W.batched]) := by
  set cap := st.fsv σ with hcap
  set cl := σ (.n st.claim) with hcl
  set cur := st.cur σ with hcur
  set k := st.k with hk
  have k36 : 36 ≤ k := hsf.k
  set s1 := (osRounds c.plan lv.foldsOff lv.folds st).2 with hs1
  set s2 := (osCommit c lvl lv s1).2 with hs2
  set s4 := (osSqueezes c lvl lv s2).2 with hs4
  set s5 := (osLam s4).2 with hs5
  set s6 := (osCap c lvl lv s5).2 with hs6
  set s7 := (osHsMid lvl lv s6).2 with hs7
  set s8 := (osQueries c lvl lv s7).2 with hs8
  have sf1 : s1.Sf := osRounds_sf _ _ _ _ hsf
  have k1 : k ≤ s1.k := osRounds_k _ _ _ _
  -- the rounds
  have b1 : BlkA H σ k s1.k (osRounds c.plan lv.foldsOff lv.folds st).1 (fun σ' ↦
      RoundsOut σ σ' st s1 (roundsTr lv.folds cap cl W.rw) lv.folds ∧ AgreeBelow k σ σ') :=
    osRounds_completeA lv.folds lv.foldsOff st σ W.rw hsf.co hr3 hsf.below
      (fun C rd hH ↦ (hok C rd hH).mats) hsf.k hsf.fs fun C rd hH ↦ (hC C rd hH).rounds
  have ep1 : s1.pad = st.pad := osRounds_pad _ _ _ _
  -- the message
  have b2 := BlkA.seqK b1 (fun σ' h ↦ h.1.k) (B := (osCommit c lvl lv s1).1)
    (OutB := fun σ' ↦ s2.Ok σ' ∧ s1.k ≤ s2.k ∧ k ≤ s2.k ∧ s2.F σ' = ⟨capOf (W.S2 lv cap cl), []⟩ ∧
      σ' (.n s2.word0) = rdCell (W.S2 lv cap cl) 0 ∧ σ' (.n s2.pow0) = rdCell (W.S2 lv cap cl) 1 ∧
      σ' (.n (s2.ys.getD 0 0)) = W.y0 ∧ σ' (.n (s2.ys.getD 1 0)) = W.y1 ∧
      σ' (.n s2.sent) = W.pS ∧ σ' (.n s1.k) = gw (2 + lv.folds) ∧
      s2.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧ s2.claim = s1.claim ∧
      s2.pad = s1.pad)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ro := (ho1 C0 rd0 hH0).1
      have ef : s1.fsv σ1 = W.cap1 lv cap cl := by
        have := congrArg Fs.cap ro.F
        simpa [OsSt.F, OsSt.fsv, MidW.cap1] using this
      have ecur : s1.cur σ1 = MidW.cur1 lv cur := ro.cur
      have hroots : σ1 (.n osRoots) = σ (.n osRoots) := ha1 _ (by show 17 < k; omega)
      have hoodz : σ1 (.n osOodz) = σ (.n osOodz) := ha1 _ (by show 29 < k; omega)
      have h := osCommit_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s1) σ1 sf1
        (fun C rd hH ↦ ⟨sf1, (ho1 C rd hH).1.mats, by rw [ep1]; exact ((hok C rd hH).agree ha1).pad⟩)
        W.x0 W.x1 W.high W.y0 W.y1 W.nq W.pS hoff
        (fun C rd hH ↦ by rw [ef, ecur]; exact (hC C rd hH).om)
        (fun C rd hH ↦ by rw [hroots]; exact (hC C rd hH).sent)
        (fun C rd hH ↦ by rw [ef, hoodz]; exact (hC C rd hH).spf)
        (fun C rd hH ↦ by rw [ef, hoodz]; exact (hC C rd hH).sp)
        (fun C rd hH ↦ by rw [ecur]; exact (hC C rd hH).ys)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hw, hp, -, hy0, hy1, hsent, hsz, hcur, hclm, hpad⟩ := ho
      rw [ef] at hF hw hp
      rw [ecur] at hcur
      exact ⟨hst.ok, hst.le, le_trans ro.k hst.le, hF, hw, hp, hy0, hy1, hsent, hsz, hcur, hclm, hpad⟩)
    (fun _ _ ↦ le_trans (Nat.le_add_right _ 2) (osCommit_k2 c lvl lv s1))
  -- the query grind
  have b3 := BlkA.seqK b2 (fun σ' h ↦ h.2.2.2.1) (B := [.call ("grind_check__L" ++ natStr queryGrind) ([s2.pow0, osTabs].map V.n) []])
    (OutB := fun _ ↦ True) (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have w := osCommit_word0_lt c lvl lv s1
      have h := call0_blk (H := H) (σ := σ1) (k := s2.k)
        (f := "grind_check__L" ++ natStr queryGrind) (args := [s2.pow0, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact w.2.1
          · have := (ho1 C0 rd0 hH0).2.2.2.1; show 9 < s2.k; omega)
        fun C rd hH ↦ by
          simp only [List.map_cons, List.map_nil]
          rw [(ho1 C rd hH).2.2.2.2.2.2.1, ha1 _ (show 9 < k by omega)]
          exact (hC C rd hH).g17
      exact h.mono fun _ _ ↦ trivial) (fun _ _ ↦ le_rfl)
  -- the squeezes
  have b4 := BlkA.seqK b3 (fun σ' h ↦ h.1.2.2.2.1) (B := (osSqueezes c lvl lv s2).1)
    (OutB := fun σ' ↦ s4.Ok σ' ∧ s2.k ≤ s4.k ∧ k ≤ s4.k ∧ s4.F σ' = ⟨W.cap3 lv cap cl, []⟩ ∧
      σ' (.n s2.k) = gw ((c.maxSq + 1) * 5) ∧ σ' (.n (s2.k + 1)) = W.pZ ∧
      s4.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧ s4.co = s2.co ∧
      (osDecCallAt c lv s2).2.2.1.map σ' = [rdCell (W.S2 lv cap cl) 0, σ (.n osQpos) * gen ^ lv.posOff,
        σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osSqCallAt c lvl lv s2).1.map σ' = some (gen + gen ^ lv.squeezes) ∧
      (osSqCallAt c lvl lv s2).2.2.1.map σ' =
        [gen, gen ^ lv.squeezes, W.pZ, σ (.n osQpos), σ (.n osQbp), σ (.n osTabs)])
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok2, -, hk2, hF2, hw2, -, -, -, -, -, hcur2, -, -⟩ := (ho1 C0 rd0 hH0).1.2
      have ef : s2.fsv σ1 = capOf (W.S2 lv cap cl) := by
        have := congrArg Fs.cap hF2
        simpa [OsSt.F, OsSt.fsv] using this
      have eq9 : σ1 (.n osTabs) = σ (.n osTabs) := ha1 _ (show 9 < k by omega)
      have eqp : σ1 (.n osQpos) = σ (.n osQpos) := ha1 _ (show 33 < k by omega)
      have eqb : σ1 (.n osQbp) = σ (.n osQbp) := ha1 _ (show 35 < k by omega)
      have h := osSqueezes_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s2) σ1 ok2.sf
        (fun C rd hH ↦ (ho1 C rd hH).1.2.1) (osCommit_word0_lt c lvl lv s1).1 W.pZ hpo hS5 hS
        (fun C rd hH ↦ by rw [ef]; exact (hC C rd hH).rows)
        (fun C rd hH ↦ by rw [hw2, eqp, eqb, eq9]; exact (hC C rd hH).dec)
        (fun C rd hH ↦ by rw [eqp, eqb, eq9]; exact (hC C rd hH).loop)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hsz, hpz, hcur, -, -, hco, -, hdec, hg, hla⟩ := ho
      rw [ef] at hF
      rw [hw2, eqp, eqb, eq9] at hdec
      rw [eqp, eqb, eq9] at hla
      rw [hcur2] at hcur
      exact ⟨hst.ok, hst.le, le_trans hk2 hst.le, hF, hsz, hpz, hcur, hco, hdec, hg, hla⟩)
    (fun σ' h ↦ h.2.1)
  -- the batching challenge
  have b5 := BlkA.seqK b4 (fun σ' h ↦ h.2.2.2.1) (B := (osLam s4).1)
    (OutB := fun σ' ↦ s5.Ok σ' ∧ s4.k ≤ s5.k ∧ k ≤ s5.k ∧ s5.F σ' = ⟨capOf (W.SL lv cap cl), []⟩ ∧
      σ' (.n s5.lam) = W.lam lv cap cl ∧ σ' (.n s5.lamInv) = (W.lam lv cap cl)⁻¹ ∧
      s5.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 * gen)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok4, -, hk4, hF4, -, -, hcur4, hco4, -⟩ := (ho1 C0 rd0 hH0).2
      have ef : s4.fsv σ1 = W.cap3 lv cap cl := by
        have := congrArg Fs.cap hF4
        simpa [OsSt.F, OsSt.fsv] using this
      have hco : s4.co = 3 := hco4.trans (osCommit_word0_lt c lvl lv s1).2.2.2.2
      have h := osLam_complete (H := H) (st := s4) σ1 ok4.sf (fun C rd hH ↦ (ho1 C rd hH).2.1)
        (by rw [hco]; unfold u128Bound; omega) W.n2 (by rw [ef]; exact hlam)
        (fun C rd hH ↦ by rw [hcur4]; exact (hC C rd hH).nb)
        (fun C rd hH ↦ by rw [ef, ha1 _ (show 9 < k by omega)]; exact (hC C rd hH).g14)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hl, hli, hcur, -⟩ := ho
      rw [ef] at hF hl hli
      rw [hcur4] at hcur
      exact ⟨hst.ok, hst.le, le_trans hk4 hst.le, hF, hl, hli, hcur⟩)
    (fun σ' h ↦ h.2.1)
  -- the cap
  have b6 := BlkA.seqK b5 (fun σ' h ↦ h.2.2.2.1) (B := (osCap c lvl lv s5).1)
    (OutB := fun σ' ↦ s6.Ok σ' ∧ s5.k ≤ s6.k ∧ k ≤ s6.k)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok5, -, hk5, -⟩ := (ho1 C0 rd0 hH0).2
      have h := osCap_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s5) σ1 ok5.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.r0 W.r1 hc4
        (fun C rd hH ↦ by
          rw [ha1 _ (show 11 < k by omega), ha1 _ (show 13 < k by omega)]; exact (hC C rd hH).mcap)
        (fun C rd hH ↦ by rw [ha1 _ (show 17 < k by omega)]; exact (hC C rd hH).roots)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le, le_trans hk5 ho.le⟩)
    (fun σ' h ↦ h.2.1)
  -- the high part
  have b7 := BlkA.seqK b6 (fun σ' h ↦ h.2.2.2) (B := (osHsMid lvl lv s6).1)
    (OutB := fun σ' ↦ s7.Ok σ' ∧ s6.k ≤ s7.k ∧ k ≤ s7.k)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok6 := (ho1 C0 rd0 hH0).2.1
      have hk6 := (ho1 C0 rd0 hH0).2.2.2
      obtain ⟨-, -, -, -, -, -, -, -, hsent2, -⟩ := (ho1 C0 rd0 hH0).1.1.1.1.2
      have r4 := (ho1 C0 rd0 hH0).1.1.2.2.1
      have r5 := (ho1 C0 rd0 hH0).1.2.2.1
      have r6 := (ho1 C0 rd0 hH0).2.2.1
      have e6 : s6.sent = s1.k + 1 := rfl
      have hk12 : s1.k + 2 ≤ s2.k := osCommit_k2 c lvl lv s1
      have h := osHsMid_complete (H := H) (lvl := lvl) (lv := lv) (st := s6) σ1 ok6.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by rw [e6]; omega) (fun j ↦ W.high.getD j 0)
        (fun C rd hH j hj ↦ by
          rw [show s6.sent = s2.sent from rfl, hsent2, ha1 _ (show 27 < k by omega)]
          exact (hC C rd hH).hs j hj)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le, le_trans hk6 ho.le⟩)
    (fun σ' h ↦ h.2.1)
  -- the queries
  have eq5l : s7.lamInv = s5.lamInv := rfl
  have b8 := BlkA.seqK b7 (fun σ' h ↦ h.2.2.2) (B := (osQueries c lvl lv s7).1)
    (OutB := fun σ' ↦ s8.Ok σ' ∧ s7.k ≤ s8.k ∧ k ≤ s8.k ∧
      (osQCallAt c lvl lv s7).2.2.1.map σ' =
        [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
          (W.lam lv cap cl)⁻¹, σ (.n osCoefs) * gen ^ (3 * lv.foldsOff),
          σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff, gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)] ∧
      (osQCallAt c lvl lv s7).2.2.2.map σ' = [W.batched] ∧ σ' (.n s8.batched) = W.batched)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok7 := (ho1 C0 rd0 hH0).2.1
      have hk7 := (ho1 C0 rd0 hH0).2.2.2
      obtain ⟨-, r5, -, -, -, hli5, -⟩ := (ho1 C0 rd0 hH0).1.1.2
      have r6 := (ho1 C0 rd0 hH0).1.2.2.1
      have r7 := (ho1 C0 rd0 hH0).2.2.1
      have hl5 : s5.lamInv < s5.k := (osLam_lt s4).2
      have eA : osQArgsV σ1 c lvl lv s7 =
          [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
            (W.lam lv cap cl)⁻¹, σ (.n osCoefs) * gen ^ (3 * lv.foldsOff),
            σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
            σ (.n osQbp) * gen ^ lv.posOff, gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)] := by
        simp only [osQArgsV, hfin, ↓reduceIte]
        rw [eq5l, hli5, ha1 _ (show 11 < k by omega), ha1 _ (show 13 < k by omega),
          ha1 _ (show 21 < k by omega), ha1 _ (show 27 < k by omega), ha1 _ (show 33 < k by omega),
          ha1 _ (show 35 < k by omega)]
      have h := osQueries_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s7) σ1 ok7.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.batched hc4 h3 hpo hh8 hpq
        (fun _ ↦ by rw [eq5l]; omega) (fun h ↦ absurd h hfin)
        (fun C rd hH ↦ by rw [eA]; exact (hC C rd hH).q)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hargs, hrets, hbat⟩ := ho
      rw [eA] at hargs
      exact ⟨hst.ok, hst.le, le_trans hk7 hst.le, hargs, hrets, hbat⟩)
    (fun σ' h ↦ h.2.1)
  -- the glue
  have b9 := BlkA.seqK b8 (fun σ' h ↦ h.2.2.2.1) (B := (osGlue lvl lv s8).1)
    (OutB := fun σ' ↦ (osGlue lvl lv s8).2.Ok σ' ∧ s8.k ≤ (osGlue lvl lv s8).2.k ∧
      k ≤ (osGlue lvl lv s8).2.k ∧ σ' (.n (osGlue lvl lv s8).2.claim) = W.claimOut lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok8 := (ho1 C0 rd0 hH0).2.1
      have hk8 := (ho1 C0 rd0 hH0).2.2.2.1
      have hbat8 := (ho1 C0 rd0 hH0).2.2.2.2.2.2
      have r8 := (ho1 C0 rd0 hH0).2.2.1
      have r7 := (ho1 C0 rd0 hH0).1.2.2.1
      have r6 := (ho1 C0 rd0 hH0).1.1.2.2.1
      obtain ⟨-, r5, -, -, hl5, hli5, -⟩ := (ho1 C0 rd0 hH0).1.1.1.2
      obtain ⟨-, r4, -⟩ := (ho1 C0 rd0 hH0).1.1.1.1.2
      obtain ⟨-, r2, -, -, -, -, hy0, hy1, -⟩ := (ho1 C0 rd0 hH0).1.1.1.1.1.1.2
      have ro := (ho1 C0 rd0 hH0).1.1.1.1.1.1.1.1
      have w2 := osCommit_word0_lt c lvl lv s1
      have hlt5 : s5.lam < s5.k ∧ s5.lamInv < s5.k := osLam_lt s4
      have hbl : s8.batched < s8.k := osQueries_batched_lt c lvl lv s7
      have fq := osQueries_fields c lvl lv s7
      have e8l : s8.lam = s5.lam := fq.1
      have e8i : s8.lamInv = s5.lamInv := fq.2.1
      have e8y : s8.ys = s2.ys := fq.2.2.1
      have e8c : s8.claim = s1.claim := fq.2.2.2.1
      have w2' : s2.ys.getD 0 0 < s2.k ∧ s2.ys.getD 1 0 < s2.k := ⟨w2.2.2.1, w2.2.2.2.1⟩
      have h := osGlue_complete (H := H) (lvl := lvl) (lv := lv) (st := s8) σ1 ok8.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by rw [e8l]; omega) (by rw [e8y]; omega)
        (by rw [e8y]; omega) hbl (by rw [e8i]; omega) hpw
        (fun C rd hH ↦ by
          rw [e8l, e8i, hl5, hli5, ha1 _ (show 31 < k by omega), ha1 _ (show 23 < k by omega),
            ha1 _ (show 25 < k by omega)]
          exact (hC C rd hH).glue)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hcl⟩ := ho
      rw [e8l, e8y, e8c, hl5, hy0, hy1, hbat8, ro.claim] at hcl
      exact ⟨hst.ok, hst.le, le_trans hk8 hst.le, hcl⟩)
    (fun σ' h ↦ h.2.1)
  -- the level
  have eL : osLevel c lvl lv st = ((osRounds c.plan lv.foldsOff lv.folds st).1 ++
      (osCommit c lvl lv s1).1 ++
      [.call ("grind_check__L" ++ natStr queryGrind) ([s2.pow0, osTabs].map V.n) []] ++
      (osSqueezes c lvl lv s2).1 ++ (osLam s4).1 ++ (osCap c lvl lv s5).1 ++ (osHsMid lvl lv s6).1 ++
      (osQueries c lvl lv s7).1 ++ (osGlue lvl lv s8).1, (osGlue lvl lv s8).2) := by
    simp only [osLevel, hfin, ↓reduceIte]
    rfl
  have eM : (lvM c lvl lv st).2 = s2 := by simp only [lvM, lvF, hfin, ↓reduceIte]; rfl
  have eH : (lvH c lvl lv st).2 = s7 := by simp only [lvH, lvS, lvM, lvF, hfin, ↓reduceIte]; rfl
  have eF : (lvF c lv st).2 = s1 := rfl
  rw [eL, eM, eH, eF]
  refine BlkA.mono b9.agree fun σ' ho ↦ ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro, -⟩, B2⟩, -⟩, B4⟩, B5⟩, -⟩, -⟩, B8⟩, B9⟩, hag⟩ := ho
  obtain ⟨-, -, -, -, -, -, -, -, hsent2, hsz2, -⟩ := B2
  obtain ⟨-, -, -, -, hsz4, hpz4, -, -, hdec, hg, hla⟩ := B4
  obtain ⟨-, -, -, hF5, -, -, hcur5⟩ := B5
  obtain ⟨-, -, -, hargs, hrets, -⟩ := B8
  obtain ⟨ok9, -, hk9, hcl9⟩ := B9
  have fq := osQueries_fields c lvl lv s7
  refine ⟨⟨ok9, hk9, hag⟩, ?_, ?_, hcl9, hsz2, hsent2, hsz4, hpz4, hdec, hg, hla, hargs, hrets⟩
  · rw [← hF5]
    simp only [OsSt.F]
    rw [show (osGlue lvl lv s8).2.fs = s5.fs from fq.2.2.2.2.1]
  · rw [← hcur5]
    simp only [OsSt.cur]
    rw [show (osGlue lvl lv s8).2.cb = s5.cb from fq.2.2.2.2.2.1,
      show (osGlue lvl lv s8).2.co = s5.co from fq.2.2.2.2.2.2.1]

end
end LeanVM.Guest.B1.Whir
