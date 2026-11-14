/-
  LeanVM.Guest.B1.Whir.CLevel

  A level of open_stacked honestly: its blocks composed, at its honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CLvB
public import LeanVM.Guest.B1.Whir.CLvLam
public import LeanVM.Guest.B1.Whir.CRoundsA
public import LeanVM.Guest.B1.Whir.CDisp

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
  n1 : E
  y0 : E
  nq : E
  r0 : E
  r1 : E
  batched : E
  pS : E

namespace MidW

variable (lv : OsLv) (cap : List E) (cl cur : E) (W : MidW)

/-- The next commitment's message. -/
def msg : List E := W.x0 :: W.x1 :: W.high

/-- The capacity, claim and cursor after the rounds. -/
def cap1 : List E := (roundsTr lv.folds cap cl W.rw).1
def cl1 : E := (roundsTr lv.folds cap cl W.rw).2
def cur1 : E := cur * gen ^ (5 * lv.folds)

/-- The query nonce's permutation. -/
def S2 : KeccakState := commitS (W.cap1 lv cap cl) W.msg W.n1 lv.logCols W.y0 W.nq

/-- The capacity after the squeezes. -/
def cap3 : List E := sqCapD (capOf (W.S2 lv cap cl)) (lv.squeezes - 1)

/-- The squeeze's permutation, `λ`. -/
def SL : KeccakState := lamS (W.cap3 lv cap cl)
def lam : E := rdCell (W.SL lv cap cl) 0

/-- The claim after the glue. -/
def claimOut : E :=
  W.cl1 lv cap cl + W.lam lv cap cl * W.y0 +
    W.lam lv cap cl * W.lam lv cap cl * W.lam lv cap cl ^ lv.queries * W.batched

end MidW

/-- **A non-final level's calls and memory** at its honest values (the fixed buffers' pointers
read from `σ`). -/
structure MidC (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (cap : List E) (cl cur : E) (W : MidW) : Prop where
  rounds : RoundsC C (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) lv.folds lv.foldsOff cap cl cur W.rw
  om : C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1")
    (W.cap1 lv cap cl ++ [MidW.cur1 lv cur, W.pS])
    (omRets (W.cap1 lv cap cl) W.msg (some W.n1) (MidW.cur1 lv cur) (2 + lv.folds + 1))
  g0 : C ("grind_check__L" ++ natStr levelOodGrind)
    [cellsOfState (omState (W.cap1 lv cap cl) W.msg (some W.n1)) false 1, σ (.n osTabs)] []
  sent : LoadHolds rd W.pS 0 W.x0 ∧ LoadHolds rd W.pS 1 W.x1 ∧
    LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) W.x0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) W.x1
  spf : C ("squeeze_point_from__L" ++ natStr lv.logCols)
    (capOf (omState (W.cap1 lv cap cl) W.msg (some W.n1)) ++
      [cellsOfState (omState (W.cap1 lv cap cl) W.msg (some W.n1)) false 0,
        σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)])
    (spfRets (W.cap1 lv cap cl) W.msg W.n1 lv.logCols)
  ys : ReadsAt rd (MidW.cur1 lv cur * gen ^ (2 + lv.folds + 1)) [W.y0, W.nq]
  g17 : C ("grind_check__L" ++ natStr queryGrind) [rdCell (W.S2 lv cap cl) 1, σ (.n osTabs)] []
  lp : C (osPositionsName lv) (rdCell (W.S2 lv cap cl) 0 :: capOf (W.S2 lv cap cl) ++
    [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)]) (W.cap3 lv cap cl)
  hs : ∀ j < lv.folds, LoadHolds rd W.pS (2 + j) (W.high.getD j 0) ∧
    LoadHolds rd (σ (.n osHs)) (lvl * hsStride + j) (W.high.getD j 0 *
      word (hsScale lv.vanish lv.highBits j (vanishInv (lv.vanish + lv.logCols))) 0)
  q : C (osQueriesName c lvl lv)
    [W.lam lv cap cl, (W.lam lv cap cl)⁻¹, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
      σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
      σ (.n osQbp) * gen ^ lv.posOff] [W.r0, W.r1, W.batched, W.lam lv cap cl ^ lv.queries]
  roots : LoadHolds rd (σ (.n osRoots)) (2 * lvl) W.r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) W.r1
  glue : LoadHolds rd (σ (.n osOodSc)) (lvl + 1) (W.lam lv cap cl) ∧
    LoadHolds rd (σ (.n osBetas)) lvl (W.lam lv cap cl * W.lam lv cap cl *
      W.lam lv cap cl ^ lv.queries) ∧
    LoadHolds rd (σ (.n osMus)) lvl (W.lam lv cap cl)⁻¹

/-! ## Static facts of the blocks' states -/

theorem lt_osPad (pad : Option ℕ) (b : ℕ) : b < (osPad pad (b + 6)).2.2 + 13 := by
  have := osPad_next pad (b + 6); omega

theorem osCommit_word0_lt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osCommit c lvl lv s).2.word0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.pow0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.ys.getD 0 0 < (osCommit c lvl lv s).2.k ∧
      (osCommit c lvl lv s).2.co = 2 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · unfold osCommit; dsimp only; omega
  · unfold osCommit; dsimp only; omega
  · unfold osCommit; dsimp only; simp only [List.getD_cons_zero]; exact lt_osPad _ _

theorem osCommit_k2 (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    s.k + 2 ≤ (osCommit c lvl lv s).2.k := by
  set cu := osCurS { s with k := s.k + 2 } with hcu
  set o0 := osMatS c.plan osOodz ((lvl + 1) * ligColsCap) { cu.2.2 with k := cu.2.2.k + 10 }
  have a : s.k + 2 ≤ cu.2.2.k := osCurS_k { s with k := s.k + 2 }
  have b : cu.2.2.k + 10 ≤ o0.2.2.k := osMatS_k c.plan osOodz ((lvl + 1) * ligColsCap)
    { cu.2.2 with k := cu.2.2.k + 10 }
  have d := osPad_next o0.2.2.pad (o0.2.2.k + 10 + 6)
  show s.k + 2 ≤ (osPad o0.2.2.pad (o0.2.2.k + 10 + 6)).2.2 + 13
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
    (osQueries c lvl lv s).2.batched < (osQueries c lvl lv s).2.k ∧
      (osQueries c lvl lv s).2.lamPow < (osQueries c lvl lv s).2.k := by
  simp only [osQueries]; omega

/-- **A non-final level, honestly**. -/
theorem osLevelMid_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hfin : lvl ≠ c.yrLevel) (W : MidW)
    (hr3 : 2 * (lv.foldsOff + lv.folds) < u128Bound)
    (hoff : (lvl + 1) * ligColsCap < u128Bound) (hpo : lv.posOff < u128Bound)
    (h3 : 2 * lv.foldsOff < u128Bound) (hh8 : lvl * hsStride < u128Bound)
    (hlam : W.lam lv (st.fsv σ) (σ (.n st.claim)) ≠ 0)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, H C rd → MidC C rd σ c lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W) :
    BlkA H σ st.k (osLevel c lvl lv st).2.k (osLevel c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osLevel c lvl lv st).2 ∧
      (osLevel c lvl lv st).2.F σ' = ⟨capOf (W.SL lv (st.fsv σ) (σ (.n st.claim))), []⟩ ∧
      (osLevel c lvl lv st).2.cur σ' = MidW.cur1 lv (st.cur σ) * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      σ' (.n (osLevel c lvl lv st).2.claim) = W.claimOut lv (st.fsv σ) (σ (.n st.claim)) ∧
      σ' (.n (osRounds c.plan lv.foldsOff lv.folds st).2.k) = gw (2 + lv.folds) ∧
      σ' (.n ((osRounds c.plan lv.foldsOff lv.folds st).2.k + 1)) = W.pS ∧
      (osPosCall c lv (osCommit c lvl lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).1.map σ' =
        rdCell (W.S2 lv (st.fsv σ) (σ (.n st.claim))) 0 :: capOf (W.S2 lv (st.fsv σ) (σ (.n st.claim))) ++
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osPosCall c lv (osCommit c lvl lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2.map σ' =
        W.cap3 lv (st.fsv σ) (σ (.n st.claim)) ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).1.map σ' =
        [W.lam lv (st.fsv σ) (σ (.n st.claim)), (W.lam lv (st.fsv σ) (σ (.n st.claim)))⁻¹,
          σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), σ (.n osHs) * gen ^ (lvl * hsStride),
          σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).2.map σ' =
        [W.r0, W.r1, W.batched, W.lam lv (st.fsv σ) (σ (.n st.claim)) ^ lv.queries]) := by
  set cap := st.fsv σ with hcap
  set cl := σ (.n st.claim) with hcl
  set cur := st.cur σ with hcur
  set k := st.k with hk
  have k33 : 33 ≤ k := hsf.k
  set s1 := (osRounds c.plan lv.foldsOff lv.folds st).2 with hs1
  set s2 := (osCommit c lvl lv s1).2 with hs2
  set s4 := (osPositions c lvl lv s2).2 with hs4
  set s5 := (osLam s4).2 with hs5
  set s6 := (osHsMid lvl lv s5).2 with hs6
  set s7 := (osQueries c lvl lv s6).2 with hs7
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
      σ' (.n (s2.ys.getD 0 0)) = W.y0 ∧
      σ' (.n s2.sent) = W.pS ∧ σ' (.n s1.k) = gw (2 + lv.folds) ∧
      s2.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧ s2.claim = s1.claim)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ro := (ho1 C0 rd0 hH0).1
      have ef : s1.fsv σ1 = W.cap1 lv cap cl := by
        have := congrArg Fs.cap ro.F
        simpa [OsSt.F, OsSt.fsv, MidW.cap1] using this
      have ecur : s1.cur σ1 = MidW.cur1 lv cur := ro.cur
      have hroots : σ1 (.n osRoots) = σ (.n osRoots) := ha1 _ (by show 14 < k; omega)
      have hoodz : σ1 (.n osOodz) = σ (.n osOodz) := ha1 _ (by show 26 < k; omega)
      have h := osCommit_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s1) σ1 sf1
        (fun C rd hH ↦ ⟨sf1, (ho1 C rd hH).1.mats, by rw [ep1]; exact ((hok C rd hH).agree ha1).pad⟩)
        W.x0 W.x1 W.high W.n1 W.y0 W.nq W.pS hoff
        (fun C rd hH ↦ by rw [ef, ecur]; exact (hC C rd hH).om)
        (fun C rd hH ↦ by rw [ef, ha1 _ (show 10 < k by omega)]; exact (hC C rd hH).g0)
        (fun C rd hH ↦ by rw [hroots]; exact (hC C rd hH).sent)
        (fun C rd hH ↦ by rw [ef, hoodz]; exact (hC C rd hH).spf)
        (fun C rd hH ↦ by rw [ecur]; exact (hC C rd hH).ys)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hw, hp, -, hy0, hsent, hsz, hcur, hclm⟩ := ho
      rw [ef] at hF hw hp
      rw [ecur] at hcur
      exact ⟨hst.ok, hst.le, le_trans ro.k hst.le, hF, hw, hp, hy0, hsent, hsz, hcur, hclm⟩)
    (fun _ _ ↦ le_trans (Nat.le_add_right _ 2) (osCommit_k2 c lvl lv s1))
  -- the query grind
  have b3 := BlkA.seqK b2 (fun σ' h ↦ h.2.2.2.1)
    (B := [.call ("grind_check__L" ++ natStr queryGrind) ([s2.pow0, osTabs].map V.n) []])
    (OutB := fun _ ↦ True) (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have w := osCommit_word0_lt c lvl lv s1
      have h := call0_blk (H := H) (σ := σ1) (k := s2.k)
        (f := "grind_check__L" ++ natStr queryGrind) (args := [s2.pow0, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact w.2.1
          · have := (ho1 C0 rd0 hH0).2.2.2.1; show 10 < s2.k; omega)
        fun C rd hH ↦ by
          simp only [List.map_cons, List.map_nil]
          rw [(ho1 C rd hH).2.2.2.2.2.2.1, ha1 _ (show 10 < k by omega)]
          exact (hC C rd hH).g17
      exact h.mono fun _ _ ↦ trivial) (fun _ _ ↦ le_rfl)
  -- the positions
  have b4 := BlkA.seqK b3 (fun σ' h ↦ h.1.2.2.2.1) (B := (osPositions c lvl lv s2).1)
    (OutB := fun σ' ↦ s4.Ok σ' ∧ s2.k ≤ s4.k ∧ k ≤ s4.k ∧ s4.F σ' = ⟨W.cap3 lv cap cl, []⟩ ∧
      s4.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧ s4.co = s2.co ∧
      (osPosCall c lv s2).1.map σ' = rdCell (W.S2 lv cap cl) 0 :: capOf (W.S2 lv cap cl) ++
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osPosCall c lv s2).2.map σ' = W.cap3 lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok2, -, hk2, hF2, hw2, -, -, -, -, hcur2, -⟩ := (ho1 C0 rd0 hH0).1.2
      have ef : s2.fsv σ1 = capOf (W.S2 lv cap cl) := by
        have := congrArg Fs.cap hF2
        simpa [OsSt.F, OsSt.fsv] using this
      have eq9 : σ1 (.n osTabs) = σ (.n osTabs) := ha1 _ (show 10 < k by omega)
      have eqp : σ1 (.n osQpos) = σ (.n osQpos) := ha1 _ (show 30 < k by omega)
      have eqb : σ1 (.n osQbp) = σ (.n osQbp) := ha1 _ (show 32 < k by omega)
      have hcl3 : (W.cap3 lv cap cl).length = 5 := sqCapD_length (by simp [capOf]) _
      have h := osPositions_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s2) σ1 ok2.sf
        (fun C rd hH ↦ (ho1 C rd hH).1.2.1) (osCommit_word0_lt c lvl lv s1).1 hpo (W.cap3 lv cap cl)
        hcl3
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          rw [(ho1 C rd hH).1.2.2.2.2.2.1, ef, eqp, eqb, eq9]; exact (hC C rd hH).lp)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hcur, -, -, hco, -, hargs, hrets⟩ := ho
      rw [hw2, ef, eqp, eqb, eq9] at hargs
      rw [hcur2] at hcur
      exact ⟨hst.ok, hst.le, le_trans hk2 hst.le, hF, hcur, hco, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the batching challenge
  have b5 := BlkA.seqK b4 (fun σ' h ↦ h.2.2.2.1) (B := (osLam s4).1)
    (OutB := fun σ' ↦ s5.Ok σ' ∧ s4.k ≤ s5.k ∧ k ≤ s5.k ∧ s5.F σ' = ⟨capOf (W.SL lv cap cl), []⟩ ∧
      σ' (.n s5.lam) = W.lam lv cap cl ∧ σ' (.n s5.lamInv) = (W.lam lv cap cl)⁻¹ ∧
      s5.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok4, -, hk4, hF4, hcur4, hco4, -⟩ := (ho1 C0 rd0 hH0).2
      have ef : s4.fsv σ1 = W.cap3 lv cap cl := by
        have := congrArg Fs.cap hF4
        simpa [OsSt.F, OsSt.fsv] using this
      have hco : s4.co = 2 := hco4.trans (osCommit_word0_lt c lvl lv s1).2.2.2
      have h := osLam_complete (H := H) (st := s4) σ1 ok4.sf (fun C rd hH ↦ (ho1 C rd hH).2.1)
        (by rw [hco]; unfold u128Bound; omega) (by rw [ef]; exact hlam)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hl, hli, hcur, -⟩ := ho
      rw [ef] at hF hl hli
      rw [hcur4] at hcur
      exact ⟨hst.ok, hst.le, le_trans hk4 hst.le, hF, hl, hli, hcur⟩)
    (fun σ' h ↦ h.2.1)
  -- the high part
  have b6 := BlkA.seqK b5 (fun σ' h ↦ h.2.2.2.1) (B := (osHsMid lvl lv s5).1)
    (OutB := fun σ' ↦ s6.Ok σ' ∧ s5.k ≤ s6.k ∧ k ≤ s6.k)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok5 := (ho1 C0 rd0 hH0).2.1
      have hk5 := (ho1 C0 rd0 hH0).2.2.2.1
      obtain ⟨-, -, -, -, -, -, -, hsent2, -⟩ := (ho1 C0 rd0 hH0).1.1.1.2
      have r4 := (ho1 C0 rd0 hH0).1.2.2.1
      have r5 := (ho1 C0 rd0 hH0).2.2.1
      have e5 : s5.sent = s1.k + 1 := rfl
      have hk12 : s1.k + 2 ≤ s2.k := osCommit_k2 c lvl lv s1
      have h := osHsMid_complete (H := H) (lvl := lvl) (lv := lv) (st := s5) σ1 ok5.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by rw [e5]; omega) (fun j ↦ W.high.getD j 0)
        (fun C rd hH j hj ↦ by
          rw [show s5.sent = s2.sent from rfl, hsent2, ha1 _ (show 24 < k by omega)]
          exact (hC C rd hH).hs j hj)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le, le_trans hk5 ho.le⟩)
    (fun σ' h ↦ h.2.1)
  -- the queries
  have b7 := BlkA.seqK b6 (fun σ' h ↦ h.2.2.2) (B := (osQueries c lvl lv s6).1)
    (OutB := fun σ' ↦ s7.Ok σ' ∧ s6.k ≤ s7.k ∧ k ≤ s7.k ∧
      (osQCallOf c lvl lv s6).1.map σ' =
        [W.lam lv cap cl, (W.lam lv cap cl)⁻¹, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
          σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv s6).2.map σ' = [W.r0, W.r1, W.batched, W.lam lv cap cl ^ lv.queries] ∧
      σ' (.n s7.batched) = W.batched ∧ σ' (.n s7.lamPow) = W.lam lv cap cl ^ lv.queries)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok6 := (ho1 C0 rd0 hH0).2.1
      have hk6 := (ho1 C0 rd0 hH0).2.2.2
      have hl5 : s5.lam < s5.k ∧ s5.lamInv < s5.k := osLam_lt s4
      have k56 := (ho1 C0 rd0 hH0).2.2.1
      have eA : ∀ C rd, H C rd → osQArgsV σ1 c lvl lv s6 =
          [W.lam lv cap cl, (W.lam lv cap cl)⁻¹, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
            σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
            σ (.n osQbp) * gen ^ lv.posOff] := fun C rd hH ↦ by
        obtain ⟨-, -, -, -, el5, eli5, -⟩ := (ho1 C rd hH).1.2
        simp only [osQArgsV, hfin, ↓reduceIte]
        rw [show s6.lam = s5.lam from rfl, show s6.lamInv = s5.lamInv from rfl, el5, eli5,
          ha1 _ (show 18 < k by omega), ha1 _ (show 24 < k by omega), ha1 _ (show 30 < k by omega),
          ha1 _ (show 32 < k by omega)]
      have h := osQueries_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s6) σ1 ok6.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.r0 W.r1 W.batched (W.lam lv cap cl ^ lv.queries) h3 hpo hh8
        (fun _ ↦ ⟨show s5.lam < s6.k by omega, show s5.lamInv < s6.k by omega⟩)
        (fun h ↦ absurd h hfin)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [eA C rd hH]; exact (hC C rd hH).q)
        (fun C rd hH ↦ by rw [ha1 _ (show 14 < k by omega)]; exact (hC C rd hH).roots)
      refine BlkA.monoH h fun C rd hH σ' _ ho ↦ ?_
      obtain ⟨hst, hargs, hrets, hbat, hlp⟩ := ho
      rw [eA C rd hH] at hargs
      exact ⟨hst.ok, hst.le, le_trans hk6 hst.le, hargs, hrets, hbat, hlp⟩)
    (fun σ' h ↦ h.2.1)
  -- the glue
  have b8 := BlkA.seqK b7 (fun σ' h ↦ h.2.2.2.1) (B := (osGlue lvl s7).1)
    (OutB := fun σ' ↦ (osGlue lvl s7).2.Ok σ' ∧ s7.k ≤ (osGlue lvl s7).2.k ∧
      k ≤ (osGlue lvl s7).2.k ∧ σ' (.n (osGlue lvl s7).2.claim) = W.claimOut lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok7, -, hk7, -, -, hbat7, hlp7⟩ := (ho1 C0 rd0 hH0).2
      obtain ⟨-, k45, -, -, hl5, hli5, -⟩ := (ho1 C0 rd0 hH0).1.1.2
      obtain ⟨-, -, -, -, -, -, hy0, -⟩ := (ho1 C0 rd0 hH0).1.1.1.1.1.2
      have ro := (ho1 C0 rd0 hH0).1.1.1.1.1.1.1
      have k24 := (ho1 C0 rd0 hH0).1.1.1.2.2.1
      have k56 := (ho1 C0 rd0 hH0).1.2.2.1
      have k67 := (ho1 C0 rd0 hH0).2.2.1
      have w2 : s2.ys.getD 0 0 < s2.k := (osCommit_word0_lt c lvl lv s1).2.2.1
      have hlt5 : s5.lam < s5.k ∧ s5.lamInv < s5.k := osLam_lt s4
      have hbl := osQueries_batched_lt c lvl lv s6
      have fq := osQueries_fields c lvl lv s6
      have e7l : s7.lam = s5.lam := fq.1
      have e7i : s7.lamInv = s5.lamInv := fq.2.1
      have e7y : s7.ys = s2.ys := fq.2.2.1
      have e7c : s7.claim = s1.claim := fq.2.2.2.1
      have h := osGlue_complete (H := H) (lvl := lvl) (st := s7) σ1 ok7.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by rw [e7l]; omega) (by rw [e7y]; omega)
        hbl.1 (by rw [e7i]; omega) hbl.2
        (fun C rd hH ↦ by
          obtain ⟨-, -, -, -, -, -, hlp⟩ := (ho1 C rd hH).2
          obtain ⟨-, -, -, -, el5, eli5, -⟩ := (ho1 C rd hH).1.1.2
          rw [e7l, e7i, el5, eli5, hlp, ha1 _ (show 28 < k by omega), ha1 _ (show 20 < k by omega),
            ha1 _ (show 22 < k by omega)]
          exact (hC C rd hH).glue)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hcl⟩ := ho
      rw [e7l, e7y, e7c, hl5, hy0, hbat7, hlp7, ro.claim] at hcl
      exact ⟨hst.ok, hst.le, le_trans hk7 hst.le, hcl⟩)
    (fun σ' h ↦ h.2.1)
  -- the level
  have eL : osLevel c lvl lv st = ((osRounds c.plan lv.foldsOff lv.folds st).1 ++
      (osCommit c lvl lv s1).1 ++
      [.call ("grind_check__L" ++ natStr queryGrind) ([s2.pow0, osTabs].map V.n) []] ++
      (osPositions c lvl lv s2).1 ++ (osLam s4).1 ++ (osHsMid lvl lv s5).1 ++
      (osQueries c lvl lv s6).1 ++ (osGlue lvl s7).1, (osGlue lvl s7).2) := by
    simp only [osLevel, hfin, ↓reduceIte]
    rfl
  have eQ : osPreQ c lvl lv st = s6 := by simp only [osPreQ, hfin, ↓reduceIte]; rfl
  rw [eL, eQ]
  refine BlkA.mono b8.agree fun σ' ho ↦ ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ro, -⟩, B2⟩, -⟩, B4⟩, B5⟩, -⟩, B7⟩, B8⟩, hag⟩ := ho
  obtain ⟨-, -, -, -, -, -, -, hsent2, hsz2, -⟩ := B2
  obtain ⟨-, -, -, -, -, -, hpa, hpr⟩ := B4
  obtain ⟨-, -, -, hF5, -, -, hcur5⟩ := B5
  obtain ⟨-, -, -, hargs, hrets, -⟩ := B7
  obtain ⟨ok8, -, hk8, hcl8⟩ := B8
  have fq := osQueries_fields c lvl lv s6
  refine ⟨⟨ok8, hk8, hag⟩, ?_, ?_, hcl8, hsz2, hsent2, hpa, hpr, hargs, hrets⟩
  · rw [← hF5]
    simp only [OsSt.F]
    rw [show (osGlue lvl s7).2.fs = s5.fs from fq.2.2.2.2.1]
  · rw [← hcur5]
    simp only [OsSt.cur]
    rw [show (osGlue lvl s7).2.cb = s5.cb from fq.2.2.2.2.2.1,
      show (osGlue lvl s7).2.co = s5.co from fq.2.2.2.2.2.2.1]

/-! ## The final level -/

theorem osFinalMsg_lt (c : OsCfg) (lv : OsLv) (s : OsSt) :
    (osFinalMsg c lv s).2.word0 < (osFinalMsg c lv s).2.k ∧
      (osFinalMsg c lv s).2.pow0 < (osFinalMsg c lv s).2.k ∧ s.k ≤ (osFinalMsg c lv s).2.k := by
  have := osCurS_k s
  simp only [osFinalMsg]
  omega

theorem osHsFinal_hs_lt (c : OsCfg) (lv : OsLv) (s : OsSt) :
    (osHsFinal c lv s).2.hs < (osHsFinal c lv s).2.k := by
  have := osHsCoefs_k osFmsg (s.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0
    (c.yrLen + lv.folds) 0 (s.k + 2)
  simp only [osHsFinal]
  omega

/-- The final level's data. -/
structure FinWD where
  rw : List E
  lane : List E
  nq : E
  r0 : E
  r1 : E
  batched : E
  pH : E

namespace FinWD

variable (c : OsCfg) (lv : OsLv) (cap : List E) (cl : E) (W : FinWD)

/-- The capacity and claim after the rounds. -/
def cap1 : List E := (roundsTr lv.folds cap cl W.rw).1
def cl1 : E := (roundsTr lv.folds cap cl W.rw).2

/-- The lane's and the query nonce's permutation. -/
def S2 : KeccakState := omState (W.cap1 lv cap cl) W.lane (some W.nq)

/-- The capacity after the squeezes. -/
def cap3 : List E := sqCapD (capOf (W.S2 lv cap cl)) (lv.squeezes - 1)

end FinWD

/-- **The final level's calls and memory** at its honest values. -/
structure FinC (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (cap : List E) (cl cur : E) (W : FinWD) : Prop where
  rounds : RoundsC C (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) lv.folds lv.foldsOff cap cl cur W.rw
  om : C ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1")
    (W.cap1 lv cap cl ++ [MidW.cur1 lv cur, σ (.n osFmsg)])
    (omRets (W.cap1 lv cap cl) W.lane (some W.nq) (MidW.cur1 lv cur) (c.yrLen + lv.folds + 1))
  g17 : C ("grind_check__L" ++ natStr queryGrind) [cellsOfState (W.S2 lv cap cl) false 1, σ (.n osTabs)] []
  lp : C (osPositionsName lv) (cellsOfState (W.S2 lv cap cl) false 0 :: capOf (W.S2 lv cap cl) ++
    [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)]) (W.cap3 lv cap cl)
  hs : ∀ j < c.yrLen + lv.folds, LoadHolds rd (σ (.n osFmsg)) j (W.lane.getD j 0) ∧
    LoadHolds rd W.pH j (W.lane.getD j 0 * word (hsScale lv.vanish (c.yrLog + 1) j 1) 0)
  q : C (osQueriesName c lvl lv)
    [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
      σ (.n osQbp) * gen ^ lv.posOff] [W.r0, W.r1, W.batched, 0 ^ lv.queries]
  roots : LoadHolds rd (σ (.n osRoots)) (2 * lvl) W.r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) W.r1

/-- **The final level, honestly**. -/
theorem osLevelFin_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hfin : lvl = c.yrLevel) (W : FinWD)
    (hr3 : 2 * (lv.foldsOff + lv.folds) < u128Bound) (hpo : lv.posOff < u128Bound)
    (h3 : 2 * lv.foldsOff < u128Bound) (hh8 : lvl * hsStride < u128Bound)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, H C rd → FinC C rd σ c lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W) :
    BlkA H σ st.k (osLevel c lvl lv st).2.k (osLevel c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osLevel c lvl lv st).2 ∧
      (osLevel c lvl lv st).2.F σ' = ⟨W.cap3 lv (st.fsv σ) (σ (.n st.claim)), []⟩ ∧
      (osLevel c lvl lv st).2.cur σ' = MidW.cur1 lv (st.cur σ) * gen ^ (c.yrLen + lv.folds + 1) ∧
      σ' (.n (osLevel c lvl lv st).2.claim) = W.cl1 lv (st.fsv σ) (σ (.n st.claim)) ∧
      σ' (.n (osPositions c lvl lv (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2.k) =
        gw (c.yrLen + lv.folds) ∧
      σ' (.n (osPreQ c lvl lv st).hs) = W.pH ∧
      (osPosCall c lv (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).1.map σ' =
        cellsOfState (W.S2 lv (st.fsv σ) (σ (.n st.claim))) false 0 ::
          capOf (W.S2 lv (st.fsv σ) (σ (.n st.claim))) ++
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osPosCall c lv (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2.map σ' =
        W.cap3 lv (st.fsv σ) (σ (.n st.claim)) ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).1.map σ' =
        [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).2.map σ' = [W.r0, W.r1, W.batched, 0 ^ lv.queries]) := by
  set cap := st.fsv σ with hcap
  set cl := σ (.n st.claim) with hcl
  set cur := st.cur σ with hcur
  set k := st.k with hk
  have k33 : 33 ≤ k := hsf.k
  set s1 := (osRounds c.plan lv.foldsOff lv.folds st).2 with hs1
  set s2 := (osFinalMsg c lv s1).2 with hs2
  set s4 := (osPositions c lvl lv s2).2 with hs4
  set s6 := (osHsFinal c lv s4).2 with hs6
  set s7 := (osQueries c lvl lv s6).2 with hs7
  have sf1 : s1.Sf := osRounds_sf _ _ _ _ hsf
  have ep1 : s1.pad = st.pad := osRounds_pad _ _ _ _
  have b1 : BlkA H σ k s1.k (osRounds c.plan lv.foldsOff lv.folds st).1 (fun σ' ↦
      RoundsOut σ σ' st s1 (roundsTr lv.folds cap cl W.rw) lv.folds ∧ AgreeBelow k σ σ') :=
    osRounds_completeA lv.folds lv.foldsOff st σ W.rw hsf.co hr3 hsf.below
      (fun C rd hH ↦ (hok C rd hH).mats) hsf.k hsf.fs fun C rd hH ↦ (hC C rd hH).rounds
  -- the lane
  have b2 := BlkA.seqK b1 (fun σ' h ↦ h.1.k) (B := (osFinalMsg c lv s1).1)
    (OutB := fun σ' ↦ s2.Ok σ' ∧ s1.k ≤ s2.k ∧ k ≤ s2.k ∧
      s2.F σ' = ⟨capOf (W.S2 lv cap cl), []⟩ ∧
      σ' (.n s2.word0) = cellsOfState (W.S2 lv cap cl) false 0 ∧
      σ' (.n s2.pow0) = cellsOfState (W.S2 lv cap cl) false 1 ∧
      s2.cur σ' = MidW.cur1 lv cur * gen ^ (c.yrLen + lv.folds + 1) ∧ s2.claim = s1.claim)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ro := (ho1 C0 rd0 hH0).1
      have ef : s1.fsv σ1 = W.cap1 lv cap cl := by
        have := congrArg Fs.cap ro.F
        simpa [OsSt.F, OsSt.fsv, FinWD.cap1] using this
      have ecur : s1.cur σ1 = MidW.cur1 lv cur := ro.cur
      have h := osFinalMsg_complete (H := H) (c := c) (lv := lv) (st := s1) σ1 sf1
        (fun C rd hH ↦ ⟨sf1, (ho1 C rd hH).1.mats, by rw [ep1]; exact ((hok C rd hH).agree ha1).pad⟩)
        W.lane W.nq (fun C rd hH ↦ by
          rw [ef, ecur, ha1 _ (show 12 < k by omega)]; exact (hC C rd hH).om)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hw, hp, hcur, hclm, -⟩ := ho
      rw [ef] at hF hw hp
      rw [ecur] at hcur
      exact ⟨hst.ok, hst.le, le_trans ro.k hst.le, hF, hw, hp, hcur, hclm⟩)
    (fun _ _ ↦ (osFinalMsg_lt c lv s1).2.2)
  -- the query grind
  have b3 := BlkA.seqK b2 (fun σ' h ↦ h.2.2.2.1) (B := [.call ("grind_check__L" ++ natStr queryGrind)
      ([s2.pow0, osTabs].map V.n) []])
    (OutB := fun _ ↦ True) (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have w := osFinalMsg_lt c lv s1
      have h := call0_blk (H := H) (σ := σ1) (k := s2.k)
        (f := "grind_check__L" ++ natStr queryGrind) (args := [s2.pow0, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact w.2.1
          · have := (ho1 C0 rd0 hH0).2.2.2.1; show 10 < s2.k; omega)
        fun C rd hH ↦ by
          simp only [List.map_cons, List.map_nil]
          rw [(ho1 C rd hH).2.2.2.2.2.2.1, ha1 _ (show 10 < k by omega)]
          exact (hC C rd hH).g17
      exact h.mono fun _ _ ↦ trivial) (fun _ _ ↦ le_rfl)
  -- the positions
  have b4 := BlkA.seqK b3 (fun σ' h ↦ h.1.2.2.2.1) (B := (osPositions c lvl lv s2).1)
    (OutB := fun σ' ↦ s4.Ok σ' ∧ s2.k ≤ s4.k ∧ k ≤ s4.k ∧ s4.F σ' = ⟨W.cap3 lv cap cl, []⟩ ∧
      s4.cur σ' = MidW.cur1 lv cur * gen ^ (c.yrLen + lv.folds + 1) ∧
      (osPosCall c lv s2).1.map σ' = cellsOfState (W.S2 lv cap cl) false 0 :: capOf (W.S2 lv cap cl) ++
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osPosCall c lv s2).2.map σ' = W.cap3 lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨ok2, -, hk2, hF2, hw2, -, hcur2, -⟩ := (ho1 C0 rd0 hH0).1.2
      have ef : s2.fsv σ1 = capOf (W.S2 lv cap cl) := by
        have := congrArg Fs.cap hF2
        simpa [OsSt.F, OsSt.fsv] using this
      have eq9 : σ1 (.n osTabs) = σ (.n osTabs) := ha1 _ (show 10 < k by omega)
      have eqp : σ1 (.n osQpos) = σ (.n osQpos) := ha1 _ (show 30 < k by omega)
      have eqb : σ1 (.n osQbp) = σ (.n osQbp) := ha1 _ (show 32 < k by omega)
      have hcl3 : (W.cap3 lv cap cl).length = 5 := sqCapD_length (by simp [capOf]) _
      have h := osPositions_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s2) σ1 ok2.sf
        (fun C rd hH ↦ (ho1 C rd hH).1.2.1) (osFinalMsg_lt c lv s1).1 hpo (W.cap3 lv cap cl) hcl3
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          rw [(ho1 C rd hH).1.2.2.2.2.2.1, ef, eqp, eqb, eq9]; exact (hC C rd hH).lp)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hcur, -, -, -, -, hargs, hrets⟩ := ho
      rw [hw2, ef, eqp, eqb, eq9] at hargs
      rw [hcur2] at hcur
      exact ⟨hst.ok, hst.le, le_trans hk2 hst.le, hF, hcur, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the lane normalized
  have b6 := BlkA.seqK b4 (fun σ' h ↦ h.2.2.2.1) (B := (osHsFinal c lv s4).1)
    (OutB := fun σ' ↦ s6.Ok σ' ∧ s4.k ≤ s6.k ∧ k ≤ s6.k ∧ σ' (.n s4.k) = gw (c.yrLen + lv.folds) ∧
      σ' (.n s6.hs) = W.pH)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok4 := (ho1 C0 rd0 hH0).2.1
      have hk4 := (ho1 C0 rd0 hH0).2.2.2.1
      have h := osHsFinal_complete (H := H) (c := c) (lv := lv) (st := s4) σ1 ok4.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.pH (fun j ↦ W.lane.getD j 0)
        (fun C rd hH j hj ↦ by rw [ha1 _ (show 12 < k by omega)]; exact (hC C rd hH).hs j hj)
      exact h.mono fun σ' ho ↦ ⟨ho.1.ok, ho.1.le, le_trans hk4 ho.1.le, ho.2.1, ho.2.2⟩)
    (fun σ' h ↦ h.2.1)
  -- the queries
  have b7 := BlkA.seqK b6 (fun σ' h ↦ h.2.2.2.1) (B := (osQueries c lvl lv s6).1)
    (OutB := fun σ' ↦ s7.Ok σ' ∧ s6.k ≤ s7.k ∧ k ≤ s7.k ∧
      (osQCallOf c lvl lv s6).1.map σ' =
        [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv s6).2.map σ' = [W.r0, W.r1, W.batched, 0 ^ lv.queries])
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have ok6 := (ho1 C0 rd0 hH0).2.1
      have hk6 := (ho1 C0 rd0 hH0).2.2.2.1
      have eA : ∀ C rd, H C rd → osQArgsV σ1 c lvl lv s6 =
          [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
            σ (.n osQbp) * gen ^ lv.posOff] := fun C rd hH ↦ by
        have hpH := (ho1 C rd hH).2.2.2.2.2
        simp only [osQArgsV, hfin, ↓reduceIte]
        rw [hpH, ha1 _ (show 18 < k by omega), ha1 _ (show 30 < k by omega), ha1 _ (show 32 < k by omega)]
      have h := osQueries_complete (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s6) σ1 ok6.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.r0 W.r1 W.batched (0 ^ lv.queries) h3 hpo hh8
        (fun h ↦ absurd hfin h) (fun _ ↦ osHsFinal_hs_lt c lv s4)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [eA C rd hH]; exact (hC C rd hH).q)
        (fun C rd hH ↦ by rw [ha1 _ (show 14 < k by omega)]; exact (hC C rd hH).roots)
      refine BlkA.monoH h fun C rd hH σ' _ ho ↦ ?_
      obtain ⟨hst, hargs, hrets, -⟩ := ho
      rw [eA C rd hH] at hargs
      exact ⟨hst.ok, hst.le, le_trans hk6 hst.le, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the level
  have eL : osLevel c lvl lv st = ((osRounds c.plan lv.foldsOff lv.folds st).1 ++
      (osFinalMsg c lv s1).1 ++
      [.call ("grind_check__L" ++ natStr queryGrind) ([s2.pow0, osTabs].map V.n) []] ++
      (osPositions c lvl lv s2).1 ++ (osHsFinal c lv s4).1 ++
      (osQueries c lvl lv s6).1, (osQueries c lvl lv s6).2) := by
    simp only [osLevel, hfin, ↓reduceIte, List.append_nil]
    rfl
  have eQ : osPreQ c lvl lv st = s6 := by simp only [osPreQ, hfin, ↓reduceIte]; rfl
  rw [eL, eQ]
  refine BlkA.mono b7.agree fun σ' ho ↦ ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨ro, -⟩, -⟩, -⟩, B4⟩, B6⟩, B7⟩, hag⟩ := ho
  obtain ⟨-, -, -, hF4, hcur4, hpa, hpr⟩ := B4
  obtain ⟨-, -, -, hsz6, hpH⟩ := B6
  obtain ⟨ok7, -, hk7, hargs, hrets⟩ := B7
  have fq := osQueries_fields c lvl lv s6
  refine ⟨⟨ok7, hk7, hag⟩, ?_, ?_, ?_, hsz6, hpH, hpa, hpr, hargs, hrets⟩
  · rw [← hF4]
    simp only [OsSt.F]
    rw [show (osQueries c lvl lv s6).2.fs = s4.fs from fq.2.2.2.2.1]
  · rw [← hcur4]
    simp only [OsSt.cur]
    rw [show (osQueries c lvl lv s6).2.cb = s4.cb from fq.2.2.2.2.2.1,
      show (osQueries c lvl lv s6).2.co = s4.co from fq.2.2.2.2.2.2.1]
  · rw [show (osQueries c lvl lv s6).2.claim = s1.claim from fq.2.2.2.1, ro.claim]
    rfl

/-! ## The levels -/

/-- **The levels in sequence**: each level from a start satisfying `Q` is a block whose outcome
gives the next level's `Q` and its own `R`; `Q` holds on any valuation agreeing below the state's
next free value. -/
theorem osLevels_complete (c : OsCfg) (Q : ℕ → OsSt → Val → Prop) (R : ℕ → Val → Prop)
    (hQ : ∀ lvl st σ σ', Q lvl st σ → AgreeBelow st.k σ σ' → Q lvl st σ') :
    ∀ (lvs : List OsLv) (lvl : ℕ),
      (∀ i (h : i < lvs.length) st σ, Q (lvl + i) st σ →
        BlkA H σ st.k (osLevel c (lvl + i) lvs[i] st).2.k (osLevel c (lvl + i) lvs[i] st).1
          (fun σ' ↦ st.k ≤ (osLevel c (lvl + i) lvs[i] st).2.k ∧
            Q (lvl + i + 1) (osLevel c (lvl + i) lvs[i] st).2 σ' ∧ R (lvl + i) σ')) →
      ∀ st σ, Q lvl st σ →
        BlkA H σ st.k (osLevels c lvl lvs st).2.k (osLevels c lvl lvs st).1
          (fun σ' ↦ st.k ≤ (osLevels c lvl lvs st).2.k ∧ Q (lvl + lvs.length) (osLevels c lvl lvs st).2 σ' ∧
            ∀ i < lvs.length, R (lvl + i) σ')
  | [], lvl, _, st, σ, hq => by
    refine BlkA.nil fun σ' ha ↦ ⟨le_rfl, ?_, fun i hi ↦ absurd hi (by simp)⟩
    exact hQ lvl st σ σ' hq ha
  | lv :: rest, lvl, hstep, st, σ, hq => by
    have e : osLevels c lvl (lv :: rest) st = ((osLevel c lvl lv st).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).1,
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2) := rfl
    rw [e]
    have h0 := hstep 0 (by simp) st σ hq
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have ih := osLevels_complete c Q R hQ rest (lvl + 1) fun i hi st' σ' hq' ↦ by
      have := hstep (i + 1) (by simp; omega) st' σ' (by rw [← Nat.add_assoc, Nat.add_right_comm]; exact hq')
      simp only [List.getElem_cons_succ] at this
      rw [show lvl + (i + 1) = lvl + 1 + i by omega] at this
      exact this
    refine BlkA.mono (BlkA.seqK h0 (fun σ' h ↦ h.1) (fun σ1 _ ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦
      ih (osLevel c lvl lv st).2 σ1 (ho1 C0 rd0 hH0).2.1) (fun σ' h ↦ h.1)) fun σ' ⟨ha, hb⟩ ↦ ?_
    refine ⟨le_trans ha.1 hb.1, by rw [List.length_cons, show lvl + (rest.length + 1) =
      lvl + 1 + rest.length by omega]; exact hb.2.1, fun i hi ↦ ?_⟩
    rcases i with _ | i
    · simpa using ha.2.2
    · rw [show lvl + (i + 1) = lvl + 1 + i by omega]
      exact hb.2.2 i (by simp at hi; omega)

end
end LeanVM.Guest.B1.Whir
