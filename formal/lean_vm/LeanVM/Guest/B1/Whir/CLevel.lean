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

A level is its `level_rate` block (`osRates`), its rounds (`osRounds`, inline grinds on `rd0`'s
words, `RoundsH`), its message (a non-final level's next commitment `osCommit`, the final level's
lane `osFinalMsg`), the query grind (`osQGrind`), the positions (`osPositions`), a non-final level's
batching challenge (`osLam`), its high part (`osHsMid`, `osHsFinal`), the queries (`osQueries`) and a
non-final level's glue (`osGlue`); `BlkA.seqK` composes them.

* `MidW`: a non-final level's data (round words, the next root's cells and high part, the
  out-of-domain values, the nonces, the cap's root cells, the batch, the pointers of `sent` and the
  squeeze run); its honest values (`cap1`, `cl1`, `cur1`, `S2`, `cap3`, `SL`, `lam`, `claimOut`).
  `lpArgsV`: `level_positions`' honest arguments.
* `MidC C rd σ …`: the level's calls and memory at those values
  on the grinds' table; `osLevelMid_complete`: the level's outcome, the positions' and queries'
  dispatches' values and its calls' values (`cvMid`).
* `FinWD`, `FinC`, `cvFin`, `osLevelFin_complete`: the same at the final level.
* `osRndSt`, `osPosStL`: the states after the rounds and entering the positions; `RtVals`,
  `rtVals_new`: the levels' `level_rate` values in `rts`; `osLevels_complete`: the levels in sequence.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- **Two blocks in sequence**, their bounds read off their outcomes. -/
theorem BlkA.seqK {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (hA : BlkA M H σ k k1 A OutA) (hkA : ∀ σ', OutA σ' → k ≤ k1)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → (∀ C rd, HM M H C rd → OutA σ1) → BlkA M H σ1 k1 k2 B OutB)
    (hkB : ∀ σ', OutB σ' → k1 ≤ k2) :
    BlkA M H σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  by_cases hne : ∃ C rd, H C rd
  swap
  · exact ⟨fun _ ↦ 0, fun C rd hH ↦ absurd ⟨C, rd, hH⟩ hne⟩
  obtain ⟨C0, rd0, hH0⟩ := hne
  obtain ⟨fA, hfA⟩ := hA
  have hO1 := (hfA C0 rd0 hH0 (fill σ k k1 fA) (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.2
  have h1 := hkA _ hO1
  obtain ⟨fB, hfB⟩ := hB (fill σ k k1 fA) (agree_fill _ _ _ _) (HM.indep fun C rd hH ↦
    (hfA C rd hH _ (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.2)
  have h2 := hkB _ (hfB C0 rd0 hH0 (fill (fill σ k k1 fA) k1 k2 fB) (agree_fill _ _ _ _)
    (range_fill _ _ _ _)).2.2
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

/-- `level_positions`' honest arguments: the first word, the capacity, the level's positions and
window pointers, the table, `g^squeezes`. -/
def lpArgsV (σ : Val) (lv : OsLv) (w0 : E) (cap : List E) : List E :=
  w0 :: cap ++ [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs),
    gen ^ lv.squeezes]

/-- **A non-final level's calls and memory** at its honest values (the fixed buffers' pointers
read from `σ`), the grinds' words passing. -/
structure MidC (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (cap : List E) (cl cur : E) (W : MidW) : Prop where
  rounds : RoundsH rd (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) lv.folds lv.foldsOff cap cl cur W.rw
  om : C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1")
    (W.cap1 lv cap cl ++ [MidW.cur1 lv cur, W.pS])
    (omRets (W.cap1 lv cap cl) W.msg (some W.n1) (MidW.cur1 lv cur) (2 + lv.folds + 1))
  g0 : ((cellsOfState (omState (W.cap1 lv cap cl) W.msg (some W.n1)) false 1).limb 0).lane.toNat %
    2 ^ levelOodGrind = 0
  low : WinTabs rd (σ (.n osTabs))
  sent : LoadHolds rd W.pS 0 W.x0 ∧ LoadHolds rd W.pS 1 W.x1 ∧
    LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) W.x0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) W.x1
  spf : C ("squeeze_point_from__L" ++ natStr lv.logCols)
    (capOf (omState (W.cap1 lv cap cl) W.msg (some W.n1)) ++
      [cellsOfState (omState (W.cap1 lv cap cl) W.msg (some W.n1)) false 0,
        σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)])
    (spfRets (W.cap1 lv cap cl) W.msg W.n1 lv.logCols)
  ys : ReadsAt rd (MidW.cur1 lv cur * gen ^ (2 + lv.folds + 1)) [W.y0, W.nq]
  g17 : ((rdCell (W.S2 lv cap cl) 1).limb 0).lane.toNat % 2 ^ queryGrind = 0
  lp : C (osPositionsName lv) (lpArgsV σ lv (rdCell (W.S2 lv cap cl) 0) (capOf (W.S2 lv cap cl)))
    (W.cap3 lv cap cl)
  hs : ∀ j < lv.folds, LoadHolds rd W.pS (2 + j) (W.high.getD j 0) ∧
    LoadHolds rd (σ (.n osHs)) (lvl * hsStride + j) (W.high.getD j 0 *
      word (hsScale lv.vanish lv.highBits j (vanishInv (lv.vanish + lv.logCols))) 0)
  q : C (osQueriesName c lvl lv)
    [W.lam lv cap cl, lamInvOf (W.lam lv cap cl), σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
      σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
      σ (.n osQbp) * gen ^ lv.posOff] [W.r0, W.r1, W.batched, W.lam lv cap cl ^ lv.queries]
  roots : LoadHolds rd (σ (.n osRoots)) (2 * lvl) W.r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) W.r1
  glue : LoadHolds rd (σ (.n osOodSc)) (lvl + 1) (W.lam lv cap cl) ∧
    LoadHolds rd (σ (.n osBetas)) lvl (W.lam lv cap cl * W.lam lv cap cl *
      W.lam lv cap cl ^ lv.queries) ∧
    LoadHolds rd (σ (.n osMus)) lvl (lamInvOf (W.lam lv cap cl))

/-! ## The levels' calls -/

theorem osPositions_calls (c : OsCfg) (lvl : ℕ) (s : OsSt) :
    (osPositions c lvl s).1.filterMap callVs = [.n osRate :: ((osPosCall s).1 ++ (osPosCall s).2)] := rfl

theorem osQueries_calls (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).1.filterMap callVs =
      [.n osRate :: ((osQCallOf c lvl lv s).1 ++ (osQCallOf c lvl lv s).2)] := by
  unfold osQueries osQCallOf
  dsimp only
  split_ifs <;> simp only [calls_append, osMatS_calls, List.nil_append] <;> rfl

/-- **A non-final level's calls' values**: the message's (`commitCV`), `level_positions`', `is_zero`
of `λ` and `level_queries`', at the rate's selector `x`, the pointers of `ood_z` (`oz`),
`round_coefs` (`cf`) and `level_hs` (`hp`), the positions and windows (`qp`, `qb`), the table `tb`. -/
def cvMid (lvl : ℕ) (lv : OsLv) (cap : List E) (cl cur : E) (W : MidW) (x oz cf hp qp qb tb : E) :
    List (List E) :=
  commitCV (W.cap1 lv cap cl) W.msg W.n1 (MidW.cur1 lv cur) W.pS (oz * gen ^ ((lvl + 1) * ligColsCap))
      lv.folds lv.logCols ++
    [x :: ((rdCell (W.S2 lv cap cl) 0 :: capOf (W.S2 lv cap cl) ++
        [qp * gen ^ lv.posOff, qb * gen ^ lv.posOff, tb, gen ^ lv.squeezes]) ++ W.cap3 lv cap cl),
      [W.lam lv cap cl, zeroOf (W.lam lv cap cl)],
      x :: ([W.lam lv cap cl, lamInvOf (W.lam lv cap cl), cf * gen ^ (2 * lv.foldsOff),
        hp * gen ^ (lvl * hsStride), qp * gen ^ lv.posOff, qb * gen ^ lv.posOff] ++
        [W.r0, W.r1, W.batched, W.lam lv cap cl ^ lv.queries])]

/-! ## The level's states -/

/-- The state after a level's rounds. -/
def osRndSt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : OsSt :=
  (osRounds true lv.foldsOff lv.folds (osRates c lvl st).2).2

/-- The state entering a level's positions: after its message and the query grind. -/
def osPosStL (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : OsSt :=
  (osQGrind (if lvl = c.yrLevel then osFinalMsg c lv (osRndSt c lvl lv st)
    else osCommit c lvl lv (osRndSt c lvl lv st)).2).2

theorem osRndSt_fields (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    (osRndSt c lvl lv st).rts = (osRates c lvl st).2.rts ∧ (osRndSt c lvl lv st).lp = (osRates c lvl st).2.lp ∧
      (osRndSt c lvl lv st).lw = (osRates c lvl st).2.lw := by
  obtain ⟨_, _, _, _, h⟩ := osRounds_snd true lv.foldsOff lv.folds (osRates c lvl st).2
  unfold osRndSt; rw [h]; exact ⟨rfl, rfl, rfl⟩

/-- A state with a larger next free value keeps the invariants. -/
theorem OsSt.Ok.withK {σ : Val} {s : OsSt} (h : s.Ok σ) {k' : ℕ} (hk : s.k ≤ k') :
    ({ s with k := k' } : OsSt).Ok σ :=
  ⟨⟨h.sf.fs, ⟨fun f hf ↦ lt_of_lt_of_le (h.sf.below.fs f hf) hk, lt_of_lt_of_le h.sf.below.cb hk,
    lt_of_lt_of_le h.sf.below.claim hk, fun m hm ↦ by
      obtain ⟨a1, a2, a3⟩ := h.sf.below.mats m hm
      exact ⟨lt_of_lt_of_le a1 hk, lt_of_lt_of_le a2 hk, lt_of_lt_of_le a3 hk⟩⟩, h.sf.co,
    fun p hp ↦ lt_of_lt_of_le (h.sf.padB p hp) hk, le_trans h.sf.k hk⟩, h.mats, h.pad⟩

theorem osSqCell_of {s : OsSt} {r : List (List ℕ)} {e : List ℕ} (h : s.rts = r ++ [e]) :
    osSqCell s = e.getD 1 0 := by
  simp [osSqCell, h]

theorem gcLen_q : 3 ≤ gcLen queryGrind := by unfold gcLen; omega

/-- **The query grind, inline**, at a state holding its invariants: the grinds' word passing. -/
theorem osQGrind_complete {s : OsSt} (σ : Val) (rd0 : Reader) (hl0 : LowDef 11 rd0) (hok : ∀ C rd, HM M H C rd → s.Ok σ)
    (hpw : s.pow0 < s.k) (hlow : ((σ (.n s.pow0)).limb 0).lane.toNat % 2 ^ queryGrind = 0)
    (htab : ∀ C rd, H C rd → LowAgree rd rd0) (htW : ∀ C rd, HM M H C rd → WinTabs rd (σ (.n osTabs))) :
    BlkA M H σ s.k (osQGrind s).2.k (osQGrind s).1 (fun σ' ↦ OsStep σ σ' s (osQGrind s).2) := by
  refine BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ ?_
  have k43 := (hok C0 rd1 hH0).sf.k
  have hg := gcLen_q
  have e3 : (osQGrind s).2.k = s.k + (gcLen queryGrind - 2) := by
    show s.k + gcLen queryGrind - 2 = _; omega
  rw [e3]
  refine BlkA.monoH (gc_blk (M := M) (H := H) (σ := σ) (b := queryGrind) (o := s.k) (wi := s.pow0) (ti := osTabs)
    rd0 hl0 (by decide) hpw (by show 10 < s.k; omega) hlow htab htW).agree fun C rd hH σ' _ ⟨_, ha⟩ ↦ ?_
  exact ⟨by
    have := ((hok C rd hH).agree ha).withK (k' := s.k + gcLen queryGrind - 2) (by omega)
    exact this, by show s.k ≤ s.k + gcLen queryGrind - 2; omega, ha⟩

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
  set g := cu.2.2.k + 8 + gcLen levelOodGrind - 2 with hg
  set o0 := osMatS c.plan osOodz ((lvl + 1) * ligColsCap) { cu.2.2 with k := g + 2 } with ho0
  have a : s.k + 2 ≤ cu.2.2.k := osCurS_k { s with k := s.k + 2 }
  have b : g + 2 ≤ o0.2.2.k := osMatS_k c.plan osOodz ((lvl + 1) * ligColsCap) { cu.2.2 with k := g + 2 }
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
    (hok : ∀ C rd, HM M H C rd → st.Ok σ) (hfin : lvl ≠ c.yrLevel) (W : MidW) (rd0 : Reader)
    (hl0 : LowDef 11 rd0) (hrwl : W.rw.length = 5 * lv.folds) (hpad : ∃ p, st.pad = some p)
    (hco : st.co + 5 * lv.folds < u128Bound)
    (hoff : (lvl + 1) * ligColsCap < u128Bound) (hpo : lv.posOff < u128Bound)
    (hsq : lv.squeezes < u128Bound)
    (h3 : 2 * lv.foldsOff < u128Bound) (hh8 : lvl * hsStride < u128Bound)
    (hiz : IsZeroC (HM M H))
    (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, HM M H C rd → MidC C rd σ c lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W)
    (hag0 : ∀ C rd, H C rd → LowAgree rd rd0) :
    BlkA M H σ st.k (osLevel c lvl lv st).2.k (osLevel c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osLevel c lvl lv st).2 ∧
      (osLevel c lvl lv st).2.F σ' = ⟨capOf (W.SL lv (st.fsv σ) (σ (.n st.claim))), []⟩ ∧
      (osLevel c lvl lv st).2.cur σ' = MidW.cur1 lv (st.cur σ) * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      σ' (.n (osLevel c lvl lv st).2.claim) = W.claimOut lv (st.fsv σ) (σ (.n st.claim)) ∧
      (∀ j < 4, σ' (.n (st.k + 1 + 2 * j + 1)) = gw ((osRateVals lv).getD j 0)) ∧
      σ' (.n (osRndSt c lvl lv st).k) = gw (2 + lv.folds) ∧
      σ' (.n ((osRndSt c lvl lv st).k + 1)) = W.pS ∧
      (osPosCall (osPosStL c lvl lv st)).1.map σ' =
        lpArgsV σ lv (rdCell (W.S2 lv (st.fsv σ) (σ (.n st.claim))) 0)
          (capOf (W.S2 lv (st.fsv σ) (σ (.n st.claim)))) ∧
      (osPosCall (osPosStL c lvl lv st)).2.map σ' = W.cap3 lv (st.fsv σ) (σ (.n st.claim)) ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).1.map σ' =
        [W.lam lv (st.fsv σ) (σ (.n st.claim)), lamInvOf (W.lam lv (st.fsv σ) (σ (.n st.claim))),
          σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), σ (.n osHs) * gen ^ (lvl * hsStride),
          σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).2.map σ' =
        [W.r0, W.r1, W.batched, W.lam lv (st.fsv σ) (σ (.n st.claim)) ^ lv.queries] ∧
      st.k + 9 ≤ (osLevel c lvl lv st).2.k ∧
      cvOf (osLevel c lvl lv st).1 σ' = cvMid lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W
        (σ (.n osRate)) (σ (.n osOodz)) (σ (.n osCoefs)) (σ (.n osHs)) (σ (.n osQpos)) (σ (.n osQbp))
        (σ (.n osTabs))) := by
  set cap := st.fsv σ with hcap
  set cl := σ (.n st.claim) with hcl
  set cur := st.cur σ with hcur
  set k := st.k with hk
  have k43 : 43 ≤ k := hsf.k
  set s0 := (osRates c lvl st).2 with hs0
  set s1 := (osRounds true lv.foldsOff lv.folds s0).2 with hs1
  set s2 := (osCommit c lvl lv s1).2 with hs2
  set s3 := (osQGrind s2).2 with hs3
  set s4 := (osPositions c lvl s3).2 with hs4
  set s5 := (osLam s4).2 with hs5
  set s6 := (osHsMid lvl lv s5).2 with hs6
  set s7 := (osQueries c lvl lv s6).2 with hs7
  have k0 : s0.k = k + 1 + 8 + 4 * (ligNRates - 1) + 2 := rfl
  have hn4 : ligNRates = 4 := rfl
  have k01 : s0.k ≤ s1.k := osRounds_k _ _ _ _ (by omega)
  have k12 : s1.k + 2 ≤ s2.k := osCommit_k2 c lvl lv s1
  have k23 : s2.k + 1 ≤ s3.k := by have := gcLen_q; show s2.k + 1 ≤ s2.k + gcLen queryGrind - 2; omega
  have hlp0 : s0.lp + 2 = s0.k := rfl
  have hlw0 : s0.lw + 1 = s0.k := rfl
  obtain ⟨hrts1, hlp1, hlw1⟩ := osRndSt_fields c lvl lv st
  have e3lp : s3.lp = s0.lp := hlp1
  have e3lw : s3.lw = s0.lw := hlw1
  have e3rts : s3.rts = st.rts ++ [[k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1,
      k + 1 + 2 * 3 + 1]] := hrts1
  have hsqc : osSqCell s3 = k + 1 + 2 * 1 + 1 := osSqCell_of e3rts
  have hpo' : gw lv.posOff = gen ^ lv.posOff := gw_eq hpo
  -- the rates
  have b0 := osRates_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := st) σ hsf hok hrate
  -- the rounds
  have b1 := BlkA.seqK b0 (fun σ' h ↦ h.1.le) (B := (osRounds true lv.foldsOff lv.folds s0).1)
    (OutB := fun σ' ↦ OsStep σ σ' st s1 ∧ s1.F σ' = ⟨(roundsTr lv.folds cap cl W.rw).1, []⟩ ∧
      s1.cur σ' = cur * gen ^ (5 * lv.folds) ∧ σ' (.n s1.claim) = (roundsTr lv.folds cap cl W.rw).2 ∧
      s1.co = st.co + 5 * lv.folds ∧ s1.pad = st.pad)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok0 := (ho1 C0 rd1 hH0).1.ok
      obtain ⟨ef0, -, ec0, ecur0⟩ := OsSt.agree hsf.below ha1
      have ef0' : s0.fsv σ1 = cap := ef0
      have ec0' : σ1 (.n s0.claim) = cl := ec0
      have ecur0' : s0.cur σ1 = cur := ecur0
      have h := osRounds_completeA (M := M) (H := H) rd0 hl0 true lv.folds lv.foldsOff s0 σ1 W.rw ok0.sf
        (by show st.co + 5 * lv.folds < u128Bound; omega) hpad (fun C rd hH ↦ (ho1 C rd hH).1.ok) hrwl
        (fun C rd hH ↦ by
          rw [ef0', ec0', ecur0', ha1 osFch (by show 16 < k; omega), ha1 osCoefs (by show 18 < k; omega),
            ha1 osTabs (by show 10 < k; omega)]
          exact (hC C rd hH).rounds) hag0
      rw [ef0', ec0'] at h
      refine BlkA.monoH h fun C rd hH σ' _ ⟨ro, hag⟩ ↦ ?_
      have hag' : AgreeBelow k σ σ' := fun i hi ↦ (hag i (by omega)).trans (ha1 i hi)
      have hk1 : k ≤ s1.k := by omega
      refine ⟨osStep_of hsf (hok C rd hH) hag' hk1 ro.fs ro.below.fs ro.below.cb ro.below.claim
        (by rw [ro.co]; show st.co + 5 * lv.folds < u128Bound; omega) ro.pad ro.mats ro.below.mats,
        ro.F, by rw [ro.cur, ecur0'], ro.claim, ro.co, ro.pad⟩)
    (fun _ _ ↦ k01)
  -- the message
  have b2 := BlkA.seqK b1 (fun _ _ ↦ by show st.k ≤ s1.k; omega) (B := (osCommit c lvl lv s1).1)
    (OutB := fun σ' ↦ s2.Ok σ' ∧ s1.k ≤ s2.k ∧ k ≤ s2.k ∧ s2.F σ' = ⟨capOf (W.S2 lv cap cl), []⟩ ∧
      σ' (.n s2.word0) = rdCell (W.S2 lv cap cl) 0 ∧ σ' (.n s2.pow0) = rdCell (W.S2 lv cap cl) 1 ∧
      σ' (.n (s2.ys.getD 0 0)) = W.y0 ∧
      σ' (.n s2.sent) = W.pS ∧ σ' (.n s1.k) = gw (2 + lv.folds) ∧
      s2.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧ s2.claim = s1.claim ∧
      cvOf (osCommit c lvl lv s1).1 σ' = commitCV (W.cap1 lv cap cl) W.msg W.n1 (MidW.cur1 lv cur) W.pS
        (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)) lv.folds lv.logCols)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      obtain ⟨st1, hF1, hcur1, -, -, -⟩ := (ho1 C0 rd1 hH0).2
      have sf1 : s1.Sf := st1.ok.sf
      have ef : s1.fsv σ1 = W.cap1 lv cap cl := by
        have := congrArg Fs.cap hF1
        simpa [OsSt.F, OsSt.fsv, MidW.cap1] using this
      have ecur : s1.cur σ1 = MidW.cur1 lv cur := hcur1
      have hroots : σ1 (.n osRoots) = σ (.n osRoots) := ha1 _ (by show 14 < k; omega)
      have hoodz : σ1 (.n osOodz) = σ (.n osOodz) := ha1 _ (by show 26 < k; omega)
      have h := osCommit_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s1) σ1 sf1
        (fun C rd hH ↦ (ho1 C rd hH).2.1.ok)
        W.x0 W.x1 W.high W.n1 W.y0 W.nq W.pS hoff
        (fun C rd hH ↦ by rw [ef, ecur]; exact (hC C rd hH).om) rd0 hl0
        (by rw [ef]; exact (hC C0 rd1 hH0).g0)
        hag0 (fun C rd hH ↦ by rw [ha1 _ (show 10 < k by omega)]; exact (hC C rd hH).low)
        (fun C rd hH ↦ by rw [hroots]; exact (hC C rd hH).sent)
        (fun C rd hH ↦ by rw [ef, hoodz]; exact (hC C rd hH).spf)
        (fun C rd hH ↦ by rw [ecur]; exact (hC C rd hH).ys)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hw, hp, -, hy0, hsent, hsz, hcur, hclm, hcv⟩ := ho
      rw [ef] at hF hw hp
      rw [ecur] at hcur
      rw [ef, ecur, hoodz] at hcv
      exact ⟨hst.ok, hst.le, by show st.k ≤ s2.k; omega, hF, hw, hp, hy0, hsent, hsz, hcur, hclm, hcv⟩)
    (fun _ _ ↦ by show s1.k ≤ s2.k; omega)
  -- the query grind
  have b3 := BlkA.seqK b2 (fun _ _ ↦ by show st.k ≤ s2.k; omega) (B := (osQGrind s2).1)
    (OutB := fun σ' ↦ s3.Ok σ' ∧ s2.k ≤ s3.k) (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have w := osCommit_word0_lt c lvl lv s1
      have h := osQGrind_complete (M := M) (H := H) (s := s2) σ1 rd0 hl0 (fun C rd hH ↦ (ho1 C rd hH).2.1) w.2.1
        (by rw [(ho1 C0 rd1 hH0).2.2.2.2.2.2.1]; exact (hC C0 rd1 hH0).g17)
        hag0 (fun C rd hH ↦ by rw [ha1 _ (show 10 < k by omega)]; exact (hC C rd hH).low)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le⟩)
    (fun _ _ ↦ by show s2.k ≤ s3.k; omega)
  -- the positions
  have b4 := BlkA.seqK b3 (fun _ _ ↦ by show st.k ≤ s3.k; omega) (B := (osPositions c lvl s3).1)
    (OutB := fun σ' ↦ s4.Ok σ' ∧ s3.k ≤ s4.k ∧ s4.F σ' = ⟨W.cap3 lv cap cl, []⟩ ∧
      s4.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      (osPosCall s3).1.map σ' = lpArgsV σ lv (rdCell (W.S2 lv cap cl) 0) (capOf (W.S2 lv cap cl)) ∧
      (osPosCall s3).2.map σ' = W.cap3 lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok3 := (ho1 C0 rd1 hH0).2.1
      have w1 : s2.word0 < s2.k := (osCommit_word0_lt c lvl lv s1).1
      have hcl3 : (W.cap3 lv cap cl).length = 5 := sqCapD_length (by simp [capOf]) _
      have eA : ∀ C rd, HM M H C rd → (osPosCall s3).1.map σ1 =
          lpArgsV σ lv (rdCell (W.S2 lv cap cl) 0) (capOf (W.S2 lv cap cl)) := fun C rd hH ↦ by
        obtain ⟨⟨⟨⟨-, hrv, hlpv, hlwv⟩, -⟩, -, -, -, hF2, hw2, -⟩, -⟩ := ho1 C rd hH
        have ef : s3.fsv σ1 = capOf (W.S2 lv cap cl) := by
          show s2.fsv σ1 = _
          have := congrArg Fs.cap hF2
          simpa [OsSt.F, OsSt.fsv] using this
        have hsv := hrv 1 (by omega)
        rw [osPosCall_map, hsqc, ef, show s3.word0 = s2.word0 from rfl, hw2, e3lp, e3lw, hlpv, hlwv, hsv,
          ha1 _ (show 10 < k by omega), hpo']
        simp only [lpArgsV, osRateVals, List.getD_cons_succ, List.getD_cons_zero]
        rw [gw_eq hsq]
      have h := osPositions_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s3) σ1 ok3.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by show s2.word0 < s3.k; omega)
        (by rw [e3lp]; omega) (by rw [e3lw]; omega) (by rw [hsqc]; omega) (W.cap3 lv cap cl) hcl3
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [eA C rd hH]; exact (hC C rd hH).lp)
      refine BlkA.monoH h fun C rd hH σ' _ ho ↦ ?_
      obtain ⟨hst, hF, hcur, hargs, hrets⟩ := ho
      rw [eA C rd hH] at hargs
      have hcur2 := (ho1 C rd hH).1.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨hst.ok, hst.le, hF, by rw [hcur]; exact hcur2, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the batching challenge
  have b5 := BlkA.seqK b4 (fun σ' h ↦ by have := h.2.2.1; show st.k ≤ s4.k; omega) (B := (osLam s4).1)
    (OutB := fun σ' ↦ s5.Ok σ' ∧ s4.k ≤ s5.k ∧ s5.F σ' = ⟨capOf (W.SL lv cap cl), []⟩ ∧
      σ' (.n s5.lam) = W.lam lv cap cl ∧ σ' (.n s5.lamInv) = lamInvOf (W.lam lv cap cl) ∧
      s5.cur σ' = MidW.cur1 lv cur * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      cvOf (osLam s4).1 σ' = [[W.lam lv cap cl, zeroOf (W.lam lv cap cl)]])
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      obtain ⟨ok4, -, hF4, hcur4, -⟩ := (ho1 C0 rd1 hH0).2
      have ef : s4.fsv σ1 = W.cap3 lv cap cl := by
        have := congrArg Fs.cap hF4
        simpa [OsSt.F, OsSt.fsv] using this
      have hco4 : s4.co = 2 := (osCommit_word0_lt c lvl lv s1).2.2.2
      have h := osLam_complete (M := M) (H := H) (st := s4) σ1 ok4.sf (fun C rd hH ↦ (ho1 C rd hH).2.1)
        (by rw [hco4]; unfold u128Bound; omega) hiz
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hl, hli, hcur, -, -, -, -, hcv⟩ := ho
      rw [ef] at hF hl hli hcv
      rw [hcur4] at hcur
      exact ⟨hst.ok, hst.le, hF, hl, hli, hcur, hcv⟩)
    (fun σ' h ↦ h.2.1)
  -- the high part
  have b6 := BlkA.seqK b5 (fun σ' h ↦ by
      have := h.2.2.1; have := h.1.2.2.1; show st.k ≤ s5.k; omega) (B := (osHsMid lvl lv s5).1)
    (OutB := fun σ' ↦ s6.Ok σ' ∧ s5.k ≤ s6.k)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok5 := (ho1 C0 rd1 hH0).2.1
      have k34 := (ho1 C0 rd1 hH0).1.2.2.1
      have k45 := (ho1 C0 rd1 hH0).2.2.1
      have hs5 : s5.sent < s5.k := by show s1.k + 1 < s5.k; omega
      have h := osHsMid_complete (M := M) (H := H) (lvl := lvl) (lv := lv) (st := s5) σ1 ok5.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) hs5 (fun j ↦ W.high.getD j 0)
        (fun C rd hH j hj ↦ by
          rw [show s5.sent = s2.sent from rfl, (ho1 C rd hH).1.1.1.2.2.2.2.2.2.2.2.1,
            ha1 _ (show 24 < k by omega)]
          exact (hC C rd hH).hs j hj)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le⟩)
    (fun σ' h ↦ h.2)
  -- the queries
  have b7 := BlkA.seqK b6 (fun σ' h ↦ by
      have := h.2.2; have := h.1.2.2.1; have := h.1.1.2.2.1; show st.k ≤ s6.k; omega) (B := (osQueries c lvl lv s6).1)
    (OutB := fun σ' ↦ s7.Ok σ' ∧ s6.k ≤ s7.k ∧
      (osQCallOf c lvl lv s6).1.map σ' =
        [W.lam lv cap cl, lamInvOf (W.lam lv cap cl), σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
          σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv s6).2.map σ' = [W.r0, W.r1, W.batched, W.lam lv cap cl ^ lv.queries] ∧
      σ' (.n s7.batched) = W.batched ∧ σ' (.n s7.lamPow) = W.lam lv cap cl ^ lv.queries)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok6 := (ho1 C0 rd1 hH0).2.1
      have k56 := (ho1 C0 rd1 hH0).2.2
      have k45 := (ho1 C0 rd1 hH0).1.2.2.1
      have k34 := (ho1 C0 rd1 hH0).1.1.2.2.1
      have hl5 : s5.lam < s5.k ∧ s5.lamInv < s5.k := osLam_lt s4
      have eA : ∀ C rd, HM M H C rd → osQArgsV σ1 c lvl lv s6 =
          [W.lam lv cap cl, lamInvOf (W.lam lv cap cl), σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
            σ (.n osHs) * gen ^ (lvl * hsStride), σ (.n osQpos) * gen ^ lv.posOff,
            σ (.n osQbp) * gen ^ lv.posOff] := fun C rd hH ↦ by
        obtain ⟨-, -, -, el5, eli5, -⟩ := (ho1 C rd hH).1.2
        obtain ⟨-, -, hlpv, hlwv⟩ := (ho1 C rd hH).1.1.1.1.1.1
        simp only [osQArgsV, hfin, ↓reduceIte]
        rw [show s6.lam = s5.lam from rfl, show s6.lamInv = s5.lamInv from rfl, el5, eli5,
          ha1 _ (show 18 < k by omega), ha1 _ (show 24 < k by omega), show s6.lp = s0.lp from e3lp,
          show s6.lw = s0.lw from e3lw, hlpv, hlwv, hpo']
      have h := osQueries_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s6) σ1 ok6.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.r0 W.r1 W.batched (W.lam lv cap cl ^ lv.queries) h3 hh8
        (by show s3.lp < s6.k; omega) (by show s3.lw < s6.k; omega)
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
      exact ⟨hst.ok, hst.le, hargs, hrets, hbat, hlp⟩)
    (fun σ' h ↦ h.2.1)
  -- the glue
  have b8 := BlkA.seqK b7 (fun σ' h ↦ by
      have := h.2.2.1; have := h.1.2.2; have := h.1.1.2.2.1; have := h.1.1.1.2.2.1; show st.k ≤ s7.k; omega) (B := (osGlue lvl s7).1)
    (OutB := fun σ' ↦ (osGlue lvl s7).2.Ok σ' ∧ s7.k ≤ (osGlue lvl s7).2.k ∧
      σ' (.n (osGlue lvl s7).2.claim) = W.claimOut lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      obtain ⟨ok7, k67, -, -, hbat7, hlp7⟩ := (ho1 C0 rd1 hH0).2
      obtain ⟨-, k45, -, hl5, hli5, -⟩ := (ho1 C0 rd1 hH0).1.1.2
      have hy0 := (ho1 C0 rd1 hH0).1.1.1.1.1.2.2.2.2.2.2.2.1
      have hcl1 := (ho1 C0 rd1 hH0).1.1.1.1.1.1.2.2.2.2.1
      have k56 := (ho1 C0 rd1 hH0).1.2.2
      have k34 := (ho1 C0 rd1 hH0).1.1.1.2.2.1
      have w2 : s2.ys.getD 0 0 < s2.k := (osCommit_word0_lt c lvl lv s1).2.2.1
      have hlt5 : s5.lam < s5.k ∧ s5.lamInv < s5.k := osLam_lt s4
      have hbl := osQueries_batched_lt c lvl lv s6
      have fq := osQueries_fields c lvl lv s6
      have e7l : s7.lam = s5.lam := fq.1
      have e7i : s7.lamInv = s5.lamInv := fq.2.1
      have e7y : s7.ys = s2.ys := fq.2.2.1
      have e7c : s7.claim = s1.claim := fq.2.2.2.1
      have h := osGlue_complete (M := M) (H := H) (lvl := lvl) (st := s7) σ1 ok7.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by rw [e7l]; omega) (by rw [e7y]; omega)
        hbl.1 (by rw [e7i]; omega) hbl.2
        (fun C rd hH ↦ by
          obtain ⟨-, -, -, -, -, hlp⟩ := (ho1 C rd hH).2
          obtain ⟨-, -, -, el5, eli5, -⟩ := (ho1 C rd hH).1.1.2
          rw [e7l, e7i, el5, eli5, hlp, ha1 _ (show 28 < k by omega), ha1 _ (show 20 < k by omega),
            ha1 _ (show 22 < k by omega)]
          exact (hC C rd hH).glue)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hcl⟩ := ho
      rw [e7l, e7y, e7c, hl5, hy0, hbat7, hlp7, hcl1] at hcl
      exact ⟨hst.ok, hst.le, hcl⟩)
    (fun σ' h ↦ h.2.1)
  -- the level
  have eL : osLevel c lvl lv st = ((osRates c lvl st).1 ++ (osRounds true lv.foldsOff lv.folds s0).1 ++
      (osCommit c lvl lv s1).1 ++ (osQGrind s2).1 ++ (osPositions c lvl s3).1 ++ (osLam s4).1 ++
      (osHsMid lvl lv s5).1 ++ (osQueries c lvl lv s6).1 ++ (osGlue lvl s7).1, (osGlue lvl s7).2) := by
    simp only [osLevel, hfin, ↓reduceIte]
    rfl
  have eQ : osPreQ c lvl lv st = s6 := by simp only [osPreQ, hfin, ↓reduceIte]; rfl
  have eP : osPosStL c lvl lv st = s3 := by simp only [osPosStL, hfin, ↓reduceIte]; rfl
  have eR : osRndSt c lvl lv st = s1 := rfl
  rw [eL, eQ, eP, eR]
  refine BlkA.mono b8.agree fun σ' ho ↦ ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hrv, -, -⟩, B1⟩, B2⟩, -⟩, B4⟩, B5⟩, B6⟩, B7⟩, B8⟩, hag⟩ := ho
  obtain ⟨-, -, -, -, -, -, -, hsent2, hsz2, -, -, hcv2⟩ := B2
  obtain ⟨-, k34, -, -, hpa, hpr⟩ := B4
  obtain ⟨-, k45, hF5, -, -, hcur5, hcv5⟩ := B5
  obtain ⟨-, k56⟩ := B6
  obtain ⟨-, k67, hargs, hrets, -⟩ := B7
  obtain ⟨ok8, k78, hcl8⟩ := B8
  have fq := osQueries_fields c lvl lv s6
  refine ⟨⟨ok8, by show k ≤ (osGlue lvl s7).2.k; omega, hag⟩, ?_, ?_, hcl8, hrv, hsz2, hsent2, hpa, hpr, hargs, hrets,
    by show k + 9 ≤ (osGlue lvl s7).2.k; omega, ?_⟩
  · rw [← hF5]
    simp only [OsSt.F]
    rw [show (osGlue lvl s7).2.fs = s5.fs from fq.2.2.2.2.1]
  · rw [← hcur5]
    simp only [OsSt.cur]
    rw [show (osGlue lvl s7).2.cb = s5.cb from fq.2.2.2.2.2.1,
      show (osGlue lvl s7).2.co = s5.co from fq.2.2.2.2.2.2.1]
  · show cvOf ((osRates c lvl st).1 ++ (osRounds true lv.foldsOff lv.folds s0).1 ++ (osCommit c lvl lv s1).1 ++
      (osQGrind s2).1 ++ (osPositions c lvl s3).1 ++ (osLam s4).1 ++ (osHsMid lvl lv s5).1 ++
      (osQueries c lvl lv s6).1 ++ (osGlue lvl s7).1) σ' = _
    simp only [cvOf_append, cvOf_of_calls (osRates_calls _ _ _), cvOf_of_calls (osRounds_calls _ _ _ _),
      cvOf_of_calls (osQGrind_calls _), cvOf_of_calls (osHsMid_calls _ _ _), cvOf_of_calls (osGlue_calls _ _),
      cvOf_of_calls (osPositions_calls _ _ _), cvOf_of_calls (osQueries_calls _ _ _ _), hcv2, hcv5,
      List.map_nil, List.nil_append, List.append_nil, List.map_cons, List.map_append, hpa, hpr, hargs, hrets]
    rw [show σ' (.n osRate) = σ (.n osRate) from hag _ (by show 0 < k; omega)]
    simp only [cvMid, lpArgsV, List.append_assoc, List.cons_append, List.nil_append]

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

/-- **The final level's calls and memory** at its honest values, the grind's word passing, the memory
agreeing with `rd0` on the grinds' table. -/
structure FinC (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (cap : List E) (cl cur : E) (W : FinWD) : Prop where
  rounds : RoundsH rd (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) lv.folds lv.foldsOff cap cl cur W.rw
  om : C ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1")
    (W.cap1 lv cap cl ++ [MidW.cur1 lv cur, σ (.n osFmsg)])
    (omRets (W.cap1 lv cap cl) W.lane (some W.nq) (MidW.cur1 lv cur) (c.yrLen + lv.folds + 1))
  low : WinTabs rd (σ (.n osTabs))
  g17 : ((cellsOfState (W.S2 lv cap cl) false 1).limb 0).lane.toNat % 2 ^ queryGrind = 0
  lp : C (osPositionsName lv) (lpArgsV σ lv (cellsOfState (W.S2 lv cap cl) false 0) (capOf (W.S2 lv cap cl)))
    (W.cap3 lv cap cl)
  hs : ∀ j < c.yrLen + lv.folds, LoadHolds rd (σ (.n osFmsg)) j (W.lane.getD j 0) ∧
    LoadHolds rd W.pH j (W.lane.getD j 0 * word (hsScale lv.vanish (c.yrLog + 1) j 1) 0)
  q : C (osQueriesName c lvl lv)
    [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
      σ (.n osQbp) * gen ^ lv.posOff] [W.r0, W.r1, W.batched, 0 ^ lv.queries]
  roots : LoadHolds rd (σ (.n osRoots)) (2 * lvl) W.r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) W.r1

/-- **The final level's calls' values**: `opening_message` into `final_msg` (`fm`), `level_positions`'
and `level_queries`', as `cvMid`'s. -/
def cvFin (c : OsCfg) (lv : OsLv) (cap : List E) (cl cur : E) (W : FinWD) (x fm cf qp qb tb : E) :
    List (List E) :=
  [W.cap1 lv cap cl ++ [MidW.cur1 lv cur, fm] ++
      omRets (W.cap1 lv cap cl) W.lane (some W.nq) (MidW.cur1 lv cur) (c.yrLen + lv.folds + 1),
    x :: ((cellsOfState (W.S2 lv cap cl) false 0 :: capOf (W.S2 lv cap cl) ++
      [qp * gen ^ lv.posOff, qb * gen ^ lv.posOff, tb, gen ^ lv.squeezes]) ++ W.cap3 lv cap cl),
    x :: ([0, 0, cf * gen ^ (2 * lv.foldsOff), W.pH, qp * gen ^ lv.posOff, qb * gen ^ lv.posOff] ++
      [W.r0, W.r1, W.batched, 0 ^ lv.queries])]

/-- **The final level, honestly**. -/
theorem osLevelFin_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, HM M H C rd → st.Ok σ) (hfin : lvl = c.yrLevel) (W : FinWD) (rd0 : Reader)
    (hl0 : LowDef 11 rd0) (hrwl : W.rw.length = 5 * lv.folds) (hpad : ∃ p, st.pad = some p)
    (hco : st.co + 5 * lv.folds < u128Bound) (hpo : lv.posOff < u128Bound)
    (hsq : lv.squeezes < u128Bound)
    (h3 : 2 * lv.foldsOff < u128Bound) (hh8 : lvl * hsStride < u128Bound)
    (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, HM M H C rd → FinC C rd σ c lvl lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W)
    (hag0 : ∀ C rd, H C rd → LowAgree rd rd0) :
    BlkA M H σ st.k (osLevel c lvl lv st).2.k (osLevel c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osLevel c lvl lv st).2 ∧
      (osLevel c lvl lv st).2.F σ' = ⟨W.cap3 lv (st.fsv σ) (σ (.n st.claim)), []⟩ ∧
      (osLevel c lvl lv st).2.cur σ' = MidW.cur1 lv (st.cur σ) * gen ^ (c.yrLen + lv.folds + 1) ∧
      σ' (.n (osLevel c lvl lv st).2.claim) = W.cl1 lv (st.fsv σ) (σ (.n st.claim)) ∧
      (∀ j < 4, σ' (.n (st.k + 1 + 2 * j + 1)) = gw ((osRateVals lv).getD j 0)) ∧
      σ' (.n (osPositions c lvl (osPosStL c lvl lv st)).2.k) = gw (c.yrLen + lv.folds) ∧
      σ' (.n (osPreQ c lvl lv st).hs) = W.pH ∧
      (osPosCall (osPosStL c lvl lv st)).1.map σ' =
        lpArgsV σ lv (cellsOfState (W.S2 lv (st.fsv σ) (σ (.n st.claim))) false 0)
          (capOf (W.S2 lv (st.fsv σ) (σ (.n st.claim)))) ∧
      (osPosCall (osPosStL c lvl lv st)).2.map σ' = W.cap3 lv (st.fsv σ) (σ (.n st.claim)) ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).1.map σ' =
        [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv (osPreQ c lvl lv st)).2.map σ' = [W.r0, W.r1, W.batched, 0 ^ lv.queries] ∧
      st.k + 9 ≤ (osLevel c lvl lv st).2.k ∧
      cvOf (osLevel c lvl lv st).1 σ' = cvFin c lv (st.fsv σ) (σ (.n st.claim)) (st.cur σ) W (σ (.n osRate))
        (σ (.n osFmsg)) (σ (.n osCoefs)) (σ (.n osQpos)) (σ (.n osQbp)) (σ (.n osTabs))) := by
  set cap := st.fsv σ with hcap
  set cl := σ (.n st.claim) with hcl
  set cur := st.cur σ with hcur
  set k := st.k with hk
  have k43 : 43 ≤ k := hsf.k
  set s0 := (osRates c lvl st).2 with hs0
  set s1 := (osRounds true lv.foldsOff lv.folds s0).2 with hs1
  set s2 := (osFinalMsg c lv s1).2 with hs2
  set s3 := (osQGrind s2).2 with hs3
  set s4 := (osPositions c lvl s3).2 with hs4
  set s6 := (osHsFinal c lv s4).2 with hs6
  set s7 := (osQueries c lvl lv s6).2 with hs7
  have k0 : s0.k = k + 1 + 8 + 4 * (ligNRates - 1) + 2 := rfl
  have k01 : s0.k ≤ s1.k := osRounds_k _ _ _ _ (by omega)
  have k12 : s1.k ≤ s2.k := (osFinalMsg_lt c lv s1).2.2
  have k23 : s2.k + 1 ≤ s3.k := by have := gcLen_q; show s2.k + 1 ≤ s2.k + gcLen queryGrind - 2; omega
  have hlp0 : s0.lp + 2 = s0.k := rfl
  have hlw0 : s0.lw + 1 = s0.k := rfl
  obtain ⟨hrts1, hlp1, hlw1⟩ := osRndSt_fields c lvl lv st
  have e3lp : s3.lp = s0.lp := hlp1
  have e3lw : s3.lw = s0.lw := hlw1
  have e3rts : s3.rts = st.rts ++ [[k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1,
      k + 1 + 2 * 3 + 1]] := hrts1
  have hsqc : osSqCell s3 = k + 1 + 2 * 1 + 1 := osSqCell_of e3rts
  have hpo' : gw lv.posOff = gen ^ lv.posOff := gw_eq hpo
  -- the rates
  have b0 := osRates_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := st) σ hsf hok hrate
  -- the rounds
  have b1 := BlkA.seqK b0 (fun σ' h ↦ h.1.le) (B := (osRounds true lv.foldsOff lv.folds s0).1)
    (OutB := fun σ' ↦ OsStep σ σ' st s1 ∧ s1.F σ' = ⟨(roundsTr lv.folds cap cl W.rw).1, []⟩ ∧
      s1.cur σ' = cur * gen ^ (5 * lv.folds) ∧ σ' (.n s1.claim) = (roundsTr lv.folds cap cl W.rw).2 ∧
      s1.co = st.co + 5 * lv.folds ∧ s1.pad = st.pad)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok0 := (ho1 C0 rd1 hH0).1.ok
      obtain ⟨ef0, -, ec0, ecur0⟩ := OsSt.agree hsf.below ha1
      have ef0' : s0.fsv σ1 = cap := ef0
      have ec0' : σ1 (.n s0.claim) = cl := ec0
      have ecur0' : s0.cur σ1 = cur := ecur0
      have h := osRounds_completeA (M := M) (H := H) rd0 hl0 true lv.folds lv.foldsOff s0 σ1 W.rw ok0.sf
        (by show st.co + 5 * lv.folds < u128Bound; omega) hpad (fun C rd hH ↦ (ho1 C rd hH).1.ok) hrwl
        (fun C rd hH ↦ by
          rw [ef0', ec0', ecur0', ha1 osFch (by show 16 < k; omega), ha1 osCoefs (by show 18 < k; omega),
            ha1 osTabs (by show 10 < k; omega)]
          exact (hC C rd hH).rounds) hag0
      rw [ef0', ec0'] at h
      refine BlkA.monoH h fun C rd hH σ' _ ⟨ro, hag⟩ ↦ ?_
      have hag' : AgreeBelow k σ σ' := fun i hi ↦ (hag i (by omega)).trans (ha1 i hi)
      have hk1 : k ≤ s1.k := by omega
      refine ⟨osStep_of hsf (hok C rd hH) hag' hk1 ro.fs ro.below.fs ro.below.cb ro.below.claim
        (by rw [ro.co]; show st.co + 5 * lv.folds < u128Bound; omega) ro.pad ro.mats ro.below.mats,
        ro.F, by rw [ro.cur, ecur0'], ro.claim, ro.co, ro.pad⟩)
    (fun _ _ ↦ k01)
  -- the lane
  have b2 := BlkA.seqK b1 (fun _ _ ↦ by show st.k ≤ s1.k; omega) (B := (osFinalMsg c lv s1).1)
    (OutB := fun σ' ↦ s2.Ok σ' ∧ s1.k ≤ s2.k ∧ s2.F σ' = ⟨capOf (W.S2 lv cap cl), []⟩ ∧
      σ' (.n s2.word0) = cellsOfState (W.S2 lv cap cl) false 0 ∧
      σ' (.n s2.pow0) = cellsOfState (W.S2 lv cap cl) false 1 ∧
      s2.cur σ' = MidW.cur1 lv cur * gen ^ (c.yrLen + lv.folds + 1) ∧ s2.claim = s1.claim ∧
      cvOf (osFinalMsg c lv s1).1 σ' = [W.cap1 lv cap cl ++ [MidW.cur1 lv cur, σ (.n osFmsg)] ++
        omRets (W.cap1 lv cap cl) W.lane (some W.nq) (MidW.cur1 lv cur) (c.yrLen + lv.folds + 1)])
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      obtain ⟨st1, hF1, hcur1, -, -, -⟩ := (ho1 C0 rd1 hH0).2
      have sf1 : s1.Sf := st1.ok.sf
      have ef : s1.fsv σ1 = W.cap1 lv cap cl := by
        have := congrArg Fs.cap hF1
        simpa [OsSt.F, OsSt.fsv, FinWD.cap1] using this
      have ecur : s1.cur σ1 = MidW.cur1 lv cur := hcur1
      have h := osFinalMsg_complete (M := M) (H := H) (c := c) (lv := lv) (st := s1) σ1 sf1
        (fun C rd hH ↦ (ho1 C rd hH).2.1.ok) W.lane W.nq (fun C rd hH ↦ by
          rw [ef, ecur, ha1 _ (show 12 < k by omega)]; exact (hC C rd hH).om)
      refine h.mono fun σ' ho ↦ ?_
      obtain ⟨hst, hF, hw, hp, hcur, hclm, -, hcv⟩ := ho
      rw [ef] at hF hw hp
      rw [ecur] at hcur
      rw [ef, ecur, ha1 _ (show 12 < k by omega)] at hcv
      exact ⟨hst.ok, hst.le, hF, hw, hp, hcur, hclm, hcv⟩)
    (fun _ _ ↦ k12)
  -- the query grind
  have b3 := BlkA.seqK b2 (fun _ _ ↦ by show st.k ≤ s2.k; omega) (B := (osQGrind s2).1)
    (OutB := fun σ' ↦ s3.Ok σ' ∧ s2.k ≤ s3.k) (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have w := osFinalMsg_lt c lv s1
      have h := osQGrind_complete (M := M) (H := H) (s := s2) σ1 rd0 hl0 (fun C rd hH ↦ (ho1 C rd hH).2.1) w.2.1
        (by rw [(ho1 C0 rd1 hH0).2.2.2.2.2.1]; exact (hC C0 rd1 hH0).g17)
        hag0 (fun C rd hH ↦ by rw [ha1 _ (show 10 < k by omega)]; exact (hC C rd hH).low)
      exact h.mono fun σ' ho ↦ ⟨ho.ok, ho.le⟩)
    (fun _ _ ↦ by show s2.k ≤ s3.k; omega)
  -- the positions
  have b4 := BlkA.seqK b3 (fun _ _ ↦ by show st.k ≤ s3.k; omega) (B := (osPositions c lvl s3).1)
    (OutB := fun σ' ↦ s4.Ok σ' ∧ s3.k ≤ s4.k ∧ s4.F σ' = ⟨W.cap3 lv cap cl, []⟩ ∧
      s4.cur σ' = MidW.cur1 lv cur * gen ^ (c.yrLen + lv.folds + 1) ∧
      (osPosCall s3).1.map σ' = lpArgsV σ lv (cellsOfState (W.S2 lv cap cl) false 0) (capOf (W.S2 lv cap cl)) ∧
      (osPosCall s3).2.map σ' = W.cap3 lv cap cl)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok3 := (ho1 C0 rd1 hH0).2.1
      have w1 : s2.word0 < s2.k := (osFinalMsg_lt c lv s1).1
      have hcl3 : (W.cap3 lv cap cl).length = 5 := sqCapD_length (by simp [capOf]) _
      have eA : ∀ C rd, HM M H C rd → (osPosCall s3).1.map σ1 =
          lpArgsV σ lv (cellsOfState (W.S2 lv cap cl) false 0) (capOf (W.S2 lv cap cl)) := fun C rd hH ↦ by
        obtain ⟨⟨⟨⟨-, hrv, hlpv, hlwv⟩, -⟩, -, -, hF2, hw2, -⟩, -⟩ := ho1 C rd hH
        have ef : s3.fsv σ1 = capOf (W.S2 lv cap cl) := by
          show s2.fsv σ1 = _
          have := congrArg Fs.cap hF2
          simpa [OsSt.F, OsSt.fsv] using this
        have hsv := hrv 1 (by omega)
        rw [osPosCall_map, hsqc, ef, show s3.word0 = s2.word0 from rfl, hw2, e3lp, e3lw, hlpv, hlwv, hsv,
          ha1 _ (show 10 < k by omega), hpo']
        simp only [lpArgsV, osRateVals, List.getD_cons_succ, List.getD_cons_zero]
        rw [gw_eq hsq]
      have h := osPositions_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s3) σ1 ok3.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) (by show s2.word0 < s3.k; omega)
        (by rw [e3lp]; omega) (by rw [e3lw]; omega) (by rw [hsqc]; omega) (W.cap3 lv cap cl) hcl3
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [eA C rd hH]; exact (hC C rd hH).lp)
      refine BlkA.monoH h fun C rd hH σ' _ ho ↦ ?_
      obtain ⟨hst, hF, hcur, hargs, hrets⟩ := ho
      rw [eA C rd hH] at hargs
      have hcur2 := (ho1 C rd hH).1.2.2.2.2.2.2.1
      exact ⟨hst.ok, hst.le, hF, by rw [hcur]; exact hcur2, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the lane normalized
  have b6 := BlkA.seqK b4 (fun σ' h ↦ by have := h.2.2.1; show st.k ≤ s4.k; omega)
    (B := (osHsFinal c lv s4).1)
    (OutB := fun σ' ↦ s6.Ok σ' ∧ s4.k ≤ s6.k ∧ σ' (.n s4.k) = gw (c.yrLen + lv.folds) ∧
      σ' (.n s6.hs) = W.pH)
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok4 := (ho1 C0 rd1 hH0).2.1
      have h := osHsFinal_complete (M := M) (H := H) (c := c) (lv := lv) (st := s4) σ1 ok4.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.pH (fun j ↦ W.lane.getD j 0)
        (fun C rd hH j hj ↦ by rw [ha1 _ (show 12 < k by omega)]; exact (hC C rd hH).hs j hj)
      exact h.mono fun σ' ho ↦ ⟨ho.1.ok, ho.1.le, ho.2.1, ho.2.2⟩)
    (fun σ' h ↦ h.2.1)
  -- the queries
  have b7 := BlkA.seqK b6 (fun σ' h ↦ by
      have := h.2.2.1; have := h.1.2.2.1; show st.k ≤ s6.k; omega) (B := (osQueries c lvl lv s6).1)
    (OutB := fun σ' ↦ s7.Ok σ' ∧ s6.k ≤ s7.k ∧
      (osQCallOf c lvl lv s6).1.map σ' =
        [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
          σ (.n osQbp) * gen ^ lv.posOff] ∧
      (osQCallOf c lvl lv s6).2.map σ' = [W.r0, W.r1, W.batched, 0 ^ lv.queries])
    (fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd1, hH0⟩ ↦ by
      have ok6 := (ho1 C0 rd1 hH0).2.1
      have k46 := (ho1 C0 rd1 hH0).2.2.1
      have k34 := (ho1 C0 rd1 hH0).1.2.2.1
      have eA : ∀ C rd, HM M H C rd → osQArgsV σ1 c lvl lv s6 =
          [0, 0, σ (.n osCoefs) * gen ^ (2 * lv.foldsOff), W.pH, σ (.n osQpos) * gen ^ lv.posOff,
            σ (.n osQbp) * gen ^ lv.posOff] := fun C rd hH ↦ by
        have hpH := (ho1 C rd hH).2.2.2.2
        obtain ⟨-, -, hlpv, hlwv⟩ := (ho1 C rd hH).1.1.1.1.1
        simp only [osQArgsV, hfin, ↓reduceIte]
        rw [hpH, ha1 _ (show 18 < k by omega), show s6.lp = s0.lp from e3lp,
          show s6.lw = s0.lw from e3lw, hlpv, hlwv, hpo']
      have h := osQueries_complete (M := M) (H := H) (c := c) (lvl := lvl) (lv := lv) (st := s6) σ1 ok6.sf
        (fun C rd hH ↦ (ho1 C rd hH).2.1) W.r0 W.r1 W.batched (0 ^ lv.queries) h3 hh8
        (by show s3.lp < s6.k; omega) (by show s3.lw < s6.k; omega)
        (fun h ↦ absurd hfin h) (fun _ ↦ osHsFinal_hs_lt c lv s4)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [eA C rd hH]; exact (hC C rd hH).q)
        (fun C rd hH ↦ by rw [ha1 _ (show 14 < k by omega)]; exact (hC C rd hH).roots)
      refine BlkA.monoH h fun C rd hH σ' _ ho ↦ ?_
      obtain ⟨hst, hargs, hrets, -⟩ := ho
      rw [eA C rd hH] at hargs
      exact ⟨hst.ok, hst.le, hargs, hrets⟩)
    (fun σ' h ↦ h.2.1)
  -- the level
  have eL : osLevel c lvl lv st = ((osRates c lvl st).1 ++ (osRounds true lv.foldsOff lv.folds s0).1 ++
      (osFinalMsg c lv s1).1 ++ (osQGrind s2).1 ++ (osPositions c lvl s3).1 ++
      (osHsFinal c lv s4).1 ++ (osQueries c lvl lv s6).1, (osQueries c lvl lv s6).2) := by
    simp only [osLevel, hfin, ↓reduceIte, List.append_nil]
    rfl
  have eQ : osPreQ c lvl lv st = s6 := by simp only [osPreQ, hfin, ↓reduceIte]; rfl
  have eP : osPosStL c lvl lv st = s3 := by simp only [osPosStL, hfin, ↓reduceIte]; rfl
  rw [eL, eQ, eP]
  refine BlkA.mono b7.agree fun σ' ho ↦ ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hrv, -, -⟩, B1⟩, B2⟩, -⟩, B4⟩, B6⟩, B7⟩, hag⟩ := ho
  have hcv2 := B2.2.2.2.2.2.2.2
  obtain ⟨-, k34, hF4, hcur4, hpa, hpr⟩ := B4
  obtain ⟨-, k46, hsz6, hpH⟩ := B6
  obtain ⟨ok7, k67, hargs, hrets⟩ := B7
  have fq := osQueries_fields c lvl lv s6
  refine ⟨⟨ok7, by show k ≤ s7.k; omega, hag⟩, ?_, ?_, ?_, hrv, hsz6, hpH, hpa, hpr, hargs, hrets,
    by show k + 9 ≤ s7.k; omega, ?_⟩
  · rw [← hF4]
    simp only [OsSt.F]
    rw [show (osQueries c lvl lv s6).2.fs = s4.fs from fq.2.2.2.2.1]
  · rw [← hcur4]
    simp only [OsSt.cur]
    rw [show (osQueries c lvl lv s6).2.cb = s4.cb from fq.2.2.2.2.2.1,
      show (osQueries c lvl lv s6).2.co = s4.co from fq.2.2.2.2.2.2.1]
  · rw [show (osQueries c lvl lv s6).2.claim = s1.claim from fq.2.2.2.1, B1.2.2.2.1]
    rfl
  · show cvOf ((osRates c lvl st).1 ++ (osRounds true lv.foldsOff lv.folds s0).1 ++ (osFinalMsg c lv s1).1 ++
      (osQGrind s2).1 ++ (osPositions c lvl s3).1 ++ (osHsFinal c lv s4).1 ++ (osQueries c lvl lv s6).1) σ' = _
    simp only [cvOf_append, cvOf_of_calls (osRates_calls _ _ _), cvOf_of_calls (osRounds_calls _ _ _ _),
      cvOf_of_calls (osQGrind_calls _), cvOf_of_calls (osHsFinal_calls _ _ _),
      cvOf_of_calls (osPositions_calls _ _ _), cvOf_of_calls (osQueries_calls _ _ _ _), hcv2,
      List.map_nil, List.nil_append, List.append_nil, List.map_cons, List.map_append, hpa, hpr, hargs, hrets]
    rw [show σ' (.n osRate) = σ (.n osRate) from hag _ (by show 0 < k; omega)]
    simp only [cvFin, lpArgsV, List.append_assoc, List.cons_append, List.nil_append]

/-! ## What a level leaves -/

theorem osQueries_rts (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).2.rts = s.rts := by
  unfold osQueries
  dsimp only
  split_ifs <;> rfl

/-- **A level's state**: its cursor's offset at most `2`, the zero run allocated, `level_rate`'s
values appended to `rts`. -/
theorem osLevel_fields (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (hp : ∃ p, st.pad = some p) :
    (osLevel c lvl lv st).2.co ≤ 2 ∧ (∃ p, (osLevel c lvl lv st).2.pad = some p) ∧
      (osLevel c lvl lv st).2.rts = st.rts ++ [[st.k + 1 + 2 * 0 + 1, st.k + 1 + 2 * 1 + 1,
        st.k + 1 + 2 * 2 + 1, st.k + 1 + 2 * 3 + 1]] := by
  obtain ⟨hrts1, -, -⟩ := osRndSt_fields c lvl lv st
  have hpad1 : (osRndSt c lvl lv st).pad = st.pad := osRounds_pad _ _ _ _
  by_cases hfin : lvl = c.yrLevel
  · have e : (osLevel c lvl lv st).2 = (osQueries c lvl lv (osHsFinal c lv (osPositions c lvl
        (osQGrind (osFinalMsg c lv (osRndSt c lvl lv st)).2).2).2).2).2 := by
      simp only [osLevel, hfin, ↓reduceIte, List.append_nil]; rfl
    rw [e]
    obtain ⟨-, -, -, -, -, -, eco, epad⟩ := osQueries_fields c lvl lv (osHsFinal c lv (osPositions c lvl
        (osQGrind (osFinalMsg c lv (osRndSt c lvl lv st)).2).2).2).2
    rw [eco, epad, osQueries_rts]
    refine ⟨Nat.zero_le _ |>.trans (by show 0 ≤ 2; omega), ?_, hrts1⟩
    obtain ⟨p, hp⟩ := hp
    exact ⟨p, hpad1.trans hp⟩
  · have e : (osLevel c lvl lv st).2 = (osGlue lvl (osQueries c lvl lv (osHsMid lvl lv (osLam (osPositions c lvl
        (osQGrind (osCommit c lvl lv (osRndSt c lvl lv st)).2).2).2).2).2).2).2 := by
      simp only [osLevel, hfin, ↓reduceIte]; rfl
    rw [e]
    obtain ⟨-, -, -, -, -, -, eco, epad⟩ := osQueries_fields c lvl lv (osHsMid lvl lv (osLam (osPositions c lvl
        (osQGrind (osCommit c lvl lv (osRndSt c lvl lv st)).2).2).2).2).2
    refine ⟨?_, ?_, ?_⟩
    · show (osQueries c lvl lv _).2.co ≤ 2
      rw [eco]
      exact le_of_eq (osCommit_word0_lt c lvl lv (osRndSt c lvl lv st)).2.2.2
    · show ∃ p, (osQueries c lvl lv _).2.pad = some p
      rw [epad]
      exact ⟨_, rfl⟩
    · show (osQueries c lvl lv _).2.rts = _
      rw [osQueries_rts]
      exact hrts1

/-- A level's `level_rate` values below `k`, holding its row's: `g^posOff`, `g^(n / resBatch)`,
`g^(n % resBatch)`. -/
def RtVals (σ : Val) (rts : List (List ℕ)) (k lvl : ℕ) (lv : OsLv) : Prop :=
  (∀ i < 4, (rts.getD lvl []).getD i 0 < k) ∧
    σ (.n ((rts.getD lvl []).getD 0 0)) = gen ^ lv.posOff ∧
    σ (.n ((rts.getD lvl []).getD 2 0)) = gen ^ (lv.queries / resBatch) ∧
    σ (.n ((rts.getD lvl []).getD 3 0)) = gen ^ (lv.queries % resBatch)

theorem RtVals.agree {σ σ' : Val} {rts : List (List ℕ)} {k k' lvl : ℕ} {lv : OsLv}
    (h : RtVals σ rts k lvl lv) (hk : k ≤ k') (ha : AgreeBelow k σ σ') : RtVals σ' rts k' lvl lv := by
  obtain ⟨hb, h0, h2, h3⟩ := h
  exact ⟨fun i hi ↦ lt_of_lt_of_le (hb i hi) hk, by rw [ha _ (hb 0 (by omega))]; exact h0,
    by rw [ha _ (hb 2 (by omega))]; exact h2, by rw [ha _ (hb 3 (by omega))]; exact h3⟩

theorem RtVals.append {σ : Val} {rts : List (List ℕ)} {k lvl : ℕ} {lv : OsLv} (e : List ℕ)
    (h : RtVals σ rts k lvl lv) (hl : lvl < rts.length) : RtVals σ (rts ++ [e]) k lvl lv := by
  have : (rts ++ [e]).getD lvl [] = rts.getD lvl [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
  unfold RtVals; rw [this]; exact h

/-- **The level's own `level_rate` values**, as `rts`' new entry. -/
theorem rtVals_new {σ : Val} {rts : List (List ℕ)} {k k' lvl : ℕ} {lv : OsLv} (hl : rts.length = lvl)
    (hk : k + 9 ≤ k') (hpo : lv.posOff < u128Bound) (hq : lv.queries < u128Bound)
    (h : ∀ j < 4, σ (.n (k + 1 + 2 * j + 1)) = gw ((osRateVals lv).getD j 0)) :
    RtVals σ (rts ++ [[k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1, k + 1 + 2 * 3 + 1]]) k' lvl lv := by
  have e : (rts ++ [[k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1, k + 1 + 2 * 3 + 1]]).getD lvl [] =
      [k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1, k + 1 + 2 * 3 + 1] := by
    subst hl; simp [List.getD_eq_getElem?_getD]
  unfold RtVals
  rw [e]
  have h0 := h 0 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [osRateVals, List.getD_cons_zero, List.getD_cons_succ] at h0 h2 h3 ⊢
  refine ⟨fun i hi ↦ by interval_cases i <;> simp <;> omega, ?_, ?_, ?_⟩
  · rw [h0, gw_eq hpo]
  · rw [h2, gw_eq (lt_of_le_of_lt (Nat.div_le_self _ _) hq)]
  · rw [h3, gw_eq (lt_of_le_of_lt (Nat.mod_le _ _) hq)]

/-! ## The levels -/

/-- **The levels in sequence**: each level from a start satisfying `Q` is a block whose outcome
gives the next level's `Q` and its own `R`; `Q` holds on any valuation agreeing below the state's
next free value. -/
theorem osLevels_complete (c : OsCfg) (Q : ℕ → OsSt → Val → Prop) (R : ℕ → Val → Prop)
    (hQ : ∀ lvl st σ σ', Q lvl st σ → AgreeBelow st.k σ σ' → Q lvl st σ') :
    ∀ (lvs : List OsLv) (lvl : ℕ),
      (∀ i (h : i < lvs.length) st σ, Q (lvl + i) st σ →
        BlkA M H σ st.k (osLevel c (lvl + i) lvs[i] st).2.k (osLevel c (lvl + i) lvs[i] st).1
          (fun σ' ↦ st.k ≤ (osLevel c (lvl + i) lvs[i] st).2.k ∧
            Q (lvl + i + 1) (osLevel c (lvl + i) lvs[i] st).2 σ' ∧ R (lvl + i) σ')) →
      ∀ st σ, Q lvl st σ →
        BlkA M H σ st.k (osLevels c lvl lvs st).2.k (osLevels c lvl lvs st).1
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
