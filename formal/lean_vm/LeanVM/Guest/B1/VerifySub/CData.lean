/-
  LeanVM.Guest.B1.VerifySub.CData

  `verify_sub`'s completeness data: one accepting run of the deferring verifier, the pointers of
  the run's `HeapBuf`s, the honest memory there, and the block-by-block valuation tools.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteIface
public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.Sig.Frame
public import LeanVM.Guest.B1.Tables.Common

/-!
# `verify_sub`'s completeness: the run, the pointers, the memory

* `VsData`: one run of the deferring verifier as `verify_sub` runs it (the announced sizes, the
  root, each callee's words, value and final state, the values the callees return), with the
  derived challenges (`alphas`, `beta`, `mcs`, `lam`), the opening's target, the exported claims
  `fresh` and the proof `proof`.
* `VsData.Ok`: the phases run, within the deployed limits (the stack log in `[22, 28]`, the tables'
  log-heights below `29`, the bus depth below `33`).
* `VsPtrs`: the `HeapBuf` pointers, `verify_sub`'s and its callees'; `VsMem`: the honest words at
  `verify_sub`'s own (the callees' scratch is their own predicates, `VsCallees`).
* `Fixes σ l`: `σ` takes the listed values; `Completes.flatten`: a family of blocks completes in
  sequence; `numBelowB`: `NumBelow` by evaluation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## The run -/

/-- One run of the deferring verifier, as `verify_sub` and its callees read it. -/
structure VsData where
  seed : Digest
  pi : Digest
  logMem : ℕ
  rows : List ℕ
  rate : ℕ
  root : Digest
  /-- GKR: its words, its result, its final state. -/
  xsG : List E
  gr : E × List E × List E
  cvG : Digest
  /-- The tables: words, bus result, column claims, final state, and the values
  `verify_tables` returns (`g^n`, the bytecode's value, the public input's challenge). -/
  xsT : List E
  bus : BusResult
  claims : List ColumnClaim
  cvT : Digest
  gzcn : E
  bv : E
  rm : E
  /-- Flock: words, skip challenge, `alpha`, the matrices' value, the zerocheck's point, the
  lincheck's challenges in round order, the slices, final state. -/
  xsF : List E
  zSkip : E
  alpha : E
  mv : E
  chi : List E
  rcs : List E
  s : List E
  cvF : Digest
  /-- The stacked opening: words, openings, end, final state, roots. -/
  xsW : List E
  os : List Opening
  w : WhirEnd
  cvW : Digest
  roots' : List (Digest × ℕ × ℕ)
  /-- The table sumcheck's point, where the tables' claims lie (`chi`). -/
  chis : List E

namespace VsData

variable (D : VsData)

/-- The seed's chain state. -/
def cv0 : Digest := blake2sBytes (digestBytes D.seed ++ digestBytes D.pi)

/-- The eight announced words. -/
def ann : List E := announce D.logMem D.rows D.rate

/-- The root's two words. -/
def x0 : E := (digestScalars D.root).1

def x1 : E := (digestScalars D.root).2

/-- The state after the root. -/
def cv10 : Digest := obsAll (obsAll D.cv0 D.ann) [D.x0, D.x1]

/-- The bus challenges. -/
def alphas : List E := (sqAll 4 D.cv10).1

/-- The state GKR starts from. -/
def cvB : Digest := sqCv (sqAll 4 D.cv10).2

def beta : E := challengeOf D.cvB

/-- The tables' log-heights and the BLAKE2s table's, `τ`. -/
def hs : List ℕ := D.rows.map log2Ceil

def tau : ℕ := D.hs.getD 5 0

/-- The ring map's challenges and the state after them. -/
def mcs : List E := (sqAll 6 D.cvF).1

def cvM : Digest := (sqAll 6 D.cvF).2

/-- The batching challenge and the state the opening starts from. -/
def cvL : Digest := sqCv D.cvM

def lam : E := challengeOf D.cvL

/-- The opening's target. -/
def target : E := dot (powers D.lam (D.claims.length + 1)) (ringTarget D.s D.mcs :: D.claims.map (·.value))

/-- Flock's point, in the order the ring switch reads it. -/
def fpoint : List E := D.rcs.reverse ++ D.chi.drop 8

/-- The claims on the fixed polynomials. -/
def fresh : FixedClaims :=
  ⟨D.gr.2.1.take 18 ++ D.alphas, D.bv, D.alpha, D.zSkip, D.chi.take 8, D.rcs.reverse, D.s, D.mv⟩

/-- The stream after the announced words and the root. -/
def tail : List E := D.xsG ++ (D.xsT ++ (D.xsF ++ D.xsW))

/-- The stream. -/
def stream : List E := D.ann ++ D.x0 :: D.x1 :: D.tail

def proof : Proof := ⟨D.stream, D.os⟩

/-- The push side's total and the stack's. -/
def pushTotal : ℕ := ((pushKappas D.logMem D.hs).map (2 ^ ·)).sum

def stackTot : ℕ := stackTotal (columnKappas D.logMem 18 D.hs)

/-- The ring switch's chain `rs_chain`: row `j ≤ 64` is `g^j` and `Σ_{i<j} g^i Φ(s_i)`. -/
def rsChain : List E :=
  (List.range 65).flatMap fun j ↦
    [gen ^ j, ((List.range j).map fun i ↦ phiMap (D.s.getD i 0) D.mcs * gen ^ i).sum]

end VsData

/-- **The run is an accepting run within the deployed limits.** -/
structure VsData.Ok (bytecode : List K) (D : VsData) : Prop where
  logMem_ge : 16 ≤ D.logMem
  logMem_le : D.logMem ≤ 32
  rate_ge : 1 ≤ D.rate
  rate_le : D.rate ≤ 4
  rows_length : D.rows.length = 6
  rows_log : ∀ n ∈ D.rows, log2Ceil n < 29
  stack_ge : 22 ≤ (layoutOf bytecode D.logMem D.rows).stackLog
  stack_le : (layoutOf bytecode D.logMem D.rows).stackLog ≤ 28
  depth_lt : pushDepth (layoutOf bytecode D.logMem D.rows) < 33
  gkr : RunsTo (gkrPhase (pushDepth (layoutOf bytecode D.logMem D.rows))) D.cvB D.xsG D.gr D.cvG
  point_length : D.gr.2.1.length = pushDepth (layoutOf bytecode D.logMem D.rows)
  values_length : D.gr.2.2.length = 3
  tables : ∀ ev, BytecodeAt ev bytecode
      (D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++ D.alphas) D.bv →
    RunsTo (tablesSeg ev (layoutOf bytecode D.logMem D.rows) D.pi D.alphas D.beta D.gr.2.1
      D.gr.2.2) D.cvG D.xsT (D.bus, D.claims) D.cvT
  claims_length : D.claims.length = nClaims
  flock : ∀ ev, MatricesAt ev D.alpha D.zSkip (D.chi.take 8) D.rcs.reverse D.s D.mv →
    RunsTo (verifyFlock ev (blake2sR1csLogSize + D.tau)) D.cvT D.xsF (D.fpoint, D.s) D.cvF
  chi_length : D.chi.length = 8 + D.tau
  rcs_length : D.rcs.length = 8
  s_length : D.s.length = 64
  opening : RunsWith (whirOpen (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.target)
    D.cvL D.xsW D.os [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)]
    D.w D.cvW D.roots'
  open_point : D.w.point.length = (layoutOf bytecode D.logMem D.rows).stackLog
  accepts : D.w.Accepts (stackWeight (layoutOf bytecode D.logMem D.rows) D.claims D.fpoint
    (ringCoefficients D.mcs) D.lam)

/-! ## The pointers and the memory -/

/-- The `HeapBuf` pointers of the run: `verify_sub`'s buffers (G:2092-2228), the bit buffers of
its group 1 callees, the buffers `certify_placement` and `open_stacked` return, and each callee's
scratch pointers. -/
structure VsPtrs where
  pool : E
  cplen : E
  stream : E
  rows : E
  dims : E
  kbase : E
  bk : E
  zeta : E
  alpha : E
  fpw : E
  chi : E
  zchis : E
  lrs : E
  zpart : E
  mcs : E
  ctab : E
  zvals : E
  rs : E
  lam : E
  /-- `g_power_of_word`'s bit buffers, for the rate and the memory's log. -/
  gpwRate : E
  gpwMem : E
  /-- `log2_ceil_in_the_exponent`'s bit and prefix buffers, for the push total and the stack's. -/
  bpPush : E
  psPush : E
  bpStack : E
  psStack : E
  /-- `certify_placement`'s offsets and logs, `open_stacked`'s point. -/
  off : E
  kap : E
  pt : E
  /-- The callees' scratch. -/
  gkr : List E
  tab : List E
  fl : List E
  pl : List E
  op : List E
  term : List E

/-- **The honest memory at `verify_sub`'s buffers**: the stream, the tables' outputs, the stored
sizes, the challenges and every table the body fills, and `defer_out`. -/
structure VsMem0 (rd : Reader) (D : VsData) (P : VsPtrs) (out : E) : Prop where
  stream : ReadsAt rd P.stream D.stream
  pool : ReadsAt rd P.pool (D.claims.map (·.value))
  rows : ReadsAt rd P.rows (D.rows.map eOfNat)
  dims : ReadsAt rd P.dims (gen ^ D.logMem :: D.hs.map (gen ^ ·))
  kbase : ReadsAt rd P.kbase (kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·)))
  bk : ReadsAt rd P.bk (blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·)))
  zeta : ReadsAt rd P.zeta D.gr.2.1
  alpha : ReadsAt rd P.alpha D.alphas
  fpw : ReadsAt rd P.fpw (eqKernel D.alphas)
  zchis : ReadsAt rd P.zchis D.chi
  lrs : ReadsAt rd P.lrs D.rcs
  zpart : ReadsAt rd P.zpart D.s
  mcs : ReadsAt rd P.mcs D.mcs
  ctab : ReadsAt rd P.ctab (ringCoefficients D.mcs)
  zvals : ReadsAt rd P.zvals D.fpoint
  rs : ReadsAt rd P.rs D.rsChain
  lam : ReadsAt rd P.lam (powersFrom D.lam D.lam nClaims)
  out : ReadsAt rd out (Node.fixedCells D.fresh)

/-- `VsMem0` and the group 1 callees' bit buffers and the opening's point buffer, for the
`Rel`-level completeness. -/
structure VsMem (rd : Reader) (D : VsData) (P : VsPtrs) (out : E) : Prop
    extends VsMem0 rd D P out where
  gpwRate : ∀ j < 6, LoadHolds rd P.gpwRate j (bitE (D.rate.testBit j))
  gpwMem : ∀ j < 6, LoadHolds rd P.gpwMem j (bitE (D.logMem.testBit j))
  bpPush : ∀ j < 34, LoadHolds rd P.bpPush j (bitE (D.pushTotal.testBit j))
  psPush : ∀ j ≤ 34, LoadHolds rd P.psPush j (eOfNat (D.pushTotal % 2 ^ j))
  bpStack : ∀ j < 34, LoadHolds rd P.bpStack j (bitE (D.stackTot.testBit j))
  psStack : ∀ j ≤ 34, LoadHolds rd P.psStack j (eOfNat (D.stackTot % 2 ^ j))
  pt : ReadsAt rd P.pt (D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)

/-- **The callees' honest scratch**, at the arguments and return words of the honest run. -/
structure VsCallees (GMem TMem FMem PMem : Reader → List E → List E → List E → Prop)
    (OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop)
    (EMem : Reader → List E → List E → Prop) (bytecode : List K) (rd : Reader) (D : VsData)
    (P : VsPtrs) (lp sq : E) : Prop where
  gkr : GMem rd P.gkr [(digestScalars D.cvB).1, (digestScalars D.cvB).2, P.stream * gen ^ 10,
      gen ^ D.gr.2.1.length, P.zeta]
    ([(digestScalars D.cvG).1, (digestScalars D.cvG).2, P.stream * gen ^ 10 * gen ^ D.xsG.length] ++
      D.gr.2.2)
  tab : TMem rd P.tab
    [(digestScalars D.cvG).1, (digestScalars D.cvG).2, P.stream * gen ^ 10 * gen ^ D.xsG.length,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ D.gr.2.1.length, P.dims,
      P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0,
      D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]
    [(digestScalars D.cvT).1, (digestScalars D.cvT).2,
      P.stream * gen ^ 10 * gen ^ D.xsG.length * gen ^ D.xsT.length, D.gzcn, D.bv, D.rm]
  fl : FMem rd P.fl [(digestScalars D.cvT).1, (digestScalars D.cvT).2,
      P.stream * gen ^ 10 * gen ^ D.xsG.length * gen ^ D.xsT.length, gen ^ D.tau, P.zchis, P.lrs,
      P.zpart]
    [(digestScalars D.cvF).1, (digestScalars D.cvF).2,
      P.stream * gen ^ 10 * gen ^ D.xsG.length * gen ^ D.xsT.length * gen ^ D.xsF.length,
      D.zSkip, D.alpha, D.mv]
  pl : PMem rd P.pl [P.kbase, sq] [gen ^ D.stackTot, P.off, P.kap]
  op : OMem (layoutOf bytecode D.logMem D.rows).stackLog D.rate rd P.op
    [(digestScalars D.cvL).1, (digestScalars D.cvL).2, D.target, D.x0, D.x1,
      P.stream * gen ^ 10 * gen ^ D.xsG.length * gen ^ D.xsT.length * gen ^ D.xsF.length]
    [D.w.target, P.pt, D.w.inner, D.w.residual]
  term : EMem rd P.term [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn, gen ^ D.logMem,
    gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner, D.w.residual,
    D.w.target]

/-- The cursor after the announced words, the root, GKR's, the tables' and Flock's words. -/
def curG (P : VsPtrs) : E := P.stream * gen ^ 10

def curT (D : VsData) (P : VsPtrs) : E := curG P * gen ^ D.xsG.length

def curF (D : VsData) (P : VsPtrs) : E := curT D P * gen ^ D.xsT.length

def curW (D : VsData) (P : VsPtrs) : E := curF D P * gen ^ D.xsF.length

/-- **The calls of `verify_sub`'s body hold of `C`**, at the honest run's words: `C` is
`coreProgram.Rel rd` for `Rel`-level completeness (`callsOk_rel`), and `True` when the calls are
placed separately. -/
structure VsCallsOk (C : CallRel) (bytecode : List K) (D : VsData) (P : VsPtrs) (lp sq : E) :
    Prop where
  gpwRate : C "g_power_of_word__L6" [eOfNat D.rate, sq] [gen ^ D.rate]
  gpwMem : C "g_power_of_word__L6" [eOfNat D.logMem, sq] [gen ^ D.logMem]
  log2Push : C "log2_ceil_in_the_exponent__L0_L34" [gen ^ D.pushTotal, lp, sq]
    [gen ^ log2Ceil D.pushTotal]
  canon0 : C "assert_canonical" [D.x0] [0]
  canon1 : C "assert_canonical" [D.x1] [0]
  gkr : C "verify_bus_gkr" [(digestScalars D.cvB).1, (digestScalars D.cvB).2, curG P,
    gen ^ log2Ceil D.pushTotal, P.zeta]
    [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
      D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]
  tables : C "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
    (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
    P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
    D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm]
  flock : C "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P,
    gen ^ D.tau, P.zchis, P.lrs, P.zpart]
    [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv]
  loop84 : C "__loop84" [word 1 0 0, P.zpart, P.mcs, P.rs] []
  loop85 : D.tau ≠ 0 →
    C "__loop85" [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0] []
  certify : C "certify_placement" [P.kbase, sq] [gen ^ D.stackTot, P.off, P.kap]
  log2Stack : C "log2_ceil_in_the_exponent__L15_L34" [gen ^ D.stackTot, lp, sq]
    [gen ^ max 15 (log2Ceil D.stackTot)]
  opening : C (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
    [(digestScalars D.cvL).1, (digestScalars D.cvL).2, D.target, D.x0, D.x1, curW D P]
    [D.w.target, P.pt, D.w.inner, D.w.residual]
  terminal : C "check_opening_terminal" [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
    gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
    D.w.residual, D.w.target] []

/-! ## Valuations, block by block -/

/-- Every value of the list is numbered below `hi`, by evaluation. -/
def numBelowB (hi : ℕ) (vs : List V) : Bool := vs.all fun v ↦ v == .n v.idx && decide (v.idx < hi)

theorem numBelow_of_B {hi : ℕ} {vs : List V} (h : numBelowB hi vs = true) : NumBelow hi vs := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨v.idx, this.2, this.1⟩

/-- `σ` takes the listed values. -/
def Fixes (σ : Val) (l : List (ℕ × E)) : Prop := ∀ p ∈ l, σ (.n p.1) = p.2

theorem Fixes.of_ext {lo hi : ℕ} {σ σ' : Val} {l : List (ℕ × E)} (h : Fixes σ l)
    (he : Ext lo hi σ σ') (hl : ∀ p ∈ l, p.1 < lo) : Fixes σ' l := fun p hp => by
  rw [he.apply (Or.inl (hl p hp))]; exact h p hp

theorem Fixes.append {σ : Val} {l l' : List (ℕ × E)} (h : Fixes σ l) (h' : Fixes σ l') :
    Fixes σ (l ++ l') := fun p hp => by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem Fixes.left {σ : Val} {l l' : List (ℕ × E)} (h : Fixes σ (l ++ l')) : Fixes σ l :=
  fun p hp => h p (List.mem_append_left _ hp)

theorem Fixes.right {σ : Val} {l l' : List (ℕ × E)} (h : Fixes σ (l ++ l')) : Fixes σ l' :=
  fun p hp => h p (List.mem_append_right _ hp)

theorem Fixes.get {σ : Val} {l : List (ℕ × E)} (h : Fixes σ l) {k : ℕ} {e : E} (hk : (k, e) ∈ l) :
    σ (.n k) = e := h _ hk

variable {C : CallRel} {rd : Reader}

/-- A block completes with a valuation updated on its range. -/
theorem completes_upds {lo hi : ℕ} {ss : List Stmt} {σ : Val} {Post : Val → Prop}
    (l : List (ℕ × E)) (hl : ∀ p ∈ l, lo ≤ p.1 ∧ p.1 < hi)
    (hh : ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd (upds σ l) ss next kret)
    (hp : Post (upds σ l)) : Completes C rd lo hi ss σ Post :=
  ⟨upds σ l, upds_ext σ l hl, hp, hh⟩

theorem completes_nil (lo hi : ℕ) (σ : Val) {P : Val → Prop} (hp : P σ) :
    Completes C rd lo hi [] σ P :=
  ⟨σ, Ext.refl _ _ _, hp, fun _ _ hn => hn⟩

theorem mono_of_succ {st : ℕ → ℕ} {n : ℕ} (hst : ∀ i < n, st i ≤ st (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → st i ≤ st j := by
  intro i j hij hj
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_trans (ih (by omega) (by omega)) (hst j (by omega))

/-- **A family of blocks completes in sequence**, block `i` on `st i ..< st (i + 1)`, each from
the invariant before it to the one after. -/
theorem Completes.flatten {blk : ℕ → List Stmt} {st : ℕ → ℕ} {Inv : ℕ → Val → Prop} :
    ∀ n, (∀ i < n, st i ≤ st (i + 1)) → (∀ i < n, NumBelow (st (i + 1)) (Stmt.valsList (blk i))) →
    (∀ i < n, ∀ σ, Inv i σ → Completes C rd (st i) (st (i + 1)) (blk i) σ (Inv (i + 1))) →
    ∀ σ, Inv 0 σ → Completes C rd (st 0) (st n) ((List.range n).map blk).flatten σ (Inv n)
  | 0, _, _, _, σ, h0 => completes_nil _ _ σ h0
  | n + 1, hst, hnb, hb, σ, h0 => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton]
    have hm := mono_of_succ hst
    refine Completes.append (hm 0 n (by omega) (by omega)) (hst n (by omega)) ?_
      (Completes.flatten n (fun i hi => hst i (by omega)) (fun i hi => hnb i (by omega))
        (fun i hi => hb i (by omega)) σ h0)
      (fun σ' _ hσ' => hb n (by omega) σ' hσ')
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    refine numBelow_valsList_flatMap _ _ fun i hi => ?_
    have hi' : i < n := by simpa using hi
    exact (hnb i (by omega)).mono (hm (i + 1) n (by omega) (by omega))

end
end LeanVM.Guest.B1.VerifySub
