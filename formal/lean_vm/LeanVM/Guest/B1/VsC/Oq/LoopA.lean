/-
  LeanVM.Guest.B1.VsC.Oq.LoopA

  `opening_queries`' loop completes placed: each iteration by `callAtA_nodeL` on its honest
  valuation, fixed before the memory.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.NoHeap
public import LeanVM.Guest.B1.VsC.LpLoopA
public import LeanVM.Guest.B1.Opening.QueriesFns

/-!
# `opening_queries`' loop, placed

`OqCall`: the honest data of a call of `opening_queries__L…` of shape `s` below a cap of depth
`cd`: its `N` iterations and odd count `odd` (`g^N`, `g^odd`), the fold rounds, the final
coefficients, query `k`'s witness `ws k` (its position, row and siblings below the cap) and the
frame index `wp k` of its windows, `λ⁻¹`, and the first cells of the caller's buffers (cap leaves,
flags, rounds, final coefficients, positions, window pointers). Its queries number `Q`
(`oqCount`); query `k`'s fold is `ds k`, the chain `chain i` (`oqChain`).

* `OqCall.Static`: the opening's facts: each query's position below `2^(pd + cd)`, its row's and
  siblings' lengths, at the final level its fold the final polynomial at its point.
* `OqCall.Mem rd`: what the memory holds: the rounds, the final coefficients, each query's
  position, window pointer and windows, and its opening (`QueryOpensS`: its cap leaf and flag).
* `OqCall.Reg R`: those words lie in the region `R`.
* `OqLA … j`: iteration `j` of the loop at `(fp, c)` completes placed, ending at its cursor (no
  words of its own), popping its iterations' entries (`popsFrom j`).
* `oqL1_step`, `oqL0_step`: an iteration, given the next; `oqL_complete`: every one.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **The honest data of a call of `opening_queries`.** -/
structure OqCall where
  s : Oq
  cd : ℕ
  N : ℕ
  odd : ℕ
  rounds : List FoldRound
  hsv : List E
  ws : ℕ → QW
  wp : ℕ → ℕ
  mu : E
  icap : ℕ
  iflg : ℕ
  icf : ℕ
  ihs : ℕ
  ipos : ℕ
  iptr : ℕ

namespace OqCall

variable (o : OqCall)

/-- The queries. -/
def Q : ℕ := oqCount o.odd o.s.base o.N

/-- Query `k`'s honest values from `b`. -/
def qd (k b : ℕ) (emit : Bool) (pr : ℕ) : QD :=
  oqQD o.s o.cd b emit pr (ptrAt (o.wp k)) (ptrAt o.icap) (ptrAt o.iflg) o.rounds o.hsv (o.ws k)

/-- Query `k`'s fold. -/
def ds (k : ℕ) : E := qwFold o.s.base o.rounds (o.ws k)

/-- The chain after `i` iterations. -/
def chain (i : ℕ) : E := oqChain o.odd o.s.base o.mu o.ds i

/-- The chain buffer's words. -/
def chainL : List E := (List.range (o.N + 1)).map o.chain

/-- Iteration `j`'s arguments, the chain at `ich`. -/
def args (ich j : ℕ) : List E :=
  [gen ^ j, gen ^ o.N, ptrAt (o.ipos + o.odd), ptrAt (o.iptr + o.odd), ptrAt o.icap, ptrAt o.iflg,
    ptrAt o.icf, ptrAt o.ihs, ptrAt ich, o.mu]

/-- **The opening's facts.** -/
def Static : Prop :=
  o.s.RowShape ∧ o.s.FinOk ∧ 1 ≤ o.cd ∧ o.rounds.length = o.s.folds ∧
    (o.s.final = 1 → o.hsv.length = o.s.nHs) ∧ o.odd ≤ o.s.base ∧ o.N + 1 < ordG ∧
    ∀ k < o.Q, (o.ws k).1 < 2 ^ (o.s.pd + o.cd) ∧ (o.ws k).2.1.length = rowLen o.s.base o.s.folds ∧
      (o.ws k).2.2.length = o.s.pd ∧
      (o.s.final = 1 → foldRow (lanesOf o.s.base (o.ws k).2.1) (K.ofBits (o.ws k).1) o.rounds =
        novelSum o.hsv (wsChain (o.s.vs.map K.ofBits) (eOfNat (o.ws k).1)) o.s.nHs o.s.hsBits)

/-- What the memory holds of query `k`. -/
def QMem (rd : Reader) (k : ℕ) : Prop :=
  LoadHolds rd (ptrAt o.ipos) k (eOfNat (o.ws k).1) ∧ LoadHolds rd (ptrAt o.iptr) k (ptrAt (o.wp k)) ∧
    (∀ i < qwN (o.s.pd + o.cd) o.cd, LoadHolds rd (ptrAt (o.wp k)) i (gen ^ qwVal (o.s.pd + o.cd) o.cd (o.ws k).1 i)) ∧
    QueryOpensS rd o.s.base o.s.folds o.s.pd (ptrAt o.icap) (ptrAt o.iflg) (o.ws k).1 (o.ws k).2.1 (o.ws k).2.2

/-- **What the memory holds**: the rounds, the final coefficients, the queries. -/
def Mem (rd : Reader) : Prop :=
  RoundsAt rd (ptrAt o.icf) o.rounds ∧ (o.s.final = 1 → WordsAt rd (ptrAt o.ihs) o.hsv) ∧
    ∀ k < o.Q, o.QMem rd k

/-- **The region the calls read.** -/
def Reg (R : ℕ → Prop) : Prop :=
  (∀ k < o.Q, OqQReg R o.s (ptrAt o.icap) (ptrAt o.iflg) (ptrAt o.icf) (ptrAt o.ihs) (ptrAt (o.wp k))
    (o.ws k).1) ∧ ∀ k < o.Q, R (o.ipos + k) ∧ R (o.iptr + k)

/-- Iteration `j`'s entries. -/
def iterPops (j : ℕ) : List Pop :=
  if o.s.base = 1 then oqQE o.s (o.ws (o.odd + 2 * j)) ++ oqQE o.s (o.ws (o.odd + 2 * j + 1))
  else oqQE o.s (o.ws j)

/-- The entries of the iterations from `j`. -/
def popsFrom (j : ℕ) : List Pop := (List.range' j (o.N - j)).flatMap o.iterPops

theorem popsFrom_succ {j : ℕ} (h : j < o.N) : o.popsFrom j = o.iterPops j ++ o.popsFrom (j + 1) := by
  unfold popsFrom
  rw [show o.N - j = (o.N - (j + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem popsFrom_self : o.popsFrom o.N = [] := by simp [popsFrom]

theorem qdOk {rd : Reader} (hst : o.Static) (hm : o.Mem rd) {k : ℕ} (hk : k < o.Q) (b : ℕ)
    (emit : Bool) (pr : ℕ) : (o.qd k b emit pr).Ok rd (ptrAt o.icf) (ptrAt o.ihs) := by
  obtain ⟨-, -, hcd, hrl, hnh, -, -, hw⟩ := hst
  obtain ⟨hq, hrow, hsl, hfold⟩ := hw k hk
  obtain ⟨hR, hW, hm⟩ := hm
  obtain ⟨-, -, hwin, -, -, hc0, hc1, hfl⟩ := hm k hk
  exact qdOk_of_mem hcd hrow hsl hq hwin hc0 hc1 hfl hR hrl fun hf => ⟨hW hf, hnh hf, hfold hf⟩

end OqCall

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **Iteration `j` of the loop `loop` completes placed**, at every frame and cursor past its block,
ending at its cursor, popping its iterations' entries. -/
def OqLA (kd : ℕ) (loop : String) (o : OqCall) (ich : ℕ) (R : ℕ → Prop) (j : ℕ) : Prop :=
  ∀ fp c, fp + lpB fs loop o.N j ≤ c →
    CallAtA fs al cert kd loop (o.args ich j) [] R (fun _ => False) (fun _ => True)
      (fun rd => o.Mem rd ∧ (o.s.final ≠ 1 → ReadsAt rd (ptrAt ich) o.chainL))
      (fun rd t => t.pops coreProgram rd = o.popsFrom j) (lpB fs loop o.N j) fp c c

variable {fs al cert}

/-! ## Shared pieces -/

theorem oqIn_addr {R : ℕ → Prop} {a k off : ℕ} (h : R (a + k + off)) :
    OqIn R ((ptrAt a * gen ^ k).limb 0 * addressOfIndex off) :=
  ⟨a + k + off, addr_gpow a k off, h⟩

theorem chain_load {o : OqCall} {rd : Reader} {ich i : ℕ} (h : ReadsAt rd (ptrAt ich) o.chainL)
    (hi : i ≤ o.N) : LoadHolds rd (ptrAt ich) i (o.chain i) := by
  have hl : i < o.chainL.length := by simp [OqCall.chainL]; omega
  have := h i hl
  simpa [OqCall.chainL] using this

theorem oqResV_eq {s : Oq} (hf : s.final ≠ 1) (rounds : List FoldRound) (w : QW) :
    oqResV s rounds w = qwFold s.base rounds w := by simp [oqResV, hf]

/-- The tail call's taken flag at the guard `g^(j+1) + g^N`. -/
theorem guard_taken {N j : ℕ} (hN : N + 1 < ordG) (hj : j < N) :
    IsInK (gen ^ j * gen + gen ^ N) ∧ (decide (gen ^ j * gen + gen ^ N ≠ 0) = decide (j + 1 < N)) := by
  obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) (N := N) (by omega) (by omega)
  exact ⟨hK, decide_eq_decide.mpr hne⟩

/-- The kids' entries of a node whose one call is its tail, entered or a phantom. -/
theorem tail_pops {rd : Reader} {σ : Val} {c : Call} {ts : List Tree} {Q : Reader → Tree → Prop}
    {kn : List Pop} (hv : Tree.KidsValid coreProgram rd σ [c] ts) (hq : KidsPost rd [Q] [c] ts)
    (hT : c.taken = true → ∀ t, Q rd t → t.pops coreProgram rd = kn) (hF : c.taken = false → kn = []) :
    Tree.popsKids coreProgram rd ts = [kn] := by
  match ts, hv with
  | [t], hv =>
    rw [Tree.KidsValid] at hv
    obtain ⟨-, ht, -⟩ := hv
    simp only [Tree.popsKids, List.cons.injEq, and_true]
    by_cases hc : c.taken = true
    · exact hT hc t ((kidsPost_cons.mp hq).1 hc)
    · have hc' : c.taken = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at ht
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := ht
      rw [hF (by simpa using hc), Tree.pops]
  | [], hv => exact absurd hv (by simp [Tree.KidsValid])
  | _ :: _ :: _, hv => exact absurd hv (by simp [Tree.KidsValid])

/-! ## An iteration's node -/

/-- **An iteration completes placed** from its path at a valuation fixed before the memory: its
parameters the iteration's arguments, its events holding on every memory the loop reads, its one
call its tail at the guard `g`, its loads in `R`, no heap hint, and its entries its queries' then
its tail's. -/
theorem oqL_node {kd : ℕ} {loop : String} {fl : Fn} {o : OqCall} (hfl : coreProgram.find? loop = some fl)
    (hlp : coreProgram.loop loop = true) (hN : o.N + 1 < ordG) {R : ℕ → Prop} {ich j : ℕ} (hj : j < o.N)
    (hnext : j + 1 < o.N → OqLA fs al cert kd loop o ich R (j + 1))
    {σ : Val} {es : List Memory.Ev} {g : ℕ} (hpar : fl.params.map σ = o.args ich j) (hw : walk σ fl.body = .ret es [])
    (hdst : allocDsts es = []) (hallocs : allocs σ es = []) (haddr : addrs es = [])
    (hcalls : calls es = [⟨loop, oqNextArgs g, [], decide (σ (.n (g + 2)) ≠ 0)⟩])
    (hg2 : σ (.n (g + 2)) = gen ^ j * gen + gen ^ o.N)
    (hta : (oqNextArgs g).map σ = o.args ich (j + 1)) (hpl : fl.params = oqLoopParams)
    (hlo : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i) (hhi : heapHintAddrs σ es = [])
    (hev : ∀ rd, o.Mem rd ∧ (o.s.final ≠ 1 → ReadsAt rd (ptrAt ich) o.chainL) → ∀ ev ∈ es, ev.Holds rd σ)
    (hpops : ∀ rd ts kn, Tree.popsKids coreProgram rd ts = [kn] →
      (Memory.Tree.node loop σ (allocs σ es) ts).pops coreProgram rd = o.iterPops j ++ kn) :
    OqLA fs al cert kd loop o ich R j := by
  intro fp c hfc
  obtain ⟨hK, hdec⟩ := guard_taken hN hj
  have hnode : NodeAt cert (fp, c) loop σ (allocs σ es) es := by
    rw [hallocs]
    refine ⟨by rw [hdst]; rfl, fun q hq => ?_⟩
    rw [haddr] at hq
    exact absurd hq List.not_mem_nil
  have hc0 : c + (allocs σ es).sum = c := by rw [hallocs]; rfl
  have hlo' : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False) := fun A hA => by
    obtain ⟨i, h1, h2⟩ := hlo A hA
    exact ⟨i, h1, Or.inr (Or.inl h2)⟩
  have hhi' : ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False) := fun A hA => by
    rw [hhi] at hA; exact absurd hA List.not_mem_nil
  have hpost : ∀ (kn : List Pop) (Qn : Reader → Tree → Prop),
      (∀ rd ts, Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd [Qn] (calls es) ts →
        Tree.popsKids coreProgram rd ts = [kn]) → kn = o.popsFrom (j + 1) →
      ∀ rd ts, LowDef kd rd → (o.Mem rd ∧ (o.s.final ≠ 1 → ReadsAt rd (ptrAt ich) o.chainL)) → True →
        Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd [Qn] (calls es) ts →
        (Memory.Tree.node loop σ (allocs σ es) ts).pops coreProgram rd = o.popsFrom j := by
    intro kn Qn hk hkn rd ts _ _ _ hv hq
    rw [hpops rd ts kn (hk rd ts hv hq), o.popsFrom_succ hj, hkn]
  by_cases hlast : j + 1 = o.N
  · -- the last iteration: the tail is a phantom
    have hd : decide (σ (.n (g + 2)) ≠ 0) = false := by
      rw [hg2, hdec]; simp [hlast]
    have hB : lpB fs loop o.N j = fs loop + fs (tailKey loop) := by
      unfold lpB; rw [show o.N - j = 1 by omega, one_mul]
    rw [hB]
    refine callAtA_nodeL (Bt := fs (tailKey loop)) hlp (by rw [← hB]; exact hfc)
      ⟨σ, fl, es, [], [], [fun rd t => t.pops coreProgram rd = o.popsFrom (j + 1)], fun _ => True,
        fun _ => False, hfl, hpar, hw, rfl, hnode,
        by rw [hallocs]; exact ⟨by simp, List.Pairwise.nil⟩, hlo', hhi', fun i h => h.elim, ?_,
        fun _ _ => trivial, fun rd _ hP _ => hev rd hP, ?_⟩
    · rw [hc0, hcalls, KidsAtL]
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => (o.args ich (j + 1)).getD v.idx 0, fl, hfl, ?_⟩, trivial, trivial, fun _ _ => trivial,
        fun i h => h⟩
      rw [hpl, ← hpl, hta]
      rw [hpl]
      exact params_range_map (o.args ich (j + 1))
    · refine fun rd ts hl hp ho hv hq => hpost [] _ (fun rd ts hv hq => ?_) (by rw [hlast, o.popsFrom_self])
        rd ts hl hp ho hv hq
      rw [hcalls] at hv hq
      exact tail_pops hv hq (fun h => absurd h (by simp [hd])) (fun _ => rfl)
  · -- the next iteration
    have hlt : j + 1 < o.N := by omega
    have hd : decide (σ (.n (g + 2)) ≠ 0) = true := by
      rw [hg2, hdec]; simp [hlt]
    have hB := lpB_succ fs loop hj
    rw [hB]
    have hnx := hnext hlt (fp + fs loop) c (by rw [hB] at hfc; omega)
    refine callAtA_nodeL (Bt := lpB fs loop o.N (j + 1)) hlp (by rw [← hB]; exact hfc)
      ⟨σ, fl, es, [], [], [fun rd t => t.pops coreProgram rd = o.popsFrom (j + 1)], fun _ => True,
        fun _ => False, hfl, hpar, hw, rfl, hnode,
        by rw [hallocs]; exact ⟨by simp, List.Pairwise.nil⟩, hlo', hhi', fun i h => h.elim, ?_,
        fun _ _ => trivial, fun rd _ hP _ => hev rd hP, ?_⟩
    · rw [hc0, hcalls, KidsAtL]
      simp only [hd, ↓reduceIte]
      refine ⟨R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, fun _ _ _ => trivial,
        fun i h => h.elim⟩
      rw [hta]
      exact hnx.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => h.1) (fun _ _ _ h => h)
    · refine fun rd ts hl hp ho hv hq => hpost (o.popsFrom (j + 1)) _ (fun rd ts hv hq => ?_) rfl
        rd ts hl hp ho hv hq
      rw [hcalls] at hv hq
      exact tail_pops hv hq (fun _ t h => h) (fun h => absurd h (by simp [hd]))

theorem oqLoopParams_map (σ : Val) (args : List E) (h : oqLoopParams.map σ = args) :
    ∀ i < 10, σ (.n i) = args.getD i 0 := by
  intro i hi
  have := congrArg (·.getD i 0) h
  simp only [oqLoopParams] at this
  interval_cases i <;> simpa using this

/-! ## A level-0 iteration -/

/-- **A level-0 iteration completes placed**, given the next. -/
theorem oqL1_step {kd : ℕ} {loop : String} {fl : Fn} {o : OqCall} (hfl : coreProgram.find? loop = some fl)
    (hpl : fl.params = oqLoopParams) (hbl : fl.body = oqLoop1T o.s loop) (hlp : coreProgram.loop loop = true)
    (hb : o.s.base = 1) (hst : o.Static) {R : ℕ → Prop} (hR : o.Reg R) {ich : ℕ}
    (hRc : o.s.final ≠ 1 → ∀ i ≤ o.N, R (ich + i)) {j : ℕ} (hj : j < o.N)
    (hnext : j + 1 < o.N → OqLA fs al cert kd loop o ich R (j + 1)) :
    OqLA fs al cert kd loop o ich R j := by
  obtain ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ := hst
  set k1 := o.odd + 2 * j with hk1
  set k2 := o.odd + 2 * j + 1 with hk2
  have hQ : o.Q = o.odd + 2 * o.N := by simp [OqCall.Q, oqCount, hb]
  have hk1Q : k1 < o.Q := by omega
  have hk2Q : k2 < o.Q := by omega
  set D1 := o.qd k1 15 true 0 with hD1
  set D2 := o.qd k2 (oqE1 o.s + 2) false (oqK1 o.s 15) with hD2
  set args := o.args ich j with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F o.s args D1 D2 (o.chain j) w.idx := ⟨_, fun _ => rfl⟩
  obtain ⟨hpar, hv1, hv2, e11, e12, e14, eB2, eCh, eG2, eG4⟩ := oqIter1_vals (σ := σ) (fun _ => hσ _)
  have eP := oqLoopParams_map σ args hpar
  -- the path
  set ca : Stmt := .callIf (.n (oqG1 o.s + 2)) loop (oqNextArgs (oqG1 o.s)) with hca
  set pre := oqLoop1A o.s ++ [ca] with hpre
  have hok := oqLoop1A_ok o.s
  have hfm : pre.all Stmt.flatM = true := by rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact oqLoop1A_matchOk (D1.winSel hv1) (D2.winSel hv2) x hx
    · simp only [List.mem_singleton] at hx; subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop1T, oqNextT_eq, List.append_assoc]; rfl
  obtain ⟨es, hes⟩ : ∃ es, es = pre.flatMap (fmEvs σ) := ⟨_, rfl⟩
  have hw : walk σ fl.body = .ret es [] := by rw [hbody, hes]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [hes, i2, hal]; rfl
  have hcalls : calls es = [⟨loop, oqNextArgs (oqG1 o.s), [], decide (σ (.n (oqG1 o.s + 2)) ≠ 0)⟩] := by
    rw [hes, i4, hpre, List.filterMap_append, callS_flat (oqLoop1A_flat o.s)]; rfl
  have haddr : addrs es = [] := by
    rw [hes, i3, hpre, List.filterMap_append, hok.addrS]; simp [hca, Stmt.addrS]
  obtain ⟨hK, -⟩ := guard_taken hN hj
  have hta : (oqNextArgs (oqG1 o.s)).map σ = o.args ich (j + 1) := by
    simp only [oqNextArgs, List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
      eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega),
      eP 8 (by omega), eP 9 (by omega), ← pow_succ]
    rfl
  refine oqL_node hfl hlp hN hj hnext (g := oqG1 o.s) (by rw [hpl]; exact hpar) hw
    (by rw [hes, i1, hal]; rfl) hallocs haddr hcalls eG2 hta hpl ?_ ?_ ?_ ?_
  · -- the loads
    intro A hA
    rw [hes, loadAddrs_flatM σ pre hfm] at hA
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hA
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | hl | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact oqQLoad_in (d := D1) hv1 (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n 14)
          (by rw [eP 6 (by omega), eP 7 (by omega), e14]; exact hR.1 k1 hk1Q) hl
      · exact oqQLoad_in (d := D2) hv2 (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n (oqE1 o.s + 1))
          (by rw [eP 6 (by omega), eP 7 (by omega), eB2]; exact hR.1 k2 hk2Q) hl
      · rw [e11]
        exact oqIn_addr (by
          have := (hR.2 (k1 + off) (by omega)).1
          rwa [show o.ipos + (k1 + off) = o.ipos + o.odd + 2 * j + off by omega] at this)
      · rw [e12]
        exact oqIn_addr (by
          have := (hR.2 (k1 + off) (by omega)).2
          rwa [show o.iptr + (k1 + off) = o.iptr + o.odd + 2 * j + off by omega] at this)
      · rw [(eCh hf).1]
        exact oqIn_addr (by simpa using hRc hf j (by omega))
      · rw [(eCh hf).2]
        exact oqIn_addr (by
          have := hRc hf (j + 1) (by omega)
          rwa [show ich + (j + 1) = ich + j + 1 by omega] at this)
    · simp [hca, stmtLoad?] at hq
  · rw [hes]
    exact heapHintAddrs_flatM σ pre hfm (by
      rw [hpre, Stmt.atomsAll_append, oqLoop1A_noHeap]; simp [Stmt.atomsAll, hca])
  · -- the events
    rintro rd ⟨hm, hch⟩
    have hok1 := o.qdOk ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ hm hk1Q 15 true 0
    have hok2 := o.qdOk ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ hm hk2Q (oqE1 o.s + 2) false (oqK1 o.s 15)
    obtain ⟨hx1, hb1, -, -⟩ := hm.2.2 k1 hk1Q
    obtain ⟨hx2, hb2, -, -⟩ := hm.2.2 k2 hk2Q
    have hA := (oqIter1_at (rd := rd) hs hfin hok1 hok2
      (by rw [loadHolds_ptrAt_add]; exact hx1) (by rw [loadHolds_ptrAt_add, ← Nat.add_assoc]; exact hx2)
      (by rw [loadHolds_ptrAt_add]; exact hb1) (by rw [loadHolds_ptrAt_add, ← Nat.add_assoc]; exact hb2)
      (fun hf => by
        have hc := hch hf
        refine ⟨chain_load hc (by omega), ?_⟩
        have := chain_load hc (show j + 1 ≤ o.N by omega)
        rw [oqResV_eq hf, oqResV_eq hf]
        simpa [OqCall.chain, oqChain, hb, OqCall.ds, ← hk1, ← hk2] using this)
      (σ := σ) (fun i => hσ _)).2.1
    intro ev hev'
    rw [hes, hpre, List.flatMap_append] at hev'
    rcases List.mem_append.mp hev' with hev' | hev'
    · exact hok.evs_holds hA ev hev'
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hev'
      change ev ∈ slEvs σ ca at hev'
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev'
      rcases hev' with rfl | hev'
      · show IsInK (σ (.n (oqG1 o.s + 2)))
        rw [eG2]; exact hK
      · rw [hev']; split <;> trivial
  · -- the pops
    intro rd ts kn hk
    rw [oqLoop1_pops hfl hbl σ _ (D1.winSel hv1) (D2.winSel hv2) hk,
      show queryPops σ o.s 15 true = queryPops σ D1.s D1.b D1.emit from rfl, D1.queryPops_vals hv1,
      show queryPops σ o.s (oqE1 o.s + 2) false = queryPops σ D2.s D2.b D2.emit from rfl,
      D2.queryPops_vals hv2]
    simp only [OqCall.iterPops, hb, ↓reduceIte]
    rfl

/-! ## A deeper iteration -/

/-- **A deeper iteration completes placed**, given the next. -/
theorem oqL0_step {kd : ℕ} {loop : String} {fl : Fn} {o : OqCall} (hfl : coreProgram.find? loop = some fl)
    (hpl : fl.params = oqLoopParams) (hbl : fl.body = oqLoop0T o.s loop) (hlp : coreProgram.loop loop = true)
    (hb : o.s.base = 0) (hst : o.Static) {R : ℕ → Prop} (hR : o.Reg R) {ich : ℕ}
    (hRc : o.s.final ≠ 1 → ∀ i ≤ o.N, R (ich + i)) {j : ℕ} (hj : j < o.N)
    (hnext : j + 1 < o.N → OqLA fs al cert kd loop o ich R (j + 1)) :
    OqLA fs al cert kd loop o ich R j := by
  obtain ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ := hst
  have ho0 : o.odd = 0 := by omega
  have hQ : o.Q = o.N := by simp [OqCall.Q, oqCount, hb]
  have hjQ : j < o.Q := by omega
  set D := o.qd j 14 true 0 with hD
  set args := o.args ich j with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter0F o.s args D (o.chain j) w.idx := ⟨_, fun _ => rfl⟩
  obtain ⟨hpar, hv, e10, e12, e13, eCh, eG2, eG4⟩ := oqIter0_vals (σ := σ) (fun _ => hσ _)
  have eP := oqLoopParams_map σ args hpar
  set ca : Stmt := .callIf (.n (oqG0 o.s + 2)) loop (oqNextArgs (oqG0 o.s)) with hca
  set pre := oqLoop0A o.s ++ [ca] with hpre
  have hok := oqLoop0A_ok o.s
  have hfm : pre.all Stmt.flatM = true := by rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact oqLoop0A_matchOk (D.winSel hv) x hx
    · simp only [List.mem_singleton] at hx; subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop0T, oqNextT_eq, List.append_assoc]; rfl
  obtain ⟨es, hes⟩ : ∃ es, es = pre.flatMap (fmEvs σ) := ⟨_, rfl⟩
  have hw : walk σ fl.body = .ret es [] := by rw [hbody, hes]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [hes, i2, hal]; rfl
  have hcalls : calls es = [⟨loop, oqNextArgs (oqG0 o.s), [], decide (σ (.n (oqG0 o.s + 2)) ≠ 0)⟩] := by
    rw [hes, i4, hpre, List.filterMap_append, callS_flat (oqLoop0A_flat o.s)]; rfl
  have haddr : addrs es = [] := by
    rw [hes, i3, hpre, List.filterMap_append, hok.addrS]; simp [hca, Stmt.addrS]
  obtain ⟨hK, -⟩ := guard_taken hN hj
  have hta : (oqNextArgs (oqG0 o.s)).map σ = o.args ich (j + 1) := by
    simp only [oqNextArgs, List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
      eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega),
      eP 8 (by omega), eP 9 (by omega), ← pow_succ]
    rfl
  refine oqL_node hfl hlp hN hj hnext (g := oqG0 o.s) (by rw [hpl]; exact hpar) hw
    (by rw [hes, i1, hal]; rfl) hallocs haddr hcalls eG2 hta hpl ?_ ?_ ?_ ?_
  · -- the loads
    intro A hA
    rw [hes, loadAddrs_flatM σ pre hfm] at hA
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hA
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact oqQLoad_in (d := D) hv (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n 13)
          (by rw [eP 6 (by omega), eP 7 (by omega), e13]; exact hR.1 j hjQ) hl
      · rw [e10]
        exact oqIn_addr (by
          have := (hR.2 j hjQ).1
          rwa [show o.ipos + j = o.ipos + o.odd + j + 0 by omega] at this)
      · rw [e12]
        exact oqIn_addr (by
          have := (hR.2 j hjQ).2
          rwa [show o.iptr + j = o.iptr + o.odd + j + 0 by omega] at this)
      · rw [(eCh hf).1]
        exact oqIn_addr (by simpa using hRc hf j (by omega))
      · rw [(eCh hf).2]
        exact oqIn_addr (by
          have := hRc hf (j + 1) (by omega)
          rwa [show ich + (j + 1) = ich + j + 1 by omega] at this)
    · simp [hca, stmtLoad?] at hq
  · rw [hes]
    exact heapHintAddrs_flatM σ pre hfm (by
      rw [hpre, Stmt.atomsAll_append, oqLoop0A_noHeap]; simp [Stmt.atomsAll, hca])
  · -- the events
    rintro rd ⟨hm, hch⟩
    have hok1 := o.qdOk ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ hm hjQ 14 true 0
    obtain ⟨hx, hbp, -, -⟩ := hm.2.2 j hjQ
    have hA := (oqIter0_at (rd := rd) hs hfin hok1
      (by rw [loadHolds_ptrAt_add, ho0, Nat.zero_add]; exact hx)
      (by rw [loadHolds_ptrAt_add, ho0, Nat.zero_add]; exact hbp)
      (fun hf => by
        have hc := hch hf
        refine ⟨chain_load hc (by omega), ?_⟩
        have := chain_load hc (show j + 1 ≤ o.N by omega)
        rw [oqResV_eq hf]
        simpa [OqCall.chain, oqChain, hb, OqCall.ds] using this)
      (σ := σ) (fun i => hσ _)).2.1
    intro ev hev'
    rw [hes, hpre, List.flatMap_append] at hev'
    rcases List.mem_append.mp hev' with hev' | hev'
    · exact hok.evs_holds hA ev hev'
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hev'
      change ev ∈ slEvs σ ca at hev'
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev'
      rcases hev' with rfl | hev'
      · show IsInK (σ (.n (oqG0 o.s + 2)))
        rw [eG2]; exact hK
      · rw [hev']; split <;> trivial
  · -- the pops
    intro rd ts kn hk
    rw [oqLoop0_pops hfl hbl σ _ (D.winSel hv) hk,
      show queryPops σ o.s 14 true = queryPops σ D.s D.b D.emit from rfl, D.queryPops_vals hv]
    simp only [OqCall.iterPops, hb]
    rfl

/-! ## The loop -/

/-- **Every iteration of `opening_queries`' loop completes placed.** -/
theorem oqL_complete {kd : ℕ} {loop : String} {fl : Fn} {o : OqCall} (hfl : coreProgram.find? loop = some fl)
    (hpl : fl.params = oqLoopParams) (hbl : fl.body = oqLoopT o.s loop) (hlp : coreProgram.loop loop = true)
    (hst : o.Static) {R : ℕ → Prop} (hR : o.Reg R) {ich : ℕ} (hRc : o.s.final ≠ 1 → ∀ i ≤ o.N, R (ich + i)) :
    ∀ n j, j + n + 1 = o.N → OqLA fs al cert kd loop o ich R j := by
  have hb01 : o.s.base = 0 ∨ o.s.base = 1 := by rcases hst.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have step : ∀ j, j < o.N → (j + 1 < o.N → OqLA fs al cert kd loop o ich R (j + 1)) →
      OqLA fs al cert kd loop o ich R j := fun j hj hn => by
    rcases hb01 with hb | hb
    · exact oqL0_step hfl hpl (by rw [hbl, oqLoopT_zero hb]) hlp hb hst hR hRc hj hn
    · exact oqL1_step hfl hpl (by rw [hbl, oqLoopT_one hb]) hlp hb hst hR hRc hj hn
  intro n
  induction n with
  | zero => intro j hj; exact step j (by omega) fun h => absurd h (by omega)
  | succ n ih => intro j hj; exact step j (by omega) fun _ => ih (j + 1) (by omega)

end
end LeanVM.Guest.B1.VsC
