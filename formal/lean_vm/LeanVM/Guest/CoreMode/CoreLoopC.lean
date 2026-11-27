/-
  LeanVM.Guest.CoreMode.CoreLoopC

  The core route for a loop helper whose body has calls: atoms and calls, its tail call, its return.
-/

module

public import LeanVM.Guest.CoreMode.CoreLoop
public import LeanVM.Guest.CoreMode.LoopBC
public import LeanVM.Guest.CoreMode.PairLoopC
public import LeanVM.Guest.CoreMode.LoopPtr
public import LeanVM.Guest.Mode.InvCert
import LeanVM.Guest.StmtsAppend

/-!
# The core route for a loop helper

A loop helper (`loopBC`, a leaf one's body among them): atoms and calls, its tail call `callIf c f args` to
itself, `ret []`; compiled (`loopCodeC`) to code whose last two `JUMP`s are the tail call's (through
a next-frame cell, to the function's entry) and the return, every other `JUMP` a call's (on a nonzero
constant, `jumpCallOk`). `LoopOkC K Cf`: the kernel's checks, as `CoreOk`'s, with the heap check's
loop rules (`heapOkC` at a termination fact), the loop's mode signature translated (`sigOkLP`), the
callees' heap signatures (`callsBL`) and the frame walk told the environment's callee signatures, its own
entry's among them.

`frameSpec_loopC`: such a function meets `FrameSpec` for `CoreAt`: its steps are the function route's
(`heapRd_pair`, `fall_wrk`), its calls `frameSpec_core`'s (`entry_fitB`, `post_wrk`). The tail `JUMP`, whichever way the frame walk hands it over (a tail
call, or a call into the function's own entry), is the loop's tail call (`tail_nextC`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs
  walk_ret_cons walk_callIf_cons)
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk TermAt LTF Back
  TermEntry)

@[expose] public section

variable {κ : ℕ}

/-! ## The shape -/

/-- **A callee's mode signature holds of its heap signature** at a call: `fitB`'s, a heap run it guarantees
also allowed to be a mode pointer run's run (whose cells a pointer run has written). -/
def fitBL (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Bool :=
  (match G.self with
    | some o => decide (o < 2 ^ 28)
    | none => true) &&
    (G.preP.all fun r ↦ monoS G na true (rngM r.1) && h.prePR.any (prunIs r ·) && h.preR.any (rngXIs r.1 ·)) &&
    G.entry.contains 0 && G.entry.contains 1 && h.postP.all (hpAll G (na + nr) G.post) &&
    (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && prunIs r p) &&
    (h.retM.isEmpty && h.postQ.isEmpty) &&
    G.pre.all (fun m ↦ (monoS G na true m && match monoC m with
      | some c => cellIn c h.pre
      | none => false) || hpIn G na true h.preP h.pre m) &&
    G.preR.all (fun r ↦ (monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
      | _, _ => false)) || (monoS G na true (rngM r) && h.preR.any (rngXIs r ·))) &&
    h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) &&
    (h.postR.all fun q ↦ ((G.postR ++ G.postL).any fun r ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
      (monoS G (na + nr) false (rngM r) && rngXIs r q)) ||
      (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && rngXIs r.1 q) && Nat.beq h.ghosts 0

/-- **`fitBL`'s guarantees**: its callee's heap guarantees among its mode signature's. -/
def fitBLpost (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Bool :=
  h.postP.all (hpAll G (na + nr) G.post) &&
    (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && prunIs r p) &&
    (h.retM.isEmpty && h.postQ.isEmpty) &&
    h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) &&
    (h.postR.all fun q ↦ ((G.postR ++ G.postL).any fun r ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
      (monoS G (na + nr) false (rngM r) && rngXIs r q)) ||
      (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && rngXIs r.1 q)

/-- **`fitBL`'s conjuncts**, by name. -/
structure FitBL (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Prop where
  self : (match G.self with
    | some o => decide (o < 2 ^ 28)
    | none => true) = true
  preP : (G.preP.all fun r ↦ monoS G na true (rngM r.1) && h.prePR.any (prunIs r ·) && h.preR.any (rngXIs r.1 ·)) = true
  ent0 : G.entry.contains 0 = true
  ent1 : G.entry.contains 1 = true
  postP : h.postP.all (hpAll G (na + nr) G.post) = true
  postPR : (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦
    monoS G (na + nr) false (rngM r.1) && prunIs r p) = true
  retM : h.retM.isEmpty = true
  postQ : h.postQ.isEmpty = true
  pre : G.pre.all (fun m ↦ (monoS G na true m && match monoC m with
    | some c => cellIn c h.pre
    | none => false) || hpIn G na true h.preP h.pre m) = true
  preR : G.preR.all (fun r ↦ (monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
    match monoC r.q, runPts ⟨[], 0⟩ r with
    | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
    | _, _ => false)) || (monoS G na true (rngM r) && h.preR.any (rngXIs r ·))) = true
  post : h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
    G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) = true
  postR : (h.postR.all fun q ↦ ((G.postR ++ G.postL).any fun r ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
    (monoS G (na + nr) false (rngM r) && rngXIs r q)) ||
    (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && rngXIs r.1 q) = true
  ghosts : Nat.beq h.ghosts 0 = true

theorem FitBL.of_ok {G : Mode.Sig} {h : HSig} {na nr : ℕ} (hf : fitBL G h na nr = true) : FitBL G h na nr := by
  simp only [fitBL, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, ⟨h7, h8⟩⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hf
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem fitBLpost_of {G : Mode.Sig} {h : HSig} {na nr : ℕ} (hf : fitBL G h na nr = true) :
    fitBLpost G h na nr = true := by
  have h := FitBL.of_ok hf
  simp only [fitBLpost, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h.postP, h.postPR⟩, ⟨h.retM, h.postQ⟩⟩, h.post⟩, h.postR⟩

/-- **A call's callee in a loop helper**: `fitBL`, or one naming ghosts (the function route's `fitB` at its pointer
bases, `hpArgOk`) with `fitBL`'s guarantees. -/
noncomputable def fitBLC (Cf : CFun) (G : Mode.Sig) (f : String) (na nr : ℕ) : Bool :=
  fitBL G (Cf.sigOf f) na nr || (fitB G (Cf.sigOf f) na nr && fitBLpost G (Cf.sigOf f) na nr && hpArgOk Cf G f)

/-- **A call's `JUMP`**, `jumpCallOk` at `fitBLC`. -/
noncomputable def jumpCallOkL (Cf : CFun) : OffsetInstruction → Bool
  | .jump _ od of => match Cf.X.pcAt od with
    | some t => match getF Cf.X.ents t with
      | some f => !(decide (Cf.frame.entry ≤ t) && decide (t < Cf.frame.entry + Cf.frame.len)) &&
        decide (t < 2 ^ 30) && !Cf.X.selfAt of && match Cf.frame.sigs.get t, getF Cf.X.sites of with
        | some G, some s => decide (s.r < 2 ^ 30) && fitBLC Cf G f s.args.length s.rets.length
        | _, _ => false
      | none => true
    | none => true
  | _ => true

theorem jumpCallOkL_spec {Cf : CFun} {oc od of t : ℕ} {f : String} (h : jumpCallOkL Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) (hent : getF Cf.X.ents t = some f) :
    ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧ Cf.X.selfAt of = false ∧
      ∃ G s, Cf.frame.sigs.get t = some G ∧ getF Cf.X.sites of = some s ∧ s.r < 2 ^ 30 ∧
        fitBLC Cf G f s.args.length s.rets.length = true := by
  simp only [jumpCallOkL, hpt, hent, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨hout, ht⟩, hsf⟩, h⟩ := h
  refine ⟨fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht, hsf, ?_⟩
  split at h
  · rename_i G s hG hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨G, s, hG, hs, h.1, h.2⟩
  · cases h

/-- A conditional call's `JUMP`: its target the entry of a function other than the loop itself. -/
noncomputable def callIfJ (Cf : CFun) (b : ℕ) : Bool :=
  match Cf.X.pcAt b with
  | some t => match getF Cf.X.ents t with
    | some f => !(f == Cf.fn.name)
    | none => false
  | none => false

/-- **A `JUMP` of a loop helper's code before its tail call**: on a constant `0` (never taken), or a
call's: on a nonzero constant, not in the frame, not a return, to a callee whose mode signature holds
of its heap signature (`jumpCallOkL`); or a conditional call's: on no constant, through a cell neither
the own frame's nor a next frame's nor a dispatch's target, to the entry of another function
(`callIfJ`, `jumpCallOkL`); or a jump in the frame (a branch's, a `match`'s), through no dispatch's
target cell, to no callee (`jumpCallOkL`). -/
noncomputable def callJ (Cf : CFun) : OffsetInstruction → Bool
  | .jump a b c => Cf.X.zeroAt a || (Cf.X.nzAt a && !Cf.X.selfAt c && !(Nat.beq b 0 && Nat.beq c 1) &&
      jumpCallOkL Cf (.jump a b c)) || (Cf.X.selfAt c && dspNo Cf.X b c && jumpCallOkL Cf (.jump a b c)) ||
      (!Cf.X.nzAt a && !Cf.X.selfAt c && !Cf.X.nextAt c && !(Nat.beq b 0 && Nat.beq c 1) && dspNo Cf.X b c &&
        callIfJ Cf b && jumpCallOkL Cf (.jump a b c))
  | _ => true

/-- **A loop helper's code with calls**: its last two instructions the tail call's `JUMP` (its
condition no constant, through a next-frame cell, to the function's entry) and the return (its
condition a nonzero constant); every other `JUMP` a call's (`callJ`). -/
noncomputable def loopCodeC (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  match code.reverse with
  | .jump oc' od' of' :: .jump oc od of :: pre =>
    Nat.beq od' 0 && Nat.beq of' 1 && !Cf.X.zeroAt oc' && Cf.X.nzAt oc' && !Cf.X.zeroAt oc && !Cf.X.nzAt oc &&
      !Cf.X.selfAt of && Cf.X.nextAt of && !Nat.beq od 0 && decide (Cf.X.pcAt od = some Cf.X.entry) &&
      Cf.X.entOk Cf.X.entry Cf.fn.name &&
      pre.all (callJ Cf)
  | _ => false

/-- **The shape around a loop helper**: not `main`, frame cell `1` not its frame pointer, cell `0` no pc, the frame
walk's callee signatures out of its own code, not `main`'s frame, its entry cells and self cell small, the header
among the entry cells, its hints by increasing pc, and no conditional call's condition at a nonzero constant's
cell. -/
noncomputable def loopShapeOk0 (Cf : CFun) : Bool :=
  !Cf.X.main && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len &&
    !Cf.frame.F.fpOne &&
    Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    (match Cf.frame.sig.self with
      | some o => decide (o + 1 < 2 ^ Exec.envDepth) && decide (o < 2 ^ 28)
      | none => true) &&
    Cf.frame.sig.entry.contains 0 && Cf.frame.sig.entry.contains 1 &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints &&
    stmtsAll (fun s ↦ match s with
      | .callIf c _ _ => !Cf.X.nzAt (Cf.X.locAt c.idx)
      | _ => true) Cf.fn.body

/-- **`loopShapeOk0`'s conjuncts**, by name. -/
structure LoopShape0 (Cf : CFun) : Prop where
  main : Cf.X.main = false
  self1 : Cf.X.selfAt 1 = false
  pc0 : Cf.X.pcAt 0 = none
  sigsOut : sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len = true
  fp1 : Cf.frame.F.fpOne = false
  ent : ∀ o ∈ Cf.frame.sig.entry, o + 1 < 2 ^ Exec.envDepth
  self : ∀ o, Cf.frame.sig.self = some o → o + 1 < 2 ^ Exec.envDepth ∧ o < 2 ^ 28
  ent0 : 0 ∈ Cf.frame.sig.entry
  ent1 : 1 ∈ Cf.frame.sig.entry
  len : Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30
  incr : Mode.pcsIncr Cf.frame.hints = true
  cif : ∀ c f args, Stmt.callIf c f args ∈ stmtsOf Cf.fn.body → Cf.X.nzAt (Cf.X.locAt c.idx) = false

theorem LoopShape0.of_ok {Cf : CFun} (h : loopShapeOk0 Cf = true) : LoopShape0 Cf := by
  simp only [loopShapeOk0, stmtsAll_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    Option.isNone_iff_eq_none, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun o ho ↦ ?_, h8, h9, h10, h11, fun c f args hc ↦ by simpa using h12 _ hc⟩
  rw [ho] at h7
  simpa using h7

/-- **A ghost slot's exponent** (`hiRes`'s ghost case): the bound the word of ghost slot `b` (`np ≤ b < np + ng`),
its exponent by a residual `e(a) < e(GB + b - np)` over its ghost value. -/
def hiG (np ng : ℕ) (res : List CRes) : CIdx → Bool
  | .val b => decide (np ≤ b) && decide (b < np + ng) && res.any fun x ↦ match x with
    | .lt _ b' => decide (b' = .val (GB + (b - np)))
    | _ => false
  | _ => false

/-- **Each linked upper bound of a loop's runs over its caller's cells has an exponent by a residual**: for each mode
precondition run `rngH` translates with an upper bound other than a constant, that bound over the parameters and a
residual `e(a) < e(hi)`. -/
def hiRes (G : Mode.Sig) (gl : List (ℕ × ℕ × ℕ)) (np ng : ℕ) (res : List CRes) : Bool :=
  G.preR.all fun r ↦ match rngH gl r with
    | some q => match q.hi with
      | .num _ => true
      | hi => (hi.vals.all (Nat.blt · np) && res.any fun x ↦ match x with
          | .lt _ b => decide (b = hi)
          | _ => false) || hiG np ng res hi
    | none => true

/-- **The shape around a loop helper with calls** (`loopShapeOk0`), its linked upper bounds with exponents by
residuals (`hiRes`). -/
noncomputable def loopShapeOkC (Cf : CFun) : Bool :=
  loopShapeOk0 Cf && hiRes Cf.frame.sig Cf.gl Cf.fn.params.length Cf.H.sig.ghosts Cf.H.res

theorem hiRes_spec {G : Mode.Sig} {gl : List (ℕ × ℕ × ℕ)} {np ng : ℕ} {res : List CRes}
    (h : hiRes G gl np ng res = true)
    {r : Mode.Rng} (hr : r ∈ G.preR) {q : CRun} (hq : rngH gl r = some q) (hn : ∀ n, q.hi ≠ .num n) :
    ((∀ v ∈ q.hi.vals, v < np) ∧ ∃ a, CRes.lt a q.hi ∈ res) ∨
      ∃ b, q.hi = .val b ∧ np ≤ b ∧ b < np + ng ∧ ∃ a, CRes.lt a (.val (GB + (b - np))) ∈ res := by
  have h1 := List.all_eq_true.mp h r hr
  rw [hq] at h1
  simp only at h1
  have hhi : q.hi = q.hi := rfl
  rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
  · simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, List.any_eq_true] at h1
    obtain ⟨h2, x, hx, h3⟩ := h1
    refine Or.inl ⟨by rw [hhi]; exact h2, ?_⟩
    match x, h3 with
    | .lt a b, h3 =>
      simp only [decide_eq_true_eq] at h3
      exact ⟨a, hhi ▸ h3 ▸ hx⟩
  · unfold hiG at h1
    split at h1
    · rename_i b hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h1
      obtain ⟨⟨h2, h3⟩, x, hx, h4⟩ := h1
      refine Or.inr ⟨b, hb, h2, h3, ?_⟩
      match x, h4 with
      | .lt a b', h4 =>
        simp only [decide_eq_true_eq] at h4
        exact ⟨a, h4 ▸ hx⟩
    · cases h1

/-- A slot the tail call passes on unchanged has the same word at the next iteration. -/
theorem slotW_pass {σ : Val} {ps args : List V} {G : List E} (hp : ps = (List.range ps.length).map V.n) {b : ℕ}
    (ha : args[b]? = some (V.n b)) (hl : args.length = ps.length) :
    slotW (args.map σ ++ G) b = slotW (ps.map σ ++ G) b := by
  have hb : b < args.length := (List.getElem?_eq_some_iff.mp ha).1
  rw [slotW_lt (by simpa using hb), slotW_lt (by simpa [← hl] using hb), slotW_get (by simpa using hb),
    List.getElem_map, (List.getElem?_eq_some_iff.mp ha).2, slotW_params' hp (by omega)]


/-- An atom whose relation reads memory only through a `load`: no range check, `touch` or `frameAddr`. -/
def rdFree : Stmt → Bool
  | .atom (.rangeCheck ..) | .atom (.touch ..) | .atom (.frameAddr ..) => false
  | _ => true

/-- A loop helper's heap check (`heapOkC`'s loop branch) states no guarantee at a word (`postQ`). -/
theorem postQ_of_loop {pows : Exec.PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) {G : Mode.Sig} {np : ℕ}
    (ht : ∃ hi ei, G.term = [(.ex (.fr 2) 0, hi)] ∧ H.sig.term = [(.val 0, ei)] ∧ parCell G np 2 = true ∧
      idxT G np hi = some ei) : H.sig.postQ = [] := by
  obtain ⟨-, ei, -, ht, -⟩ := ht
  rcases heapOkC_cases hok with ⟨-, hok⟩ | ⟨hok, -⟩
  swap
  · rw [(splitOk_spec hok).2.2.2.1] at ht; cases ht
  unfold heapOkC1 at hok
  simp only [Bool.and_eq_true, Exec.Trie.seq_eq] at hok
  obtain ⟨-, hc⟩ := hok
  split at hc
  · rw [ht] at hc
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
    exact hc.1.2
  · cases hc

/-- A call whose callee guarantees no pointer cell, each of its pointer runs' runs among its runs. -/
noncomputable def calleePtrOk (Cf : CFun) : Stmt → Bool
  | .call g _ _ => (Cf.sigOf g).postP.isEmpty && (Cf.sigOf g).postQ.isEmpty &&
      (Cf.sigOf g).postPR.all fun p ↦ runIn p.1 (Cf.sigOf g).postR
  | .callIf _ g _ => g == Cf.fn.name || (Cf.sigOf g).postP.isEmpty && (Cf.sigOf g).postQ.isEmpty &&
      (Cf.sigOf g).postPR.all fun p ↦ runIn p.1 (Cf.sigOf g).postR
  | _ => true

/-- **No pointer fact on the loop's path**: no pointer run of its own, no callee's pointer run (its pointer
cells excluded by `calleePtrOk`): the heap facts read the memory through no reader. -/
noncomputable def noPtrL (Cf : CFun) : Bool :=
  Cf.H.sig.prePR.isEmpty && Cf.H.sig.postPR.isEmpty &&
    stmtsAll (fun s ↦ match s with
      | .call g _ _ => (Cf.sigOf g).postPR.isEmpty
      | .callIf _ g _ => g == Cf.fn.name || (Cf.sigOf g).postPR.isEmpty
      | _ => true) Cf.fn.body

/-- **Each call of the body** (a conditional one of another function, not its tail `callIf`) checked by
`callChk`. -/
noncomputable def callsBL (Cf : CFun) : Bool :=
  stmtsAll (fun s ↦ match s with
    | .call g args _ => callChk Cf g args
    | .callIf _ g args => g == Cf.fn.name || callChk Cf g args
    | _ => true) Cf.fn.body

/-- A call statement of the body: a `call`, or a conditional call of another function. -/
def CallSt (body : List Stmt) (nm : String) (f : String) (args rets : List V) : Prop :=
  Stmt.call f args rets ∈ stmtsOf body ∨ (rets = [] ∧ (∃ c, Stmt.callIf c f args ∈ stmtsOf body) ∧ f ≠ nm)

theorem callsBL_chk {Cf : CFun} (hcb : callsBL Cf = true) {f : String} {args rets : List V}
    (hs : CallSt Cf.fn.body Cf.fn.name f args rets) : callChk Cf f args = true := by
  rw [callsBL, stmtsAll_eq] at hcb
  rcases hs with hs | ⟨-, ⟨c, hs⟩, hne⟩
  · exact List.all_eq_true.mp hcb _ hs
  · have := List.all_eq_true.mp hcb _ hs
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hne

theorem cptr_of {Cf : CFun} (h : stmtsAll (calleePtrOk Cf) Cf.fn.body = true) {f : String}
    {args rets : List V} (hs : CallSt Cf.fn.body Cf.fn.name f args rets) :
    ((Cf.sigOf f).postP.isEmpty && (Cf.sigOf f).postQ.isEmpty &&
      (Cf.sigOf f).postPR.all fun p ↦ runIn p.1 (Cf.sigOf f).postR) = true := by
  rw [stmtsAll_eq] at h
  rcases hs with hs | ⟨-, ⟨c, hs⟩, hne⟩
  · exact List.all_eq_true.mp h _ hs
  · have := List.all_eq_true.mp h _ hs
    simp only [calleePtrOk, Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hne

theorem noPtrL_of {Cf : CFun} (h : stmtsAll (fun s ↦ match s with
      | .call g _ _ => (Cf.sigOf g).postPR.isEmpty
      | .callIf _ g _ => g == Cf.fn.name || (Cf.sigOf g).postPR.isEmpty
      | _ => true) Cf.fn.body = true) {f : String} {args rets : List V} (hs : CallSt Cf.fn.body Cf.fn.name f args rets) :
    (Cf.sigOf f).postPR.isEmpty = true := by
  rw [stmtsAll_eq] at h
  rcases hs with hs | ⟨-, ⟨c, hs⟩, hne⟩
  · exact List.all_eq_true.mp h _ hs
  · have := List.all_eq_true.mp h _ hs
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hne

/-- **A call's callee runs' bounds have exponents** (`callsBL`'s `idxPowC`). -/
theorem callsBL_spec {Cf : CFun} (hcb : callsBL Cf = true) {f : String} {args rets : List V}
    (hs : CallSt Cf.fn.body Cf.fn.name f args rets) :
    (∀ q ∈ (Cf.sigOf f).preR, (idxPowC Cf args q.lo && idxPowC Cf args q.hi) = true) ∧
    ∀ p ∈ (Cf.sigOf f).prePR,
      (idxPowC Cf args p.1.lo && idxPowC Cf args p.1.hi) = true := by
  have := callsBL_chk hcb hs
  simp only [callChk, Bool.and_eq_true] at this
  exact ⟨List.all_eq_true.mp this.1.2, List.all_eq_true.mp this.2⟩

/-- **The tail call names its own ghosts**: each ghost monomial list the certificate gives a call of the function
itself the own ghosts' (`ghostMs`). -/
def tailG (Cf : CFun) : Bool :=
  Cf.H.gargs.all fun p ↦ !(p.1 == Cf.fn.name) || decide (p.2.2 = ghostMs Cf.H.sig.ghosts)

/-- **The kernel's checks of a loop helper on the core route**, and its ties to its mode
certificate `K`, as `CoreOk`'s: its calls' callees' heap signatures (`callsBL`), the frame walk's callee
signatures the environment's. -/
structure LoopOkC (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : heapOkC Cf.pows Cf.sigOf Cf.fn Cf.H = true
  body : loopBB Cf.fn = true
  /-- The frame walk's tables the `match`es' arms. -/
  tgt : tgtOk Cf K.code = true
  /-- The jump table's reads. -/
  jtd : jtdOk Cf K.E K.code = true
  calls : callsBL Cf = true
  top : Cf.fn.body.all topOk = true
  rdFree : (stmtsAll rdFree Cf.fn.body || noPtrL Cf) = true
  cptr : stmtsAll (calleePtrOk Cf) Cf.fn.body = true
  ders : Cf.H.ders = []
  gw : Cf.H.sig.gw = []
  nofa : noFA Cf.fn.body = true
  code : loopCodeC Cf K.code = true
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : envOk Cf.frame = true ∧ armsOk Cf.frame = true ∧ FrameAcc Cf.frame K.code
  sig : sigOkLP K.F.sig Cf.H.sig Cf.fn.params.length (tailPass Cf.fn.body) Cf.gl = true
  /-- Its tail call names its own ghosts. -/
  gtail : tailG Cf = true
  shape : loopShapeOkC Cf = true
  sigE : K.E.sigs.get K.F.entry = some K.F.sig
  fsig : Cf.frame.sig = K.F.sig
  fsigs : Cf.frame.sigs = K.E.sigs
  fentry : Cf.frame.entry = K.F.entry
  flen : Cf.frame.len = K.code.length
  xentry : Cf.X.entry = K.F.entry
  xlen : Cf.X.len = K.code.length
  dhints : Cf.d.2.2 = Cf.frame.hints
  hints : ∀ i < K.code.length, Mode.hintsAt Data.adviceHints (K.F.entry + i) =
    Mode.hintsAt Cf.frame.hints (K.F.entry + i)
  fetch : Exec.Fetches guestProgram K.F.entry K.code
  small : ∀ i (hi : i < K.code.length), SmallOps K.code[i]
  pows : Cf.pows.Ok
  fpows : Cf.frame.F.pows.Ok
  /-- Its frame walk's residual divisors are its certificate's nonzero residuals (`nzrOk`). -/
  nzrc : nzrOk Cf K.F.res K.code = true
  /-- Its contract is its mode signature's, and its callees'. -/
  hc : Cf.hc = false
  hcs : Cf.hcs = []

/-! ## The code -/

theorem callJ_spec {Cf : CFun} {a b c : ℕ} (h : callJ Cf (.jump a b c) = true) (hz : Cf.X.zeroAt a = false)
    (hsf : Cf.X.selfAt c = false) :
    Cf.X.selfAt c = false ∧ ¬ (b = 0 ∧ c = 1) ∧ jumpCallOkL Cf (.jump a b c) = true ∧
      (Cf.X.nzAt a = true ∨ (Cf.X.nextAt c = false ∧ dspNo Cf.X b c = true ∧ callIfJ Cf b = true)) := by
  have hr : ∀ (x : Bool), (!(Nat.beq b 0 && Nat.beq c 1) && x) = true → ¬ (b = 0 ∧ c = 1) ∧ x = true :=
    fun x hx ↦ by
      refine ⟨fun ⟨hb, hc⟩ ↦ ?_, by simp only [Bool.and_eq_true] at hx; exact hx.2⟩
      subst hb hc
      simp at hx
  simp only [callJ, hz, hsf, Bool.false_or, Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true,
    Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [Bool.and_assoc] at h
    obtain ⟨h2, h4⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨h4, h5⟩ := hr _ h4
    exact ⟨hsf, h4, h5, Or.inl h2⟩
  · simp only [Bool.and_assoc] at h
    obtain ⟨-, h⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hnx, h⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨h4, h⟩ := hr _ h
    obtain ⟨hdn, h⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hcj, h5⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨hsf, h4, h5, Or.inr ⟨by simpa using hnx, hdn, hcj⟩⟩

/-- **A jump in the frame of a loop helper's code**: through no dispatch's target cell, to no callee. -/
theorem callJ_self {Cf : CFun} {a b c : ℕ} (h : callJ Cf (.jump a b c) = true) (hz : Cf.X.zeroAt a = false)
    (hsf : Cf.X.selfAt c = true) :
    (∀ t f, Cf.X.pcAt b = some t → getF Cf.X.ents t = some f → Cf.X.selfAt c = false) ∧
      ∀ s, getF Cf.X.sites c = some s → s.tgt = b → Cf.X.selfAt c = false := by
  simp only [callJ, hz, hsf, Bool.false_or, Bool.not_true, Bool.and_false, Bool.false_and, Bool.true_and,
    Bool.or_false, Bool.and_eq_true] at h
  obtain ⟨hd, hj⟩ := h
  refine ⟨fun t f ht hf ↦ (jumpCallOkL_spec hj ht hf).2.2.1, fun s hs he ↦ ?_⟩
  simp only [dspNo, hs, he, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hd
  exact hd.2

theorem loopCodeC_spec {Cf : CFun} {code : List OffsetInstruction} (h : loopCodeC Cf code = true) :
    ∃ pre oc od of oc', code = pre ++ [.jump oc od of, .jump oc' 0 1] ∧ (∀ ins ∈ pre, callJ Cf ins = true) ∧
      Cf.X.zeroAt oc' = false ∧ Cf.X.nzAt oc' = true ∧ Cf.X.zeroAt oc = false ∧ Cf.X.nzAt oc = false ∧
      Cf.X.selfAt of = false ∧ Cf.X.nextAt of = true ∧ od ≠ 0 ∧ Cf.X.pcAt od = some Cf.X.entry ∧
      Cf.X.entOk Cf.X.entry Cf.fn.name = true := by
  unfold loopCodeC at h
  split at h
  · rename_i oc' od' of' oc od of pre hrev
    simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h3'⟩, h4⟩, h5⟩, h7⟩, hpt⟩, hen⟩, h8⟩ := h
    refine ⟨pre.reverse, oc, od, of, oc', ?_, fun ins hi ↦ h8 ins (List.mem_reverse.mp hi), h1, h2, h3, h3', h4, h5,
      fun h0 ↦ by simp [h0] at h7, hpt, hen⟩
    rw [← List.reverse_reverse code, hrev]
    simp
  · cases h

/-- **A `JUMP` of a loop helper's code with calls** is a call's, before the last two, its tail call's,
second to last, or its return, last. -/
theorem loopCodeC_jump {Cf : CFun} {code pre : List OffsetInstruction} {oc od of oc' : ℕ}
    (hc : code = pre ++ [.jump oc od of, .jump oc' 0 1]) (hpre : ∀ ins ∈ pre, callJ Cf ins = true) {i a b c : ℕ}
    (h : code[i]? = some (.jump a b c)) :
    (i < pre.length ∧ callJ Cf (.jump a b c) = true) ∨ (i = pre.length ∧ a = oc ∧ b = od ∧ c = of) ∨
      (i = pre.length + 1 ∧ a = oc' ∧ b = 0 ∧ c = 1) := by
  subst hc
  rcases lt_trichotomy i pre.length with hi | rfl | hi
  · rw [List.getElem?_append_left hi] at h
    exact Or.inl ⟨hi, hpre _ (List.mem_of_getElem? h)⟩
  · simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
      OffsetInstruction.jump.injEq] at h
    exact Or.inr (Or.inl ⟨rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩)
  · rw [List.getElem?_append_right (by omega)] at h
    rcases hk : i - pre.length with _ | _ | k
    · omega
    · rw [hk] at h
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        OffsetInstruction.jump.injEq] at h
      exact Or.inr (Or.inr ⟨by omega, h.1.symm, h.2.1.symm, h.2.2.symm⟩)
    · rw [hk] at h
      simp at h

/-! ## The body and its path -/

theorem loopStmtB_of {nm : String} {pre : List Stmt} (hpre : ∀ s ∈ stmtsOf pre, isBS nm s = true) {c : V} {f : String}
    {args : List V} : ∀ s ∈ stmtsOf (pre ⧺ [.callIf c f args, .ret []]), loopStmtC s = true := fun s hs ↦ by
  rcases stmts_loopB hs with hs | rfl | rfl
  · have := hpre s hs
    cases s <;> simp_all [isBS, loopStmtC]
  · rfl
  · rfl

/-! ## The heap facts -/

/-- **A loop helper's calls give nothing beyond their writes**: its callees' by `callChk`, its own by its
signature. -/
theorem loopC_evM {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {σ : Val} (rd : Reader) {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) : ∀ e ∈ es, EvM Cf.sigOf rd σ e := fun e he ↦ by
  have hs := sigLP_of hok.sig
  have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  cases e with
  | call f args rets =>
    rcases loopB_callEv hok.body hw he with hmem | hmem | ⟨rfl, -⟩
    · exact callChk_evM (callsBL_chk hok.calls (Or.inl hmem)) (by rw [hok.hcs]; rfl) rd σ
    · exact callChk_evM (callsBL_chk hok.calls (Or.inr hmem)) (by rw [hok.hcs]; rfl) rd σ
    · simp only [EvM, hself]
      refine ⟨fun k c hkc ↦ ?_, fun i m him ↦ ?_, fun p hp ↦ ?_⟩
      · rw [hs.hretM] at hkc; cases hkc
      · rw [hs.hpostV] at him; cases him
      · rw [hs.hretEq] at hp; cases hp
  | _ => trivial

theorem loopC_evM_pre {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {σ : Val} (rd : Reader) {pre es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret (pre ++ es) vs) : ∀ e ∈ pre, EvM Cf.sigOf rd σ e :=
  fun e he ↦ loopC_evM hok rd hw e (List.mem_append_left _ he)

/-- **The heap facts of an honest path of a loop helper with calls**, its parameter cells holding its
words and its termination fact holding: every event's needs written before it, its guarantees at
return. -/
theorem loopC_heap {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {σ : Val} {rd : Reader} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) (hR : ResF Cf.H σ) {s : St}
    (hP : ParAt K.F.sig Cf.fn.params.length s (Cf.fn.params.map σ)) (hT : ∀ p ∈ K.F.sig.term, LTF s p.1 p.2) :
    ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es ∧ PostOkW Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es vs := by
  have hs := sigLP_of hok.sig
  have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  have hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e := loopC_evM hok rd hw
  obtain ⟨hr, hp, -⟩ := heapOkC_sound hok.pows hok.heap hself hw hh hM (termAt_entryFP hs hP hT)
    hR (derOk_nil hok.ders rd σ) (gwOk_nil hok.gw rd σ)
  exact ⟨hr, postOkW_of (noFAW hok.nofa hw) hp⟩

/-! ## The tail call -/

/-- **An atom's relation at another reader**: one agreeing at its `load`'s cell, no other read. -/
theorem atom_holds_swap {rd rd' : Reader} {σ : Val} {a : Atom} (hf : rdFree (.atom a) = true)
    (hl : ∀ d p off, a = .load d p off → rd' (cellAt σ p off) = rd (cellAt σ p off)) (h : a.Holds rd σ) :
    a.Holds rd' σ := by
  cases a with
  | load d p off => exact ⟨h.1, (hl d p off rfl).trans h.2⟩
  | rangeCheck => simp [rdFree] at hf
  | touch => simp [rdFree] at hf
  | frameAddr => simp [rdFree] at hf
  | _ => exact h

/-- **The path's events hold at a reader agreeing with the reference at the cells written at the tail
call.** -/
theorem holds_memRd {K : Mode.Cert} {Cf : CFun} (_hok : LoopOkC K Cf) (hrf : stmtsAll rdFree Cf.fn.body = true)
    {img : MemoryImage κ} {m : Mem} {rd : Reader}
    {σ0 : Val} {pre es evs : List Ev} {cs : List Atom} {c : V} {args : List V}
    (hb : walk σ0 Cf.fn.body = .ret (pre ++ es) []) (hh0 : ∀ e ∈ pre ++ es, e.Holds img.read σ0)
    (heq : es = evs ++ Ev.inK c :: Ev.call Cf.fn.name args [] :: cs.map Ev.atom)
    (hWc : ∀ x, WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK m x)
    (hcs : ∀ a ∈ cs, stopL a = false) (hsame : ∀ y, WrK m y → rd y = img.read y) :
    ∀ e ∈ pre ++ es, e.Holds rd σ0 := by
  have hatoms : ∀ a, Ev.atom a ∈ pre ++ es → Stmt.atom a ∈ stmtsOf Cf.fn.body := fun a ha ↦
    Bridge.walk_atomS Cf.fn.body (by rw [hb]; exact ha)
  intro e he
  have h := hh0 e he
  cases e with
  | atom a =>
    refine atom_holds_swap (List.all_eq_true.mp (stmtsAll_eq _ _ ▸ hrf) _ (hatoms a he)) (fun d p off ha ↦ ?_) h
    subst ha
    have hin : Ev.atom (.load d p off) ∈ pre ++ evs := by
      rw [heq, ← List.append_assoc] at he
      rcases List.mem_append.mp he with he | he
      · exact he
      rcases List.mem_cons.mp he with he | he
      · cases he
      rcases List.mem_cons.mp he with he | he
      · cases he
      obtain ⟨a', ha', he⟩ := List.mem_map.mp he
      simp only [Ev.atom.injEq] at he
      subst he
      have := hcs _ ha'
      simp [stopL, isLoad] at this
    exact hsame _ (hWc _ (Or.inr ⟨_, hin, rfl⟩))
  | inK c' => simpa only [Ev.Holds] using h
  | call => trivial
  | skip => trivial

/-- **Written at another reader**: the cells the events write, read through a reader agreeing with `rd'`
at the cells written in `m`, where the pointer runs' cells (preconditions' and callees' guarantees')
are among the signatures' runs. -/
theorem writtenC_swap {sigOf : String → HSig} {H : HCert} {rd rd' : Reader} {σ : Val} {ws0 : List E}
    {es : List Ev} {m : Mem} (hW : ∀ x, WrittenC sigOf H rd' σ ws0 es x → WrK m x)
    (hsame : ∀ y, WrK m y → rd y = rd' y) (hpre : H.sig.preP = []) (hpreIn : ∀ p ∈ H.sig.prePR, p.1 ∈ H.sig.preR)
    (hcalls : ∀ f a r, Ev.call f a r ∈ es → ((sigOf f).postP = [] ∧ (sigOf f).postQ = []) ∧
      ∀ p ∈ (sigOf f).postPR, p.1 ∈ (sigOf f).postR) :
    ∀ x, WrittenC sigOf H rd σ ws0 es x → WrK m x := by
  intro x hx
  rcases hx with (hS | hP) | ⟨e, he, hwe⟩
  · exact hW x (Or.inl (Or.inl hS))
  · rcases hP with ⟨p, hp, -⟩ | ⟨p, hp, a, ha, w, hw, o, ho, hx⟩
    · rw [hpre] at hp; cases hp
    · have hwa : WrK m a := hW a (Or.inl (Or.inl (Or.inr ⟨p.1, hpreIn p hp, ha⟩)))
      rw [hsame a hwa] at hw
      exact hW x (Or.inl (Or.inr (Or.inr ⟨p, hp, a, ha, w, hw, o, ho, hx⟩)))
  · cases e with
    | atom a => exact hW x (Or.inr ⟨.atom a, he, hwe⟩)
    | call f a r =>
      obtain ⟨⟨hPf, hQf⟩, hPRf⟩ := hcalls f a r he
      rcases hwe with hS | hP | ⟨p, hp, -⟩
      · exact hW x (Or.inr ⟨_, he, Or.inl hS⟩)
      · rcases hP with ⟨p, hp, -⟩ | ⟨p, hp, b, hb', w, hw, o, ho, hx⟩
        · rw [hPf] at hp; cases hp
        · have hwa : WrK m b := hW b (Or.inr ⟨_, he, Or.inl (Or.inr ⟨p.1, hPRf p hp, hb'⟩)⟩)
          rw [hsame b hwa] at hw
          exact hW x (Or.inr ⟨_, he, Or.inr (Or.inl (Or.inr ⟨p, hp, b, hb', w, hw, o, ho, hx⟩))⟩)
      · rw [hQf] at hp; cases hp
    | _ => cases hwe

/-- **Written, through no reader**: with no pointer fact of the signature's or the calls' callees', the
cells the events write are the same through any reader. -/
theorem writtenC_rd {sigOf : String → HSig} {H : HCert} {rd rd' : Reader} {σ : Val} {ws0 : List E}
    {es : List Ev} (hpP : H.sig.preP = []) (hpPR : H.sig.prePR = [])
    (hc : ∀ f a r, Ev.call f a r ∈ es → (sigOf f).postP = [] ∧ (sigOf f).postPR = [] ∧ (sigOf f).postQ = []) {x : K}
    (h : WrittenC sigOf H rd σ ws0 es x) : WrittenC sigOf H rd' σ ws0 es x := by
  rcases h with (hS | hP) | ⟨e, he, hwe⟩
  · exact Or.inl (Or.inl hS)
  · rcases hP with ⟨p, hp, -⟩ | ⟨p, hp, -⟩
    · rw [hpP] at hp; cases hp
    · rw [hpPR] at hp; cases hp
  · cases e with
    | atom a => exact Or.inr ⟨.atom a, he, hwe⟩
    | call f a r =>
      obtain ⟨h1, h2, h3⟩ := hc f a r he
      rcases hwe with hS | (⟨p, hp, -⟩ | ⟨p, hp, -⟩) | ⟨p, hp, -⟩
      · exact Or.inr ⟨_, he, Or.inl hS⟩
      · rw [h1] at hp; cases hp
      · rw [h2] at hp; cases hp
      · rw [h3] at hp; cases hp
    | _ => cases hwe

/-- `PostOkW` through no reader (`writtenC_rd`), no pointer guarantee of the signature's. -/
theorem postOkW_rd {sigOf : String → HSig} {H : HCert} {rd rd' : Reader} {σ : Val} {ws0 : List E}
    {es : List Ev} {vs : List V} (hpP : H.sig.preP = []) (hpPR : H.sig.prePR = []) (hqP : H.sig.postP = [])
    (hqPR : H.sig.postPR = []) (hqQ : H.sig.postQ = [])
    (hc : ∀ f a r, Ev.call f a r ∈ es → (sigOf f).postP = [] ∧ (sigOf f).postPR = [] ∧ (sigOf f).postQ = [])
    (h : PostOkW sigOf H rd σ ws0 es vs) : PostOkW sigOf H rd' σ ws0 es vs := by
  refine ⟨⟨fun c hc' ↦ writtenC_rd hpP hpPR hc (h.1.1 c hc'), fun r hr x hx ↦ writtenC_rd hpP hpPR hc
    (h.1.2 r hr x hx)⟩, fun x hx ↦ ?_, fun x ⟨p, hp, _⟩ ↦ (by rw [hqQ] at hp; cases hp),
    fun c hc' ↦ writtenC_rd hpP hpPR hc (h.2.2.2.1 c hc'), fun r hr x hx ↦ writtenC_rd hpP hpPR hc
    (h.2.2.2.2 r hr x hx)⟩
  rcases hx with ⟨p, hp, -⟩ | ⟨p, hp, -⟩
  · rw [hqP] at hp; cases hp
  · rw [hqPR] at hp; cases hp

/-- **The entry runs' bound cells hold powers of `g`** in a memory agreeing with the reference, the
entry cells written. -/
theorem expM_of {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {fp : ℕ}
    (hfp : fp < maxCells) {G : Mode.Sig} (hx : ExpW img (expCells G) fp)
    (hw : ∀ o ∈ G.entry, m.written (fp + o) = true) (ps : List ℕ) : ExpM G ps (stOf m fp) := by
  intro o h1 _ h3 h4
  obtain ⟨e, he, hr⟩ := hx o h1
  obtain ⟨u, hu⟩ := Mem.get_of_written (hw o h3)
  exact ⟨e, he, by rw [show (stOf m fp).mem = m from rfl, show (stOf m fp).fp = fp from rfl, hu,
    rd_getA hκ ha hfp h4 hr hu]⟩

/-- **The next frame's cells a call passes on hold the same powers of `g`.** -/
theorem expM_next {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {fp fp' : ℕ}
    (hfp' : fp' < maxCells) {G : Mode.Sig} (hx : ExpW img (expCells G) fp)
    (hw' : ∀ o ∈ G.entry, m.written (fp' + o) = true) {ps : List ℕ} (hpass : ∀ o ∈ ps, Rd img fp' o = Rd img fp o) :
    ExpM G ps (stOf m fp') := by
  intro o h1 h2 h3 h4
  obtain ⟨e, he, hr⟩ := hx o h1
  obtain ⟨u, hu⟩ := Mem.get_of_written (hw' o h3)
  exact ⟨e, he, by rw [show (stOf m fp').mem = m from rfl, show (stOf m fp').fp = fp' from rfl, hu,
    rd_getA hκ ha hfp' h4 ((hpass o h2).trans hr) hu]⟩

/-- **This iteration returns what the next one does** (`Back`): the heap facts of its path taken again
at the reader of the later memory (`memRd m' img.read`), its path's events holding there (each
`load`'s cell written at the tail call), the pointer cells its writes before the tail call name written
at the tail call (so both readers agree on them), the tail call's guarantees the next iteration's. -/
theorem back_nextC {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {img : MemoryImage κ} (hκ : κ ≤ 28)
    {s s1 s' : St} (hfp1 : s1.fp = s.fp) (hle : s.mem ≤ s'.mem) (hf' : Fine (refMem img) s')
    (hu' : s'.mem.used ≤ 2 ^ κ) {σ0 : Val} {pre es evs : List Ev} {cs : List Atom} {c : V} {args : List V}
    (hb : walk σ0 Cf.fn.body = .ret (pre ++ es) []) (hh0 : ∀ e ∈ pre ++ es, e.Holds img.read σ0)
    (hR0 : ResF Cf.H σ0) (heq : es = evs ++ Ev.inK c :: Ev.call Cf.fn.name args [] :: cs.map Ev.atom)
    (hWc : ∀ x, WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x)
    (hPN : ParAt K.F.sig Cf.fn.params.length (stOf s'.mem s'.fp) (args.map σ0))
    (hP0 : ParAt K.F.sig Cf.fn.params.length (stOf s.mem s.fp) (Cf.fn.params.map σ0))
    (hT : TermAt s.mem s.fp K.F.sig) (hX : ExpM K.F.sig (expCells K.F.sig) (stOf s'.mem s.fp))
    (hcs : ∀ a ∈ cs, stopL a = false) :
    Mode.BackM s'.mem K.F.sig s1.fp s'.fp := by
  intro m' hm' _ _ hR
  have hs := sigLP_of hok.sig
  have hsigf : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  have hRdB := rdM_memRd m' img.read
  have hRimg : RdM img.read s'.mem := rdM_img hκ hf'.agree hu'
  have hWimg : RdW img.read s'.mem := rdW_img hκ hf'.agree
  have hsame : ∀ y, WrK s'.mem y → memRd m' img.read y = img.read y := by
    rintro y ⟨x, rfl, hx, hw⟩
    rw [memRd_le hm' _ hx hw, hRimg x hx hw]
  have hPN' : ParAt K.F.sig Cf.fn.params.length (stOf m' s'.fp) (args.map σ0) :=
    hPN.mono (s := stOf s'.mem s'.fp) (s' := stOf m' s'.fp) hm' rfl
  have hnext := postSet_of_retAllP hs hPN' hR hRdB.rdW
  -- the path's events
  have hpQ : Cf.H.sig.postQ = [] := postQ_of_loop hok.heap hs.term
  have hcalls : ∀ f a r, Ev.call f a r ∈ pre ++ es → ((Cf.sigOf f).postP = [] ∧ (Cf.sigOf f).postQ = []) ∧
      ∀ p ∈ (Cf.sigOf f).postPR, p.1 ∈ (Cf.sigOf f).postR := fun f a r he ↦ by
    rcases loopB_callEv hok.body hb he with hm | hm | ⟨rfl, -⟩
    · have := cptr_of hok.cptr (Or.inl hm)
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at this
      exact ⟨this.1, fun p hp ↦ runIn_mem (this.2 p hp)⟩
    · have := cptr_of hok.cptr (Or.inr hm)
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at this
      exact ⟨this.1, fun p hp ↦ runIn_mem (this.2 p hp)⟩
    · rw [hsigf]
      exact ⟨⟨hs.hpostP, hpQ⟩, hs.inPost⟩
  have hposts : PostOkW Cf.sigOf Cf.H (memRd m' img.read) σ0 (Cf.fn.params.map σ0) (pre ++ es) [] := by
    rcases Bool.or_eq_true_iff.mp hok.rdFree with hrf | hnp
    · exact (loopC_heap hok hb (holds_memRd hok hrf hb hh0 heq hWc hcs hsame) hR0 hP0 hT).2
    · simp only [noPtrL, Bool.and_eq_true, List.isEmpty_iff] at hnp
      obtain ⟨⟨hpPR, hqPR⟩, hcPR⟩ := hnp
      refine postOkW_rd hs.hpreP hpPR hs.hpostP hqPR hpQ
        (fun f a r he ↦ ⟨(hcalls f a r he).1.1, ?_, (hcalls f a r he).1.2⟩)
        (loopC_heap hok hb hh0 hR0 hP0 hT).2
      rcases loopB_callEv hok.body hb he with hm | hm | ⟨rfl, -⟩
      · simpa using noPtrL_of hcPR (Or.inl hm)
      · simpa using noPtrL_of hcPR (Or.inr hm)
      · rw [hsigf]; exact hqPR
  simp only [PostOkW, List.map_nil, List.append_nil] at hposts
  -- what the path writes, at the later memory's reader
  have hWB := writtenC_swap (es := pre ++ evs) hWc hsame hs.hpreP hs.inPre fun f a r he ↦
    hcalls f a r (by rw [heq, ← List.append_assoc]; exact List.mem_append_left _ he)
  have hWall : ∀ x, WrittenC Cf.sigOf Cf.H (memRd m' img.read) σ0 (Cf.fn.params.map σ0) (pre ++ es) x →
      WrK m' x := by
    intro x hx
    rw [heq, ← List.append_assoc] at hx
    rcases writtenC_append hx with h | ⟨e, he, hwe⟩
    · exact (hWB x h).mono hm'
    · rcases List.mem_cons.mp he with rfl | he
      · cases hwe
      rcases List.mem_cons.mp he with rfl | he
      · simp only [EvW, List.append_nil] at hwe
        rw [hsigf] at hwe
        exact hnext x hwe
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
        exact absurd hwe (no_writes_of_stopL (hcs a ha))
  have hP1 : ParAt K.F.sig Cf.fn.params.length (stOf m' s1.fp) (Cf.fn.params.map σ0) :=
    hP0.mono (s := stOf s.mem s.fp) (s' := stOf m' s1.fp) (Mem.le_trans hle hm') hfp1
  exact retAll_of_wrkP hs hP1 (fun p hp ↦ by rw [hfp1]; exact Mode.LTF.mem (Mem.le_trans hle hm') (hT p hp))
    (by rw [hfp1]; exact hX.mono (s := stOf s'.mem s.fp) (s' := stOf m' s.fp) hm' rfl)
    (fun c hc ↦ hWall _ (hposts.1.1 c hc)) (fun r hr x hx ↦ hWall x (hposts.1.2 r hr x hx))
    (rdM_memRd m' img.read) fun x hx ↦ hWall x (hposts.2.1 x hx)

theorem slotW_app_ge {l l' G : List E} (hl : l.length = l'.length) {b : ℕ} (hb : l.length ≤ b) :
    slotW (l ++ G) b = slotW (l' ++ G) b := by
  simp only [slotW, List.getD_eq_getElem?_getD, List.getElem?_append_right hb,
    List.getElem?_append_right (hl ▸ hb), hl]

theorem parAt_app {G : Mode.Sig} {np : ℕ} {s : St} {ws gs : List E} (h : ParAt G np s ws) (hl : ws.length = np) :
    ParAt G np s (ws ++ gs) := fun o ho ↦ by
  rw [h o ho, slotW_lt (by have := (parCell_spec ho).2.1; omega)]

theorem loopC_params {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) :
    Cf.fn.params = (List.range Cf.fn.params.length).map V.n :=
  heapOkC_params hok.heap

/-- **The caller's linked cells at the next iteration**: its header names the same caller's frame, each linked slot
the same word. -/
theorem glF_next {img : MemoryImage κ} {gl : List (ℕ × ℕ × ℕ)} {fp fp' : ℕ} (h1 : Rd img fp' 1 = Rd img fp 1)
    {ws ws' : List E} (hs : ∀ d b k, (d, b, k) ∈ gl → slotW ws' b = slotW ws b) (h : GlF img gl fp ws) :
    GlF img gl fp' ws' := fun d b k hm ↦ by
  obtain ⟨a, ha1, had, hL⟩ := h d b k hm
  refine ⟨a, h1.trans ha1, had, ?_⟩
  rwa [hs d b k hm]

/-- **The tail call's ghost words are the own ghosts'** (`tailG`), as many as the function has. -/
theorem gargsW_tail {Cf : CFun} (hg : tailG Cf = true) {σ : Val} {args : List V}
    (hn : (gargsOf Cf.H.gargs Cf.fn.name args).length = Cf.H.sig.ghosts) :
    gargsW Cf.H σ Cf.fn.name args = ownG Cf.H.sig σ := by
  have hms : gargsOf Cf.H.gargs Cf.fn.name args = ghostMs Cf.H.sig.ghosts := by
    unfold gargsOf at hn ⊢
    split
    · rename_i p hp
      have hpm := List.mem_of_find?_eq_some hp
      have hpn := List.find?_some hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpn
      have := List.all_eq_true.mp hg p hpm
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq] at this
      exact this.resolve_left (fun h ↦ h hpn.1)
    · rename_i hp
      rw [hp] at hn
      simp only [List.length_nil] at hn
      simp [ghostMs, ← hn]
  unfold gargsW ownG
  rw [hms]
  simp [ghostMs, valW_baseC, vw]

/-- **A loop's tail call taken**, into frame `s.fp + S` of the honest tree, for a loop helper with
calls, pointer runs included. -/
theorem tail_nextC {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {img : MemoryImage κ} (hκ : κ ≤ 28)
    {s s1 s' : St} (hfp0 : s.fp < maxCells) (hfp1 : s1.fp = s.fp) (hle1 : s.mem ≤ s1.mem)
    (hf' : Fine (refMem img) s') (hle' : s1.mem ≤ s'.mem) (hu' : s'.mem.used ≤ 2 ^ κ) {S : ℕ}
    (hfpS : s'.fp = s.fp + S) (hS : S < 2 ^ 30)
    (hpc' : s'.pc = K.F.entry) (hentry : EntryFr img Cf.frame.sig s') (hr0 : Rd img s'.fp 0 = Rd img s1.fp 0)
    (hr1 : Rd img s'.fp 1 = Rd img s1.fp 1) (hTE : TermEntry K s') (hjt : RW s' (Mode.jtRng K.E))
    (hwE : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true)
    (hso : ∀ o, K.F.sig.self = some o → o < 2 ^ 28)
    (hent0 : 0 ∈ Cf.frame.sig.entry) (hent1 : 1 ∈ Cf.frame.sig.entry)
    {σ0 : Val} {pre es evs : List Ev} {cs : List Atom} {c : V} {args : List V}
    (hb : walk σ0 Cf.fn.body = .ret (pre ++ es) []) (hh0 : ∀ e ∈ pre ++ es, e.Holds img.read σ0)
    (hR0 : ResF Cf.H σ0) (hgl0 : GlF img Cf.gl s.fp (Cf.fn.params.map σ0 ++ ownG Cf.H.sig σ0))
    (heq : es = evs ++ Ev.inK c :: Ev.call Cf.fn.name args [] :: cs.map Ev.atom)
    (hrw0 : ReadsOkC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ es))
    (hWc : ∀ x, WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x)
    (hnargs : ∀ k (hk : k < args.length), Rd img (s.fp + S) (2 + k) = some (σ0 args[k]))
    (hargs : args.length = Cf.fn.params.length)
    (hP0 : ParAt K.F.sig Cf.fn.params.length (stOf s.mem s.fp) (Cf.fn.params.map σ0))
    (hT : TermAt s.mem s.fp K.F.sig) (hX : ExpM K.F.sig (expCells K.F.sig) (stOf s'.mem s.fp))
    (hXN : ExpM K.F.sig (tailPass Cf.fn.body) (stOf s'.mem s'.fp)) (hcs : ∀ a ∈ cs, stopL a = false)
    (hpass : ∀ b, 2 + b ∈ tailPass Cf.fn.body → args[b]? = some (V.n b)) :
    s'.pc = K.F.entry ∧ (∀ o ∈ K.F.sig.entry, s'.mem.written (s'.fp + o) = true) ∧
      (∀ o < 2, ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u) ∧
      Mode.BackM s'.mem K.F.sig s1.fp s'.fp ∧ Mode.Holds s' (entryAbs K.E K.F.sig) := by
  have hs := sigLP_of hok.sig
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  have hwN : ∀ o ∈ K.F.sig.entry, s'.mem.written (s'.fp + o) = true := fun o ho ↦ hentry.w o (hok.fsig ▸ ho)
  have hTN : ∀ p ∈ K.F.sig.term, LTF (stOf s'.mem s'.fp) p.1 p.2 :=
    hTE K.F.sig (by rw [hpc']; exact hok.sigE) hwN
  have hPN : ParAt K.F.sig Cf.fn.params.length (stOf s'.mem s'.fp) (args.map σ0) :=
    parAt_of hκ hf'.agree hf'.fp hwN fun b hb' ↦ by
      have hba : b < args.length := by rw [hargs]; exact hb'
      rw [hfpS, slotW_get (by simpa using hba)]
      simpa using hnargs b hba
  have hsigf : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  have hb0 : s.fp < 2 ^ 28 := by unfold maxCells at hfp0; omega
  refine ⟨hpc', hwN, fun o ho ↦ ?_, back_nextC hok hκ hfp1 hle hf' hu' hb hh0 hR0 heq hWc hPN hP0 hT hX hcs, ?_⟩
  · -- the header copied
    have hwo : ∀ o ∈ K.F.sig.entry, s'.mem.written (s1.fp + o) = true := fun o ho ↦ by
      rw [hfp1]; exact written_mono hle (hwE o ho)
    interval_cases o
    · exact hdr_copy hκ hf'.agree hr0 (hwo 0 (hok.fsig ▸ hent0)) (hwN 0 (hok.fsig ▸ hent0)) (by omega)
        (by rw [hfpS]; omega)
    · exact hdr_copy hκ hf'.agree hr1 (hwo 1 (hok.fsig ▸ hent1)) (hwN 1 (hok.fsig ▸ hent1)) (by omega)
        (by rw [hfpS]; omega)
  · -- the next iteration's entry facts: the tail call's preconditions
    have hreq := hrw0 (pre ++ evs ++ [Ev.inK c]) (.call Cf.fn.name args []) (cs.map Ev.atom)
      (by rw [heq]; simp)
    have hreq := callReq_pre hok.ders hreq
    have hreqS := hreq.2.1
    have hreqP := hreq.2.2
    have hga : gargsW Cf.H σ0 Cf.fn.name args = ownG Cf.H.sig σ0 :=
      gargsW_tail hok.gtail (by rw [hreq.1, hsigf])
    rw [hsigf, hga] at hreqS hreqP
    have hw1 : s'.mem.written (s'.fp + 1) = true := hwN 1 (hok.fsig ▸ hent1)
    have hpN := loopC_params hok
    -- a linked slot: a ghost's, copied, or a parameter's the tail call passes on
    have hsl : ∀ d b k, (d, b, k) ∈ Cf.gl →
        slotW (args.map σ0 ++ ownG Cf.H.sig σ0) b = slotW (Cf.fn.params.map σ0 ++ ownG Cf.H.sig σ0) b := by
      intro d b k hm
      rcases hs.pass _ hm with hb | hb
      · exact slotW_app_ge (by simp [hargs]) (by simpa [hargs] using hb)
      · exact slotW_pass hpN (hpass b hb) hargs
    have hLN : LinkM (stOf s'.mem s'.fp) Cf.gl (args.map σ0 ++ ownG Cf.H.sig σ0) :=
      linkM_of hκ hf'.agree hf'.fp hw1 (glF_next (by rw [hr1, hfp1]) hsl hgl0)
    -- a linked upper bound's exponent, by its residual
    have hE : ∀ r ∈ K.F.sig.preR, ∀ q, rngH Cf.gl r = some q →
        ∃ y, rep ((idxC q.hi).valW (slotW (args.map σ0 ++ ownG Cf.H.sig σ0))) = some y := by
      intro r hr q hq
      obtain ⟨d0, b0, lo0, hi, -, -, hhi, -, -, -, hqe⟩ := rngH_spec hq
      have hqh : q.hi = hi := by rw [hqe]
      rw [hqh]
      rcases hiH_spec hhi with ⟨n, -, rfl, hn⟩ | ⟨d', b', k', -, -, hl', hvw, hvals⟩
      · exact ⟨n, by rw [idxC]; exact rep_const (by rw [capE_eq]; exact hn)⟩
      · have hsh := ((Bool.and_eq_true _ _).mp hok.shape).2
        rw [hok.fsig] at hsh
        rcases hiRes_spec hsh hr hq (fun n hn ↦ by
          rw [hqh] at hn; rw [hn] at hvals; simp [CIdx.vals] at hvals) with ⟨hlt, a, ha⟩ | ⟨b, hb, hnb, hbg, a, ha⟩
        · rw [hqh] at hlt ha
          have hb' : b' < Cf.fn.params.length := hlt b' (by rw [hvals]; exact List.mem_singleton_self _)
          obtain ⟨ya, yb, -, hyb, -⟩ := hR0 _ ha
          refine ⟨yb, ?_⟩
          rw [hvw] at hyb
          rw [hvw, hsl _ _ _ (lookup_memL hl'), slotW_lt (by simpa using hb'), slotW_params' hpN hb']
          exact hyb
        · -- a ghost slot's word, its value `GB + b - np`'s
          obtain ⟨ya, yb, -, hyb, -⟩ := hR0 _ ha
          refine ⟨yb, ?_⟩
          rw [hqh] at hb
          rw [hb]
          have hl : (args.map σ0).length = Cf.fn.params.length := by simp [hargs]
          have hg : slotW (args.map σ0 ++ ownG Cf.H.sig σ0) b = vw σ0 (GB + (b - Cf.fn.params.length)) := by
            unfold slotW
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
            simp only [ownG, List.getElem?_map, List.getElem?_range (show b - Cf.fn.params.length < Cf.H.sig.ghosts
              by omega), Option.map_some, Option.getD_some]
          simp only [idxC, valW_baseC] at hyb ⊢
          rw [hg]
          exact hyb
    obtain ⟨hpreN, hpreRN, hprePN⟩ := entry_of_preP hs (parAt_app hPN (by simp [hargs])) hLN hTN hXN
      (W := WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ evs ++ [Ev.inK c]))
      (fun x hx ↦ hWc x (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) hx)) hreqS hreqP
      (rdM_img hκ hf'.agree hu') hE
    refine holds_entryP hwN
      (fun m hm' ↦ Mode.HW.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hpreN m hm'))
      hjt (fun r hr ↦ Mode.RW.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hpreRN r hr))
      (fun q hq ↦ Mode.PW.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hprePN q hq))
      (fun p hp ↦ Mode.LTF.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hTN p hp))
      (fun o ho ↦ ?_)
    obtain ⟨hwo, hro⟩ := hentry.self o (hok.fsig ▸ ho)
    obtain ⟨u, hu⟩ := Mem.get_of_written hwo
    exact ⟨hwo, by rw [hu, rd_get hκ hf' (hso o ho) hro hu]⟩

/-! ## A call -/

/-- **A call's `JUMP` taken** in a loop helper with calls: `frameSpec_core`'s call case. -/
theorem call_stepC {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {C : Ctx} (hK : CodeOk C K)
    {img : MemoryImage κ} (hκ : κ ≤ 28) {Y : St → Prop} (hU : UsedNext C img Y)
    {s s1 s' : St} {i : ℕ} (hi : i < K.code.length) (hpc : s.pc = K.F.entry + i) (hYs : Y s)
    (hs : Fine (refMem img) s) (hat : CoreIn img Cf K.code i s.mem s.fp)
    (hxw : ExpW img Cf.xc s.fp) {σ0 : Val} (hσ0 : HonF img Cf s.fp σ0)
    (hT : TermAt s.mem s.fp K.F.sig) (hjtR : ∀ s', s.mem ≤ s'.mem → RW s' (Mode.jtRng K.E))
    (e1 : (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (he1 : ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hm : Moves (refMem img) s s1) (e' : runOp C s1 (opOfOff K.code[i]) = .ok s') (hf' : Fine (refMem img) s')
    (hle' : s1.mem ≤ s'.mem) (hjo : JumpOut img Cf.frame K.code (∃ c, K.code[i]? = some (.jump c 0 1)) s1 s')
    {oc od of : ℕ} (hci : K.code[i]? = some (.jump oc od of)) (h0 : s1.mem.get (s1.fp + od) = some (ofK (g ^ s'.pc)))
    (h1 : s1.mem.get (s1.fp + of) = some (ofK (g ^ s'.fp))) (hpcs : s'.pc < C.ops.size)
    (hsz : C.ops.size ≤ 2 ^ 30) (hcj : callJ Cf (.jump oc od of) = true) (hz : Cf.X.zeroAt oc = false)
    (hsfc : Cf.X.selfAt of = false) (hcn : ∃ v, s1.mem.get (s1.fp + oc) = some v ∧ v ≠ 0) {Ct : Mode.Cts}
    (hCt : Mode.ModeCts Ct K) :
    Out Ct K (CoreAt img Cf K.code) i s1 s' := by
  obtain ⟨-, hentw, hheap⟩ := hat
  obtain ⟨hsf', hr01, hcall, hkind⟩ := callJ_spec hcj hz hsfc
  have hsh := LoopShape0.of_ok ((Bool.and_eq_true _ _).mp hok.shape).1
  have hend := hsh.len
  obtain ⟨pre0, c0, args0, hbody, hargs0, hpre0⟩ := loopBB_spec hok.body
  have hst : ∀ s ∈ stmtsOf Cf.fn.body, loopStmtC s = true := by rw [hbody]; exact loopStmtB_of hpre0
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hpar := heapOkC_params hok.heap
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  have hwE : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦ hentw o (hok.fsig ▸ ho)
  have hPs : ∀ {σ : Val}, HonF img Cf s.fp σ → ParAt K.F.sig np (stOf s.mem s.fp) (Cf.fn.params.map σ) :=
    fun hσ ↦ parAt_of hκ hs.agree hs.fp hwE (hws0 hσ)
  have hrwOf : ∀ σ pre es vs rd, HonF img Cf s.fp σ → walk σ Cf.fn.body = .ret (pre ++ es) vs →
      (∀ e ∈ pre ++ es, e.Holds rd σ) → ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es :=
    fun σ pre es vs rd hσ hb hh0 ↦ readsAt_of_C (loopC_heap hok hb hh0 (hσ.res hxw) (hPs hσ) hT).1
  have hhd : ∀ j, (Cf.d.2.2.lookup (Cf.X.entry + j)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) :=
    fun j ↦ by rw [lookupD_hintsAt, hok.dhints, hok.xentry, hok.fentry]
  have hlen : Cf.frame.len = K.code.length := hok.flen
  have hcode : K.code[i] = .jump oc od of := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hci)
  have hsm := hok.small i hi
  rw [hcode] at hsm
  obtain ⟨soc, sod, sof⟩ := hsm
  have hfw : fwdJ Cf.X i oc od of = false := by simp [fwdJ, hsf']
  obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
  -- the call's pairing: a `call` on a nonzero constant, or a conditional call (`callIfJ`), entered
  obtain ⟨f, args, rets, st, t, o, pos', hcS, hsite, hpt, hentF, hfo, hat', as, hpairs, hkC⟩ :
      ∃ f args rets st t o pos', CallSt Cf.fn.body Cf.fn.name f args rets ∧ Cf.X.siteAt of args rets = some st ∧
        Cf.X.pcAt od = some t ∧ Cf.X.entOk t f = true ∧ Cf.X.fwdOff i st.r = some o ∧
        pairAt Cf.P Cf.fn.body K.code Cf.d o = some pos' ∧ ∃ as : List Atom,
        List.Forall₂ (Pairs Cf.X) (as.filter flowAtom)
          (((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).filter isaFlowHint) ∧
        ∀ {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader}, HonF img Cf s.fp σ →
          walk σ Cf.fn.body = .ret (pre ++ es) vs → walk σ pos = .ret es vs →
          ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es →
          ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
            es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧ walk σ pos' = .ret es' vs ∧
            (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
            (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
              WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
              ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x := by
    rcases hkind with hnz | ⟨hnx, hdn, hcj'⟩
    · obtain ⟨f, args, rets, st, t, o, pos', hcS, hsite, hpt, hentF, hfo, hat', as, hpairs, hkC⟩ :=
        pair_callLC hok.pair hpos hci hz hnz hfw hr01 hsh.main hsf' hst hsh.cif
      exact ⟨f, args, rets, st, t, o, pos', Or.inl hcS, hsite, hpt, hentF, hfo, hat', as, hpairs,
        fun _ _ hwp' hrw ↦ hkC hwp' hrw⟩
    -- a conditional call: its target another function's entry
    obtain ⟨t0, ht0, hf0⟩ : ∃ t0, Cf.X.pcAt od = some t0 ∧ getF Cf.X.ents t0 ≠ some Cf.fn.name := by
      unfold callIfJ at hcj'
      split at hcj'
      · rename_i t0 ht0
        refine ⟨t0, ht0, fun he ↦ ?_⟩
        rw [he] at hcj'
        simp at hcj'
      · cases hcj'
    have hd : ∀ s, getF Cf.X.sites of = some s → s.tgt ≠ od := fun s hs he ↦ by
      simp [dspNo, hs, he, ht0] at hdn
    obtain ⟨f, args, rets, st, t, o, pos', hsite, hpt, hentF, hfo, hat', as, hpairs, hkA⟩ :=
      pair_callAny hok.pair hpos hci hz hfw hr01 hsf' (fun _ _ _ _ ↦ hnx) hd
    have hfn : f ≠ Cf.fn.name := fun h ↦ by
      rw [ht0, Option.some.injEq] at hpt
      subst hpt
      exact hf0 (h ▸ entOk_spec hentF)
    rcases hkA with ⟨hcS, hkA⟩ | ⟨c, hcS, hloc, rfl, hkA⟩
    · exact ⟨f, args, rets, st, t, o, pos', Or.inl hcS, hsite, hpt, hentF, hfo, hat', as, hpairs,
        fun _ _ hwp' hrw ↦ hkA hwp' hrw⟩
    refine ⟨f, args, [], st, t, o, pos', Or.inr ⟨rfl, ⟨c, hcS⟩, hfn⟩, hsite, hpt, hentF, hfo, hat', as, hpairs,
      fun {σ pre es vs rd} hσ hb' hwp' hrw ↦ ?_⟩
    obtain ⟨evs, cs, es', rfl, hwp2, hcs, hasin, hevM, hW'⟩ := hkA hwp' hrw
    obtain ⟨v, hv, hv0⟩ := hcn
    have hcond := hσ.jc.cond _ _ hb' c (by simp)
    rw [hloc] at hcond
    have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine soc (by rw [hm.fp]; exact hcond) hv, h0])
    refine ⟨evs ++ [Ev.inK c], cs, es', by simp [hσc], hwp2, hcs, fun a ha ↦ by simp [hasin a ha],
      evM_app hevM (evM_inK_cons evM_nil), fun x hx ↦ ?_⟩
    rcases hW' x (writtenC_noAtom (e := Ev.inK c) (pre := pre ++ evs) (fun a h ↦ by cases h)
        (fun f a r h ↦ by cases h) (by simpa [List.append_assoc] using hx)) with h | ⟨a, ha, hfa, hma, hwa⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, hfa, by simp [hma], hwa⟩
  rw [hhd i] at hpairs
  obtain ⟨hout, ht30, -, G, st', hG, hst', hr30, hfitC⟩ := jumpCallOkL_spec hcall hpt (entOk_spec hentF)
  obtain ⟨hst'', hna, hnr'⟩ := siteAt_spec hsite
  rw [hst''] at hst'
  cases hst'
  rw [hna, hnr'] at hfitC
  -- the callee's guarantees (`fitBLpost`), its header and self cells, in both cases
  have hpostC : fitBLpost G (Cf.sigOf f) args.length rets.length = true := by
    rcases Bool.or_eq_true_iff.mp hfitC with h | h
    · exact fitBLpost_of h
    · simp only [Bool.and_eq_true] at h; exact h.1.2
  obtain ⟨hGself, hG0, hG1⟩ : (match G.self with
      | some o => decide (o < 2 ^ 28)
      | none => true) = true ∧ 0 ∈ G.entry ∧ 1 ∈ G.entry := by
    rcases Bool.or_eq_true_iff.mp hfitC with h | h
    · have h := FitBL.of_ok h
      exact ⟨h.self, List.contains_iff_mem.mp h.ent0, List.contains_iff_mem.mp h.ent1⟩
    · simp only [Bool.and_eq_true] at h
      have h := FitB.of_ok h.1.1
      exact ⟨h.self, List.contains_iff_mem.mp h.ent0, List.contains_iff_mem.mp h.ent1⟩
  simp only [fitBLpost, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hpostC
  obtain ⟨⟨⟨⟨hhpostP, hhpostPR⟩, ⟨-, hhpostQ⟩⟩, hhpost⟩, hhpostR⟩ := hpostC
  have hpe : s'.pc = t := by
    have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.jc.pcw od t hpt) h0
    exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
  -- the walk's split at the call, the callee frame
  have hsplit {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader} (hσ : HonF img Cf s.fp σ)
      (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs) (hwp : walk σ pos = .ret es vs)
      (hh0 : ∀ e ∈ pre ++ es, e.Holds rd σ) :=
    have hrw := hrwOf σ pre _ vs rd hσ hb hh0
    call_split hκ hm sof h1 hsite hσ hb hrw (hkC hσ hb hwp hrw)
  obtain ⟨evs, cs, es', heq, hwp', hcs, hasin, hevM, hW', hreq, kfp, hfpE, hwsE, hk0, hk1⟩ :=
    hsplit hσ0 hb hwp hh0
  obtain ⟨hpwR, hpwPR⟩ := callsBL_spec hok.calls hcS
  have hexp : ∀ j, idxPowC Cf args j = true →
      IdxEx (slotW (args.map σ0)) j := fun j h ↦ by
    simpa using idxPowC_rep (ws := []) hok.pows hok.top hb hh0 hσ0.par hxw (hσ0.res hxw) h
  have hWs1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s1.mem x := by
    intro x hx
    rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
    · exact (hW _ h).mono hm.le
    · subst heq
      exact flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
        (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa
  cases hjo with
  | ret _ _ hr =>
    obtain ⟨c', hc'⟩ := hr
    rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
    exact absurd ⟨hc'.2.1, hc'.2.2⟩ hr01
  | «local» t' _ _ hpc'' hat'' =>
    exfalso
    have ht' : K.code.length ≤ t' := by
      by_contra hlt
      exact hout ⟨by rw [← hpe, hpc'']; omega, by rw [← hpe, hpc'', hlen]; omega⟩
    obtain ⟨cur, pend, h0', hh0'⟩ := hat''
    obtain ⟨rfl, rfl⟩ := preF_end hacc ht' h0'
    rcases hh0' with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
    · cases hA
    · cases hg'
  | halt _ hfpo _ => exact absurd hfpo (by simp [hsh.fp1])
  | tail e _ hpc'' _ _ _ _ _ =>
    exfalso
    exact hout ⟨by rw [← hpe, hpc''], by rw [← hpe, hpc'', hlen]; omega⟩
  | call G' t' _ htl hsig hentry hrr hcont =>
    rw [hpe, hG, Option.some.injEq] at hsig
    subst hsig
    -- the return offset
    have ht'r : st.r = K.F.entry + t' := by
      have h2 := hrr
      unfold retRegs at h2
      rw [show img.read (g ^ s'.fp * addressOfIndex 0) = Rd img s'.fp 0 from rfl, hk0] at h2
      simp only [Option.bind_some] at h2
      obtain ⟨fw, -, hfw'⟩ := Option.map_eq_some_iff.mp h2
      simp only [Registers.mk.injEq, limb_ofK] at hfw'
      rw [← hok.fentry]
      exact gpow_inj (by omega) (by omega) hfw'.1
    obtain ⟨-, hoo⟩ := fwdOff_spec hfo
    rw [hok.xentry, ht'r, show K.F.entry + t' - K.F.entry = t' by omega] at hoo
    subst hoo
    have hsigK : K.E.sigs.get s'.pc = some G := by rw [← hok.fsigs, hpe]; exact hG
    refine .call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_, hentry.w, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
      rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
    · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
      rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
    · -- the callee's entry facts
      rw [Mode.preAt_none (hCt.2 _ _ hsigK)]
      refine holds_entryAbs ?_ fun o ho ↦ ?_
      swap
      · -- its self cell (a loop's)
        have ho28 : o < 2 ^ 28 := by rw [ho] at hGself; simpa using hGself
        obtain ⟨hwo, hro⟩ := hentry.self o ho
        obtain ⟨u, hu⟩ := Mem.get_of_written hwo
        exact ⟨hwo, by rw [hu, rd_get hκ hf' ho28 hro hu]⟩
      rcases Bool.or_eq_true_iff.mp hfitC with hfit | hfit
      · have hf := FitBL.of_ok hfit
        have hGpreP := hf.preP
        have hGpre := hf.pre
        have hGpreR := hf.preR
        have hhgh := hf.ghosts
        simp only [Bool.and_eq_true, List.all_eq_true] at hGpreP hGpre hGpreR
        have hSG : ∀ {m : Mode.Mono}, monoS G args.length true m = true →
            SlotGet s' (args.map σ0) m.bs := fun hm' ↦
          slotGet_of hκ hf'.agree hf'.fp (fun b hb' ↦ by
            rw [hwsE b (by omega), List.map_append, slotW_lt (by simpa using hb')]) hentry.w hm'
        have hW1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x :=
          fun x hx ↦ (hWs1 x hx).mono hle'
        obtain ⟨hgl, ⟨hrpre, hrpreR⟩, hrptr⟩ := callReq_pre hok.ders hreq
        have hga : gargsW Cf.H σ0 f args = [] := by
          rw [← List.length_eq_zero_iff]
          simp only [gargsW, List.length_map, hgl]
          simpa using hhgh
        rw [hga, List.append_nil] at hrpre hrpreR hrptr
        refine ⟨fun o ho ↦ hentry.w o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
          fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), fun m hm' ↦ ?_,
          fun r hr ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ (by cases hp), fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
          fun q hq ↦ ?_, fun q hq ↦ (by cases hq)⟩
        · rcases Bool.or_eq_true_iff.mp (hGpre m hm') with hc | hc
          · obtain ⟨hmS, hc⟩ := Bool.and_eq_true_iff.mp hc
            split at hc
            · rename_i c hmc
              obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
              rw [CCell.beq_eq hbeq] at hc'
              exact slot_hw hmc (hSG hmS) (hW1 _ (hrpre c hc'))
            · cases hc
          · unfold hpIn at hc
            split at hc
            · rename_i q d hqd
              simp only [Bool.and_eq_true] at hc
              obtain ⟨⟨hsl, hcl⟩, hps⟩ := hc
              obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hps
              simp only [Bool.and_eq_true, List.contains_iff_mem] at hpp
              obtain ⟨hpb, hko⟩ := hpp
              have h2 : 2 ≤ q := by
                simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
              have hu' : s'.mem.used ≤ 2 ^ κ :=
                hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) he1 hm e'
              obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcl
              rw [CCell.beq_eq hbeq] at hc'
              rw [hpOf_spec hqd]
              refine hp_hw (s := s') hκ hf'.agree hu' h2 (hSG (monoS_fr hsl)) (hW1 _ (hrpre _ hc')) fun w hw ↦ ?_
              refine hW1 _ (hrptr _ (Or.inl ⟨p', hp', w, ?_, m.k, hko, rfl⟩))
              rw [CCell.beq_eq hpb, hrd]
              exact hw
            · cases hc
        · rcases List.mem_cons.mp hr with rfl | hr
          · exact hjtR s' (Mem.le_trans hm.le hle')
          rcases Bool.or_eq_true_iff.mp (hGpreR r hr) with h0 | h0
          · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
            rcases Bool.or_eq_true_iff.mp h with h | h
            · obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
              unfold rngIs at hrq
              split at hrq
              · rename_i q' hq'
                obtain rfl := of_decide_eq_true hrq
                exact slot_rw hq' (hSG hmS) fun x hx ↦ hW1 x (hrpreR q' hq x hx)
              · cases hrq
            · split at h
              · rename_i c l hmc hl
                exact pts_slot hmc hl (hSG hmS) fun p hp ↦ by
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
                  rw [← CCell.beq_eq hbeq]
                  exact hW1 _ (hrpre c' hc')
              · cases h
          · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
            obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
            unfold rngXIs at hrq
            split at hrq
            · rename_i q' hq'
              have hqq : q' = q := of_decide_eq_true hrq
              subst hqq
              have hpw := Bool.and_eq_true_iff.mp (hpwR q' hq)
              exact slot_rwX hq' (hSG hmS) (hexp _ hpw.1) (hexp _ hpw.2) fun x hx ↦ hW1 x (hrpreR q' hq x hx)
            · cases hrq
        · exact Mode.LTF.mono (s := Mode.stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl
            (hTE G hsigK hentry.w p hp)
        · obtain ⟨⟨hmS, hpr⟩, hrr⟩ := hGpreP q hq
          obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hpr
          simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hpp
          obtain ⟨hrq, hos⟩ := hpp
          split at hrq
          · rename_i q' hq'
            have hpq : q' = p'.1 := of_decide_eq_true hrq
            obtain ⟨q2, hq2, hrr'⟩ := List.any_eq_true.mp hrr
            unfold rngXIs at hrr'
            rw [hq'] at hrr'
            have hq2e : q' = q2 := of_decide_eq_true hrr'
            subst hq2e
            have hpw := Bool.and_eq_true_iff.mp (hpwPR p' hp')
            rw [← hpq] at hpw
            have hu' : s'.mem.used ≤ 2 ^ κ :=
              hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) he1 hm e'
            refine slot_pwX (s := s') hκ hf'.agree hu' hq' (hSG hmS) (hexp _ hpw.1) (hexp _ hpw.2)
              (fun x hx ↦ hW1 x (hrpreR q' hq2 x hx)) fun x hx ↦ ?_
            obtain ⟨a, ha, hpa⟩ := hx
            refine hW1 x (hrptr x (Or.inr ⟨p', hp', a, ?_⟩))
            rw [← hpq, ← hos, hrd]
            exact ⟨ha, hpa⟩
          · cases hrq
      -- a callee naming ghosts: the caller's cells at its pointer bases (`hpBs`), as the function route's
      simp only [Bool.and_eq_true] at hfit
      obtain ⟨⟨hfit, -⟩, hpa⟩ := hfit
      exact entry_fitB hκ hf' (Mem.le_trans hm.le hle') (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) he1 hm e')
        hentry hwsE hk1 hG1 hentw hσ0 hok.pows hok.top hb hh0 hrd (FitB.of_ok hfit) hpa (callReq_pre hok.ders hreq)
        (fun x hx ↦ (hWs1 x hx).mono hle')
        (fun q hq ↦ ⟨idxPowC_rep hok.pows hok.top hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwR q hq)).1,
          idxPowC_rep hok.pows hok.top hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwR q hq)).2⟩)
        (fun p hp ↦ ⟨idxPowC_rep hok.pows hok.top hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwPR p hp)).1,
          idxPowC_rep hok.pows hok.top hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwPR p hp)).2⟩)
        (hjtR s' (Mem.le_trans hm.le hle')) (fun p hp ↦ hTE G hsigK hentry.w p hp)
    · -- resumed once the callee guarantees its signature
      intro m hm0 hwf hu hfpE hfpC hP hT
      rw [Mode.postAt_none (hCt.2 _ _ hsigK)] at hP
      obtain ⟨hR, hL, hLP⟩ := hP
      refine ⟨by rw [Mode.stOf, hm.fp]; exact hxw, fun m' hm' ham' ↦ ?_⟩
      have hle0 : s.mem ≤ m' := Mem.le_trans hm.le (Mem.le_trans hle' (Mem.le_trans hm0 hm'))
      refine ⟨?_, fun o' ho' ↦ ?_, fun σ hσ ↦ ?_⟩
      · have := hcont { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }
          ⟨ham', Prover.Exec.Dlog.ok_empty, Prover.Exec.Dlog.small_empty, hfpC⟩ rfl rfl
          (Mem.le_trans hle' (Mem.le_trans hm0 hm')) (fun o' ho' ↦ written_mono hm' (hR.1 o' ho'))
        exact atF_mono (s := { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }) (Mem.le_refl _) rfl this
      · show m'.written (s1.fp + o') = true
        rw [hm.fp]; exact written_mono hle0 (hentw o' ho')
      · change HonF img Cf s1.fp σ at hσ
        rw [hm.fp] at hσ
        obtain ⟨pos2, pre2, es2, vs2, rd2, hrd2, hpos2, hb2, hwp2, hh2, -, hW2⟩ := hheap σ hσ
        rw [hpos, Option.some.injEq] at hpos2
        subst hpos2
        obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hevM2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
          hsplit hσ hb2 hwp2 hh2
        refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hrd2, hat',
          by simpa using hb2, hwp2', by simpa using hh2, loopC_evM_pre hok _ (by simpa using hb2), fun y hy ↦ ?_⟩
        refine resume_wrk hκ hs hm hle0 (Mem.le_trans hle' (Mem.le_trans hm0 hm')) e1 hpairs hσ hb2
          hW2 hW2' hcs2 (fun hwe ↦ ?_) hy
        -- the callee's guarantees
        refine post_wrk hκ ham' hm' hf'.fp hwsE2 hrd2 hR hL hLP hhpost (fun q hq ↦ ?_)
          (fun p hp ↦ Bool.or_eq_true_iff.mpr (.inl (hhpostP p hp))) hhpostPR (fun p hp ↦ by rw [hhpostQ] at hp; cases hp) hwe
        rcases Bool.or_eq_true_iff.mp (hhpostR q hq) with h | h
        · obtain ⟨r, hr, hx⟩ := List.any_eq_true.mp h
          exact Bool.or_eq_true_iff.mpr (.inl (List.any_eq_true.mpr ⟨r, hr, Bool.or_eq_true_iff.mpr (.inl hx)⟩))
        · exact Bool.or_eq_true_iff.mpr (.inr h)

/-! ## The frame interface -/

/-- **A loop helper with calls on the core route meets the frame interface**, for `CoreAt`. -/
theorem frameSpec_loopC {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) (hU : UsedNext C img Y) {Ct : Mode.Cts} (hCt : Mode.ModeCts Ct K) :
    FrameSpec C (refMem img) Y Ct K (CoreAt img Cf K.code) := by
  obtain ⟨pre0, c0, args0, hbody, hargs, hpre0⟩ := loopBB_spec hok.body
  have hst : ∀ s ∈ stmtsOf Cf.fn.body, loopStmtC s = true := by rw [hbody]; exact loopStmtB_of hpre0
  have hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true := fun s _ ↦ by cases s <;> rfl
  have hnd : ∀ x fs a r, Stmt.dispatch x fs a r ∉ stmtsOf Cf.fn.body := fun _ _ _ _ ↦ loopBB_noDsp hok.body
  have hdspB : (stmtsOf Cf.fn.body).all (dspB Cf) = true := List.all_eq_true.mpr fun s hs ↦ by
    cases s with
    | dispatch x fs a r => exact absurd hs (hnd x fs a r)
    | _ => rfl
  obtain ⟨cpre, toc, tod, tof, roc, hcode, hcpre, hrz, hrnz, htz, htnz, htsf, htnx, htod,
    htpc, hentS⟩ := loopCodeC_spec hok.code
  have hsh := LoopShape0.of_ok ((Bool.and_eq_true _ _).mp hok.shape).1
  have hend := hsh.len
  have hs := sigLP_of hok.sig
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hsh.ent
  have hso : ∀ o, K.F.sig.self = some o → o + 1 < 2 ^ Exec.envDepth ∧ o < 2 ^ 28 := fun o ho ↦
    hsh.self o (hok.fsig ▸ ho)
  have hpar := heapOkC_params hok.heap
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  have hlen : Cf.frame.len = K.code.length := hok.flen
  have hcl : K.code.length = cpre.length + 2 := by rw [hcode]; simp
  refine ⟨fun hle hfp h ↦ h.mono hle hfp, ?_, ?_⟩
  · -- the entry
    intro s hH0 hs0
    rw [Mode.preAt_none hCt.1] at hH0
    obtain ⟨hw, hpre, hpreR, hself⟩ := entry_facts hent' (fun o ho ↦ (hso o ho).1) hH0
    refine coreAt_of (by rw [CFun.xc_of hok.hc, hok.fsig]; exact expW_entry hκ hs0.agree hH0)
      ⟨atF_mono (s := s) (Mem.le_refl _) rfl (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho),
      fun o hso' ↦ ?_⟩), fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    · rw [hok.fsig] at hso'
      obtain ⟨hwo, hgo⟩ := hself o hso'
      exact ⟨hwo, rdE_of_get hκ hs0.agree hgo (Mode.ofK_gpow_ne_zero _)⟩
    obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
      by simpa using hσ.holds _ _ hwk, by simp,
      fun y hy ↦ ?_⟩
    have hP := parAt_of (G := K.F.sig) hκ hs0.agree hs0.fp hw (hws0 hσ)
    rcases hy with hy | ⟨e, he, -⟩
    · have hw1 : s.mem.written (s.fp + 1) = true := hw 1 (hok.fsig ▸ hsh.ent1)
      exact preSet_of_entryP hs (parAt_app hP (by simp [hnp])) (linkM_of hκ hs0.agree hs0.fp hw1 hσ.gl) (fun m hm ↦ Mode.HW.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl
        (hpre m hm)) (fun r hr ↦ Mode.RW.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl (hpreR r hr))
        (fun q hq ↦ Mode.PW.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl (entry_preP hH0 q hq))
        (rdW_img hκ hs0.agree) y hy
    · cases he
  · -- a step
    intro s i hi hpc hat hs0 hYs hsz _ henvK _ hjtR hT _ _ hh hres href Inv k
    have hat0 := hat.2 s.mem (Mem.le_refl _) hs0.agree
    have hxw := hat.1
    have hxwE : ExpW img (expCells Cf.frame.sig) s.fp := CFun.xc_of hok.hc ▸ hxw
    have hAtF0 := hat0.1
    have hentw := hat0.2.1
    have hheap := hat0.2.2
    have hAtF : AtF img Cf.frame K.code i s := atF_mono (s := Mode.stOf s.mem s.fp) (Mem.le_refl _) rfl hAtF0
    obtain ⟨σ0, hσ0⟩ := hH s i hYs hi hpc
    obtain ⟨n, hon⟩ := hY s hYs
    have hpcF : s.pc = Cf.frame.entry + i := by rw [hok.fentry]; exact hpc
    have hhintsF := hintsF_of hC ha hK hok.fentry hok.hints
    have hhd := hintsD_of hok.dhints hok.xentry hok.fentry
    have hwE : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦ hentw o (hok.fsig ▸ ho)
    have hPs : ∀ {σ : Val}, HonF img Cf s.fp σ → ParAt K.F.sig np (stOf s.mem s.fp) (Cf.fn.params.map σ) :=
      fun hσ ↦ parAt_of hκ hs0.agree hs0.fp hwE (hws0 hσ)
    have hrwOf : ∀ σ pre es vs rd, HonF img Cf s.fp σ → walk σ Cf.fn.body = .ret (pre ++ es) vs →
        (∀ e ∈ pre ++ es, e.Holds rd σ) → ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es :=
      fun σ pre es vs rd hσ hb hh0 ↦ readsAt_of_C (loopC_heap hok hb hh0 (hσ.res hxw) (hPs hσ) hT).1
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
    have hsm : ∀ oc od of, K.code[i]? = some (.jump oc od of) → oc < 2 ^ 28 ∧ od < 2 ^ 28 ∧ of < 2 ^ 28 :=
      fun oc od of hci ↦ by
        have h := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at h
        exact h
    have hselfs : ∀ {σ : Val}, HonF img Cf s.fp σ → ∀ {pre es : List Ev} {vs : List V},
        walk σ Cf.fn.body = .ret (pre ++ es) vs →
        ∃ E, pre ++ es = E ++ [.inK c0, if σ c0 = 0 then .skip Cf.fn.name args0 else .call Cf.fn.name args0 []] ∧
          vs = [] := by
      intro σ _ pre es vs hb
      rw [hbody] at hb
      obtain ⟨E, -, h1, h2⟩ := walk_loopB σ hpre0 hb
      exact ⟨E, h1, h2⟩
    refine frame_step (prog := guestProgram) (k := n - s.steps) hκ harm hacc hok.fpows hsh.len hsz
      (fun j hj ↦ by rw [hok.fentry]; exact hK.ops j hj) hhintsF (hok.fentry ▸ hok.fetch) hok.small hi hpcF hAtF hs0
      hon.2 (fun h ↦ absurd h (by simp [hsh.fp1]))
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (by rw [hpcF, hhintsF i hi]; exact hp) s1 e hm hin)
      (nzr_hnz hκ hok.nzrc harm hacc hi hAtF hs0 hres) ?_ ?_
      (fun s1 hm ↦ refOk_fp hm.fp href) ?_ ?_
    · -- the oracle's heap cell, written
      intro hOi s1 e1 hm
      have main : ∀ a o c, K.code[i] = .deref a o c .cell → HeapRd s1 (.deref a o c .cell) := by
        intro a o c hci
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
        by_cases hj : jtd Cf.X a o c = true
        · have hsm := hok.small i hi
          rw [hci] at hsm
          exact core_jtd hκ hok.pair hctrl hok.jtd (.inl hnd) (by rw [List.getElem?_eq_getElem hi, hci]) hj hsm.1
            henvK hm hσ0 hpos hb hwp
        replace hj := Bool.eq_false_iff.mpr hj
        have hsm := hok.small i hi
        rw [hci] at hsm
        exact heapRd_pair hκ hok.pair hpos (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi)
          hj hsm.1 hσ0 hb hwp (hrwOf σ0 pre es vs rd hσ0 hb hh0) hW (hhd i) hs0 hm e1
      generalize hci : K.code[i] = ins
      cases ins with
      | deref a o c mode =>
        cases mode with
        | cell => exact main a o c hci
        | pc => trivial
        | fp => trivial
      | _ => trivial
    · -- a table jump's target, one of its arms
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, -, -, -⟩ := hheap σ0 hσ0
      exact core_tgt hok.pair hctrl hok.tgt hdspB hσ0 hpos hb hwp
    · -- falling through
      intro s1 s' e1 hm hmo e' hpc' hfp' hf' hle' hat' hstw hc0
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hi1 : i + 1 < K.code.length := by
        by_contra hn
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
        rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
        · cases hA
        · cases hg'
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) (coreAt_of (by rw [hfp']; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
          fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ hσ
      by_cases hj : ∃ oc od of, K.code[i]? = some (.jump oc od of)
      · obtain ⟨oc, od, of, hci⟩ := hj
        have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
          rw [hhd i]; exact e1
        obtain ⟨pos', hpos', evs, es', rfl, hwp', -, hWr⟩ := core_jfall hκ hok.pair hctrl hci (hsm oc od of hci).1 e1'
          hs0 hm (hc0 oc od of hci) hσ hpos hb hwp (hrwOf σ pre _ vs rd hσ hb hh0) hW
        exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
          by rw [List.append_assoc]; exact hh0, loopC_evM_pre hok _ (by rw [List.append_assoc]; exact hb),
          fun y hy ↦ (hWr y hy).mono hle'⟩
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fallC (sigOf := Cf.sigOf) (rd := rd)
        (ws0 := Cf.fn.params.map σ) hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', -, hWr⟩ := hfallP hwp (hrwOf σ pre _ vs rd hσ hb hh0)
      refine ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
        by rw [List.append_assoc]; exact hh0, loopC_evM_pre hok _ (by rw [List.append_assoc]; exact hb),
        fun y hy ↦ ?_⟩
      exact fall_wrk hκ hi (hok.small i hi) hσ hb hW hpairs (hhd i) hs0 hm hle' hfp' hf' e1 hstw (hWr y hy)
    · -- a jump taken
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt hcn
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      obtain ⟨soc, sod, sof⟩ := hsm _ _ _ hci
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hT1 : ∀ p ∈ K.F.sig.term, LTF (stOf s1.mem s1.fp) p.1 p.2 := fun p hp ↦ by
        rw [hm.fp]; exact Mode.LTF.mem hm.le (hT p hp)
      have hP1 : ∀ {σ : Val}, HonF img Cf s.fp σ → ParAt K.F.sig np (stOf s1.mem s1.fp) (Cf.fn.params.map σ) :=
        fun hσ ↦ (hPs hσ).mono (s := stOf s.mem s.fp) (s' := stOf s1.mem s1.fp) hm.le hm.fp
      rcases loopCodeC_jump hcode hcpre hci with ⟨-, hcj⟩ | ⟨hi', rfl, rfl, rfl⟩ | ⟨hi', rfl, rfl, rfl⟩
      · -- a call (a jump on a constant `0` is never taken)
        have hzc : Cf.X.zeroAt oc = false := by
          cases hzz : Cf.X.zeroAt oc
          · rfl
          · obtain ⟨v, hv, hv0⟩ := hcn _ _ _ hci
            exact absurd (rd_get hκ hm.fine soc (by rw [hm.fp]; exact hσ0.jc.zero _ hzz) hv) hv0
        by_cases hsfc : Cf.X.selfAt of = true
        swap
        · exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (call_stepC hok hK hκ hU hi hpc hYs hs0 hat0 hxw hσ0 hT hjtR e1
            (he1 s1 e1) hm e' hf' hle' hjo hci h0 h1 hpcs hsz hcj hzc (by simpa using hsfc) (hcn _ _ _ hci) hCt)
        -- a jump in the frame: a branch's side, a `match`'s arm
        obtain ⟨hcj', hdn⟩ := callJ_self hcj hzc hsfc
        have hof1 : of ≠ 1 := fun h ↦ by rw [h, hsh.self1] at hsfc; cases hsfc
        have hlenX : ∀ o < K.code.length, Cf.X.entry + o < 2 ^ 30 := fun o ho ↦ by
          rw [hok.xentry, ← hok.fentry]; rw [hlen] at hend; omega
        have hpcs' : s'.pc < 2 ^ 30 := by omega
        have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
          rw [hhd i]; exact e1
        obtain ⟨v, hv, hv0⟩ := hcn _ _ _ hci
        have hnoret : ∀ {σ : Val}, ¬ (if Cf.X.main then Cf.X.selfAt of = true ∧ Cf.X.pcAt od = some Cf.X.halt
            else od = 0 ∧ of = 1) := fun h ↦ by
          simp only [hsh.main, Bool.false_eq_true, ↓reduceIte] at h
          exact hof1 h.2
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
        rcases core_jtaken hκ hok.pair hctrl hlenX hci hcj' hsfc hdn soc sod e1' hs0 hm hv hv0 h0 hpcs' hσ0 hpos hb hwp
          (hrwOf σ0 pre es vs rd hσ0 hb hh0) hW with ⟨hif, -⟩ | ⟨-, o, pos0, hpco, hio, hpos0, -⟩
        · exact absurd hif (hnoret (σ := σ0))
        have hol := pairAt_lt hok.pair hpos0
        cases hjo with
        | «local» t hnr hfp' hpc' hat' =>
          have hto : t = o := by rw [hok.fentry, ← hok.xentry] at hpc'; omega
          subst hto
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move t hfp' hol (by rw [hpc', hok.fentry])
            (coreAt_of (by rw [hfp', hm.fp]; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
              fun o ho ↦ by rw [hfp', hm.fp]; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
          rw [hfp', hm.fp] at hσ
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ hσ
          rcases core_jtaken hκ hok.pair hctrl hlenX hci hcj' hsfc hdn soc sod e1' hs0 hm hv hv0 h0 hpcs' hσ hpos hb
            hwp (hrwOf σ pre es vs rd hσ hb hh0) hW with ⟨hif, -⟩ |
              ⟨-, o', pos', hpco', -, hpos', evs, es', rfl, hwp', -, hWr⟩
          · exact absurd hif (hnoret (σ := σ))
          have ho' : o' = t := by omega
          subst ho'
          exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
            by rw [List.append_assoc]; exact hh0, loopC_evM_pre hok _ (by rw [List.append_assoc]; exact hb),
            fun y hy ↦ (hWr y hy).mono hle'⟩
        | ret _ _ hr =>
          obtain ⟨c, hc⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc
          exact absurd hc.2.2 hof1
        | halt _ hfpo _ _ => exact absurd hfpo (by simp [hsh.fp1])
        | tail e _ hpc' => rw [hpc', hok.fentry, ← hok.xentry] at hpco; omega
        | call G t _ _ hG _ _ _ =>
          have h := sigsOut_get hsh.sigsOut (by rw [hlen]; exact hol)
          simp only [Bool.or_eq_true, Nat.beq_eq] at h
          rcases h with h | h
          · omega
          rw [hpco, hok.xentry, ← hok.fentry] at hG
          rw [hG] at h
          cases h
      swap
      · -- the return
        have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨_, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj hnr
        | halt hnr => exact absurd hrj hnr
        | tail e hnr => exact absurd hrj hnr
        | call G' t hnr => exact absurd hrj hnr
        | ret hregs hretw _ =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret _ hci (by omega) h0 h1 ?_)
          rw [Mode.postAt_none hCt.1]
          obtain ⟨pos, pre, es, vs, rd, rfl, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
          obtain ⟨hreads, hposts⟩ := loopC_heap hok hb hh0 (hσ0.res hxw) (hPs hσ0) hT
          obtain ⟨as, hpairs, hpr⟩ := pair_retL hok.pair hpos hci hrz hsh.self1 hsh.pc0 hst hwp (readsAt_of_C hreads)
          rw [hhd i] at hpairs
          have W1 : ∀ x, WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK s1.mem x := by
            intro x hx
            rcases hpr x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hm.le
            · exact flow_wrk hκ e1 hs0 hm hpairs ha hfa
                (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
          obtain ⟨-, -, hvs⟩ := hselfs hσ0 hb
          subst hvs
          simp only [PostOkW, List.map_nil, List.append_nil] at hposts
          have hu1 : s1.mem.used ≤ 2 ^ κ := le_trans hle'.used
            (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e')
          have hX1 : ExpM K.F.sig (expCells K.F.sig) (stOf s1.mem s1.fp) := by
            rw [hm.fp]
            exact expM_of hκ hm.fine.agree hs0.fp (hok.fsig ▸ hxwE)
              (fun o ho ↦ written_mono hm.le (hwE o ho)) _
          exact retAll_of_wrkP hs (hP1 hσ0) hT1 hX1 (fun c hc ↦ W1 _ (hposts.1.1 c hc))
            (fun r hr x hx ↦ W1 x (hposts.1.2 r hr x hx)) (rdM_img hκ hm.fine.agree hu1)
            fun x hx ↦ W1 x (hposts.2.1 x hx)
      · -- the tail call
        obtain ⟨pos, pre, es, vs, rd, rfl, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
        obtain ⟨c, f, args, pos', hcm, hloc, ⟨t0, ht0, hentT⟩, -, hrn, as, hpairs, hsplit⟩ :=
          pair_tailL hok.pair hpos hci htz htnz htsf htnx htod hst
        have hrw0 := hrwOf σ0 pre es vs img.read hσ0 hb hh0
        have hrw0C := (loopC_heap hok hb hh0 (hσ0.res hxw) (hPs hσ0) hT).1
        obtain ⟨evs, cs, es', heq, hwp', hcs, -, -, hW'⟩ := hsplit hwp hrw0
        -- the tail `JUMP` enters the loop's own entry, which names it
        have hfn : f = Cf.fn.name := by
          rw [htpc, Option.some.injEq] at ht0
          subst ht0
          have := entOk_spec hentT
          rw [entOk_spec hentS, Option.some.injEq] at this
          exact this.symm
        subst hfn
        rw [hbody] at hcm
        obtain ⟨rfl, rfl⟩ := loopB_callIf hpre0 hcm
        -- its condition nonzero: the call entered
        obtain ⟨v, hv, hv0⟩ := hcn _ _ _ hci
        have hcond := hσ0.jc.cond _ _ hb c (by rw [heq]; simp)
        rw [hloc] at hcond
        have hσc : σ0 c ≠ 0 := by
          have := rd_get hκ hm.fine soc (by rw [hm.fp]; exact hcond) hv
          rw [← this]; exact hv0
        simp only [hσc, ↓reduceIte] at heq
        obtain ⟨E0, hpe, hvs⟩ := hselfs hσ0 hb
        simp only [hσc, ↓reduceIte] at hpe
        subst hvs
        have hes' : es' = [] := by
          rw [Bridge.retNil_eq hrn, walk_ret_cons, Out.ret.injEq] at hwp'
          exact hwp'.1.symm
        subst hes'
        -- the next frame, of the honest tree
        have hcl0 : (calls (pre ++ es))[(calls E0).length]? = some ⟨Cf.fn.name, args, [], true⟩ ∧
            (calls E0).length + 1 = (calls (pre ++ es)).length := by
          rw [hpe]
          simp [calls, List.filterMap_append, List.filterMap_cons, Ev.call?]
        have hfetch := (hok.fetch i _ hci).1
        rw [← hok.xentry] at hfetch
        obtain ⟨S, hS0, hS30, hq, hn0, hn1, hnargs⟩ := hσ0.tail _ _ hb _ _ hcl0.1 hcl0.2 i _ _ _
          (by rw [hok.xlen]; exact hi) soc sod sof hfetch htnx
        have hfpS : s'.fp = s.fp + S := by
          have := rd_get hκ hm.fine sof (by rw [hm.fp]; exact hq) h1
          have h2 := hf'.fp
          have h3 := hs0.fp
          unfold maxCells at h2 h3
          exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        have hpe' : s'.pc = K.F.entry := by
          have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.jc.pcw _ _ htpc) h0
          have hb' := hok.xentry ▸ hok.fentry ▸ hsh.len
          rw [← hok.xentry]
          exact gpow_inj (by omega) (by rw [hok.xentry, ← hok.fentry]; omega) (pow_of_ofK this)
        have hWc : ∀ x, WrittenC Cf.sigOf Cf.H img.read σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x := by
          intro x hx
          rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
          · exact (hW _ h).mono hle
          · rw [hhd i] at hpairs
            exact (flow_wrk hκ e1 hs0 hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
              (by rw [heq]; simp [hma]) hq) hwa).mono hle'
        have hout : EntryFr img Cf.frame.sig s' → Out Ct K (CoreAt img Cf K.code) i s1 s' := fun hentry ↦
          .tail hok.sigE fun hTE ↦ Mode.tail_of_mode hCt.1 <| tail_nextC (c := c) (args := args) hok hκ hs0.fp hm.fp hm.le hf' hle'
            (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e') hfpS hS30
            hpe' hentry (by rw [hfpS, hm.fp]; exact hn0) (by rw [hfpS, hm.fp]; exact hn1) hTE (hjtR s' hle) hwE
            (fun o ho ↦ (hso o ho).2) hsh.ent0 hsh.ent1 hb hh0 (hσ0.res hxw) hσ0.gl (by simpa using heq) hrw0C hWc
            (fun k hk ↦ hnargs k hk)
            hargs (hPs hσ0) hT
            (expM_of hκ hf'.agree hs0.fp (hok.fsig ▸ hxwE) (fun o ho ↦ written_mono hle (hwE o ho)) _)
            (expM_next hκ hf'.agree hf'.fp (hok.fsig ▸ hxwE) (fun o ho ↦ hentry.w o (hok.fsig ▸ ho))
              fun o ho ↦ by
                obtain ⟨k, rfl, hk⟩ := tailPass_spec hbody ho
                have hkl : k < args.length := (List.getElem?_eq_some_iff.mp hk).1
                rw [hfpS, hnargs k hkl, show args[k] = V.n k from (List.getElem?_eq_some_iff.mp hk).2,
                  ← hσ0.par k (by omega)]) hcs
            fun b hb ↦ by
              obtain ⟨k, hk, hka⟩ := tailPass_spec hbody hb
              obtain rfl : k = b := by omega
              exact hka
        cases hjo with
        | ret _ _ hr =>
          obtain ⟨c', hc'⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact absurd hc'.2.1 htod
        | «local» t _ hfp' _ _ =>
          exfalso
          rw [hfpS, hm.fp] at hfp'
          omega
        | halt _ h1' _ => simp [hsh.fp1] at h1'
        | call G' t _ _ hsig hentry _ _ =>
          rw [hpe', hok.fsigs, hok.sigE, Option.some.injEq] at hsig
          subst hsig
          exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (hout (hok.fsig ▸ hentry))
        | tail e _ _ _ hentry _ _ _ =>
          exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (hout hentry)

/-- **A loop helper with calls on the core route meets its frame interface**, from the kernel's checks. -/
theorem fnSpecC_of_loopC {K : Mode.Cert} {Cf : CFun} (hok : LoopOkC K Cf) : Mode.FnSpecC K Cf :=
  fun _ _ hC ha hK _ _ _ _ hκ hY hH hU hCt ↦ frameSpec_loopC hok hC ha hK hκ hY hH hU (modeCts_of hCt hok.hc hok.hcs)

end

end LeanVM.Guest.CoreMode
