/-
  LeanVM.Guest.EndExec

  The executor runs the guest to completion on the guest's advice: the final chain, every piece not
  yet proved a field of `ExecGaps`.
-/

module

public import LeanVM.Guest.EndExecRef
public import LeanVM.Guest.ExecDecodable
public import LeanVM.Guest.Mode.ResRef
public import LeanVM.Guest.EndRpm
public import LeanVM.Guest.Budget.Fits
public import Statement.LeanVmGuestCompleteness

/-!
# The executor on the guest

The chain: a node within the budget has a reference run (`ref_exists`, `EndExecRef.lean`); the
executor run on the guest's advice (`guestAdvice`) follows it (`execute_complete_guest`, the mode
walk's invariant `guestInv` and its rule `inv_rule`), so it returns a valid execution committing no
more cells than the reference, at most `2^30` (`execute_guest_complete`, `guestExecution_complete`).

What the chain rests on and is not yet proved is `ExecGaps Ks Km E0 X Pro`, for the mode walk's
certificates `Ks` (`main`'s `Km`, their program `E0`), the other tracks' invariant `X` (the witness
streams' cursor, the bump pointer, the frame-to-instance map) and the prologue's states `Pro`, each a
function of the node's reference run. Each field names the track that discharges it. Proved here:
the reference run (but `MainExactHyp`), the memory's log-size at most `28` and the steps at most
`maxSteps` from the committed size (`logMemorySize_le_28`, `stepCount_le_maxSteps`), every slot
decoding (`guest_decodable`), `main`'s frame, the executor's tables, and `ProgOk` from the
certificates (`progOk_of`).

`GuestExecutionComplete advice` is the `Statement/` field `notes/exec-statement.md` proposes, and
`aggregate_complete_exec` the guest's completeness in the random-permutation model with the
executor's execution (`End.aggregate_complete_of`'s form). The honest-children forms are in
`EndExecHonest.lean`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (hdrOf bytecode work publicInputOf)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)
open LeanVM.Guest.Mode
open LeanVM.Prover.Exec
open scoped ENNReal

@[expose] public section

/-! ## From the committed size -/

/-- **A run's steps are its instructions**, counted by opcode. -/
theorem steps_le_counts {κ : ℕ} {prog : LeanIsaProgram} {M : MemoryImage κ} :
    ∀ (n : ℕ) (r r' : Registers K), run prog M n r = some r' →
      n ≤ opcodeCountInRun prog M .xor n r + opcodeCountInRun prog M .mulNative n r +
        opcodeCountInRun prog M .setConstant n r + opcodeCountInRun prog M .deref n r +
        opcodeCountInRun prog M .jump n r + opcodeCountInRun prog M .keccak n r
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, r, r', h => by
    rw [run] at h
    split_ifs at h
    cases hs : Semantics.step prog M r with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some r1 =>
      rw [hs] at h
      have ih := steps_le_counts n r1 r' h
      cases hf : prog.fetch r.pc with
      | none => rw [Semantics.step, hf] at hs; exact absurd hs (by simp)
      | some ins =>
        simp only [opcodeCountInRun, hf, hs]
        cases ins <;> simp only [LeanIsaInstruction.opcode] <;> simp <;> omega

/-- **The committed size counts the memory thrice and each instruction at least seven times.** -/
theorem committedSize_ge {prog : LeanIsaProgram} (e : Execution prog) :
    3 * 2 ^ e.logMemorySize + 7 * (e.opcodeCount .xor + e.opcodeCount .mulNative +
      e.opcodeCount .setConstant + e.opcodeCount .deref + e.opcodeCount .jump +
      e.opcodeCount .keccak) ≤ e.committedSize := by
  have hle : ∀ op, e.opcodeCount op ≤ 2 ^ Nat.clog 2 (e.opcodeCount op) := fun op ↦
    Nat.le_pow_clog (by norm_num) _
  have hk : 2 ^ Nat.clog 2 (e.opcodeCount .keccak) ≤ 2 ^ max (Nat.clog 2 (e.opcodeCount .keccak)) 9 :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h1 := hle .xor
  have h2 := hle .mulNative
  have h3 := hle .setConstant
  have h4 := hle .deref
  have h5 := hle .jump
  have h6 := hle .keccak
  simp only [Execution.committedSize]
  generalize 2 ^ e.logMemorySize = a at *
  generalize 2 ^ prog.logSize = b at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .xor) = c at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .mulNative) = d at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .setConstant) = f at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .deref) = i at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .jump) = j at *
  generalize 2 ^ max (Nat.clog 2 (e.opcodeCount .keccak)) 9 = k at *
  generalize 2 ^ Nat.clog 2 (e.opcodeCount .keccak) = q at *
  omega

/-- **An execution within `2^30` committed cells has at most `maxSteps` steps.** -/
theorem stepCount_le_maxSteps {prog : LeanIsaProgram} {input : PublicInput} {e : Execution prog}
    (hv : ValidExecution prog input e) (hs : e.committedSize ≤ 2 ^ 30) : e.stepCount ≤ maxSteps := by
  have h : e.stepCount ≤ e.opcodeCount .xor + e.opcodeCount .mulNative + e.opcodeCount .setConstant +
      e.opcodeCount .deref + e.opcodeCount .jump + e.opcodeCount .keccak := steps_le_counts _ _ _ hv.2
  have := committedSize_ge e
  unfold maxSteps
  omega

/-- **An execution within `2^30` committed cells has at most `2^28` words.** -/
theorem logMemorySize_le_28 {prog : LeanIsaProgram} {e : Execution prog}
    (hs : e.committedSize ≤ 2 ^ 30) : e.logMemorySize ≤ 28 := by
  by_contra h
  have : 2 ^ 29 ≤ 2 ^ e.logMemorySize := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := committedSize_ge e
  omega

/-! ## The certificates -/

/-- **The mode walk's certificates, closed**: each is a guest function's (its code and entry), its
walk accepting its code, of its length, its operands below `2^28` and its hints the advice's; and
they are tied to each other as `ProgOk` asks. -/
structure ModeCerts (Ks : List Mode.Cert) (Km : Mode.Cert) (E0 : Mode.Env) : Prop where
  fn : ∀ K ∈ Ks, ∃ f ∈ Data.functions, K.code = f.code ∧ K.F.entry = f.entryPc ∧
    walk K.E K.F K.code = true ∧ K.F.len = K.code.length ∧ K.code.all offSmall = true ∧
    HintsOk K.F Data.adviceHints
  ne : ∀ K ∈ Ks, 0 < K.code.length
  uniq : ∀ K ∈ Ks, ∀ K' ∈ Ks, K.F.entry = K'.F.entry → K = K'
  sigs : ∀ K ∈ Ks, ∀ t G, K.E.sigs.get t = some G →
    ∃ K' ∈ Ks, K'.F.entry = t ∧ K'.F.sig = G ∧ K'.F.main = false
  env : ∀ K ∈ Ks, K.E.pows = E0.pows ∧ K.E.jt = E0.jt ∧ K.E.jtLo = E0.jtLo ∧ K.E.jtHi = E0.jtHi ∧
    K.E.halt = E0.halt
  pows : E0.pows.Ok
  jt : ∀ d e, E0.jt.get d = some e → e < 2 ^ 62
  halt : E0.halt = 2 ^ guestProgram.logSize - 1
  main : Km ∈ Ks
  mainF : Km.F.main = true
  mainRet : ∀ (i c : ℕ), Km.code[i]? ≠ some (OffsetInstruction.jump c 0 1)
  mainTerm : Km.F.sig.term = []
  tailRet : ∀ K ∈ Ks, ∀ G, K.E.sigs.get K.F.entry = some G → RetEmpty G
  loopRng : ∀ K ∈ Ks, ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term
  endOk : ∀ K ∈ Ks, ∀ cur pend, preAt K.E K.F K.code K.code.length = some (cur, pend) → cur = []

/-- **The certificates tied to the executor**, run on any advice with the guest's hints. -/
theorem progOk_of {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} (h : ModeCerts Ks Km E0) {adv : Advice}
    {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) :
    ProgOk guestProgram C Ks Km E0 where
  ok K hK := by
    obtain ⟨f, hf, hcode, hentry, hw, hlen, hs, hh⟩ := h.fn K hK
    exact certOk_fn hC ha hf hcode hentry hw hlen hs hh
  ne := h.ne
  uniq := h.uniq
  sigs := h.sigs
  env := h.env
  pows := h.pows
  jt := h.jt
  halt := h.halt
  main := h.main
  mainF := h.mainF
  mainRet := h.mainRet
  mainTerm := h.mainTerm
  tailRet := h.tailRet
  loopRng := h.loopRng
  endOk := h.endOk

/-! ## What is not yet proved -/

/-- An allocation hint: a frame's or a buffer's base, or a cell's address. -/
def isAllocHint : Prover.Exec.Hint → Bool
  | .frameAddress .. | .allocFrames .. | .alloc .. | .allocDyn .. | .allocAdvice .. | .allocArm ..
  | .cellAddress .. => true
  | _ => false

/-- A witness hint: an entry popped from a stream. -/
def isWitnessHint : Prover.Exec.Hint → Bool
  | .witnessStack .. | .witnessHeap .. => true
  | _ => false

/-- **A step's premises on the reference**: at a state of the node's run on its reference with `X`,
fine against the reference memory, the executor's tables `C` for the guest's advice. -/
abbrev OnRun (X : Ref → St → Prop) (r : Ref) (s : St) : Prop :=
  X r s ∧ Fine (refMem r.img) s ∧ OnRef guestProgram r.img r.n s

/-- **What the executor's completeness on the guest rests on and is not yet proved**, for the mode
walk's certificates `Ks` (`main`'s `Km`, their program `E0`), the other tracks' invariant `X` and the
prologue's states `Pro`, each read at a node's reference run `r` (`Ref.Ok`) and the executor's
tables `C` for its advice. -/
structure ExecGaps (Ks : List Mode.Cert) (Km : Mode.Cert) (E0 : Mode.Env) (X Pro : Ref → St → Prop) : Prop where
  /-- Every function the run enters passes the mode walk, its certificate kernel-checked and tied
  to the others (the mode walk track: `scripts/mode-cert/gen.py`, the walk closed on its remaining
  functions, the heavy functions' checks, the certificates assembled). -/
  certs : ModeCerts Ks Km E0
  /-- The children's loop, `main_loop2` and `main_loop3` complete by trees exact on the memory
  (the exactness track: `Budget.mainExactHyp_of_l5`, the children's loop's E form). -/
  mainExact : Budget.MainExactHyp
  /-- Each allocation hint's needs once its inputs are written: a reservation at the bump
  pointer, below `maxCells`, of the size the tree allocates there, an `allocAdvice`'s size the
  next entry of `heap_sizes` (the allocation track: `AllocInv` in `X`, the compiler's reservation
  order, `Tree.heapPops` against the `heap_sizes` pushes). -/
  hintAlloc : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
    h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = true → HintIn s h → HintOk C (refMem r.img) s h
  /-- Each witness hint pops the next entry of its stream, the reference's words at its
  destination (the hint bridge: the alignment's soundness pairing each ISA hint with its core
  atom on the instance's path, and the tree track's cursor, `TrackOk.witness_next`, in `X`). -/
  hintWitness : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
    h ∈ (C.hints[s.pc]?).getD [] → isWitnessHint h = true → HintIn s h → HintOk C (refMem r.img) s h
  /-- Each computed hint's destination holds, on the reference, its formula of its inputs (the
  hint bridge with the tree's exactness, `Ref.Ok.tree`'s `ExactAt`). -/
  hintComputed : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
    h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → HintIn s h →
    HintOk C (refMem r.img) s h
  /-- Each certificate's residuals hold of the reference at the state's frame (the residuals by
  family: `ResFam`'s obligations from the honest-child hypotheses, `WalkKnown`, `LoadsIn` and
  `BufsOk`). -/
  res : ∀ r, r.Ok → ResRef guestProgram r.img r.n Ks (X r)
  /-- Each function's termination facts at its entry (from the loops' exits and the table calls'
  arms, through the frame-to-instance map in `X`). -/
  term : ∀ r, r.Ok → ∀ K ∈ Ks, ∀ s, OnRun X r s → s.pc = K.F.entry → ∀ p ∈ K.F.sig.term,
    LTF s p.1 p.2
  /-- A `DEREF`'s pointer and a taken `JUMP`'s frame are powers below `maxCells` on the reference
  (`RefOk`, from the reference step, as `ref_mul` reads a `MUL`). -/
  ref : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op, OnRun X r s →
    C.ops[s.pc]? = some op → RefOk (refMem r.img) s op
  /-- Each hint keeps `X` (the tree track and the allocation track). -/
  keepHint : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h s', OnRun X r s →
    h ∈ (C.hints[s.pc]?).getD [] → runHint C s h = .ok s' → X r s'
  /-- Each instruction keeps `X` (the tree track along the reference run, `RefTrace`). -/
  keepOp : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s', OnRun X r s →
    C.ops[s.pc]? = some op → runOp C s op = .ok s' → X r { s' with steps := s'.steps + 1 }
  /-- `__jump_tables`' straight-line `SET`s write the jump table and fall into `main`'s entry
  (the prologue). -/
  pro : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op, OnRun X r s → Pro r s →
    C.ops[s.pc]? = some op →
    StepOk C (refMem r.img) (fun s' ↦ Pro r s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s
  /-- `X` and the prologue at the executor's initial state. -/
  init : ∀ r, r.Ok → ∀ C m, Ctx.of guestProgram r.adv = .ok C → initMem r.adv r.input = .ok m →
    X r (initSt C r.adv m) ∧ Pro r (initSt C r.adv m)
  /-- `X` keeps the cells the run touches within the reference's `2^κ`. -/
  used : ∀ r, r.Ok → ∀ s, X r s → s.mem.used ≤ 2 ^ r.κ

/-! ## The chain -/

section

variable {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {X Pro : Ref → St → Prop}

/-- **The executor follows a node's reference run**: on the guest's advice it returns a valid
execution committing no more cells than the reference. -/
theorem execute_ref (G : ExecGaps Ks Km E0 X Pro) {r : Ref} (hr : r.Ok) :
    ∃ t, execute guestProgram r.input r.adv = .ok t ∧ ValidExecution guestProgram r.input t ∧
      t.committedSize ≤ 2 ^ 30 := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hn : r.n ≤ maxSteps := stepCount_le_maxSteps (e := r.exec) hr.valid hr.size
  have hmain : r.adv.mainFrame < maxCells := by
    show Data.adviceMainFrame < maxCells
    decide
  obtain ⟨t, he, hv, -, -, -, -, hsz⟩ := execute_complete_guest (Ks := Ks) (Km := Km) (E0 := E0)
    (X := X r) (Pro := Pro r) hκ hn hr.valid guest_decodable hmain
    (fun C hC ↦ progOk_of G.certs hC rfl)
    (fun C hC ↦
      { hint := fun s h hX hs hon hh hin ↦ by
          cases ha : isAllocHint h
          · cases hw : isWitnessHint h
            · exact G.hintComputed r hr C hC s h ⟨hX, hs, hon⟩ hh ha hw hin
            · exact G.hintWitness r hr C hC s h ⟨hX, hs, hon⟩ hh hw hin
          · exact G.hintAlloc r hr C hC s h ⟨hX, hs, hon⟩ hh ha hin
        res := prem_res (G.res r hr)
        term := fun K hK s hX hs hon hpc ↦ G.term r hr K hK s ⟨hX, hs, hon⟩ hpc
        ref := fun s op hX hs hon hop ↦ G.ref r hr C hC s op ⟨hX, hs, hon⟩ hop
        xh := fun s h s' hX hs hon hh e ↦ G.keepHint r hr C hC s h s' ⟨hX, hs, hon⟩ hh e
        xo := fun s op s' hX hs hon hop e ↦ G.keepOp r hr C hC s op s' ⟨hX, hs, hon⟩ hop e })
    (fun C hC s op hX hP hs hon hop ↦ G.pro r hr C hC s op ⟨hX, hs, hon⟩ hP hop)
    (fun C m hC hm ↦ G.init r hr C m hC hm) (G.used r hr)
  exact ⟨t, he, hv, hsz.trans hr.size⟩

/-- **The executor is complete on the guest**: for every node meeting `NodeRelation`, within the
limits, its children acceptable and within the budget, the executor run on the guest's advice
returns a valid execution of the guest on the statement's digest, of committed size at most
`2^30`. -/
theorem execute_guest_complete (G : ExecGaps Ks Km E0 X Pro) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 →
      ∃ t, execute guestProgram (publicInputOf (statementDigest seed s)) (guestAdvice seed s w) = .ok t ∧
        ValidExecution guestProgram (publicInputOf (statementDigest seed s)) t ∧ t.committedSize ≤ 2 ^ 30 := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨r, rfl, rfl, rfl, hr⟩ := ref_exists G.mainExact seed s w hrel hlim hok hbs
  exact execute_ref G hr

/-- **`guestExecution` is complete**, under `execute_guest_complete`'s hypotheses. -/
theorem guestExecution_complete (G : ExecGaps Ks Km E0 X Pro) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 →
      ∃ t, guestExecution seed s w = .ok t ∧
        ValidExecution guestProgram (publicInputOf (statementDigest seed s)) t ∧ t.committedSize ≤ 2 ^ 30 :=
  fun seed s w hrel hlim hok hbs ↦
    let ⟨t, he, hv, hsz⟩ := execute_guest_complete G seed s w hrel hlim hok hbs
    ⟨t, guestExecution_of_execute he, hv, hsz⟩

/-- **A node within the deployed limits is within the budget**, its children acceptable. -/
theorem budget_of_limits {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hlim : DeployedLimits s w) (hok : ChildrenOk bytecode seed w) :
    (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 :=
  (Budget.deployedBudget_size_mono (work s w) fun (p : ℕ × ℕ) hp ↦ by
    obtain ⟨ch, hch, rfl⟩ :=
      List.mem_map.mp (show p ∈ w.children.map (childShape bytecode) from hp)
    obtain ⟨h1, h2, h3, h4⟩ := B1.Main.childShape_bounds Budget.vsCompleteHyp_deployed hok hch
    exact (Budget.vsBoundAt_eq_deployedBvAt h1 h2 h3 h4).le).trans (Budget.size_le hlim)

/-- **The guest's completeness in the random-permutation model, with the executor's execution**:
the execution the executor returns on the guest's advice, proved by the honest prover at an inverse
rate `2^ρ`, `1 ≤ ρ ≤ 4`, with at most `2^64` nonces, is rejected with probability at most
`completenessError fuel + rpmError (completenessPermCalls fuel)` (`End.aggregate_complete_of`'s
form). -/
theorem aggregate_complete_exec (G : ExecGaps Ks Km E0 X Pro) {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (hrel : NodeRelation bytecode seed s w) (hlim : GuestLimits s w)
    (hok : ChildrenOk bytecode seed w)
    (hbudget : (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30) :
    ∃ t, execute guestProgram (publicInputOf (statementDigest seed s)) (guestAdvice seed s w) = .ok t ∧
      ValidExecution guestProgram (publicInputOf (statementDigest seed s)) t ∧
      ∀ ρ fuel, 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
        Pr{let v ← verifierCompletenessExperimentWithHash
            (fun prog input t ρ fuel ↦
              some <$> LeanVM.Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel)
            guestProgram (publicInputOf (statementDigest seed s)) t ρ fuel}[v = false] ≤
          completenessError fuel + rpmError (completenessPermCalls fuel) := by
  obtain ⟨t, he, hv, hsz⟩ := execute_guest_complete G seed s w hrel hlim hok hbudget
  exact ⟨t, he, hv, fun _ _ hρ hfuel ↦ Rpm.completenessRpm hv hsz hρ hfuel⟩

end

/-! ## The proposed `Statement/` field -/

/-- The guest program's run on a node: the executor on the statement's digest, with the advice the
generator makes from the statement and the witness. -/
def guestRun (advice : Digest → NodeStatement → NodeWitness → Advice) (statement : NodeStatement)
    (witness : NodeWitness) : Except (ℕ × Fault) (Execution guestProgram) :=
  execute guestProgram (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement))
    (advice (deployedSeed guestProgram) statement witness)

/-- **The executor runs the guest program to completion on the advice**, within `2^30` committed
cells, on every node `GuestCompleteOnHonestChildren` admits. -/
def GuestExecutionComplete (advice : Digest → NodeStatement → NodeWitness → Advice) : Prop :=
  ∀ statement witness,
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness →
    (∀ child ∈ witness.children, Completeness.HonestChild child) →
    ∃ execution, guestRun advice statement witness = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      execution.committedSize ≤ 2 ^ 30

/-- **`GuestExecutionComplete` gives `GuestCompleteOnHonestChildren`**, for any advice. -/
theorem guestCompleteOnHonestChildren_of_exec {advice : Digest → NodeStatement → NodeWitness → Advice}
    (h : GuestExecutionComplete advice) : Completeness.GuestCompleteOnHonestChildren :=
  fun statement witness hrel hlim hon ↦
    let ⟨t, _, hv, hsz⟩ := h statement witness hrel hlim hon
    ⟨t, hv, hsz⟩

end

end LeanVM.Guest.EndExec
