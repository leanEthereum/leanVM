module

public import LeanVM.Guest.EndExecTrace
public import LeanVM.Guest.ExecWindows
public import LeanVM.Guest.EndExecPro
public import Statement.LeanVmGuestProver
import all Statement.Data.AdviceHints

/-!
# The executor follows a node's reference run

A node's reference run (`Ref`) is a memory image and a step count on which the guest program runs
validly on the node's statement digest. `Ref.Ok` is what the route takes of it: the run valid, its
memory at most `2^28` words, at most `maxSteps` steps, its frames powers below `2^κ` (`FramesIn`)
and aligned at its `KECCAK`s (`KeccakFramesAligned`), so that its `KECCAK`s have their blocks in
windows (`Ref.Ok.windows`, from the guest's offsets, `functions_kecOk`). Its producers: B2 completeness on
the guest's aligned honest memory (`b2c`), within the budget's bounds (`budget`).

`execute_ref`: given `ExecGaps` and a reference run, the executor run on the guest's advice
(`guestAdvice`, as `guestExecution` runs it) returns a valid execution of the reference's steps and
instruction counts, its memory at most the reference's `2^κ` words, committing no more than it.
The chain is `Mode.execute_complete_guest` (the invariant `guestInv` and its rule
`inv_rule_of_specs`) with the tracks' invariant `XOf Y`: the executor's registers on the reference
run's (`Trace`, proved here: `trace_next`), and `Y`, the hint tracks' (the witness streams' cursor,
the bump pointer), a parameter.

Proved here, beside the chain: every slot decoding (`guest_decodable`), `main`'s frame below
`maxCells`, the certificates tied to the executor (`progOk_of`), the trace started and kept, the
reference's part of each instruction's modedness (`refOk_of_trace`: a `MUL` holds, a `DEREF`'s
pointer and a taken `JUMP`'s frame are powers below `2^κ`, a `KECCAK`'s blocks lie in windows at
the executor's frame), the prologue (`pro_step`, `pro_init`, given `main`'s certificate's
`MainOk`), and the termination facts and residuals from their reference forms
(`term_of_ref_entry`, `prem_res`). Each field of `ExecGaps` is a named part still to be proved: the
certificates' own checks (`certs`, `main`), the core route (`frame`: each function's frame
interface, the core route's `FnSpec` with each frame an honest instance), its families (`res`,
`term`), the hint bridge (`hintAlloc`, `hintWitness`, `hintComputed`) and the hint tracks
(`initY`, `keepY`, `usedY`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The reference run -/

/-- **A node and its reference run**: the seed, statement and witness, a memory image of `2^κ`
words and the run's steps. -/
structure Ref where
  seed : Digest
  s : NodeStatement
  w : NodeWitness
  κ : ℕ
  img : MemoryImage κ
  n : ℕ

/-- The node's public input. -/
abbrev Ref.input (r : Ref) : PublicInput := PublicInput.ofDigest (statementDigest r.seed r.s)

/-- The guest's advice on the node, as `guestExecution` passes it. -/
abbrev Ref.adv (r : Ref) : Advice := guestAdvice (bytecodeWords guestProgram) r.seed r.s r.w

/-- **The reference execution.** -/
abbrev Ref.exec (r : Ref) : Execution guestProgram := ⟨r.κ, r.img, r.n⟩

/-- **What the route takes of a reference run.** -/
structure Ref.Ok (r : Ref) : Prop where
  /-- A valid execution of the guest on the node's statement digest. -/
  valid : ValidExecution guestProgram r.input r.exec
  /-- At most `2^28` words. -/
  log : r.κ ≤ 28
  /-- At most `maxSteps` steps. -/
  steps : r.n ≤ maxSteps
  /-- Its frames are powers below `2^κ`. -/
  frames : FramesIn guestProgram r.img r.n
  /-- Its frames at its `KECCAK`s are aligned: multiples of the window (b2c's aligned layout). -/
  aligned : KeccakFramesAligned guestProgram r.img r.n

/-- **The reference's `KECCAK`s have their blocks in windows**: the guest's offsets in windows from
an aligned frame (`functions_kecOk`). -/
theorem Ref.Ok.windows {r : Ref} (hr : r.Ok) : r.exec.KeccakBlocksInWindows :=
  guest_windows hr.log (by rw [hr.valid.2]; rfl) hr.aligned

/-! ## The certificates -/

/-- **The certificates, closed**: each is a guest function's (its code and entry), its operands below
`2^28`; and they are tied to each other as `ProgOk` asks. -/
structure ModeCerts (Ks : List Cert) (Km : Cert) (E0 : Env) : Prop where
  fn : ∀ K ∈ Ks, ∃ f ∈ Data.functions, K.code = f.code ∧ K.F.entry = f.entryPc ∧
    K.code.all offSmall = true
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
  termFr : ∀ K ∈ Ks, termFr K.F.sig = true

/-- **The certificates tied to the executor**, run on any advice. -/
theorem progOk_of {Ks : List Cert} {Km : Cert} {E0 : Env} (h : ModeCerts Ks Km E0) {adv : Advice}
    {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) : ProgOk guestProgram C Ks Km E0 where
  ok K hK := by
    obtain ⟨f, hf, hcode, hentry, hs⟩ := h.fn K hK
    exact codeOk_fn hC hf hcode hentry hs
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

/-! ## What the executor's completeness rests on -/

/-- An allocation hint: a frame's or a buffer's base, or a cell's address. -/
def isAllocHint : Hint → Bool
  | .frameAddress .. | .allocFrames .. | .alloc .. | .allocDyn .. | .allocArm .. | .cellAddress .. => true
  | _ => false

/-- A witness hint: an entry popped from a stream. -/
def isWitnessHint : Hint → Bool
  | .witnessStack .. | .witnessHeap .. => true
  | _ => false

/-- **The tracks' invariant**: the executor's registers on the reference run's, and the hint
tracks' `Y`. -/
abbrev XOf (Y : Ref → St → Prop) (r : Ref) (s : St) : Prop := Trace guestProgram r.img s ∧ Y r s

/-- **A step's premises on the reference**: at a state of the node's run with `X`, fine against the
reference memory, on the reference run. -/
abbrev OnRun (X : Ref → St → Prop) (r : Ref) (s : St) : Prop :=
  X r s ∧ Fine (refMem r.img) s ∧ OnRef guestProgram r.img r.n s

/-- **The termination facts on the reference**: at each function's entry on the reference run, each
termination fact holds of the reference memory at the frame. -/
def TermRef (R : Ref → Prop) (Ks : List Cert) (X : Ref → St → Prop) : Prop :=
  ∀ r, R r → r.Ok → ∀ K ∈ Ks, ∀ s, OnRun X r s → s.pc = K.F.entry → ∀ p ∈ K.F.sig.term,
    RIn (refMem r.img) s.fp (.lt p.1 p.2) → RRes (refMem r.img) s.fp (.lt p.1 p.2)

theorem idxIn_fr {es : List ℕ} {s : St} (hw : ∀ o ∈ es, s.mem.written (s.fp + o) = true) :
    ∀ {i : Mode.Idx}, idxFr es i = true → IdxIn s i
  | .num _, _ => trivial
  | .ex (.fr o) _, h => Mem.get_of_written (hw o (of_decide_eq_true h))
  | .ex (.hp _ _) _, h => absurd h (by simp [idxFr])

/-- **The termination facts at an entry from the reference**, read off its written entry cells. -/
theorem term_of_ref_entry {R : Ref → Prop} {Ks : List Cert} {X : Ref → St → Prop} (h : TermRef R Ks X)
    {r : Ref} (hR : R r) (hr : r.Ok) {K : Cert} (hK : K ∈ Ks) (hfr : termFr K.F.sig = true) {s : St}
    (hon : OnRun X r s) (hpc : s.pc = K.F.entry)
    (hw : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true) :
    ∀ p ∈ K.F.sig.term, LTF s p.1 p.2 := fun p hp ↦ by
  have := List.all_eq_true.mp hfr p hp
  rw [Bool.and_eq_true] at this
  have hin : ResIn s (.lt p.1 p.2) := ⟨idxIn_fr hw this.1, idxIn_fr hw this.2⟩
  exact resHolds_of_ref hon.2.1.agree hin
    (h r hR hr K hK s hon hpc p hp (rin_of hon.2.1.agree hin))

/-- **What the executor's completeness on the guest rests on**, for the reference runs `R`, the
certificates `Ks` (`main`'s `Km`, their program `E0`), the contracts `Ct` and frame predicates `Q`,
and the hint tracks' invariant `Y`, each read at a node's reference run
`r` and the executor's tables `C` for its advice. `Y` is read at the states where an instruction
starts, before its hints; a hint's obligation is at the state its predecessors at that pc reach. -/
structure ExecGaps (R : Ref → Prop) (Ks : List Cert) (Km : Cert) (E0 : Env) (Ct : Ref → Cts)
    (Q : Ref → Cert → ℕ → St → Prop) (Y : Ref → St → Prop) : Prop where
  /-- The certificates are the guest's functions, tied to each other (the core route's
  `CoreMode.coreFacts`, `assemble`). -/
  certs : ModeCerts Ks Km E0
  /-- `main`'s certificate entered past the prologue, the jump table its slots (`EndExecPro`). -/
  main : MainOk Km E0
  /-- Every function the run enters meets its frame interface (the core route's `FnSpec`, its
  checks kernel-checked, at frames with honest valuations: `frameSpec_guest`, `CoreHonAll`). -/
  frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
    FrameSpec C (refMem r.img) (OnRun (XOf Y) r) (Ct r) K (Q r K)
  /-- `main`'s contract is its mode signature's. -/
  ctMain : ∀ r, Ct r Km.F.entry = none
  /-- Each allocation hint's needs once its inputs are written, after the pc's hints before it: a
  reservation at `allocBase` of the bump pointer, aligned for a frame holding `KECCAK` blocks,
  below `maxCells`, of the size the tree allocates there (the allocation track: the bump pointer in
  `Y`, the compiler's reservation order, b2c's aligned layout). -/
  hintAlloc : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s →
    ∀ pre h post, (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    Moves (refMem r.img) s s1 → isAllocHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h
  /-- Each witness hint pops the next entry of its stream, the reference's words at its
  destination, after the pc's hints before it (the hint bridge and the witness streams' cursor in
  `Y`, against `honestPushes`). -/
  hintWitness : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s →
    ∀ pre h post, (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    Moves (refMem r.img) s s1 → isWitnessHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h
  /-- Each computed hint's destination holds, on the reference, its formula of its inputs, at any
  state the pc's hints reach (the hint bridge with the tree's exactness). -/
  hintComputed : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun (XOf Y) r s →
    h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → ∀ s1,
    Moves (refMem r.img) s s1 → HintIn s1 h → HintOk C (refMem r.img) s1 h
  /-- Each certificate's residuals hold of the reference at the state's frame (the residuals by
  family, from the honest tree). -/
  res : ∀ r, R r → r.Ok → ResRef guestProgram r.img r.n Ks (fun s ↦ XOf Y r s)
  /-- Each function's termination facts at its entry, on the reference (the loops' instances in
  the honest tree). -/
  term : TermRef R Ks (XOf Y)
  /-- The hint tracks at the executor's initial state. -/
  initY : ∀ r, R r → r.Ok → ∀ C m, Ctx.of guestProgram r.adv = .ok C → initMem r.adv r.input = .ok m →
    Y r (initSt C r.adv m)
  /-- Each step, its hints and its instruction, keeps the hint tracks. -/
  keepY : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s →
    C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
    Moves (refMem r.img) s s1 → OpModed (refMem r.img) s1 op → runOp C s1 op = .ok s' →
    Y r { s' with steps := s'.steps + 1 }
  /-- The hint tracks keep the cells the run touches within the reference's `2^κ`. -/
  usedY : ∀ r, R r → r.Ok → ∀ s, Y r s → s.mem.used ≤ 2 ^ r.κ

/-! ## The chain -/

/-- `main`'s frame lies below `maxCells`. -/
theorem mainFrame_lt : Data.adviceMainFrame < maxCells := by
  unfold maxCells
  decide

/-- **The executor follows a node's reference run**: on the guest's advice it returns a valid
execution of the reference's steps and instruction counts, of at most the reference's `2^κ` words,
committing no more cells than the reference. -/
theorem execute_ref {R : Ref → Prop} {Ks : List Cert} {Km : Cert} {E0 : Env} {Ct : Ref → Cts}
    {Q : Ref → Cert → ℕ → St → Prop} {Y : Ref → St → Prop} (G : ExecGaps R Ks Km E0 Ct Q Y)
    {r : Ref} (hR : R r) (hr : r.Ok) :
    ∃ t, execute guestProgram r.input r.adv = .ok t ∧ ValidExecution guestProgram r.input t ∧
      t.stepCount = r.n ∧ (∀ op, t.opcodeCount op = r.exec.opcodeCount op) ∧
      t.logMemorySize ≤ r.κ ∧ t.committedSize ≤ r.exec.committedSize := by
  have hκ := hr.log
  obtain ⟨t, he, hv, hn, -, hc, hlog, hsz⟩ := execute_complete_guest (Ks := Ks) (Km := Km) (E0 := E0)
    (Ct := Ct r) (Q := Q r) (X := XOf Y r) (Pro := ProAt) hκ hr.steps hr.valid guest_decodable
    mainFrame_lt (fun C hC ↦ progOk_of G.certs hC) (fun C hC K hK ↦ G.frame r hR hr C hC K hK)
    (G.ctMain r)
    (fun C hC ↦
      { hint := fun s hX hs hon pre h post hp s1 e hm hin ↦ by
          have hh : h ∈ (C.hints[s.pc]?).getD [] := by rw [hp]; simp
          cases ha : isAllocHint h
          · cases hw : isWitnessHint h
            · exact G.hintComputed r hR hr C hC s h ⟨hX, hs, hon⟩ hh ha hw s1 hm hin
            · exact G.hintWitness r hR hr C hC s ⟨hX, hs, hon⟩ pre h post hp s1 e hm hw hin
          · exact G.hintAlloc r hR hr C hC s ⟨hX, hs, hon⟩ pre h post hp s1 e hm ha hin
        res := prem_res (G.res r hR hr)
        term := fun K hK s hX hs hon hpc hw ↦
          term_of_ref_entry G.term hR hr hK (G.certs.termFr K hK) ⟨hX, hs, hon⟩ hpc hw
        ref := fun s op hX hs hon hop ↦
          refOk_of_trace hκ hC hr.frames hr.windows hs hon hX.1 hop
        xo := fun s op s1 s' hX hs hon hop e1 hm hmo e ↦
          ⟨trace_next hκ hC hm.fine (onRef_moves hm hon) (by
              unfold Trace; rw [hm.steps, hm.pc, hm.fp]; exact hX.1)
              (by rw [hm.pc]; exact hop) hmo e,
            G.keepY r hR hr C hC s op s1 s' ⟨hX, hs, hon⟩ hop e1 hm hmo e⟩ })
    (fun C hC s op _ hP hs _ hop ↦ pro_step G.main (G.certs.env Km G.certs.main).2.2.1
      (G.certs.env Km G.certs.main).2.2.2.1 G.certs.mainTerm hC rfl hP hs hop)
    (fun C m hC hm ↦ ⟨⟨by
        show run guestProgram r.img 0 Registers.initial = some ⟨g ^ 0, g ^ 0⟩
        rw [run_zero, pow_zero]
        rfl, G.initY r hR hr C m hC hm⟩, pro_init hm⟩)
    (fun s hX ↦ G.usedY r hR hr s hX.2)
  exact ⟨t, he, hv, hn, hc, hlog, hsz⟩

end

end LeanVM.Guest.EndExec
