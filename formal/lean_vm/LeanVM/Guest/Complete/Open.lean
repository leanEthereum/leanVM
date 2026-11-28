/-
  LeanVM.Guest.Complete.Open

  The end composition: `GuestExecutionComplete` from the packages' parts.
-/

module

public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.Complete.MainWin
public import LeanVM.Guest.Complete.Committed
public import LeanVM.Guest.B1.VsC.CalleesA
public import LeanVM.Guest.EndExecAGaps
public import LeanVM.Guest.EndExecRuns
public import LeanVM.Guest.Budget.CheckerCount
public import LeanVM.Guest.Budget.FramesV
public import LeanVM.Guest.Child.Accepted
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.JumpTable
public import LeanVM.Guest.Memory.RetempExactA

/-!
# The guest's execution completeness from its parts

`guestExecutionComplete_of_open : GuestOpen → GuestExecutionComplete`. `GuestOpen` is the
packages' statements (named when they were open; each is now proved, `Left.lean` and
`Holds.lean`), each a field of `GuestOpenAt` named after its owner's statement, at a choice of the aligned flags `al`, the memory floor `17 ≤ k ≤ 23`, the route's
alignment data `A`, whether the count takes the zero-challenge sum (`zs`) and the budget's
coefficients `C`; the hint-only table is the alignment's (`exA`, which the reference run's `RefH.extra`
reads).

The chain, on a node with `NodeRelation` and `DeployedLimits`:
* the children are ones the guest accepts, or some child's openings collide
  (`acceptableChildren_or_collide`);
* `verify_sub`'s placed completeness from its window and callees (`vsComplete_of_calleesA`), then
  `main`'s (`MainFromVsA`, from its callees left and its body's window by
  `mainCalleesA_to_mainFromVs_of_window`), so `main` placed at the root (`MainCompleteA`);
* B2's reference run on it (`refX_of_callAtA`): the reference `Ref` with `RefH` (its
  prologue from the jump table, `run_jumpTables`; its pops through the re-chosen temporaries,
  `pops_retempA`) and `Ref.Ok`,
  and its bounds from the checker's counts (`checker_bounds`, `checkerZero_bounds` over
  `wh`/`wz_cost_le_count` and `ch`/`cz_weight_le_count`: within `2^24` words, fewer than `2^24`
  steps, at most `2^30` committed words);
* the executor follows it (`ExecGaps.ofHintsAlloc`, `execute_ref`), within the same bounds
  (`guestExecutionComplete_of_runsWithin`).

The words go through the checker's count `nodeWordsC`, not `Count.lean`'s tables `nodeWords` that
`RunWithinCount` reads, whose deployed coefficients the checker's count exceeds: so the chain ends at
`GuestRunsWithin` directly. The zero-challenge question is `zs`: with `zs = false` the hand facts
(`MainHand`, `MainCycles`) say no `level_residual_sum__*` instance runs, i.e. no child's opening takes the sum,
and the coefficients need only cover `Coefs.checkerZero`'s; with `zs = true` the sum is counted.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **A path's entries depend only on the values its events name.** -/
theorem splice_congr_uses {rd : Reader} {σ σ' : Val} :
    ∀ {es : List Ev} (ks : List (List Pop)), EvAgree σ σ' es → splice rd σ' es ks = splice rd σ es ks
  | [], _, _ => rfl
  | .atom a :: es, ks, h => by
    have ih := splice_congr_uses (rd := rd) (es := es) ks fun e he ↦ h e (List.mem_cons_of_mem _ he)
    have hu : ∀ v ∈ atomUses a, σ' v = σ v := fun v hv ↦ h _ List.mem_cons_self v hv
    rw [splice, splice, ih]
    congr 1
    cases a with
    | hint hh =>
      cases hh with
      | witness s d =>
        cases d with
        | stack vs =>
          simp only [Atom.pops, Hint.pops, Dest.words, List.cons.injEq, Prod.mk.injEq, true_and,
            and_true]
          exact List.map_congr_left fun v hv ↦ hu v hv
        | heap p off len =>
          simp only [Atom.pops, Hint.pops, Dest.words]
          rw [hu p (by simp [atomUses, hintUses, destUses])]
      | _ => rfl
    | _ => rfl
  | .inK _ :: es, ks, h => by
    rw [splice, splice, splice_congr_uses (rd := rd) ks fun e he ↦ h e (List.mem_cons_of_mem _ he)]
  | .call .. :: es, ks, h => by
    rw [splice, splice, splice_congr_uses (rd := rd) ks.tail fun e he ↦ h e (List.mem_cons_of_mem _ he)]
  | .skip .. :: es, ks, h => by
    rw [splice, splice, splice_congr_uses (rd := rd) ks.tail fun e he ↦ h e (List.mem_cons_of_mem _ he)]

variable {P : Core.Program} {fs : String → ℕ} {al : String → Bool} {ν : ℕ → String → Val → V → E}
  {rd : Reader}

mutual
/-- **A re-chosen tree, aligned, pops what the tree pops.** -/
theorem pops_retempA (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ),
    (t.retempA P fs al ν pos).pops P rd = t.pops P rd
  | .node f σ bufs kids, pos => by
    rw [retempA_node, Tree.pops, Tree.pops, events_retemp hF (bufs' := bufs) (ks' := kids),
      popsKids_retempKidsA hF]
    apply splice_congr_uses
    intro e he v hv
    unfold Tree.events at he
    simp only [Tree.name, Tree.val] at he
    cases hf : P.find? f with
    | none => simp [hf] at he
    | some fn =>
      simp only [hf] at he
      cases hw : walk σ fn.body with
      | ret es vs => simp only [hw] at he; exact evAgree_retemp hF hf hw e he v hv
      | fall _ => simp [hw] at he
      | stuck => simp [hw] at he
  | .phantom f σ, pos => by rw [retempA_phantom]

/-- `pops_retempA` for the callees. -/
theorem popsKids_retempKidsA (hF : P.Fresh) : ∀ (ps : List (ℕ × ℕ)) (ks : List Tree),
    Tree.popsKids P rd (Tree.retempKidsA P fs al ν ps ks) = Tree.popsKids P rd ks
  | _, [] => by rw [retempKidsA_nil]
  | [], k :: ks => by rw [Tree.retempKidsA]
  | p :: ps, k :: ks => by
    rw [retempKidsA_cons, Tree.popsKids, Tree.popsKids, pops_retempA hF k p, popsKids_retempKidsA hF ps ks]
end

end

end LeanVM.Guest.Memory

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness LeanVM.Guest.Budget LeanVM.Guest.EndExec LeanVM.Guest.Mode
open LeanVM.Prover.Exec
open LeanVM.Guest.Bridge (FnAl)

@[expose] public section

/-! ## The prologue, step by step -/

/-- A non-`JUMP` that `Holds` falls through in one step. -/
theorem run_one_of_holds {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ} {pc : ℕ} {fp : K}
    {ins : OffsetInstruction} (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (hj : ins.isJump = false) (h : Holds L pc fp ins) :
    run prog L 1 ⟨addressOfIndex pc, fp⟩ = some ⟨addressOfIndex (pc + 1), fp⟩ := by
  rw [run_succ_of_ne (gpow_ne_pcFinal hpc), step_of_fetch_eq_some hf, (execute_iff_holds hj).mpr ⟨h, rfl⟩]
  rfl

/-- **The jump table's prologue, step by step**: on a memory holding the jump table, the run's
`i`-th registers, `i ≤ proLen`, are pc `i` in frame `0`. -/
theorem run_jumpTables {κ : ℕ} {L : MemoryImage κ} (h : End.JumpTables L) :
    ∀ i ≤ proLen, run guestProgram L i Registers.initial = some (Bridge.regs i 0) := by
  have h0 : ∀ j, Bridge.regs j 0 = ⟨addressOfIndex j, 1⟩ := fun j => by
    rw [regs_eq]; simp [addressOfIndex]
  intro i
  induction i with
  | zero =>
    intro _
    rw [run_zero, h0]
    simp [Registers.initial, addressOfIndex]
  | succ i ih =>
    intro hi
    have hi' : i < Data.f0.instructionCount := Nat.lt_of_succ_le hi
    obtain ⟨o, k0, k1, hins, hq⟩ := End.f0_instr hi'
    have hf := End.f0_fetch hi'
    rw [hins] at hf
    have hH : Holds L i 1 (.set o k0 k1) := by
      show L.read (1 * addressOfIndex o) = some (OffsetInstruction.immediateWord k0 k1)
      rw [End.gpow_mul_one]
      exact h _ hq
    have h1 := run_one_of_holds hf (End.f0_pc_lt hi') rfl hH
    rw [Semantics.run_add, ih (Nat.le_of_succ_le hi), h0, Option.bind_eq_bind, Option.bind_some, h1, h0]

/-! ## The packages' statements -/

/-- The guest's aligned layout at the flags `al`: b2c's frame sizes, headers, cells and certificate
cells. -/
noncomputable abbrev lay (al : String → Bool) : Lay := ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩

/-- The reference runs of the honest tree. -/
def RefOf (al : String → Bool) (r : Ref) : Prop := ∃ d, RefH (lay al) d r

instance : Nonempty RefD := ⟨⟨fun _ => none, .phantom "" (fun _ => 0), []⟩⟩

/-- **The honest data of a reference run**: chosen among those it is a reference run of (the hint
bridge's `D`, b2c's construction). -/
noncomputable def refD (al : String → Bool) (r : Ref) : RefD := Classical.epsilon fun d => RefH (lay al) d r

theorem refH_refD {al : String → Bool} {r : Ref} (h : RefOf al r) : RefH (lay al) (refD al r) r :=
  Classical.epsilon_spec h

/-- A node's items for the count (the children's shapes unread by `nodeWordsC` and `Coefs.budget`). -/
def itemsOf (s : NodeStatement) (w : NodeWitness) : NodeItems :=
  NodeItems.ofWitness (fun _ => ⟨0, 0, false⟩) s w

/-- **`main`'s honest tree on a node**: `main`'s, valid on `rd`, placed at the root, popping the
honest pushes, exact at every node (what `MainCompleteA` and B2 give of it). -/
structure MainHonest (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (rd : Reader) (t : Tree) :
    Prop where
  name : t.name = "main"
  valid : t.Valid coreProgram rd [] []
  bufsOk : t.BufsOk coreProgram
  placed : t.PlacedA coreProgram B2C.fs al B2C.cert (0, t.block B2C.fs coreProgram.loop)
  pops : SameStreams (t.pops coreProgram rd) (Prover.honestPushes guestBytecode guestSeed s w)
  exact : t.Every (ExactAt coreProgram rd)

/-- The checker's coefficients: the zero-challenge sum counted (`zs`) or absent. -/
def checkerOf (zs : Bool) : Coefs := if zs then Coefs.checker else Coefs.checkerZero

/-- **The hand facts of `main`'s tree, the zero-challenge sum counted** (budget4's left items 1 to 3,
`wh_cost_le_count`'s hypotheses). -/
def HandH (it : NodeItems) (rd : Reader) (t : Tree) : Prop :=
  ∃ σ bufs kids, t = .node "main" σ bufs kids ∧
    (∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (whCertAt (daWordsC it.rows) (loopWordsC iterSum it)) (whHandAt (daWordsC it.rows) (loopWordsC iterSum it))
      whOut)) ∧
    (∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl).params Data.whloopHand 62
        (fun k => k.Every (HandFact coreProgram (whCertAt (daWordsC it.rows) (loopWordsC iterSum it))
          (whHandAt (daWordsC it.rows) (loopWordsC iterSum it)) whOut)) k S ∧ S ≤ loopWordsC iterSum it) ∧
    ArgsPre Data.whmainHand.pre ([] ++ Data.whmainHand.vps.map σ) ∧
    Data.whmainHand.b.eval ([] ++ Data.whmainHand.vps.map σ) ≤ mainWordsC it

/-- **The hand facts of `main`'s tree, the zero-challenge sum absent** (`wz_cost_le_count`'s
hypotheses): no `level_residual_sum__*` instance (`wzOut`), so no child's opening takes the sum. -/
def HandZ (it : NodeItems) (rd : Reader) (t : Tree) : Prop :=
  ∃ σ bufs kids, t = .node "main" σ bufs kids ∧
    (∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (wzCertAt (daWordsC it.rows) (loopWordsC iterZero it)) (wzHandAt (daWordsC it.rows) (loopWordsC iterZero it))
      wzOut)) ∧
    (∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.wzidxLoop]'wz_nodeIdx.hl).params Data.wzloopHand 62
        (fun k => k.Every (HandFact coreProgram (wzCertAt (daWordsC it.rows) (loopWordsC iterZero it))
          (wzHandAt (daWordsC it.rows) (loopWordsC iterZero it)) wzOut)) k S ∧ S ≤ loopWordsC iterZero it) ∧
    ArgsPre Data.wzmainHand.pre ([] ++ Data.wzmainHand.vps.map σ) ∧
    Data.wzmainHand.b.eval ([] ++ Data.wzmainHand.vps.map σ) ≤ mainWordsC it

/-- **`main`'s honest tree within the checker's count** (b1c, vsc: the honest valuation's hand facts),
on every node within the deployed limits whose children the guest accepts. -/
def MainHand (al : String → Bool) (zs : Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd t, MainHonest al s w rd t → if zs then HandH (itemsOf s w) rd t else HandZ (itemsOf s w) rd t

/-- **The hand facts of `main`'s tree at opcode `op`, the zero-challenge sum counted** (budget5,
`ch_weight_le_count`'s hypotheses). -/
def CycH (op : Opcode) (it : NodeItems) (rd : Reader) (t : Tree) : Prop :=
  ∃ σ bufs kids, t = .node "main" σ bufs kids ∧
    (∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (chCertAt op (daCntC op it.rows) (loopCntC iterSumV op it))
      (chHandAt op (daCntC op it.rows) (loopCntC iterSumV op it)) (chOut op))) ∧
    (∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
        (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (chCertAt op (daCntC op it.rows) (loopCntC iterSumV op it))
          (chHandAt op (daCntC op it.rows) (loopCntC iterSumV op it)) (chOut op))) k S ∧
        S ≤ loopCntC iterSumV op it) ∧
    ArgsPre Data.chmainHand.pre ([] ++ Data.chmainHand.vps.map σ) ∧
    (Data.chmainHand.b.proj (B2C.opIdx op)).eval ([] ++ Data.chmainHand.vps.map σ) ≤ mainCntC op it

/-- **The hand facts of `main`'s tree at opcode `op`, the zero-challenge sum absent** (budget5,
`cz_weight_le_count`'s hypotheses). -/
def CycZ (op : Opcode) (it : NodeItems) (rd : Reader) (t : Tree) : Prop :=
  ∃ σ bufs kids, t = .node "main" σ bufs kids ∧
    (∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (czCertAt op (daCntC op it.rows) (loopCntC iterZeroV op it))
      (czHandAt op (daCntC op it.rows) (loopCntC iterZeroV op it)) (czOut op))) ∧
    (∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.czidxLoop]'cz_nodeIdx.hl).params
        (Data.czloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (czCertAt op (daCntC op it.rows) (loopCntC iterZeroV op it))
          (czHandAt op (daCntC op it.rows) (loopCntC iterZeroV op it)) (czOut op))) k S ∧
        S ≤ loopCntC iterZeroV op it) ∧
    ArgsPre Data.czmainHand.pre ([] ++ Data.czmainHand.vps.map σ) ∧
    (Data.czmainHand.b.proj (B2C.opIdx op)).eval ([] ++ Data.czmainHand.vps.map σ) ≤ mainCntC op it

/-- **`main`'s honest tree's instructions within the checker's count** (b1c, vsc: the honest
valuation's hand facts at each opcode). -/
def MainCycles (al : String → Bool) (zs : Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd t, MainHonest al s w rd t → ∀ op, if zs then CycH op (itemsOf s w) rd t else CycZ op (itemsOf s w) rd t

/-- **The frames the count reads within the certificates'** (budget2's left item 3): b2c's frame
sizes within `fsW` on the guest's functions (the only weights a valid tree's cost reads; off them
`fsW` is `0`, `Budget.not_fs_le_fsW`), the aligned flags within `alW`, a loop's tail frame within its
frame. -/
structure FramesWithin (al : String → Bool) : Prop where
  fs : FnWithin coreProgram B2C.fs fsW
  al : ∀ g, al g = true → alW g = true
  tail : ∀ f, B2C.fs (tailKey f) ≤ B2C.fs f

/-- **The reference run's frames** (the route's tree track, `traceRef`, against B2's aligned
layout): on every reference run of the honest tree that is a valid execution, every state's frame a
power below `2^κ` and each `KECCAK`'s a multiple of the window. -/
def RefFrames (al : String → Bool) : Prop :=
  ∀ r, RefH (lay al) (refD al r) r → ValidExecution guestProgram r.input r.exec →
    FramesIn guestProgram r.img r.n ∧ KeccakFramesAligned guestProgram r.img r.n

/-- **The core route's fields of `ExecGaps`** (route), at the hint tracks `Y`. -/
structure RouteGaps (R : Ref → Prop) (Y : Ref → St → Prop) (Ks : List Mode.Cert) (Km : Mode.Cert)
    (E0 : Mode.Env) (Ct : Ref → Mode.Cts) (Q : Ref → Mode.Cert → ℕ → St → Prop) : Prop where
  certs : ModeCerts Ks Km E0
  main : MainOk Km E0
  frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
    FrameSpec C (refMem r.img) (OnRun (XOf Y) r) (Ct r) K (Q r K)
  ctMain : ∀ r, Ct r Km.F.entry = none
  res : ∀ r, R r → r.Ok → ResRef guestProgram r.img r.n Ks (fun s ↦ XOf Y r s)
  term : TermRef R Ks (XOf Y)

/-- **What `GuestExecutionComplete` rests on, but the coefficients**, at the aligned flags `al`, the
memory floor `k`, the hint-only table `exOf`, the alignment data `A` and the zero-challenge choice
`zs`: each field a package's statement. -/
structure GuestRestAt (al : String → Bool) (k : ℕ) (exOf : ℕ → List (ℕ × ℕ)) (A : String → FnAl)
    (zs : Bool) : Prop where
  /-- vsc: `verify_sub`'s window from its callees. -/
  vsWindows : VsC.VsWindowsFromCallees al k
  /-- vsc: `verify_sub`'s callees, placed. -/
  vsCallees : VsC.VsCalleesCompleteA B2C.fs al B2C.cert k
  /-- b1c: `main`'s callees left, placed, each ending within `2^40` of its cursor below `2^60`. -/
  mainCallees : MainCalleesOpenA al k
  /-- b1c: `main`'s body as one placed window from its callees and `verify_sub`'s completeness. -/
  mainWindow : MainWindowFromCallees al k
  /-- b1c, vsc: `main`'s honest tree's hand facts for its words (with `zs = false`, no zero-challenge
  sum). -/
  hand : MainHand al zs
  /-- budget: the frames within the certificates'. -/
  framesWithin : FramesWithin al
  /-- b1c, vsc: `main`'s honest tree's hand facts at each opcode. -/
  cycles : MainCycles al zs
  /-- route: the hint-only cells fresh. -/
  extraOk : ExtraOk exOf
  /-- route: the reference run's frames. -/
  refFrames : RefFrames al
  /-- hints: the hint bridge's premises. -/
  hints : HintHyps (lay al) (refD al) A
  /-- alloc: the cursor facts. -/
  cur : CurHyps (lay al) (refD al) A
  /-- alloc: the buffer hints. -/
  bufHint : BufHint (lay al) (refD al) A
  /-- alloc: the frame hints. -/
  frameHint : FrameHint (lay al) (refD al) A
  /-- alloc: the address hints. -/
  addrReady : AddrReady (lay al) (refD al) A
  /-- route: the certificates, the frames, the residuals and the termination facts. -/
  route : ∃ (Ks : List Mode.Cert) (Km : Mode.Cert) (E0 : Mode.Env) (Ct : Ref → Mode.Cts)
      (Q : Ref → Mode.Cert → ℕ → St → Prop),
    RouteGaps (RefOf al) (YH (lay al) (refD al) A (YAlloc (lay al) (refD al) A)) Ks Km E0 Ct Q

/-- **What `GuestExecutionComplete` rests on**, at the coefficients `C` too: the budget at `C`
covers the checker's count and fits `2^24` on every node within the limits. -/
structure GuestOpenAt (al : String → Bool) (k : ℕ) (exOf : ℕ → List (ℕ × ℕ)) (A : String → FnAl)
    (zs : Bool) (C : Coefs) : Prop extends GuestRestAt al k exOf A zs where
  /-- The coefficients cover the checker's count. -/
  coefs : Coefs.Above (checkerOf zs) C
  /-- The budget at `C` within `2^24` on every node within the limits. -/
  fits : ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
    C.budget (itemsOf s w) ≤ 2 ^ 24

/-- **What `GuestExecutionComplete` rests on.** -/
def GuestOpen : Prop :=
  ∃ (al : String → Bool) (k : ℕ) (A : String → FnAl) (zs : Bool) (C : Coefs),
    17 ≤ k ∧ k ≤ 23 ∧ GuestOpenAt al k exA A zs C

/-! ## The glue -/

/-- With the deployed coefficients the budget fits by `DeployedLimits`. -/
theorem fits_deployed (s : NodeStatement) (w : NodeWitness) (hl : DeployedLimits s w) :
    Coefs.deployed.budget (itemsOf s w) ≤ 2 ^ 24 := by
  rw [itemsOf, deployed_budget_ofWitness]; exact hl.withinMemoryBudget

theorem rows_le_32 {s : NodeStatement} {w : NodeWitness} (hl : DeployedLimits s w) :
    ∀ n ∈ (itemsOf s w).rows, n ≤ 32 := by
  intro n hn
  simp only [itemsOf, NodeItems.ofWitness, Option.mem_def, Option.map_eq_some_iff] at hn
  obtain ⟨p, hp, rfl⟩ := hn
  exact hl.atMostMaxRows p hp

/-- **The reference run's bounds from the checker's count**: a valid execution of `main`'s honest
tree's re-chosen memory, its memory's log the tree's words', its opcode counts within B2's count. -/
theorem bounds_main {al : String → Bool} {zs : Bool} {C : Coefs} (hH : MainHand al zs)
    (hY : MainCycles al zs) (hW : FramesWithin al) (hC : Coefs.Above (checkerOf zs) C) {s : NodeStatement}
    {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hB : C.budget (itemsOf s w) ≤ 2 ^ 24) {rd : Reader}
    {t : Tree} (ht : MainHonest al s w rd t) {input : PublicInput} {x : Execution guestProgram}
    (hv : ValidExecution guestProgram input x)
    (hlog : x.logMemorySize ≤ logMem (t.wordsA B2C.fs coreProgram.loop al))
    (hc : ∀ op, x.opcodeCount op ≤ B2C.cnt t op) :
    x.logMemorySize ≤ 24 ∧ x.stepCount < 2 ^ 24 ∧ x.committedSize ≤ 2 ^ 30 := by
  have hd := declaredFit_of_held (shape := fun _ => ⟨0, 0, false⟩) hr.1
  have hh := hH s w hr hl hok rd t ht
  have hy := hY s w hr hl hok rd t ht
  cases zs with
  | false =>
    obtain ⟨σ, bufs, kids, rfl, hk, hlp, hpre, hm⟩ := hh
    refine checkerZero_bounds_v hC hd (rows_le_32 hl) hB hW.fs hW.al hW.tail ht.valid ht.bufsOk
      (wz_cost_le_count ht.valid ht.bufsOk hk hlp hpre hm) hv hlog
      (opcodeCount_le_cnt ht.valid hc fun op => ?_)
    obtain ⟨σ', bufs', kids', he, hk', hlp', hpre', hm'⟩ := (by simpa using hy op : CycZ op _ rd _)
    cases he
    exact cz_weight_le_count op ht.valid ht.bufsOk hk' hlp' hpre' hm'
  | true =>
    obtain ⟨σ, bufs, kids, rfl, hk, hlp, hpre, hm⟩ := hh
    refine checker_bounds_v hC hd (rows_le_32 hl) hB hW.fs hW.al hW.tail ht.valid ht.bufsOk
      (wh_cost_le_count ht.valid ht.bufsOk hk hlp hpre hm) hv hlog
      (opcodeCount_le_cnt ht.valid hc fun op => ?_)
    obtain ⟨σ', bufs', kids', he, hk', hlp', hpre', hm'⟩ := (by simpa using hy op : CycH op _ rd _)
    cases he
    exact ch_weight_le_count op ht.valid ht.bufsOk hk' hlp' hpre' hm'

theorem digestCells_eq (d : Digest) :
    Prover.digestCells d = [(PublicInput.ofDigest d).word0, (PublicInput.ofDigest d).word1] := rfl

/-- **`main`'s end within `2^24` from the count**: a placed `main` at the root on a node, its end below
`2^63`, the honest pops and exactness its post-condition. -/
theorem end_le_of_count {al : String → Bool} {zs : Bool} {C : Coefs} {k : ℕ} (hk : k ≤ 23)
    (hH : MainHand al zs) (hW : FramesWithin al) (hC : Coefs.Above (checkerOf zs) C) {s : NodeStatement}
    {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hB : C.budget (itemsOf s w) ≤ 2 ^ 24)
    {D : ℕ → Prop} {Out : Reader → Prop} {e : ℕ}
    (h : CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out
      (fun rd => ReadsAt rd 1 (Prover.digestCells (statementDigest guestSeed s)))
      (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.honestPushes guestBytecode guestSeed s w) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs "main") 0 (B2C.fs "main") e) (he : e ≤ 2 ^ 63) : e ≤ 2 ^ 24 := by
  set input := PublicInput.ofDigest (statementDigest guestSeed s) with hinput
  set hdr : E × E := (input.word0, input.word1) with hhdr
  obtain ⟨W, hW', hce, -, hrd⟩ := h
  have hB2 := B2C.two_le_fs "main"
  have hκ : logMem e < 64 := by
    have : logMem e ≤ 63 := logMem_le_iff.mpr ⟨by norm_num, he⟩
    omega
  have hle : e ≤ 2 ^ logMem e := le_two_pow_logMem e
  have h4 : 4 ≤ 2 ^ logMem e :=
    Nat.le_trans (by decide : 4 ≤ 2 ^ 23) (Nat.pow_le_pow_right (by decide) (twentyThree_le_logMem e))
  have hread := fun {j : ℕ} (hj : j < 2 ^ logMem e) => rootImage_read hκ hdr W hj
  have hl' : LowDef k (rootImage (logMem e) hdr W).read := fun i hi => by
    have : 2 ^ k ≤ 2 ^ logMem e := Nat.pow_le_pow_right (by decide) (hk.trans (twentyThree_le_logMem e))
    rw [hread (by omega)]; rfl
  have hw : HoldsWords (rootImage (logMem e) hdr W).read W := by
    intro q hq j hj
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    rw [Main.addr_ofK]
    have hb := hW'.1 q hq
    have h2 : 2 ≤ q.1 + j := by omega
    rw [hread (by omega)]
    simp only [show q.1 + j ≠ 0 by omega, show q.1 + j ≠ 1 by omega, ↓reduceIte]
    rw [wordOf_of_mem hW'.2 hq (by omega) (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem]
  have hpre : ReadsAt (rootImage (logMem e) hdr W).read 1 (Prover.digestCells (statementDigest guestSeed s)) := by
    rw [digestCells_eq, ← hinput]
    intro j hj
    refine ⟨(isInK_iff _).mpr ⟨_, one_eq_ofK⟩, ?_⟩
    rw [one_eq_ofK, Main.addr_ofK, Nat.zero_add]
    have hj2 : j < 2 := by simpa using hj
    rw [hread (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  obtain ⟨t, hn, hv, hb, hbl, hend, hpl, -, -, -, hq⟩ := hrd _ hl' hw hpre
  have hwA : t.wordsA B2C.fs coreProgram.loop al = e := by
    unfold Tree.wordsA; rw [hbl, hend]
  have hmh : MainHonest al s w _ t := ⟨hn, hv, hb, by rw [hbl]; exact hpl, hq.1, hq.2⟩
  have hd := declaredFit_of_held (shape := fun _ => ⟨0, 0, false⟩) hr.1
  have hh := hH s w hr hl hok _ t hmh
  rw [← hwA]
  cases zs with
  | false =>
    obtain ⟨σ, bufs, kids, rfl, hk', hlp, hpre', hm⟩ := hh
    exact (wordsA_le_of_cost_v hW.fs hW.al hW.tail hv hb ((wz_cost_le_count hv hb hk' hlp hpre' hm).trans
      (nodeWordsC_le (K := iterZero) hC _ hd (rows_le_32 hl)))).trans hB
  | true =>
    obtain ⟨σ, bufs, kids, rfl, hk', hlp, hpre', hm⟩ := hh
    exact (wordsA_le_of_cost_v hW.fs hW.al hW.tail hv hb ((wh_cost_le_count hv hb hk' hlp hpre' hm).trans
      (nodeWordsC_le (K := iterSum) hC _ hd (rows_le_32 hl)))).trans hB

/-- **A placed `main` below `2^63` ends within `2^30`** on every node, from the count: `MainEndWithin`. -/
theorem endWithin_of_count {al : String → Bool} {zs : Bool} {C : Coefs} {k : ℕ} (hk : k ≤ 23)
    (hH : MainHand al zs) (hW : FramesWithin al) (hC : Coefs.Above (checkerOf zs) C)
    (hfits : ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      C.budget (itemsOf s w) ≤ 2 ^ 24) : MainEndWithin al k :=
  fun _ _ hr hl hok _ _ _ h he =>
    (end_le_of_count hk hH hW hC hr hl hok (hfits _ _ hr hl) h he).trans (by norm_num)

/-- **A node's reference run**: on a node within the limits whose children the guest accepts, a
reference run of the honest tree under the deployed seed, at the node, `Ok`, within `2^24` words,
of fewer than `2^24` steps, committing at most `2^30` words. -/
theorem ref_of_open {al : String → Bool} {k : ℕ} {A : String → FnAl}
    {zs : Bool} {C : Coefs} (hk17 : 17 ≤ k) (hk : k ≤ 23) (h : GuestOpenAt al k exA A zs C)
    {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) :
    ∃ r : Ref, RefOf al r ∧ r.Ok ∧ r.seed = guestSeed ∧ r.s = s ∧ r.w = w ∧ r.κ ≤ 24 ∧ r.n < 2 ^ 24 ∧
      r.exec.committedSize ≤ 2 ^ 30 := by
  have hvs := VsC.vsComplete_of_calleesA h.vsWindows (by omega) h.vsCallees guestSeed
  obtain ⟨D, Out, e, he, hc⟩ :=
    mainCalleesA_to_mainFromVs_of_window h.mainWindow hk17 hk h.mainCallees.toMainCalleesA
      (endWithin_of_count hk h.hand h.framesWithin h.coefs h.fits) hvs s w hr hl hok
  set input := PublicInput.ofDigest (statementDigest guestSeed s) with hinput
  rw [digestCells_eq] at hc
  obtain ⟨t, M, hb, ⟨hpops, hex⟩, ν, n, hname, ⟨rdh, hHA, hHX⟩, hv, hcnt, hcnteq, hwA, hhw, hxr⟩ :=
    refX_of_callAtA al h.extraOk input hk (B2C.two_le_fs "main") he hc
  have hmh : MainHonest al s w M.read t := ⟨hb.name, hb.valid, hb.bufsOk, hb.placed, hpops, hex⟩
  set T := B2C.reTree al ν t with hT
  set X := B2C.refWrites al exA (input.word0, input.word1) t M with hX
  let r : Ref := ⟨guestSeed, s, w, logMem (T.wordsA B2C.fs coreProgram.loop al),
    honestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) T X, n⟩
  have hcnt' : ∀ op, r.exec.opcodeCount op ≤ B2C.cnt t op := fun op =>
    (hcnt op).trans (le_of_eq (congrFun hcnteq op))
  obtain ⟨hκ, hn, hsz⟩ := bounds_main h.hand h.cycles h.framesWithin h.coefs hr hl hok (h.fits s w hr hl) hmh
    (x := r.exec) hv (le_of_eq (congrArg logMem hwA)) hcnt'
  have hRH : RefH (lay al) ⟨M.read, T, X⟩ r :=
    { κ := rfl
      img := fun _ => rfl
      name := hname
      honest := ⟨rdh, hHA, hHX⟩
      pro := run_jumpTables (B2C.jumpTables_cover hHA.toHonestA hHX.covers hname)
      hintWords := hhw
      pops := by
        show SameStreams (T.pops coreProgram M.read) _
        rw [hT, pops_retempA coreProgram_fresh]
        exact hpops
      exact := every_exact_retempA coreProgram_fresh t _ hex
      extra := hxr }
  have hR : RefOf al r := ⟨_, hRH⟩
  obtain ⟨hfr, hal⟩ := h.refFrames r (refH_refD hR) hv
  have hms : (2 : ℕ) ^ 24 ≤ maxSteps := by unfold maxSteps; norm_num
  have hκ28 : r.κ ≤ 28 := le_trans hκ (by norm_num)
  exact ⟨r, hR, ⟨hv, hκ28, by have : r.n < 2 ^ 24 := hn; omega, hfr, hal⟩, rfl, rfl, rfl, hκ, hn, hsz⟩

/-- **`GuestExecutionComplete` from the packages' statements.** -/
theorem guestExecutionComplete_of_open (h : GuestOpen) : GuestExecutionComplete := by
  obtain ⟨al, k, A, zs, C, hk17, hk, h⟩ := h
  obtain ⟨Ks, Km, E0, Ct, Q, hg⟩ := h.route
  have G : ExecGaps (RefOf al) Ks Km E0 Ct Q (YH (lay al) (refD al) A (YAlloc (lay al) (refD al) A)) :=
    ExecGaps.ofHintsAlloc h.hints (fun r hr => refH_refD hr) rfl h.cur h.bufHint h.frameHint h.addrReady
      hg.certs hg.main hg.frame hg.ctMain hg.res hg.term
  refine guestExecutionComplete_of_runsWithin fun s w hrel hlim ↦ ?_
  rcases LeanVM.Guest.Child.acceptableChildren_or_collide hrel with hok | hcol
  · left
    obtain ⟨r, hR, hr, hseed, rfl, rfl, hκ, hn, hsz⟩ := ref_of_open hk17 hk h hrel hlim hok
    obtain ⟨t, he, -, htn, -, hlog, hc⟩ := execute_ref G hR hr
    exact ⟨t, (guestExecution_eq hseed).trans he, hlog.trans hκ, by rw [htn]; exact hn, hc.trans hsz⟩
  · exact Or.inr hcol


/-- **The statement's coefficients cover the checker's count**, the zero-challenge sum counted. -/
theorem deployed_above_checker : Coefs.Above (checkerOf true) Coefs.deployed :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **What `GuestExecutionComplete` rests on at the statement's coefficients**: every package's
statement, the zero-challenge sum counted; the coefficients' two fields hold. -/
def GuestRest : Prop :=
  ∃ (al : String → Bool) (k : ℕ) (A : String → FnAl),
    17 ≤ k ∧ k ≤ 23 ∧ GuestRestAt al k exA A true

/-- **`GuestExecutionComplete` from the packages' statements**, at the statement's
coefficients. -/
theorem guestExecutionComplete_of_rest (h : GuestRest) : GuestExecutionComplete := by
  obtain ⟨al, k, A, hk17, hk, hr⟩ := h
  exact guestExecutionComplete_of_open ⟨al, k, A, true, Coefs.deployed, hk17, hk,
    { hr with coefs := deployed_above_checker, fits := fun s w _ hl ↦ fits_deployed s w hl }⟩

end

end LeanVM.Guest.Complete
