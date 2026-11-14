/-
  LeanVM.Guest.EndExecRef

  A node's reference run, the one the executor is to follow: the honest memory of `main`'s honest
  tree, extended by its hints' heap words, a valid execution within `2^30` committed cells, its
  tree exact and popping the honest pushes.
-/

module

public import LeanVM.Guest.Bridge.TrackHonest
public import LeanVM.Guest.Budget.ClosedPE
public import LeanVM.Guest.Executor

/-!
# The reference run of a node

`Ref`: a node and the reference run built for it, `Ref.Ok` what is proved of it (`ref_exists`):
the honest memory of a re-choice of the temporaries of a tree valid on a memory `rd0`, every node of
that tree exact on `rd0` (`ExactAt`), extended by the words its hints write to the heap
(`honestX`, read off `rd0`); a valid execution of the guest on the statement's digest within
`2^30` committed cells; the tree's pops on `rd0` the honest pushes but the advised sizes, stream by
stream. `ref_exists` is `End.refX_valid_of_main` and `Bridge.honest_of_mainP` on one tree, under
`MainCompletePE` (`Budget.mainCompletePE_deployed`, given `Budget.MainExactHyp`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (hdrOf bytecode work publicInputOf)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)
open LeanVM.Prover.Exec (Advice)

@[expose] public section

/-- **A node and its reference run**: the seed, statement and witness; the memory `rd0` B1's tree is
valid on; the honest tree `T`; the heap words `X` its hints write; the run's steps. -/
structure Ref where
  seed : Digest
  s : NodeStatement
  w : NodeWitness
  rd0 : Reader
  T : Tree
  X : List Write
  n : ℕ

/-- The header of the node's statement digest. -/
abbrev Ref.hdr (r : Ref) : E × E := hdrOf (statementDigest r.seed r.s)

/-- The reference memory's log-size. -/
noncomputable abbrev Ref.κ (r : Ref) : ℕ := logMem (r.T.total B2C.fs)

/-- **The reference memory**: the honest memory of `T` extended by `X`. -/
noncomputable abbrev Ref.img (r : Ref) : MemoryImage r.κ :=
  honestX coreProgram B2C.fs B2C.H B2C.C r.hdr r.T r.X

/-- The node's public input. -/
abbrev Ref.input (r : Ref) : PublicInput := publicInputOf (statementDigest r.seed r.s)

/-- The guest's advice on the node. -/
abbrev Ref.adv (r : Ref) : Advice := guestAdvice r.seed r.s r.w

/-- **The reference execution.** -/
noncomputable abbrev Ref.exec (r : Ref) : Execution guestProgram := ⟨r.κ, r.img, r.n⟩

/-- **What is proved of a node's reference run.** -/
structure Ref.Ok (r : Ref) : Prop where
  rel : NodeRelation bytecode r.seed r.s r.w
  lim : GuestLimits r.s r.w
  kids : ChildrenOk bytecode r.seed r.w
  /-- `T` re-chooses the temporaries of a tree valid on `rd0`, placed, its loads and heap hints in
  its data, every node exact on `rd0`. -/
  tree : ∃ (t : Tree) (ν : ℕ → String → Val → V → E), t.Valid coreProgram r.rd0 [] [] ∧
    t.BufsOk coreProgram ∧ t.Placed coreProgram B2C.fs B2C.cert (0, t.block B2C.fs coreProgram.loop) ∧
    t.LoadsIn coreProgram B2C.fs B2C.cert (fun i => i < 2) (0, t.block B2C.fs coreProgram.loop) ∧
    t.HintsIn coreProgram B2C.fs B2C.cert (fun i => i < 2) (0, t.block B2C.fs coreProgram.loop) ∧
    t.Every (ExactAt coreProgram r.rd0) ∧
    r.T = t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop)
  name : r.T.name = "main"
  honest : ∃ rd, HonestAt coreProgram B2C.fs B2C.H B2C.C r.hdr r.T B2C.cert rd [] [] ∧
    HonestX coreProgram B2C.fs B2C.H B2C.C r.hdr r.T rd [] [] r.X
  valid : ValidExecution guestProgram r.input r.exec
  size : r.exec.committedSize ≤ 2 ^ 30
  /-- The extension holds each heap word the tree's hints write, as `rd0` does. -/
  hintWords : ∀ a ∈ hintWords coreProgram B2C.fs B2C.H r.hdr r.T, ∃ v, r.rd0 a = some v ∧
    r.img.read a = some v
  /-- The tree pops the honest pushes, but the advised sizes, stream by stream. -/
  pops : SameStreams (r.T.pops coreProgram r.rd0)
    ((Hints.honestPushes bytecode r.seed r.s r.w).filter (·.1 != Hints.heapSizeStream))

section

open LeanVM.Guest.End LeanVM.Guest.B2C

/-- **Every node within the budget has a reference run**, given the exactness still open
(`Budget.MainExactHyp`). -/
theorem ref_exists (hE : Budget.MainExactHyp) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 →
      ∃ r : Ref, r.seed = seed ∧ r.s = s ∧ r.w = w ∧ r.Ok := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨N, L, hcons, hin, hN, hNb, hrelL⟩ := Budget.mainCompletePE_deployed hE seed s w hrel hlim hok hbs
  set hdr := hdrOf (statementDigest seed s) with hhdr
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  set M := B1.Main.imageOf (logMem N) L hdr with hM
  have hlow : LowDef (logMem N) M.read := fun i hi => by
    rw [MemoryImage.read_gpow h64 M ⟨i, hi⟩]; rfl
  have hL := B1.Main.memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := B1.Main.imageOf_hdr h64 (le_trans (by decide) (twentyThree_le_logMem N)) L hdr
  have e0 : (1 : K) = Parameters.addressOfIndex 0 := by simp [Parameters.addressOfIndex]
  have e1 : Parameters.g = Parameters.addressOfIndex 1 := by simp [Parameters.addressOfIndex]
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hcntT, hss, hex⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  have hhint := B1.Main.main_hintsIn (logMem_le_maxLogMem hN) hn hv hb hp hl
  subst ht
  have hkf := kFactsAll hdr t hn
  have hd : DischargeHyps coreProgram B2C.fs B2C.cert B2C.H B2C.C hdr t (fun i => i < 2) M [] [] :=
    { fresh := coreProgram_fresh
      valid := hv
      bufsOk := hb
      placed := hp
      loads := hl
      region := fun i hi => Or.inl hi
      hdr_read := ⟨hh0, hh1⟩
      size := hN
      addr := B1.Main.dischargeAddr h64 hv hp fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hcl := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hcl).2
        have hw := honest_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.total B2C.fs)
        omega
      cells := hkf.cells
      cells' := hkf.cells'
      cert_lt := hkf.cert_lt
      cert_inj := hkf.cert_inj
      run := hkf.run
      tmp := hkf.tmp
      keep := hkf.keep }
  obtain ⟨ν, hν, hX, hsub, hrd⟩ := honestX_retempH hd hhint
  have hname : (t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop)).name = "main" := by
    rw [name_retemp]; exact hn
  have hw : (t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop)).total B2C.fs ≤
      (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).words.eval (work s w) := by
    rw [total_retemp]; exact hNb
  have hc : ∀ op, cnt (t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop)) op ≤
      ((Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).instrs op).eval (work s w) := fun op => by
    rw [cntRetemp coreProgram_fresh]; exact hcntT op
  have hb' := hX.publicBoundary (prog := guestProgram)
  have hreach := (reach_jumpTables (jumpTables_cover hν.toHonest hX.covers hname)).trans
    (b2_completeL b2Hyps _ _ _ hname hν _ hX.covers)
  obtain ⟨n, hvx⟩ := validExecution_of_reach hb' hreach
  refine ⟨⟨seed, s, w, M.read, t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop),
    readerWrites M.read (hintWords coreProgram B2C.fs B2C.H hdr t), n⟩, rfl, rfl, rfl,
    { rel := hrel
      lim := hlim
      kids := hok
      tree := ⟨t, ν, hv, hb, hp, hl, hhint, hex, rfl⟩
      name := hname
      honest := ⟨_, hν, hX⟩
      valid := hvx
      size := ?_
      hintWords := fun a ha => ?_
      pops := by rw [Bridge.pops_retemp coreProgram_fresh]; exact hss }⟩
  · show Execution.committedSize ⟨_, _, n⟩ ≤ 2 ^ 30
    rw [committedSize_eq_sizeOf]
    exact (sizeOf_mono hw fun op =>
      (b2_countL b2Hyps _ _ _ hname hν _ hX.covers n hvx.2 op).trans (hc op)).trans hbs
  · obtain ⟨v, hrv⟩ := hrd a (hsub ha)
    refine ⟨v, hrv, ?_⟩
    have := hX.read_X (List.mem_map_of_mem (f := fun a => (a, (M.read a).getD 0)) (hsub ha))
    rw [hrv, Option.getD_some] at this
    exact this

end

end

end LeanVM.Guest.EndExec
