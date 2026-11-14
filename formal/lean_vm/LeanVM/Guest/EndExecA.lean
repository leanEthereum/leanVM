/-
  LeanVM.Guest.EndExecA

  The bump pointer's track: past the prologue, the executor's next free cell is the top frame's
  cursor, and each frame below resumes where the frame above ends.
-/

module

public import LeanVM.Guest.EndExecCAlign
public import LeanVM.Guest.Bridge.AllocLink
public import LeanVM.Guest.Bridge.AllocSound
public import LeanVM.Guest.Memory.Cursor

/-!
# The bump pointer's track

`cursorAt A e off`: frame `e`'s cursor (`Inst.curAt`) at offset `off` of its function, past the
buffers the function reserves before `off` (`Bridge.nbAt`) and the calls the frame has made, plus
the next callee's block while its frame is reserved and not entered (`Bridge.pendAt`). `ChainA`:
each frame below the top resumes, at the return pc the header of the frame above holds, at the
cursor where that frame's subtree ends (`Inst.endCur`). `YAlloc A r s`: in the prologue the next
free cell is past `main`'s frame; past it, a state of the tree track at the state's pc and frame
whose top frame's cursor is the next free cell, its frames chained.

Proved here: the track holds initially (`initY_alloc`), and the reference holds a buffer's base at
its hint's pointer cell (`bufBase_ref`: the `k`-th buffer hint of a function passing the allocation
check compiles the `k`-th allocation atom of every path, `Bridge.allocShape_walk`, whose pointer the
placement puts at the instance's cursor past the buffers before it, `Bridge.EntOk.alloc_at`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **Frame `e`'s cursor at offset `off`**: past the buffers its function reserves before `off`
and its calls made, and the next callee's block while that callee's frame is reserved and not
entered. -/
noncomputable def cursorAt (A : String → FnAl) (e : Ent) (off : ℕ) : ℕ :=
  e.I.curAt B2C.fs coreProgram.loop (nbAt (A e.I.t.name).X (A e.I.t.name).d off) e.nc +
    bif pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off then
      (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0
    else 0

/-- **Each frame below resumes where the frame above ends**: at the return pc the header of the
frame above holds in `M`, its cursor that frame's end. -/
def ChainA (A : String → FnAl) (M : ℕ → E) : List Ent → Prop
  | [] => True
  | [_] => True
  | e :: e' :: st => (∃ r, M (e.I.fp + 0) = ofK (addressOfIndex r) ∧
      e.I.endCur B2C.fs coreProgram.loop = cursorAt A e' (r - entOf A e'.I.t.name)) ∧ ChainA A M (e' :: st)

/-- **The bump pointer's track**: in the prologue the next free cell is past `main`'s frame; past
it, a state of the tree track at the state's pc and frame whose top frame's cursor is the next free
cell, its frames chained. -/
def YAlloc (A : String → FnAl) (r : Ref) (s : St) : Prop :=
  (s.steps < proLen → s.nextFree = r.adv.mainFrame) ∧
    (proLen ≤ s.steps → s.steps < r.n → ∃ done e st, RefTrack A r s.pc s.fp (done, e :: st) ∧
      s.nextFree = cursorAt A e (s.pc - entOf A e.I.t.name) ∧ ChainA A (memOf r.img) (e :: st))

end

public section

/-- **The bump pointer's track holds initially.** -/
theorem initY_alloc (A : String → FnAl) : InitY (YAlloc A) := by
  intro r hr C m hC hm
  refine ⟨fun _ ↦ rfl, fun h ↦ ?_⟩
  exact absurd h (by show ¬ proLen ≤ 0; rw [proLen_eq]; norm_num)

theorem compilesA_ptr {X : AlignCtx} {fs : ℕ} {a : Core.Hint} {h : Prover.Exec.Hint} (hc : compilesA X fs a h = true)
    {p : ℕ} (hp : allocPtr h = some p) :
    allocCellOk X fs (allocDstOf a) = true ∧ X.locAt (allocDstOf a).idx = p := by
  cases a <;> cases h <;> simp_all [compilesA, allocPtr, allocDstOf, Bool.and_eq_true, Nat.beq_eq]

theorem allocDst_mem {es : List Ev} {d : V} (h : d ∈ allocDsts es) : ∃ a, Ev.atom a ∈ es ∧ d ∈ atomUses a := by
  obtain ⟨e, he, hd⟩ := List.mem_filterMap.mp h
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    simp only [Ev.allocDst?, reduceCtorEq, Option.some.injEq] at hd <;> subst hd <;>
    exact ⟨_, he, by simp [atomUses, hintUses]⟩

/-- **The reference holds a buffer's base at its hint's pointer cell**: at a frame of the tree track
whose function passes the allocation check, the `k`-th buffer hint's pointer cell holds
`g^(cur + bufs[0] + … + bufs[k-1])`, the instance's cursor past the buffers before it. -/
theorem bufBase_ref {r : Ref} (hr : r.Ok) (hXR : ExtraRef alignA) {pc fp : ℕ} {done : List Pop} {e : Ent}
    {st : List Ent} (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j)
    (hA : AllocJ j) {k : ℕ} {h : Prover.Exec.Hint}
    (hk : (((allocHints (adviceOf j)).filter fun q ↦ isBuf (ctxOf j) q.2).map (·.2))[k]? = some h)
    {p : ℕ} (hp : allocPtr h = some p) :
    k < e.I.t.bufs.length ∧ e.I.fp + p < maxCells ∧
      refMem r.img (e.I.fp + p) = ofK (addressOfIndex (e.I.cur + (e.I.t.bufs.take k).sum)) := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  -- the check
  have hA' := hA
  simp only [AllocJ, allocChk, allocRest, Exec.listSeq_eq, Exec.natSeq_eq, Bool.and_eq_true] at hA'
  obtain ⟨hshape, ⟨⟨⟨⟨⟨⟨hpairs, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hA'
  obtain ⟨a, ha, hca⟩ := pairsA_get hpairs k h hk
  obtain ⟨hcell, hloc⟩ := compilesA_ptr hca hp
  -- the path allocates the atoms in order
  have hw0 := hw
  rw [← hfn] at hw
  have hds := allocDsts_of_shape hshape hw
  have hdk : (allocDsts (e.pre ++ e.es))[k]? = some (allocDstOf a) := by
    rw [hds, List.getElem?_map, ha]; rfl
  -- the placement
  obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
  have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
    rw [hTt, block_retemp]
    exact placed_retemp coreProgram_fresh t _ hv hpl
  have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hIp := insts_placedAt r.T _ r.hdr hTp e.I hI'
  have hIP := insts_placed r.T _ r.hdr (by omega) e.I hI'
  have hE' : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) { e with nb := k } :=
    ⟨hE.mem, hE.node, hE.find, hE.path, hE.kids⟩
  obtain ⟨hσ, hlt⟩ := hE'.alloc_at (cert := B2C.cert) hIp hIP hdk
  refine ⟨hlt, ?_⟩
  -- the pointer's cell
  set d := allocDstOf a
  have hdmem : d ∈ allocDsts (e.pre ++ e.es) := List.mem_of_getElem? hdk
  obtain ⟨at', hat, hdu⟩ := allocDst_mem hdmem
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw0
  have hM : e.I.fp + p < 2 ^ r.κ ∧ refMem r.img (e.I.fp + p) = e.σ d := by
    rcases hx : (alignA e.I.t.name).X.extra.lookup d.idx with _ | c
    · have hA2 : alignA e.I.t.name = fnAl j := alignA_of hj
      have hx' : (ctxOf j).extra.lookup d.idx = none := by rw [← hx, hA2]; rfl
      simp only [allocCellOk, hx', Option.isSome_none, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hcell
      obtain ⟨-, hlocC⟩ := pairOk_alignA _ _ j hE.find hj
      have hlc : (ctxOf j).locAt d.idx = (certOf j).locs.getD d.idx 0 := by
        have := hlocC d.idx (by rw [hA2]; exact hx') hcell.1.1
        rwa [hA2] at this
      have hcj : B2C.cellJ j d = (ctxOf j).locAt d.idx := hlc.symm
      rw [← hcj] at hcell hloc
      have hrd := hFH.val d (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hat, hdu⟩)))
        hcell.1.2 hcell.2
      obtain ⟨i, -, -, -, -, -, hfs, -⟩ := B2C.fn_of_idx hj
      have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
        honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
      have h28 : r.T.total B2C.fs ≤ 2 ^ r.κ := le_two_pow_logMem _
      have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
      rw [← hloc]
      refine ⟨by rw [hfs] at hwithin; omega, ?_⟩
      exact (refRd_img hκ r.img _ _ (by rw [hfs] at hwithin; omega) hrd).2
    · have hc := hXR r hr e.I hI _ _ bufs kids hIt d (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, hat, hdu⟩) c hx
      have hlc : (alignA e.I.t.name).X.locAt d.idx = c := by
        unfold Bridge.AlignCtx.locAt; rw [hx]; rfl
      have hA2 : alignA e.I.t.name = fnAl j := alignA_of hj
      rw [hA2] at hlc
      change (ctxOf j).locAt d.idx = c at hlc
      rw [hlc] at hloc
      subst hloc
      refine ⟨?_, hc⟩
      by_contra hge
      have h0 : refMem r.img (e.I.fp + c) = 0 := by unfold refMem; rw [dite_eq_right_iff.mpr (fun h ↦ absurd h hge)]
      rw [hc, hσ] at h0
      exact Mode.ofK_gpow_ne_zero _ h0
  refine ⟨lt_of_lt_of_le hM.1 (Nat.pow_le_pow_right (by norm_num) hκ), ?_⟩
  rw [hM.2]
  exact hσ

end

end LeanVM.Guest.EndExec
