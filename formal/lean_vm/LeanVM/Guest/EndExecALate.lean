/-
  LeanVM.Guest.EndExecALate

  The late hints: each finds its buffer reserved by its `allocAdvice`, its size cell a power.
-/

module

public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.EndExecAHeap
public import LeanVM.Guest.Bridge.AllocLate

/-!
# The late hints

`lateReady_alignA : LateExcl → LateReady alignA`. A late hint of a function the allocation check
admits sizes the `k`-th buffer, an advised one at an earlier offset whose atom is an `allocDyn`
(`Bridge.lateChk_all`): every path allocates it (`topAtom`), so its advice wrote the pointer cell
(`AdvWr`, the advised sizes' track), and its size cell holds the atom's size value, a power
(`dynPow_guest`) of the buffer's size, below `maxCells`. `LateExcl`, named: the late hints of the
function the allocation check excludes (`claim_list_digest`, its buffer in a branch).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **The late hints of the functions the allocation check excludes** find their buffers reserved, and
their sizes powers below `maxCells` once their size cells are written. -/
def LateExcl : Prop :=
  ∀ r C e s sx i p b j, HintAt alignA r C e s sx i (.allocLate p b) → B2C.idxOf e.I.t.name = some j →
    j ∈ AllocChk.allocExcl → sx.mem.written (sx.fp + p) = true ∧
      (Mode.HintIn sx (.allocLate p b) → ∃ n, BufOk sx b n)

end

public section

/-- **A top-level allocation atom of a function the allocation check admits** is on the frame's path,
its buffer the frame's of its index. -/
theorem topAtom {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j) (hA : AllocJ j)
    {k : ℕ} {a : Core.Hint} (hk : (topAllocs (coreOf j).body)[k]? = some a) :
    Ev.atom (.hint a) ∈ e.pre ++ e.es ∧ e.I.t.bufs[k]? = some (allocSizeOf e.σ a) := by
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, -⟩ := (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  have hA' := hA
  simp only [AllocJ, allocChk, allocRest, Bool.and_eq_true] at hA'
  obtain ⟨⟨hshape, -⟩, -, -⟩ := hA'
  have hw0 := hw
  rw [← hfn] at hw
  refine ⟨?_, ?_⟩
  · have hmem : a ∈ (e.pre ++ e.es).filterMap Ev.allocH? := by
      rw [allocShape_walk _ hshape _ (Or.inr ⟨vs, hw⟩)]; exact List.mem_of_getElem? hk
    obtain ⟨ev, hev, hev'⟩ := List.mem_filterMap.mp hmem
    rw [← allocH_eq hev']; exact hev
  · have hb1 := bufs_of_ok (insts_bufsOk r.T _ r.hdr hHon.bufsOk e.I hI) hIt
    have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw0
    have hbufs : e.I.t.bufs = bufs := congrArg Memory.Tree.bufs hIt
    rw [hevs, allocs_of_shape hshape hw] at hb1
    rw [hbufs, hb1, List.getElem?_map, hk]
    rfl

/-- **Each late hint finds its buffer reserved**, its size cell a power, given the excluded
function's. -/
theorem lateReady_alignA (hX : LateExcl) : LateReady alignA := by
  intro r C e s sx i p b hat
  have hat' := hat
  obtain ⟨hr, hC, ⟨done, st, htr, hch, -, -, hwr⟩, -, hfine, -, hget, hpre, hag⟩ := hat'
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, -⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  by_cases hex : j ∈ AllocChk.allocExcl
  · exact hX r C e s sx i p b j hat hj hex
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  have hU := hintsUp_frame hE.find
  obtain ⟨i0, rfl, hi0, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  have hAJ : AllocJ (i0 + 1) := AllocChk.allocJ_all _ h1 (by have : nFns = 1602 := rfl; omega) hex
  have hlc := (lateChk_all (i0 + 1) h2).resolve_left hex
  -- the hint among the allocation hints
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some (.allocLate p b) := by
    rw [← hintsAtOff_eq, ← hhs]; exact hget
  have hqm : (off, Hint.allocLate p b) ∈ allocHints (alignA e.I.t.name).d := by
    unfold allocHints hintsOff
    refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, mem_of_lookupN (lookup_at hget'),
      List.mem_map.mpr ⟨_, List.mem_of_getElem? hget', ?_⟩⟩, rfl⟩
    rw [hU.1]; simp
  rw [hA2] at hqm
  obtain ⟨c, k, o, S, d, nv, rfl, hka, hkb, ho, hc, hcell⟩ := lateChk_get hlc hqm
  obtain ⟨hev, hbk⟩ := topAtom hr htr hj hAJ hka
  have hklt : k < e.I.t.bufs.length := (List.getElem?_eq_some_iff.mp hbk).1
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans htr.linked.top.1.symm
  refine ⟨?_, fun hin ↦ ?_⟩
  · have := hwr.1 k o p S (by rw [hA2]; exact hkb) (by rw [hoff]; exact ho) hklt
    rw [hsxfp]
    exact Mode.written_mono hfol.le this
  -- the size cell holds the atom's size value, a power of the buffer's size
  have hin' : sx.mem.written (sx.fp + c) = true := hin
  have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hcell
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  have hpow := dynPow_guest r hr e.I hI _ _ _ _ hIt d nv (by rw [hevs]; exact hev)
  have hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
  have he1 := curAt_le_endCur (fs := B2C.fs) (lp := coreProgram.loop) hn e.I.t.bufs.length 0
  simp only [Inst.curAt, List.take_length, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] at he1
  have he2 := endCur_chain (A := alignA) hr st e s.pc s.fp htr.track.ents htr.linked hch
  have he3 := le_two_pow_logMem (r.T.total B2C.fs)
  have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
  have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI
  have hcur2 : 2 ≤ e.I.cur := by
    have h2 := hHon.cells.two_le e.I hI
    have hb2 : B2C.fs e.I.t.name ≤ e.I.t.block B2C.fs coreProgram.loop := by
      rw [hIt]; simp only [Tree.block, Tree.name]; omega
    have := hIP.2.2
    omega
  have hle : allocSizeOf e.σ (.allocDyn d nv) ≤ e.I.t.bufs.sum := List.le_sum_of_mem (List.mem_of_getElem? hbk)
  refine ⟨allocSizeOf e.σ (.allocDyn d nv), ?_, ?_⟩
  · rw [peek_of_written hag hin', hsxfp, ← hc]
    show refMem r.img (e.I.fp + (ctxOf (i0 + 1)).locAt nv.idx) = _
    rw [hval.2]
    exact hpow
  · unfold maxCells; unfold Ref.κ at he3 h2k; omega

end

end LeanVM.Guest.EndExec
