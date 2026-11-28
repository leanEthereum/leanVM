/-
  LeanVM.Guest.EndExecABuf

  The buffer hints on B2's layout at the deployed alignment: `BufHint` from the buffer hints' check
  (`Bridge.bufFnChk`) and the dynamic sizes being powers of `g` (`DynPowA`).
-/

module

public import LeanVM.Guest.EndExecAWithin
public import LeanVM.Guest.EndExecAStat
public import LeanVM.Guest.Bridge.BufChk
public import LeanVM.Guest.Bridge.AllocIdx
public import LeanVM.Guest.EndExecACurHyps

/-!
# The buffer hints

The bus era's `bufAtom`, `cellRef` and `bufBase_ref` (`EndExecA`, `EndExecAReady`) on the aligned
layout. At a frame of the tree track, the `k`-th buffer hint of its function (`bufsOf_idx`, `k` the
hint's `bufIdxA`) compiles the `k`-th top-level allocation atom of its body (`pairsB_get`), which
every path allocates in order (`allocShape_walk`), so the frame's `k`-th buffer is that atom's size
(`Tree.BufsOk`, `allocs_of_shape`) and its pointer the frame's cursor past the buffers before it
(`Inst.nodeAtA`, `allocDsts_of_shape`); the pointer and a dynamic size are at their certificate
cells (`cellRefB`, from `FrameHolds.val`), a size compiled constant at its fixed cell
(`JumpCells.pcw`). A buffer hint comes before any call (`NcTop`), so the bump pointer is that
cursor, and the buffer ends within the frame's subtree, within `2^κ`.

`DynPowA` (each dynamic `HeapBuf`'s size word a power of `g`, the bus era's `DynPow`) is what is
left: the bus era proved it from the nonzero facts' families (`EndExecADyn`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **Every dynamic `HeapBuf`'s size is a power of `g`**, at each instance of every reference's honest
tree. -/
def DynPowA (L : Lay) (D : Ref → RefD) : Prop :=
  ∀ r, RefH L (D r) r → r.Ok → ∀ I ∈ instsOf L (D r) r, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ d s, Ev.atom (.hint (.allocDyn d s)) ∈ I.t.events coreProgram → σ s = ofK (addressOfIndex (logG (σ s)))

end

public section

variable {D : Ref → RefD}

theorem bufs_of_okA {t : Tree} {P : Core.Program} (h : t.BufsOk P) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : t = .node f σ bufs kids) : bufs = allocs σ (t.events P) := by
  subst ht; simp only [Tree.BufsOk] at h; exact h.1

theorem allocH_eqB {ev : Ev} {a : Core.Hint} (h : Ev.allocH? ev = some a) : ev = .atom (.hint a) := by
  cases ev with
  | atom aa =>
    cases aa with
    | hint hh =>
      simp only [Ev.allocH?] at h
      cases hc : coreFlow hh <;> simp only [hc, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
      rw [h]
    | _ => simp [Ev.allocH?] at h
  | _ => simp [Ev.allocH?] at h

/-- **A value's cell holds it on the reference**: at a frame of the tree track of function `j`, a
value an atom of its path uses, at a certificate cell the buffer check admits, is at that cell of
the frame, below `maxCells`. -/
theorem cellRefB {al : String → Bool} {r : Ref} (hR : RefH ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ (D r) r)
    (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA r pc fp (done, e :: st)) {j : ℕ}
    (hj : B2C.idxOf e.I.t.name = some j) {v : V} (hv : ∃ a, Ev.atom a ∈ e.pre ++ e.es ∧ v ∈ atomUses a)
    (hlo : (ctxOf j).locOk = true) (hcell : bufCellOk (ctxOf j) (B2C.fsN j) v = true) :
    e.I.fp + (ctxOf j).locAt v.idx < maxCells ∧ refMem r.img (e.I.fp + (ctxOf j).locAt v.idx) = e.σ v := by
  obtain ⟨rd, hHa, hX⟩ := hR.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun w hw ha ↦ (hR.img w.1).trans (hX.covers w hw ha)
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, -, -, hF⟩ :=
    Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  obtain ⟨i0, rfl, -, -, -, -, hfsj, -, -, -⟩ := B2C.fn_of_idx hj
  simp only [bufCellOk, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hcell
  obtain ⟨⟨⟨hx, hlt⟩, h2⟩, hfs⟩ := hcell
  have hloc : (ctxOf (i0 + 1)).locAt v.idx = (certOf (i0 + 1)).locs.getD v.idx 0 := locAt_ofData hlo hx hlt
  obtain ⟨a, ha, hu⟩ := hv
  have hrd := hF.val v (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hu⟩)))
    (by rw [B2C.cellJ, ← hloc]; exact h2) (by rw [B2C.cellJ, ← hloc]; exact hfs)
  rw [B2C.cellJ, ← hloc] at hrd
  have h2' : 2 ≤ e.I.t.fsz B2C.fs := hHa.cells.two_le e.I hI
  have hw : e.I.fp + B2C.fs e.I.t.name ≤ (D r).T.wordsA B2C.fs coreProgram.loop al :=
    honestA_within_node hI hIt (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA B2C.fs coreProgram.loop al)
  have hlog : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
  have h28 : 2 ^ logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) hlog
  have hκ : r.κ ≤ 28 := by rw [hR.κ]; exact hlog
  exact refRd_img hκ r.img _ _ (by omega) hrd

/-- **A buffer hint's atom and base**: at a frame of the tree track, the `k`-th buffer hint of its
function compiles the `k`-th top-level allocation atom of its body, on the frame's path, the frame's
`k`-th buffer its size, its pointer the frame's cursor past the buffers before it. -/
theorem bufAtomB {al : String → Bool} {r : Ref} (hR : RefH ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ (D r) r)
    {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA r pc fp (done, e :: st))
    (hshape : allocShape e.fn.body = true) {X : AlignCtx} {n : ℕ} {k : ℕ} {h : Hint} {hs : List Hint}
    (hpairs : pairsB X n (topAllocs e.fn.body) hs = true) (hk : hs[k]? = some h) :
    ∃ a, compilesB X n a h = true ∧ Ev.atom (.hint a) ∈ e.pre ++ e.es ∧
      e.I.t.bufs[k]? = some (allocSizeOf e.σ a) ∧
      e.σ (allocDstOf a) = ofK (addressOfIndex (e.I.cur + (e.I.t.bufs.take k).sum)) := by
  obtain ⟨rd, hHa, hX⟩ := hR.honest
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f, bufs, kids, hIt⟩ := hE.node
  obtain ⟨vs, hw, -⟩ := hE.path
  obtain ⟨a, ha, hca⟩ := pairsB_get hpairs k h hk
  have hI := hE.mem
  have hn : e.I.t.name = f := by rw [hIt]; rfl
  have hfind : coreProgram.find? f = some e.fn := by rw [← hn]; exact hE.find
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hfind hw
  refine ⟨a, hca, ?_, ?_, ?_⟩
  · have hmem : a ∈ (e.pre ++ e.es).filterMap Ev.allocH? := by
      rw [allocShape_walk _ hshape _ (Or.inr ⟨vs, hw⟩)]; exact List.mem_of_getElem? ha
    obtain ⟨ev, hev, hev'⟩ := List.mem_filterMap.mp hmem
    rw [← allocH_eqB hev']; exact hev
  · have hb1 := bufs_of_okA (instsA_bufsOk (D r).T _ r.hdr hHa.bufsOk e.I hI) hIt
    have hbufs : e.I.t.bufs = bufs := congrArg Memory.Tree.bufs hIt
    rw [hevs, allocs_of_shape hshape hw] at hb1
    rw [hbufs, hb1, List.getElem?_map, ha]
    rfl
  · have hpl := insts_placedAtA (D r).T _ r.hdr hHa.placed e.I hI
    have hIP := instsA_placed (D r).T _ r.hdr (by omega) e.I hI
    have hna := (Inst.nodeAtA hpl hIP hIt).1
    rw [hIP.2.1, hevs, allocDsts_of_shape hshape hw, List.map_map] at hna
    have h1 := congrArg (·[k]?) hna
    simp only [List.getElem?_map, ha, Option.map_some] at h1
    have hlt : k < e.I.t.bufs.length := by
      by_contra hc
      have : (bases e.I.cur e.I.t.bufs)[k]? = none := by
        rw [List.getElem?_eq_none]
        rw [bases_length]
        omega
      rw [this] at h1
      cases h1
    rw [bases_getElem? _ _ _ hlt] at h1
    exact (Option.some.inj h1)


/-- What a buffer hint compiles, by kind. -/
theorem compilesB_cases {X : AlignCtx} {fs : ℕ} {a : Core.Hint} {h : Hint} (hc : compilesB X fs a h = true) :
    (∃ d n, a = .alloc d n ∧ h = .alloc (X.locAt d.idx) n false ∧ bufCellOk X fs d = true) ∨
    (∃ d nv, a = .allocDyn d nv ∧ h = .allocDyn (X.locAt d.idx) (X.locAt nv.idx) ∧ bufCellOk X fs d = true ∧
      bufCellOk X fs nv = true) ∨
    (∃ d nv n, a = .allocDyn d nv ∧ h = .alloc (X.locAt d.idx) n false ∧ bufCellOk X fs d = true ∧
      bufCellOk X fs nv = true ∧ X.pcAt (X.locAt nv.idx) = some n ∧ n < 2 ^ 28) := by
  cases a <;> cases h <;> simp only [compilesB, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Nat.blt_eq,
    Bool.not_eq_true', Bool.false_eq_true] at hc
  · obtain ⟨⟨⟨hd, rfl⟩, rfl⟩, rfl⟩ := hc
    exact Or.inl ⟨_, _, rfl, rfl, hd⟩
  · obtain ⟨⟨⟨⟨⟨hd, hn⟩, rfl⟩, hpc⟩, hlt⟩, rfl⟩ := hc
    exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, hd, hn, hpc, hlt⟩)
  · obtain ⟨⟨⟨hd, hn⟩, rfl⟩, rfl⟩ := hc
    exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hd, hn⟩)

/-- **The buffer hints on B2's layout at the deployed alignment**, from the buffer hints' check and
the dynamic sizes being powers of `g`. -/
theorem bufHint_of {L : Lay} (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) (hH : HintHyps L D alignA) (hD : DynPowA L D)
    (hchk : ∀ f fn, coreProgram.find? f = some fn → bufFnChk (alignA f).X (B2C.fs f) fn (alignA f).d = true) :
    BufHint L D alignA := by
  obtain ⟨fs, al, H, C, cert⟩ := L
  simp only at hfs hHd hC hc
  subst hfs hHd hC hc
  intro r Cx e s sx i h hat hb
  obtain ⟨done, st, htr, hch⟩ := hat.track
  have hR := hat.ref
  have hr := hat.ok
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f, bufs, kids, hIt⟩ := hE.node
  obtain ⟨j, hj⟩ := Bridge.idxOf_of_find' hE.find
  obtain ⟨i0, rfl, -, -, -, -, hfsj, -, -, -⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  -- the hint among its function's buffer hints
  have hne : (Cx.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by have := hat.get; rw [h0] at this; simp at this
  have hoff := hints_off hH.progAl hH.advAl hat.ctx htr hne
  have hi := hat.get
  rw [hoff] at hi
  have hU := hintsUp_of hH.progAl hE.find
  have hidx := bufsOf_idx hU hi hb
  set k := bufIdxA alignA e (s.pc - entOf alignA e.I.t.name) i with hkdef
  have hk : (bufHints (alignA e.I.t.name).X (alignA e.I.t.name).d)[k]? = some h := by
    show ((bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).map (·.2))[k]? = some h
    rw [List.getElem?_map]
    exact congrArg (Option.map (·.2)) hidx
  have hnc0 : e.nc = 0 := hat.nc ⟨_, List.mem_of_getElem? hidx, le_refl _⟩
  -- the check
  have hck := hchk _ _ hE.find
  simp only [bufFnChk, Bool.and_eq_true] at hck
  obtain ⟨⟨hlo, hshape⟩, hpairs⟩ := hck
  obtain ⟨a, hca, hev, hbk, hbase⟩ := bufAtomB hR htr hshape hpairs hk
  rw [hA2] at hlo hca
  change (ctxOf (i0 + 1)).locOk = true at hlo
  change compilesB (ctxOf (i0 + 1)) (B2C.fs e.I.t.name) a h = true at hca
  rw [hfsj] at hca
  have hsxfp : sx.fp = e.I.fp := by rw [hat.fp]; exact htr.linked.top.1.symm
  have hcur : e.I.curA B2C.fs coreProgram.loop al k e.nc = e.I.cur + (e.I.t.bufs.take k).sum := by
    simp only [Inst.curA, hnc0, List.take_zero, curF_nil]
  -- the buffer ends within `2^κ`
  have hbound : e.I.cur + (e.I.t.bufs.take k).sum + e.I.t.bufs.getD k 0 ≤ maxCells := by
    have hend := curA_le_endCurA (fs := B2C.fs) (lp := coreProgram.loop) (al := al) ⟨_, _, _, _, hIt⟩ (k + 1) 0
    simp only [Inst.curA, List.take_zero, curF_nil, take_succ_sum] at hend
    have hpow : e.I.endCurA B2C.fs coreProgram.loop al ≤ 2 ^ r.κ := endCurA_le_pow hR htr hch
    have hlog : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
    have h28 : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by rw [hR.κ]; exact hlog)
    unfold maxCells
    omega
  have hcur2 : 2 ≤ e.I.cur := by
    have hIP := instsA_placed (fs := B2C.fs) (lp := coreProgram.loop) (al := al) (H := B2C.H) (D r).T
      (0, (D r).T.block B2C.fs coreProgram.loop) r.hdr (by simp) e.I hE.mem
    have h2 := B2C.two_le_fs e.I.t.name
    have hb2 : B2C.fs e.I.t.name ≤ e.I.t.block B2C.fs coreProgram.loop := by
      rw [hIt]; simp only [Tree.block, Tree.name]; omega
    have := hIP.2.2
    omega
  have hgetD : e.I.t.bufs.getD k 0 = allocSizeOf e.σ a := by
    rw [List.getD_eq_getElem?_getD, hbk]; rfl
  rcases compilesB_cases hca with ⟨d, n, rfl, rfl, hd⟩ | ⟨d, nv, rfl, rfl, hd, hnv⟩ |
    ⟨d, nv, n, rfl, rfl, hd, hnv, hpc, hlt⟩
  · have hcd := cellRefB hR hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hlo hd
    refine ⟨by rw [hgetD]; rfl, fun _ hnf ↦ ?_⟩
    rw [hcur] at hnf
    rw [hgetD] at hbound
    refine ⟨by rw [hsxfp]; exact hcd.1, ?_, ?_⟩
    · rw [allocBase_false, hnf]; exact hbound
    · rw [allocBase_false, hsxfp, hcd.2, hnf]; exact hbase
  · have hcd := cellRefB hR hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hlo hd
    have hcn := cellRefB hR hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hlo hnv
    refine ⟨by rw [hgetD, rszA, hsxfp, hcn.2]; rfl, fun hin hnf ↦ ?_⟩
    rw [hcur] at hnf
    rw [hgetD] at hbound
    have hpow := hD r hR hr e.I hE.mem _ _ _ _ hIt d nv (by
      have hn : e.I.t.name = f := by rw [hIt]; rfl
      have hfind : coreProgram.find? f = some e.fn := by rw [← hn]; exact hE.find
      obtain ⟨vs, hw, -⟩ := hE.path
      rw [hIt, events_node hfind hw]; exact hev)
    have hn28 : logG (e.σ nv) < maxCells := by simp only [allocSizeOf] at hbound; omega
    refine ⟨logG (e.σ nv), ⟨?_, hn28⟩,
      by rw [hsxfp]; exact hcd.1, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := Mem.get_of_written (show sx.mem.written (sx.fp + _) = true from hin)
      have hMv := hat.agree _ _ hv
      unfold Mem.peek
      rw [hv, Option.getD_some, ← hMv, hsxfp, hcn.2]
      exact hpow
    · rw [allocBase_false, hnf]; exact hbound
    · rw [allocBase_false, hsxfp, hcd.2, hnf]; exact hbase
  · have hcd := cellRefB hR hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hlo hd
    have hcn := cellRefB hR hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hlo hnv
    have hJ := (hH.jumpCells r hR hr _ _ _ _ _ htr).pcw _ n (by rw [hA2]; exact hpc)
    have hlog : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
    have hκ : r.κ ≤ 28 := by rw [hR.κ]; exact hlog
    have hw := (refRd_img hκ r.img _ _ (by unfold maxCells at hcn; omega) hJ).2
    rw [hcn.2] at hw
    have hsz : allocSizeOf e.σ (.allocDyn d nv) = n := by
      simp only [allocSizeOf]; rw [hw, logG_spec (by omega)]
    refine ⟨by rw [hgetD, hsz]; rfl, fun _ hnf ↦ ?_⟩
    rw [hcur] at hnf
    rw [hgetD, hsz] at hbound
    refine ⟨by rw [hsxfp]; exact hcd.1, ?_, ?_⟩
    · rw [allocBase_false, hnf]; exact hbound
    · rw [allocBase_false, hsxfp, hcd.2, hnf]; exact hbase

end

end LeanVM.Guest.EndExec
