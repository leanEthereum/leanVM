/-
  LeanVM.Guest.EndExecAExcl

  The function the allocation check excludes, `claim_list_digest`: its one buffer, in the nonempty
  list's branch, by a path argument.
-/

module

public import LeanVM.Guest.EndExecALate
public import LeanVM.Guest.EndExecRCld

/-!
# `claim_list_digest`'s buffer

Its one buffer hint is the `allocAdvice` at offset `0` (`cld_bufs`), its one late hint at offset `31`
(`cld_lates`), both for the `allocDyn` of the nonempty list's branch, its only allocation atom: a
path allocates it exactly when it takes that branch (`cld_allocH`), and calls only then
(`cld_zero_noCall`).

* `exclReady_alignA : ExclReady alignA`: the advice pops the buffer's size (`rsz_adv`), nothing when
  the path allocates none; otherwise the reference holds the buffer's base at the pointer cell, the
  path's first allocation (`EntOk.alloc_at`), where the bump pointer is, the frame having reserved
  nothing before.
* `lateExcl_guest : LateExcl`: at offset `31` the alignment reaches a call past atoms
  (`cld_late_al`, `callsSure`), so the path calls, so it took the branch and allocates the buffer,
  whose advice wrote the pointer cell (`AdvWr`); the size cell holds the atom's size value, a power
  (`dynPow_guest`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **A call on every returning path**: past atoms and conditional calls, a call or a dispatch. -/
def callsSure : List Stmt → Bool
  | .atom _ :: ss => callsSure ss
  | .callIf .. :: ss => callsSure ss
  | .call .. :: _ => true
  | .dispatch .. :: _ => true
  | _ => false

/-- What follows `claim_list_digest`'s branch. -/
abbrev cldTail : List Stmt := [.atom (.copy (.n 76) (.n 10)), .atom (.copy (.n 77) (.n 11)), .ret [.n 76, .n 77]]

end

public section

/-! ## The checks -/

theorem cld_idx24 : B2C.idxOf "claim_list_digest" = some 24 := by decide +kernel

theorem cld_bufs : bufsOf (fnAl 24).X (fnAl 24).d = [(0, .allocAdvice 33 Hints.heapSizeStream)] := by
  decide +kernel

theorem cld_lates : (allocHints (fnAl 24).d).filter (fun q ↦ isLate q.2) = [(31, .allocLate 33 (.exp 32))] := by
  decide +kernel

theorem cld_cells : (ctxOf 24).locAt 23 = 33 ∧ allocCellOk (ctxOf 24) (B2C.fsN 24) (.n 23) = true ∧
    (ctxOf 24).locAt 22 = 32 ∧ allocCellOk (ctxOf 24) (B2C.fsN 24) (.n 22) = true := by
  decide +kernel

theorem cld_late_al : (alOf alignA "claim_list_digest" 31).map callsSure = some true := by decide +kernel

theorem cld_else_shape : allocShape (B1.Digest.cl23Else ++ cldTail) = true ∧
    topAllocs (B1.Digest.cl23Else ++ cldTail) = [.allocDyn (.n 23) (.n 22)] := by
  decide +kernel

theorem cld_zero_noA : Stmt.noAllocList (B1.Digest.cl23Zero ++ cldTail) = true := by decide +kernel

/-! ## The paths -/

/-- **A path past a sure call calls.** -/
theorem callsSure_sound {σ : Core.Val} : ∀ {ss : List Stmt}, callsSure ss = true → ∀ {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∃ g args rets, Ev.call g args rets ∈ es
  | .atom a :: ss, h, es, vs, hw => by
    rw [Bridge.walk_atom_cons] at hw
    obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
    obtain ⟨g, args, rets, hg⟩ := callsSure_sound (ss := ss) h hw'
    exact ⟨g, args, rets, List.mem_append_right _ hg⟩
  | .callIf c f args :: ss, h, es, vs, hw => by
    rw [Bridge.walk_callIf_cons] at hw
    obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
    obtain ⟨g, args, rets, hg⟩ := callsSure_sound (ss := ss) h hw'
    exact ⟨g, args, rets, List.mem_append_right _ hg⟩
  | .call f args rets :: ss, _, es, vs, hw => by
    rw [walk_call_cons] at hw
    obtain ⟨es', -, rfl⟩ := Bridge.pre_eq_ret hw
    exact ⟨f, args, rets, List.mem_cons_self⟩
  | .dispatch x fs args rets :: ss, _, es, vs, hw => by
    obtain ⟨g, hg⟩ := dispatch_call (bs := []) (by simpa using hw)
    exact ⟨g, args, rets, hg⟩
  | [], h, _, _, _ | .ite .. :: _, h, _, _, _ | .match_ .. :: _, h, _, _, _ | .ret _ :: _, h, _, _, _ => by
    simp [callsSure] at h

theorem callsSure_atoms : ∀ (as : List Atom) (ss : List Stmt), callsSure (as.map Stmt.atom ++ ss) = callsSure ss
  | [], _ => rfl
  | _ :: as, ss => callsSure_atoms as ss

theorem cld_walk_split {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : walk σ (Fn.body fn% «claim_list_digest») = .ret es vs) :
    ∃ δ es', δ.filterMap Ev.allocH? = [] ∧ (∀ g args rets, Ev.call g args rets ∉ δ) ∧ es = δ ++ es' ∧
      walk σ ((if σ (.n 3) = 0 then B1.Digest.cl23Zero else B1.Digest.cl23Else) ++ cldTail) = .ret es' vs := by
  rw [B1.Digest.claim_list_digest_shape, Bridge.walk_atom_cons, Bridge.walk_atom_cons, Bridge.walk_ite_cons,
    Bridge.out_pre_pre, Bridge.out_pre_pre] at hw
  obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
  exact ⟨_, es', by simp [Ev.allocH?], by simp, rfl, hw'⟩

/-- **`claim_list_digest`'s path allocates its branch's buffer exactly when it takes the branch.** -/
theorem cld_allocH {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : walk σ (Fn.body fn% «claim_list_digest») = .ret es vs) :
    es.filterMap Ev.allocH? = if σ (.n 3) = 0 then [] else [.allocDyn (.n 23) (.n 22)] := by
  obtain ⟨δ, es', hδ, -, rfl, hw'⟩ := cld_walk_split hw
  rw [List.filterMap_append, hδ, List.nil_append]
  by_cases h3 : σ (.n 3) = 0
  · rw [ite_eq_left h3] at hw' ⊢
    refine filterMap_noA fun e he ↦ ?_
    have := walk_noA (σ := σ) _ cld_zero_noA
    rw [hw'] at this
    exact this e he
  · rw [ite_eq_right h3] at hw' ⊢
    rw [allocShape_walk _ cld_else_shape.1 es' (Or.inr ⟨vs, hw'⟩), cld_else_shape.2]

/-- **`claim_list_digest`'s empty list's path calls nothing.** -/
theorem cld_zero_noCall {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : walk σ (Fn.body fn% «claim_list_digest») = .ret es vs) (h3 : σ (.n 3) = 0) {g : String} {args rets : List V} :
    Ev.call g args rets ∉ es := by
  intro hg
  obtain ⟨δ, es', -, hδ, rfl, hw'⟩ := cld_walk_split hw
  rw [ite_eq_left h3] at hw'
  rcases List.mem_append.mp hg with hg | hg
  · exact hδ _ _ _ hg
  · have hc : (⟨g, args, rets, true⟩ : Call) ∈ calls (walk σ (B1.Digest.cl23Zero ++ cldTail)).evs := by
      rw [hw']
      simpa [Out.evs] using mem_calls_of_call hg
    have := walk_callees _ hc
    rw [cl_zero_callees] at this
    cases this

theorem allocs_eq {σ : Core.Val} (es : List Ev) : allocs σ es = (es.filterMap Ev.allocH?).map (allocSizeOf σ) := by
  rw [allocs, List.map_filterMap]
  exact List.filterMap_congr fun e _ ↦ alloc_of

theorem allocDsts_eq (es : List Ev) : allocDsts es = (es.filterMap Ev.allocH?).map allocDstOf := by
  rw [allocDsts, List.map_filterMap]
  exact List.filterMap_congr fun e _ ↦ allocDst_of

/-! ## A frame of `claim_list_digest` -/

/-- **A frame of the excluded function**: `claim_list_digest`'s, its buffers its path's, its branch's
when the path takes it. -/
theorem cld_frame {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j)
    (hex : j ∈ AllocChk.allocExcl) :
    j = 24 ∧ e.I.t.name = "claim_list_digest" ∧ e.fn = fn% «claim_list_digest» ∧ alignA e.I.t.name = fnAl 24 ∧
      (e.pre ++ e.es).filterMap Ev.allocH? = (if e.σ (.n 3) = 0 then [] else [.allocDyn (.n 23) (.n 22)]) ∧
      e.I.t.bufs = ((e.pre ++ e.es).filterMap Ev.allocH?).map (allocSizeOf e.σ) := by
  have hj24 : j = 24 := by simpa [AllocChk.allocExcl] using hex
  subst hj24
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, -⟩ := (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : (24 : ℕ) = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  obtain ⟨i, hi, hia, hna, -⟩ := B2C.fn_of_idx hj
  obtain ⟨i', hi', hia', hna', -⟩ := B2C.fn_of_idx cld_idx24
  obtain rfl : i = i' := by omega
  have hname : e.I.t.name = "claim_list_digest" := hna.symm.trans hna'
  have hfn' : e.fn = fn% «claim_list_digest» := by
    have := hE.find
    rw [hname, B1.Digest.find_claim_list_digest] at this
    exact (Option.some.inj this).symm
  have hw0 := hw
  rw [← hfn, show coreOf 24 = fn% «claim_list_digest» from hfn.trans hfn'] at hw
  have hA := cld_allocH hw
  refine ⟨rfl, hname, hfn', alignA_of hj, hA, ?_⟩
  have hb1 := bufs_of_ok (insts_bufsOk r.T _ r.hdr hHon.bufsOk e.I hI) hIt
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw0
  have hbufs : e.I.t.bufs = bufs := congrArg Memory.Tree.bufs hIt
  rw [hbufs, hb1, hevs, allocs_eq]

/-- **A buffer's size within the tree**: an entry of a frame's buffers, the frame below the bottom
frame's subtree, is below `maxCells` with the frame's cursor before it. -/
theorem buf_bound {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) (hch : ChainA alignA (memOf r.img) (e :: st)) {n : ℕ}
    (hn : n ∈ e.I.t.bufs) : 2 ≤ e.I.cur ∧ e.I.cur + n ≤ maxCells := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, -⟩ := (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hn' : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
  have he1 := curAt_le_endCur (fs := B2C.fs) (lp := coreProgram.loop) hn' e.I.t.bufs.length 0
  simp only [Inst.curAt, List.take_length, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] at he1
  have he2 := endCur_chain (A := alignA) hr st e pc fp hT.track.ents hT.linked hch
  have he3 := le_two_pow_logMem (r.T.total B2C.fs)
  have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
  have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI
  have hcur2 : 2 ≤ e.I.cur := by
    have h2 := hHon.cells.two_le e.I hI
    have hb2 : B2C.fs e.I.t.name ≤ e.I.t.block B2C.fs coreProgram.loop := by
      rw [hIt]; simp only [Tree.block, Tree.name]; omega
    have := hIP.2.2
    omega
  have hle : n ≤ e.I.t.bufs.sum := List.le_sum_of_mem hn
  refine ⟨hcur2, ?_⟩
  unfold maxCells; unfold Ref.κ at he3 h2k; omega

theorem cld_atom {e : Ent} {σ3 : Core.Val} (hH : (e.pre ++ e.es).filterMap Ev.allocH? =
      (if σ3 (.n 3) = 0 then [] else [.allocDyn (.n 23) (.n 22)])) (h3 : σ3 (.n 3) ≠ 0) :
    Ev.atom (.hint (.allocDyn (.n 23) (.n 22))) ∈ e.pre ++ e.es := by
  rw [ite_eq_right h3] at hH
  obtain ⟨ev, hev, hev'⟩ := List.mem_filterMap.mp (show Core.Hint.allocDyn (.n 23) (.n 22) ∈ _ by
    rw [hH]; exact List.mem_singleton_self _)
  rw [← allocH_eq hev']; exact hev

/-! ## The hints -/

/-- **`claim_list_digest`'s buffer hint**: its advice pops its buffer's size, nothing when the path
allocates none, and otherwise finds the bump pointer at the buffer's base. -/
theorem exclReady_alignA : ExclReady alignA := by
  intro r C e s sx i h j hat hj hex hb
  have hat' := hat
  obtain ⟨hr, hC, ⟨done, st, htr, hch, -⟩, hnc, hfine, -, hget, hpre, -⟩ := hat'
  obtain ⟨rfl, hname, hfn, hA2, hH, hbufs⟩ := cld_frame hr htr hj hex
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  have hU := hintsUp_frame hE.find
  have hCF := curFacts_frame hj
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some h := by
    rw [← hintsAtOff_eq, ← hhs]; exact hget
  have hidx := bufsOf_idx hU hget' hb
  have hm := List.mem_of_getElem? hidx
  rw [hA2, cld_bufs, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have hk0 : bufIdx alignA e 0 i = 0 := by
    have hlt := (List.getElem?_eq_some_iff.mp hidx).1
    rw [hA2, cld_bufs] at hlt
    unfold bufIdx
    rw [hintsAtOff_eq, hA2]
    simp only [List.length_singleton] at hlt
    omega
  refine ⟨rsz_adv advNext_alignA hat, fun hnf ↦ ?_⟩
  have hnx := advNext_alignA r C e s sx i 33 Hints.heapSizeStream hat
  rw [hoff, hk0] at hnx
  rw [hoff] at hnf hnc
  by_cases h3 : e.σ (.n 3) = 0
  · rw [hbufs, hH, ite_eq_left h3] at hnx
    exact Or.inl hnx
  set n := allocSizeOf e.σ (.allocDyn (.n 23) (.n 22))
  have hb1 : e.I.t.bufs = [n] := by rw [hbufs, hH, ite_eq_right h3]; rfl
  rw [hb1] at hnx
  -- the bump pointer: the frame's cursor
  have hnc0 : e.nc = 0 := hnc ⟨_, List.mem_of_getElem? hidx, le_refl _⟩
  obtain ⟨hfq, hcf⟩ := buf_noFrame hU hCF.first hget' hb
  have hpend : pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d 0 = false := by
    unfold pendAt pendIn
    rw [List.any_eq_false]
    intro q hq
    have := hfq q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega
  have hnfx : sx.nextFree = e.I.cur + (e.I.t.bufs.take (bufIdx alignA e 0 i)).sum := by
    rw [hnf, cursorAt_unfold, hnc0, hpend, ← treeSizes_take_buf alignA e 0 i hcf]
    simp only [List.take_zero, List.map_nil, List.sum_nil, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
    omega
  rw [hk0, List.take_zero, List.sum_nil, Nat.add_zero] at hnfx
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans htr.linked.top.1.symm
  obtain ⟨hcur2, hbound⟩ := buf_bound hr htr hch (n := n) (by rw [hb1]; exact List.mem_singleton_self _)
  -- the pointer: the path's first allocation, at the frame's cursor
  have hev := cld_atom hH h3
  have hdk : (allocDsts (e.pre ++ e.es))[0]? = some (.n 23) := by
    rw [allocDsts_eq, hH, ite_eq_right h3]; rfl
  obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
  have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
    rw [hTt, block_retemp]
    exact placed_retemp coreProgram_fresh t _ hv hpl
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, -⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hIp := insts_placedAt r.T _ r.hdr hTp e.I hI'
  have hIP := insts_placed r.T _ r.hdr (by omega) e.I hI'
  have hE' : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) { e with nb := 0 } :=
    ⟨hE.mem, hE.node, hE.find, hE.path, hE.kids⟩
  obtain ⟨hσ, -⟩ := hE'.alloc_at (cert := B2C.cert) hIp hIP hdk
  obtain ⟨hc1, hc2⟩ := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ cld_cells.2.1
  have h33 : (ctxOf 24).locAt (V.n 23).idx = 33 := cld_cells.1
  rw [h33] at hc1 hc2
  refine Or.inr ⟨n, hnx, by unfold maxCells at hbound ⊢; omega, by rw [hsxfp]; exact hc1, by rw [hnfx]; exact hbound, ?_⟩
  rw [hsxfp, hc2, hnfx]
  exact hσ.trans (by simp)

/-- **`claim_list_digest`'s late hint** finds its buffer reserved: the path calls past its offset, so
it took the branch, whose buffer the advice reserved; its size cell holds the buffer's size value, a
power. -/
theorem lateExcl_guest : LateExcl := by
  intro r C e s sx i p b j hat hj hex
  obtain ⟨hr, hC, ⟨done, st, htr, hch, -, -, hwr⟩, -, hfine, -, hget, hpre, hag⟩ := hat
  obtain ⟨rfl, hname, hfn, hA2, hH, hbufs⟩ := cld_frame hr htr hj hex
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  have hU := hintsUp_frame hE.find
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some (.allocLate p b) := by
    rw [← hintsAtOff_eq, ← hhs]; exact hget
  have hqm : (off, Hint.allocLate p b) ∈ allocHints (alignA e.I.t.name).d := by
    unfold allocHints hintsOff
    refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, mem_of_lookupN (lookup_at hget'),
      List.mem_map.mpr ⟨_, List.mem_of_getElem? hget', ?_⟩⟩, rfl⟩
    rw [hU.1]; simp
  rw [hA2] at hqm
  have hm : (off, Hint.allocLate p b) ∈ (allocHints (fnAl 24).d).filter (fun q ↦ isLate q.2) :=
    List.mem_filter.mpr ⟨hqm, rfl⟩
  rw [cld_lates, List.mem_singleton, Prod.mk.injEq, Hint.allocLate.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  -- the path calls past offset `31`, so it took the branch
  obtain ⟨-, hat0⟩ := htr.linked.top
  obtain ⟨off', hpc', q, hal, as, -, hpos⟩ := hat0
  obtain rfl : off' = 31 := by omega
  rw [hname] at hal
  have hq := cld_late_al
  rw [hal] at hq
  obtain ⟨vs, hwb, hrest⟩ := hE.path
  rw [hfn] at hwb
  rw [hpos] at hrest
  obtain ⟨g, args, rets, hg⟩ := callsSure_sound (by rw [callsSure_atoms]; exact Option.some.inj hq) hrest
  have h3 : e.σ (.n 3) ≠ 0 := fun h3 ↦ cld_zero_noCall hwb h3 (List.mem_append_right _ hg)
  set n := allocSizeOf e.σ (.allocDyn (.n 23) (.n 22))
  have hb1 : e.I.t.bufs = [n] := by rw [hbufs, hH, ite_eq_right h3]; rfl
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans htr.linked.top.1.symm
  refine ⟨?_, fun hin ↦ ?_⟩
  · have := hwr.1 0 0 33 Hints.heapSizeStream (by rw [hA2, cld_bufs]; rfl) (by rw [hoff]; norm_num)
      (by rw [hb1]; simp)
    rw [hsxfp]
    exact Mode.written_mono hfol.le this
  -- the size cell holds the buffer's size value, a power
  have hin' : sx.mem.written (sx.fp + 32) = true := hin
  have hev := cld_atom hH h3
  obtain ⟨hcur2, hbound⟩ := buf_bound hr htr hch (n := n) (by rw [hb1]; exact List.mem_singleton_self _)
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs', -, hIt, -, hw, -⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  have hpow := dynPow_guest r hr e.I hI _ _ _ _ hIt (.n 23) (.n 22) (by rw [hevs]; exact hev)
  have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ cld_cells.2.2.2
  have h32 : (ctxOf 24).locAt (V.n 22).idx = 32 := cld_cells.2.2.1
  rw [h32] at hval
  refine ⟨n, ?_, by unfold maxCells at hbound ⊢; omega⟩
  rw [peek_of_written hag hin', hsxfp, hval.2]
  exact hpow

end

end LeanVM.Guest.EndExec
