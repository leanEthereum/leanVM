/-
  LeanVM.Guest.EndExecCore

  `ExecGaps.core` on the tracks' invariant: each frame of a function on the core route, at each
  state of its run, is an honest instance of it, whose valuation is the core route's honest one.
-/

module

public import LeanVM.Guest.EndExecRT
public import LeanVM.Guest.EndExecRKid

/-!
# The core route's honest frames

`coreHonAll_X`: for core data of the deployed guest at a function's entry (`CfOk`), at each state
of the tracks' invariant at an offset of the function, the top frame of the tree track (`trackAt_X`)
is an honest instance (`RefOk.frames`) of the function at that entry (the alignment's function there,
`res_of_top`'s argument; entries distinct, `fnOf_entry_inj`), a node of a valid tree, so its path's
events hold (`insts_good`); its frame holds each value the path names at its certificate cell
(`FrameHolds.val`), which are the alignment context's cells (`locAt_ofData`) for its pointers, and
`2 + k` for its parameters (`honB`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds plumbOf fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl ProgAl AtPc Ent entOf alOf alignAt alignAt_step)
open LeanVM.Prover.Exec

public section

theorem straightC_mem {σ : Val} {body : List Stmt} (h : CoreMode.straightC body = true) {es : List Ev}
    {vs : List V} (hw : walk σ body = .ret es vs) {a : Atom} (ha : Ev.atom a ∈ es) : Stmt.atom a ∈ body := by
  rcases CoreMode.straightC_ev h hw _ ha with ⟨a', he, hm⟩ | ⟨f, args, rets, he, -⟩
  · cases he; exact hm
  · cases he

theorem ptrOf_uses {a : Atom} {p : V} (h : CoreMode.ptrOf a = some p) : p ∈ Memory.atomUses a := by
  cases a with
  | load d p' off => cases h; simp [Memory.atomUses]
  | hint hh =>
    simp only [CoreMode.ptrOf, Option.map_eq_some_iff] at h
    obtain ⟨⟨p', off, len⟩, hd, rfl⟩ := h
    cases hh with
    | witness s d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | bits v st nb d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | bitsExp v nb d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | digitsExp v nb nd db st sc d =>
      cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | windowsExp v st w c d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | _ => simp [CoreMode.hintHeap] at hd
  | _ => cases h

/-- **The core route's frames are honest**, on the tracks' invariant. -/
theorem coreHonAll_X {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {A : String → FnAl}
    {Y : Ref → St → Prop} (certs : ModeCerts Ks Km E0) (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = End.mainEntry) (hJ : JumpCellsAt A)
    (hL : AlLayout A) (hAX : ∀ f j, B2C.idxOf f = some j → (A f).X = Bridge.ctxOf j) : CoreHonAll Ks (XOf Y) := by
  intro r hr K hK Cf hCf hent s i hon' hi hpc
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K hK
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  have hge : proLen ≤ s.steps := by
    rcases hon'.1.1 with ⟨hlt, hpcs, -⟩ | ⟨hge, -⟩
    · have := consecutive_entry functions_consecutive _ f0_mem f hf (by rw [f0_entry']; omega)
        (by rw [f0_entry']; show f.entryPc < 0 + proLen; omega)
      rw [f0_entry'] at this
      exact absurd (hentry.trans this) (hKs K hK)
    · exact hge
  have hpcf := guest_pc_lt hf hif
  obtain ⟨done, e0, st, htr⟩ := trackAt_X hP hmain hJ hL hr hon' hge (by omega)
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := htr.top
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hF⟩ :=
    htr.frames hr.name hH hXh.covers e (by rw [hst]; exact List.mem_cons_self)
  -- the frame's function is `K`'s
  have hentK : entryOf e.I.t.name = K.F.entry := by
    obtain ⟨off, hpcoff, p, hal, -⟩ := hat
    obtain ⟨cf, hcf, hcent, hcentry, hlen⟩ := hL _ _ hE.find
    obtain ⟨ins, -, -, -, -, hins, -⟩ :=
      alignAt_step (hP.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
    have hoff : off < cf.instructionCount := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
    rw [hcent] at hpcoff
    have heq : cf.entryPc = f.entryPc := by
      rcases le_total cf.entryPc f.entryPc with h1 | h1
      · exact (consecutive_entry functions_consecutive cf hcf f hf h1 (by omega)).symm
      · exact consecutive_entry functions_consecutive f hf cf hcf h1 (by omega)
    rw [hcentry, heq, hentry]
  -- it is `Cf`'s function
  obtain ⟨j0, hj0, he0, hc0, hx0, hb0⟩ := hCf
  obtain ⟨-, -, -, -, -, -, -, -, -, hjn⟩ := fn_of_idx hj
  have hjj : j = j0 := fnOf_entry_inj hjn hj0 (by rw [← B2C.entryOf_of hj, hentK, ← hent, he0])
  subst hjj
  rw [hc0] at hfn
  -- the honest valuation
  simp only [CoreMode.honB, Bool.and_eq_true, List.all_eq_true] at hb0
  obtain ⟨⟨⟨⟨⟨⟨hlocs, hst0⟩, hj1⟩, hptr⟩, hpar⟩, hcells⟩, hrc⟩ := hb0
  have hfpL : e.I.fp = s.fp := hfp
  have hXA : (A e.I.t.name).X = Cf.X := by rw [hAX _ _ hj, hx0]
  have hJC : Bridge.JumpCells r.img A e s.pc := hJ r hr _ _ _ _ _ (by rw [← hst]; exact htr)
  refine ⟨e.σ, ⟨⟨e.pre ++ e.es, vs, rd, by rw [hfn]; exact hw, ?_⟩, fun es0 vs0 hw0 a p hl hpa ↦ ?_, fun k hk ↦ ?_,
    fun es0 vs0 hw0 v hv ↦ ?_, fun es0 vs0 hw0 k hk ↦ ?_, fun o ho ↦ ?_, fun o t ho ↦ ?_,
    fun es0 vs0 hw0 i0 c q s0 hc htk hs0 ↦ ?_⟩⟩
  · -- the events hold: the instance is a node of the valid tree
    rcases insts_good (P := coreProgram) (rd := rd) _ _ _ hH.valid e.I hI with ⟨args, rets, hv⟩ | ⟨f', σ', hph⟩
    · rw [hIt] at hv
      obtain ⟨fn', hfind, -, es', vs', hw', -, hh', -⟩ := hv
      rw [hE.find, Option.some.injEq] at hfind
      subst hfind
      rw [hw, Memory.Out.ret.injEq] at hw'
      obtain ⟨rfl, -⟩ := hw'
      exact hh'
    · rw [hIt] at hph; cases hph
  · -- a pointer at its cell
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hmem := straightC_mem hst0 (by rw [hfn]; exact hw) hl
    have hc := hptr _ hmem
    simp only [CoreMode.ptrCellB, hpa, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
    have hloc : Cf.X.locAt p.idx = cellJ j p := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    have hnamed : p ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      unfold namedOf
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hl, by simpa [Ev.uses] using ptrOf_uses hpa⟩))
    have := hF.val p hnamed h2 h3
    rw [hloc, ← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a parameter at its cell
    have hc := hcells k (List.mem_range.mpr hk)
    simp only [Nat.beq_eq, decide_eq_true_eq] at hc
    have hpe := CoreMode.paramsN_eq _ 0 hpar
    have hnamed : V.n k ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      simp only [namedOf, List.mem_append]
      refine Or.inl (Or.inl ?_)
      rw [hc0, hpe]
      simpa using hk
    have := hF.val (V.n k) hnamed (by omega) (by omega)
    rw [hc.1] at this
    rw [← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a returned value at its cell
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hc := hrc _ (CoreMode.straightC_ret hst0 (by rw [hfn]; exact hw))
    simp only [CoreMode.retCellB, List.all_eq_true] at hc
    have hc := hc v hv
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
    have hloc : Cf.X.locAt v.idx = cellJ j v := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    have hnamed : v ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := List.mem_append_right _ hv
    have := hF.val v hnamed h2 h3
    rw [hloc, ← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- its returned values after its parameters
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    have hv' := hv
    obtain ⟨fn', hfind, hargs, es', vs', hw', hrets, -, -⟩ := hv'
    have hfe : fn' = e.fn := Option.some.inj (hfind.symm.trans hE.find)
    rw [hfe, hw, Memory.Out.ret.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    rw [hfe, ← hfn] at hargs
    have hnm : e.I.t.name = "main" → e.I.fp = 0 := fun hm ↦ by
      rw [hm, B2C.idxOf_main, Option.some.injEq] at hj
      subst hj
      simp at hj1
    obtain ⟨-, -, -, -, -, hrr⟩ := B2C.inst_runs B2C.b2Hyps hr.name hH hXh.covers (e.I.t.total B2C.fs + 1) e.I hI
      (Nat.lt_succ_self _) hnm args rets (by rw [hIt]; exact hv)
    subst hargs hrets
    have := hrr k (by simpa using hk)
    rw [← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a nonzero constant
    obtain ⟨w, hw', hne⟩ := hJC.nz o (by rw [hXA]; exact ho)
    refine ⟨w, ?_, hne⟩
    rw [← hfpL]
    simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using hw'
  · -- a constant pc
    have := hJC.pcw o t (by rw [hXA]; exact ho)
    rw [← hfpL]
    simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using this
  · -- a call's callee frame
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨kfp, hk, hq, h0, h1, -⟩ := hJC.site _ _ hw i0 c q s0 hc htk (by rw [hXA]; exact hs0)
    have hkid := (hF.kid i0 c kfp hc hk).2.2.1
    have hret := kid_rets hr hI hIt hE.find hw hc hk htk
    refine ⟨kfp, ?_, ?_, ?_, fun k hk' ↦ ?_, fun k hk' ↦ ?_⟩
    · rw [← hfpL]; simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using hq
    · simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h0
    · rw [← hfpL]; simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h1
    · simpa [CoreMode.Rd, addressOfIndex, pow_add] using hkid k hk'
    · have := hret k hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at this
      simpa [CoreMode.Rd, addressOfIndex, pow_add] using this

end

end LeanVM.Guest.EndExec
