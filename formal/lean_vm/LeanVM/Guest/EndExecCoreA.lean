/-
  LeanVM.Guest.EndExecCoreA

  `CoreHonAll` on b2c's aligned honest tree: each frame of a function on the core route, at each
  state of its run, is an honest instance of it, given its families' part (`CoreGhost`).
-/

module

public import LeanVM.Guest.EndExecTop
public import LeanVM.Guest.EndExecCoreJ
public import LeanVM.Guest.Bridge.FrameMapA
public import LeanVM.Guest.CoreMode.Route
public import LeanVM.Guest.CoreMode.Fam.ResTA

/-!
# The core route's honest frames, aligned

The bus era's `EndExecCore.coreHonAll_X` on Hotwire's tree track (`RefTrack`, `trackAt`) at b2c's
layout `layB al`. At a state on a reference run at an offset of a certificate, the top frame of the
tree track is an honest instance (`RefOk.framesA`), a node of the function the certificate enters
(`EntIdx`, `fnOf_entry_inj`), whose frame holds what B2's completeness check reads (`FrameHolds`):
its path's events hold (`instsA_good`), its pointers, parameters and returns are at their cells
(`locAt_ofData`), its callees' frames hold their headers, arguments and returns (`kid_retsA`, from
`B2C.inst_runs`), its jumps read what the code says (`jumpF_of`), a loop's tail call its next frame
(`tailF_of`): `HonB` at the tree's valuation (`honB_track`). The rest of `HonF` (the heap
certificate's residuals by family, the caller's linked cells, the ghost words) is `CoreGhost`, the
families' soundness: `coreHonAll_A`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds plumbOf fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl ProgAl AtPc Ent entOf alOf alignAt alignAt_step)

open LeanVM.Prover.Exec

@[expose] public section

variable {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}

/-- **The families' part of an honest frame**: at the top frame of a state of the tree track on a
reference run in `R`, for core data `Cf` of its function, an honest valuation from its base at the
tree's valuation (its heap certificate's residuals by family, its caller's linked cells, its ghost
words). -/
def CoreGhost (L : Lay) (D : Ref → RefD) (A : String → FnAl) (R : Ref → Prop) (T : List CoreMode.CFun) : Prop :=
  ∀ r, R r → r.Ok → ∀ Cf ∈ T, CoreMode.CfOk Cf → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
    ∀ j, idxOf e.I.t.name = some j → (fnOf j).entryPc = Cf.frame.entry → coreOf j = Cf.fn →
      CoreMode.HonB r.img Cf e.I.fp e.σ → ∃ σ, CoreMode.HonF r.img Cf e.I.fp σ

end

public section

variable {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}

/-- The reference memory covers the honest writes. -/
theorem RefH.coversR {r : Ref} (hR : RefH (layB al) (D r) r) :
    ∃ rd, HonestAtA coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T B2C.cert rd [] [] ∧
      HonestX coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T rd [] [] (D r).X ∧
      Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img := by
  obtain ⟨rd, hH, hX⟩ := hR.honest
  exact ⟨rd, hH, hX, fun q hq ha ↦ (hR.img q.1).trans (hX.covers q hq ha)⟩

/-- **A taken call's returns in its callee's frame**, after its arguments, on the reference. -/
theorem kid_retsA {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ honestInstsA coreProgram B2C.fs al B2C.H r.hdr (D r).T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    {i kfp : ℕ} {c : Call} (hc : (calls es)[i]? = some c) (hk : I.kidFps[i]? = some kfp)
    (htk : c.taken = true) :
    ∀ k < c.rets.length, r.img.read (addressOfIndex (kfp + (2 + c.args.length + k))) =
      some (σ (c.rets.getD k (.n 0))) := by
  obtain ⟨rd, hH, hXh⟩ := hR.honest
  have hv := Covers.valid hH.toHonestA hXh.covers
  rcases instsA_good (D r).T _ r.hdr hv I hI with ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [ht] at hval
    obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := hval
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    rw [hw] at hw'
    obtain ⟨rfl, -⟩ := Out.ret.inj hw'
    obtain ⟨k', hk1, hkn, hkval⟩ := (B2C.kidsValid_get hkv).2 i c hc
    have hkids : I.t.kids = kids := by rw [ht]; rfl
    obtain ⟨J, hJ, hJt, hJfp, -⟩ := honestA_kid hI (k := k') (by rw [hkids]; exact hk1)
    obtain rfl : kfp = J.fp := Option.some.inj (hk.symm.trans hJfp)
    have hne : c.f ≠ "main" := B2C.calls_ne_main hf hw (List.mem_of_getElem? hc)
    have hJn : J.t.name = c.f := by rw [hJt, hkn]
    obtain ⟨-, -, -, -, -, hrets⟩ := B2C.inst_runs B2C.b2Hyps hR.name hH hXh.covers (J.t.total B2C.fs + 1) J hJ
      (Nat.lt_succ_self _) (fun hm ↦ absurd (hJn ▸ hm) hne) _ _ (by rw [hJt]; exact hkval htk)
    intro k hk'
    have := hrets k (by simpa using hk')
    rw [hR.img]
    simp only [imgOf, layB] at this ⊢
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] using this
  · rw [ht] at hph; cases hph

/-- **The base of an honest valuation at the tree track's top frame**: the frame `e` on top of a state
of the track, a node of function `j`, of core data `Cf` (`CfOk`, at `j`'s entry), meets `HonB` at
the tree's valuation `e.σ`. -/
theorem honB_track (hH : HintHyps (layB al) D A)
    (hAX : ∀ f j, idxOf f = some j → (A f).X = Bridge.ctxOf j)
    {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) {pc fp : ℕ} {done} {e : Ent}
    {st : List Ent} (htr : RefTrack (layB al) D A r pc fp (done, e :: st)) {Cf : CoreMode.CFun}
    (hCf : CoreMode.CfOk Cf) {j : ℕ} (hj : idxOf e.I.t.name = some j) (he : (fnOf j).entryPc = Cf.frame.entry) :
    coreOf j = Cf.fn ∧ CoreMode.HonB r.img Cf e.I.fp e.σ := by
  obtain ⟨rd, hHa, hXh, hcov⟩ := hR.coversR
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, hF⟩ :=
    Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨-, -, -, -, -, -, -, -, -, hjn⟩ := fn_of_idx hj
  obtain ⟨j0, hj0, he0, hc0, hx0, hb0⟩ := hCf
  obtain rfl : j = j0 := fnOf_entry_inj hjn hj0 (he.trans he0.symm)
  refine ⟨hc0, ?_⟩
  rw [hc0] at hfn
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb0
  obtain ⟨⟨⟨hb0, -⟩, -⟩, hfa0⟩ := hb0
  simp only [CoreMode.honB, Bool.and_eq_true, List.all_eq_true] at hb0
  obtain ⟨⟨⟨⟨⟨⟨⟨hlocs, hbody⟩, hptr⟩, hpar⟩, hcells⟩, hrc⟩, hj1⟩, hselB⟩ := hb0
  -- `main`'s instance is the root, in frame `0`
  have hroot : j = 1 → e.I.fp = 0 := fun h1 ↦ by
    rcases Bridge.insts_main_orA _ _ _ hHa.valid e.I hI with ⟨h0, -⟩ | h0
    · exact h0
    · exact absurd ((B2C.idx_one_iff hj).mp h1) h0
  have hXA : (A e.I.t.name).X = Cf.X := by rw [hAX _ _ hj, hx0]
  have hJC : Bridge.JumpCells r.img A e pc := hH.jumpCells r hR hr _ _ _ _ _ htr
  have hparF : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img e.I.fp (2 + k) = some (e.σ (V.n k)) := by
    intro k hk
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
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  refine ⟨⟨e.pre ++ e.es, vs, rd, by rw [hfn]; exact hw, ?_⟩, fun es0 vs0 hw0 a p hl hpa ↦ ?_,
    fun hneed es0 vs0 hw0 p r0 rs hl ↦ ?_, hparF,
    fun es0 vs0 hw0 v hv ↦ ?_, fun es0 vs0 hw0 k hk ↦ ?_, fun es0 vs0 hw0 i0 c q s0 hc htk hs0 ↦ ?_,
    fun es0 vs0 hw0 i0 c q s0 hc htk hs0 htg0 t hte ↦ ?_, ?_,
    fun es0 vs0 hw0 e0 he0' ↦ ?_, fun es0 vs0 hw0 i0 c hc hi0 off oc od q hoff hoc hod hq hfetch hnx ↦ ?_,
    fun hmX ↦ hroot ?_⟩
  · -- the events hold: the instance is a node of the valid tree
    rcases instsA_good (P := coreProgram) (rd := rd) _ _ _ hHa.valid e.I hI with ⟨args, rets, hv⟩ | ⟨f', σ', hph⟩
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
    have hmem := Bridge.walk_atomS (σ := e.σ) Cf.fn.body (by rw [hfn, hw]; exact hl)
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
    rw [hloc]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a frame run's pointer, its first value's cell's address
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hmem := Bridge.walk_atomS (σ := e.σ) Cf.fn.body (by rw [hfn, hw]; exact hl)
    simp only [CoreMode.faOkB, hneed, Bool.not_true, Bool.false_or, List.all_eq_true] at hfa0
    have hc := hfa0 _ hmem
    simp only [CoreMode.faCellB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨hx, hidx⟩ := hc
    have hloc : Cf.X.locAt r0.idx = cellJ j r0 := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    rw [hloc]
    exact hF.addr (p, r0) (List.mem_filterMap.mpr ⟨_, hl, rfl⟩)
  · -- a returned value at its cell
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hc := hrc _ (Bridge.walk_retS _ (by rw [hfn]; exact hw))
    simp only [CoreMode.retCellB, List.all_eq_true] at hc
    have hc := hc v hv
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
    have hloc : Cf.X.locAt v.idx = cellJ j v := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    have hnamed : v ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := List.mem_append_right _ hv
    have := hF.val v hnamed h2 h3
    rw [hloc]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- its returned values after its parameters
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    rcases instsA_good (P := coreProgram) _ _ _ (Covers.valid hHa.toHonestA hXh.covers) e.I hI with
      ⟨args, rets, hv⟩ | ⟨f', σ', hph⟩
    · have hv' := hv
      rw [hIt] at hv'
      obtain ⟨fn', hfind, hargs, es', vs', hw', hrets, -, -⟩ := hv'
      have hfe : fn' = e.fn := Option.some.inj (hfind.symm.trans hE.find)
      rw [hfe, hw, Memory.Out.ret.injEq] at hw'
      obtain ⟨rfl, rfl⟩ := hw'
      rw [hfe, ← hfn] at hargs
      have hnm : e.I.t.name = "main" → e.I.fp = 0 := fun hm ↦ hroot ((B2C.idx_one_iff hj).mpr hm)
      obtain ⟨-, -, -, -, -, hrr⟩ := B2C.inst_runs B2C.b2Hyps hR.name hHa hXh.covers (e.I.t.total B2C.fs + 1) e.I hI
        (Nat.lt_succ_self _) hnm args rets hv
      subst hargs hrets
      have := hrr k (by simpa using hk)
      simp only [CoreMode.Rd, hR.img, imgOf, layB] at this ⊢
      simpa [addressOfIndex, pow_add] using this
    · rw [hIt] at hph; cases hph
  · -- a call's callee frame
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨kfp, hk, hq, h0, h1, -⟩ := hJC.site _ _ hw i0 c q s0 hc htk (by rw [hXA]; exact hs0)
    have hkid := (hF.kid i0 c kfp hc hk).2.2.1
    have hret := kid_retsA hR hI hIt hE.find hw hc hk htk
    refine ⟨kfp, ?_, ?_, ?_, fun k hk' ↦ ?_, fun k hk' ↦ ?_⟩
    · simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using hq
    · simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h0
    · simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h1
    · simpa [CoreMode.Rd, addressOfIndex, pow_add] using hkid k hk'
    · have := hret k hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at this
      simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a dispatch's target cell: its callee's entry
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨kfp, -, -, -, -, htgt⟩ := hJC.site _ _ hw i0 c q s0 hc htk (by rw [hXA]; exact hs0)
    rw [← hXA, hAX _ _ hj] at hte
    obtain ⟨c', hc', hce⟩ := ctxOf_ent hte
    rw [hAX _ _ hc', hce] at htgt
    simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using htgt htg0
  · -- what its jumps read
    rw [← hx0, ← hc0]
    simp only [Nat.blt_eq] at hj1
    have hJT := B2C.jumpTables_cover hHa.toHonestA hcov hR.name
    have hwb : walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs := by rw [hc0, hfn]; exact hw
    have hselU : ∀ x, (CoreMode.cellB j x = true ∧ (x ∈ (coreOf j).params ∨ ∃ a, (a ∈ ([] : List Atom) ∨
        Ev.atom a ∈ e.pre ++ e.es) ∧ x ∈ Memory.atomUses a)) →
        CoreMode.Rd r.img e.I.fp ((Bridge.ctxOf j).locAt x.idx) = some (e.σ x) := by
      rintro x ⟨hc, hsel⟩
      simp only [CoreMode.cellB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
      have hloc : (Bridge.ctxOf j).locAt x.idx = cellJ j x := Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
      have hnamed : x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
        unfold namedOf
        rcases hsel with hp | ⟨a, ha, hu⟩
        · exact List.mem_append_left _ (List.mem_append_left _ hp)
        rcases ha with ha | ha
        · cases ha
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨_, ha, by simpa [Ev.uses] using hu⟩))
      have := hF.val x hnamed h2 h3
      rw [hloc]
      simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
    refine Bridge.jumpF_of hj1 hroot hj0 (List.all_eq_true.mpr hlocs) hF hwb
      (End.jtHolds_of hJT) hJT (fun zs x arms ss pre' es' vs' hz hcur hb' hp' ↦ ?_) (fun x fs args rets hm ↦ ?_)
    · have hm : Stmt.match_ x arms ∈ Bridge.stmtsOf (coreOf j).body :=
        Bridge.zok_stmts hz (by rw [Bridge.Zip.pos, hcur]; exact List.mem_append_left _ List.mem_cons_self)
      have hnl : CoreMode.loopBC Cf.fn = false := by
        cases hl : CoreMode.loopBC Cf.fn
        · rfl
        · exact absurd (hc0 ▸ hm) (CoreMode.loopBC_noMatch hl)
      simp only [hnl, Bool.or_false] at hbody hselB
      simp only [CoreMode.bodyCore, Bool.and_eq_true] at hbody
      rw [hwb, Memory.Out.ret.injEq] at hb'
      obtain ⟨hE', rfl⟩ := hb'
      obtain ⟨hc, a, ha, hu⟩ := Bridge.selGo_reach (hc0 ▸ hselB) (hc0 ▸ hbody.2) hz hcur (hE' ▸ hwb) hp'
      exact hselU x ⟨hc, Or.inr ⟨a, Or.inr (hE' ▸ ha), hu⟩⟩
    · have hnl : CoreMode.loopBC Cf.fn = false := by
        cases hl : CoreMode.loopBC Cf.fn
        · rfl
        · exact absurd (hc0 ▸ hm) (CoreMode.loopBC_noDsp hl)
      simp only [hnl, Bool.or_false] at hbody hselB
      simp only [CoreMode.bodyCore, Bool.and_eq_true] at hbody
      obtain ⟨hc, hr'⟩ := Bridge.selGo_selD [] _ (hc0 ▸ hselB) (hc0 ▸ hbody.2) hwb x fs args rets hm
      exact hselU x ⟨hc, hr'⟩
  · -- the events hold on the reference: the tree is valid on it
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    rcases instsA_good (P := coreProgram) _ _ _ (Covers.valid hHa.toHonestA hcov) e.I hI with ⟨args, rets, hv⟩ |
      ⟨f', σ', hph⟩
    · rw [hIt] at hv
      obtain ⟨fn', hfind, -, es', vs', hw', -, hh', -⟩ := hv
      rw [hE.find, Option.some.injEq] at hfind
      subst hfind
      rw [hw, Memory.Out.ret.injEq] at hw'
      obtain ⟨rfl, -⟩ := hw'
      exact hh' e0 he0'
    · rw [hIt] at hph; cases hph
  · -- a loop's tail call, its next frame
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hfm := End.fnOf_mem hj0
    have hlenf : (fnOf j).code.length = (fnOf j).instructionCount :=
      CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hfm)
    have hX : Cf.X = Bridge.ctxOf j := hx0.symm
    rw [hX] at hoff hfetch hnx
    have hcode := Bridge.jump_of_fetch hfm (by rw [hlenf]; exact hoff) hoc hod hq hfetch
    simp only [Nat.blt_eq] at hj1
    exact ⟨B2C.fsN j, by have := B2C.two_le_fsN j; omega, B2C.fsN_lt j,
      Bridge.tailF_of (by omega) hj0 hF (by rw [hc0, hfn]; exact hw) hc hi0 hcode hnx⟩
  · -- `main`'s frame
    rw [← hx0] at hmX
    simpa [Bridge.ctxOf, Bridge.AlignCtx.ofData] using hmX

/-- **`CoreHonAll` on the aligned honest tree**, given the families' part (`CoreGhost`): at a state on a
reference run at an offset of a certificate, the tree track's top frame is an honest instance of the
function the certificate enters. -/
theorem coreHonAll_A {Ks Ks0 : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Y : Ref → St → Prop} {T : List CoreMode.CFun}
    (certs : ModeCerts Ks0 Km E0) (hsub : ∀ K ∈ Ks, K ∈ Ks0) (hKs : ∀ K ∈ Ks0, K.F.entry ≠ 0)
    (hH : HintHyps (layB al) D A) (hRH : ∀ r, R r → RefH (layB al) (D r) r) (hEI : EntIdx A)
    (hAX : ∀ f j, idxOf f = some j → (A f).X = Bridge.ctxOf j) (hT : ∀ Cf ∈ T, CoreMode.CfOk Cf)
    (hG : CoreGhost (layB al) D A R T) : CoreHonAll R T Ks (XOf Y) := by
  intro r hR0 hr K hK Cf hCf hent s i hon hi hpc
  have hR := hRH r hR0
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K (hsub K hK)
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  obtain ⟨hge, hlt⟩ := past_pro certs hKs hR hon (hsub K hK) hi hpc
  obtain ⟨done, e0, st, htr⟩ :=
    trackAt hH.progAl hH.mainAt hH.jumpCells hH.layout hR hr hon.1.1 hon.2.1 hon.2.2 hge hlt
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := htr.top
  injection hst with h1 h2
  subst e0 st
  -- the frame's function is `K`'s
  have hentK : entOf A e.I.t.name = K.F.entry := by
    obtain ⟨off, hpcoff, p, hal, -⟩ := hat
    obtain ⟨cf, hcf, hcentry, hlen⟩ := hH.layout _ _ hE.find
    obtain ⟨ins, -, -, -, -, hins, -⟩ :=
      alignAt_step (hH.progAl.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
    have hoff : off < cf.instructionCount := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
    rw [hcentry] at hpcoff
    have heq : cf.entryPc = f.entryPc := by
      rcases le_total cf.entryPc f.entryPc with h1 | h1
      · exact (consecutive_entry functions_consecutive cf hcf f hf h1 (by omega)).symm
      · exact consecutive_entry functions_consecutive f hf cf hcf h1 (by omega)
    rw [hcentry, heq, hentry]
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hE.find
  have he : (fnOf j).entryPc = Cf.frame.entry := by rw [← hEI _ _ hj, hentK, hent]
  obtain ⟨hc, hB⟩ := honB_track hH hAX hR hr htr (hT Cf hCf) hj he
  rw [← hfp]
  exact hG r hR0 hr Cf hCf (hT Cf hCf) _ _ _ _ _ htr j hj he hc hB

end

end LeanVM.Guest.EndExec
