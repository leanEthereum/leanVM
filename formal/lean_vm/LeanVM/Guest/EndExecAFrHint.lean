/-
  LeanVM.Guest.EndExecAFrHint

  The callee frames' hints on B2's layout at the deployed alignment: `FrameHint` from the frame
  sizes' check (`Bridge.frChk`), the flags' check (`Bridge.frAlChk` at `al`) and the jump
  cells' check (`jcData`, its sites unique).
-/

module

public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.EndExecACurHyps
public import LeanVM.Guest.Bridge.FrAlLink
public import LeanVM.Guest.Bridge.JumpCells

/-!
# The callee frames' hints

At a frame hint of pointer `p` (`frame_nextA`, `frameSize_of`): the frame's next call `c` is through
the site `s0` the pointer names, made by a call statement `stm` of the body.

* *All buffers first* (`allBufs_of_frame`): no buffer hint of the function after the frame hint's
  offset (`CurFactsX.ord` up to its call site's jump, then `CurFactsX.bufs` at that jump, a call
  site's, which `bufJumpOk` refuses), nor after it at its offset (`ordHints`), so the bump pointer
  the track gives is the cursor past all the frame's buffers (`CurHyps.bufsLe`).
* *The site* (`siteAt_ofData`, `siteOf_eq` with `jcData`'s `sitesUniq`): `s0` is `siteOf`'s, so the
  pointer cell holds the callee's frame (`FrameHolds.site`), at `kidPosA` (`kid_posA`).
* *The flag* (`frAl_of`): `c.f`, the callee's name, is among the callees `stm` names through `s0`,
  so its flag `al c.f` is the hint's.
* *The size* (`frameSize_of`): read off the reference, the callee's block.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

public section

/-- **All buffer hints come before a frame hint**: at a frame hint, the buffer hints before it in
order are all of its function's. -/
theorem allBufs_of_frame {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Hint)} (hU : HintsUp d X.entry) (hF : CurFactsX X body code d)
    {off i : ℕ} {h : Hint} {hs : List Hint} (hlk : d.2.2.lookup (X.entry + off) = some hs)
    (hi : hs[i]? = some h) (hqm : (off, h) ∈ frames X d) :
    nbAt X d off + (hs.take i).countP (isBuf X) = (bufsOf X d).length := by
  have hfr : isFrame X h = true := (List.mem_filter.mp hqm).2
  obtain ⟨oc, od, q, hjc, hpq, -, -, -, -⟩ := frameOk_spec (hF.frame _ hqm)
  have hsq : (getF X.sites q).isSome = true := by
    unfold isFrame at hfr; rw [hpq] at hfr; exact hfr
  have hsn : (getF X.sites q).isNone = false := by
    cases hx : getF X.sites q <;> simp_all
  have hall : ∀ q' ∈ bufsOf X d, q'.1 ≤ off := by
    intro q' hq'
    by_contra hgt'
    have hgt := Nat.lt_of_not_le hgt'
    have hq'b : isBuf X q'.2 = true := (List.mem_filter.mp hq').2
    have hq'a : q' ∈ hintsOff d := (List.mem_filter.mp (List.mem_filter.mp hq').1).1
    obtain ⟨pp, hpp, hq''⟩ := List.mem_flatMap.mp hq'a
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hq''
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hh'
    have hord := hF.ord pp hpp
    have hat := ordHints_at _ _ k h' hord hk (Or.inl hq'b)
    simp only [Bool.or_eq_false_iff] at hat
    have hpend := hat.1
    simp only at hgt
    rw [hU.1] at hgt
    by_cases hle : pp.1 - X.entry ≤ nextJump code off
    · have : pendIn code (frames X d) (pp.1 - X.entry) = true :=
        List.any_eq_true.mpr ⟨(off, h), hqm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      rw [this] at hpend; cases hpend
    · rcases hF.bufs _ oc od q hjc with hb | hb
      · have := hb _ hq'; simp only at this; rw [hU.1] at this; omega
      · simp [bufJumpOk, hsn] at hb
  have hcnt : (hs.take i).countP (isBuf X) = hs.countP (isBuf X) := by
    have hord := hF.ord _ (mem_of_lookup' hlk)
    conv_rhs => rw [← List.take_append_drop i hs]
    rw [List.countP_append]
    suffices (hs.drop i).countP (isBuf X) = 0 by omega
    rw [List.countP_eq_zero]
    intro x hx hb
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_drop] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.add_zero, hi] at hn
      cases hn
      simp [isBuf, hfr] at hb
    · have hat := ordHints_at _ _ (i + n) x hord hn (Or.inl hb)
      simp only [Bool.or_eq_false_iff] at hat
      have hti : (hs.take (i + n))[i]? = some h := by
        have hlt : i < i + n := by omega
        rw [List.getElem?_take]; simp only [hlt, ↓reduceIte]; exact hi
      have hin : h ∈ hs.take (i + n) := List.mem_of_getElem? hti
      have := List.any_eq_true.mpr ⟨h, hin, hfr⟩
      rw [hat.2] at this; cases this
  have hn := (nb_none hU hall).1
  unfold hintsAtD at hn
  rw [hlk, Option.getD_some] at hn
  rw [hcnt]; exact hn

/-- The callee a call statement names through a site whose values are the call's. -/
theorem callee_in_site {σ : Val} {c : Call} {st : Stmt} {s : B2C.Site} (hco : CallOf σ c st)
    (ha : s.args = c.args.map (·.idx)) (hr : s.rets = c.rets.map (·.idx)) : c.f ∈ siteCallees s st := by
  cases st with
  | call f args rets =>
    simp only [CallOf] at hco; subst hco
    simp [siteCallees, ha, hr]
  | callIf b f args =>
    obtain ⟨hf, hargs, hrets, -⟩ := hco
    simp [siteCallees, ha, hr, hf, hargs, hrets]
  | dispatch x fs args rets =>
    obtain ⟨hargs, hrets, -, j, hj, -⟩ := hco
    simp only [siteCallees, ha, hr, hargs, hrets, beq_self_eq_true, Bool.and_self, Bool.cond_true]
    exact List.mem_of_getElem? hj
  | _ => exact hco.elim

variable {D : Ref → RefD}

/-- **The callee frames' hints on B2's layout at the deployed alignment**, at flags `al`: from the
frame sizes' check, the allocation check, the flags' check at `al`, the jump cells' check and the
loops' facts. -/
theorem frameHint_of {L : Lay} {al : String → Bool} (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) (hal : L.al = al) (hH : HintHyps L D alignA) (hPO : Res.ProgOk coreProgram)
    (hchk : ∀ f fn, coreProgram.find? f = some fn →
      ∃ cs, frChk (alignA f).X (B2C.fs f) cs fn.params fn.body (alignA f).d = true)
    (hcur : ∀ f fn, coreProgram.find? f = some fn → allocFnChk (alignA f).X fn (alignA f).code (alignA f).d = true)
    (hfal : ∀ j, 1 ≤ j → j < nFns → FrAlJ al j) (hjc : ∀ j, 1 ≤ j → j < nFns → jcData j = true) :
    FrameHint L D alignA := by
  obtain ⟨fs, al', H, C, cert⟩ := L
  simp only at hfs hHd hC hc hal
  subst hfs hHd hC hc
  subst al'
  have hCur : CurHyps ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA := curHyps_of hH.progAl hcur
  intro r Cx e s sx i h hat hfr
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (isFrame_ptr hfr)
  obtain ⟨c, s0, stm, hc, hsite, hkC, hco, hmem, hsz⟩ := frameSize_of hH hCur hPO hchk hat hfr hp
  obtain ⟨hs, hlk, hhs, hqm⟩ := frame_memA hH hat hfr
  obtain ⟨done, st, htr, hch⟩ := hat.track
  have hR := hat.ref
  have hr := hat.ok
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨rd, hHa, hX⟩ := hR.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun w hw ha ↦ (hR.img w.1).trans (hX.covers w hw ha)
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hF⟩ :=
    Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
  have hlog : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
  have hκ : r.κ ≤ 28 := by rw [hR.κ]; exact hlog
  have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
  obtain ⟨i0, rfl, -, -, -, -, hfsj, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  have hsxfp : sx.fp = e.I.fp := by rw [hat.fp]; exact htr.linked.top.1.symm
  -- the next callee
  obtain ⟨k, hk⟩ : ∃ k, (e.I.t.kidsC coreProgram.loop)[e.nc]? = some k := ⟨_, List.getElem?_eq_getElem hkC⟩
  rw [hk, Option.map_some, Option.getD_some] at hsz
  obtain ⟨rv, hkv⟩ := hE.kids
  have hkn : k.name = c.f := (kidsValid_atF hkv hc (kidsC_getElem? hk)).1
  have hstep : frameStep ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ e = (al c.f, k.block B2C.fs coreProgram.loop) := by
    simp only [frameStep, hk, Option.map_some, Option.getD_some, hkn]
  rw [hstep]
  -- the site's cell holds the callee's frame
  have hsite' : (ctxOf (i0 + 1)).siteAt p c.args c.rets = some s0 := by rw [hA2] at hsite; exact hsite
  obtain ⟨hsm, hsq, hsa, hsr⟩ := siteAt_ofData hsite'
  have hd := hjc _ h1 h2
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hsites⟩, huniq⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hd
  have hso : B2C.siteOf (i0 + 1) c = some s0 := siteOf_eq huniq hsm hsa hsr
  have hb := List.all_eq_true.mp hsites _ hsm
  simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.or_eq_true, beq_iff_eq] at hb
  have hlt : e.nc < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[e.nc]? = some kfp :=
    ⟨_, List.getElem?_eq_getElem (by rw [hF.len]; exact hlt)⟩
  have hread := (hF.site e.nc c kfp s0 hc hkfp hso).1 hb.1.1 hb.1.2
  rw [hsq] at hread hb
  have hIP := instsA_placed (fs := B2C.fs) (lp := coreProgram.loop) (al := al) (H := B2C.H) (D r).T
    (0, (D r).T.block B2C.fs coreProgram.loop) r.hdr (by simp) e.I hI
  rw [hIP.1, List.getElem?_map, kid_posA hk] at hkfp
  obtain rfl := (Option.some.inj hkfp).symm
  have h2' : 2 ≤ e.I.t.fsz B2C.fs := hHa.cells.two_le e.I hI
  have hwn : e.I.fp + B2C.fs e.I.t.name ≤ (D r).T.wordsA B2C.fs coreProgram.loop al :=
    honestA_within_node hI hIt (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA B2C.fs coreProgram.loop al)
  rw [hfsj] at hwn
  have h28' : 2 ^ logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) hlog
  have hpfs : p < B2C.fsN (i0 + 1) := hb.1.2
  obtain ⟨hplt, hpm⟩ := refRd_img hκ r.img _ _ (by omega) hread
  -- the block within `2^κ`
  have hbl := curA_block_le (fs := B2C.fs) (lp := coreProgram.loop) (al := al) ⟨_, _, _, _, hIt⟩
    (nb := e.I.t.bufs.length) hk
  have hpow : e.I.endCurA B2C.fs coreProgram.loop al ≤ 2 ^ r.κ := endCurA_le_pow hR htr hch
  have hend : allocBase (al c.f) (e.I.curA B2C.fs coreProgram.loop al e.I.t.bufs.length e.nc) +
      k.block B2C.fs coreProgram.loop ≤ maxCells := by
    rw [← hkn]; unfold maxCells; omega
  -- the bump pointer: all buffers first
  have hU := hintsUp_of hH.progAl hE.find
  have hFx := hCur.facts _ _ hE.find
  have hall := allBufs_of_frame hU hFx hlk hhs hqm
  have hbl2 := hCur.bufsLe r hR hr e.I hE.mem
  have hcur : e.I.curA B2C.fs coreProgram.loop al
      (bufIdxA alignA e (s.pc - entOf alignA e.I.t.name) i) e.nc =
      e.I.curA B2C.fs coreProgram.loop al e.I.t.bufs.length e.nc := by
    have hbi : bufIdxA alignA e (s.pc - entOf alignA e.I.t.name) i =
        (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length := by
      unfold bufIdxA hintsAtOff; rw [hlk, Option.getD_some]; exact hall
    rw [hbi]
    simp only [Inst.curA, List.take_of_length_le hbl2, List.take_length]
  -- the flag
  have hflag : ∀ b, frameFlag h = some b → al c.f = b := fun b hb' ↦ by
    have hq : (s.pc - entOf alignA e.I.t.name, h) ∈ allocHints (adviceOf (i0 + 1)) := by
      have := (List.mem_filter.mp hqm).1; rw [hA2] at this; exact this
    have hst : stm ∈ stmtsOf (coreOf (i0 + 1)).body := by rw [hfn]; exact hmem
    exact frAl_of (hfal _ h1 h2) hq hb' hp hsm hsq hst (callee_in_site hco hsa hsr)
  have hptr : ∀ a, al c.f = a → refMem r.img (sx.fp + p) =
      ofK (g ^ allocBase a (e.I.curA B2C.fs coreProgram.loop al e.I.t.bufs.length e.nc)) := by
    rintro a rfl; rw [hsxfp, hpm, ← hkn]
  have hplt' : sx.fp + p < maxCells := by rw [hsxfp]; unfold maxCells; omega
  -- by kind
  cases h with
  | alloc ptr n a =>
    obtain rfl : ptr = p := Option.some.inj hp
    have ha := hflag a rfl
    simp only [SizeOkA] at hsz
    subst hsz
    refine ⟨by rw [rszA, ha], fun _ hnf ↦ ?_⟩
    rw [hcur] at hnf
    refine ⟨hplt', by rw [hnf, ← ha]; exact hend, by rw [hnf]; exact hptr a ha⟩
  | allocArm ptr sel sizes a =>
    obtain rfl : ptr = p := Option.some.inj hp
    have ha := hflag a rfl
    obtain ⟨kk, hsel, hkk, hsk⟩ := hsz
    have hlg : logG (refMem r.img (sx.fp + sel)) = kk := by
      rw [hsxfp, hsel]; exact logG_spec (by unfold maxCells at hkk; omega)
    refine ⟨by rw [rszA, hlg, List.getD_eq_getElem?_getD, hsk, Option.getD_some, ha], fun hin hnf ↦ ?_⟩
    rw [hcur] at hnf
    refine ⟨kk, k.block B2C.fs coreProgram.loop, ⟨?_, hkk⟩, hsk, hplt', by rw [hnf, ← ha]; exact hend,
      by rw [hnf]; exact hptr a ha⟩
    obtain ⟨v, hv⟩ := Mem.get_of_written (show sx.mem.written (sx.fp + sel) = true from hin)
    have hMv := hat.agree _ _ hv
    unfold Mem.peek
    rw [hv, Option.getD_some, ← hMv, hsxfp, hsel]
  | allocFrames ptr size stop si tail a =>
    obtain rfl : ptr = p := Option.some.inj hp
    have ha := hflag a rfl
    obtain ⟨v, n, hstop, hvn, hnlt, hsn⟩ := hsz
    have hlg : logG (ofK ((refMem r.img (sx.fp + stop)).limb 0 * si)) = n := by
      rw [hsxfp, hstop, show (ofK v).limb 0 = v by simp, hvn]
      exact logG_spec (by unfold maxCells at hnlt; omega)
    refine ⟨by rw [rszA, hlg, hsn, ha], fun hin hnf ↦ ?_⟩
    rw [hcur] at hnf
    refine ⟨v, n, ?_, hvn, hnlt, hplt', by rw [hnf, ← ha, hsn]; exact hend, by rw [hnf]; exact hptr a ha⟩
    obtain ⟨w, hw'⟩ := Mem.get_of_written (show sx.mem.written (sx.fp + stop) = true from hin)
    have hMv := hat.agree _ _ hw'
    unfold Mem.peek
    rw [hw', Option.getD_some, ← hMv, hsxfp, hstop]
  | _ => simp [SizeOkA] at hsz

end

end LeanVM.Guest.EndExec
