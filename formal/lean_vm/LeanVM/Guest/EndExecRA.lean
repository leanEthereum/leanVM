/-
  LeanVM.Guest.EndExecRA

  The table reads of linked callees at the honest frames: each callee's entries and bound
  parameters at its caller's frame, carried down the honest tree, and the reads' residuals from
  them.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.LinkDefs
public import LeanVM.Guest.B1.Digest.Range

/-!
# Linked callees' table reads

`LinkQ M L J`: an instance `J` of a callee of `L` has a header naming a frame `a` whose cells `2`
and `5` hold, in `M`, its entries parameter and its bound parameter times `g`. `linkQ_all`: it holds
at every honest instance (`LinkOk L`, the checks), by `Res.insts_down`: a callee called by `L`'s
caller gets the caller's frame (its header `H`, the call site's return pc and the caller's frame),
whose cells hold the caller's parameters (`FrameHolds.val`), which it passes or which give the
bound (`uL = w · g`, atoms on every path); a loop's tail call keeps its header and its parameters but
the counter (`loop_path`).

`anyRes_top`: a read residual (`anyResB`) at an honest frame holds: the range check bounds the
index `x = g^e` by `pL = g^(e + e')`, so `e` lies below the caller's bound `g^(e + e' + 1)`, and
`[pE]·[x]^4` is the caller's table base times `g^(4e)` (`anyRead_rsub`). `resOpen_any`: the `sub`
residuals open less these.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf kidHdr siteOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The read -/

theorem ofK_gpow (n : ℕ) : ofK (Parameters.g ^ n) = gen ^ n := by
  rw [Value.gen_pow_eq_ofK]

/-- **A read inside the caller's table**: header cell `1` names frame `a`, whose cells `2` and `5`
hold the table base `vE` and `g^(e + e' + 1)`; the read is from `vE · (g^e)^4`. -/
theorem anyRead_rsub {M : ℕ → E} {fp a cE cO e e' : ℕ} {vE : E} (hT : M (fp + 1) = ofK (Parameters.g ^ a))
    (ha : a + 5 < maxCells) (hE : M (a + 2) = vE) (hL : M (a + 5) = gen ^ (e + e') * word 2 0)
    (hcE : M (fp + cE) = vE) (hcO : M (fp + cO) = gen ^ e) (he : e + e' < 2 ^ 33) :
    RSub M fp (Res.anyRead cE cO) Res.anyTab := by
  have hl : (M (fp + 1)).limb 0 = Parameters.g ^ a := by rw [hT]; simp
  refine ⟨0, 4, rfl, rfl, fun vq hvq j _ hj ↦ ?_⟩
  dsimp only [Res.anyRead] at hvq ⊢
  obtain ⟨w, ⟨u1, w1, hu1, ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩, rfl⟩ := hvq
  change M (fp + cE) = u1 at hu1
  change M (fp + cO) = u2 at hu2
  change w2 = 1 at hw2
  subst hw2
  refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩
  obtain ⟨w, ⟨u, w', ⟨x, hxn, hxM⟩, hw', rfl⟩, rfl⟩ := hvb
  change w' = 1 at hw'
  subst hw'
  change ylo = 0 at hlo
  subst hlo
  obtain ⟨v, e5, ⟨x5, hx5n, hx5M⟩, hve, he5, hy⟩ := hhi
  obtain rfl : x = a + 2 := names_uniq hxn (names_shift hl (by omega))
  obtain rfl : x5 = a + 5 := names_uniq hx5n (names_shift hl (by omega))
  have hv : v = gen ^ (e + e' + 1) := by
    rw [← hx5M, hL, B1.word_gen, pow_succ]
  rw [hve, ofK_gpow] at hv
  have he5' : e5 = e + e' + 1 := by
    rw [Value.gen_pow_eq_ofK, Value.gen_pow_eq_ofK] at hv
    exact gpow_inj (by omega) (by omega) (ofK_injective hv)
  refine ⟨e, Nat.zero_le _, by omega, ?_⟩
  dsimp only
  rw [← hu1, ← hu2, ← hxM, hcE, hcO, hE, ofK_gpow, ofK_gpow, ofK_gpow, ofK_gpow, pow_add, pow_mul]
  ring

/-! ## Down the honest tree -/

/-- **A callee's parameters at its caller's frame**: header cell `1` names a frame `a` whose cells
`2` and `5` hold the entries parameter and the bound parameter times `g`. -/
def LinkQ (M : ℕ → E) (L : Res.Link) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ F ∈ L.fams, F.1 = f → ∀ fn, coreProgram.find? f = some fn →
    ∀ pE pL, fn.params[F.2.1]? = some pE → fn.params[F.2.2]? = some pL →
      ∃ a, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 5 < maxCells ∧ M (a + 2) = σ pE ∧
        M (a + 5) = σ pL * word 2 0

/-- **The link's checks.** -/
structure LinkOk (L : Res.Link) : Prop where
  idx : idxOf L.oName = some L.o
  origin : Res.originB L = true
  fams : ∀ F ∈ L.fams, Res.calleeB F = true
  callers : ∀ fn ∈ coreProgram, Res.callersB L fn = true
  main : ∀ F ∈ L.fams, F.1 ≠ "main"

section

variable {r : Ref}

/-- An honest node's frame within `2^28` words. -/
theorem inst_fb (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {f : String}
    {j : ℕ} (hn : I.t.name = f) (hj : idxOf f = some j) : I.fp + fsN j ≤ 2 ^ 28 := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨_, -, -, -, -, -, hfs, -⟩ := fn_of_idx hj
  have h2 := hH.cells.two_le I hI
  have hwi := honest_within hI (by omega)
  have hle := le_two_pow_logMem (r.T.total B2C.fs)
  have h28 : 2 ^ logMem (r.T.total B2C.fs) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (logMemorySize_le_28 (e := r.exec) hr.size)
  rw [hn, hfs] at hwi
  omega

/-- A word the reference image holds at a cell below `2^28`, as `refMem`. -/
theorem ref_read (hr : r.Ok) {c : ℕ} {v : E} (hc : c < 2 ^ 62) (h : r.img.read (addressOfIndex c) = some v) :
    c < maxCells ∧ refMem r.img c = v :=
  (refRd_img (logMemorySize_le_28 (e := r.exec) hr.size) r.img) c v hc h

/-- An honest node's frame holds what the completeness check reads. -/
theorem inst_frame (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {j : ℕ}
    (hj : idxOf f = some j) {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) :
    FrameHolds r.img j I.fp σ es vs I.kidFps I.hdr := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  exact B2C.b2Hyps.frame r.hdr rd r.T hr.name hH r.img hXh.covers I hI f σ bufs kids ht j hj es vs hw

/-- The reference memory is a memory image of at most `2^32` words. -/
theorem ref_memOk (hr : r.Ok) : B1.Digest.MemOk r.img.read :=
  ⟨r.κ, le_trans (by decide) (twentyThree_le_logMem (r.T.total B2C.fs)),
    le_trans (logMemorySize_le_28 (e := r.exec) hr.size) (by decide), r.img, rfl⟩

theorem getElem?_map_eq {α β : Type} {f : α → β} {l : List α} {k : ℕ} {a : α} (h : l[k]? = some a) :
    (l.map f)[k]? = some (f a) := by simp [h]

/-- **The link passes down a call.** -/
theorem linkQ_step {L : Res.Link} (hL : LinkOk L) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
      (LinkQ (refMem r.img) L) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci _ _ _ hhdr hname hval hph hQI
    f σ bufs kids hJt F hF hFf fn hfn pE pL hpE hpL
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hfnI : fnI ∈ coreProgram := List.mem_of_find?_eq_some hfI
  have hnI : fnI.name = fI := fn_name_of_find hfI
  have hcall := Res.calls_sites (hL.callers fnI hfnI) hw c hc
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq, Bool.and_eq_true, hnI,
    hcf] at hcall
  have hpk : ∀ k u, fn.params[k]? = some u → (c.args.map σI)[k]? = some (σ u) := fun k u h ↦ by
    rw [← hpar]; exact getElem?_map_eq h
  rcases hcall with (hb0 | rfl) | hb1
  · exact absurd hFf (hb0 F hF)
  · -- the caller
    have hj := hL.idx
    obtain ⟨i', hoi, hi', -, hf', hc', -⟩ := fn_of_idx hj
    obtain rfl : fnI = coreOf L.o := by rw [hc']; exact Option.some.inj (hfI.symm.trans hf')
    have hO := hL.origin
    simp only [Res.originB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
      Nat.blt_eq] at hO
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hloop⟩, huE⟩, huL⟩, hcE⟩, hcL⟩, h5⟩, hmul⟩, hcst⟩, hsites⟩ := hO
    have hs := Res.calls_sites hsites hw c hc
    simp only [List.all_eq_true] at hs
    have hs' := hs F hF
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq, hcf, hFf,
      not_true_eq_false, false_or] at hs'
    obtain ⟨⟨hE, hW⟩, hsite⟩ := hs'
    obtain ⟨s, hs⟩ : ∃ s, siteOf L.o c = some s := Option.isSome_iff_exists.mp hsite
    have hH := B2C.H_eq_kidHdr hIt hj hw i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_right (by rw [hloop]; simp), hs] at hH
    have hfb := inst_fb hr hI (by rw [hIt]; rfl) hj
    have hF0 := inst_frame hr hI hIt hj hw
    have hval' : ∀ u ∈ (coreOf L.o).params, 2 ≤ cellJ L.o u → cellJ L.o u < fsN L.o →
        I.fp + cellJ L.o u < maxCells ∧ refMem r.img (I.fp + cellJ L.o u) = σI u := fun u hu h2 hlt ↦
      ref_read hr (by omega) (hF0.val u (List.mem_append_left _ (List.mem_append_left _ hu)) h2 hlt)
    obtain ⟨-, hm2⟩ := hval' L.uE huE (by omega) (by omega)
    obtain ⟨hlt5, hm5⟩ := hval' L.uL huL (by omega) (by omega)
    rw [hcE] at hm2
    rw [hcL] at hm5
    obtain ⟨a1, ha1, he1⟩ := Res.scanAt_sound hmul hw
    obtain ⟨a2, ha2, he2⟩ := Res.scanAt_sound hcst hw
    have hmulv : σI L.uL = σI L.w * σI L.c := by
      have := hh _ he1
      cases a1 <;> simp only [Res.isMulAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha1
      exact this
    have hcv : σI L.c = word 2 0 := B1.Digest.const_sound (atoms := [a2]) (by simpa using ha2)
      (fun a ha ↦ by rw [List.mem_singleton] at ha; subst ha; exact hh _ he2)
    have hE' := hpk _ _ hpE
    have hL' := hpk _ _ hpL
    rw [List.getElem?_map, hE] at hE'
    rw [List.getElem?_map, hW] at hL'
    simp only [Option.map_some, Option.some.injEq] at hE' hL'
    refine ⟨I.fp, by rw [hhdr, hH], by omega, by rw [hm2, hE'], by rw [hm5, hmulv, hcv, hL']⟩
  · -- a loop's tail call
    obtain ⟨hfe, hl⟩ := hb1
    obtain rfl : f = fI := hfe.symm
    obtain rfl : fn = fnI := Option.some.inj (hfn.symm.trans hfI)
    have hfam := hL.fams F hF
    simp only [Res.calleeB, hFf, hfn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.or_eq_true,
      Bool.not_eq_true', hl, List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at hfam
    obtain ⟨⟨⟨⟨hk1, hk2⟩, -⟩, -⟩, hnc⟩ := hfam
    replace hnc : ∀ x ∈ Stmt.blockCallees (loopBody fn), ¬f = x := by
      rcases hnc with h | h
      · cases h
      · exact h
    obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop f fn hfn hl
    obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, -, -⟩ := Res.loop_path hsh hw hh
    subst hes
    have hnm : fn.name = f := fn_name_of_find hfn
    rw [Res.loop_calls, hnm] at hci
    have hi : i = (calls es1).length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hci
        have hc1 := walk_callees (σ := σI) (loopBody fn) (c := c)
          (by rw [hw1]; exact List.mem_of_getElem? hci)
        exact hnc _ hc1 hcf.symm
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
        cases hci
    subst hi
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
    simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
    subst hci
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfn
    obtain ⟨i2, hji2, hi2, -, hf', hc', -⟩ := fn_of_idx hj
    have hcj : coreOf j = fn := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfn)
    have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) (calls es1).length
    unfold kidHdr at hH
    rw [Res.loop_calls, hnm, List.getElem?_append_right le_rfl, Nat.sub_self] at hH
    simp only [List.getElem?_singleton, ↓reduceIte] at hH
    rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl, by simp⟩)] at hH
    have hrest : ∀ k u, 1 ≤ k → fn.params[k]? = some u → σ u = σI u := fun k u hk h ↦ by
      have h1 := hpk k u h
      rw [hps] at h
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.getElem?_cons_succ] at h
      simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_map, h, Option.map_some,
        Option.some.injEq] at h1
      exact h1.symm
    obtain ⟨a, ha, h5, hm2, hm5⟩ := hQI f σI bufsI kidsI hIt F hF hFf fn hfn pE pL hpE hpL
    refine ⟨a, by rw [hhdr, hH, ha], h5, by rw [hm2, hrest _ _ hk1 hpE], by rw [hm5, hrest _ _ hk2 hpL]⟩

/-- **The link at every honest instance.** -/
theorem linkQ_all {L : Res.Link} (hL : LinkOk L) (hr : r.Ok) :
    ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, LinkQ (refMem r.img) L J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (linkQ_step hL hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro f σ bufs kids hJt F hF hFf
  have hn := hr.name
  rw [← ht, hJt] at hn
  exact absurd (hFf.trans hn) (hL.main F hF)

end

/-! ## At the honest frames -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A read residual at an honest frame.** -/
theorem anyRes_top (t : TopAt A r K i e j) (hr : r.Ok) {L : Res.Link} (hL : LinkOk L) {x : Mode.Res}
    (hx : Res.anyResB L j x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [Res.anyResB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hx
    obtain ⟨rfl, F, hF, hn, hx⟩ := hx
    split at hx
    · rename_i pE pL cE cO hpE hpL hbs
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hx
      obtain ⟨⟨⟨⟨⟨⟨rfl, hcE⟩, h2E⟩, hltE⟩, h2O⟩, hltO⟩, hrc⟩ := hx
      obtain ⟨f, bufs, kids, hIt⟩ := t.node
      have hj := t.idx
      rw [hIt] at hj
      obtain ⟨i', rfl, hi', hname, hfind, hc, -⟩ := fn_of_idx hj
      rw [hc] at hn hpE hpL hrc
      obtain ⟨a0, ha0, h5, hm2, hm5⟩ := linkQ_all hL hr e.I t.inst f e.σ bufs kids hIt F hF
        (hn.symm.trans hname) _ hfind pE pL hpE hpL
      obtain ⟨vs, hw, hF0, hev⟩ := t.events hr
      rw [← hc] at hrc
      obtain ⟨at0, hat0, hmem⟩ := Res.scanAt_sound hrc hw
      cases at0 with
      | rangeCheck x y t1 t2 k =>
        simp only [Res.rcAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hat0
        obtain ⟨rfl, hcx⟩ := hat0
        obtain ⟨e1, e2, he1, he2, hx1, hk⟩ := B1.Digest.rc_sound (ref_memOk hr) (hev _ hmem)
        have hfb := t.fb
        have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ a0) := by
          have := (ref_read hr (by omega) hF0.hdr1).2
          rw [this, ha0]
        have hcE' : refMem r.img (e.I.fp + cE) = e.σ pE := by
          rw [← hcE]
          refine t.cell hr hF0 (List.mem_append_left _ (List.mem_append_left _ ?_)) (by omega) (by omega)
          rw [hc]; exact List.mem_of_getElem? hpE
        have hcO' : refMem r.img (e.I.fp + cO) = gen ^ e1 := by
          rw [← hcx, t.cell hr hF0 (namedOf_atom hmem (by simp [atomUses])) (by omega) (by omega), hx1]
        exact anyRead_rsub hT h5 hm2 (by rw [hm5, hk]) hcE' hcO' (by omega)
      | _ => simp [Res.rcAt] at hat0
    · cases hx
  | .lt _ _, hx => simp [Res.anyResB] at hx
  | .nz _, hx => simp [Res.anyResB] at hx
  | .name _, hx => simp [Res.anyResB] at hx

end

/-- **The `sub` residuals open, less the linked reads.** -/
theorem resOpen_any {Ks : List Mode.Cert} {A : String → FnAl} {L : Res.Link} (hL : LinkOk L)
    {p : ℕ → Mode.Res → Prop} (h : ResOpen Ks A fun j x ↦ p j x ∧ Res.anyResB L j x = false) :
    ResOpen Ks A p := by
  intro r hr K hK i hi e j t x hx hp hin
  cases hb : Res.anyResB L j x
  · exact h r hr K hK i hi e j t x hx ⟨hp, hb⟩ hin
  · exact anyRes_top t hr hL hb

end

end LeanVM.Guest.EndExec
