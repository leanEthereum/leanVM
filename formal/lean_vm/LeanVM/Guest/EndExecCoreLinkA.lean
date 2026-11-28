/-
  LeanVM.Guest.EndExecCoreLinkA

  The callees of `anyLink` at the honest instances of b2c's aligned tree: their caller's entries and
  bound cells, carried down the tree, and the caller's cells the core route links to their slots
  (`CFun.gl`).
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fam.LinkDefs
public import LeanVM.Guest.CoreMode.Fam.LoopTree
public import LeanVM.Guest.CoreMode.CoreGhost
public import LeanVM.Guest.B1.Digest.Range

/-!
# Linked callees, aligned

The bus era's `Fam/ResA` and `EndExecCoreLink` on `honestInstsA`. `LinkQ M L J`: an instance `J` of a
callee of `L` has a header naming a frame `a` whose cells `2` and `5` hold, in `M`, its entries
parameter and its bound parameter times `g`. `linkQ_allA`: it holds at every honest instance (`LinkOk
L`, the checks), by `Res.insts_downA`: a callee called by `L`'s caller gets the caller's frame (its
header `H`, the call site's return pc and the caller's frame), whose cells hold the caller's
parameters (`FrameHolds.val`), which it passes or which give the bound (`uL = w · g`, atoms on every
path); a loop's tail call keeps its header and its parameters but the counter (`loop_path`, under
`Res.ProgOk`, the loops' check). `glF_instA`, `alGlF_instA`: the linked cells (`GlF`) of core data
whose links are `anyLink`'s.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf kidHdr siteOf)
open LeanVM.Guest.CoreMode (CFun slotW slotW_lt slotW_params')
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

theorem ofK_gpow (n : ℕ) : ofK (Parameters.g ^ n) = gen ^ n := by
  rw [Value.gen_pow_eq_ofK]

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

end

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

theorem getElem?_map_eq {α β : Type} {f : α → β} {l : List α} {k : ℕ} {a : α} (h : l[k]? = some a) :
    (l.map f)[k]? = some (f a) := by simp [h]

/-- **The link passes down a call.** -/
theorem linkQ_stepA {L : Res.Link} (hL : LinkOk L) (hR : RefH (layB al) (D r) r) (hr : r.Ok)
    (hP : Res.ProgOk coreProgram) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r)
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
    have hfb := inst_fbA hR hr hI (by rw [hIt]) hj
    have hF0 := inst_frameA hR hI hIt hj hw
    have hval' : ∀ u ∈ (coreOf L.o).params, 2 ≤ cellJ L.o u → cellJ L.o u < fsN L.o →
        I.fp + cellJ L.o u < maxCells ∧ refMem r.img (I.fp + cellJ L.o u) = σI u := fun u hu h2 hlt ↦
      ref_readA hr (by omega) (hF0.val u (List.mem_append_left _ (List.mem_append_left _ hu)) h2 hlt)
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
    obtain ⟨-, e0, -, hsh, -⟩ := hP.loop f fn hfn hl
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
theorem linkQ_allA {L : Res.Link} (hL : LinkOk L) (hR : RefH (layB al) (D r) r) (hr : r.Ok)
    (hP : Res.ProgOk coreProgram) : ∀ J ∈ instsR al D r, LinkQ (refMem r.img) L J := by
  refine insts_allA hR (linkQ_stepA hL hR hr hP) fun J hm ↦ ?_
  intro f σ bufs kids hJt F hF hFf
  exact absurd (hFf.trans (hm _ _ _ _ hJt)) (hL.main F hF)


/-- **Header cell `1` names the caller's frame** `a`, in the reference. -/
theorem rd_hdr {r : Ref} {I : Inst} {a : ℕ} (hdr1 : r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2)
    (ha : I.hdr.2 = ofK (addressOfIndex a)) : CoreMode.Rd r.img I.fp 1 = some (ofK (Parameters.g ^ a)) := by
  rw [ha] at hdr1
  simpa [CoreMode.Rd, addressOfIndex, pow_add] using hdr1

/-- **The caller's linked cells at an honest instance** (`GlF`), for core data whose links are of a family. -/
theorem glF_instA {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) (hP : Res.ProgOk coreProgram) {I : Inst}
    (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (hpN : Cf.fn.params = (List.range Cf.fn.params.length).map V.n)
    (hL : LinkOk Res.anyLink)
    (h : (Cf.gl.isEmpty || Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 &&
      decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1)])) = true)
    (hdr1 : r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2) (ws0 : List E) :
    CoreMode.GlF r.img Cf.gl I.fp (Cf.fn.params.map σ ++ ws0) := by
  intro d b k hmem
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [List.isEmpty_iff] at h
    rw [h] at hmem
    cases hmem
  obtain ⟨F, hF, hFe⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hFe
  obtain ⟨hname, hgl⟩ := hFe
  have hn : F.1 = f := hname.symm.trans (find_name' hf)
  have hcal := hL.fams F hF
  unfold Res.calleeB at hcal
  rw [hn, hf] at hcal
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hcal
  obtain ⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩ := hcal
  have hget : ∀ k < Cf.fn.params.length, Cf.fn.params[k]? = some (V.n k) := fun k hk ↦ by
    rw [hpN]
    simp [hk]
  obtain ⟨a, ha, h5, hm2, hm5⟩ := linkQ_allA hL hR hr hP I hI f σ bufs kids ht F hF hn Cf.fn hf _ _
    (hget _ h1) (hget _ h2)
  have hRd := rd_hdr hdr1 ha
  have hsl : ∀ k < Cf.fn.params.length, slotW (Cf.fn.params.map σ ++ ws0) k = σ (V.n k) := fun k hk ↦ by
    rw [slotW_lt (by simpa using hk), slotW_params' hpN hk]
  rw [hgl] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
    rw [hm2, hsl _ h1, pow_zero]
    simp
  · refine ⟨a, hRd, h5, ?_⟩
    simp only [CoreMode.LinkW, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte]
    rw [hm5, hsl _ h2, B1.word_gen, ← pow_one LeanVM.Protocol.Verifier.gen, Value.gen_pow_eq_ofK]

/-- **A loop callee of `anyLink`'s linked cells at an honest instance** (`GlF`, `alGl`'s links), its ghost word its
caller's frame address `a`: cell `2` its entries parameter, cell `5` its bound parameter times `g` (`linkQ_all`). -/
theorem alGlF_instA {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) (hP : Res.ProgOk coreProgram) {I : Inst}
    (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (hpN : Cf.fn.params = (List.range Cf.fn.params.length).map V.n)
    (hL : LinkOk Res.anyLink)
    (h : (Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 &&
      decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1), (0, Cf.fn.params.length, 0)])) = true)
    (hdr1 : r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2) (hgh : Cf.H.sig.ghosts = 1)
    (hnp : Cf.fn.params.length < CoreMode.GB) :
    ∃ a, CoreMode.GlF r.img Cf.gl I.fp (Cf.fn.params.map (CoreMode.setG σ [ofK (Parameters.g ^ a)]) ++
      CoreMode.ownG Cf.H.sig (CoreMode.setG σ [ofK (Parameters.g ^ a)])) := by
  obtain ⟨F, hF, hFe⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hFe
  obtain ⟨hname, hgl⟩ := hFe
  have hn : F.1 = f := hname.symm.trans (find_name' hf)
  have hcal := hL.fams F hF
  unfold Res.calleeB at hcal
  rw [hn, hf] at hcal
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hcal
  obtain ⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩ := hcal
  have hget : ∀ k < Cf.fn.params.length, Cf.fn.params[k]? = some (V.n k) := fun k hk ↦ by
    rw [hpN]
    simp [hk]
  obtain ⟨a, ha, h5, hm2, hm5⟩ := linkQ_allA hL hR hr hP I hI f σ bufs kids ht F hF hn Cf.fn hf _ _
    (hget _ h1) (hget _ h2)
  refine ⟨a, ?_⟩
  have hRd := rd_hdr hdr1 ha
  rw [CoreMode.ownG_setG (by rw [hgh]; rfl)]
  have hsl : ∀ k < Cf.fn.params.length,
      slotW (Cf.fn.params.map (CoreMode.setG σ [ofK (Parameters.g ^ a)]) ++ [ofK (Parameters.g ^ a)]) k =
        σ (V.n k) := fun k hk ↦ by
    rw [slotW_lt (by simpa using hk), slotW_params' hpN hk, CoreMode.setG_eq (show (V.n k).idx < CoreMode.GB by
      simp only; omega)]
  have hsf : slotW (Cf.fn.params.map (CoreMode.setG σ [ofK (Parameters.g ^ a)]) ++ [ofK (Parameters.g ^ a)])
      Cf.fn.params.length = ofK (Parameters.g ^ a) := by
    simp [slotW, List.getD_eq_getElem?_getD]
  intro d b k hmem
  rw [hgl] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
    rw [hm2, hsl _ h1, pow_zero]
    simp
  · refine ⟨a, hRd, h5, ?_⟩
    simp only [CoreMode.LinkW, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte]
    rw [hm5, hsl _ h2, B1.word_gen, ← pow_one LeanVM.Protocol.Verifier.gen, Value.gen_pow_eq_ofK]
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, ↓reduceIte]
    rw [hsf]
    simp



end

end LeanVM.Guest.EndExec
