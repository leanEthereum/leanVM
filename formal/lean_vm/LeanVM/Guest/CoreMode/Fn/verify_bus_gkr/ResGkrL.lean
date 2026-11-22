/-
  LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrL

  The cursor of `gkr_layer__L{p}_L{o}`'s loop in the proof stream (`GlLQ`), carried down from the layer.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrQ
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»

/-!
# A layer's loop's cursor

`GlLQ r J`: at an instance of `gkr_layer__L{p}_L{o}_loop0` at `y = g^k` below `x_m = g^m` (`m < 4`), its
header names a frame `a` whose cell `10` (the layer's stream) holds `st`, and its record `head·g^k` holds
the cursor `st·g^q` with room for its `32 (m - k)` words.

`glLQ_all`: the loop's callers are its layer and its own tail (`Res.glCallers_all`). The layer calls it
only at its site (`gl_loop_sites`), never last on its path (it is no loop), so the header names the
layer's frame; its head record holds the slot's cursor `8p` words on (`B1.Tables.gl_curs`), which `GlQ`
puts `q` words into the stream with room for the layer's `4L + 12`. An iteration's record holds the
next one's cursor `32` words on (`gll_next`, from its atoms).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec

@[expose] public section

/-- **A layer's loop's cursor in the layer's stream.** -/
def GlLQ (r : Ref) (J : Inst) : Prop :=
  ∀ p < 4, ∀ o < 2, ∀ σ bufs kids, J.t = .node (glLoopName p o) σ bufs kids →
    ∃ a k m q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 10 < maxCells ∧ σ (.n (valf% «gkr_layer» «_loop0» "y")) = gen ^ k ∧
      σ (.n (valf% «gkr_layer» «_loop0» "bound")) = gen ^ m ∧ k < m ∧ m < 4 ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_layer» «_loop0» "head")) * σ (.n (valf% «gkr_layer» «_loop0» "y"))) 4310 (refMem r.img (a + 10) * gen ^ q) ∧
      q + 32 * (m - k) ≤ 8192

end

public section

/-- **An iteration moves the cursor `32` words on**, into the next record. -/
theorem gll_next {p o : ℕ} (hp : p < 4) (ho : o < 2) {rd : Reader} {σ : Core.Val} {fn : Fn}
    (hb : fn.body = glLoopBody (glLoopName p o)) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) {cur : E} (h0 : LoadHolds rd (σ (.n (valf% «gkr_layer» «_loop0» "head")) * σ (.n (valf% «gkr_layer» «_loop0» "y"))) 4310 cur) :
    σ (.n (valf% «gkr_layer» «_loop0» "cur")) = cur ∧ LoadHolds rd (σ (.n (valf% «gkr_layer» «_loop0» "head")) * (σ (.n (valf% «gkr_layer» «_loop0» "y")) * gen)) 4310 (cur * gen ^ 32) := by
  rw [hb] at hw
  have hA : ∀ a ∈ [Atom.mul (.n (valf% «gkr_layer» «_loop0» "rd")) (.n (valf% «gkr_layer» «_loop0» "head")) (.n (valf% «gkr_layer» «_loop0» "y")), .load (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4310, .const (.n (valf% «gkr_layer» «_loop0» "s12#0")) (word (2 ^ 32) 0),
      .mul (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "s12#0")), .load (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4311], a.Holds rd σ := fun a ha ↦
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp (List.all_eq_true.mp (gll_atoms p hp o ho) a ha)))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hA
  obtain ⟨m6, l17, c339, m340, l340⟩ := hA
  simp only [Atom.Holds] at m6 l17 c339 m340 l340
  rw [tb_word_two_pow (by norm_num)] at c339
  rw [m6] at l17 l340
  obtain rfl : σ (.n (valf% «gkr_layer» «_loop0» "cur")) = cur := tb_loadHolds_unique l17 h0
  refine ⟨rfl, ?_⟩
  have h := (tb_loadHolds_mul_gen_pow rd (σ (.n (valf% «gkr_layer» «_loop0» "head")) * σ (.n (valf% «gkr_layer» «_loop0» "y"))) 1 4310 (σ (.n (valf% «gkr_layer» «_loop0» "cur")) * gen ^ 32)).mpr
    (by rw [← c339, ← m340]; exact l340)
  rwa [pow_one, mul_assoc] at h

variable {r : Ref}

/-- **A layer's loop's cursor passes down from the layer, and from one iteration to the next.** -/
theorem glLQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (GlLQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    p hp o ho σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = glLoopName p o := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hf', hp', hb'⟩ := glIs_sound (glIs_loops p hp o ho)
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  obtain ⟨hlp, hend, hnc⟩ := loop_of (gl_loopsB.2 p hp o ho).2 hfn
  rw [hp', glLoopParams_eq] at hpar
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  -- the counter below the bound, at the callee
  suffices H : ∃ a k m q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 10 < maxCells ∧ σ (.n 0) = gen ^ k ∧
      σ (.n 1) = gen ^ m ∧ k ≤ m ∧ m < 4 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0)) 4310 (refMem r.img (a + 10) * gen ^ q) ∧
      q + 32 * (m - k) ≤ 8192 by
    obtain ⟨a, k, m, q, h1, h2, h3, h4, hkm, h6, h7, h8⟩ := H
    obtain ⟨k', hk', h0'⟩ := loop_ctr_lt hr hJS hJt hfn hlp hend (hp'.trans glLoopParams_eq) h4 (by omega)
    obtain rfl : k = k' := gen_pow_inj (by omega) (by omega) (h3.symm.trans h0')
    exact ⟨a, k, m, q, h1, h2, h3, h4, hk', h6, h7, h8⟩
  rcases gl_caller hfI hw hc ((gl_callers_mem.2 p hp o ho).2) hcf with h | ⟨h, hl⟩
  · -- the layer's call
    simp only [List.mem_singleton] at h
    subst h
    obtain ⟨fnL, hfL, hpL, hbL⟩ := glIs_sound (glIs_layers p hp o ho)
    obtain rfl : fnI = fnL := Option.some.inj (hfI.symm.trans hfL)
    obtain ⟨hidx, hcell, hfs, hsite⟩ := gl_idx p hp o ho
    obtain ⟨i', hji, hi', -, hfi, hci', -⟩ := fn_of_idx hidx
    have hcj := hci'.trans (Option.some.inj (hfi.symm.trans hfI))
    -- the site
    obtain ⟨hsb, hat⟩ := gl_loop_sites p hp o ho
    have hs := Res.calls_sites (by rw [hbL]; exact hsb) hw c hc
    simp only [hcf, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hargs, hrets⟩ := hs
    have hsite' : ∃ s, siteOf (glIdx p o) c = some s := by
      have e : siteOf (glIdx p o) c = siteOf (glIdx p o) ⟨glLoopName p o, glLoopArgs p, [], true⟩ := by
        unfold siteOf; rw [hargs, hrets]
      rw [e]
      exact Option.isSome_iff_exists.mp hsite
    obtain ⟨s, hsite''⟩ := hsite'
    -- not the path's last call: the layer is no loop
    have hw' : walk σI (coreOf (glIdx p o)).body = .ret es vs := by rw [hcj]; exact hw
    have hlast : ¬ ((coreOf (glIdx p o)).loop = true ∧ i + 1 = (calls es).length) := by
      rintro ⟨hl', -⟩
      rw [hcj, not_loop_of (gl_loopsB.2 p hp o ho).1 hfI] at hl'
      cases hl'
    have hH := B2C.H_eq_kidHdr hIt hidx hw' i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    simp only [hlast, ↓reduceIte, hsite''] at hH
    -- the stream at the layer's frame
    have hfb := inst_fb hr hI (by rw [hIt]; rfl) hidx
    have hF0 := inst_frame hr hI hIt hidx hw'
    have hp8 : V.n 8 ∈ (coreOf (glIdx p o)).params := by rw [hcj, hpL, glParams_eq]; simp
    obtain ⟨hlt10, hm10⟩ := ref_read hr (by rw [hcell]; omega)
      (hF0.val (.n 8) (List.mem_append_left _ (List.mem_append_left _ hp8)) (by rw [hcell]; omega)
        (by rw [hcell]; omega))
    rw [hcell] at hlt10 hm10
    -- the layer's slot and its head record
    obtain ⟨m, q, h3, hm, h4, h5, hsl, hroom⟩ := glQ_all hr I hI p hp o ho σI bufsI kidsI hIt
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
    rw [hbL] at hb
    obtain ⟨-, -, -, hrec, -, -⟩ := gl_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hp ho hb h3 h4 h5 (by omega) hsl
    have hc0 : σI (.n (glA0 p)) = 1 := by
      have hw2 := hw
      rw [hbL] at hw2
      have := hh _ (topAtoms_on_path hw2 (List.contains_iff_mem.mp hat))
      simpa [Ev.Holds, Atom.Holds, tb_word_one] using this
    have hhd : J.hdr.2 = ofK (addressOfIndex I.fp) := by rw [hhdr, hH]
    obtain ⟨rest, hrest⟩ := glLoopArgs_eq p
    rw [hargs, hrest] at hpar
    simp only [List.map_cons, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -⟩ := hpar
    refine ⟨I.fp, 0, m, q + 8 * p, hhd, hlt10, by rw [p0, hc0, pow_zero], by rw [p1, h3], Nat.zero_le _, hm,
      ?_, by omega⟩
    have h0 := hrec 0 (Nat.zero_le _)
    rw [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, mul_assoc, ← pow_add] at h0
    rw [p2, p0, hc0, mul_one, hm10]
    exact h0
  · -- the loop's tail call
    subst h
    obtain rfl := Option.some.inj (hfI.symm.trans hfn)
    obtain ⟨p0, prest, i0, hps, hargs, hi0, hlen⟩ := loop_tail hfI hlp hnc hw hh hci hcf
    rw [hp', glLoopParams_eq] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
    obtain ⟨i2, hji2, hi2, -, hf2, hc2, -⟩ := fn_of_idx hj
    have hcj := hc2.trans (Option.some.inj (hf2.symm.trans hfI))
    have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hlp, hlen⟩)] at hH
    rw [hargs] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -⟩ := hpar
    -- the iteration's cursor
    obtain ⟨a, kI, m, q, hhdI, ha10, h0I, h1I, hkm, hm, hldI, hroomI⟩ := hQI p hp o ho σI bufsI kidsI hIt
    obtain ⟨-, hnext⟩ := gll_next hp ho hb' hw hh hldI
    refine ⟨a, kI + 1, m, q + 32, by rw [hhdr, hH, hhdI], ha10, ?_, by rw [p1, h1I], by omega, hm, ?_, by omega⟩
    · rw [p0, hi0, h0I, ← gen_pow_eq_ofK, ← pow_add]
    · rw [p2, p0, hi0, ← gen_pow_eq_ofK, pow_one, pow_add, ← mul_assoc (refMem r.img (a + 10))]
      exact hnext

/-- **A layer's loop's cursor at every honest instance.** -/
theorem glLQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, GlLQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (glLQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro p hp o ho σ bufs kids hJt
  have := root_main hr he hJt
  interval_cases p <;> interval_cases o <;> exact absurd this (by decide)

end

end LeanVM.Guest.EndExec