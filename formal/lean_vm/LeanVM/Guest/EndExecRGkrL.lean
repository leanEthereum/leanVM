/-
  LeanVM.Guest.EndExecRGkrL

  The cursor of `verify_bus_gkr`'s pair loop `verify_bus_gkr_loop0_loop0` in the proof stream (`PairQ`),
  carried down from the layer loop.
-/

module

public import LeanVM.Guest.EndExecRGkrQ

/-!
# The pair loop's cursor

`PairQ r J`: at an instance of `verify_bus_gkr_loop0_loop0` at `y = g^k` below `x_pair = g^n`
(`n ≤ 16`), its header names a frame `a` whose cell `11` (the layer loop's stream) holds `st`, and
its record `head·g^k` holds the cursor `st·g^q` with room for its `8 (n - k)` words.

`pairQ_all`: the loop's callers are the layer loop and its own tail (`Res.termCallers_all`). The layer
loop calls it only at its site (`ly_pair_sites`), never last on its path, so the header names the
layer loop's frame; its first record holds the slot's cursor (`ly_curs`), which `LyQ` puts `q` words
into the stream with room for `140` a layer. An iteration's record holds the next one's cursor eight
words on (`pair_next`, from its atoms).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Mode LeanVM.Prover.Exec

@[expose] public section

/-- **The pair loop's cursor in the layer loop's stream.** -/
def PairQ (r : Ref) (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_bus_gkr_loop0_loop0» σ bufs kids →
    ∃ a k n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 11 < maxCells ∧ σ (.n 0) = gen ^ k ∧
      σ (.n 1) = gen ^ n ∧ k < n ∧ n ≤ 16 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0)) 4310 (refMem r.img (a + 11) * gen ^ q) ∧
      q + 8 * (n - k) ≤ 8192

/-- The pair loop's call arguments in the layer loop. -/
def pairArgsV : List V := [63, 0, 56, 55, 4].map .n

end

public section

theorem find_pair : coreProgram.find? name% «verify_bus_gkr_loop0_loop0» = some fn% «verify_bus_gkr_loop0_loop0» :=
  coreProgram_find?_at (j := idx% «verify_bus_gkr_loop0_loop0») rfl

theorem pair_params : (fn% «verify_bus_gkr_loop0_loop0»).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl

theorem pair_loop : (fn% «verify_bus_gkr_loop0_loop0»).loop = true ∧
    Res.endOfFn (fn% «verify_bus_gkr_loop0_loop0») = some none := by decide +kernel

theorem ly_idx : idxOf name% «verify_bus_gkr_loop0» = some (fn_idx% «verify_bus_gkr_loop0») := by
  decide +kernel

theorem ly_cell9 : cellJ (fn_idx% «verify_bus_gkr_loop0») (.n 9) = 11 ∧ 11 < fsN (fn_idx% «verify_bus_gkr_loop0») := by
  decide +kernel

/-- **The layer loop calls the pair loop only at its site.** -/
theorem ly_pair_sites : Res.sitesB (fun f args rets ↦ f != name% «verify_bus_gkr_loop0_loop0» ||
    (args == pairArgsV && rets == [])) (fn% «verify_bus_gkr_loop0»).body = true := by
  decide +kernel

/-- The pair loop's site in the layer loop's plumbing. -/
theorem ly_pair_site {c : Call} (ha : c.args = pairArgsV) (hr : c.rets = []) :
    ∃ s, siteOf (fn_idx% «verify_bus_gkr_loop0») c = some s := by
  unfold siteOf
  rw [ha, hr]
  exact Option.isSome_iff_exists.mp (by decide +kernel)

/-- The layer loop calls no layer loop but its tail. -/
theorem ly_body_callees : name% «verify_bus_gkr_loop0» ∉ Stmt.blockCallees (loopBody (fn% «verify_bus_gkr_loop0»)) := by
  decide +kernel

/-- The pair loop's atoms the cursor moves through. -/
theorem pair_atoms :
    [Atom.mul (.n 5) (.n 2) (.n 0), .load (.n 13) (.n 5) 4310, .const (.n 95) (word 256 0),
      .mul (.n 96) (.n 13) (.n 95), .load (.n 96) (.n 5) 4311].all
      (topAtoms (fn% «verify_bus_gkr_loop0_loop0»).body).contains = true := by
  decide +kernel

theorem pair_cell13 : cellJ (fn_idx% «verify_bus_gkr_loop0_loop0») (.n 13) = 17 ∧
    17 < fsN (fn_idx% «verify_bus_gkr_loop0_loop0») := by
  decide +kernel

/-- **An iteration moves the cursor eight words on**, into the next record. -/
theorem pair_next {rd : Reader} {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : walk σ (fn% «verify_bus_gkr_loop0_loop0»).body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    {cur : E} (h0 : LoadHolds rd (σ (.n 2) * σ (.n 0)) 4310 cur) :
    σ (.n 13) = cur ∧ LoadHolds rd (σ (.n 2) * (σ (.n 0) * gen)) 4310 (cur * gen ^ 8) := by
  have hA : ∀ a ∈ [Atom.mul (.n 5) (.n 2) (.n 0), .load (.n 13) (.n 5) 4310, .const (.n 95) (word 256 0),
      .mul (.n 96) (.n 13) (.n 95), .load (.n 96) (.n 5) 4311], a.Holds rd σ := fun a ha ↦
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp (List.all_eq_true.mp pair_atoms a ha)))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hA
  obtain ⟨m5, l13, c95, m96, l96⟩ := hA
  simp only [Atom.Holds] at m5 l13 c95 m96 l96
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)] at c95
  rw [m5] at l13 l96
  obtain rfl : σ (.n 13) = cur := tb_loadHolds_unique l13 h0
  refine ⟨rfl, ?_⟩
  have h := (tb_loadHolds_mul_gen_pow rd (σ (.n 2) * σ (.n 0)) 1 4310 (σ (.n 13) * gen ^ 8)).mpr
    (by rw [← c95, ← m96]; exact l96)
  rwa [pow_one, mul_assoc] at h

variable {r : Ref}

/-- **The pair loop's cursor passes down from the layer loop, and from one iteration to the next.** -/
theorem pairQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (PairQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = name% «verify_bus_gkr_loop0_loop0» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «verify_bus_gkr_loop0_loop0» := Option.some.inj (hfn.symm.trans find_pair)
  rw [pair_params] at hpar
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  -- the counter below the bound, at the callee
  suffices H : ∃ a k n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 11 < maxCells ∧ σ (.n 0) = gen ^ k ∧
      σ (.n 1) = gen ^ n ∧ k ≤ n ∧ n ≤ 16 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0)) 4310 (refMem r.img (a + 11) * gen ^ q) ∧
      q + 8 * (n - k) ≤ 8192 by
    obtain ⟨a, k, n, q, h1, h2, h3, h4, hkn, h6, h7, h8⟩ := H
    obtain ⟨k', hk', h0'⟩ := loop_ctr_lt hr hJS hJt find_pair pair_loop.1 pair_loop.2 pair_params h4 (by omega)
    obtain rfl : k = k' := gen_pow_inj (by omega) (by omega) (h3.symm.trans h0')
    exact ⟨a, k, n, q, h1, h2, h3, h4, hk', h6, h7, h8⟩
  -- the caller: the layer loop, or the loop's tail
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) (name% «verify_bus_gkr_loop0_loop0», name% «verify_bus_gkr_loop0») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  rcases hcal with hL | ⟨hS, hl⟩
  · -- the layer loop's call
    obtain rfl : fI = name% «verify_bus_gkr_loop0» := hnI.symm.trans hL
    obtain rfl : fnI = fn% «verify_bus_gkr_loop0» := Option.some.inj (hfI.symm.trans find_ly)
    obtain ⟨i', hji, hi', -, hfi, hci', -⟩ := fn_of_idx ly_idx
    have hcj : coreOf (fn_idx% «verify_bus_gkr_loop0») = fn% «verify_bus_gkr_loop0» := by
      rw [hci']; exact Option.some.inj (hfi.symm.trans find_ly)
    -- the site
    have hs := Res.calls_sites ly_pair_sites hw c hc
    rw [hcf] at hs
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hargs, hrets⟩ := hs
    obtain ⟨s, hsite⟩ := ly_pair_site hargs hrets
    -- not the path's last call: that is the tail's
    obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ _ hfI ly_loop.1
    have hw' : walk σI (coreOf (fn_idx% «verify_bus_gkr_loop0»)).body = .ret es vs := by rw [hcj]; exact hw
    have hlast : ¬ ((coreOf (fn_idx% «verify_bus_gkr_loop0»)).loop = true ∧ i + 1 = (calls es).length) := by
      rintro ⟨-, hi1⟩
      obtain ⟨p0, prest, c0, i0, es1, -, -, hes, -, -⟩ := Res.loop_path hsh hw hh
      rw [hes, Res.loop_calls] at hci hi1
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hi1
      subst hi1
      rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
      simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
      rw [← hci] at hcf
      dsimp only at hcf
      rw [Da.fn_name_of_find find_ly] at hcf
      exact absurd hcf (by decide)
    have hH := B2C.H_eq_kidHdr hIt ly_idx hw' i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    simp only [hlast, ↓reduceIte, hsite] at hH
    -- the stream at the layer loop's frame
    have hfb := inst_fb hr hI (by rw [hIt]; rfl) ly_idx
    have hF0 := inst_frame hr hI hIt ly_idx hw'
    obtain ⟨h9c, h11⟩ := ly_cell9
    have hp9 : V.n 9 ∈ (coreOf (fn_idx% «verify_bus_gkr_loop0»)).params := by rw [hcj, ly_params]; simp
    obtain ⟨hlt11, hm11⟩ := ref_read hr (by rw [h9c]; omega)
      (hF0.val (.n 9) (List.mem_append_left _ (List.mem_append_left _ hp9)) (by rw [h9c]; omega)
        (by rw [h9c]; omega))
    rw [h9c] at hlt11 hm11
    -- the layer loop's slot and its first record
    obtain ⟨jI, m, sh, q, h0I, h1I, hjm, hm, hsh2, h2I, h8I, hcurI, hroomI⟩ := lyQ_all hr I hI σI bufsI kidsI hIt
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid gkr_hfs hv hfI
    rw [ly_body, holdsList_append, holdsList_noRet _ lyPre_noRet] at hb
    obtain ⟨hrec, -⟩ := ly_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hb.1 (by omega) hsh2 h0I h2I h8I hcurI
    have c63 := tb_holds_atom lyPre_noRet hb.1 47 (.const (.n 63) (word 1 0)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_one] at c63
    have hhd : J.hdr.2 = ofK (addressOfIndex I.fp) := by rw [hhdr, hH]
    rw [hargs] at hpar
    simp only [pairArgsV, List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -⟩ := hpar
    refine ⟨I.fp, 0, jI, q, hhd, hlt11, by rw [p0, c63, pow_zero], by rw [p1, h0I], Nat.zero_le _, by omega, ?_,
      by omega⟩
    rw [p2, p0, c63, mul_one, hm11]
    exact hrec
  · -- the loop's tail call
    obtain rfl : fI = name% «verify_bus_gkr_loop0_loop0» := hnI.symm.trans hS
    obtain rfl : fnI = fn% «verify_bus_gkr_loop0_loop0» := Option.some.inj (hfI.symm.trans find_pair)
    obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ _ hfI hl
    obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, -⟩ := Res.loop_path hsh hw hh
    have hw0 := hw
    subst hes
    have hnm : (fn% «verify_bus_gkr_loop0_loop0»).name = name% «verify_bus_gkr_loop0_loop0» :=
      Da.fn_name_of_find find_pair
    rw [Res.loop_calls, hnm] at hci
    have hi : i = (calls es1).length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hci
        have hc1 := walk_callees (σ := σI) (loopBody (fn% «verify_bus_gkr_loop0_loop0»)) (c := c)
          (by rw [hw1]; exact List.mem_of_getElem? hci)
        rw [hcf] at hc1
        exact absurd hc1 (by decide +kernel)
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
        cases hci
    subst hi
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
    obtain ⟨i2, hji2, hi2, -, hf', hc', -⟩ := fn_of_idx hj
    have hcj : coreOf j = fn% «verify_bus_gkr_loop0_loop0» := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
    have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw0) (calls es1).length
    unfold kidHdr at hH
    rw [Res.loop_calls, hnm, List.getElem?_append_right le_rfl, Nat.sub_self] at hH
    simp only [List.getElem?_singleton, ↓reduceIte] at hH
    rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl, by simp⟩)] at hH
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
    simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
    subst hci
    rw [pair_params] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -⟩ := hpar
    -- the iteration's cursor
    obtain ⟨a, kI, n, q, hhdI, ha11, h0I, h1I, hkn, hn, hldI, hroomI⟩ := hQI σI bufsI kidsI hIt
    obtain ⟨-, hnext⟩ := pair_next hw0 hh hldI
    refine ⟨a, kI + 1, n, q + 8, by rw [hhdr, hH, hhdI], ha11, ?_, by rw [p1, h1I], by omega, hn, ?_, by omega⟩
    · rw [p0, hi0, h0I, ← gen_pow_eq_ofK, ← pow_add]
    · rw [p2, p0, hi0, ← gen_pow_eq_ofK, pow_one, pow_add, ← mul_assoc (refMem r.img (a + 11))]
      exact hnext

/-- **The pair loop's cursor at every honest instance.** -/
theorem pairQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, PairQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (pairQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro σ bufs kids hJt
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
