/-
  LeanVM.Guest.EndExecRStP

  `keccak_layer`'s two loops' cursors in the proof stream (`LoopQ`), carried down from the layer.
-/

module

public import LeanVM.Guest.EndExecRStL
public import LeanVM.Guest.EndExecRA

/-!
# The pack rounds' cursors

`LoopQ r J`: at an instance of `keccak_layer__L{first}`'s eight-round loop (`rem = false`) or its
remainder loop, its header names a frame `a` whose cell `17` (the layer's stream) holds `st`, its
counter is `g^j` below its bound `g^n`, `n < 32`, and its record `rounds·g^j` holds the cursor
`st·g^q` with room for its `S (n - j)` words (`S = stStep rem`, sixteen or two).

`loopQ_all`: at every honest instance, by `Res.insts_down`. The loops' callers are the layer and the
loop itself (`Res.termCallers_all`). The layer calls a loop only at its site (`lay_sites`), so the
callee's header names the layer's frame and its arguments are the layer's: the counter `1`, the
bound `step_g` or `rem_g`, the first record's cursor `48` words past the layer's (`layer_setup`), the
remainder loop's record `16 (y / 8)` words further (`pack_cur`), and `LayQ` gives the room. A tail
call keeps the header and steps the counter (`Res.loop_path`); the iteration's step moves the cursor
(`stLoop_next`). The counter lies below the bound at every instance (`loop_ctr_lt`, `Res.chain`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- `keccak_layer__L{first}`'s eight-round loop (`rem = false`) or its remainder loop. -/
def stLoop (first : ℕ) (rem : Bool) : String := if rem then remLoopName first else packLoopName first

/-- The words an iteration reads past its cursor. -/
def stStep (rem : Bool) : ℕ := if rem then 2 else 16

/-- The loop's arguments at the layer's call, the layer's values from `o`. -/
def stArgs (o : ℕ) (rem : Bool) : List V :=
  if rem then [.n (o + 738), .n 10, .n (o + 727), .n (o + 731), .n 14, .n (o + 735)]
  else [.n (o + 726), .n 9, .n (o + 720), .n (o + 718), .n (o + 719), .n 14]

/-- The layer's index. -/
def layIdx (first : ℕ) : ℕ := if first = 1 then fn_idx% «keccak_layer__L1» else fn_idx% «keccak_layer__L0»

/-- The layer's calls of its loops: at their arguments, returning nothing. -/
def laySiteP (first : ℕ) (g : String) (args rets : List V) : Bool :=
  [false, true].all fun rem ↦ g != stLoop first rem || (args == stArgs (layOff first) rem && rets == [])

/-- **A loop's cursor in the layer's stream.** -/
def LoopQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ first < 2, ∀ rem, f = stLoop first rem →
    ∃ a j n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 17 < maxCells ∧ σ (.n 0) = gen ^ j ∧
      σ (.n 1) = gen ^ n ∧ j < n ∧ n < 32 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0)) 80 (refMem r.img (a + 17) * gen ^ q) ∧
      q + stStep rem * (n - j) ≤ 8192

end

public section

variable {rd : Reader}

/-! ## The loops -/

/-- A loop, found: its parameters `loopParams`, a loop helper ending at its bound parameter, its
body without the tail free of calls. -/
theorem stLoop_found {first : ℕ} (hf : first < 2) (rem : Bool) :
    ∃ fn, coreProgram.find? (stLoop first rem) = some fn ∧ fn.params = loopParams ∧ fn.loop = true ∧
      Res.endOfFn fn = some none ∧ Stmt.blockCallees (loopBody fn) = [] := by
  interval_cases first <;> cases rem
  · exact ⟨_, find_pack8_458, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨_, find_packRem_459, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨_, find_pack8_456, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨_, find_packRem_457, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A loop returns nothing. -/
theorem stLoop_rets {first : ℕ} (hf : first < 2) (rem : Bool) {args rets : List E}
    (h : coreProgram.Rel rd (stLoop first rem) args rets) : rets = [] := by
  cases rem
  · simp only [stLoop, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨fn, hfn, hb, -⟩ := find_pack8 hf
    obtain ⟨σ, -, hbody⟩ := (rel_iff_sem hfn args rets).mp h
    rw [hb, pack8T, holdsList_append] at hbody
    obtain ⟨-, hc⟩ := (holdsList_atoms (VerifySub.allAtoms_of_all pack8Pre_atoms) _ _).1 hbody
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hc
    exact hc.2.2.symm
  · simp only [stLoop, ↓reduceIte] at h
    obtain ⟨fn, hfn, hb, -⟩ := find_packRem hf
    obtain ⟨σ, -, hbody⟩ := (rel_iff_sem hfn args rets).mp h
    rw [hb, packRemT, holdsList_append] at hbody
    obtain ⟨-, hc⟩ := (holdsList_atoms (VerifySub.allAtoms_of_all packRemPre_atoms) _ _).1 hbody
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hc
    exact hc.2.2.symm

/-- **An iteration moves the cursor** `stStep rem` words on, into the next record. -/
theorem stLoop_next {first : ℕ} (hf : first < 2) (rem : Bool) {x hg rec a3 a4 a5 cur : E} {rets : List E}
    {j : ℕ} (h : coreProgram.Rel rd (stLoop first rem) [x, hg, rec, a3, a4, a5] rets) (hx : x = gen ^ j)
    (h0 : LoadHolds rd (rec * x) 80 cur) :
    LoadHolds rd (rec * gen ^ (j + 1)) 80 (cur * gen ^ stStep rem) := by
  obtain rfl := stLoop_rets hf rem h
  obtain ⟨d, hd⟩ := h
  cases d with
  | zero => exact hd.elim
  | succ d =>
    cases rem
    · simp only [stLoop, Bool.false_eq_true, ↓reduceIte] at hd
      obtain ⟨fn, hfn, hb, hp⟩ := find_pack8 hf
      obtain ⟨⟨cap, cur', cl, sc, rs, ms, chs, cl', sc', cap', h0', -, -, -, -, -, h1'⟩, -⟩ :=
        pack8_step hfn hb hp d x hg rec a3 a4 a5 hd
      have e : cur' = cur := loadHolds_unique h0'.2.1 h0
      have h1 := h1'.2.1
      rw [hx, loadHolds_rec_succ, e] at h1
      exact h1
    · simp only [stLoop, ↓reduceIte] at hd
      obtain ⟨fn, hfn, hb, hp⟩ := find_packRem hf
      obtain ⟨cap, cur', cl, sc, r, g1, g2, h0', -, -, -, h1'⟩ := (packRem_step hfn hb hp d x hg rec a3 a4 a5 hd).1
      have e : cur' = cur := loadHolds_unique h0'.2.1 h0
      have h1 := h1'.2.1
      rw [hx, loadHolds_rec_succ, e] at h1
      exact h1

theorem room_step {S q n j : ℕ} (h : j < n) (h' : q + S * (n - j) ≤ 8192) : q + S + S * (n - (j + 1)) ≤ 8192 := by
  have e : n - j = n - (j + 1) + 1 := by omega
  rw [e, Nat.mul_succ] at h'
  omega

variable {r : Ref}

/-- **A loop's counter lies below its bound** at an honest instance: `g^j`, `j < n`, the bound `g^n`. -/
theorem loop_ctr_lt (hr : r.Ok) {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node f σ bufs kids)
    {fn : Fn} (hf : coreProgram.find? f = some fn) (hl : fn.loop = true) (he : Res.endOfFn fn = some none)
    (hps : fn.params = loopParams) {n : ℕ} (h1 : σ (.n 1) = gen ^ n) (hn : n < 32) :
    ∃ j < n, σ (.n 0) = gen ^ j := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  have hfs : ∀ g, 1 ≤ B2C.fs g := fun g ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  have hroot : Res.CtrOk coreProgram B2C.fs (r.T.total B2C.fs + 1) r.T := by
    intro f' σ' _ _ fn' hT' hg hl'
    have := (progOk_guest.loop f' fn' hg hl').1
    have hn' := hr.name
    rw [hT'] at hn'
    simp only [Tree.name] at hn'
    subst hn'
    exact absurd this (by decide)
  obtain ⟨p0, prest, e1, hps', hσ0, hb⟩ := Res.insts_ctr hfs progOk_guest r.T _ r.hdr hH.valid le_rfl hroot J hJ
    f σ bufs kids fn hJt hf hl
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hJ hJt
  obtain ⟨-, e, he', hs, -⟩ := progOk_guest.loop f fn hf hl
  obtain rfl : e = none := Option.some.inj (he'.symm.trans he)
  obtain ⟨m, p0', prest', hps'', hm1, hm2, hm⟩ := Res.chain hfs _ le_rfl hv hf hs
  rw [hps] at hps' hps''
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps''
  simp only [Res.endVal, hps, loopParams, h1] at hm
  rw [hσ0, Res.ofK_gpow_add, ← Value.gen_pow_eq_ofK] at hm
  have hT : r.T.total B2C.fs ≤ 2 ^ 28 := (le_two_pow_logMem _).trans (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [hJt] at hb
  have := Value.gen_pow_inj (by omega) (by omega) hm
  exact ⟨e1, by omega, by rw [hσ0, Value.gen_pow_eq_ofK]⟩

/-! ## The layer's calls -/

theorem layIdx_eq {first : ℕ} (hf : first < 2) : idxOf (layerName first) = some (layIdx first) := by
  interval_cases first <;> decide +kernel

theorem layIdx_facts {first : ℕ} (hf : first < 2) :
    cellJ (layIdx first) (.n 15) = 17 ∧ 17 < fsN (layIdx first) ∧ (coreOf (layIdx first)).loop = false := by
  interval_cases first <;> decide +kernel

/-- **The layer calls its loops only at their sites.** -/
theorem lay_sites {first : ℕ} (hf : first < 2) : Res.sitesB (laySiteP first) (coreOf (layIdx first)).body = true := by
  interval_cases first <;> decide +kernel

/-- Each loop's site in the layer's plumbing. -/
theorem lay_site {first : ℕ} (hf : first < 2) (rem : Bool) {c : Call} (ha : c.args = stArgs (layOff first) rem)
    (hr : c.rets = []) : ∃ s, siteOf (layIdx first) c = some s := by
  unfold siteOf
  rw [ha, hr]
  refine Option.isSome_iff_exists.mp ?_
  interval_cases first <;> cases rem <;> decide +kernel

theorem packSetupT_noRet {first : ℕ} (hf : first < 2) : Stmt.noRetList (packSetupT (layOff first) first) = true := by
  interval_cases first <;> decide +kernel

/-- **The layer's pack rounds' setup**: the first record's cursor `48` words past the layer's, the
eight-round loop's call, the remainder loop's record, the counters' `1`. -/
theorem layer_setup {first : ℕ} (hf : first < 2) {C : CallRel} {σ : Val} {kret : List E → Prop}
    {body : List Stmt} (hbd : body = layerT first) (h : Stmt.HoldsList C rd σ body False kret) :
    LoadHolds rd (σ (.n (layOff first + 720))) 80 (σ (.n 7) * gen ^ 48) ∧
      (1 + σ (.n 9) ≠ 0 → C (packLoopName first) [1, σ (.n 9), σ (.n (layOff first + 720)),
        σ (.n (layOff first + 718)), σ (.n (layOff first + 719)), σ (.n 14)] []) ∧
      σ (.n (layOff first + 727)) = σ (.n (layOff first + 720)) * σ (.n 9) ∧
      σ (.n (layOff first + 726)) = 1 ∧ σ (.n (layOff first + 738)) = 1 := by
  subst hbd
  rw [layerT_split, holdsList_append, holdsList_noRet _ (layA_noRet hf)] at h
  replace h := h.2
  rw [holdsList_append] at h
  obtain ⟨ha, -⟩ := holdsList_mem (packSetupT_noRet hf) h
  obtain ⟨-, hrec0, -, hloopC, e727, -, -, -⟩ := packSetupT_holds h
  have e726 := ha (.const (.n (layOff first + 726)) (word 1 0)) (by simp [packSetupT])
  have e738 := ha (.const (.n (layOff first + 738)) (word 1 0)) (by simp [packSetupT])
  simp only [Atom.Holds] at e726 e738
  exact ⟨hrec0.2.1, hloopC, e727, by rw [e726, word_one], by rw [e738, word_one]⟩

/-! ## Down the honest tree -/

/-- **A loop's cursor passes down from the layer, and from one iteration to the next.** -/
theorem loopQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (LoopQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    f σ bufs kids hJt first hf rem hfL
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fl, hfl, hpl, hll, hel, hbc⟩ := stLoop_found hf rem
  rw [hfL] at hfn
  obtain rfl : fn = fl := Option.some.inj (hfn.symm.trans hfl)
  rw [hpl] at hpar
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  -- the counter below the bound, at the callee
  suffices H : ∃ a j n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 17 < maxCells ∧ σ (.n 0) = gen ^ j ∧
      σ (.n 1) = gen ^ n ∧ j ≤ n ∧ n < 32 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0)) 80 (refMem r.img (a + 17) * gen ^ q) ∧
      q + stStep rem * (n - j) ≤ 8192 by
    obtain ⟨a, j, n, q, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
    obtain ⟨j', hj', h0'⟩ := loop_ctr_lt hr hJS hJt (hfL ▸ hfl) hll hel hpl h4 h6
    obtain rfl : j = j' := Value.gen_pow_inj (by omega) (by omega) (h3.symm.trans h0')
    exact ⟨a, j, n, q, h1, h2, h3, h4, hj', h6, h7, h8⟩
  -- the caller: the layer, or the loop's tail
  have hmem : (stLoop first rem, layerName first) ∈ Res.termCallers := by
    interval_cases first <;> cases rem <;> decide
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf, hfL] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  rcases hcal with hL | ⟨hS, hl⟩
  · -- the layer's call
    obtain rfl : fI = layerName first := hnI.symm.trans hL
    have hjL := layIdx_eq hf
    obtain ⟨i', hji, hi', -, hfi, hci', -⟩ := fn_of_idx hjL
    obtain rfl : fnI = coreOf (layIdx first) := by rw [hci']; exact Option.some.inj (hfI.symm.trans hfi)
    obtain ⟨fL, hfL', hbL, hpL⟩ := layer_found hf
    obtain rfl : coreOf (layIdx first) = fL := Option.some.inj (hfI.symm.trans hfL')
    obtain ⟨h15, h17, hloopL⟩ := layIdx_facts hf
    -- the site
    have hs := List.all_eq_true.mp (Res.calls_sites (lay_sites hf) hw c hc) rem (by cases rem <;> simp)
    rw [hcf, hfL] at hs
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hargs, hrets⟩ := hs
    obtain ⟨s, hsite⟩ := lay_site hf rem hargs hrets
    have hH := B2C.H_eq_kidHdr hIt hjL hw i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_right (by rw [hloopL]; simp), hsite] at hH
    -- the stream at the layer's frame
    have hfb := inst_fb hr hI (by rw [hIt]; rfl) hjL
    have hF0 := inst_frame hr hI hIt hjL hw
    have hp15 : V.n 15 ∈ (coreOf (layIdx first)).params := by rw [hpL]; simp
    obtain ⟨hlt17, hm17⟩ := ref_read hr (by rw [h15]; omega)
      (hF0.val (.n 15) (List.mem_append_left _ (List.mem_append_left _ hp15)) (by rw [h15]; omega)
        (by rw [h15]; omega))
    rw [h15] at hlt17 hm17
    -- the layer's cursor and its setup
    obtain ⟨p, y, e7, hy, h9, h10, hroom⟩ := layQ_all hr I hI _ σI bufsI kidsI hIt first hf rfl
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
    obtain ⟨hrec0, hloopC, e727, e726, e738⟩ := layer_setup hf hbL hb
    have hhd : J.hdr.2 = ofK (addressOfIndex I.fp) := by rw [hhdr, hH]
    rw [hargs] at hpar
    have hd : y / krStep < 32 ∧ y % krStep < 32 ∧ 16 * (y / krStep) + 2 * (y % krStep) = 2 * y := by
      simp only [krStep]; omega
    cases rem
    · simp only [stArgs, loopParams, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
        List.cons.injEq] at hpar
      obtain ⟨p0, p1, p2, -, -, -⟩ := hpar
      refine ⟨I.fp, 0, y / krStep, p + 48, hhd, hlt17, by rw [p0, e726, pow_zero], by rw [p1, h9],
        Nat.zero_le _, by omega, ?_, ?_⟩
      · rw [p2, p0, e726, mul_one, hm17]
        rw [e7, mul_assoc, ← pow_add] at hrec0
        exact hrec0
      · simp only [stStep, Bool.false_eq_true, ↓reduceIte]
        omega
    · simp only [stArgs, loopParams, ↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq] at hpar
      obtain ⟨p0, p1, p2, -, -, -⟩ := hpar
      have hP := pack_cur hf hd.1 h9 (fun hne ↦ Res.KidRel.rel (hloopC hne)) hrec0 _ le_rfl
      refine ⟨I.fp, 0, y % krStep, p + 48 + 16 * (y / krStep), hhd, hlt17, by rw [p0, e738, pow_zero],
        by rw [p1, h10], Nat.zero_le _, by omega, ?_, ?_⟩
      · rw [p2, p0, e738, mul_one, e727, h9, hm17]
        rw [e7, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← Nat.add_assoc] at hP
        exact hP
      · simp only [stStep, ↓reduceIte]
        omega
  · -- a loop's tail call
    obtain rfl : fI = f := (hnI.symm.trans hS).trans hfL.symm
    obtain rfl : fnI = fn := Option.some.inj (hfI.symm.trans (by rw [hfL]; exact hfn))
    obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ fnI hfI hl
    obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, -⟩ := Res.loop_path hsh hw hh
    subst hes
    have hnm : fnI.name = fI := Da.fn_name_of_find hfI
    rw [Res.loop_calls, hnm] at hci
    have hi : i = (calls es1).length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hci
        have hc1 := walk_callees (σ := σI) (loopBody fnI) (c := c)
          (by rw [hw1]; exact List.mem_of_getElem? hci)
        rw [hbc] at hc1
        exact absurd hc1 List.not_mem_nil
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
        cases hci
    subst hi
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
    simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
    subst hci
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
    obtain ⟨i2, hji2, hi2, -, hf', hc', -⟩ := fn_of_idx hj
    have hcj : coreOf j = fnI := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
    have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) (calls es1).length
    unfold kidHdr at hH
    rw [Res.loop_calls, hnm, List.getElem?_append_right le_rfl, Nat.sub_self] at hH
    simp only [List.getElem?_singleton, ↓reduceIte] at hH
    rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl, by simp⟩)] at hH
    -- the parameters: the counter stepped, the rest kept
    rw [hpl] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    simp only [loopParams, List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -, -⟩ := hpar
    -- the iteration's cursor
    obtain ⟨a, jI, n, q, hhdI, ha17, h0I, h1I, hjn, hn, hldI, hroomI⟩ := hQI fI σI bufsI kidsI hIt first hf rem hfL
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    have hrel := Tree.Valid.rel _ hv
    unfold Tree.Valid at hv
    obtain ⟨fn', hf'', hp', -⟩ := hv
    obtain rfl : fn' = fnI := Option.some.inj (hf''.symm.trans hfI)
    rw [hpl] at hp'
    simp only [loopParams, List.map_cons, List.map_nil] at hp'
    rw [← hp'] at hrel
    simp only [Tree.name] at hrel
    rw [hfL] at hrel
    have hnext := stLoop_next hf rem hrel h0I hldI
    refine ⟨a, jI + 1, n, q + stStep rem, by rw [hhdr, hH, hhdI], ha17, ?_, by rw [p1, h1I], by omega, hn, ?_,
      room_step hjn hroomI⟩
    · rw [p0, hi0, h0I, ← Value.gen_pow_eq_ofK, ← pow_add]
    · rw [p2, p0, hi0, h0I, ← Value.gen_pow_eq_ofK, ← pow_add, pow_add gen q, ← mul_assoc]
      exact hnext

/-- **A loop's cursor at every honest instance.** -/
theorem loopQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, LoopQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (loopQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro f σ bufs kids hJt first hf rem hfL
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  subst hn
  interval_cases first <;> cases rem <;> exact absurd hfL (by decide)

end

end LeanVM.Guest.EndExec
