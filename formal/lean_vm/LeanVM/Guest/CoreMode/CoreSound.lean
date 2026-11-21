/-
  LeanVM.Guest.CoreMode.CoreSound

  The core route meets the frame interface: `frameSpec_core`.
-/

module

public import LeanVM.Guest.CoreMode.CoreJump

/-!
# The core route's frame interface, proved

`frameSpec_core`: a function passing the kernel's checks (`CoreOk`) meets `FrameSpec` for `CoreAt`
on a reference image, at states on its run where its frames have honest valuations (`CoreHon`).

* The heap facts (`heapK_sound`): `heapOk` or the check with calls give every event's needs
  written before it (`ReadsOkC`) and the promised cells written by the end.
* Entry: the frame walk's entry (`atF_entry`), the pairing at the body (`pairAt_zero`), the heap
  preconditions the signature's, written at entry (`hw_slot`).
* A step: `frame_step`, its oracle's heap cell written by the pairing (`pair_readC`), a fall-through
  at the pairing's next position (`pair_fallC`), a store's cell written by its `DEREF` (`StoreW`); the
  return, the last instruction, with the signature's guarantees (`pair_retC`); a call or a conditional
  call entered (`pair_callAny`): the callee's mode signature's entry facts from its heap signature's
  preconditions (`jumpCallOk`, `fitB`; a loop's self cell from the frame walk, `holds_entryAbs`), and the
  caller resumed in any memory agreeing with the reference past the callee's guarantees (`Resume`, a
  loop's runs among them), the callee frame's cells holding the call's words (`HonF.kid`); a conditional
  call skipped falls through (`core_jfall`).

Its parts: the heap facts and the body's values (`CoreFacts.lean`), the frame's hints, jumps and calls
(`CoreJump.lean`); here the proof.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs fwdOff_eq
  walk_ret_cons walk_atom_cons pre_eq_ret)
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk)

@[expose] public section

variable {κ : ℕ}

/-- **The core route meets the frame interface**: a function passing the kernel's checks, on the
executor's tables for the guest's advice, its code the executor's, at states `Y` on a reference run
where its frames have honest valuations. -/
theorem frameSpec_core {K : Mode.Cert} {Cf : CFun} (hok : CoreOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) (hU : UsedNext C img Y) {Ct : Mode.Cts} (hCt : CtOk img Ct K Cf) :
    FrameSpec C (refMem img) Y Ct K (CoreAt img Cf K.code) := by
  have hsh := hok.shape
  simp only [shapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    Option.isNone_iff_eq_none, beq_iff_eq] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbody, hmainO⟩, hself1⟩, hpc0⟩, hrN⟩, htgt⟩, hsout⟩, hfpM⟩, hent⟩, hend⟩, hincr⟩ := hsh
  have hctrl := bodyC_ctrl hbody
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hown := hok.sig
  unfold ownOk at hown
  have hsigM : Cf.hc = false → sigOk K.F.sig Cf Cf.fn.params.length (retN Cf.fn.body) (Mode.jtRng K.E) = true := fun h ↦ by
    rw [h] at hown; exact hown
  obtain ⟨hself, hghost⟩ : K.F.sig.self = none ∧ (Cf.hc = true → Cf.H.sig.ghosts = 0) := by
    cases hc : Cf.hc
    · exact ⟨Option.isNone_iff_eq_none.mp (SigOkP.of_ok (hsigM hc)).self, fun h ↦ by cases h⟩
    · rw [hc] at hown
      simp only [hcOwn, Bool.cond_true, Bool.and_eq_true, Option.isNone_iff_eq_none] at hown
      exact ⟨hown.1.1.1.1, fun _ ↦ by simpa using hown.2⟩
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
  have hpar := heapK_params hok.heap
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  have hws0' : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ ++ ownG Cf.H.sig σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_lt (by simpa using hb)]
    exact hws0 hσ b hb
  refine ⟨fun hle hfp h ↦ h.mono hle hfp, ?_, ?_⟩
  · -- the entry
    intro s hH0 hs
    cases hhc : Cf.hc
    case true =>
      -- a heap contract: its preconditions at the parameters' words
      rw [preAt_ownH hCt hhc] at hH0
      obtain ⟨hw, hpreH⟩ := hH0
      refine coreAt_of (by rw [CFun.xc, hhc]; intro o ho; cases ho) ⟨atF_mono (s := s) (Mem.le_refl _) rfl
        (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho), fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩),
        fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
      obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
      refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
        by simpa using hσ.holds _ _ hwk, by simp, fun y hy ↦ ?_⟩
      simp only [WrittenC, ownG_zero (hghost hhc), List.append_nil] at hy
      rcases hy with hy | ⟨e, he, -⟩
      · exact hpreH y (by rw [wsAt_eq (by simp [hnp]) (hws0 hσ)]; exact hy)
      · cases he
    rw [preAt_own hCt hhc] at hH0
    have hsig := SigOkP.of_ok (hsigM hhc)
    have hpreP := hsig.preP
    have hprePR := hsig.prePR
    have hpre := hsig.pre
    have hpreR := hsig.preR
    have hgwS := hsig.gw
    simp only [Bool.and_eq_true, List.all_eq_true] at hpreP hprePR hpreR hgwS
    have hgwS' : ∀ x ∈ Cf.H.sig.gw, x.2 < Cf.H.sig.ghosts ∧ ∀ p, x.1.bases = [(p, 1)] → p < Cf.fn.params.length := by
      intro x hx
      obtain ⟨h1, h2⟩ := hgwS x hx
      refine ⟨Nat.blt_eq.mp h1, fun p hp ↦ ?_⟩
      rw [hp] at h2
      simpa using h2
    have hA : entryAbs K.E K.F.sig = ⟨Mode.foldlT .nil K.F.sig.entry, .nil, .nil, [], K.F.sig.pre,
        Mode.jtRng K.E :: K.F.sig.preR, K.F.sig.term, [], .nil, K.F.sig.preP, []⟩ := by
      unfold entryAbs
      rw [hself]
    rw [hA] at hH0
    have hw : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦
      hH0.w o (foldlT_mem _ _ hent' ho)
    refine coreAt_of (by rw [CFun.xc_of hhc, hok.fsig]; exact expW_of hκ hs.agree (fun r hr ↦ hH0.r r (List.mem_cons_of_mem _ hr)) hH0.p)
      ⟨atF_mono (s := s) (Mem.le_refl _) rfl (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho),
      fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩), fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
      by simpa using hσ.holds _ _ hwk, by simp,
      fun y hy ↦ ?_⟩
    have hSE : ∀ {m : Mode.Mono}, monoS K.F.sig np false m = true →
        SlotEq s (Cf.fn.params.map σ ++ ownG Cf.H.sig σ) m.bs :=
      fun hm ↦ slotEq_of hκ hs.agree hs.fp (hws0' hσ) hm
    simp only [WrittenC] at hy
    rcases hy with ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, hps⟩ | ⟨p, hp, a, ha', hpa⟩)) | ⟨e, he, -⟩
    · by_cases hmp : mainPre Cf K.F.sig c = true
      · -- `main`'s entry cell, in its frame `0`
        have h0 : s.fp = 0 := hσ.main (by simp only [mainPre, Bool.and_eq_true] at hmp; exact hmp.1.1)
        exact mainPre_wrk hmp h0 hw hs _
      rcases Bool.or_eq_true_iff.mp (preCov_spec hpre c (List.mem_filter.mpr ⟨hc, by simpa using hmp⟩)) with h | h
      · obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp h
        rw [Bool.and_eq_true] at hmc
        obtain ⟨hmS, hmc⟩ := hmc
        unfold monoIs at hmc
        split at hmc
        · rename_i c' hc'
          rw [← CCell.beq_eq hmc]
          exact hw_slot hc' (hSE hmS) (hH0.h m hm)
        · cases hmc
      · obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp h
        rw [Bool.and_eq_true] at hrc
        exact ptIn_slot hrc.2 (hSE hrc.1) (hH0.r r (List.mem_cons_of_mem _ hr))
    · rcases Bool.or_eq_true_iff.mp (hpreR r hr) with hany | hpt
      swap
      · -- a one-point run at a precondition, over own parameter words
        obtain ⟨m, hm, hmq⟩ := List.any_eq_true.mp hpt
        rw [Bool.and_eq_true] at hmq
        exact rw_ptL hmq.2 (slotEqL_of hκ hs.agree hs.fp (hws0' hσ) hσ.gl (gpF_of hκ hσ hgwS') hmq.1)
          (hH0.h m hm) y hx
      rcases Bool.or_eq_true_iff.mp hany with hany | hcov
      swap
      · exact rw_cov hcov (fun r' _ hm ↦ hSE hm) (fun r' hr' ↦ hH0.r r' (List.mem_cons_of_mem _ hr')) y hx
      obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp hany
      rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
      · rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
        · rw [Bool.and_eq_true] at hrq
          obtain ⟨hmS, hrq⟩ := hrq
          unfold rngIs at hrq
          split at hrq
          · rename_i q hq
            obtain rfl := of_decide_eq_true hrq
            exact rw_slot hq (hSE hmS) (hH0.r r' hr') y hx
          · cases hrq
        · rw [Bool.and_eq_true] at hrq
          obtain ⟨hmS, hrq⟩ := hrq
          unfold rngXIs at hrq
          split at hrq
          · rename_i q hq
            obtain rfl := of_decide_eq_true hrq
            exact rw_slotX hq (hSE hmS) (hH0.r r' hr') y hx
          · cases hrq
      · -- a run over the caller's linked cells
        rw [Bool.and_eq_true] at hrq
        obtain ⟨hbs, hrq⟩ := hrq
        unfold rngLIs at hrq
        split at hrq
        · rename_i q hq
          obtain rfl := of_decide_eq_true hrq
          exact rw_slotL hq (slotEqL_of hκ hs.agree hs.fp (hws0' hσ) hσ.gl (gpF_of hκ hσ hgwS') hbs)
            (hH0.r r' hr')
            y hx
        · cases hrq
    · obtain ⟨w', hw', o, ho, rfl⟩ := hps
      have hall := hpreP p hp
      unfold hpAll at hall
      obtain ⟨m, hm, hmm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall o ho)
      split at hmm
      · rename_i q d hqd
        simp only [Bool.and_eq_true, Nat.beq_eq] at hmm
        obtain ⟨⟨hsl, hpb⟩, rfl⟩ := hmm
        rw [CCell.beq_eq hpb] at hw'
        have h2 : 2 ≤ q := by simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
        exact hw_hp hκ hs.agree h2 (hSE (monoS_fr hsl)) (hpOf_spec hqd ▸ hH0.h m hm) hw'
      · cases hmm
    · obtain ⟨r', hr', hrp⟩ := List.any_eq_true.mp (hprePR p hp)
      simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hrp
      obtain ⟨hmS, hrq, hos⟩ := hrp
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        rw [← hos] at hpa
        exact pw_slotX hκ hs.agree hq (hSE hmS) (hH0.p r' hr') y ⟨a, ha', hpa⟩
      · cases hrq
    · cases he
  · -- a step
    intro s i hi hpc hat hs hYs hsz hhalt henvK _ hjtR _ hmainS _ hh hres href Inv k
    obtain ⟨hAtF0, hentw, hheap⟩ := hat.2 s.mem (Mem.le_refl _) hs.agree
    have hxw := hat.1
    have hAtF : AtF img Cf.frame K.code i s := atF_mono (s := Mode.stOf s.mem s.fp) (Mem.le_refl _) rfl hAtF0
    obtain ⟨σ0, hσ0⟩ := hH s i hYs hi hpc
    obtain ⟨n, hon⟩ := hY s hYs
    have hpcF : s.pc = Cf.frame.entry + i := by rw [hok.fentry]; exact hpc
    have hhintsF := hintsF_of hC ha hK hok.fentry hok.hints
    have hhd := hintsD_of hok.dhints hok.xentry hok.fentry
    have hrwOf : ∀ σ pre es vs rd, walk σ Cf.fn.body = .ret (pre ++ es) vs → (∀ e ∈ pre ++ es, e.Holds rd σ) →
        ResF Cf.H σ → GwOk Cf.H.sig rd σ → (∀ e ∈ pre, EvM Cf.sigOf rd σ e) → ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es :=
      fun σ pre es vs rd hb hh0 hR hG hM ↦ readsAt_of_P (heapK_reads hok.heap hok.pows hbody hb hh0 hR hG) hM
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
    have hlen : Cf.frame.len = K.code.length := hok.flen
    have hlenX : ∀ o < K.code.length, Cf.X.entry + o < 2 ^ 30 := fun o ho ↦ by
      have h := hK.ops o ho
      rw [hok.xentry]
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at h
      cases h
    have hsm : ∀ oc od of, K.code[i]? = some (.jump oc od of) → oc < 2 ^ 28 ∧ od < 2 ^ 28 ∧ of < 2 ^ 28 :=
      fun oc od of hci ↦ by
        have h := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at h
        exact h
    refine frame_step (prog := guestProgram) (k := n - s.steps) hκ harm hacc hok.fpows hend hsz
      (fun j hj ↦ by rw [hok.fentry]; exact hK.ops j hj) hhintsF (hok.fentry ▸ hok.fetch) hok.small hi hpcF hAtF hs
      hon.2 (fun h ↦ hmainS (hok.fmain.trans (hfpM.symm.trans h)))
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (by rw [hpcF, hhintsF i hi]; exact hp) s1 e hm hin)
      (nzr_hnz hκ hok.nzrc harm hacc hi hAtF hs hres) ?_ ?_
      (fun s1 hm ↦ refOk_fp hm.fp href) ?_ ?_
    · -- the oracle's heap cell, written
      intro hOi s1 e1 hm
      have main : ∀ a o c, K.code[i] = .deref a o c .cell → HeapRd s1 (.deref a o c .cell) := by
        intro a o c hci
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        by_cases hj : jtd Cf.X a o c = true
        · have hsm := hok.small i hi
          rw [hci] at hsm
          exact core_jtd hκ hok.pair hctrl hok.jtd (.inr hok.calls) (by rw [List.getElem?_eq_getElem hi, hci]) hj hsm.1 henvK hm hσ0
            hpos hb hwp
        have hsm := hok.small i hi
        rw [hci] at hsm
        exact heapRd_pair hκ hok.pair hpos (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi)
          (Bool.eq_false_iff.mpr hj) hsm.1 hσ0 hb hwp (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) (hrd ▸ hσ0.gw.ok) hM0) hW (hhd i) hs hm e1
      generalize hci : K.code[i] = ins
      cases ins with
      | deref a o c mode =>
        cases mode with
        | cell => exact main a o c hci
        | pc => trivial
        | fp => trivial
      | _ => trivial
    · -- a table jump's target, one of its arms
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, -, -, -⟩ := hheap σ0 hσ0
      exact core_tgt hok.pair hctrl htgt (dspB_of_callsB (callsB_of' hok.heap)) hσ0 hpos hb hwp
    · -- falling through
      intro s1 s' e1 hm hmo e' hpc' hfp' hf' hle' hat' hstw hc0
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hi1 : i + 1 < K.code.length := by
        by_contra hn
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
        rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
        · cases hA
        · cases hg'
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) (coreAt_of (by rw [hfp']; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
          fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ hσ
      by_cases hj : ∃ oc od of, K.code[i]? = some (.jump oc od of)
      · -- a jump not taken
        obtain ⟨oc, od, of, hci⟩ := hj
        have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
          rw [hhd i]; exact e1
        obtain ⟨pos', hpos', evs, es', rfl, hwp', hevs, hWr⟩ := core_jfall hκ hok.pair hctrl hci (hsm oc od of hci).1 e1'
          hs hm (hc0 oc od of hci) hσ hpos hb hwp (hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) (hrd ▸ hσ.gw.ok) hM0) hW
        exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
          by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ (hWr y hy).mono hle'⟩
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fallC (sigOf := Cf.sigOf) (rd := rd)
        (ws0 := Cf.fn.params.map σ) hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', hevs, hWr⟩ := hfallP hwp (hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) (hrd ▸ hσ.gw.ok) hM0)
      refine ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
        by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ ?_⟩
      exact fall_wrk hκ hi (hok.small i hi) hσ hb hW hpairs (hhd i) hs hm hle' hfp' hf' e1 hstw (hWr y hy)
    · -- a jump taken
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt hcn
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      have hcode : K.code[i] = .jump oc od of := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hci)
      have hsm := hok.small i hi
      rw [hcode] at hsm
      obtain ⟨soc, sod, sof⟩ := hsm
      have hw1 : ∀ o ∈ K.F.sig.entry, s1.mem.written (s1.fp + o) = true := fun o ho ↦ by
        rw [hm.fp]; exact written_mono hm.le (hentw o (hok.fsig ▸ ho))
      have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
        rw [hhd i]; exact e1
      obtain ⟨v, hv, hv0⟩ := hcn oc od of hci
      have hz : Cf.X.zeroAt oc = false := by
        cases hzz : Cf.X.zeroAt oc
        · rfl
        · exact absurd (rd_get hκ hm.fine soc (by rw [hm.fp]; exact hσ0.jc.zero oc hzz) hv) hv0
      have hcall0 := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
      rw [hcode] at hcall0
      by_cases hsf : Cf.X.selfAt of = true
      · -- a jump in the frame: a branch's side, a `match`'s arm, a forward jump
        have hof1 : of ≠ 1 := fun h ↦ by rw [h, hself1] at hsf; cases hsf
        have hcj : ∀ t f, Cf.X.pcAt od = some t → getF Cf.X.ents t = some f → Cf.X.selfAt of = false :=
          fun t f ht hf ↦ (jumpCallOk_spec hcall0 ht hf).2.2.1
        have hdn : ∀ s, getF Cf.X.sites of = some s → s.tgt = od → Cf.X.selfAt of = false :=
          fun s hs he ↦ (jumpCallOk_dsp hcall0 hs he).2.2.2
        have hpcs' : s'.pc < 2 ^ 30 := by omega
        -- a return here is `main`'s halting jump
        have hxh : Cf.X.halt < 2 ^ 30 := hok.xhalt ▸ hhalt
        have hmret : (if Cf.X.main then Cf.X.selfAt of = true ∧ Cf.X.pcAt od = some Cf.X.halt else od = 0 ∧ of = 1) →
            Cf.X.main = true ∧ s'.pc = Cf.X.halt := by
          intro hif
          cases hmm : Cf.X.main
          · simp only [hmm, Bool.false_eq_true, ↓reduceIte] at hif; exact absurd hif.2 hof1
          simp only [hmm, ↓reduceIte] at hif
          refine ⟨rfl, ?_⟩
          have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.jc.pcw od _ hif.2) h0
          exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        rcases core_jtaken hκ hok.pair hctrl hlenX hci hcj hsf hdn soc sod e1' hs hm hv hv0 h0 hpcs' hσ0 hpos hb hwp
          (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) (hrd ▸ hσ0.gw.ok) hM0) hW with ⟨hif, -⟩ | ⟨-, o, pos0, hpco, hio, hpos0, -⟩
        · -- `main`'s halt, in its frame `0`
          obtain ⟨hmX, hpcH⟩ := hmret hif
          have hfpS : s'.fp = s1.fp := by
            have := rd_get hκ hm.fine sof (by rw [hm.fp]; exact hσ0.jc.self of hsf) h1
            exact (gpow_inj (lt_maxCells_63 hf'.fp) (lt_maxCells_63 hs.fp) (pow_of_ofK this)).trans hm.fp.symm
          exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.halt (hok.fmain.trans hmX) (hpcH.trans hok.xhalt)
            (hfpS.trans (hm.fp.trans (hmainS (hok.fmain.trans hmX)))))
        have hol := pairAt_lt hok.pair hpos0
        cases hjo with
        | «local» t hnr hfp' hpc' hat' =>
          have hto : t = o := by rw [hok.fentry, ← hok.xentry] at hpc'; omega
          subst hto
          have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move t hfp' hol (by rw [hpc', hok.fentry])
            (coreAt_of (by rw [hfp', hm.fp]; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
              fun o ho ↦ by rw [hfp', hm.fp]; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
          rw [hfp', hm.fp] at hσ
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ hσ
          rcases core_jtaken hκ hok.pair hctrl hlenX hci hcj hsf hdn soc sod e1' hs hm hv hv0 h0 hpcs' hσ hpos hb
            hwp (hrwOf σ pre es vs rd hb hh0 (hσ.res hxw) (hrd ▸ hσ.gw.ok) hM0) hW with ⟨hif, -⟩ |
              ⟨-, o', pos', hpco', -, hpos', evs, es', rfl, hwp', hevs, hWr⟩
          · obtain ⟨hmX, hpcH⟩ := hmret hif
            have hmO := hmainO
            simp only [mainOk, hmX, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmO
            omega
          have ho' : o' = t := by omega
          subst ho'
          exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
            by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ (hWr y hy).mono hle'⟩
        | ret _ _ hr =>
          obtain ⟨c, hc⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc
          exact absurd hc.2.2 hof1
        | halt _ hfpo hpcH hfpS =>
          have hmK : K.F.main = true := hok.fmain.trans (hfpM.symm.trans hfpo)
          exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.halt hmK (hpcH.trans hok.fhalt)
            (hfpS.trans (hm.fp.trans (hmainS hmK))))
        | tail e _ hpc' => rw [hpc', hok.fentry, ← hok.xentry] at hpco; omega
        | call G t _ _ hG _ _ _ =>
          have h := List.all_eq_true.mp hsout o (List.mem_range.mpr (by rw [hlen]; exact hol))
          simp only [Bool.or_eq_true, Nat.beq_eq] at h
          rcases h with h | h
          · omega
          rw [hpco, hok.xentry, ← hok.fentry] at hG
          rw [hG] at h
          cases h
      have hsf' : Cf.X.selfAt of = false := by simpa using hsf
      have hfw : fwdJ Cf.X i oc od of = false := by simp [fwdJ, hsf']
      by_cases hr01 : od = 0 ∧ of = 1
      · -- the return
        obtain ⟨rfl, rfl⟩ := hr01
        have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨oc, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj hnr
        | halt hnr => exact absurd hrj hnr
        | tail e hnr => exact absurd hrj hnr
        | call G t hnr => exact absurd hrj hnr
        | ret hregs hretw _ =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret oc hci (by omega) h0 h1 ?_)
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
          obtain ⟨as, hpairs, hevR, hpr⟩ := pair_retC hok.pair hpos hci hz hfw hpc0 hself1 hwp
            (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) (hrd ▸ hσ0.gw.ok) hM0)
          obtain ⟨-, -, hposts, hpostRs, hretM, hpostM, hptrs, hqs, hretV, hretE, hpostN⟩ :=
            heapK_sound hok.heap hok.pows hbody hb hh0 (hσ0.res hxw) (hrd ▸ hσ0.gw.ok) (evM_app hM0 hevR)
          rw [hhd i] at hpairs
          have W1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK s1.mem x := by
            intro x hx
            rcases hpr x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hm.le
            · exact flow_wrk hκ e1 hs hm hpairs ha hfa
                (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
          have W1' : ∀ x, WrF Cf rd σ0 (pre ++ es) x → WrK s1.mem x := fun x hx ↦
            hx.elim (W1 x) fun ⟨hn, hf⟩ ↦ faw_wrk hok hi hci hAtF hm.le hm.fine hσ0.toHonB hb hn hf
          have hvl : vs.length = retN Cf.fn.body := retsN_len hrN hb
          have hxw1 : Cf.hc = false → ExpW img (expCells K.F.sig) s1.fp := fun hc ↦ by
            rw [hm.fp, ← hok.fsig, ← CFun.xc_of hc]; exact hxw
          have hws : ∀ b < np + retN Cf.fn.body, Rd img s1.fp (2 + b) =
              some (slotW (Cf.fn.params.map σ0 ++ vs.map σ0) b) := by
            intro b hb'
            rw [hm.fp]
            by_cases hb1 : b < np
            · rw [slotW_lt (by simpa using hb1)]; exact hws0 hσ0 b hb1
            · rw [slotW_append]
              simp only [List.length_map, show ¬ b < Cf.fn.params.length from hb1, ↓reduceIte]
              rw [slotW_get (by simp; omega)]
              have := hσ0.retc _ _ hb (b - np) (by omega)
              rw [show 2 + Cf.fn.params.length + (b - np) = 2 + b by omega] at this
              simpa using this
          have htop : Cf.fn.body.all topOk = true := by
            simp only [bodyCore, Bool.and_eq_true] at hbody
            exact hbody.2
          have hcellsP : ∀ m, monoOkP K.F.sig Cf.fn.params.length m = true →
              BaseCellsF (baseOfP Cf.X Cf.fn.body Cf.fn.params.length) (Mode.stOf s1.mem s1.fp) σ0 m.bs :=
            fun m hmk ↦ baseCellsP_of (s := s1) hκ hmk htop hm.fine hw1
              (fun o ho ↦ hretw o (hok.fsig ▸ ho)) (hm.fp ▸ hσ0) hb
              (fun a ha y hy ↦ W1 y (Or.inr ⟨.atom a, ha, hy⟩))
          have hin : ∀ c, cellIn c (Cf.post.map (·.1)) = true → WrK s1.mem (c.addr σ0) := by
            intro c hc
            obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
            rw [← CCell.beq_eq hbeq]
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
            exact W1 _ (hpostM p hp)
          have hSG : ∀ {m : Mode.Mono}, monoR K.F.sig np (retN Cf.fn.body) m = true →
              SlotGet (Mode.stOf s1.mem s1.fp) (Cf.fn.params.map σ0 ++ vs.map σ0) m.bs :=
            fun hm' ↦ slotGet_ret (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hm.fine.fp hws hw1
              (fun o ho ↦ hretw o (hok.fsig ▸ ho)) hm'
          cases hhc : Cf.hc
          case true =>
            -- a heap contract: its guarantees and returned words at its slots' words
            rw [postAt_ownH hCt hhc]
            have hwsA : wsAt img s1.fp (Cf.fn.params.length + retN Cf.fn.body) =
                Cf.fn.params.map σ0 ++ vs.map σ0 := wsAt_eq (by simp [hvl]) hws
            have hwsP : wsAt img s1.fp Cf.fn.params.length = Cf.fn.params.map σ0 :=
              wsAt_eq (by simp) fun b hb' ↦ by rw [hws b (by omega), slotW_lt (by simpa using hb')]
            refine ⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun y hy ↦ ?_, ?_⟩
            · rw [hwsA] at hy
              rcases hy with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | hp
              · exact W1' _ (hposts c (List.mem_append_right _ hc))
              · exact W1' _ (hpostRs r hr _ hx)
              · rcases hp with hp | hp
                · rw [← hrd] at hp; exact W1' _ (hptrs _ hp)
                · rw [← hrd] at hp; exact W1' _ (hqs _ hp)
            · rw [hwsP, hwsA, List.drop_left' (by simp)]
              exact ⟨hretM, hrd ▸ hretV, hretE⟩
          rw [postAt_own hCt hhc]
          have hsig := SigOkP.of_ok (hsigM hhc)
          have hpostL := List.isEmpty_iff.mp hsig.postL
          have hpostP := hsig.postP
          have hpostLP := List.isEmpty_iff.mp hsig.postLP
          have hpostT := List.isEmpty_iff.mp hsig.postT
          have hpostC := List.isEmpty_iff.mp hsig.postC
          have hpost := hsig.post
          have hpostR := hsig.postR
          simp only [Bool.and_eq_true, List.all_eq_true] at hpostP hpost hpostR
          refine ⟨⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun m hm' ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
            fun p hp ↦ ?_, fun p hp ↦ ?_, fun q hq ↦ ?_⟩, fun r hr ↦ ?_, fun q hq ↦ ?_⟩
          · rcases Bool.or_eq_true_iff.mp (hpost m hm') with hc | hc
            swap
            · -- a guarantee over the body's values (`postNIn`)
              simp only [postNIn, Bool.and_eq_true] at hc
              obtain ⟨hmk, hc⟩ := hc
              split at hc
              · rename_i c hmc
                simp only [Bool.and_eq_true] at hc
                obtain ⟨hcv, hcin⟩ := hc
                refine wrk_hwF (expKeep_P _ _ _) hmc (hcellsP m hmk) ?_
                obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcin
                rw [CCell.beq_eq hbeq] at hc'
                have := W1' _ (hpostN.1 _ hc')
                rwa [CCell.addrW, mapN_valW hcv, ← CCell.addrW, ← addr_eq] at this
              · cases hc
            rcases Bool.or_eq_true_iff.mp hc with hc | hc
            · rcases Bool.or_eq_true_iff.mp hc with hc | hc
              · rw [Bool.and_eq_true] at hc
                obtain ⟨hmR, hc⟩ := hc
                split at hc
                · rename_i c hmc
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
                  rw [CCell.beq_eq hbeq] at hc'
                  exact slot_hw hmc (hSG hmR) (W1' _ (hposts c hc'))
                · cases hc
              · simp only [postIn, Bool.and_eq_true] at hc
                obtain ⟨hmk, hc⟩ := hc
                split at hc
                · rename_i c hmc
                  exact wrk_hwF (expKeep_P _ _ _) hmc (hcellsP m hmk) (hin c hc)
                · cases hc
            · unfold hpIn at hc
              split at hc
              · rename_i q d hqd
                simp only [Bool.and_eq_true] at hc
                obtain ⟨⟨hsl, hcl⟩, hps⟩ := hc
                obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hps
                simp only [Bool.and_eq_true, List.contains_iff_mem] at hpp
                obtain ⟨hpb, hko⟩ := hpp
                have h2 : 2 ≤ q := by
                  simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
                have hmR : monoR K.F.sig np (retN Cf.fn.body) ⟨0, 0, [(.fr q, 1)]⟩ = true := by
                  simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or,
                    List.contains_iff_mem] at hsl
                  have h28 : q < 268435456 := hsl.1.2
                  simp [monoR, hsl.1.1.1, h28, hsl.1.1.2, hsl.2]
                have hu1 : s1.mem.used ≤ 2 ^ κ := le_trans hle'.used
                  (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e')
                obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcl
                rw [CCell.beq_eq hbeq] at hc'
                rw [hpOf_spec hqd]
                refine hp_hw (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hu1 h2 (hSG hmR)
                  (W1' _ (hposts _ hc')) fun w hw ↦ ?_
                refine W1' _ (hptrs _ (Or.inl ⟨p', hp', w, ?_, m.k, hko, rfl⟩))
                rw [CCell.beq_eq hpb, hrd]
                exact hw
              · cases hc
          · have hold : ∀ r ∈ K.F.sig.postR, postRB K.F.sig Cf Cf.fn.params.length r = false →
                Mode.RW (Mode.stOf s1.mem s1.fp) r := by
              intro r hr hnb
              have h0 := hpostR r hr
              rcases Bool.or_eq_true_iff.mp h0 with h0 | hRN
              swap
              · -- a guarantee over the body's values (`postRNIn`)
                simp only [postRNIn, Bool.and_eq_true] at hRN
                obtain ⟨hmk, hRN⟩ := hRN
                split at hRN
                · rename_i c lo hi hmc hlo hhi
                  simp only [Bool.and_eq_true, List.contains_iff_mem] at hRN
                  obtain ⟨⟨⟨hokl, hokh⟩, hqv⟩, hqin⟩ := hRN
                  exact rwN_exp hmc (hcellsP _ hmk) hlo hhi (hσ0.res hxw) (hxw1 hhc)
                    (fun k hk ↦ by rw [hm.fp]; exact hσ0.par k hk) hokl hokh fun x hx ↦
                    W1' x (hpostN.2 _ hqin x ((mapN_runSet hqv x).mpr hx))
                · cases hRN
              rw [hnb, Bool.or_false] at h0
              rcases Bool.or_eq_true_iff.mp h0 with h | h
              swap
              · -- bounded by an entry run's exponent cell
                simp only [Bool.and_eq_true] at h
                obtain ⟨⟨⟨hmR, hlo⟩, hhi⟩, hq⟩ := h
                obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp hq
                unfold rngXIs at hrq
                split at hrq
                · rename_i q' hq'
                  obtain rfl := of_decide_eq_true hrq
                  obtain ⟨hl, hh⟩ := rngX_rep_exp hws (hxw1 hhc) (fun k hk ↦ by rw [hm.fp]; exact hσ0.par k hk) (hσ0.res hxw) hq' hlo hhi
                  exact slot_rwX hq' (hSG hmR) hl hh fun x hx ↦ W1' x (hpostRs q' hq x hx)
                · cases hrq
              rcases Bool.or_eq_true_iff.mp h with h | h
              swap
              · simp only [postRIn, Bool.and_eq_true] at h
                obtain ⟨hmk, hc⟩ := h
                split at hc
                · rename_i c hmc
                  split at hc
                  · rename_i l hl
                    exact wrk_rwF (expKeep_P _ _ _) hmc (hcellsP r.q hmk) hl fun p hp ↦ hin p (List.all_eq_true.mp hc p hp)
                  · cases hc
                · cases hc
              rw [Bool.and_eq_true] at h
              obtain ⟨hmR, h⟩ := h
              rcases Bool.or_eq_true_iff.mp h with h | h
              · obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
                unfold rngIs at hrq
                split at hrq
                · rename_i q' hq'
                  obtain rfl := of_decide_eq_true hrq
                  exact slot_rw hq' (hSG hmR) fun x hx ↦ W1' x (hpostRs q' hq x hx)
                · cases hrq
              · split at h
                · rename_i c l hmc hl
                  exact pts_slot hmc hl (hSG hmR) fun p hp ↦ by
                    obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
                    rw [← CCell.beq_eq hbeq]
                    exact W1' _ (hposts c' hc')
                · cases h
            by_cases hb : postRB K.F.sig Cf Cf.fn.params.length r = true
            swap
            · exact hold r hr (by simpa using hb)
            -- inside a guaranteed run up to a constant (`postRB`)
            unfold postRB at hb
            split at hb
            · rename_i q d c hhi
              simp only [Bool.and_eq_true] at hb
              obtain ⟨hmk, hb⟩ := hb
              split at hb
              · rename_i n hn
                obtain ⟨r2, hr2, hr2b⟩ := List.any_eq_true.mp hb
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hr2b
                obtain ⟨⟨⟨⟨hq2, hlo2⟩, hS2⟩, hd2⟩, hr2b⟩ := hr2b
                split at hr2b
                · rename_i N hN
                  obtain ⟨x, hx, hxb⟩ := List.any_eq_true.mp hr2b
                  obtain ⟨m, rfl, hmc, hmcap⟩ := resBnd_spec hxb
                  obtain ⟨vq, xlo, xhi, hmv, hlo, hhi2, hall⟩ := hold r2 hr2 (by simp [postRB, hN])
                  rw [hN] at hhi2
                  obtain rfl : xhi = N := hhi2
                  obtain ⟨ya, yb, hya, hyb, hlt⟩ := hσ0.res hxw _ hx
                  rw [idxC, rep_const (by exact hmcap)] at hyb
                  obtain rfl : yb = m := (Option.some.inj hyb).symm
                  rw [idxC, valW_baseC] at hya
                  obtain ⟨hyac, hσn⟩ := rep_spec hya
                  have hm1 := List.all_eq_true.mp hmk (.hp q d, 1) List.mem_cons_self
                  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hm1
                  obtain ⟨⟨⟨-, hq2'⟩, hqn⟩, -⟩ := hm1
                  have hbv := hcellsP ⟨0, 0, [(.hp q d, 1)]⟩ hmk (.hp q d, 1) List.mem_cons_self n 1
                    (by simp only [baseOfP, show 2 ≤ q ∧ q - 2 < Cf.fn.params.length from ⟨hq2', hqn⟩, and_self,
                      ↓reduceIte, hn, Option.map_some])
                  refine ⟨vq, xlo, ya + c, hq2 ▸ hmv, hlo2 ▸ hlo, ?_, fun j h1 h2 ↦ ?_⟩
                  · rw [hhi]
                    refine ⟨_, ya, (hbv _).mpr rfl, ?_, by rw [capE_eq] at hyac; omega, rfl⟩
                    exact hσn
                  · rw [← hS2, ← hd2]
                    exact hall j h1 (by omega)
                · cases hr2b
              · cases hb
            · cases hb
          · obtain ⟨⟨⟨⟨hmR, hlo⟩, hhi⟩, hpr⟩, hrr⟩ := hpostP q hq
            obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hpr
            simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hpp
            obtain ⟨hrq, hos⟩ := hpp
            split at hrq
            · rename_i q' hq'
              have hpq : q' = p'.1 := of_decide_eq_true hrq
              obtain ⟨q2, hq2, hrr'⟩ := List.any_eq_true.mp hrr
              unfold rngXIs at hrr'
              rw [hq'] at hrr'
              have hq2e : q' = q2 := of_decide_eq_true hrr'
              subst hq2e
              have hu1 : s1.mem.used ≤ 2 ^ κ := le_trans hle'.used
                (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e')
              obtain ⟨hl, hh⟩ := rngX_rep_exp hws (hxw1 hhc) (fun k hk ↦ by rw [hm.fp]; exact hσ0.par k hk) (hσ0.res hxw) hq' hlo hhi
              refine slot_pwX (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hu1 hq' (hSG hmR) hl hh
                (fun x hx ↦ W1' x (hpostRs q' hq2 x hx)) fun x hx ↦ ?_
              obtain ⟨a, ha, hpa⟩ := hx
              refine W1' x (hptrs x (Or.inr ⟨p', hp', a, ?_⟩))
              rw [← hpq, ← hos, hrd]
              exact ⟨ha, hpa⟩
            · cases hrq
          · obtain ⟨h28, hret', hmo', c, hmc, hcase⟩ := retVOk_sound hok.pows (by simpa [hhc] using hok.retv) hb hh0 p hp
            obtain ⟨u, hu⟩ := Mem.get_of_written (hretw p.1 (hok.fsig ▸ hret'))
            have hSG0 : SlotGet (Mode.stOf s1.mem s1.fp) (Cf.fn.params.map σ0) p.2.bs :=
              slotGet_of (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hm.fine.fp
                (fun b hb' ↦ by rw [hm.fp]; exact hws0 hσ0 b hb') hw1 hmo'
            refine ⟨u, hu, ?_⟩
            have hval := monoVal_slot' hmc hSG0
            suffices hu' : u = c.valW (slotW (Cf.fn.params.map σ0)) by rw [hu']; exact hval
            rcases hcase with ⟨v, hv, hloc, hvv⟩ | ⟨h2, hrm⟩
            · have hrd : Rd img s1.fp p.1 = some (σ0 v) := by
                rw [hm.fp, ← hloc]; exact hσ0.rets _ _ hb v hv
              rw [rd_get hκ hm.fine h28 hrd hu, hvv, val_eq]
              refine valW_congr fun b hb' ↦ ?_
              rw [slotW_params' hpar (monoC_bases_lt hmo' hmc b hb')]
              rfl
            · have hk := hretM _ c hrm
              rw [List.getElem?_map] at hk
              obtain ⟨v, hv, hvv⟩ := Option.map_eq_some_iff.mp hk
              have hkl : p.1 - 2 - np < vs.length := (List.getElem?_eq_some_iff.mp hv).1
              have hrd := hσ0.retc _ _ hb (p.1 - 2 - np) hkl
              rw [show 2 + Cf.fn.params.length + (p.1 - 2 - np) = p.1 by omega, hm.fp.symm] at hrd
              rw [rd_get hκ hm.fine h28 hrd hu, (List.getElem?_eq_some_iff.mp hv).2, hvv]
          · rw [hpostT] at hp; cases hp
          · rw [hpostC] at hq; cases hq
          · rw [hpostL] at hr; cases hr
          · rw [hpostLP] at hq; cases hq
      · -- a call
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        have hcall := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
        rw [hcode] at hcall
        -- the call's pairing (a `call`, a `callIf` entered, or a `dispatch`), its callee the same for
        -- every honest valuation of the frame, entered at `t`, its mode signature there `G`
        obtain ⟨f, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, hkC, hpe, hout, ht30, G, hG, hr30,
            hentf, hfit⟩ : ∃ f args rets st t o pos', Cf.X.siteAt of args rets = some st ∧ Cf.X.fwdOff i st.r = some o ∧
            pairAt Cf.P Cf.fn.body K.code Cf.d o = some pos' ∧ ∃ as : List Atom,
            List.Forall₂ (Pairs Cf.X) (as.filter flowAtom)
              (((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).filter isaFlowHint) ∧
            (∀ {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader}, HonF img Cf s.fp σ →
              walk σ Cf.fn.body = .ret (pre ++ es) vs → walk σ pos = .ret es vs →
              ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es →
              ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
                es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧ walk σ pos' = .ret es' vs ∧
                (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
                (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
                  WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
                  ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∧
            s'.pc = t ∧ ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧
            ∃ G, Cf.frame.sigs.get t = some G ∧ st.r < 2 ^ 30 ∧ getF Cf.X.ents t = some f ∧
              callOkC Cf G f st.args.length st.rets.length = true := by
          cases hpcod : Cf.X.pcAt od with
          | some t =>
            obtain ⟨f, args, rets, st, t', o, pos', hsite, hpt, hentF, hfo, hat', as, hpairs, hkA⟩ :=
              pair_callAny hok.pair hpos hci hz hfw hr01 hsf'
                (fun t f ht he ↦ jumpCallOk_next hcall ht (entOk_spec he)) (jumpCallOk_tgt hcall hpcod)
            rw [hpcod, Option.some.injEq] at hpt
            subst hpt
            obtain ⟨hout, ht30, -, G, st', hG, hst', hr30, hfit⟩ := jumpCallOk_spec hcall hpcod (entOk_spec hentF)
            rw [(siteAt_spec hsite).1, Option.some.injEq] at hst'
            subst hst'
            refine ⟨f, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, ?_, ?_, hout, ht30, G, hG, hr30,
              entOk_spec hentF, hfit⟩
            · intro σ pre es vs rd hσ hb' hwp' hrw
              rcases hkA with ⟨-, hkA⟩ | ⟨c, -, hloc, rfl, hkA⟩
              · exact hkA hwp' hrw
              obtain ⟨evs, cs, es', rfl, hwp2, hcs, hasin, hevM, hW'⟩ := hkA hwp' hrw
              have hcond := hσ.jc.cond _ _ hb' c (by simp)
              rw [hloc] at hcond
              have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine soc (by rw [hm.fp]; exact hcond) hv, h0])
              refine ⟨evs ++ [Ev.inK c], cs, es', by simp [hσc], hwp2, hcs, fun a ha ↦ by simp [hasin a ha],
                evM_app hevM (evM_inK_cons evM_nil), fun x hx ↦ ?_⟩
              rcases hW' x (writtenC_noAtom (e := Ev.inK c) (pre := pre ++ evs) (fun a h ↦ by cases h)
                  (fun f a r h ↦ by cases h) (by simpa [List.append_assoc] using hx)) with h | ⟨a, ha, hfa, hma, hwa⟩
              · exact Or.inl h
              · exact Or.inr ⟨a, ha, hfa, by simp [hma], hwa⟩
            · have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.jc.pcw od t hpcod) h0
              exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
          | none =>
            -- a dispatch: the callee its target cell names, by `HonF.tgt` the same for every honest valuation
            obtain ⟨x, fs, args, rets, st, o, pos', hmem, hsite, htg, hfo, hat', as, hpairs, hkD⟩ :=
              pair_dispatch hok.pair hpos hci hz hfw hr01 hsf' hpcod
            have hd0 : od ≠ 0 := (jumpCallOk_dsp hcall (siteAt_spec hsite).1 htg).1
            have hds := dspSite_of hpcod hsite htg hd0
            rw [tgtOk, Exec.listSeq_eq] at htgt
            obtain ⟨kk, hkk⟩ : ∃ kk, Cf.frame.tgt.get (0 + i) = some kk := by
              cases hk : Cf.frame.tgt.get (0 + i) with
              | none => rw [tgtGo_none htgt hci hk] at hds; cases hds
              | some kk => exact ⟨kk, rfl⟩
            obtain ⟨-, hdj⟩ : dspSite Cf.X od of = true ∧ dspJ Cf kk od of = true := by
              rcases tgtGo_at htgt hci hkk with h | ⟨h, -⟩
              · exact h
              · rw [hds] at h; cases h
            obtain ⟨pcs, -, -, -, -, hr30, -, hpcs, hfs⟩ := dsp_at (dspB_of_callsB (callsB_of' hok.heap)) hdj hmem hsite
            -- the callee a path's dispatch calls: entered at the entry its target cell holds
            have hpick : ∀ {σ : Val} {pre es : List Ev} {vs : List V} {f : String} {evs es' : List Ev},
                HonF img Cf s.fp σ → walk σ Cf.fn.body = .ret (pre ++ es) vs →
                es = evs ++ Ev.call f args rets :: es' → f ∈ fs → ∃ t ∈ pcs, Cf.X.entOk t f = true ∧
                  Rd img s.fp od = some (ofK (g ^ t)) := by
              intro σ pre es vs f evs es' hσ hb' hes hf
              obtain ⟨t, ht, hte⟩ := hfs f hf
              refine ⟨t, ht, hte, ?_⟩
              rw [← htg]
              exact honF_dsp hσ (pre := pre ++ evs) (by rw [hb', hes, List.append_assoc]) hsite (by omega) hte
            obtain ⟨f0, hf0, evs0, cs0, es0, hes0, -⟩ := hkD hwp (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) (hrd ▸ hσ0.gw.ok) hM0)
            obtain ⟨t, ht, hte, hrdt⟩ := hpick hσ0 hb hes0 hf0
            have hpt := hpcs t ht
            simp only [dspPc] at hpt
            split at hpt
            swap
            · cases hpt
            rename_i f1 hf1
            have hf10 : f1 = f0 := by
              have := entOk_spec hte
              rw [hf1, Option.some.injEq] at this
              exact this
            subst hf10
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpt
            obtain ⟨⟨hout, ht30⟩, hpt⟩ := hpt
            split at hpt
            swap
            · cases hpt
            rename_i G hG
            refine ⟨f1, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, ?_, ?_,
              fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht30, G, hG, hr30, hf1, hpt⟩
            · intro σ pre es vs rd hσ hb' hwp' hrw
              obtain ⟨f', hf', evs, cs, es', hes, hrest⟩ := hkD hwp' hrw
              obtain ⟨t', ht', hte', hrdt'⟩ := hpick hσ hb' hes hf'
              have htt : t' = t := by
                rw [hrdt, Option.some.injEq] at hrdt'
                have h30 : t' < 2 ^ 30 := by
                  have hp' := hpcs t' ht'
                  simp only [dspPc] at hp'
                  split at hp'
                  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
                    exact hp'.1.2
                  · cases hp'
                exact gpow_inj (by omega) (by omega) (pow_of_ofK hrdt'.symm)
              subst htt
              have hff : f' = f1 := by
                have := entOk_spec hte'
                rw [hf1, Option.some.injEq] at this
                exact this.symm
              subst hff
              exact ⟨evs, cs, es', hes, hrest⟩
            · have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hrdt) h0
              exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        rw [hhd i] at hpairs
        obtain ⟨hst'', hna, hnr'⟩ := siteAt_spec hsite
        rw [hna, hnr'] at hfit
        obtain ⟨hG0, hG1⟩ : 0 ∈ G.entry ∧ 1 ∈ G.entry := by
          unfold callOkC at hfit
          split at hfit
          · simp only [Bool.and_eq_true, List.contains_iff_mem] at hfit
            exact ⟨hfit.1.2, hfit.2⟩
          · simp only [Bool.and_eq_true] at hfit
            have hf := FitB.of_ok hfit.1
            exact ⟨List.contains_iff_mem.mp hf.ent0, List.contains_iff_mem.mp hf.ent1⟩
        -- the walk's split at the call, the callee frame
        have hsplit {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader} (hσ : HonF img Cf s.fp σ)
            (hrd : rd = img.read) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs) (hwp : walk σ pos = .ret es vs)
            (hh0 : ∀ e ∈ pre ++ es, e.Holds rd σ) (hM0 : ∀ e ∈ pre, EvM Cf.sigOf rd σ e) :=
          have hrw := hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) (hrd ▸ hσ.gw.ok) hM0
          call_split hκ hm sof h1 hsite hσ hb hrw (hkC hσ hb hwp hrw)
        obtain ⟨evs, cs, es', heq, hwp', hcs, hasin, hevM, hW', hreq, kfp, hfpE, hwsE, hk0, hk1⟩ :=
          hsplit hσ0 hrd hb hwp hh0 hM0
        have hcallE : Ev.call f args rets ∈ pre ++ es := by rw [heq]; simp
        obtain ⟨hpwR, hpwPR⟩ := callsB_spec (callsB_of hok.heap hbody hb hcallE) (body_callS hbody hb hcallE)
        have htop : Cf.fn.body.all topOk = true := (Bool.and_eq_true_iff.mp hbody).2
        have hexp : ∀ j, idxPowC Cf args j = true →
            IdxEx (slotW (args.map σ0)) j := fun j h ↦ by
          simpa using idxPowC_rep (ws := []) hok.pows htop hb hh0 hσ0.par hxw (hσ0.res hxw) h
        have hWs1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s1.mem x := by
          intro x hx
          rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · subst heq
            exact flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
              (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa
        cases hjo with
        | ret _ _ hr =>
          obtain ⟨c', hc'⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact absurd ⟨hc'.2.1, hc'.2.2⟩ hr01
        | «local» t' _ _ hpc'' hat'' =>
          exfalso
          have ht' : K.code.length ≤ t' := by
            by_contra hlt
            exact hout ⟨by rw [← hpe, hpc'']; omega, by rw [← hpe, hpc'', hlen]; omega⟩
          obtain ⟨cur, pend, h0', hh0'⟩ := hat''
          obtain ⟨rfl, rfl⟩ := preF_end hacc ht' h0'
          rcases hh0' with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
          · cases hA
          · cases hg'
        | halt _ hfpo hpcH hfpS =>
          have hmK : K.F.main = true := hok.fmain.trans (hfpM.symm.trans hfpo)
          exact k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.halt hmK (hpcH.trans hok.fhalt)
            (hfpS.trans (hm.fp.trans (hmainS hmK))))
        | tail e _ hpc'' _ _ _ _ _ =>
          exfalso
          exact hout ⟨by rw [← hpe, hpc''], by rw [← hpe, hpc'', hlen]; omega⟩
        | call G' t' _ htl hsig hentry hrr hcont =>
          rw [hpe, hG, Option.some.injEq] at hsig
          subst hsig
          -- the return offset
          have ht'r : st.r = K.F.entry + t' := by
            have h2 := hrr
            unfold retRegs at h2
            rw [show img.read (g ^ s'.fp * addressOfIndex 0) = Rd img s'.fp 0 from rfl, hk0] at h2
            simp only [Option.bind_some] at h2
            obtain ⟨fw, -, hfw'⟩ := Option.map_eq_some_iff.mp h2
            simp only [Registers.mk.injEq, limb_ofK] at hfw'
            rw [← hok.fentry]
            exact gpow_inj (by omega) (by omega) hfw'.1
          obtain ⟨-, hoo⟩ := fwdOff_spec hfo
          rw [hok.xentry, ht'r, show K.F.entry + t' - K.F.entry = t' by omega] at hoo
          subst hoo
          have hsigK : K.E.sigs.get s'.pc = some G := by rw [← hok.fsigs, hpe]; exact hG
          have hCtt : Ct s'.pc = hcAt img Cf G f := ct_callee hCt hsigK (by rw [hpe]; exact hentf)
          cases hl : Cf.hcs.lookup f
          case some p =>
            -- a callee whose contract is its heap signature's: no translation
            have hp : p = (args.length, rets.length) := by
              simp only [callOkC, hl, Bool.and_eq_true, decide_eq_true_eq] at hfit
              exact hfit.1.1
            subst hp
            have hCs : Ct s'.pc = some (heapCtr img (Cf.sigOf f) G args.length rets.length) := by
              rw [hCtt]; simp [hcAt, hl]
            refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_,
              hentry.w, ?_, ?_⟩)
            · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
              rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
            · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
              rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
            · -- its preconditions at its arguments' words, written before the call
              unfold Mode.PreAt
              rw [hCs]
              refine ⟨hentry.w, fun y hy ↦ ?_⟩
              obtain ⟨hgl, ⟨hrpre, hrpreR⟩, hrptr⟩ := callReq_pre (ders_of hok.heap hbody hb hcallE) hreq
              have hga : gargsW Cf.H σ0 f args = [] := by
                rw [← List.length_eq_zero_iff]
                simp only [gargsW, List.length_map, hgl]
                exact callChk_ghosts (callsB_chk (callsB_of' hok.heap) (body_callS hbody hb hcallE)) (by rw [hl]; rfl)
              rw [hga, List.append_nil] at hrpre hrpreR hrptr
              have hwsA : wsAt img s'.fp args.length = args.map σ0 := by
                rw [wsAt_take hwsE (by omega) (by simp), List.map_append, List.take_left' (by simp)]
              rw [hwsA] at hy
              have hW1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x :=
                fun x hx ↦ (hWs1 x hx).mono hle'
              rcases hy with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | hp
              · exact hW1 _ (hrpre c hc)
              · exact hW1 _ (hrpreR r hr _ hx)
              · rw [← hrd] at hp; exact hW1 _ (hrptr _ hp)
            · -- resumed once the callee guarantees its contract
              intro m hm0 hwf hu hfpE hfpC hP hT
              unfold Mode.PostAt at hP
              rw [hCs] at hP
              obtain ⟨hRet, hPost, hRM, hRV, hRE⟩ := hP
              refine ⟨by rw [Mode.stOf, hm.fp]; exact hxw, fun m' hm' ham' ↦ ?_⟩
              have hle0 : s.mem ≤ m' := Mem.le_trans hm.le (Mem.le_trans hle' (Mem.le_trans hm0 hm'))
              refine ⟨?_, fun o' ho' ↦ ?_, fun σ hσ ↦ ?_⟩
              · have := hcont { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }
                  ⟨ham', Prover.Exec.Dlog.ok_empty, Prover.Exec.Dlog.small_empty, hfpC⟩ rfl rfl
                  (Mem.le_trans hle' (Mem.le_trans hm0 hm')) (fun o' ho' ↦ written_mono hm' (hRet o' ho'))
                exact atF_mono (s := { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }) (Mem.le_refl _) rfl this
              · show m'.written (s1.fp + o') = true
                rw [hm.fp]; exact written_mono hle0 (hentw o' ho')
              · change HonF img Cf s1.fp σ at hσ
                rw [hm.fp] at hσ
                obtain ⟨pos2, pre2, es2, vs2, rd2, hrd2, hpos2, hb2, hwp2, hh2, hM2, hW2⟩ := hheap σ hσ
                rw [hpos, Option.some.injEq] at hpos2
                subst hpos2
                obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hevM2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
                  hsplit hσ hrd2 hb2 hwp2 hh2 hM2
                -- the callee's returned words, its contract's
                have hEv : EvM Cf.sigOf rd2 σ (.call f args rets) := by
                  have hwF : wsAt img s'.fp (args.length + rets.length) = (args ++ rets).map σ :=
                    wsAt_eq (by simp) hwsE2
                  have hwP : wsAt img s'.fp args.length = args.map σ := by
                    rw [wsAt_take hwsE2 (by omega) (by simp), List.map_append, List.take_left' (by simp)]
                  rw [hwF, hwP, List.map_append, List.drop_left' (by simp)] at hRM
                  rw [hwF] at hRV hRE
                  subst hrd2
                  exact ⟨hRM, by simpa using hRV, by simpa using hRE⟩
                refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hrd2, hat',
                  by simpa using hb2, hwp2', by simpa using hh2,
                  evM_app (evM_app hM2 hevM2) fun e he ↦ ?_, fun y hy ↦ ?_⟩
                · rcases List.mem_cons.mp he with rfl | he
                  · exact hEv
                  · exact evM_atoms _ e he
                refine resume_wrk hκ hs hm hle0 (Mem.le_trans hle' (Mem.le_trans hm0 hm')) e1 hpairs hσ hb2
                  hW2 hW2' hcs2 (fun hwe ↦ ?_) hy
                -- the callee's guarantees, its contract's
                subst hrd2
                refine (hPost y ?_).mono hm'
                rw [wsAt_eq (by simp) hwsE2]
                exact hwe
          -- a callee of a mode contract, through `fitB`
          have hCn : Ct s'.pc = none := by rw [hCtt]; simp [hcAt, hl]
          simp only [callOkC, hl, Bool.and_eq_true] at hfit
          obtain ⟨hfit, hpa⟩ := hfit
          have hf := FitB.of_ok hfit
          have hGself := hf.self
          have hhpostP := hf.postP
          have hhpostPR := hf.postPR
          have hhretM := hf.retM
          have hhpostQ := hf.postQ
          have hhpost := hf.post
          have hhpostR := hf.postR
          simp only [List.all_eq_true] at hhpostP hhpostPR hhretM hhpostQ hhpost
          replace hhpostR := allAnyPos_all hhpostR
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_,
            hentry.w, ?_, ?_⟩)
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
            rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
            rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
          · -- the callee's entry facts
            rw [Mode.preAt_none hCn]
            refine holds_entryAbs ?_ fun o ho ↦ ?_
            swap
            · -- its self cell (a loop's)
              have ho28 : o < 2 ^ 28 := by rw [ho] at hGself; simpa using hGself
              obtain ⟨hwo, hro⟩ := hentry.self o ho
              obtain ⟨u, hu⟩ := Mem.get_of_written hwo
              exact ⟨hwo, by rw [hu, rd_get hκ hf' ho28 hro hu]⟩
            exact entry_fitB hκ hf' (Mem.le_trans hm.le hle')
              (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e') hentry hwsE hk1 hG1 hentw hσ0
              hok.pows htop hb hh0 hrd hf hpa (callReq_pre (ders_of hok.heap hbody hb hcallE) hreq)
              (fun x hx ↦ (hWs1 x hx).mono hle')
              (fun q hq ↦ ⟨idxPowG_rep hok.pows htop hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwR q hq)).1,
                idxPowG_rep hok.pows htop hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwR q hq)).2⟩)
              (fun p hp ↦ ⟨idxPowG_rep hok.pows htop hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwPR p hp)).1,
                idxPowG_rep hok.pows htop hb hh0 hσ0.par hxw (hσ0.res hxw) (Bool.and_eq_true_iff.mp (hpwPR p hp)).2⟩)
              (hjtR s' (Mem.le_trans hm.le hle')) (fun p hp ↦ hTE G hsigK hentry.w p hp)
          · -- resumed once the callee guarantees its signature
            intro m hm0 hwf hu hfpE hfpC hP hT
            rw [Mode.postAt_none hCn] at hP
            obtain ⟨hR, hL, hLP⟩ := hP
            refine ⟨by rw [Mode.stOf, hm.fp]; exact hxw, fun m' hm' ham' ↦ ?_⟩
            have hle0 : s.mem ≤ m' := Mem.le_trans hm.le (Mem.le_trans hle' (Mem.le_trans hm0 hm'))
            refine ⟨?_, fun o' ho' ↦ ?_, fun σ hσ ↦ ?_⟩
            · have := hcont { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }
                ⟨ham', Prover.Exec.Dlog.ok_empty, Prover.Exec.Dlog.small_empty, hfpC⟩ rfl rfl
                (Mem.le_trans hle' (Mem.le_trans hm0 hm')) (fun o' ho' ↦ written_mono hm' (hR.1 o' ho'))
              exact atF_mono (s := { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }) (Mem.le_refl _) rfl this
            · show m'.written (s1.fp + o') = true
              rw [hm.fp]; exact written_mono hle0 (hentw o' ho')
            · change HonF img Cf s1.fp σ at hσ
              rw [hm.fp] at hσ
              obtain ⟨pos2, pre2, es2, vs2, rd2, hrd2, hpos2, hb2, hwp2, hh2, hM2, hW2⟩ := hheap σ hσ
              rw [hpos, Option.some.injEq] at hpos2
              subst hpos2
              obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hevM2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
                hsplit hσ hrd2 hb2 hwp2 hh2 hM2
              have hEv : EvM Cf.sigOf rd2 σ (.call f args rets) :=
                evM_mode hκ (callsB_chk (callsB_of' hok.heap) (body_callS (r := rets) hbody hb2 (by simp))) hl
                  hhretM (Mode.RetHolds.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp) hm' rfl hR) ham'
                  hf'.fp hwsE2
              refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hrd2, hat',
                by simpa using hb2, hwp2', by simpa using hh2,
                evM_app (evM_app hM2 hevM2) fun e he ↦ ?_, fun y hy ↦ ?_⟩
              · rcases List.mem_cons.mp he with rfl | he
                · exact hEv
                · exact evM_atoms _ e he
              refine resume_wrk hκ hs hm hle0 (Mem.le_trans hle' (Mem.le_trans hm0 hm')) e1 hpairs hσ hb2
                hW2 hW2' hcs2 (fun hwe ↦ ?_) hy
              -- the callee's guarantees
              exact post_wrk hκ ham' hm' hf'.fp hwsE2 hrd2 hR hL hLP hhpost
                (fun q hq ↦ Bool.or_eq_true_iff.mpr (.inl (hhpostR q hq))) hhpostP hhpostPR hhpostQ hwe

end

end LeanVM.Guest.CoreMode
