/-
  LeanVM.Guest.CoreMode.Fam.ResTA

  `TermNodeA` from the loops' runs: at every entered honest instance of a loop helper, on the
  aligned allocator, its counter is below its end on the reference.
-/

module

public import LeanVM.Guest.CoreMode.Fam.LoopTreeA
public import LeanVM.Guest.CoreMode.Fam.TermOk
public import LeanVM.Guest.EndExecAssemble
public import LeanVM.Guest.B2C.B2Final

/-!
# The termination facts of the entered instances, aligned

The bus era's `Fam/ResT.lean` on Hotwire's allocator. Every function of the guest passes
`Res.termChk` (`Gen/LoopCheck`'s `Res.termAll`, `scripts/core-mode/loopcheck.py`), so the program is
`Res.ProgOk` (`progOk_of_termAll`). On the honest tree every instance of a loop helper has as counter a power
`g^e`, `e` and its subtree's words at most the tree's words plus one (`Res.instsA_ctr`), and its run
reaches its end `m ≥ 1` iterations later, `m` at most its subtree's words (`Res.chain`): the end is
`g^(e + m)`, no wrap since the tree's words are at most the aligned words (`Res.total_le_wordsA`),
within `2^28`. Its frame holds both as its first two arguments (`B2C.read_argsL`), or the end is a
constant (`endOfFn`).

`TermOk K`: a certificate has no termination fact, or is function `j`'s, a loop helper, with the one
fact `[2] < end` its shape names (`endIdx`). The layout is b2c's (`layB al`: `B2C.fs`, `B2C.H`,
`B2C.C`, `B2C.cert`), and the alignment enters each function at its compiled entry (`EntIdx`), so an
instance entered at `K`'s entry is function `j`'s (`fnOf_entry_inj`). `termNodeA_of`: `TermNodeA`
from `TermOk` of each certificate; `termNodeA_assembled`: at the assembled certificates carrying
termination facts (`EndExec.termOk_all`), the routed ones' `TermOk` decided in `core_cert%`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (termChk endOfFn bodyOf entL ProgOk CtrOk endVal)
open LeanVM.Guest.Bridge (FnAl entOf)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The loops' check -/

theorem termChk_find (hA : RangeOk (fun _ fn => termChk fn) 0 coreProgram.length) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) : termChk fn = true := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hf)
  exact hA.all hj

theorem endOfFn_tail {fn : Fn} {e : Option ℕ} (h : endOfFn fn = some e) : (loopTail fn e).isSome = true := by
  unfold endOfFn at h
  split_ifs at h with h0
  · cases h; exact h0
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.find?_some (p := fun e ↦ (loopTail fn (some e)).isSome) hx

theorem endOfFn_lt {fn : Fn} {N : ℕ} (h : endOfFn fn = some (some N)) : N < 256 := by
  unfold endOfFn at h
  split_ifs at h
  · cases h
  · obtain ⟨x, hx, hxN⟩ := Option.map_eq_some_iff.mp h
    cases hxN
    exact List.mem_range.mp (List.mem_of_find?_eq_some hx)

/-- **The guest passes the loops' check**, from the kernel's check of every function. -/
theorem progOk_of_termAll (hA : RangeOk (fun _ fn => termChk fn) 0 coreProgram.length) : ProgOk coreProgram where
  loop f fn hf hl := by
    have h := termChk_find hA hf
    have hn := fn_name_of_find hf
    simp only [termChk, bodyOf, hl, Bool.not_true, Bool.false_or, ↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h2
    exact ⟨hn ▸ h1, e, he, loopShape_of (endOfFn_tail he) (Res.entL_noRet _ h3), h3⟩
  body f fn hf hl := by
    have h := termChk_find hA hf
    simp only [termChk, bodyOf, hl, Bool.not_false, Bool.true_or, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte] at h
    exact h

/-! ## On the aligned honest tree -/

theorem ridx_fr {M : ℕ → E} {fp o e : ℕ} (h : M (fp + o) = ofK (addressOfIndex e)) (he : e < 2 ^ 62) :
    Mode.RIdx M fp (.ex (.fr o) 0) e :=
  ⟨_, e, h, rfl, he, rfl⟩

/-- **b2c's aligned layout**, at the per-callee alignment flag `al`. -/
noncomputable def layB (al : String → Bool) : Lay := ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩

/-- **The alignment enters each function at its compiled entry.** -/
def EntIdx (A : String → FnAl) : Prop :=
  ∀ f j, B2C.idxOf f = some j → entOf A f = (fnOf j).entryPc

/-- **`TermNodeA` from each certificate's `TermOk`.** -/
theorem termNodeA_of {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}
    {Ks : List Mode.Cert} (hP : ProgOk coreProgram) (hE : EntIdx A)
    (hRH : ∀ r, R r → RefH (layB al) (D r) r) (h : ∀ K ∈ Ks, TermOk K) : TermNodeA (layB al) D A R Ks := by
  intro r hR0 hr K hK I hI ⟨f, σ, bufs, kids, hIt⟩ hent p hp _
  have hR := hRH r hR0
  rcases h K hK with h0 | ⟨j, hj1, hj2, hje, hjl, hterm⟩
  · rw [h0] at hp; cases hp
  rw [hterm, List.mem_singleton] at hp
  subst hp
  obtain ⟨rd, hH, hXh⟩ := hR.honest
  have hκ : r.κ ≤ 28 := hr.log
  -- the instance's function is `j`'s, a loop helper of its shape
  obtain ⟨args, rets, hv⟩ : ∃ args rets, I.t.Valid coreProgram rd args rets := by
    rcases instsA_good (D r).T _ r.hdr hH.valid I hI with h' | ⟨_, _, h'⟩
    · exact h'
    · rw [hIt] at h'; cases h'
  rw [hIt] at hv
  have hv' := hv
  unfold Tree.Valid at hv'
  obtain ⟨fn, hf, -⟩ := hv'
  obtain ⟨j', hj'⟩ := B2C.idxOf_of_find hf
  obtain ⟨i, rfl, hi, -, hfi, hc, -, -, h1, h2⟩ := B2C.fn_of_idx hj'
  obtain rfl : fn = coreProgram[i] := Option.some.inj (hf.symm.trans hfi)
  have hjj : j = i + 1 := by
    refine fnOf_entry_inj hj2 h2 ?_
    rw [hje, ← hent, hIt]
    exact hE f (i + 1) hj'
  subst hjj
  rw [hc] at hjl
  obtain ⟨-, e, he, hs, -⟩ := hP.loop f _ hfi hjl
  rw [hc, he, Option.getD_some]
  -- the counter and the end
  have hfs : ∀ g, 1 ≤ B2C.fs g := fun g ↦ le_trans (by norm_num) (B2C.two_le_fs g)
  have hT : (D r).T.total B2C.fs ≤ 2 ^ 28 := by
    have h3 := Res.total_le_wordsA (fs := B2C.fs) (lp := coreProgram.loop) (al := al) (D r).T
    have h4 := le_two_pow_logMem ((D r).T.wordsA B2C.fs coreProgram.loop al)
    have h5 : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
    have h6 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h5
    omega
  have hroot : CtrOk coreProgram B2C.fs ((D r).T.total B2C.fs + 1) (D r).T := by
    intro g σ' _ _ fn' hT' hg hl
    have := (hP.loop g fn' hg hl).1
    have hn := hR.name
    rw [hT'] at hn
    simp only [Tree.name] at hn
    subst hn
    exact absurd this (by decide)
  obtain ⟨p0, prest, e1, hps, hσ0, he1⟩ := Res.instsA_ctr hfs hP (D r).T _ r.hdr hH.valid le_rfl hroot I hI
    f σ bufs kids _ hIt hfi hjl
  obtain ⟨m, p0', prest', hps', hm1, hm2, hm⟩ := Res.chain hfs _ le_rfl hv hfi hs
  rw [hps] at hps'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
  rw [← hIt] at hm2
  have hfp := inst_fp_lt hR hr hI
  -- the frame's arguments
  have hS := B2C.shareOk_of h1 h2
  have hchk := End.winOk_of h1 h2
  have hC := B2C.chainApart_of (B2C.Cplw.cplOk_all _ h1 h2) hchk (B2C.Chained.chainOk_all _ h1 h2)
  have hgood : (∃ σJ bufs kids es vs, I.t = .node f σJ bufs kids ∧ walk σJ (coreOf (i + 1)).body = .ret es vs ∧
      ∀ e ∈ es, e.Holds rd σJ) ∨ ∃ σJ, I.t = .phantom f σJ := by
    left
    have hv2 := hv
    unfold Tree.Valid at hv2
    obtain ⟨fn2, hf2, -, es, vs, hw, -, hh, -⟩ := hv2
    obtain rfl : fn2 = coreProgram[i] := Option.some.inj (hf2.symm.trans hfi)
    exact ⟨σ, bufs, kids, es, vs, hIt, by rw [hc]; exact hw, hh⟩
  have harg : ∀ k (hk : k < (coreOf (i + 1)).params.length), k < 2 →
      refMem r.img (I.fp + (2 + k)) = σ (coreOf (i + 1)).params[k] := fun k hk hk2 ↦ by
    have := B2C.read_argsL hH.toHonestA hXh.covers hS hC hchk hI hj' hgood k hk
    rw [hIt] at this
    have h' : r.img.read (addressOfIndex (I.fp + (2 + k))) = some (σ (coreOf (i + 1)).params[k]) := by
      rw [hR.img]; exact this
    exact ((refRd_img hκ r.img) _ _ (by unfold maxCells at hfp; omega) h').2
  rw [hc] at harg
  have hp0 := harg 0 (by rw [hps]; simp) (by omega)
  simp only [hps, List.getElem_cons_zero, Nat.add_zero] at hp0
  have hbig : e1 + m ≤ 2 ^ 28 + 1 := by omega
  refine ⟨e1, e1 + m, ridx_fr (o := 2) (by rw [hp0, hσ0]) (by omega), ?_, by omega⟩
  cases e with
  | none =>
    cases prest with
    | nil =>
      simp only [endVal, hps] at hm
      rw [hσ0, Res.ofK_gpow_add] at hm
      exact absurd hm (Mode.ofK_gpow_ne_zero _)
    | cons p1 _ =>
      have hp1 := harg 1 (by rw [hps]; simp) (by omega)
      simp only [hps, List.getElem_cons_succ, List.getElem_cons_zero] at hp1
      simp only [endVal, hps] at hm
      refine ridx_fr (o := 3) ?_ (by omega)
      rw [hp1, ← hm, hσ0, Res.ofK_gpow_add]
  | some N =>
    have hN := endOfFn_lt he
    simp only [endVal] at hm
    rw [hσ0, Res.ofK_gpow_add] at hm
    have := gpow_inj (by omega) (by omega) (ofK_injective hm)
    show e1 + m = N
    exact this

/-- **`TermNodeA` at the assembled certificates carrying termination facts.** -/
theorem termNodeA_assembled {tab : List CoreMode.HcEnt} {ls : List (List (CertE tab))} {offs : List Mode.Sig}
    {offK : Mode.Sig → Mode.Cert} {Toff : List CoreMode.CFun} (hoff : OffOk ls offs offK Toff)
    {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop} (hP : ProgOk coreProgram)
    (hE : EntIdx A) (hRH : ∀ r, R r → RefH (layB al) (D r) r) :
    TermNodeA (layB al) D A R ((certsOf ls offs offK).filter hasTerm) :=
  termNodeA_of hP hE hRH fun K hK ↦ termOk_all hoff K (List.mem_filter.1 hK).1

end

end LeanVM.Guest.EndExec
