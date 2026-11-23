/-
  LeanVM.Guest.CoreMode.Fam.ResT

  `TermNode` from the loops' runs: at every entered instance of a loop helper, its counter is below
  its end on the reference.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Res
public import LeanVM.Guest.CoreMode.Fam.LoopTree
public import LeanVM.Guest.CoreMode.Gen.LoopCheck
public import LeanVM.Guest.EndExecEntry
public import LeanVM.Guest.CoreMode.Fam.RefAll

/-!
# The termination facts of the entered instances

Every function of the guest passes `Res.termChk` (`Res.termAll`), so the program is `Res.ProgOk`
(`progOk_guest`). On the honest tree every instance of a loop helper has as counter a power `g^e`,
`e` and its subtree's words at most the tree's words plus one (`Res.insts_ctr`), and its run reaches
its end `m ≥ 1` iterations later, `m` at most its subtree's words (`Res.chain`): the end is
`g^(e + m)`, no wrap, so the counter's exponent is below the end's. Its frame holds both as its first
two arguments (`read_argsL`), or the end is a constant (`endOfFn`).

`TermOk K`: a certificate has no termination fact, or is function `j`'s, a loop helper, with the one
fact `[2] < end` its shape names (`endIdx`). `termNode_of`: `TermNode` from `TermOk` of each
certificate. Compiled functions' entries are distinct (`fnOf_entry_inj`), so an instance at `K`'s
entry is function `j`'s.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (termChk endOfFn bodyOf entL ProgOk CtrOk endVal)
open LeanVM.Guest.B2C (idxOf entryOf fn_of_idx idxOf_of_find shareOk_of chainApart_of read_argsL)
open LeanVM.Prover.Exec

@[expose] public section

theorem termChk_find {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) : termChk fn = true := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hf)
  exact Res.termAll.all hj

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

/-- **The guest passes the loops' check.** -/
theorem progOk_guest : ProgOk coreProgram where
  loop f fn hf hl := by
    have h := termChk_find hf
    have hn := fn_name_of_find hf
    simp only [termChk, bodyOf, hl, Bool.not_true, Bool.false_or, ↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h2
    exact ⟨hn ▸ h1, e, he, loopShape_of (endOfFn_tail he) (Res.entL_noRet _ h3), h3⟩
  body f fn hf hl := by
    have h := termChk_find hf
    simp only [termChk, bodyOf, hl, Bool.not_false, Bool.true_or, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte] at h
    exact h

/-! ## Distinct entries -/

/-! ## The certificates' termination facts -/

/-- A loop helper's end as an exponent: its second argument's (cell `3`), or the constant. -/
def endIdx : Option ℕ → Mode.Idx
  | none => .ex (.fr 3) 0
  | some N => .num N

/-- **A certificate's termination facts**: none, or it is function `j`'s, a loop helper, with the
one fact `[2] < end` of its shape's end. -/
def TermOk (K : Mode.Cert) : Prop :=
  K.F.sig.term = [] ∨ ∃ j, 1 ≤ j ∧ j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ (coreOf j).loop = true ∧
    K.F.sig.term = [(.ex (.fr 2) 0, endIdx ((endOfFn (coreOf j)).getD none))]

/-- `TermOk` at function `j`, decided. -/
noncomputable def termOkB (K : Mode.Cert) (j : ℕ) : Bool :=
  K.F.sig.term.isEmpty || (decide (1 ≤ j) && decide (j < nFns) && (fnOf j).entryPc == K.F.entry &&
    (coreOf j).loop && decide (K.F.sig.term = [(.ex (.fr 2) 0, endIdx ((endOfFn (coreOf j)).getD none))]))

theorem termOk_of {K : Mode.Cert} {j : ℕ} (h : termOkB K j = true) : TermOk K := by
  simp only [termOkB, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, h1, h2, h3, h4, h5⟩

theorem ridx_fr {M : ℕ → E} {fp o e : ℕ} (h : M (fp + o) = ofK (addressOfIndex e)) (he : e < 2 ^ 62) :
    Mode.RIdx M fp (.ex (.fr o) 0) e :=
  ⟨_, e, h, rfl, he, rfl⟩

/-- **`TermNode` from each certificate's `TermOk`.** -/
theorem termNode_of {Ks : List Mode.Cert} (h : ∀ K ∈ Ks, TermOk K) : TermNode Ks := by
  intro r hr K hK I hI ⟨f, σ, bufs, kids, hIt⟩ hent p hp _
  rcases h K hK with h0 | ⟨j, hj1, hj2, hje, hjl, hterm⟩
  · rw [h0] at hp; cases hp
  rw [hterm, List.mem_singleton] at hp
  subst hp
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  -- the instance's function is `j`'s, a loop helper of its shape
  obtain ⟨args, rets, hv⟩ : ∃ args rets, I.t.Valid coreProgram rd args rets := by
    rcases insts_good r.T _ r.hdr hH.valid I hI with h' | ⟨_, _, h'⟩
    · exact h'
    · rw [hIt] at h'; cases h'
  rw [hIt] at hv
  have hv' := hv
  unfold Tree.Valid at hv'
  obtain ⟨fn, hf, -⟩ := hv'
  obtain ⟨j', hj'⟩ := idxOf_of_find hf
  obtain ⟨i, rfl, hi, -, hfi, hc, -, -, h1, h2⟩ := fn_of_idx hj'
  obtain rfl : fn = coreProgram[i] := Option.some.inj (hf.symm.trans hfi)
  have hjj : j = i + 1 := by
    refine fnOf_entry_inj hj2 h2 ?_
    rw [hje, ← hent, hIt]
    simp only [Tree.name, entryOf, hj']
  subst hjj
  rw [hc] at hjl hterm
  obtain ⟨-, e, he, hs, -⟩ := progOk_guest.loop f _ hf hjl
  rw [hc, he, Option.getD_some]
  -- the counter and the end
  have hT : r.T.total B2C.fs ≤ 2 ^ 28 :=
    (le_two_pow_logMem _).trans (Nat.pow_le_pow_right (by norm_num) hκ)
  have hfs : ∀ g, 1 ≤ B2C.fs g := Res.fs_pos
  have hroot : CtrOk coreProgram B2C.fs (r.T.total B2C.fs + 1) r.T := by
    intro g σ' _ _ fn' hT' hg hl
    have := (progOk_guest.loop g fn' hg hl).1
    have hn := hr.name
    rw [hT'] at hn
    simp only [Tree.name] at hn
    subst hn
    exact absurd this (by decide)
  obtain ⟨p0, prest, e1, hps, hσ0, he1⟩ := Res.insts_ctr hfs progOk_guest r.T _ r.hdr hH.valid le_rfl hroot I hI
    f σ bufs kids _ hIt hf hjl
  obtain ⟨m, p0', prest', hps', hm1, hm2, hm⟩ := Res.chain hfs _ le_rfl hv hf hs
  rw [hps] at hps'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
  rw [← hIt] at hm2
  have hfp := inst_fp_lt hr hI
  -- the frame's arguments
  have hS := shareOk_of h1 h2
  have hC := chainApart_of (B2C.Cplw.cplOk_all _ h1 h2) (End.winOk_of h1 h2) (B2C.Chained.chainOk_all _ h1 h2)
  have hchk := End.winOk_of h1 h2
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
    have := read_argsL hH.toHonest hXh.covers hS hC hchk hI hj' hgood k hk
    rw [hIt] at this
    exact ((refRd_img hκ r.img) _ _ (by unfold maxCells at hfp; omega) this).2
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
