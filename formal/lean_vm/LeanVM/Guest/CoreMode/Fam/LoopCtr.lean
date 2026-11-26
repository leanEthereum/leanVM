/-
  LeanVM.Guest.CoreMode.Fam.LoopCtr

  A loop helper at an honest instance: its counter below its bound, and a tail call its own last call,
  the counter stepped, the rest of its parameters and its header kept.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResA
public import LeanVM.Guest.EndExecW

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf fn_of_idx kidHdr)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

variable {r : Ref}

/-- **A loop's counter lies below its bound** at an honest instance: `g^j`, `j < n`, the bound `g^n`. -/
theorem loop_ctr_lt (hr : r.Ok) {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node f σ bufs kids)
    {fn : Fn} (hf : coreProgram.find? f = some fn) (hl : fn.loop = true) (he : Res.endOfFn fn = some none)
    {rest : List V} (hps : fn.params = .n 0 :: .n 1 :: rest) {n : ℕ} (h1 : σ (.n 1) = gen ^ n) (hn : n < 34) :
    ∃ j < n, σ (.n 0) = gen ^ j := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  have hfs : ∀ g, 1 ≤ B2C.fs g := Res.fs_pos
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
  simp only [Res.endVal, hps, h1] at hm
  rw [hσ0, Res.ofK_gpow_add, ← Value.gen_pow_eq_ofK] at hm
  have hT : r.T.total B2C.fs ≤ 2 ^ 28 := (le_two_pow_logMem _).trans (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [hJt] at hb
  have := Value.gen_pow_inj (by omega) (by omega) hm
  exact ⟨e1, by omega, by rw [hσ0, Value.gen_pow_eq_ofK]⟩

/-- **A loop helper's tail call**: the last call of its path, the counter one step on, the rest of its
parameters kept. -/
theorem loop_tail {rd : Reader} {fI : String} {fnI : Fn} (hfI : coreProgram.find? fI = some fnI)
    (hl : fnI.loop = true) (hnc : fI ∉ Stmt.blockCallees (loopBody fnI)) {σI : Val} {es : List Ev} {vs : List V}
    (hw : walk σI fnI.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σI) {i : ℕ} {c : Call}
    (hci : (calls es)[i]? = some c) (hcf : c.f = fI) :
    ∃ p0 prest i0, fnI.params = p0 :: prest ∧ c.args = i0 :: prest ∧
      σI i0 = σI p0 * ofK (addressOfIndex 1) ∧ i + 1 = (calls es).length := by
  obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ _ hfI hl
  obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, -⟩ := Res.loop_path hsh hw hh
  subst hes
  have hnm : fnI.name = fI := Memory.fn_name_of_find hfI
  rw [Res.loop_calls, hnm] at hci ⊢
  have hi : i = (calls es1).length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rw [List.getElem?_append_left hlt] at hci
      have hc1 := walk_callees (σ := σI) (loopBody fnI) (c := c) (by rw [hw1]; exact List.mem_of_getElem? hci)
      rw [hcf] at hc1
      exact hnc hc1
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
      cases hci
  subst hi
  rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
  simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
  subst hci
  exact ⟨p0, prest, i0, hps, rfl, hi0, by simp⟩

/-- **A loop helper's tail call keeps its header** (`B2C.H`), as `loop_tail`. -/
theorem loop_tail_hdr {rd : Reader} {fI : String} {fnI : Fn} (hfI : coreProgram.find? fI = some fnI)
    (hl : fnI.loop = true) (hnc : fI ∉ Stmt.blockCallees (loopBody fnI)) {I : Inst} {σI : Val} {bufsI : List ℕ}
    {kidsI : List Tree} (hIt : I.t = .node fI σI bufsI kidsI) {es : List Ev} {vs : List V}
    (hw : walk σI fnI.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σI) {i : ℕ} {c : Call}
    (hci : (calls es)[i]? = some c) (hcf : c.f = fI) :
    ∃ i0 p0 prest, fnI.params = p0 :: prest ∧ c.args = i0 :: prest ∧ σI i0 = σI p0 * ofK (addressOfIndex 1) ∧
      B2C.H I i = I.hdr := by
  obtain ⟨p0, prest, i0, hps, hargs, hi0, hlen⟩ := loop_tail hfI hl hnc hw hh hci hcf
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
  obtain ⟨i2, hji2, hi2, -, hf2, hc2, -⟩ := fn_of_idx hj
  have hcj := hc2.trans (Option.some.inj (hf2.symm.trans hfI))
  have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) i
  unfold kidHdr at hH
  rw [hci] at hH
  dsimp only at hH
  rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl, hlen⟩)] at hH
  exact ⟨i0, p0, prest, hps, hargs, hi0, hH⟩

end

end LeanVM.Guest.EndExec
