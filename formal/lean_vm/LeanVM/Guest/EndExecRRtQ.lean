/-
  LeanVM.Guest.EndExecRRtQ

  The roots' tree's blob count and gap at its arms' instances (`RtQ`), carried down from
  `da_verify`.
-/

module

public import LeanVM.Guest.EndExecRCq
public import LeanVM.Guest.B1.Da.VerifyFront

/-!
# The roots' tree's arguments

`RtQ J`: at an instance of `da_roots_tree__L{k}`, its blob count and gap are `g^a` and `g^b`,
`a + b = 2^k`. `rtQ_all`: at every honest instance, by `Res.insts_down`. The arms' only caller is
`da_verify` (`Res.termCallers_all`), a flat body whose calls are `dvCallsS`, its dispatch calling
arm `log [2]` on `[17, 1, 8]`; with the exponent table at its argument (`carryQ_all`), `dv_front`
makes `[2] = g^L`, `[1] = g^r` and `[8] = g^(2^L - r)`, `r ≤ 2^L`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da (rtName rtBody dvP dvCallsS dv_callsSF dv_body dv_flat dv_front)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The roots' tree's arguments as `da_verify` hands them: the blob count `g^a` and the gap `g^b`,
`a + b = 2^k`. -/
def RtH (k : ℕ) : List E → Prop
  | [_, nb, gap] => ∃ a b, a + b = 2 ^ k ∧ nb = gen ^ a ∧ gap = gen ^ b
  | _ => False

/-- **The roots' tree's arguments at its arms' instances.** -/
def RtQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ k < 11, f = rtName k → ∀ fn,
    coreProgram.find? f = some fn → RtH k (fn.params.map σ)

end

public section

theorem dv_dispSmall : dvP.all dispSmall = true := by decide +kernel

theorem rt_other_names : (List.range 11).all (fun k ↦ rtName k != "da_row_shape" && rtName k != "da_vector" &&
    rtName k != "da_weights" && rtName k != name% «da_verify_loop0» && rtName k != "main") = true := by
  decide +kernel

theorem rt_inj : (List.range 11).all (fun a ↦ (List.range 11).all fun b ↦ rtName a != rtName b || a == b) = true := by
  decide +kernel

theorem rt_callers : (List.range 11).all (fun k ↦ Res.termCallers.contains (rtName k, name% «da_verify»)) = true := by
  decide +kernel

theorem rt_not_loop {k : ℕ} (hk : k < 11) {fn : Fn} (hf : coreProgram.find? (rtName k) = some fn) :
    fn.loop = false := by
  obtain ⟨hf', hok⟩ := Da.rt_find hk
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  simp only [Da.rtOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  unfold Core.Fn.loop
  rw [stmtsEqb_sound hok.2]
  simp [rtBody]

variable {r : Ref}

/-- **The roots' tree's arguments pass down from `da_verify`.** -/
theorem rtQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) RtQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    f σ bufs kids hJt k hk11 hf fn hfn
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hoth := List.all_eq_true.mp rt_other_names k (List.mem_range.mpr hk11)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hoth
  -- the caller is `da_verify`
  have hmem : (rtName k, name% «da_verify») ∈ Res.termCallers := by
    have := List.all_eq_true.mp rt_callers k (List.mem_range.mpr hk11)
    simpa using this
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf, hf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hdv : fI = name% «da_verify» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      rw [rt_not_loop hk11 hfI] at hl; cases hl
  subst hdv
  obtain rfl : fnI = fn% «da_verify» := Option.some.inj (hfI.symm.trans Da.find_da_verify)
  -- its calls: `dvCallsS`
  rw [dv_body] at hw
  have hD := walk_flat_disp dv_flat dv_dispSmall hw
  rw [walk_flat σI _ dvP dv_flat hD] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  rw [(flat_parts σI dvP dv_flat).2.2.2.1, dv_callsSF] at hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  simp only [dvCallsS, List.mem_cons, List.not_mem_nil, or_false] at ht
  rw [hf] at hcf
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact absurd hcf.symm hoth.1.1.1.1
  · exact absurd hcf.symm hoth.1.1.1.2
  · exact absurd hcf.symm hoth.1.1.2
  · exact absurd hcf.symm hoth.1.2
  -- the body at its own valuation
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «da_verify», 0, .tab) (by decide) rfl
    (.n 0) rfl
  obtain ⟨hexp, -⟩ := hQ
  obtain ⟨L, r', hL, hrL, h1, h2, h8⟩ :=
    dv_front (fun _ _ _ h ↦ Res.KidRel.rel h) (ref_memOk hr) hb (fun j hj ↦ hexp.1 j hj)
  -- the arm is `L`
  have hlog : logG (σI (.n 2)) = L := by rw [h2]; exact logG_gen_pow (by omega)
  simp only [Memory.mkCall, hlog] at hcf
  have hinj := List.all_eq_true.mp (List.all_eq_true.mp rt_inj L (List.mem_range.mpr (by omega))) k
    (List.mem_range.mpr hk11)
  rw [hcf] at hinj
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hinj
  subst hinj
  -- the arguments
  have hJv := hval rfl
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  rw [hpar]
  simp only [Memory.mkCall, List.map_cons, List.map_nil, RtH]
  refine ⟨r', _, ?_, h1, h8⟩
  omega

/-- **The roots' tree's arguments at every honest instance.** -/
theorem rtQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, RtQ J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (rtQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro f σ bufs kids hJt k hk hf
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  subst hn
  have hoth := List.all_eq_true.mp rt_other_names k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hoth
  exact absurd hf.symm hoth.2

end

end LeanVM.Guest.EndExec
