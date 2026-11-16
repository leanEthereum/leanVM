/-
  LeanVM.Guest.EndExecRVtP

  `verify_tables`' precondition (`B1.Tables.TablesPre`) at its honest instances (`VtPQ`), carried down
  from `verify_sub`'s front.
-/

module

public import LeanVM.Guest.EndExecRVt

/-!
# `verify_tables`' precondition

`VtPQ r J`: at an instance of `verify_tables`, its arguments satisfy `TablesPre`, which `verify_sub`
establishes before the call (`VsFront.hTP`). `vtPQ_all`: at every honest instance, by `Res.insts_down`,
as `vtQ_all`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_tables`' precondition** at an instance. -/
def VtPQ (r : Ref) (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node "verify_tables" σ bufs kids →
    ∃ pi logMem weights point values, Tables.TablesPre pi logMem weights point values r.img.read
      ((List.range 21).map fun k ↦ σ (.n k))

end

public section

variable {r : Ref}

theorem vtPQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (VtPQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  have hcf : c.f = "verify_tables" := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  -- the callee's body
  obtain ⟨hpar, hbJ⟩ := Res.holds_of_valid hfs hJv VerifySub.find_vt
  obtain ⟨-, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) VerifySub.find_vt hbJ
  -- the caller is `verify_sub`
  have hmem : ("verify_tables", name% «verify_sub») ∈ Res.termCallers := by decide
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_tables» := Option.some.inj (hfI.symm.trans VerifySub.find_vt)
      rw [vt_not_loop] at hl; cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  -- its call of `verify_tables`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vt_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨ha, -⟩ := hs
  rw [ha, vt_params] at hpar
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab) (by decide) rfl
    (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨hexp, hwin⟩ := hQ
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  refine ⟨F.pi, F.logMem, F.weights, F.r.2.1, F.r.2.2, ?_⟩
  have hl : (List.range 21).map (fun k ↦ σ (.n k)) = vtArgsV.map σI := by
    rw [← hpar, List.map_map]
    rfl
  rw [hl]
  exact F.hTP

/-- **`verify_tables`' precondition at every honest instance.** -/
theorem vtPQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VtPQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (vtPQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro σ bufs kids hJt
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  exact absurd hn (by decide)


/-- **The exponent facts but `check_opening_terminal`'s at every honest instance**: `verify_tables`'
`g_bus_mu = g^|point|`, `|point| < 33`, and `dims_g`'s first word `g^logMem`, `logMem ≤ 32`. -/
theorem expQv_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ExpQv r J := by
  intro J hJ f σ bufs kids hJt fn hf c hc hcf hn v hv
  simp only [Res.expFacts, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl) | ⟨k, -, rfl⟩) | rfl | rfl
  · exact absurd rfl hn
  · exact absurd rfl hn
  · exact absurd rfl hn
  all_goals
    subst hcf
    obtain rfl : fn = fn% «verify_tables» := Option.some.inj (hf.symm.trans VerifySub.find_vt)
    rw [vt_params] at hv
    simp only [List.getElem?_map, List.getElem?_range (by decide : (9 : ℕ) < 21),
      List.getElem?_range (by decide : (10 : ℕ) < 21), Option.map_some, Option.some.injEq] at hv
    subst hv
    obtain ⟨pi, lm, w, pt, vals, hP⟩ := vtPQ_all hr J hJ σ bufs kids hJt
    rw [show (List.range 21).map (fun k ↦ σ (.n k)) = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
      σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13),
      σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18), σ (.n 19), σ (.n 20)] from rfl] at hP
    obtain ⟨-, -, hgmu, hlen, -, hlm, ⟨ds, -, hds⟩, -⟩ := hP
  · exact ⟨pt.length, hlen, hgmu⟩
  · exact ⟨lm, show lm < 33 by omega, hds 0 (by simp)⟩

end

end LeanVM.Guest.EndExec
