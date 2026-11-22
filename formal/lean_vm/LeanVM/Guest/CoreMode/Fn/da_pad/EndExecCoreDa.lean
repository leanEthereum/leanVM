/-
  LeanVM.Guest.CoreMode.Fn.da_pad.EndExecCoreDa

  `da_pad`'s gap at its honest instances (`DaPadQ`): the `g^(DA_MAX_ROWS - n)` `da_verify` hands it, `n ≥ 1` by
  `da_padding`'s meaning, carried down the honest tree from its one caller.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.ResA
public import LeanVM.Guest.CoreMode.Fam.RefAll
public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Da.Padding
public import LeanVM.Guest.B1.Da.PadAt
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.B1.Main.Loops
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_verify»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam resOk idxC baseC vw)

@[expose] public section

/-! ## `da_pad`'s gap -/

/-- **`da_pad`'s gap at an instance**: `g^k`, `k < DA_MAX_ROWS`. -/
def DaPadQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «da_pad» σ bufs kids → ∃ k, k < guest_const% DA_MAX_ROWS ∧
    σ (.n (val% «da_pad» "gap_g")) = Protocol.Verifier.gen ^ k

/-- `da_verify` calls `da_pad` at its rows' roots, its blob count and its gap. -/
theorem dv_pad_sites : Res.sitesB (fun f args rets ↦ f != name% «da_pad» ||
    (args == [.n (val% «da_verify» "roots"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "gap_g")] && rets == [])) (fn% «da_verify»).body = true := by
  decide +kernel

theorem dv_shape : B1.stmtsEqb (fn% «da_verify»).body (B1.Da.dvP ++ [.ret [.n (val% «da_verify» "s11#0"),
      .n (val% «da_verify» "s11#0[1]"), .n (val% «da_verify» "s11#0[2]")]]) = true ∧
    B1.Da.dvP.all Stmt.flat = true ∧ B1.Main.hasCall B1.Da.dvP "da_padding" [.n (val% «da_verify» "n_blob_g")]
      [.n (val% «da_verify» "gap_g")] = true ∧
    (fn% «da_pad»).loop = false := by
  decide +kernel

/-- **`da_verify`'s blob count and gap at an instance**: `g^n` and `g^(DA_MAX_ROWS - n)`, `1 ≤ n ≤ DA_MAX_ROWS`, by
`da_padding`'s meaning. -/
theorem daV_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «da_verify» σ bufs kids) :
    ∃ n, 1 ≤ n ∧ n ≤ guest_const% DA_MAX_ROWS ∧
      σ (.n (val% «da_verify» "n_blob_g")) = Protocol.Verifier.gen ^ n ∧
      σ (.n (val% «da_verify» "gap_g")) = Protocol.Verifier.gen ^ (guest_const% DA_MAX_ROWS - n) := by
  obtain ⟨hbody, hflat, hpd, -⟩ := dv_shape
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv B1.Da.find_da_verify
  rw [B1.stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, -⟩ := B1.Digest.holdsList_flat B1.Da.dvP hflat _ _ hb
  have hall : ∀ s ∈ B1.Da.dvP, Stmt.Holds (coreProgram.Rel r.img.read) r.img.read σ s True _ :=
    fun s hs => holds_mono (fun _ _ _ h ↦ Res.KidRel.rel h) s id (fun _ h => h) (hallC s hs)
  have hpd' := B1.Da.da_padding_holds r.img.read (ref_memOk hr) _ _ (B1.Digest.call_of_flat hall hpd)
  simp only [List.map_cons, List.map_nil, B1.Da.MeaningDaPadding, List.cons.injEq, and_true] at hpd'
  obtain ⟨n, hn1, hn, e1, e2⟩ := hpd'
  rw [B1.Da.maxRows_eq] at hn e2
  exact ⟨n, hn1, hn, e1, e2⟩

/-- **`da_pad`'s gap passes down from `da_verify`**: `da_padding`'s `g^(DA_MAX_ROWS - r)`, `1 ≤ r`. -/
theorem daPadQ_step {r : Ref} (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) DaPadQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = name% «da_pad» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «da_pad» := Option.some.inj (hfn.symm.trans B1.Da.find_da_pad)
  obtain ⟨hbody, hflat, hpd, hpl⟩ := dv_shape
  -- the caller is `da_verify`
  have hmem : (name% «da_pad», name% «da_verify») ∈ Res.termCallers := by decide
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := B1.Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hdv : fI = name% «da_verify» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «da_pad» := Option.some.inj (hfI.symm.trans B1.Da.find_da_pad)
      rw [hpl] at hl; cases hl
  subst hdv
  obtain rfl : fnI = fn% «da_verify» := Option.some.inj (hfI.symm.trans B1.Da.find_da_verify)
  -- the site: `da_pad`'s gap is `da_verify`'s value `2`
  have hs := Res.calls_sites dv_pad_sites hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
  rw [hs.1, B1.Da.pad_params] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨-, -, h2, -⟩ := hpar
  -- `da_padding`'s return
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [B1.stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, -⟩ := B1.Digest.holdsList_flat B1.Da.dvP hflat _ _ hb
  have hall : ∀ s ∈ B1.Da.dvP, Stmt.Holds (coreProgram.Rel r.img.read) r.img.read σI s True _ :=
    fun s hs => holds_mono (fun _ _ _ h ↦ Res.KidRel.rel h) s id (fun _ h => h) (hallC s hs)
  have hpd' := B1.Da.da_padding_holds r.img.read (ref_memOk hr) _ _ (B1.Digest.call_of_flat hall hpd)
  simp only [List.map_cons, List.map_nil, B1.Da.MeaningDaPadding, List.cons.injEq, and_true] at hpd'
  obtain ⟨n, hn1, hn, -, e2⟩ := hpd'
  rw [B1.Da.maxRows_eq] at hn e2
  exact ⟨guest_const% DA_MAX_ROWS - n, by omega, by rw [h2, e2]⟩

/-- **`da_pad`'s gap at every honest instance.** -/
theorem daPadQ_all {r : Ref} (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, DaPadQ J := by
  refine insts_all hr (daPadQ_step hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
