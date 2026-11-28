/-
  LeanVM.Guest.CoreMode.Fn.da_pad.EndExecCoreDaA

  `da_verify`'s blob count and gap, and `da_pad`'s gap, at the honest instances of b2c's aligned tree:
  the bus era's `EndExecCoreDa` on `instsR`.
-/

module

public import LeanVM.Guest.EndExecInstA
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Da.Padding
public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.B1.Main.Loops
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# `da_verify`'s and `da_pad`'s gaps, aligned

`daV_instA`: at an honest instance of `da_verify`, its call of `da_padding` gives its blob count
`g^n` and its gap `g^(DA_MAX_ROWS - n)`, `1 ≤ n ≤ DA_MAX_ROWS` (`B1.Da.da_padding_holds`).
`daPadQ_allA`: `da_pad`'s only caller is `da_verify` (`Res.termCallers_all`), which hands it its gap,
so at every honest instance of `da_pad` its gap is `g^k`, `k < DA_MAX_ROWS` (`insts_allA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **`da_pad`'s gap at an instance**: `g^k`, `k < DA_MAX_ROWS`. -/
def DaPadQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «da_pad» σ bufs kids → ∃ k, k < guest_const% DA_MAX_ROWS ∧
    σ (.n (val% «da_pad» "gap_g")) = Protocol.Verifier.gen ^ k

end

public section

/-- `da_verify` calls `da_pad` at its rows' roots, its blob count and its gap. -/
theorem dv_pad_sites : Res.sitesB (fun f args rets ↦ f != name% «da_pad» ||
    (args == [.n (val% «da_verify» "roots"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "gap_g")] &&
      rets == [])) (fn% «da_verify»).body = true := by
  decide +kernel

theorem da_pad_facts : (fn% «da_pad»).params = [.n 0, .n 1, .n 2] ∧ (fn% «da_pad»).loop = false := by
  decide +kernel

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`da_padding`'s return at an honest instance of `da_verify`**: the blob count `g^n` and the gap
`g^(DA_MAX_ROWS - n)`, `1 ≤ n ≤ DA_MAX_ROWS`. -/
theorem daV_of_valid (hR : RefH (layB al) (D r) r) (hr : r.Ok) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {args rets : List E} (hv : (Memory.Tree.node name% «da_verify» σ bufs kids).Valid coreProgram r.img.read args rets) :
    ∃ n, 1 ≤ n ∧ n ≤ guest_const% DA_MAX_ROWS ∧
      σ (.n (val% «da_verify» "n_blob_g")) = Protocol.Verifier.gen ^ n ∧
      σ (.n (val% «da_verify» "gap_g")) = Protocol.Verifier.gen ^ (guest_const% DA_MAX_ROWS - n) := by
  have hok := B1.Da.dv_ok
  unfold B1.Da.dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hbody⟩, hflat⟩, hpd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv B1.Da.find_da_verify
  rw [B1.stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, -⟩ := B1.Digest.holdsList_flat B1.Da.dvP hflat _ _ hb
  have hall : ∀ s ∈ B1.Da.dvP, Stmt.Holds (coreProgram.Rel r.img.read) r.img.read σ s True _ :=
    fun s hs ↦ holds_mono (fun _ _ _ h ↦ Res.KidRel.rel h) s id (fun _ h ↦ h) (hallC s hs)
  have hpd' := B1.Da.da_padding_holds r.img.read (ref_memOkA hR hr) _ _ (B1.Digest.call_of_flat hall hpd)
  simp only [List.map_cons, List.map_nil, B1.Da.MeaningDaPadding, List.cons.injEq, and_true] at hpd'
  obtain ⟨n, hn1, hn, e1, e2⟩ := hpd'
  rw [B1.Da.maxRows_eq] at hn e2
  exact ⟨n, hn1, hn, e1, e2⟩

/-- **`da_verify`'s blob count and gap at an honest instance.** -/
theorem daV_instA (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «da_verify» σ bufs kids) :
    ∃ n, 1 ≤ n ∧ n ≤ guest_const% DA_MAX_ROWS ∧
      σ (.n (val% «da_verify» "n_blob_g")) = Protocol.Verifier.gen ^ n ∧
      σ (.n (val% «da_verify» "gap_g")) = Protocol.Verifier.gen ^ (guest_const% DA_MAX_ROWS - n) := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  exact daV_of_valid hR hr hv

/-- **`da_pad`'s gap passes down from `da_verify`**: `da_padding`'s `g^(DA_MAX_ROWS - n)`, `1 ≤ n`. -/
theorem daPadQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) DaPadQ := by
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
  obtain ⟨hps, hpl⟩ := da_pad_facts
  -- the caller is `da_verify`
  have hmem : (name% «da_pad», name% «da_verify») ∈ Res.termCallers :=
    CoreMode.FnReg.stCallers_of_da_pad _ (by simp [CoreMode.Own.da_pad.stCallers])
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := find_name' hfI
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
  -- the site: `da_pad`'s gap is `da_verify`'s
  have hs := Res.calls_sites dv_pad_sites hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
  rw [hs.1, hps] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨-, -, h2, -⟩ := hpar
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI hIt
  obtain ⟨n, hn1, -, -, e2⟩ := daV_of_valid hR hr hv
  exact ⟨guest_const% DA_MAX_ROWS - n, by omega, h2.trans e2⟩

/-- **`da_pad`'s gap at every honest instance.** -/
theorem daPadQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, DaPadQ J := by
  refine insts_allA hR (daPadQ_stepA hR hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
