/-
  LeanVM.Guest.EndExecCoreLink

  The caller's cells the core route links to slots (`CFun.gl`, of `glOk`'s family) at the honest
  instances: `anyLink`'s callees, their caller's entries and bound cells.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.CoreMode.CoreSound

/-!
# The caller's linked cells, sound

`glF_inst`: at an honest instance of core data whose links are of `glOk`'s ghost-free family, its
frame's header names its caller's frame, whose linked cells hold the slots' words: for a callee of
`anyLink` (its checks `LinkOk`), cell `2` its entries parameter and cell `5` its bound parameter times `g`
(`linkQ_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun slotW slotW_lt slotW_params')

public section

/-- **Header cell `1` names the caller's frame** `a`, in the reference. -/
theorem rd_hdr {r : Ref} {I : Inst} {a : ℕ} (hdr1 : r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2)
    (ha : I.hdr.2 = ofK (addressOfIndex a)) : CoreMode.Rd r.img I.fp 1 = some (ofK (Parameters.g ^ a)) := by
  rw [ha] at hdr1
  simpa [CoreMode.Rd, addressOfIndex, pow_add] using hdr1

/-- **The caller's linked cells at an honest instance** (`GlF`), for core data whose links are of a family. -/
theorem glF_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (hpN : Cf.fn.params = (List.range Cf.fn.params.length).map V.n)
    (hL : LinkOk Res.anyLink)
    (h : (Cf.gl.isEmpty || Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 &&
      decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1)])) = true)
    (hdr1 : r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2) (ws0 : List E) :
    CoreMode.GlF r.img Cf.gl I.fp (Cf.fn.params.map σ ++ ws0) := by
  intro d b k hmem
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [List.isEmpty_iff] at h
    rw [h] at hmem
    cases hmem
  obtain ⟨F, hF, hFe⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hFe
  obtain ⟨hname, hgl⟩ := hFe
  have hn : F.1 = f := hname.symm.trans (find_name' hf)
  have hcal := hL.fams F hF
  unfold Res.calleeB at hcal
  rw [hn, hf] at hcal
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hcal
  obtain ⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩ := hcal
  have hget : ∀ k < Cf.fn.params.length, Cf.fn.params[k]? = some (V.n k) := fun k hk ↦ by
    rw [hpN]
    simp [hk]
  obtain ⟨a, ha, h5, hm2, hm5⟩ := linkQ_all hL hr I hI f σ bufs kids ht F hF hn Cf.fn hf _ _
    (hget _ h1) (hget _ h2)
  have hRd := rd_hdr hdr1 ha
  have hsl : ∀ k < Cf.fn.params.length, slotW (Cf.fn.params.map σ ++ ws0) k = σ (V.n k) := fun k hk ↦ by
    rw [slotW_lt (by simpa using hk), slotW_params' hpN hk]
  rw [hgl] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, by omega, ?_⟩
    rw [hm2, hsl _ h1, pow_zero]
    simp
  · refine ⟨a, hRd, h5, ?_⟩
    rw [hm5, hsl _ h2, B1.word_gen, ← pow_one LeanVM.Protocol.Verifier.gen, Value.gen_pow_eq_ofK]

end

end LeanVM.Guest.EndExec
