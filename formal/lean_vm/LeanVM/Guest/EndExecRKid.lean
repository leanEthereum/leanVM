/-
  LeanVM.Guest.EndExecRKid

  A callee's returned values in its frame's cells on the reference memory.
-/

module

public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.EndExecW

/-!
# A callee's returns

`kid_rets`: at an honest instance, a taken call's callee frame holds the call's returns after its
arguments: the callee is an honest instance there (`honest_kid`), valid on the call's words
(`B2C.kidsValid_get`), so it runs and leaves its returns in its frame (`B2C.inst_runs`, `B2C.b2Hyps`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (kidsValid_get calls_ne_main inst_runs b2Hyps)

public section

variable {r : Ref}

/-- **A taken call's returns in its callee's frame**, after its arguments. -/
theorem kid_rets (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    {i kfp : ℕ} {c : Call} (hc : (calls es)[i]? = some c) (hk : I.kidFps[i]? = some kfp)
    (htk : c.taken = true) :
    ∀ k < c.rets.length, r.img.read (addressOfIndex (kfp + (2 + c.args.length + k))) =
      some (σ (c.rets.getD k (.n 0))) := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := hv
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hw] at hw'
  obtain ⟨rfl, -⟩ := Out.ret.inj hw'
  obtain ⟨k', hk1, hkn, hkval⟩ := (kidsValid_get hkv).2 i c hc
  have hkids : I.t.kids = kids := by rw [ht]; rfl
  obtain ⟨J, hJ, hJt, hJfp, -⟩ := honest_kid hI (k := k') (by rw [hkids]; exact hk1)
  obtain rfl : kfp = J.fp := Option.some.inj (hk.symm.trans hJfp)
  have hne : c.f ≠ "main" := calls_ne_main hf hw (List.mem_of_getElem? hc)
  have hJn : J.t.name = c.f := by rw [hJt, hkn]
  obtain ⟨-, -, -, -, -, hrets⟩ := inst_runs b2Hyps hr.name hH hXh.covers (J.t.total B2C.fs + 1) J hJ
    (Nat.lt_succ_self _) (fun hm ↦ absurd (hJn ▸ hm) hne) _ _ (by rw [hJt]; exact hkval htk)
  intro k hk'
  have := hrets k (by simpa using hk')
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] using this

end

end LeanVM.Guest.EndExec
