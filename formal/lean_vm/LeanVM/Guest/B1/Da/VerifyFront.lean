/-
  LeanVM.Guest.B1.Da.VerifyFront

  `da_verify`'s shape words: the blob count and the padding rows' count.
-/

module

public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_verify`'s shape words

`dv_front`: under a call relation below `coreProgram.Rel`, `da_verify`'s body puts (`da_padding`) the
blob count `g^r`, `1 ≤ r ≤ DA_MAX_ROWS`, in cell `1` and the padding rows' count `g^(DA_MAX_ROWS - r)`
in cell `2`. `dv_body`, `dv_flat`: its body is the flat block `dvP` and its `ret`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

public section

theorem dv_body : (fn% «da_verify»).body = dvP ++ [.ret [.n 26, .n 27, .n 28]] := by
  have h := dv_ok
  unfold dvOk at h
  simp only [Bool.and_eq_true] at h
  exact stmtsEqb_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem dv_flat : dvP.all Stmt.flat = true := by
  have h := dv_ok
  unfold dvOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- **`da_verify`'s shape words**: `[1] = g^r`, `1 ≤ r ≤ DA_MAX_ROWS`, `[2] = g^(DA_MAX_ROWS - r)`. -/
theorem dv_front {rd : Reader} {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) (hm : MemOk rd)
    {σ : Val} {rets : List E} (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify») False (· = rets)) :
    ∃ r, 1 ≤ r ∧ r ≤ guest_const% DA_MAX_ROWS ∧ σ (.n 1) = gen ^ r ∧
      σ (.n 2) = gen ^ (guest_const% DA_MAX_ROWS - r) := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hbody⟩, hflat⟩, hpd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, -⟩ := holdsList_flat dvP hflat _ _ hb
  have hall : ∀ s ∈ dvP, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  have hpd' := da_padding_holds rd hm _ _ (call_of_flat hall hpd)
  simp only [List.map_cons, List.map_nil, MeaningDaPadding] at hpd'
  obtain ⟨r, hr1, hr, h1, h2⟩ := hpd'
  simp only [List.cons.injEq, and_true] at h2
  rw [maxRows_eq] at hr h2
  exact ⟨r, hr1, hr, h1, h2⟩

end

end LeanVM.Guest.B1.Da
