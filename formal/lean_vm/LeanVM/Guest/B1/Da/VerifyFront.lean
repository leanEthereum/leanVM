/-
  LeanVM.Guest.B1.Da.VerifyFront

  `da_verify`'s shape words (G:4516-4526): the blob count, the padded count's log and the gap.
-/

module

public import LeanVM.Guest.B1.Da.Verify

/-!
# `da_verify`'s shape words

`dv_front`: under a call relation below `coreProgram.Rel`, with the exponent table at its argument,
`da_verify`'s body puts `g^L`, `L ≤ 10`, in cell `2` (its range check), and `da_row_shape` the blob
count `g^r`, `r ≤ 2^L`, in cell `1` and the gap `g^(2^L - r)` in cell `8`. `dv_body`, `dv_flat`: its
body is the flat block `dvP` and its `ret`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

public section

theorem dv_body : (fn% «da_verify»).body = dvP ++ [.ret [.n 23, .n 24, .n 25]] := by
  have h := dv_ok
  unfold dvOk at h
  simp only [Bool.and_eq_true] at h
  exact stmtsEqb_sound h.1.1.1.1.1.1.1.1.1.1.2

theorem dv_flat : dvP.all Stmt.flat = true := by
  have h := dv_ok
  unfold dvOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

/-- **`da_verify`'s shape words**: `[2] = g^L`, `L ≤ 10`, `[1] = g^r`, `r ≤ 2^L`, `[8] = g^(2^L - r)`. -/
theorem dv_front {rd : Reader} {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) (hm : MemOk rd)
    {σ : Val} {rets : List E} (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify») False (· = rets))
    (hsq : SquaresAt rd (σ (.n 0))) :
    ∃ L r, L ≤ 10 ∧ r ≤ 2 ^ L ∧ σ (.n 1) = gen ^ r ∧ σ (.n 2) = gen ^ L ∧ σ (.n 8) = gen ^ (2 ^ L - r) := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hbody⟩, hflat⟩, hrc2⟩, hcrs⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, -⟩ := holdsList_flat dvP hflat _ _ hb
  have hall : ∀ s ∈ dvP, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  have hat := atoms_of_flat hall
  obtain ⟨L, hL, h2⟩ := rcConst_sound hm (by norm_num) word_g10 hrc2 hat
  have hrs := da_row_shape_holds rd hm _ _ (call_of_flat hall hcrs)
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, -, -, h1, hnp, h34⟩ := hrs hsq L hL h2
  simp only [List.cons.injEq, and_true] at h34
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.paddedRowCount, LeanDa.logPaddedRowCount]; exact Nat.le_pow_clog (by norm_num) r
  exact ⟨L, r, hL, hrL, h1, h2, h34.2⟩

end

end LeanVM.Guest.B1.Da
