/-
  LeanVM.Guest.B1.Sig.Callees

  The signature verifiers' relations imply their meanings, and the shape `main`'s callees take
  (`Main.Callees.verify_lean_xmss`, `Main.Callees.verify_sig_lean_sphincs`).
-/

module

public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.B1.Main.Callees

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {rd : Reader}

/-- **`verify_lean_xmss` is sound**: its relation gives its meaning. -/
theorem verify_lean_xmss_meaning {args rets : List E} (h : coreProgram.Rel rd "verify_lean_xmss" args rets) :
    Meaning_verify_lean_xmss rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem Sig.find_verify_lean_xmss args rets).mp h
  obtain ⟨hr, pk, m, hc, sig, hv⟩ := Sig.verify_lean_xmss_sound hb
  exact ⟨σ (.n 0), by rw [← hp]; rfl, hr, pk, m, hc, sig, hv⟩

/-- **`verify_sig_lean_sphincs` is sound**: its relation gives its meaning. -/
theorem verify_sig_lean_sphincs_meaning {args rets : List E}
    (h : coreProgram.Rel rd "verify_sig_lean_sphincs" args rets) : Meaning_verify_sig_lean_sphincs rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem Sig.find_verify_sig_lean_sphincs args rets).mp h
  obtain ⟨hr, pk, m, hc, sig, hv⟩ := Sig.verify_sig_lean_sphincs_sound Sig.fkSound_rel hb
  exact ⟨σ (.n 0), by rw [← hp]; rfl, hr, pk, m, hc, sig, hv⟩

namespace Sig

theorem main_cellVal_cellOf (v : BitVec 128) : Main.cellVal (cellOf v) = v := cellVal_cellOf v

theorem cellPairVal_cellOf (m : BitVec 256) :
    Main.cellPairVal (cellOf (m.extractLsb' 0 128)) (cellOf (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  rw [Main.toNat_cellPairVal]
  show cellNat (cellOf _) + 2 ^ 128 * cellNat (cellOf _) = _
  rw [cellNat_cellOf, cellNat_cellOf, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := m.isLt; norm_num at this ⊢; omega))]
  have := Nat.mod_add_div m.toNat (2 ^ 128)
  omega

theorem readsAt_claim {p : E} {cs : Fin 4 → E} (h : ClaimAt rd p cs) : ReadsAt rd p [cs 0, cs 1, cs 2, cs 3] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

theorem xmssOf_claim (pk : LeanXmss.PublicKey) (m : LeanXmss.Message) :
    Main.xmssOf (claimCells pk.root pk.parameter m 0) (claimCells pk.root pk.parameter m 1)
      (claimCells pk.root pk.parameter m 2) (claimCells pk.root pk.parameter m 3) = (pk, m) := by
  show ((⟨Main.cellVal (cellOf pk.root), Main.cellVal (cellOf pk.parameter)⟩ : LeanXmss.PublicKey),
    Main.cellPairVal (cellOf (m.extractLsb' 0 128)) (cellOf (m.extractLsb' 128 128))) = (pk, m)
  rw [main_cellVal_cellOf pk.root, main_cellVal_cellOf pk.parameter]
  exact Prod.ext rfl (cellPairVal_cellOf m)

theorem sphincsOf_claim (pk : Sphincs.PublicKey) (m : Sphincs.Message) :
    Main.sphincsOf (claimCells pk.root pk.parameter m 0) (claimCells pk.root pk.parameter m 1)
      (claimCells pk.root pk.parameter m 2) (claimCells pk.root pk.parameter m 3) = (pk, m) := by
  show ((⟨Main.cellVal (cellOf pk.root), Main.cellVal (cellOf pk.parameter)⟩ : Sphincs.PublicKey),
    Main.cellPairVal (cellOf (m.extractLsb' 0 128)) (cellOf (m.extractLsb' 128 128))) = (pk, m)
  rw [main_cellVal_cellOf pk.root, main_cellVal_cellOf pk.parameter]
  exact Prod.ext rfl (cellPairVal_cellOf m)

end Sig

/-- **`main`'s callee `verify_lean_xmss`.** -/
theorem verify_lean_xmss_signed (p : E) (h : coreProgram.Rel rd "verify_lean_xmss" [p] []) : Main.XmssSigned rd p := by
  obtain ⟨q, hq, -, pk, m, hc, sig, hv⟩ := verify_lean_xmss_meaning h
  cases hq
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, sig, ?_⟩
  rw [Sig.xmssOf_claim]
  exact hv

/-- **`main`'s callee `verify_sig_lean_sphincs`.** -/
theorem verify_sig_lean_sphincs_signed (p : E) (h : coreProgram.Rel rd "verify_sig_lean_sphincs" [p] []) :
    Main.SphincsSigned rd p := by
  obtain ⟨q, hq, -, pk, m, hc, sig, hv⟩ := verify_sig_lean_sphincs_meaning h
  cases hq
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, sig, ?_⟩
  rw [Sig.sphincsOf_claim]
  exact hv

end
end LeanVM.Guest.B1
