/-
  LeanVM.Guest.B1.VerifySub.H.VtShape

  An honest child's `verify_tables` data fits B1-c's shapes (`VtShape`), and `verify_tables` is
  complete on it as `verify_sub`'s seventh callee (`H/KidsC`'s `hvt`).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Kids
public import LeanVM.Guest.B1.Tables.VtC.AComplete

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`verify_tables`' honest data fits its shapes.** -/
theorem H_shape (hbl : bytecode.length = 2 ^ 23) : Tables.VtShape S.H := by
  have hb := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  have hsl := S.hs_length
  have hh := S.hh33 hbl
  have hht : ∀ t < 6, Tables.vtHt S.rowsN t = S.hs.getD t 0 := fun t _ ↦ rfl
  obtain ⟨K, hK⟩ := (S.runG' hbl).2.2.2
  refine ⟨S.h32, ?_, ?_, ?_, S.hrowsL, fun t ht ↦ ?_, fun t ht ↦ ?_, ?_, by rw [H_f, hK]; rfl,
    fun i hi ↦ ?_, ?_, ?_, hbl⟩
  · rw [H_point, hpl, H_lm]; exact (height_le_depth S.logMem hsl (t := 0) (by norm_num)).2
  · rw [H_point, hpl]; omega
  · rw [H_point, hpl]; omega
  · rw [H_rows, hht t ht]
    exact hh _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  · rw [H_rows, H_point, hpl, hht t ht]; exact (height_le_depth S.logMem hsl ht).1
  · have := S.halphas
    show S.alphas.length = 4
    have e := congrArg (fun p ↦ p.1.length) this
    simp only [squeezeN_len] at e
    rw [← e]; rfl
  · rw [H_f, hK]
    exact Tables.tb_capOf_canonical _ _ (by
      rw [List.getD_eq_getElem _ _ (by simp [capOf]; omega)]; exact List.getElem_mem _)
  · rw [H_lm, H_rows, H_point, hpl, vtSizesP_sum S.logMem S.rowsN S.hrowsL]
    exact log2Ceil_le_iff.mp le_rfl
  · rw [H_rows, H_point, hpl]
    exact le_trans (vtSizesC_sum S.logMem S.rowsN S.hrowsL) (log2Ceil_le_iff.mp le_rfl)

theorem retsH_eq (bs : List ℕ) (sqE : ℕ) : S.H.retsH (S.vtB bs sqE) = S.vtRetsOf bs := rfl

end ChildSegs

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_tables` is complete on an honest child's data**, as `verify_sub` calls it. -/
theorem vt_kid_complete {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ) (bs : List ℕ) (sqE : ℕ) :
    CompleteAtD fs cert κ "verify_tables" (S.H.linL (S.vtB bs sqE)) (S.H.args (S.vtB bs sqE))
      (Returns (S.vtRetsOf bs)) := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  rw [← S.retsH_eq bs sqE]
  exact Tables.verify_tables_completeAt hκ hok (S.H_shape hbl) (S.vtB bs sqE)

end
end LeanVM.Guest.B1.VerifySub
