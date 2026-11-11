/-
  LeanVM.Guest.B1.VerifySub.H.KidsC

  `verify_sub`'s callees on an honest child are complete, placed: each but the terminal from its
  own completeness theorem on the honest child's data.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sec
public import LeanVM.Guest.B1.VerifySub.C.Callees
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Bits.Log2PlacedAll
public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.Ring.TargetComplete

/-!
# The callees, complete

`kid_complete`: callee `j < 12` (all but the
terminal) is `CompleteAtD` on its words, given `verify_keccak`'s completeness (`VkCompleteAt`) and
`verify_tables`' and `open_stacked`'s on the honest child's data (`hvt`, `hos`: `Complete`
discharges them from their tracks' theorems).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem x_canonical {x0 x1 : E} {root : Digest} (h : digestFromHalves (x0, x1) = some root) :
    IsCanonical128 x0 ∧ IsCanonical128 x1 := by
  unfold digestFromHalves at h
  split at h
  · rename_i hc; exact hc
  · simp at h

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub`'s callees but the terminal are complete, placed.** -/
theorem kid_complete {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ)
    (hvk : VkCompleteAt fs cert κ) (bs : List ℕ) (sqE : ℕ)
    (hvt : CompleteAtD fs cert κ "verify_tables" (S.H.linL (S.vtB bs sqE)) (S.H.args (S.vtB bs sqE))
      (Returns (S.vtRetsOf bs)))
    (hos : CompleteAtD fs cert κ (B1.Whir.openName S.μs) [(S.cW bs, S.xsW)]
      (B1.Whir.rateSel S.rate :: capOf S.s8.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
        ofK (addressOfIndex (S.cW bs))]) (vsOsOut S.μs S.w))
    {j : ℕ} (hj : j < 12) (pv : List (List E × Main.Layout)) :
    CompleteAtD fs cert κ ((S.kids bs sqE).getD j noKid pv).f
      ((S.kids bs sqE).getD j noKid pv).Lin ((S.kids bs sqE).getD j noKid pv).args
      ((S.kids bs sqE).getD j noKid pv).Out := by
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  interval_cases j
  · exact gpw_completeAt κ [] (by have := S.hr4; omega)
  · exact gpw_completeAt κ [] (by have := S.h32; omega)
  · refine log2_L0_completeAt κ (by omega) _ sqE (S.pushTotal_lt hbl) ?_
    show max 0 S.μ < 34; omega
  · exact ac_completeAt κ [] (x_canonical S.hroot).1
  · exact ac_completeAt κ [] (x_canonical S.hroot).2
  · obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
    exact Tables.verify_bus_gkr_completeAt (by omega) (by omega) (by omega) hrun S.capS_carries
      (vcG bs) (vb bs 5)
  · exact hvt
  · obtain ⟨hrun, -, -, -, hc6⟩ := S.runK' hbl
    have hf : S.s6.cap = capOf S.H.s3.perm := S.s6_capOf hbl
    exact hvk S.τ S.s6.cap S.chis S.outs S.xsK S.op S.kpt S.slices S.s7.cap S.word S.m0
      (S.cK bs) (vb bs 8) (S.cL bs) (vb bs 9) (vb bs 10) hτ.1 (by omega)
      (by rw [S.chis_length]; exact hτ.2.2) (S.lanes hbl).2.2 (by rw [hf]; rfl)
      (by rw [hf]; exact Tables.tb_capOf_canonical _) hc6 hrun
  · exact rst_completeAt κ (by have := (S.runK' hbl).2.2.2.1; exact this) S.rchs_length
  · exact Tables.certify_placement_completeAt fs cert (by omega) S.hs_length S.h32 (S.hh33 hbl)
      (by have := vsH_tau26 hbl S.hrowsL S.stack32; unfold ChildSegs.hs; omega) _ _
  · have hst : Tables.stackTotal S.kappas ≤ 2 ^ 32 := by
      have h32 := S.stack32
      rw [stackLog_eq hbl] at h32
      exact log2Ceil_le_iff.mp (by
        show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
          ≤ 32
        omega)
    refine log2_L16_completeAt κ (by omega) _ sqE (by omega) ?_
    have : log2Ceil (Tables.stackTotal S.kappas) ≤ 32 := log2Ceil_le_iff.mpr hst
    omega
  · exact hos

end
end LeanVM.Guest.B1.VerifySub
