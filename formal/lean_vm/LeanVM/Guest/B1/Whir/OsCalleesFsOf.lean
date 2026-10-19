/-
  LeanVM.Guest.B1.Whir.OsCalleesFsOf

  Group 1's callees' maxima at frame sizes agreeing with `fsOf` but at `main`, and `open_stacked`'s
  bounded completeness there, given the certificates' facts.
-/

module

public import LeanVM.Guest.B1.Whir.OsPureInst
public import LeanVM.Guest.B1.G1BoundsAt

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **Group 1's callees' maxima at frame sizes agreeing with `fsOf` but at `main`**: the constants of
`g1BoundsOf`, the out of domain point's loop at most `22` iterations, the grinding loop's `17`. -/
noncomputable def osCalleesMaxOf (fs' : String → ℕ) (h : FsAgree fs') (cert : String → V → ℕ) (k : ℕ)
    (hc : G1Certs fs' cert) : OsCalleesMax (osCalleesAtB fs' cert k hc (g1BoundsOf fs' h)) where
  foldMax := 68
  fold := fun _ => le_rfl
  canonicalMax := fs' "assert_canonical"
  canonical := fun _ => le_rfl
  oodMax := fs' "opening_ood_point" + 46 + max (22 * 78) (fs' "__loop9")
  ood := fun a m ha hm => by
    show fs' "opening_ood_point" + (2 * logG (a.getD 3 0) + 2) +
      max (logG (a.getD 3 0) * 78) (fs' "__loop9") ≤ _
    rw [ha]
    have h := (LeanVM.Guest.logG_gen_pow_le m).trans hm
    exact Nat.add_le_add (Nat.add_le_add_left (by omega) _)
      (max_le_max (Nat.mul_le_mul_right _ h) le_rfl)
  grindMax := fs' "grind_check" + max (17 * 32) (fs' "__loop6")
  grind := fun a ha => by
    show fs' "grind_check" + max (logG (a.getD 3 0) * 32) (fs' "__loop6") ≤ _
    rw [ha]
    exact Nat.add_le_add_left (max_le_max (Nat.mul_le_mul_right _
      (LeanVM.Guest.logG_gen_pow_le Whir.queryGrindingBits)) le_rfl) _
  finalMsg4Max := 72
  finalMsg4 := fun _ => le_rfl
  finalMsg8Max := 124
  finalMsg8 := fun _ => le_rfl
  finalMsg16Max := 228
  finalMsg16 := fun _ => le_rfl
  finalMsg32Max := 436
  finalMsg32 := fun _ => le_rfl
  rowWeights4Max := 57
  rowWeights4 := fun _ => le_rfl
  rowWeights6Max := 205
  rowWeights6 := fun _ => le_rfl
  foldFinal2Max := 92
  foldFinal2 := fun _ => le_rfl
  foldFinal3Max := 137
  foldFinal3 := fun _ => le_rfl
  foldFinal4Max := 194
  foldFinal4 := fun _ => le_rfl
  foldFinal5Max := 275
  foldFinal5 := fun _ => le_rfl

/-- `osCalleesMaxOf` at `fsOf`. -/
noncomputable def osCalleesMaxFsOf (cert : String → V → ℕ) (k : ℕ) (hc : G1Certs fsOf cert) :
    OsCalleesMax (osCalleesAtB fsOf cert k hc g1BoundsFsOf) :=
  osCalleesMaxOf fsOf (fun _ _ _ _ => rfl) cert k hc

/-- **`open_stacked` is complete, placed, by bounded trees, at frame sizes agreeing with `fsOf` but
at `main`**, given group 1's certificate facts and the queries loops'. -/
theorem open_stacked_completeAtB_of (fs' : String → ℕ) (h : FsAgree fs') (cert : String → V → ℕ) (k : ℕ)
    (hc : G1Certs fs' cert) (hq : OsOqFits fs' cert) :
    CompleteOpenAtB fs' cert k CapAgrees (osBop fs' (osCalleesMaxOf fs' h cert k hc) (osPureSizes fs')) :=
  open_stacked_completeAtB' fs' cert k _ (osCalleesMaxOf fs' h cert k hc) hq

/-- `open_stacked_completeAtB_of` at `fsOf`. -/
theorem open_stacked_completeAtB_fsOf (cert : String → V → ℕ) (k : ℕ) (hc : G1Certs fsOf cert)
    (hq : OsOqFits fsOf cert) :
    CompleteOpenAtB fsOf cert k CapAgrees (osBop fsOf (osCalleesMaxFsOf cert k hc) (osPureSizes fsOf)) :=
  open_stacked_completeAtB_of fsOf (fun _ _ _ _ => rfl) cert k hc hq

end
end LeanVM.Guest.B1
