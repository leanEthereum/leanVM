/-
  LeanVM.Guest.B1.VsC.VkEnd

  `verify_keccak` placed: its callees' end within `2^24` of its cursor when every frame is small.
-/

module

public import LeanVM.Guest.B1.VsC.VkPJ
public import LeanVM.Guest.B1.VsC.EndBnd
import LeanVM.Guest.ValRef

/-!
# `verify_keccak`'s end, bounded

Each layer ends within `2^18` of its cursor (`KeccakLayerCompleteA`'s bound, `lp_spec`), so the
twelve layers' positions grow by at most `2^19` each (`posP_le`); with the copy loops and the
closing rounds, `verify_keccak`'s callees end within `2^24` of its cursor (`eF_le`), on `D.Ok`'s
`τ ≤ 28`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Memory
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VsC (lpB FsSmall step_le lpB_le)

@[expose] public section

namespace VkData

variable {D : VkData} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
variable {c curE tbE : ℕ}

/-- **The layers' positions**, each within `2^19` of the one before. -/
theorem posP_le (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok) (hfs : FsSmall fs) :
    ∀ s ≤ 12, (D.posP fs al cert k c curE tbE s).1 ≤ D.l0end fs al c + s * 2 ^ 19
  | 0, _ => by simp [posP]
  | s + 1, hs => by
    have ih := posP_le hL h hfs s (by omega)
    obtain ⟨-, hb, -⟩ := lp_spec (D := D) (fs := fs) (al := al) (cert := cert) (k := k) (c := c) (curE := curE)
      (tbE := tbE) hL h (s := s) (by omega)
    replace hb := hb hfs
    have h1 := allocBase_le (al (lname s)) (D.posP fs al cert k c curE tbE s).1
    have h2 := hfs (lname s)
    unfold lfp at hb
    omega

/-- **`verify_keccak`'s callees end within `2^24` of its cursor.** -/
theorem eF_le (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok) (hfs : FsSmall fs) :
    D.eF fs al cert k c curE tbE ≤ c + 2 ^ 24 := by
  have hτ := h.2.1
  have h12 := posP_le (c := c) (curE := curE) (tbE := tbE) hL h hfs 12 le_rfl
  have hl0 : D.l0end fs al c ≤ c + D.τ + 412 + 15 + 25 * 2 ^ 16 := by
    unfold l0end l0fp
    have := allocBase_le (al name% «verify_keccak_loop0») (c + D.τ + 412)
    have := lpB_le hfs name% «verify_keccak_loop0» (D.τ - 4) 0
    have : (D.τ - 4 - 0 + 1) * 2 ^ 16 ≤ 25 * 2 ^ 16 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hq : D.q12 fs al cert k c curE tbE ≤ c + 2 ^ 23 := by
    unfold q12; omega
  unfold eF es ei e1 eo
  have s1 := step_le hfs (al "keccak_plain_rounds__L6_L0") "keccak_plain_rounds__L6_L0"
    (D.q12 fs al cert k c curE tbE)
  set x1 := allocBase (al "keccak_plain_rounds__L6_L0") (D.q12 fs al cert k c curE tbE) +
    fs "keccak_plain_rounds__L6_L0"
  have a2 := allocBase_le (al name% «verify_keccak_loop1») x1
  have l2 := lpB_le hfs name% «verify_keccak_loop1» (D.τ - 4) 0
  set x2 := allocBase (al name% «verify_keccak_loop1») x1 + lpB fs name% «verify_keccak_loop1» (D.τ - 4) 0
  have s3 := step_le hfs (al "keccak_plain_rounds__L4_L1") "keccak_plain_rounds__L4_L1" x2
  set x3 := allocBase (al "keccak_plain_rounds__L4_L1") x2 + fs "keccak_plain_rounds__L4_L1"
  have s4 := step_le hfs (al "keccak_plain_rounds__L6_L0") "keccak_plain_rounds__L6_L0" x3
  set x4 := allocBase (al "keccak_plain_rounds__L6_L0") x3 + fs "keccak_plain_rounds__L6_L0"
  have a5 := allocBase_le (al name% «verify_keccak_loop2») x4
  have l5 := lpB_le hfs name% «verify_keccak_loop2» (D.τ - 4) 0
  have m : (D.τ - 4 - 0 + 1) * 2 ^ 16 ≤ 25 * 2 ^ 16 := Nat.mul_le_mul_right _ (by omega)
  omega

end VkData

end
end LeanVM.Guest.B1.VerifySub
