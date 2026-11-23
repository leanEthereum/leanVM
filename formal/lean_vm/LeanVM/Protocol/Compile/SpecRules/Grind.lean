/-
  LeanVM.Protocol.Compile.SpecRules.Grind

  The per-message security target, the grind that brings a verifier message's round-by-round
  error to it, and a follower that starts with a challenge.
-/

module

import LeanVM.Protocol.Compile.SpecRules.Basic
public import LeanVM.Parameters.Field
public import Statement.LeanVmVerifier
import LeanVM.Protocol.Field
public import ArkLib.OracleReduction.OracleInterface
public import CompPoly.Multilinear.Basic
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Grinds

Every verifier message's round-by-round error, after the grind before it, is at most
`εmsg = 2^-securityBits` (`SECURITY_BITS`, `crates/verifier/src/transcript.rs`): a message
whose error is `N / |E|` grinds `grindingBits N` bits, and `grindingBits_discount` is the bound
`2^-grindingBits N · N / |E| ≤ 2^-125` a phase's specification discharges at the boundary after
that grind (`Spec.grindP`'s side condition, the follower's lead `N / |E|`).

`q.StartsSample R`: `q` starts with a challenge, or returns at once a value satisfying `R`, what
the follower of a program that may end on a grind must do (`EndToEnd.Sound.Moves`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters VerifierProgram

@[expose] public section

variable {α : Type}

/-! ## The per-message target -/

/-- The round-by-round error every verifier message is held to after its grind,
`2^-securityBits = 2^-125`. -/
noncomputable def εmsg : ENNReal := 2⁻¹ ^ securityBits

/-- A message whose error is `N / |E|` grinds enough bits: `N ≤ 2^(grindingBits N + 3)`. -/
theorem le_two_pow_grindingBits (N : ℕ) : N ≤ 2 ^ (grindingBits N + (128 - securityBits)) := by
  unfold grindingBits
  split_ifs with hN
  · exact hN.trans Nat.one_le_two_pow
  · have h1 : N - 1 < 2 ^ ((N - 1).log2 + 1) := Nat.lt_log2_self
    calc N ≤ 2 ^ ((N - 1).log2 + 1) := by omega
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by simp only [securityBits]; omega)

/-- **The grind's discount**: `2^-grindingBits N · N / |E| ≤ 2^-125`. -/
theorem grindingBits_discount (N : ℕ) :
    (2 : ENNReal)⁻¹ ^ grindingBits N * ((N : ENNReal) / Fintype.card E) ≤ εmsg := by
  have hN : (N : ENNReal) ≤ 2 ^ (grindingBits N + 3) := by
    have := le_two_pow_grindingBits N
    simp only [securityBits] at this
    exact_mod_cast this
  rw [Protocol.card_E, εmsg, securityBits, Nat.cast_pow, Nat.cast_ofNat]
  have h2 : (2 : ENNReal)⁻¹ ^ grindingBits N * 2 ^ grindingBits N = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc (2 : ENNReal)⁻¹ ^ grindingBits N * ((N : ENNReal) / 2 ^ 128)
      ≤ (2 : ENNReal)⁻¹ ^ grindingBits N * (2 ^ (grindingBits N + 3) / 2 ^ 128) := by gcongr
    _ = (2 : ENNReal)⁻¹ ^ grindingBits N * 2 ^ grindingBits N * (2 ^ 3 / 2 ^ 128) := by
        rw [pow_add, mul_div_assoc, mul_assoc]
    _ = 2 ^ 3 / 2 ^ 128 := by rw [h2, one_mul]
    _ = (2 : ENNReal)⁻¹ ^ 125 := by
        rw [show (2 : ENNReal) ^ 128 = 2 ^ 3 * 2 ^ 125 by rw [← pow_add],
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
          mul_comm ((2 : ENNReal) ^ 3)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
          mul_one, ENNReal.inv_pow]

/-! ## A follower that starts with a challenge -/

namespace VerifierProgram

/-- `q` starts with a challenge, or returns at once a value satisfying `R`. -/
def StartsSample (R : α → Prop) : VerifierProgram α → Prop
  | sample _ => True
  | ret a => R a
  | _ => False

theorem StartsSample.mono {R R' : α → Prop} (hR : ∀ a, R a → R' a) :
    ∀ {q : VerifierProgram α}, q.StartsSample R → q.StartsSample R'
  | sample _, _ => trivial
  | ret a, h => hR a h

end VerifierProgram

end
end LeanVM.Protocol.Compile
