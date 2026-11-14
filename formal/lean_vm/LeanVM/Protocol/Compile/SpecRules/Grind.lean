/-
  LeanVM.Protocol.Compile.SpecRules.Grind

  The per-message security target, the grind that brings a verifier message's round-by-round
  error to it, and the compositional form of `GrindThenSample`.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Basic

/-!
# Grinds

Every verifier message's round-by-round error, after the grind before it, is at most
`εmsg = 2^-securityBits` (`SECURITY_BITS`, `crates/verifier/src/transcript.rs`): a message
whose error is `N / |E|` grinds `grindingBits N` bits, and `grindingBits_discount` is the bound
`2^-grindingBits N · N / |E| ≤ 2^-125` a phase's specification discharges at the boundary after
that grind (`Spec.grindP`'s side condition, the follower's lead `N / |E|`).

`GrindThenSample P` (`LeanVM.Protocol.Compile.Prog`) is proved compositionally through
`GrindsThen p R`: every grind of `p` is followed at once by a challenge, inside `p` or, where `p`
returns right after the grind with a value satisfying `R`, by the follower
(`grindsThen_bind`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters VerifierProgram

@[expose] public section

variable {α β : Type}

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

/-! ## Grinds followed by challenges -/

namespace VerifierProgram

/-- `q` starts with a challenge, or returns at once a value satisfying `R`. -/
def StartsSample (R : α → Prop) : VerifierProgram α → Prop
  | sample _ => True
  | ret a => R a
  | _ => False

/-- Every proof of work of `p` is followed at once by a challenge: inside `p`, or, where `p`
returns right after it, by the follower, given that the value returned satisfies `R`. -/
def GrindsThen (p : VerifierProgram α) (R : α → Prop) : Prop :=
  ∀ l b k, p.after l = some (grind b k) → k.StartsSample R

theorem StartsSample.mono {R R' : α → Prop} (hR : ∀ a, R a → R' a) :
    ∀ {q : VerifierProgram α}, q.StartsSample R → q.StartsSample R'
  | sample _, _ => trivial
  | ret a, h => hR a h

theorem GrindsThen.mono {p : VerifierProgram α} {R R' : α → Prop} (hp : p.GrindsThen R)
    (hR : ∀ a, R a → R' a) : p.GrindsThen R' :=
  fun l b k h ↦ (hp l b k h).mono hR

/-- **Sequencing**: the grinds of `p.bind f` are `p`'s, each followed by a challenge or by the
start of `f a`, and those of `f a`. -/
theorem grindsThen_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {R : α → Prop}
    {R' : β → Prop} (hp : p.GrindsThen R) (hR : ∀ a, R a → (f a).StartsSample R')
    (hf : ∀ a, (f a).GrindsThen R') : (p.bind f).GrindsThen R' := by
  intro l b k h
  rcases after_bind_cases f h with ⟨q, hq, hqk⟩ | ⟨a, l₁, l₂, -, -, -, h₂⟩
  · cases q with
    | ret a => exact hf a [] b k (by simpa [after, bind] using hqk.symm)
    | grind b' k₀ =>
      simp only [bind, grind.injEq] at hqk
      obtain ⟨rfl, rfl⟩ := hqk
      have hs := hp l _ _ hq
      cases k₀ with
      | sample k₁ => trivial
      | ret a => exact hR a hs
      | _ => exact hs.elim
    | _ => simp [bind] at hqk
  · exact hf a l₂ b k h₂

/-- A program with no proof of work. -/
theorem grindsThen_of_noGrind {p : VerifierProgram α} {R : α → Prop}
    (h : ∀ l b k, p.after l ≠ some (grind b k)) : p.GrindsThen R :=
  fun l b k hl ↦ absurd hl (h l b k)

theorem grindsThen_ret (a : α) (R : α → Prop) : (ret a).GrindsThen R :=
  grindsThen_of_noGrind fun l b k ↦ by cases l <;> simp [after]

/-- A whole program whose grinds are each followed by a challenge inside it. -/
theorem GrindsThen.grindThenSample {P : VerifierProgram α} (hP : P.GrindsThen fun _ ↦ False) :
    GrindThenSample P := by
  intro l b k h
  have hs := hP l b k h
  cases k with
  | sample k' => exact ⟨k', rfl⟩
  | ret a => exact hs.elim
  | _ => exact hs.elim

end VerifierProgram

end
end LeanVM.Protocol.Compile
