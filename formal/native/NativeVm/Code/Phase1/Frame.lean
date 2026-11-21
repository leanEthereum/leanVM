module

public import NativeVm.Code.Phase1.Code

/-!
# What phase 1's code keeps after reading

`LFr p s s'`: from `s` to `s'`, `rdi` and `r14` kept, every word outside the layout's `490` words
at `p` kept (`InL`), and which words exist. Each store to a layout word and each register write
but `rdi`'s and `r14`'s keeps it (`LFr.setMem`, `LFr.setReg`); blocks that store nothing keep it by
their register frames (`LFr.of_regs`). Also the word-level facts the proofs share: conditions on
wrapped subtraction (`geu_sub`), `test`, and the words of a number.
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native
open NativeVm.Transcript (wd wd_inj toNat_toUInt64)

/-- A word of the layout at `p`. -/
def InL (p a : UInt64) : Prop := ∃ k < 490, a = wd p k

/-- Every layout word exists. -/
def LDom (p : UInt64) (mem : UInt64 → Option UInt64) : Prop := ∀ k < 490, (mem (wd p k)).isSome

/-- What the code after reading keeps. -/
structure LFr (p : UInt64) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  r14 : s'.reg .r14 = s.reg .r14
  mem : ∀ a, ¬ InL p a → s'.mem a = s.mem a
  dom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome

variable {p : UInt64} {s s₁ s₂ s₃ : QState}

theorem LFr.refl (p : UInt64) (s : QState) : LFr p s s := ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ ↦ rfl⟩

theorem LFr.trans (h₁ : LFr p s₁ s₂) (h₂ : LFr p s₂ s₃) : LFr p s₁ s₃ :=
  ⟨h₂.rdi.trans h₁.rdi, h₂.r14.trans h₁.r14, fun a ha ↦ (h₂.mem a ha).trans (h₁.mem a ha),
    fun a ↦ (h₂.dom a).trans (h₁.dom a)⟩

theorem LFr.setReg (h : LFr p s s₁) {r : Reg64} (h1 : r ≠ .rdi) (h2 : r ≠ .r14) (v : UInt64) :
    LFr p s (s₁.setReg r v) :=
  ⟨by simp [Ne.symm h1, h.rdi], by simp [Ne.symm h2, h.r14], fun a ha ↦ h.mem a ha, h.dom⟩

theorem LFr.isSome (h : LFr p s s₁) (hd : LDom p s.mem) {k : Nat} (hk : k < 490) :
    (s₁.mem (wd p k)).isSome := by rw [h.dom]; exact hd k hk

theorem LFr.setMem (h : LFr p s s₁) (hd : LDom p s.mem) {k : Nat} (hk : k < 490) (v : UInt64) :
    LFr p s (s₁.setMem (wd p k) v) := by
  refine ⟨h.rdi, h.r14, fun a ha ↦ ?_, fun a ↦ ?_⟩
  · rw [QState.setMem_mem, ite_eq_right_iff.mpr fun e ↦ absurd ⟨k, hk, e⟩ ha]; exact h.mem a ha
  · rw [QState.setMem_mem]
    split
    · subst a; rw [← h.dom]; exact (h.isSome hd hk).symm ▸ rfl
    · exact h.dom a

theorem LFr.of_regs {rs : List Reg64} (hm : s₁.mem = s.mem) (hf : RegsFrame rs s s₁)
    (h1 : .rdi ∉ rs) (h2 : .r14 ∉ rs) : LFr p s s₁ :=
  ⟨hf _ h1, hf _ h2, fun a _ ↦ by rw [hm], fun a ↦ by rw [hm]⟩

theorem LDom.of_fr (hd : LDom p s.mem) (h : LFr p s s₁) : LDom p s₁.mem := fun _ hk ↦ h.isSome hd hk

/-- Close `LFr p s s'` for `s'` register and layout-word updates of `s`. -/
syntax "fr_tac" term : tactic

macro_rules
  | `(tactic| fr_tac $hd) => `(tactic| (
      repeat (first
        | refine LFr.setReg ?_ (by decide) (by decide) _
        | refine LFr.setMem ?_ $hd (by omega) _)
      first | exact LFr.refl _ _ | assumption))

/-! ## Words -/

/-- A condition on a register holding `x - d`, wrapped: `k ≤ x - d` exactly when `x` is not in
`d .. d + k - 1`. -/
theorem geu_sub {x d k : Nat} (hx : x < 2 ^ 64) (hd : d < 2 ^ 64) (hk : k + d ≤ 2 ^ 64) :
    decide (k ≤ (x.toUInt64 - d.toUInt64).toNat) = !decide (d ≤ x ∧ x < d + k) := by
  rw [UInt64.toNat_sub, toNat_toUInt64 hx, toNat_toUInt64 hd]
  by_cases h : d ≤ x ∧ x < d + k
  · simp only [h, and_self, decide_true, Bool.not_true, decide_eq_false_iff_not, not_le]
    omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]
    omega

theorem cond_test_self (r : Reg64) (s : QState) :
    (Cond.test false r (.reg r)).eval s = !(s.reg r == 0) := by
  simp only [Cond.eval, Rhs.eval, UInt64.and_self]
  cases s.reg r == 0 <;> rfl

theorem toUInt64_and {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 &&& b.toUInt64 = (a &&& b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_toUInt64 ha, toNat_toUInt64 hb,
    toNat_toUInt64 (lt_of_le_of_lt Nat.and_le_left ha)]

theorem toUInt64_eq_zero {a : Nat} (ha : a < 2 ^ 64) : (a.toUInt64 == 0) = decide (a = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, toNat_toUInt64 ha]
  rfl

theorem toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x := UInt64.ofNat_toNat

end NativeVm.Code.Phase1
