module

public import NativeVm.Code.Phase3.EOps

/-!
# Copying and summing elements of the working area

`copyE`: `r15` elements from `r13` to `r14` (`copyE_spec`); `esum`: `A := Σ` of `r15` elements
from `r13` (`esum_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {s : QState} {E : QState → Prop} {w : UInt64}

/-- Copy `r15` elements from `r13` to `r14`, through `rax`. -/
def copyE : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .rax (at_ .r13 0)), I (.store (at_ .r14 0) .rax),
  I (.load .rax (at_ .r13 8)), I (.store (at_ .r14 8) .rax),
  I (.addi .r13 16), I (.addi .r14 16), I (.subi .r15 1)])

/-- The registers `copyE` writes. -/
abbrev copyRegs : List Reg64 := [.rax, .r13, .r14, .r15]

theorem ewArr_extract_succ {m : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {j : Nat}
    (hj : j < xs.size) (h : EWArr m p (xs.extract 0 j)) (hx : EWAt m (wd p (2 * j)) xs[j]) :
    EWArr m p (xs.extract 0 (j + 1)) := by
  intro i hi
  simp only [Array.size_extract] at hi
  simp only [Array.getElem_extract, Nat.zero_add]
  by_cases hij : i < j
  · have := h i (by simp; omega)
    simpa using this
  · have e : i = j := by omega
    subst e
    exact hx

/-- **`copyE`** copies `n` elements of `xs` from word `a` to word `b`, the two ranges apart. -/
theorem copyE_spec {xs : Array EW} {a b n : Nat} (hn : n ≤ xs.size) (h13 : s.reg .r13 = wd w a)
    (h14 : s.reg .r14 = wd w b) (h15 : s.reg .r15 = n.toUInt64) (hx : EWArr s.mem (wd w a) xs)
    (hap : a + 2 * n ≤ b ∨ b + 2 * n ≤ a) (hlim : a + 2 * n < 2 ^ 60 ∧ b + 2 * n < 2 ^ 60)
    (hdom : ∀ k < 2 * n, (s.mem (wd w (b + k))).isSome) :
    WP copyE s (fun s' ↦ EWArr s'.mem (wd w b) (xs.extract 0 n) ∧
      (∀ a', (∀ k < 2 * n, a' ≠ wd w (b + k)) → s'.mem a' = s.mem a') ∧
      (∀ a', (s'.mem a').isSome = (s.mem a').isSome) ∧ RegsFrame copyRegs s s') E := by
  unfold copyE
  refine WP.loop (fun t ↦ ∃ j ≤ n, t.reg .r13 = wd w (a + 2 * j) ∧ t.reg .r14 = wd w (b + 2 * j) ∧
      t.reg .r15 = (n - j).toUInt64 ∧ EWArr t.mem (wd w b) (xs.extract 0 j) ∧
      (∀ a', (∀ k < 2 * n, a' ≠ wd w (b + k)) → t.mem a' = s.mem a') ∧
      (∀ a', (t.mem a').isSome = (s.mem a').isSome) ∧ RegsFrame copyRegs s t)
    (fun t ↦ (t.reg .r15).toNat) ⟨0, Nat.zero_le _, by simpa using h13, by simpa using h14,
      by simpa using h15, fun i hi ↦ absurd hi (by simp), fun _ _ ↦ rfl, fun _ ↦ rfl,
      fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro t ⟨j, hj, h13', h14', h15', harr, hout, hsome, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hjn : j < n := by
      by_contra hh
      exact hne (by rw [h15', show n - j = 0 by omega]; rfl)
    have hsrc : ∀ k < 2 * n, t.mem (wd w (a + k)) = s.mem (wd w (a + k)) := fun k hk ↦
      hout _ fun k' hk' e ↦ by
        rw [wd_inj (by omega) (by omega)] at e
        omega
    have hx0 := hx j (by omega)
    have hj1 : 2 * j + 1 < 2 * n := by omega
    rw [EWAt, wd_wd, wd_wd] at hx0
    have hdb0 : (t.mem (wd w (b + 2 * j))).isSome := by rw [hsome]; exact hdom _ (by omega)
    have hdb1 : (t.mem (wd w (b + 2 * j + 1))).isSome := by
      rw [hsome, Nat.add_assoc]; exact hdom _ (by omega)
    have ne01 : wd w (b + 2 * j + 1) ≠ wd w (b + 2 * j) := fun e ↦ by
      rw [wd_inj (by omega) (by omega)] at e; omega
    have nab : wd w (a + 2 * j + 1) ≠ wd w (b + 2 * j) := fun e ↦ by
      rw [wd_inj (by omega) (by omega)] at e; omega
    have l0 : t.mem (wd w (a + 2 * j)) = some (xs[j]'(by omega)).c0 := (hsrc _ (by omega)).trans hx0.1
    have l1 : t.mem (wd w (a + 2 * j + 1)) = some (xs[j]'(by omega)).c1 := by
      rw [Nat.add_assoc, hsrc _ hj1, ← Nat.add_assoc]; exact hx0.2
    have ev0 : ∀ (q : QState) (r : Reg64) (c : Nat), q.reg r = wd w c → (at_ r 0).eval q = wd w c :=
      fun q r c h ↦ by rw [Transcript.eval_at, h, Field.int64Zero_toUInt64, UInt64.add_zero]
    have ev8 : ∀ (q : QState) (r : Reg64) (c : Nat), q.reg r = wd w c →
        (at_ r 8).eval q = wd w (c + 1) := fun q r c h ↦ by
      rw [Transcript.eval_at, h, show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add]
    refine wp_load (ev0 _ _ _ h13') l0 ?_
    refine wp_store (ev0 _ _ _ (by rsimp; exact h14')) (by rsimp; exact hdb0) ?_
    refine wp_load (ev8 _ _ _ (by rsimp; exact h13'))
      (by rw [QState.setMem_mem]; simp only [nab, ↓reduceIte, QState.setReg_mem]; exact l1) ?_
    refine wp_store (ev8 _ _ _ (by rsimp; exact h14'))
      (by simp only [QState.setReg_mem, QState.setMem_mem, ne01, ↓reduceIte]; exact hdb1) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl
      (WP.blk_nil ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)))
    · rsimp
      rw [h13', show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
    · rsimp
      rw [h14', show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
    · rsimp
      rw [h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub]
    · refine ewArr_extract_succ (by omega) (fun i hi ↦ ?_) ?_
      · simp only [Array.size_extract] at hi
        have := harr i (by simpa using hi)
        rw [EWAt, wd_wd, wd_wd] at this ⊢
        have d1 : wd w (b + 2 * i) ≠ wd w (b + 2 * j + 1) := fun e ↦ by
          rw [wd_inj (by omega) (by omega)] at e; omega
        have d2 : wd w (b + 2 * i) ≠ wd w (b + 2 * j) := fun e ↦ by
          rw [wd_inj (by omega) (by omega)] at e; omega
        have d3 : wd w (b + 2 * i + 1) ≠ wd w (b + 2 * j + 1) := fun e ↦ by
          rw [wd_inj (by omega) (by omega)] at e; omega
        have d4 : wd w (b + 2 * i + 1) ≠ wd w (b + 2 * j) := fun e ↦ by
          rw [wd_inj (by omega) (by omega)] at e; omega
        simp only [QState.setReg_mem, QState.setMem_mem, d1, d2, d3, d4, ↓reduceIte]
        exact this
      · rw [EWAt, wd_wd, wd_wd]
        simp only [QState.setReg_mem, QState.setMem_mem, Ne.symm ne01, ↓reduceIte]
        rsimp
        simp
    · intro a' ha'
      have h1 := ha' (2 * j) (by omega)
      have h2 := ha' (2 * j + 1) (by omega)
      rw [← Nat.add_assoc] at h2
      simp only [QState.setReg_mem, QState.setMem_mem, h1, h2, ↓reduceIte]
      exact hout a' ha'
    · intro a'
      simp only [QState.setReg_mem, QState.setMem_mem]
      split
      · subst a'; rw [← hsome]; exact hdb1.symm
      · split
        · subst a'; rw [← hsome]; exact hdb0.symm
        · exact hsome a'
    · intro r hr
      simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨ha, h13r, h14r, h15r⟩ := hr
      rsimp
      simp only [ha, h13r, h14r, h15r, ↓reduceIte]
      exact hf r (by simp [copyRegs, ha, h13r, h14r, h15r])
    · rsimp
      rw [h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub,
        UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro t ⟨j, hj, -, -, h15', harr, hout, hsome, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have : j = n := by
      by_contra hh
      have := Field.toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) (h15' ▸ h0)
      omega
    subst this
    exact ⟨harr, hout, hsome, hf⟩

theorem extract_succ' {α : Type} (xs : Array α) (j : Nat) (h : j < xs.size) :
    xs.extract 0 (j + 1) = (xs.extract 0 j).push xs[j] := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_extract, Array.getElem_push, Array.size_extract, Nat.zero_add]
    split
    · rfl
    · simp only [Array.size_extract] at h1; congr 1; omega

/-- `A := A + Σ` of `r15` elements from `r13`, left to right. -/
def esum : Stmt := blk [
  .loop (.test false .r15 (.reg .r15)) (blk [
    I (.load .rax (at_ .r13 0)), I (.xor .r9 .rax),
    I (.load .rax (at_ .r13 8)), I (.xor .r10 .rax),
    I (.addi .r13 16), I (.subi .r15 1)])]

/-- The registers `esum` writes. -/
abbrev sumRegs : List Reg64 := [.rax, .r9, .r10, .r13, .r15]

/-- **`esum`** adds the first `n` elements of `xs` to `A`, left to right. -/
theorem esum_spec {xs : Array EW} {a n : Nat} (hn : n ≤ xs.size) (h13 : s.reg .r13 = wd w a)
    (h15 : s.reg .r15 = n.toUInt64) (hx : EWArr s.mem (wd w a) xs) (hlim : a + 2 * n < 2 ^ 60) :
    WP esum s (fun s' ↦ (⟨s'.reg .r9, s'.reg .r10⟩ : EW) =
        (xs.extract 0 n).foldl (· + ·) ⟨s.reg .r9, s.reg .r10⟩ ∧
      s'.mem = s.mem ∧ RegsFrame sumRegs s s') E := by
  unfold esum
  refine WP.blk_cons ?_
  refine WP.mono (P := fun s' ↦ (⟨s'.reg .r9, s'.reg .r10⟩ : EW) =
      (xs.extract 0 n).foldl (· + ·) ⟨s.reg .r9, s.reg .r10⟩ ∧
      s'.mem = s.mem ∧ RegsFrame sumRegs s s') ?_ (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  refine WP.loop (fun t ↦ ∃ j ≤ n, t.reg .r13 = wd w (a + 2 * j) ∧ t.reg .r15 = (n - j).toUInt64 ∧
      (⟨t.reg .r9, t.reg .r10⟩ : EW) = (xs.extract 0 j).foldl (· + ·) ⟨s.reg .r9, s.reg .r10⟩ ∧
      t.mem = s.mem ∧ RegsFrame sumRegs s t)
    (fun t ↦ (t.reg .r15).toNat) ⟨0, Nat.zero_le _, by simpa using h13, by simpa using h15,
      by simp, rfl, fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro t ⟨j, hj, h13', h15', hsum, hm, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hjn : j < n := by
      by_contra hh
      exact hne (by rw [h15', show n - j = 0 by omega]; rfl)
    have hx0 := hx j (by omega)
    rw [EWAt, wd_wd, wd_wd] at hx0
    refine wp_load (by rw [Transcript.eval_at, h13', Field.int64Zero_toUInt64, UInt64.add_zero])
      (by rw [hm]; exact hx0.1) ?_
    refine wp_reg rfl ?_
    have ev : (at_ .r13 8).eval ((t.setReg .rax (xs[j]'(by omega)).c0).setReg .r9
        ((t.setReg .rax (xs[j]'(by omega)).c0).reg .r9 ^^^
          (t.setReg .rax (xs[j]'(by omega)).c0).reg .rax)) = wd w (a + 2 * j + 1) := by
      rw [Transcript.eval_at]; rsimp
      rw [h13', show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add]
    refine wp_load ev (by rsimp; rw [hm]; exact hx0.2) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (WP.blk_nil ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)))
    · rsimp; rw [h13', show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
    · rsimp; rw [h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub]
    · rsimp
      rw [extract_succ' xs j (by omega), Array.foldl_push, ← hsum]
      rfl
    · exact hm
    · intro r hr
      simp only [sumRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨ha, h9, h10, h13r, h15r⟩ := hr
      rsimp
      simp only [ha, h9, h10, h13r, h15r, ↓reduceIte]
      exact hf r (by simp [sumRegs, ha, h9, h10, h13r, h15r])
    · rsimp
      rw [h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub,
        UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro t ⟨j, hj, -, h15', hsum, hm, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have : j = n := by
      by_contra hh
      have := Field.toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) (h15' ▸ h0)
      omega
    subst this
    exact ⟨hsum, hm, hf⟩

end NativeVm.Code.P3
