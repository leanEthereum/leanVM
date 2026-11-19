module

public import NativeVm.Code.Phase4.Base
public import NativeVm.Equiv.Field

/-!
# The field kernels on the model's words

`NativeVm.Field`'s kernels speak of `E` (`eOf`, `EArr`); here they speak of `EW` (`EWArr`, an
element as its two limbs in registers), as phase 4's invariants do: `emulW`, `edotW`,
`epolyEvalW`, `epowersW`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters
open NativeVm.Equiv

/-- `A`'s element: `r9`, `r10`. -/
abbrev regA (s : QState) : EW := ⟨s.reg .r9, s.reg .r10⟩

/-- `B`'s element: `r11`, `r12`. -/
abbrev regB (s : QState) : EW := ⟨s.reg .r11, s.reg .r12⟩

theorem toE_eq_eOf (x : EW) : x.toE = eOf x.c0 x.c1 := rfl

/-- Two limbs are an element when their values are. -/
theorem ew_of_eOf {a b : UInt64} {x : EW} (h : eOf a b = x.toE) : (⟨a, b⟩ : EW) = x :=
  EW.toE_injective h

variable {s : QState} {E : QState → Prop}

/-- **`emul`**: `A := A · B`. -/
theorem emulW (s : QState) :
    WP emul s (fun s' ↦ regA s' = regA s * regB s ∧ s'.mem = s.mem ∧ RegsFrame eRegs s s') E :=
  WP.mono (emul_spec s) (fun _ ⟨h, hm, hr⟩ ↦ ⟨ew_of_eOf (by rw [EW.toE_mul]; exact h), hm, hr⟩)
    fun _ h ↦ h

/-- **`edot`**: `A := dot xs ys`, `xs` at `r13`, `ys` at `r14`. -/
theorem edotW {xs ys : Array EW} (hx : EWArr s.mem (s.reg .r13) xs)
    (hy : EWArr s.mem (s.reg .r14) ys) (hl : ys.size = xs.size)
    (hn : s.reg .r15 = xs.size.toUInt64) (hlen : xs.size < 2 ^ 64) :
    WP edot s (fun s' ↦ regA s' = dot xs ys ∧ s'.mem = s.mem ∧ RegsFrame arrRegs s s') E := by
  refine WP.mono (edot_spec (xs := xs.toList.map EW.toE) (ys := ys.toList.map EW.toE)
    (EWArr_iff_EArr.mp hx) (EWArr_iff_EArr.mp hy) (by simpa using hl) (by simpa using hn)
    (by simpa using hlen)) (fun _ ⟨h, hm, hr⟩ ↦ ⟨ew_of_eOf ?_, hm, hr⟩) fun _ h ↦ h
  rw [toE_dot]; exact h

/-- **`epolyEval`**: `A := polyEval cs B`, `cs` at `r13`. -/
theorem epolyEvalW {cs : Array EW} (hc : EWArr s.mem (s.reg .r13) cs)
    (hn : s.reg .r15 = cs.size.toUInt64) (hlen : cs.size < 2 ^ 64) :
    WP epolyEval s (fun s' ↦ regA s' = polyEval cs (regB s) ∧ s'.mem = s.mem ∧
      RegsFrame polyRegs s s') E := by
  refine WP.mono (epolyEval_spec (cs := cs.toList.map EW.toE) (EWArr_iff_EArr.mp hc)
    (by simpa using hn) (by simpa using hlen)) (fun _ ⟨h, hm, hr⟩ ↦ ⟨ew_of_eOf ?_, hm, hr⟩)
    fun _ h ↦ h
  rw [toE_polyEval]; exact h

theorem ew_wd (w : UInt64) (a k : Nat) : ew (wd w a) k = wd w (a + k) := wd_add w a k

/-- **`epowers`**: `powers B n` to the words from `wd w a`. -/
theorem epowersW {w : UInt64} {a n : Nat} (h14 : s.reg .r14 = wd w a) (h15 : s.reg .r15 = n.toUInt64)
    (hlen : n < 2 ^ 60) (hdom : ∀ k < 2 * n, (s.mem (wd w (a + k))).isSome) :
    WP epowers s (fun s' ↦ EWArr s'.mem (wd w a) (powers (regB s) n) ∧
      (∀ x, (∀ k < 2 * n, x ≠ wd w (a + k)) → s'.mem x = s.mem x) ∧ RegsFrame powRegs s s') E := by
  refine WP.mono (epowers_spec h14 h15 hlen fun k hk ↦ by rw [ew_wd]; exact hdom k hk)
    (fun _ ⟨h, hm, _, hr⟩ ↦ ⟨?_, fun x hx ↦ hm x fun k hk ↦ by rw [ew_wd]; exact hx k hk, hr⟩)
    fun _ h ↦ h
  rw [EWArr_iff_EArr, toList_map_powers]
  exact h

/-- A slice of an array in memory. -/
theorem EWArr.extract {mem : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {xs : Array EW}
    (h : EWArr mem (wd w a) xs) (i j : Nat) : EWArr mem (wd w (a + 2 * i)) (xs.extract i j) := by
  intro k hk
  rw [Array.size_extract] at hk
  rw [Array.getElem_extract, wd_wd, show a + 2 * i + 2 * k = a + 2 * (i + k) by omega, ← wd_wd]
  exact h (i + k) (by omega)

end NativeVm.Code.P4
