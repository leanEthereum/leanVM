module

public import NativeVm.Code.Phase7.RingWsetup

/-!
# `weightRing`'s second part: the placement's equality weight

`ringAbove`: `Placement.eqAbove ⟨vc, index⟩ x` (the selector's bits against the coordinates of `x`
from `vc` on, `selLoop`) into the buffer's words `6`, `7`; it leaves the buffer's base in `r13`.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- `eqAbove` into the buffer's words `6`, `7`. -/
def ringAbove : Stmt := blk [
  I (.mov .r13 .rbx), I (.mov .rax .rdx), minReg .rax .rbp, I (.sub .rbp .rax), I (.shli .rax 4),
  I (.add .r14 .rax), shiftLoop, I (.movi .r9 1), I (.movi .r10 0), selLoop,
  I (.store (at_ .r13 (wdisp 6)) .r9), I (.store (at_ .r13 (wdisp 7)) .r10)]

theorem eqAbove_min (X : List E) (vc idx : Nat) :
    Placement.eqAbove ⟨vc, idx⟩ X = eqEval (selectorPoint (idx >>> vc) (X.length - min vc X.length))
      (X.drop (min vc X.length)) := by
  unfold Placement.eqAbove
  rcases Nat.le_total vc X.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_length, Nat.sub_self,
      Nat.sub_eq_zero_of_le h]

/-- **`ringAbove` stores `eqAbove`.** -/
theorem ringAbove_spec {X : List E} {b xp : UInt64} {vc idx : Nat}
    (hbx : s.reg .rbx = b) (h14 : s.reg .r14 = xp) (hbp : s.reg .rbp = X.length.toUInt64)
    (hsi : s.reg .rsi = idx.toUInt64) (hdx : s.reg .rdx = vc.toUInt64) (hX : EArr s.mem xp X)
    (hXl : X.length < 2 ^ 32) (hvc : vc < 2 ^ 64) (hidx : idx < 2 ^ 64)
    (h6 : (s.mem (ew b 6)).isSome) (h7 : (s.mem (ew b 7)).isSome) :
    WP ringAbove s (fun u ↦ u.reg .r13 = b ∧ EW u.mem b 3 (Placement.eqAbove ⟨vc, idx⟩ X) ∧
      ∀ a, a ≠ ew b 6 → a ≠ ew b 7 → u.mem a = s.mem a) F := by
  set w := min vc X.length with hw
  unfold ringAbove
  fstep; fstep
  refine WP.then (minReg_spec (x := vc) (y := X.length) (by rsimp; exact hdx) (by rsimp; exact hbp)
    hvc (by omega)) fun t1 e1 ↦ ?_
  subst e1
  fstep; fstep; fstep
  refine WP.then shiftLoop_spec fun t2 ⟨h2s, h2m, h2f⟩ ↦ ?_
  have t2_14 : t2.reg .r14 = ew xp (2 * w) := by
    rw [h2f .r14 (by simp)]; rsimp; rw [h14, shl4, add16]
  have t2_bp : t2.reg .rbp = (X.drop w).length.toUInt64 := by
    rw [h2f .rbp (by simp)]; rsimp; rw [hbp, toUInt64_sub (by omega), List.length_drop]
  have t2_13 : t2.reg .r13 = b := by rw [h2f .r13 (by simp)]; rsimp; exact hbx
  have t2_si : (t2.reg .rsi).toNat = idx >>> vc := by
    rw [h2s]; rsimp; rw [hsi, hdx, toNat_toUInt64 hidx, toNat_toUInt64 hvc]
  fstep; fstep
  refine WP.then (selLoop_spec (ys := X.drop w) (by rsimp; exact t2_14)
    (by rsimp; rw [h2m]; exact Ring.EArr.drop hX (by omega)) (by rsimp; exact t2_bp)
    (by rw [List.length_drop]; omega)) fun t3 ⟨e3, m3, f3⟩ ↦ ?_
  rsimp at e3 m3
  have t3_13 : t3.reg .r13 = b := by rw [f3 .r13 (by simp)]; rsimp; exact t2_13
  refine wp_store (eval_w t3_13 6) (by rw [m3, h2m]; exact h6) ?_
  refine wp_store (eval_w t3_13 7) (isSome_setMem (by rw [m3, h2m]; exact h7) _ _) ?_
  fdone
  have he : eOf (t3.reg .r9) (t3.reg .r10) = Placement.eqAbove ⟨vc, idx⟩ X := by
    rw [e3, eOf_one, one_mul, t2_si, List.length_drop, eqAbove_min]
  obtain ⟨v0, v1⟩ := eOf_eq_iff.mp he
  refine ⟨t3_13, ⟨?_, ?_⟩, fun a h6' h7' ↦ ?_⟩
  · simp (disch := omega) only [setMem_ew, Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, v0]
  · simp (disch := omega) only [setMem_ew, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, v1]
  · simp only [QState.setMem_mem, h6', h7', ↓reduceIte, m3, h2m, QState.setReg_mem]

end NativeVm.Code.Ring
