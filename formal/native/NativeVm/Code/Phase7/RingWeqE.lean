module

public import NativeVm.Code.Phase7.RingRegs

/-!
# A stack point's equality weight

`weightEq`: `A := eqEval (pt ++ selectorPoint (index >>> vc) (stackLog - vc)) x`, the weight of a
column claim on the stack (`Placement.stackPoint`), `pt` at `r13` (`r15` elements), `x` at `r14`
(`rbp` elements), the placement's index and variable count in `rsi` and `rdx`, the stack's
log-size in `rcx`. The point's run (`eqLoop`), then the selector's (`selLoop`), each cut to the
coordinates `x` has (`eqEval_append_selector`). It writes no memory.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier

variable {s : QState} {F : QState → Prop}

/-- `A := eqEval (pt ++ selectorPoint (rsi >>> rdx) (rcx - rdx)) x`. -/
def weightEq : Stmt := blk [
  subSat .rcx .rdx, shiftLoop, minReg .r15 .rbp, I (.sub .rbp .r15), minReg .rbp .rcx,
  I (.movi .r9 1), I (.movi .r10 0), eqLoop, selLoop]

/-- **`weightEq` evaluates a stack point's equality weight.** -/
theorem weightEq_specE {pt x : List E} {idx vc sl : Nat}
    (hpt : EArr s.mem (s.reg .r13) pt) (hx : EArr s.mem (s.reg .r14) x)
    (h15 : s.reg .r15 = pt.length.toUInt64) (hbp : s.reg .rbp = x.length.toUInt64)
    (hsi : s.reg .rsi = idx.toUInt64) (hdx : s.reg .rdx = vc.toUInt64)
    (hcx : s.reg .rcx = sl.toUInt64) (hptl : pt.length < 2 ^ 59) (hxl : x.length < 2 ^ 59)
    (hidx : idx < 2 ^ 64) (hvc : vc < 2 ^ 64) (hsl : sl < 2 ^ 64) :
    WP weightEq s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      eqEval (pt ++ selectorPoint (idx >>> vc) (sl - vc)) x ∧ s'.mem = s.mem) F := by
  set n1 := min pt.length x.length with hn1
  set n2 := min (x.length - n1) (sl - vc) with hn2
  unfold weightEq
  refine WP.then (subSat_spec hcx hdx hsl hvc) fun t1 e1 ↦ ?_
  subst e1
  refine WP.then shiftLoop_spec fun t2 ⟨h2s, h2m, h2f⟩ ↦ ?_
  have g2 : ∀ r, r ≠ .rsi → r ≠ .rdx → t2.reg r = s.reg r ∨ r = .rcx := fun r h1 h2 ↦ by
    rw [h2f r (by simp [h1, h2])]
    by_cases h : r = .rcx
    · exact Or.inr h
    · left; rsimp; simp [h]
  have t2_15 : t2.reg .r15 = pt.length.toUInt64 := by
    rw [h2f .r15 (by simp)]; rsimp; exact h15
  have t2_bp : t2.reg .rbp = x.length.toUInt64 := by
    rw [h2f .rbp (by simp)]; rsimp; exact hbp
  have t2_cx : t2.reg .rcx = (sl - vc).toUInt64 := by
    rw [h2f .rcx (by simp)]; rsimp
  have t2_13 : t2.reg .r13 = s.reg .r13 := by rw [h2f .r13 (by simp)]; rsimp
  have t2_14 : t2.reg .r14 = s.reg .r14 := by rw [h2f .r14 (by simp)]; rsimp
  have t2_si : (t2.reg .rsi).toNat = idx >>> vc := by
    rw [h2s]; rsimp; rw [hsi, hdx, toNat_toUInt64 hidx, toNat_toUInt64 hvc]
  clear g2
  refine WP.then (minReg_spec t2_15 t2_bp (by omega) (by omega)) fun t3 e3 ↦ ?_
  subst e3
  fstep
  refine WP.then (minReg_spec (x := x.length - n1) (y := sl - vc) (by
      rsimp; rw [t2_bp, toUInt64_sub (by omega)]) (by rsimp; exact t2_cx) (by omega) (by omega))
    fun t4 e4 ↦ ?_
  subst e4
  fstep; fstep
  have hpt' : EArr s.mem (s.reg .r13) (pt.take n1) := Ring.EArr.take hpt n1
  have hx' : EArr s.mem (s.reg .r14) (x.take n1) := Ring.EArr.take hx n1
  have hl1 : (pt.take n1).length = n1 := by rw [List.length_take]; omega
  have hl2 : (x.take n1).length = n1 := by rw [List.length_take]; omega
  refine WP.then (eqLoop_spec (xs := pt.take n1) (ys := x.take n1) (p := s.reg .r13)
      (q := s.reg .r14) (by rsimp; exact t2_13) (by rsimp; exact t2_14) (by rsimp; rw [h2m]; exact hpt')
      (by rsimp; rw [h2m]; exact hx') (by rw [hl1, hl2]) (by rsimp; rw [hl1]) (by omega))
    fun t5 ⟨e5, _, h14', m5, f5⟩ ↦ ?_
  rsimp at e5 m5
  have hys : EArr t5.mem (ew (s.reg .r14) (2 * n1)) ((x.drop n1).take n2) := by
    rw [m5, h2m]
    exact Ring.EArr.take (Ring.EArr.drop hx (by omega)) n2
  have hyl : ((x.drop n1).take n2).length = n2 := by
    rw [List.length_take, List.length_drop]; omega
  refine WP.then (selLoop_spec (ys := (x.drop n1).take n2) (by rw [h14', hl1]) hys (by
      rw [f5 .rbp (by simp), hyl]; rsimp; rfl) (by omega))
    fun t6 ⟨e6, m6, _⟩ ↦ ?_
  fdone
  refine ⟨?_, m6.trans (m5.trans h2m)⟩
  have t5si : (t5.reg .rsi).toNat = idx >>> vc := by
    rw [f5 .rsi (by simp)]; rsimp; exact t2_si
  rw [e6, e5, eOf_one, one_mul, t5si, hyl, eqEval_append_selector]
  congr 3 <;> simp only [hn1, hn2, Nat.min_comm]

end NativeVm.Code.Ring
