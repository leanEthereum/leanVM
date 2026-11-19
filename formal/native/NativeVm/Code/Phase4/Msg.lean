module

public import NativeVm.Code.Phase4.Step
public import NativeVm.Code.Phase4.Model

/-!
# A round's message

`msgC_spec`: the message (`msgOf`) at `oMSG`, from the three scalars read after its first entry.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {s : QState} {E : QState → Prop}

/-- `claim + sumE #[x1, x2]` on limbs. -/
theorem claim_sum_limbs (c x1 x2 : EW) :
    c + sumE #[x1, x2] = ⟨c.c0 ^^^ x1.c0 ^^^ x2.c0, c.c1 ^^^ x1.c1 ^^^ x2.c1⟩ := by
  show EW.add c (EW.add (EW.add 0 x1) x2) = _
  simp only [EW.add]
  congr 1 <;> simp [UInt64.xor_assoc, show EW.c0 0 = 0 from rfl, show EW.c1 0 = 0 from rfl]

/-- The three elements of an array in memory. -/
theorem EWArr.three {mem : UInt64 → Option UInt64} {w : UInt64} {j : Nat} {x0 x1 x2 : EW}
    (h : EWArr mem (wd w j) #[x0, x1, x2]) :
    mem (wd w j) = some x0.c0 ∧ mem (wd w (j + 1)) = some x0.c1 ∧
      mem (wd w (j + 2)) = some x1.c0 ∧ mem (wd w (j + 3)) = some x1.c1 ∧
      mem (wd w (j + 4)) = some x2.c0 ∧ mem (wd w (j + 5)) = some x2.c1 := by
  have e0 := h 0 (by simp)
  have e1 := h 1 (by simp)
  have e2 := h 2 (by simp)
  simp only [EWAt, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, wd_wd]
    at e0 e1 e2
  exact ⟨by simpa using e0.1, e0.2, e1.1, e1.2, e2.1, e2.2⟩

/-- **The message** at `oMSG`, from the three scalars after its first entry. -/
theorem msgC_spec {w : UInt64} (claim x0 x1 x2 : EW) (hbp : s.reg .rbp = wd w 0)
    (hc0 : s.mem (wd w oCLM) = some claim.c0) (hc1 : s.mem (wd w (oCLM + 1)) = some claim.c1)
    (hx : EWArr s.mem (wd w (oMSG + 2)) #[x0, x1, x2])
    (hs : ∀ k, oMSG ≤ k → k < oMSG + 4 → (s.mem (wd w k)).isSome) :
    WP msgC s (fun s' ↦ EWArr s'.mem (wd w oMSG) (msgOf claim #[x0, x1, x2]) ∧
      Wr w (fun k ↦ oMSG ≤ k ∧ k < oMSG + 4) s s' ∧ RegsFrame [.rax, .rcx] s s') E := by
  obtain ⟨a0, a1, b0, b1, d0, d1⟩ := EWArr.three hx
  wnorm at hc0 hc1 a0 a1 b0 b1 d0 d1
  unfold msgC
  wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst; wst
  wdone
  refine ⟨?_, by wr_tac, by rfw⟩
  have hm : msgOf claim #[x0, x1, x2] = #[x0, claim + sumE #[x1, x2], x1, x2] := rfl
  rw [hm, claim_sum_limbs]
  intro i hi
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
  rw [wd_wd]
  interval_cases i <;> refine EWAt.of ?_ ?_ <;> fin_w

end NativeVm.Code.P4
