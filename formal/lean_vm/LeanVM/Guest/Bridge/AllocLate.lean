/-
  LeanVM.Guest.Bridge.AllocLate

  The late hints' buffers: every `allocLate` sizes the buffer of an earlier `allocAdvice`, by that
  buffer's size cell, decided by the kernel over every compiled function the allocation check admits.
-/

module

public import LeanVM.Guest.Bridge.AllocAdv
public import LeanVM.Guest.Bridge.AllocChk.All
public import LeanVM.Guest.Bridge.AllocCur

/-!
# The late hints' buffers

`lateChk F fs`: each `allocLate` of a function is of an exponent's size, its pointer that of the
`k`-th buffer hint, an `allocAdvice` at an earlier offset, the body's `k`-th top-level allocation atom
an `allocDyn` whose size value's cell, in the frame (`allocCellOk`), is the late hint's. `lateChk_all`:
every compiled function the allocation check admits passes it. `lateChk_get` reads it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Each late hint sizes an earlier advised buffer by its size cell.** -/
noncomputable def lateChk (F : FnAl) (fs : ℕ) : Bool :=
  (allocHints F.d).all fun q ↦ match q.2 with
    | .allocLate p (.exp c) => ((topAllocs F.body).zip (bufsOf F.X F.d)).any fun x ↦ decide (x.2.1 < q.1) &&
        match x.1, x.2.2 with
        | .allocDyn _ nv, .allocAdvice p' _ => Nat.beq p' p && Nat.beq (F.X.locAt nv.idx) c && allocCellOk F.X fs nv
        | _, _ => false
    | .allocLate _ (.cells _) => false
    | _ => true

end

public section


theorem lateChk_all : ∀ j < nFns, j ∈ AllocChk.allocExcl ∨ lateChk (fnAl j) (B2C.fsN j) = true := by
  decide +kernel

/-- **What `lateChk` gives at a late hint**: its size an exponent's at the cell of the size value of
the `k`-th atom, an `allocDyn`, whose buffer hint is an `allocAdvice` at its pointer, at an earlier
offset. -/
theorem lateChk_get {F : FnAl} {fs : ℕ} (h : lateChk F fs = true) {ol p : ℕ} {b : Prover.Exec.BufSize}
    (hq : (ol, Prover.Exec.Hint.allocLate p b) ∈ allocHints F.d) :
    ∃ (c k o : ℕ) (S : String) (d nv : V), b = .exp c ∧ (topAllocs F.body)[k]? = some (Core.Hint.allocDyn d nv) ∧
      (bufsOf F.X F.d)[k]? = some (o, Prover.Exec.Hint.allocAdvice p S) ∧ o < ol ∧ F.X.locAt nv.idx = c ∧
      allocCellOk F.X fs nv = true := by
  have hq' := List.all_eq_true.mp h _ hq
  rcases b with c | c
  · simp at hq'
  dsimp only at hq'
  obtain ⟨⟨a, o, hh⟩, hx, hx'⟩ := List.any_eq_true.mp hq'
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  rw [List.getElem?_zip_eq_some] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx'
  obtain ⟨ho, hm⟩ := hx'
  split at hm
  next d nv p' S =>
    simp only [Bool.and_eq_true, Nat.beq_eq] at hm
    obtain ⟨⟨rfl, hc⟩, hcell⟩ := hm
    exact ⟨c, k, o, S, d, nv, rfl, hk.1, hk.2, ho, hc, hcell⟩
  next => cases hm

end

end LeanVM.Guest.Bridge
