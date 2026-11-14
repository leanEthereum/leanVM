/-
  LeanVM.Guest.EndExecCDeref

  `DerefPow` at the `DEREF`s of offset `0`, from the reference step alone; what is left is the `DEREF`s of a nonzero offset.
-/

module

public import LeanVM.Guest.EndExecX

/-!
# A `DEREF`'s pointer on the reference

The reference step at a `DEREF` with offset `o` reads the word at `p · g^o`, `p` its pointer cell's first limb, so `p · g^o = g^i` for some `i < 2^κ ≤ 2^28`. At `o = 0` (the range checks' and touches' reads, the frame copies through a frame pointer at offset `0`) this is `p = g^i`, a power below `2^62` (`powWord_deref0`). At `o ≠ 0` it gives `p = g^(i - o)` only when `i ≥ o`: a pointer `g^(-m)` would read the same word, and nothing about the reference memory alone excludes it, so `DerefPowNZ` is left open: a pointer of a `DEREF` with a nonzero offset (a buffer's base, a callee frame, a `match` selector) is a power below `2^62` on the reference.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- **A `DEREF`'s pointer is a power at a nonzero offset**, on the reference, at each state of the
tracks. -/
def DerefPowNZ (Y : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s a o c mode, OnRun (XOf Y) r s →
    C.ops[s.pc]? = some (.deref a o c mode) → o ≠ 0 → PowWord (refMem r.img (s.fp + a))

end

public section

/-- **A `DEREF` at offset `0` reads through a power**: the reference step reads the word its
pointer names, an address `g^i`, `i < 2^κ`. -/
theorem powWord_deref0 {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) {a c : ℕ} {mode : DerefMode} (hop : C.ops[s.pc]? = some (.deref a 0 c mode)) :
    PowWord (refMem img (s.fp + a)) := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  obtain ⟨r1, k, -, -, hstep, -⟩ := onRef_step hon
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  have hrd := refRd_img hκ img
  cases ins <;> simp only [OpOf] at hdec
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨p, hp1, -, -, v3, -, v2, hv2, -⟩ := hstep
  rw [(hrd.at hs.fp hsm.1 hp1).2]
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp hv2
  have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  refine ⟨i, by omega, ?_⟩
  simpa using hi

/-- **`DerefPow` from the nonzero offsets.** -/
theorem derefPow_of {Y : Ref → St → Prop} (h : DerefPowNZ Y) : DerefPow Y := by
  intro r hr C hC s a o c mode hon hop
  by_cases ho : o = 0
  · subst ho
    exact powWord_deref0 (logMemorySize_le_28 (e := r.exec) hr.size) hC hon.2.1 hon.2.2 hop
  · exact h r hr C hC s a o c mode hon hop ho

end

end LeanVM.Guest.EndExec
