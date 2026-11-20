module

public import LeanVM.Guest.Mode.ResRef
public import LeanVM.Guest.WalkWindows

/-!
# The reference's `XOR` and a power's divisor

`ref_xor`: on the reference an `XOR` holds (`ROp`); `nz_gpow`: a divisor holding a power of `g` is
nonzero.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Core
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Uniqueness on the reference -/

section

variable {M : ℕ → E} {fp : ℕ}

end

/-! ## Nonzero divisors -/

/-- The reference's words at frame `fp` satisfy instruction `ins` (an `XOR` or a `MUL`). -/
def ROp (M : ℕ → E) (fp : ℕ) : OffsetInstruction → Prop
  | .xor a b c => M (fp + c) = M (fp + a) + M (fp + b)
  | .mul a b c => M (fp + c) = M (fp + a) * M (fp + b)
  | _ => True

/-- **The reference's `XOR`**: at a state on the reference run whose instruction is
`[c] = [a] + [b]`, the reference's words satisfy it. -/
theorem ref_xor {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) {a b c : ℕ} (hop : C.ops[s.pc]? = some (.xor a b c)) :
    refMem img (s.fp + c) = refMem img (s.fp + a) + refMem img (s.fp + b) := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, -⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  cases ins <;> simp only [OpOf] at hdec
  obtain ⟨rfl, rfl, rfl⟩ := hdec
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨vA, hA, vB, hB, vC, hC', hg⟩ := hstep
  simp [guard] at hg
  obtain ⟨rfl, -⟩ := hg
  obtain ⟨ha, hb, hc⟩ := hsm
  rw [((refRd_img hκ img).at hs.fp ha hA).2, ((refRd_img hκ img).at hs.fp hb hB).2,
    ((refRd_img hκ img).at hs.fp hc hC').2]

end

end LeanVM.Guest.Mode
