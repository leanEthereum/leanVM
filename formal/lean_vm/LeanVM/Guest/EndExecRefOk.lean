/-
  LeanVM.Guest.EndExecRefOk

  The reference's part of each instruction's modedness (`RefOk`) from the reference step: a
  `DEREF`'s pointer and a taken `JUMP`'s frame, powers of `g` below `2^62`, are below `maxCells`.
-/

module

public import LeanVM.Guest.EndExec

/-!
# `RefOk` from the reference step

`RefOk` asks a `DEREF`'s pointer and a taken `JUMP`'s frame to be `g^b`, `b < maxCells`. The reference
step reads a cell past each: the `DEREF` the cell its pointer names past its offset, and the step
after a taken `JUMP` a cell of its new frame (`step_reads`), or the run halts in frame `g^0`. A read
names a cell below `2^κ ≤ 2^28`, so a word `g^e`, `e < 2^62` (`PowWord`), read past an offset below
`2^28` has `e < 2^28` (`pow_lt_of_read`). `refOk_of_pow`: so `RefOk` holds wherever those words are
such powers (`PtrPow`), which is what the honest memory's pointer cells hold.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- A word whose first limb is `g^e`, `e < 2^62`. -/
def PowWord (v : E) : Prop := ∃ e < 2 ^ 62, v.limb 0 = Parameters.g ^ e

/-- **The pointers an instruction follows are powers**: a `DEREF`'s pointer, a taken `JUMP`'s
frame. -/
def PtrPow (M : ℕ → E) (s : St) : Op → Prop
  | .deref a _ _ _ => PowWord (M (s.fp + a))
  | .jump c _ f => M (s.fp + c) ≠ 0 → PowWord (M (s.fp + f))
  | _ => True

/-- A power `g^e`, `e < 2^62`, read past an offset below `2^28` in a memory of at most `2^28`
words, is below `maxCells`. -/
theorem pow_lt_of_read {κ : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {w : E} (hw : PowWord w) {o : ℕ}
    (ho : o < 2 ^ 28) {v : E} (hr : img.read (w.limb 0 * Parameters.g ^ o) = some v) :
    ∃ b < maxCells, w.limb 0 = Parameters.g ^ b := by
  obtain ⟨e, he, hwe⟩ := hw
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp hr
  have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [hwe, ← pow_add] at hi
  have := gpow_inj (by omega) (by omega) hi
  exact ⟨e, by unfold maxCells; omega, hwe⟩

/-- **A step reads a cell of its frame**, past an offset below `2^28`. -/
theorem step_reads {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (hC : Ctx.of prog adv = .ok C)
    {κ : ℕ} {img : MemoryImage κ} {r r' : Registers K} (h : step prog img r = some r') :
    ∃ o < 2 ^ 28, ∃ v, img.read (r.fp * Parameters.g ^ o) = some v := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  cases hf : prog.fetch r.pc with
  | none => rw [step_eq_none_of_fetch_eq_none hf] at h; cases h
  | some ins =>
  obtain ⟨i, -, hi⟩ := prog.fetch_eq_some_iff.mp hf
  rw [step_of_fetch_eq_some hf, LeanVM.Semantics.execute] at h
  have hi' : (i : ℕ) < C.ops.size := by rw [hsize]; exact i.isLt
  have hdec := hdecC i i.isLt hi'
  have hsm := ctx_small hC i hi'
  rw [Fin.eta, hi] at hdec
  generalize C.ops[(i : ℕ)] = op at hdec hsm
  cases ins <;> cases op <;> simp only [OpOf] at hdec
  · obtain ⟨rfl, -, -⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨_, hsm.1, v, hv⟩
  · obtain ⟨rfl, -, -⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨_, hsm.1, v, hv⟩
  · obtain ⟨rfl, -⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨_, hsm, v, hv⟩
  · obtain ⟨rfl, -, -, -⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨_, hsm.1, v, hv⟩
  · obtain ⟨rfl, -, -⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨_, hsm.1, v, hv⟩
  · obtain ⟨-, -, -, -, l, rfl, hl⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨input, hin, -⟩ := h
    rw [List.finRange_succ] at hl
    obtain ⟨k, l', hk, -, rfl⟩ := List.forall₂_cons_left_iff.mp hl
    unfold readCells at hin
    rw [List.finRange_succ, List.foldr_cons] at hin
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hin
    obtain ⟨v, hv, -⟩ := hin
    rw [← hk] at hv
    exact ⟨k, hsm.1 k (by simp), v, hv⟩

/-- **`RefOk` from the reference step**, the pointers it follows powers below `2^62`. -/
theorem refOk_of_pow {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ}
    {C : Ctx} (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) {op : Op} (hop : C.ops[s.pc]? = some op)
    (hp : PtrPow (refMem img) s op) : RefOk (refMem img) s op := by
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
  have hne : (⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ : Registers K) ≠ Registers.final prog :=
    fun h ↦ by rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, hrest⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  have hrd := refRd_img hκ img
  cases op with
  | deref a o c mode =>
    cases ins <;> simp only [OpOf] at hdec
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
    obtain ⟨p, hp1, -, -, v3, -, v2, hv2, -⟩ := hstep
    have hpM := (hrd.at hs.fp hsm.1 hp1).2
    change PowWord (refMem img (s.fp + a)) at hp
    show ∃ b < maxCells, (refMem img (s.fp + a)).limb 0 = Parameters.g ^ b
    rw [hpM] at hp ⊢
    exact pow_lt_of_read hκ hp hsm.2.1 hv2
  | jump c d f =>
    cases ins <;> simp only [OpOf] at hdec
    obtain ⟨rfl, rfl, rfl⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
    obtain ⟨vc, hc, vd, -, vf, hf, -, -, e⟩ := hstep
    intro hnz
    change refMem img (s.fp + c) ≠ 0 → PowWord (refMem img (s.fp + f)) at hp
    have hcM := (hrd.at hs.fp hsm.1 hc).2
    have hfM := (hrd.at hs.fp hsm.2.2 hf).2
    rw [hcM] at hnz hp
    rw [hfM] at hp ⊢
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnz)] at e
    obtain rfl : (⟨vd.limb 0, vf.limb 0⟩ : Registers K) = r1 := Option.some.inj e
    cases k with
    | zero =>
      have h1 : vf.limb 0 = fpFinal := congrArg Registers.fp (Option.some.inj hrest)
      exact ⟨0, by unfold maxCells; norm_num, by rw [h1, pow_zero]⟩
    | succ k =>
      have hne1 : (⟨vd.limb 0, vf.limb 0⟩ : Registers K) ≠ Registers.final prog :=
        fun h ↦ by rw [run_succ, ite_eq_left h] at hrest; cases hrest
      rw [run_succ_of_ne_final hne1, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrest
      obtain ⟨r2, hstep2, -⟩ := hrest
      obtain ⟨o, ho, v, hv⟩ := step_reads hC hstep2
      exact pow_lt_of_read hκ (hp hnz) ho hv
  | _ => trivial

end

end LeanVM.Guest.EndExec
