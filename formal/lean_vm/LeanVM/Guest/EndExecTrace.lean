module

public import LeanVM.Guest.Mode.ResRef
public import Statement.LeanVm

/-!
# The executor along a reference run: its trace and the reference's part of each step

`Trace prog img s`: the executor's registers at `s` are the reference run's after `s.steps` steps,
from the initial state (`run_add` composes runs). `trace_next`: a step the executor takes along the
reference, moded, keeps it. `refOk_of_trace`: at a state on the trace and on the reference run, the
reference's part of the instruction's modedness (`RefOk`) holds when the reference's frames are
powers below `2^κ` (`FramesIn`) and its `KECCAK`s have their blocks in windows
(`KeccakBlocksInWindows`): a `MUL` holds (`ref_mul`), a `DEREF`'s pointer is a power below `2^κ` (the
reference reads through it), a taken `JUMP`'s frame is the next frame of the run, and a `KECCAK`'s
blocks lie in windows at the executor's frame, the reference reading each block's first cell.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Runs composed -/

theorem run_add {κ : ℕ} (prog : LeanIsaProgram) (M : MemoryImage κ) :
    ∀ (a b : ℕ) (r : Registers K), run prog M (a + b) r = (run prog M a r).bind (run prog M b)
  | 0, b, r => by rw [Nat.zero_add, run_zero]; rfl
  | a + 1, b, r => by
    rw [show a + 1 + b = (a + b) + 1 by omega, run_succ, run_succ]
    split_ifs
    · rfl
    · simp only [Option.bind_eq_bind, Option.bind_assoc]
      congr 1
      funext r1
      exact run_add prog M a b r1

/-- Every `KECCAK` of a run's suffix has its blocks in windows, if every one of the run's does. -/
theorem windows_drop {κ : ℕ} (prog : LeanIsaProgram) (M : MemoryImage κ) :
    ∀ (a b : ℕ) (r r' : Registers K), keccakBlocksInWindowsInRun prog M (a + b) r →
      run prog M a r = some r' → keccakBlocksInWindowsInRun prog M b r'
  | 0, b, r, r', h, hr => by
    rw [run_zero, Option.some.injEq] at hr
    subst hr
    rwa [Nat.zero_add] at h
  | a + 1, b, r, r', h, hr => by
    rw [run_succ] at hr
    split_ifs at hr
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨r1, hs, hr⟩ := hr
    have hf : ∃ ins, prog.fetch r.pc = some ins := by
      cases hf : prog.fetch r.pc with
      | none => rw [Semantics.step, hf] at hs; cases hs
      | some ins => exact ⟨ins, rfl⟩
    obtain ⟨ins, hf⟩ := hf
    rw [show a + 1 + b = (a + b) + 1 by omega] at h
    simp only [keccakBlocksInWindowsInRun, hf, hs] at h
    exact windows_drop prog M a b r1 r' h.2 hr

/-! ## The trace -/

/-- **The executor's registers are the reference run's** after its steps. -/
def Trace (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (s : St) : Prop :=
  run prog img s.steps Registers.initial = some ⟨g ^ s.pc, g ^ s.fp⟩

/-- **The reference's frames are powers below `2^κ`**: every state of the reference run's first
`n` steps. -/
def FramesIn (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (n : ℕ) : Prop :=
  ∀ k ≤ n, ∀ r, run prog img k Registers.initial = some r → ∃ j < 2 ^ κ, r.fp = g ^ j

/-- The reference's step at a state on its run: the instruction there, decoded as the executor's,
its operands small, executed to the next registers, from which the run goes on. -/
theorem ref_step {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hC : Ctx.of prog adv = .ok C) {s : St} (hon : OnRef prog img n s) {op : Op}
    (hop : C.ops[s.pc]? = some op) :
    ∃ (hpc2 : s.pc < 2 ^ prog.logSize) (r1 : Registers K),
      OpOf (prog.instructions ⟨s.pc, hpc2⟩) op ∧ OpSmall op ∧
      (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog ∧
      prog.fetch (g ^ s.pc) = some (prog.instructions ⟨s.pc, hpc2⟩) ∧
      executeWith img.read ⟨g ^ s.pc, g ^ s.fp⟩ (prog.instructions ⟨s.pc, hpc2⟩) = some r1 ∧
      run prog img (n - s.steps - 1) r1 = some (Registers.final prog) := by
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
  obtain ⟨r1, hstep, hrun1⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  exact ⟨hpc2, r1, hdec, hsm, hne, prog.fetch_gpow ⟨s.pc, hpc2⟩, hstep, by rw [hk]; exact hrun1⟩

/-- **A step along the reference keeps the trace**: an instruction the executor runs, moded, at a
state on the reference run and on the trace. -/
theorem trace_next {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s' : St} {op : Op} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) (htr : Trace prog img s) (hop : C.ops[s.pc]? = some op)
    (hmo : OpModed (refMem img) s op) (e : runOp C s op = .ok s') :
    Trace prog img { s' with steps := s'.steps + 1 } := by
  obtain ⟨hsize, -⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  obtain ⟨hpc2, r1, hdec, hsm, hne, -, hstep, hrun1⟩ := ref_step hC hon hop
  have hpc : s.pc < C.ops.size := hsize ▸ hpc2
  obtain ⟨s2, e2, d2⟩ := runOp_complete hs (refRd_img hκ img) hdec hsm hpc hsz
    (nextOk_of_run hsize hrun1) hstep hmo
  rw [e] at e2
  cases e2
  unfold Trace at htr ⊢
  dsimp only
  rw [d2.steps, run_add, htr, Option.bind_some, run_succ_of_ne_final hne,
    step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute, hstep, ← d2.regs]
  rfl

/-! ## The reference's part of a step -/

theorem read_index {κ : ℕ} {img : MemoryImage κ} {a : K} {v : E} (h : img.read a = some v) :
    ∃ i : Fin (2 ^ κ), a = g ^ i.val ∧ img i = v := by
  unfold MemoryImage.read at h
  cases hi : addressIndex? κ a with
  | none => rw [hi] at h; cases h
  | some i =>
    rw [hi, Option.map_some, Option.some.injEq] at h
    refine ⟨i, ?_, h⟩
    unfold addressIndex? at hi
    split_ifs at hi with hex
    rw [Option.some.injEq] at hi
    subst hi
    exact Classical.choose_spec hex

/-- A window of the statement's at an address the reference reads, as the executor's. -/
theorem inWindow_of_read {κ fp k cells : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {v : E}
    (hfp : fp < maxCells) (hk : k < 2 ^ 28) (hr : img.read (g ^ fp * g ^ k) = some v)
    (hw : InKeccakWindow κ (g ^ fp * g ^ k) cells) : InWindow (fp + k) cells := by
  obtain ⟨i, hi, -⟩ := read_index hr
  have hai : addressIndex? κ (g ^ fp * g ^ k) = some i :=
    (gLog?_spec (by omega)).mpr hi
  have h := hw i hai
  rw [← pow_add] at hi
  have hi' : (i : ℕ) < 2 ^ 64 - 1 := by
    have := i.isLt
    have : 2 ^ κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
    omega
  have hm : fp + k < 2 ^ 64 - 1 := by unfold maxCells at hfp; omega
  have := gpow_injOn hm hi' hi
  unfold InWindow
  rw [this]
  exact h

theorem readCells_some {read : K → Option E} {fp : K} {offset : Fin 13 → K} {x : Fin 13 → E}
    (h : readCells read fp offset = some x) (c : Fin 13) : ∃ v, read (fp * offset c) = some v := by
  unfold readCells at h
  have hc : c ∈ List.finRange 13 := List.mem_finRange c
  generalize List.finRange 13 = l at h hc
  induction l generalizing x with
  | nil => cases hc
  | cons a l ih =>
    simp only [List.foldr_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, rest, hrest, -⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨v, hv⟩
    · exact ih hrest hc

theorem readFirstCells_some {read : K → Option E} {fp : K} {offset : Fin 13 → K} {count : ℕ}
    {x : Fin 13 → E} (h : readFirstCells read fp offset count = some x) (c : Fin 13)
    (hlt : c.val < count) : ∃ v, read (fp * offset c) = some v := by
  unfold readFirstCells at h
  have hc : c ∈ List.finRange 13 := List.mem_finRange c
  generalize List.finRange 13 = l at h hc
  induction l generalizing x with
  | nil => cases hc
  | cons a l ih =>
    simp only [List.foldr_cons] at h
    split_ifs at h with ha
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v, hv, rest, hrest, -⟩ := h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨v, hv⟩
      · exact ih hrest hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd hlt ha
      · exact ih h hc

/-- **The reference's part of each step**, at a state on the reference run and on the trace, the
reference's frames powers below `2^κ` and its `KECCAK` blocks in windows. -/
theorem refOk_of_trace {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ}
    {C : Ctx} (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) (hfr : FramesIn prog img n)
    (hwin : (⟨κ, img, n⟩ : Execution prog).KeccakBlocksInWindows) {s : St}
    (hs : Fine (refMem img) s) (hon : OnRef prog img n s) (htr : Trace prog img s) {op : Op}
    (hop : C.ops[s.pc]? = some op) : RefOk (refMem img) s op := by
  have hrd := refRd_img hκ img
  have hκ28 : 2 ^ κ ≤ maxCells := Nat.pow_le_pow_right (by norm_num) hκ
  obtain ⟨hpc2, r1, hdec, hsm, hne, hfetch, hstep, hrun1⟩ := ref_step hC hon hop
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hdec hstep hfetch
  cases op with
  | mul a b c => exact (ref_mul hκ hC hs hon hop).symm
  | deref a o c mode =>
    cases ins <;> simp only [OpOf] at hdec
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
    obtain ⟨p, hp, -, -, v3, -, v2, hv2, -⟩ := hstep
    obtain ⟨-, hMp⟩ := hrd.at hs.fp hsm.1 hp
    obtain ⟨i, hi, -⟩ := read_index hv2
    exact ⟨i, lt_of_lt_of_le i.isLt hκ28, by rw [hMp]; exact hi⟩
  | jump c d f =>
    cases ins <;> simp only [OpOf] at hdec
    obtain ⟨rfl, rfl, rfl⟩ := hdec
    have hr : run prog img (s.steps + 1) Registers.initial = some r1 := by
      rw [run_add, htr, Option.bind_some, run_succ_of_ne_final hne, step_of_fetch_eq_some hfetch,
        LeanVM.Semantics.execute, hstep]
      rfl
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
    obtain ⟨vc, hc, vd, -, vf, hf, -, -, hr1⟩ := hstep
    obtain ⟨-, hMc⟩ := hrd.at hs.fp hsm.1 hc
    obtain ⟨-, hMf⟩ := hrd.at hs.fp hsm.2.2 hf
    intro hnz
    rw [hMc] at hnz
    simp only [Option.pure_def, Option.some.injEq, hnz, ↓reduceIte] at hr1
    have hlt := hon.1
    obtain ⟨j, hj, hfj⟩ := hfr (s.steps + 1) (by omega) r1 hr
    refine ⟨j, lt_of_lt_of_le hj hκ28, ?_⟩
    rw [hMf, ← hfj, ← hr1]
  | keccak L out inOdd outOdd count =>
    cases ins <;> simp only [OpOf] at hdec
    rename_i om otail ob8 ocap oout inOdd' outOdd' outCells
    obtain ⟨rfl, rfl, rfl, rfl, l, rfl, hl⟩ := hdec
    have hstep1 : Semantics.step prog img ⟨g ^ s.pc, g ^ s.fp⟩ = some r1 := by
      rw [step_of_fetch_eq_some hfetch, LeanVM.Semantics.execute]; exact hstep
    have hw : keccakBlocksInWindowsInRun prog img (n - s.steps) ⟨g ^ s.pc, g ^ s.fp⟩ :=
      windows_drop prog img s.steps (n - s.steps) _ _ (by rw [Nat.add_sub_cancel' hon.1.le]; exact hwin)
        htr
    rw [show n - s.steps = (n - s.steps - 1) + 1 by have := hon.1; omega] at hw
    simp only [keccakBlocksInWindowsInRun, hfetch, hstep1] at hw
    obtain ⟨⟨w4, w9, wo⟩, -⟩ := hw
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
    obtain ⟨input, hin, output, hout, -⟩ := hstep
    have hlL : l.length = 13 := by rw [← hl.length_eq, List.length_finRange]
    have hoff : ∀ c : Fin 13, g ^ (l.toArray.getD c.val 0) = keccakInputCellOffset om otail ob8 ocap c := by
      intro c
      have h1 := forall₂_getElem hl (i := c.val) (by simp) (by rw [hlL]; exact c.isLt)
      simp only [List.getElem_finRange, Fin.cast_mk] at h1
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by rw [hlL]; exact c.isLt), Option.getD_some]
      exact h1
    have hsmall : ∀ c : Fin 13, l.toArray.getD c.val 0 < 2 ^ 28 := fun c ↦ by
      refine hsm.1 _ ?_
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by rw [hlL]; exact c.isLt), Option.getD_some, List.toList_toArray]
      exact List.getElem_mem _
    have e4 : otail = g ^ (l.toArray.getD 4 0) := by
      rw [hoff ⟨4, by decide⟩]; simp [keccakInputCellOffset]
    have e9 : ocap = g ^ (l.toArray.getD 9 0) := by
      rw [hoff ⟨9, by decide⟩]; simp [keccakInputCellOffset]
    obtain ⟨v4, hv4⟩ := readCells_some hin ⟨4, by decide⟩
    obtain ⟨v9, hv9⟩ := readCells_some hin ⟨9, by decide⟩
    obtain ⟨vo, hvo⟩ := readFirstCells_some hout ⟨0, by decide⟩ (cellCount_pos outCells)
    rw [← hoff ⟨4, by decide⟩] at hv4
    rw [← hoff ⟨9, by decide⟩] at hv9
    simp only [pow_zero, one_mul] at hvo
    rw [e4] at w4
    rw [e9] at w9
    exact ⟨inWindow_of_read hκ hs.fp (hsmall ⟨4, by decide⟩) hv4 w4,
      inWindow_of_read hκ hs.fp (hsmall ⟨9, by decide⟩) hv9 w9,
      inWindow_of_read hκ hs.fp hsm.2 hvo wo⟩
  | xor a b c => trivial
  | set o k => trivial

end

end LeanVM.Guest.EndExec
