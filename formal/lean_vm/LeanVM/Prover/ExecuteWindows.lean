module

public import LeanVM.Prover.ExecuteSound
public import Statement.LeanVm

/-!
# The executor's `KECCAK`s have their blocks in windows

`execute_keccakBlocksInWindows`: an execution the executor returns has every `KECCAK` it runs with
its blocks in windows (`Execution.KeccakBlocksInWindows`), since `runOp` checks each block's cells
(`keccakWindows`) before it reads or writes one, and faults otherwise. The run on the final image
is the executor's, step by step (`loop_spec`), so each `KECCAK` of the run is one the executor
checked, at the same frame.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A window check that passes: the cell lies below `maxCells`, and its `cells` cells in one window. -/
theorem inWindow_ok {fp off cells : ℕ} (h : inWindow fp off cells = .ok ()) :
    fp + off < maxCells ∧ (fp + off) % keccakWindow + cells ≤ keccakWindow := by
  simp only [inWindow, bind_ok] at h
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨rfl, hlt⟩ := cellAt_ok hc
  split_ifs at h with hw
  exact ⟨hlt, by omega⟩

/-- The executor's window, as the statement's: the address `g^fp · g^k` of a cell below
`maxCells` whose `cells` cells lie in one window. -/
theorem inKeccakWindow_of {κ fp k cells : ℕ} (hκ : κ < 64) (hlt : fp + k < maxCells)
    (hw : (fp + k) % keccakWindow + cells ≤ keccakWindow) :
    InKeccakWindow κ (g ^ fp * g ^ k) cells := by
  intro i hi
  rw [Option.mem_def, gLog?_spec hκ, ← pow_add] at hi
  have hi' : (i : ℕ) < 2 ^ 64 - 1 := by
    have := i.isLt
    have : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm : fp + k < 2 ^ 64 - 1 := lt_of_lt_of_le hlt (by unfold maxCells; norm_num)
  have := gpow_injOn hm hi' hi
  rw [← this]
  exact hw

/-- A `KECCAK` the executor runs passed its window check, at the frame it runs in. -/
theorem runOp_keccak_windows {C : Ctx} {s s' : St} {ins : Array ℕ} {out : ℕ} {inOdd outOdd : Bool}
    {count : ℕ} (e : runOp C s (.keccak ins out inOdd outOdd count) = .ok s') :
    keccakWindows s.fp ins out count = .ok () := by
  simp only [runOp, bind_ok] at e
  obtain ⟨u, hu, -⟩ := e
  cases u
  exact hu

/-- **A step's instruction has its blocks in windows**, at the step's frame. -/
theorem windowsAt_of_step {C : Ctx} {s s1 : St} {ins : LeanIsaInstruction} {κ : ℕ} (hκ : κ < 64)
    (hs : s.Good) (hins : ∀ op, C.ops[s.pc]? = some op → OpOf ins op) (e : step C s = .ok s1) :
    KeccakBlocksInWindowsAt κ (g ^ s.fp) ins := by
  simp only [step, bind_ok] at e
  obtain ⟨s2, h2, e⟩ := e
  rw [mapError_ok] at h2
  have f := hints_follows _ s s2 hs h2
  split at e
  · rename_i op hop
    rw [bind_ok] at e
    obtain ⟨s3, h3, -⟩ := e
    rw [mapError_ok] at h3
    have hoo := hins op hop
    cases ins with
    | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
      cases op with
      | keccak L out inOdd' outOdd' count =>
        obtain ⟨-, -, rfl, rfl, l, rfl, hl⟩ := hoo
        have hw := runOp_keccak_windows h3
        rw [f.fp] at hw
        simp only [keccakWindows, bind_ok] at hw
        obtain ⟨u1, h41, u2, h42, h43⟩ := hw
        cases u1; cases u2
        have hlL : l.length = 13 := by rw [← hl.length_eq, List.length_finRange]
        have hoff : ∀ c : Fin 13, g ^ (l.toArray.getD c.val 0) =
            keccakInputCellOffset om otail ob8 ocap c := by
          intro c
          have h1 := forall₂_getElem hl (i := c.val) (by simp) (by rw [hlL]; exact c.isLt)
          simp only [List.getElem_finRange, Fin.cast_mk] at h1
          rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
            List.getElem?_eq_getElem (by rw [hlL]; exact c.isLt), Option.getD_some]
          exact h1
        have e4 : otail = g ^ (l.toArray.getD 4 0) := by
          rw [hoff ⟨4, by decide⟩]; simp [keccakInputCellOffset]
        have e9 : ocap = g ^ (l.toArray.getD 9 0) := by
          rw [hoff ⟨9, by decide⟩]; simp [keccakInputCellOffset]
        obtain ⟨a4, b4⟩ := inWindow_ok h41
        obtain ⟨a9, b9⟩ := inWindow_ok h42
        obtain ⟨ao, bo⟩ := inWindow_ok h43
        refine ⟨?_, ?_, ?_⟩
        · rw [e4]; exact inKeccakWindow_of hκ a4 b4
        · rw [e9]; exact inKeccakWindow_of hκ a9 b9
        · exact inKeccakWindow_of hκ ao bo
      | _ => exact absurd hoo (by simp [OpOf])
    | _ => trivial
  · simp at e

/-- By induction on the fuel: every `KECCAK` of the run from a state, over the steps the loop takes,
has its blocks in windows, on every final memory extending the loop's last state. -/
theorem loop_windows {prog : LeanIsaProgram} {C : Ctx} (hsize : C.ops.size = 2 ^ prog.logSize)
    (hdec : ∀ (i : ℕ) (hi : i < 2 ^ prog.logSize) (hi' : i < C.ops.size),
      OpOf (prog.instructions ⟨i, hi⟩) C.ops[i]) (n : ℕ) :
    ∀ (s sf : St), s.Good → s.mem.Sound → s.fp < maxCells → s.pc ≤ C.ops.size → loop C n s = .ok sf →
      ∀ (M : Mem) {κ : ℕ} (img : MemoryImage κ), κ < 64 → sf.mem ≤ M → Final M img.read →
        keccakBlocksInWindowsInRun prog img (sf.steps - s.steps) ⟨g ^ s.pc, g ^ s.fp⟩ := by
  induction n with
  | zero =>
    intro s sf hs hS hfp hpc e
    rw [loop.eq_def] at e
    dsimp only at e
    split_ifs at e with hh
    · simp only [pure_ok] at e; subst e
      intro M κ img _ _ _
      rw [Nat.sub_self]
      trivial
  | succ n ih =>
    intro s sf hs hS hfp hpc e
    rw [loop.eq_def] at e
    dsimp only at e
    split_ifs at e with hh hout
    · simp only [pure_ok] at e; subst e
      intro M κ img _ _ _
      rw [Nat.sub_self]
      trivial
    rw [bind_ok] at e
    obtain ⟨s1, h1, e⟩ := e
    have hpc' : s.pc < C.ops.size := by
      have : 1 ≤ C.ops.size := hsize ▸ Nat.one_le_two_pow
      omega
    have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc'
    have hins : ∀ op, C.ops[s.pc]? = some op → OpOf (prog.instructions ⟨s.pc, hpc2⟩) op :=
      fun op hop ↦ by
        obtain ⟨h, rfl⟩ := Array.getElem?_eq_some_iff.mp hop
        exact hdec s.pc hpc2 h
    have sp := step_spec (ins := prog.instructions ⟨s.pc, hpc2⟩) hs hfp hpc' hins h1
    obtain ⟨-, -, le1, k, hk, -⟩ := loop_spec hsize hdec n s1 sf sp.good (step_sound hs hS h1) sp.fp
      sp.pc e
    have hrest := ih s1 sf sp.good (step_sound hs hS h1) sp.fp sp.pc e
    intro M κ img hκ hM hF
    have hsteps : sf.steps - s.steps = (sf.steps - s1.steps) + 1 := by rw [hk, sp.steps]; omega
    rw [hsteps]
    simp only [keccakBlocksInWindowsInRun]
    rw [prog.fetch_gpow ⟨s.pc, hpc2⟩, step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩),
      LeanVM.Semantics.execute, sp.exec M img.read (Mem.le_trans le1 hM) hF]
    exact ⟨windowsAt_of_step hκ hs hins h1, hrest M img hκ hM hF⟩

/-- **The executor's executions have their `KECCAK` blocks in windows**: for every program, hint
list and stream. -/
theorem execute_keccakBlocksInWindows {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice}
    {t : Execution prog} (h : execute prog input adv = .ok t) : t.KeccakBlocksInWindows := by
  simp only [execute, bind_ok] at h
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨hsize, hdec⟩ := ctx_of_spec hC
  split_ifs at h with hmf
  · simp [bind_ok] at h
  simp only [bind_ok] at h
  obtain ⟨mem, hmem, s, hloop, h⟩ := h
  simp only [pure_ok] at h; subst h
  rw [mapError_ok, exbind_ok] at hmem
  obtain ⟨m1, hm1, hmem⟩ := hmem
  have hA0 : Agree ⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ (fun _ ↦ 0) :=
    ⟨⟨⟨fun c k h ↦ by simp [Mem.cellOf] at h, fun c h ↦ by simp [Mem.cellOf] at h⟩,
      fun c v h ↦ by simp [Mem.get] at h, fun c d k h ↦ by simp [Mem.cellOf] at h,
      fun c k h ↦ by simp [Mem.cellOf] at h, rfl,
      show max adv.mainFrame 2 ≤ maxCells by unfold maxCells at hmf ⊢; omega⟩,
      fun p hp ↦ by simp at hp⟩
  have hS1 := hA0.self.put (by unfold maxCells; norm_num) hm1
  have hS2 := hS1.put (by unfold maxCells; norm_num) hmem
  obtain ⟨le1, -, -⟩ := Mem.put_ok hA0.wf hm1
  obtain ⟨le2, -, -⟩ := Mem.put_ok hS1.wf hmem
  obtain ⟨gs, hSf, les, -, -, -⟩ := loop_spec hsize hdec maxSteps _ s
    ⟨hS2.wf, Dlog.ok_empty.grow _⟩ hS2 (by unfold maxCells; norm_num) (Nat.zero_le _) hloop
  have hu2 : 2 ≤ s.mem.used :=
    le_trans (le_max_right _ _) (le_trans le1.used (le_trans le2.used les.used))
  obtain ⟨-, -, -, hκ28⟩ := image_log hu2 hSf.used
  have hF := final_image gs.wf hu2 hSf.used fun p hp ↦ (hSf.links p hp).1
  have hw := loop_windows hsize hdec maxSteps _ s ⟨hS2.wf, Dlog.ok_empty.grow _⟩ hS2
    (by unfold maxCells; norm_num) (Nat.zero_le _) hloop s.mem s.mem.image.snd
    (lt_of_le_of_lt hκ28 (by norm_num)) (Mem.le_refl _) hF
  have hinit : (Registers.initial : Registers K) = ⟨g ^ 0, g ^ 0⟩ := by rw [pow_zero]; rfl
  show keccakBlocksInWindowsInRun prog s.mem.image.snd s.steps Registers.initial
  rw [hinit]
  exact hw

end

end LeanVM.Prover.Exec
