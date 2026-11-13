module

public import LeanVM.Prover.ExecuteKeccak
import all Init.Data.Nat.Power2.Basic

/-!
# The executor is sound

`execute_sound`: an execution the executor returns is a valid execution of the program on the
public input, whatever the program, its hints and its streams. A step's hints keep its registers
and only extend the memory, and its instruction is a step of the ISA on every final memory
extending the state after it (`step_spec`); by induction on the loop's fuel, the run from the
initial state reaches the final state on the final image (`loop_spec`), whose links agree by the
executor's last check. The image's size is the least power of two covering `used`, between `2` and
`maxCells`.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

theorem runOp_spec {C : Ctx} {s s' : St} {ins : LeanIsaInstruction} {op : Op} (hs : s.Good)
    (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size) (hop : OpOf ins op)
    (e : runOp C s op = .ok s') : OpSpec ins C.ops.size s s' := by
  cases op <;> cases ins <;> simp only [OpOf] at hop
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact xor_spec hs hfp hpc e
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact mul_spec hs hfp hpc e
  · obtain ⟨rfl, rfl⟩ := hop; exact set_spec hs hfp hpc e
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hop; exact deref_spec hs hfp hpc e
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact jump_spec hs hfp hpc e
  · obtain ⟨rfl, rfl, rfl, rfl, l, rfl, hl⟩ := hop; exact keccak_spec hs hfp hpc hl e

/-- What a successful step gives. -/
structure StepSpec (ins : LeanIsaInstruction) (nops : ℕ) (s s' : St) : Prop where
  good : s'.Good
  le : s.mem ≤ s'.mem
  steps : s'.steps = s.steps + 1
  pc : s'.pc ≤ nops
  fp : s'.fp < maxCells
  exec : ∀ M rd, s'.mem ≤ M → Final M rd →
    executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ ins = some ⟨g ^ s'.pc, g ^ s'.fp⟩

theorem step_spec {C : Ctx} {s s' : St} {ins : LeanIsaInstruction} (hs : s.Good)
    (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size)
    (hins : ∀ op, C.ops[s.pc]? = some op → OpOf ins op) (e : step C s = .ok s') :
    StepSpec ins C.ops.size s s' := by
  simp only [step, bind_ok] at e
  obtain ⟨s1, h1, e⟩ := e
  rw [mapError_ok] at h1
  have f1 := hints_follows _ s s1 hs h1
  split at e
  · rename_i op hop
    rw [bind_ok] at e
    obtain ⟨s2, h2, e⟩ := e
    rw [mapError_ok] at h2
    simp only [pure_ok] at e; subst e
    have o := runOp_spec f1.good (by rw [f1.fp]; exact hfp) (by rw [f1.pc]; exact hpc)
      (hins op hop) h2
    refine ⟨⟨o.good.wf, o.good.dl⟩, Mem.le_trans f1.le o.le, by rw [o.steps, f1.steps], o.pc, o.fp,
      fun M rd hM hF ↦ ?_⟩
    have := o.exec M rd hM hF
    rw [f1.pc, f1.fp] at this
    exact this
  · simp at e

theorem gpow_lt (n : ℕ) (h : n < 2 ^ 30) : n < 2 ^ 64 - 1 :=
  lt_of_lt_of_le h (by norm_num)

/-- By induction on the fuel: the run from a state reaches the final state, on every final
memory extending the loop's last state. -/
theorem loop_spec {prog : LeanIsaProgram} {C : Ctx} (hsize : C.ops.size = 2 ^ prog.logSize)
    (hdec : ∀ (i : ℕ) (hi : i < 2 ^ prog.logSize) (hi' : i < C.ops.size),
      OpOf (prog.instructions ⟨i, hi⟩) C.ops[i]) (n : ℕ) :
    ∀ (s sf : St), s.Good → s.fp < maxCells → s.pc ≤ C.ops.size → loop C n s = .ok sf →
      sf.Good ∧ s.mem ≤ sf.mem ∧ ∃ k, sf.steps = s.steps + k ∧
        ∀ (M : Mem) {κ : ℕ} (img : MemoryImage κ), sf.mem ≤ M → Final M img.read →
          run prog img k ⟨g ^ s.pc, g ^ s.fp⟩ = some (Registers.final prog) := by
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have halt : ∀ s : St, s.Good → s.pc = C.ops.size - 1 ∧ s.fp = 0 →
      s.Good ∧ s.mem ≤ s.mem ∧ ∃ k, s.steps = s.steps + k ∧
        ∀ (M : Mem) {κ : ℕ} (img : MemoryImage κ), s.mem ≤ M → Final M img.read →
          run prog img k ⟨g ^ s.pc, g ^ s.fp⟩ = some (Registers.final prog) := by
    intro s hs hh
    refine ⟨hs, Mem.le_refl _, 0, rfl, fun M κ img _ _ ↦ ?_⟩
    rw [run_zero, hh.1, hh.2, hsize, pow_zero]
    rfl
  induction n with
  | zero =>
    intro s sf hs hfp hpc e
    rw [loop.eq_def] at e
    dsimp only at e
    split_ifs at e with hh
    · simp only [pure_ok] at e; subst e; exact halt s hs hh
  | succ n ih =>
    intro s sf hs hfp hpc e
    rw [loop.eq_def] at e
    dsimp only at e
    split_ifs at e with hh hout
    · simp only [pure_ok] at e; subst e; exact halt s hs hh
    rw [bind_ok] at e
    obtain ⟨s1, h1, e⟩ := e
    have hpc' : s.pc < C.ops.size := by
      have : 1 ≤ C.ops.size := hsize ▸ Nat.one_le_two_pow
      omega
    have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc'
    have sp := step_spec (ins := prog.instructions ⟨s.pc, hpc2⟩) hs hfp hpc' (fun op hop ↦ by
      obtain ⟨h, rfl⟩ := Array.getElem?_eq_some_iff.mp hop
      exact hdec s.pc hpc2 h) h1
    obtain ⟨g1, le1, k, hk, hrun⟩ := ih s1 sf sp.good sp.fp sp.pc e
    refine ⟨g1, Mem.le_trans sp.le le1, k + 1, by rw [hk, sp.steps]; omega,
      fun M κ img hM hF ↦ ?_⟩
    have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := by
      intro hr
      simp only [Registers.final, LeanIsaProgram.pcFinal, Registers.mk.injEq] at hr
      refine hh ⟨?_, ?_⟩
      · rw [hsize]
        exact gpow_injOn (gpow_lt _ (lt_of_lt_of_le hpc' hsz))
          (gpow_lt _ (by rw [← hsize]; omega)) hr.1
      · exact gpow_injOn (gpow_lt _ (lt_trans hfp (by unfold maxCells; norm_num)))
          (gpow_lt 0 (by norm_num)) (hr.2.trans (pow_zero g).symm)
    rw [run_succ_of_ne_final hne, step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩),
      LeanVM.Semantics.execute,
      sp.exec M img.read (Mem.le_trans le1 hM) hF]
    exact hrun M img hM hF

theorem ctx_of_spec {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (h : Ctx.of prog adv = .ok C) :
    C.ops.size = 2 ^ prog.logSize ∧ ∀ (i : ℕ) (hi : i < 2 ^ prog.logSize) (hi' : i < C.ops.size),
      OpOf (prog.instructions ⟨i, hi⟩) C.ops[i] := by
  simp only [Ctx.of, bind_ok, pure_ok] at h
  obtain ⟨ops, hops, rfl⟩ := h
  have hf := exMapM_ok _ _ _ hops
  have hlen : ops.length = 2 ^ prog.logSize := by rw [← hf.length_eq, List.length_finRange]
  have key : ∀ (j : Fin (2 ^ prog.logSize)) (op : Op),
      (decode (prog.instructions j)).elim (throw (j.val, Fault.badInstruction) :
        Except (ℕ × Fault) Op) pure = Except.ok op →
        OpOf (prog.instructions j) op := by
    intro j op h
    cases hd : decode (prog.instructions j) with
    | none => rw [hd] at h; simp at h
    | some op' =>
      rw [hd] at h
      simp only [Option.elim, pure_ok] at h
      subst h
      exact decode_ok hd
  refine ⟨by simp [hlen], fun i hi hi' ↦ ?_⟩
  have h1 := forall₂_getElem hf (i := i) (by simpa using hi) (by simpa [hlen] using hi)
  simp only [List.getElem_finRange, Fin.cast_mk] at h1
  simpa using key ⟨i, hi⟩ _ h1

theorem exbind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := bind_ok

theorem forIn_ok {ε : Type} {P : ℕ × ℕ → Prop}
    {f : ℕ × ℕ → PUnit.{1} → Except ε (ForInStep PUnit.{1})}
    (hf : ∀ x r y, f x r = .ok y → P x ∧ y = .yield PUnit.unit) :
    ∀ (l : List (ℕ × ℕ)) (r y : PUnit.{1}), forIn l r f = .ok y → ∀ x ∈ l, P x
  | [], _, _, _, _, hx => nomatch hx
  | x :: l, r, y, h, z, hz => by
    rw [List.forIn_cons, bind_ok] at h
    obtain ⟨st, h1, h⟩ := h
    obtain ⟨hp, rfl⟩ := hf x r st h1
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hp
    · exact forIn_ok hf l _ y h z hz

theorem image_log {u : ℕ} (h2 : 2 ≤ u) (hu : u ≤ maxCells) :
    2 ^ Nat.log2 u.nextPowerOfTwo = u.nextPowerOfTwo ∧ u ≤ 2 ^ Nat.log2 u.nextPowerOfTwo ∧
      1 ≤ Nat.log2 u.nextPowerOfTwo ∧ Nat.log2 u.nextPowerOfTwo ≤ 28 := by
  obtain ⟨k, hk⟩ := Nat.isPowerOfTwo_nextPowerOfTwo u
  have hle := Nat.le_nextPowerOfTwo u
  have hge := Nat.nextPowerOfTwo_le hu ⟨28, rfl⟩
  rw [hk, Nat.log2_two_pow]
  rw [hk] at hle hge
  refine ⟨rfl, hle, ?_, (Nat.pow_le_pow_iff_right (by norm_num)).mp hge⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hle; omega
  · exact hk

/-- **The executor is sound**: an execution it returns is a valid execution of the program on the
public input, for every program, hint list and stream. -/
theorem execute_sound {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice}
    {t : Execution prog} (h : execute prog input adv = .ok t) : ValidExecution prog input t := by
  simp only [execute, bind_ok] at h
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨hsize, hdec⟩ := ctx_of_spec hC
  split_ifs at h with hmf
  · simp [bind_ok] at h
  simp only [bind_ok] at h
  obtain ⟨mem, hmem, s, hloop, h⟩ := h
  split_ifs at h with hused
  · simp [bind_ok] at h
  rw [bind_ok] at h
  obtain ⟨u, hfor, h⟩ := h
  simp only [pure_ok] at h; subst h
  rw [mapError_ok, exbind_ok] at hmem
  obtain ⟨m1, hm1, hmem⟩ := hmem
  have hm0 : Mem.WF ⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ :=
    ⟨fun c k h ↦ by simp [Mem.cellOf] at h, fun c h ↦ by simp [Mem.cellOf] at h⟩
  obtain ⟨le1, wf1, g1⟩ := Mem.put_ok hm0 hm1
  obtain ⟨le2, wf2, g2⟩ := Mem.put_ok wf1 hmem
  obtain ⟨gs, les, k, hk, hrun⟩ := loop_spec hsize hdec maxSteps _ s ⟨wf2, Dlog.ok_empty.grow _⟩
    (by unfold maxCells; norm_num) (Nat.zero_le _) hloop
  have hu2 : 2 ≤ s.mem.used :=
    le_trans (le_max_right _ _) (le_trans le1.used (le_trans le2.used les.used))
  obtain ⟨hpow, hcov, hκ1, hκ28⟩ := image_log hu2 (not_lt.mp hused)
  have hlinks : ∀ p ∈ s.mem.links, s.mem.peek p.1 = s.mem.peek p.2 := by
    rw [← Array.forIn_toList] at hfor
    intro p hp
    refine forIn_ok (P := fun p ↦ s.mem.peek p.1 = s.mem.peek p.2) (fun x r y hy ↦ ?_) _ _ _ hfor p
      (Array.mem_toList_iff.mpr hp)
    split_ifs at hy with hne
    · cases hy
    · simp only [pure_ok] at hy
      exact ⟨not_not.mp hne, hy.symm⟩
  have hF : Final s.mem (MemoryImage.read s.mem.image.snd) :=
    ⟨gs.wf, fun c hc ↦ MemoryImage.read_gpow
      (by change Nat.log2 s.mem.used.nextPowerOfTwo < 64; omega) s.mem.image.snd
      ⟨c, lt_of_lt_of_le hc hcov⟩,
      hlinks⟩
  refine ⟨⟨hκ1, le_trans hκ28 (by decide), ?_, ?_⟩, ?_⟩
  · exact hF.get (Mem.le_trans le2 les) g1
  · exact hF.get les g2
  · have hinit : (Registers.initial : Registers K) = ⟨g ^ 0, g ^ 0⟩ := by rw [pow_zero]; rfl
    have := hrun s.mem s.mem.image.snd (Mem.le_refl _) hF
    rw [hinit]
    rw [Nat.zero_add] at hk
    rw [hk]
    exact this

end

end LeanVM.Prover.Exec
