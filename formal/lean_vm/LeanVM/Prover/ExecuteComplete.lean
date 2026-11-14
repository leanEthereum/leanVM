module

public import LeanVM.Prover.ExecuteCompleteKeccak
public import LeanVM.Prover.ExecuteCount
public import LeanVM.Prover.ExecuteSound

/-!
# The executor is complete

`execute_complete`: given a valid execution of `n ≤ maxSteps` steps on `2^κ ≤ 2^28` words, operands
that are powers below `2^28`, and an invariant `Inv` of the executor's states that holds initially
and satisfies `InvRule` (along each step, every hint's needs `HintOk` and the instruction's
modedness `OpModed` hold, and `Inv` holds after it), the executor returns an execution of `n` steps
whose memory is the reference's wherever it is not zero. The run follows the reference
(`loop_complete`), each step its hints (`hints_complete`) and then its instruction
(`runOp_complete`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A decoded instruction completes. -/
theorem runOp_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {ins : LeanIsaInstruction} {op : Op} (hs : Fine M s) (hrd : RefRd rd M) (hop : OpOf ins op)
    (hsm : OpSmall op) (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ ins = some r') (hmo : OpModed M s op) :
    ∃ s', runOp C s op = .ok s' ∧ OpDone C M s s' r' := by
  cases op <;> cases ins <;> simp only [OpOf] at hop
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact xor_complete hs hrd hsm hpc hsz hnext hex hmo
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact mul_complete hs hrd hsm hpc hsz hnext hex hmo
  · obtain ⟨rfl, rfl⟩ := hop; exact set_complete hs hrd hsm hpc hsz hnext hex
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hop; exact deref_complete hs hrd hsm hpc hsz hnext hex hmo
  · obtain ⟨rfl, rfl, rfl⟩ := hop; exact jump_complete hs hrd hsm hpc hsz hnext hex hmo
  · obtain ⟨rfl, rfl, rfl, rfl, l, rfl, hl⟩ := hop
    exact keccak_complete hs hrd hl hsm hpc hsz hnext hex hmo

/-! ## The invariant rule -/

/-- A step's obligations from state `s` on: each hint's needs at the state it runs from, then the
instruction's modedness, and `Inv` after the step. -/
def StepOk (C : Ctx) (M : ℕ → E) (Inv : St → Prop) (op : Op) : List Hint → St → Prop
  | [], s => OpModed M s op ∧
    ∀ s', runOp C s op = .ok s' → Fine M s' → s.mem ≤ s'.mem → Inv { s' with steps := s'.steps + 1 }
  | h :: hs, s => HintOk C M s h ∧
    ∀ s', runHint C s h = .ok s' → Moves M s s' → StepOk C M Inv op hs s'

/-- The reference run of `n` steps on `img` passes through `s`'s registers before its end. -/
def OnRef {κ : ℕ} (prog : LeanIsaProgram) (img : MemoryImage κ) (n : ℕ) (s : St) : Prop :=
  s.steps < n ∧ run prog img (n - s.steps) ⟨g ^ s.pc, g ^ s.fp⟩ = some (Registers.final prog)

/-- **The invariant rule**: from every state in `Inv`, fine and on the reference run, the step's
obligations hold, `Inv` after the step among them. -/
def InvRule {κ : ℕ} (prog : LeanIsaProgram) (img : MemoryImage κ) (n : ℕ) (C : Ctx) (M : ℕ → E)
    (Inv : St → Prop) : Prop :=
  ∀ s op, Inv s → Fine M s → OnRef prog img n s → C.ops[s.pc]? = some op →
    StepOk C M Inv op (C.hints[s.pc]?.getD []) s

theorem hints_complete {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {op : Op} :
    ∀ (l : List Hint) (s : St), Fine M s → StepOk C M Inv op l s →
      ∃ s1, l.foldlM (runHint C) s = .ok s1 ∧ Moves M s s1 ∧ StepOk C M Inv op [] s1
  | [], s, hs, h => ⟨s, rfl, ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩, h⟩
  | x :: l, s, hs, h => by
    obtain ⟨hx, hk⟩ := h
    obtain ⟨s1, e1, m1⟩ := runHint_complete hs hx
    obtain ⟨s2, e2, m2, h2⟩ := hints_complete l s1 m1.fine (hk s1 e1 m1)
    exact ⟨s2, by rw [List.foldlM_cons, e1, ok_bind]; exact e2, m1.trans m2, h2⟩

/-! ## The loop -/

theorem mapError_eq {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α} (h : x = .ok a) :
    x.mapError f = .ok a := by
  rw [h]; rfl

theorem final_eq {prog : LeanIsaProgram} {C : Ctx} (hsize : C.ops.size = 2 ^ prog.logSize)
    {pc fp : ℕ} (hpc : pc < C.ops.size) (hfp : fp < maxCells)
    (h : (⟨g ^ pc, g ^ fp⟩ : Registers K) = Registers.final prog) :
    pc = C.ops.size - 1 ∧ fp = 0 := by
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  simp only [Registers.final, LeanIsaProgram.pcFinal, Registers.mk.injEq] at h
  refine ⟨?_, ?_⟩
  · rw [hsize]; rw [hsize] at hpc
    exact gpow_inj (by omega) (by omega) h.1
  · unfold maxCells at hfp
    exact gpow_inj (by omega) (by omega) (h.2.trans (pow_zero g).symm)

theorem nextOk_of_run {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hsize : C.ops.size = 2 ^ prog.logSize) {j : ℕ} {r : Registers K}
    (h : run prog img j r = some (Registers.final prog)) : NextOk C r := by
  cases j with
  | zero =>
    rw [run_zero] at h
    cases h
    refine ⟨C.ops.size - 1, by rw [hsize]; exact Nat.sub_lt Nat.one_le_two_pow one_pos, ?_⟩
    rw [hsize]; rfl
  | succ j =>
    rw [run_succ] at h
    split_ifs at h
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, -⟩ := h
    unfold LeanVM.Semantics.step at h1
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
    obtain ⟨ins, h2, -⟩ := h1
    obtain ⟨i, hi, -⟩ := (LeanIsaProgram.fetch_eq_some_iff prog).mp h2
    exact ⟨i.val, by rw [hsize]; exact i.isLt, hi⟩

/-- The loop runs along the reference to its end. -/
theorem loop_complete {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    {M : ℕ → E} {Inv : St → Prop} (hsize : C.ops.size = 2 ^ prog.logSize)
    (hdec : ∀ (i : ℕ) (hi : i < 2 ^ prog.logSize) (hi' : i < C.ops.size),
      OpOf (prog.instructions ⟨i, hi⟩) C.ops[i])
    (hsmall : ∀ (i : ℕ) (hi : i < C.ops.size), OpSmall C.ops[i]) (hrd : RefRd img.read M)
    (hrule : InvRule prog img n C M Inv) :
    ∀ (j fuel : ℕ) (s : St), Fine M s → Inv s → s.pc < C.ops.size → s.steps + j = n → j ≤ fuel →
      run prog img j ⟨g ^ s.pc, g ^ s.fp⟩ = some (Registers.final prog) →
      ∃ sf, loop C fuel s = .ok sf ∧ Fine M sf ∧ sf.steps = n ∧ Inv sf ∧ s.mem ≤ sf.mem ∧
        ∀ rd, Final sf.mem rd → SameSteps prog img rd j ⟨g ^ s.pc, g ^ s.fp⟩ := by
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  intro j
  induction j with
  | zero =>
    intro fuel s hs hinv hpc hn _ hrun
    rw [run_zero, Option.some.injEq] at hrun
    obtain ⟨h1, h2⟩ := final_eq hsize hpc hs.fp hrun
    refine ⟨s, ?_, hs, by omega, hinv, Mem.le_refl _, fun _ _ ↦ trivial⟩
    rw [loop.eq_def]
    dsimp only
    rw [ite_eq_left ⟨h1, h2⟩]
    rfl
  | succ j ih =>
    intro fuel s hs hinv hpc hn hj hrun
    have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
      rw [run_succ, ite_eq_left h] at hrun; cases hrun
    rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
    obtain ⟨r1, hstep, hrun1⟩ := hrun
    have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
    rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
    have hop : C.ops[s.pc]? = some C.ops[s.pc] := Array.getElem?_eq_getElem hpc
    have hon : OnRef prog img n s := by
      refine ⟨by omega, ?_⟩
      rw [show n - s.steps = j + 1 by omega, run_succ_of_ne_final hne,
        step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute, hstep]
      exact hrun1
    have hso := hrule s _ hinv hs hon hop
    obtain ⟨s1, e1, m1, ⟨hmo, hinv'⟩⟩ := hints_complete _ s hs hso
    have hex : executeWith img.read ⟨g ^ s1.pc, g ^ s1.fp⟩ (prog.instructions ⟨s.pc, hpc2⟩) =
        some r1 := by rw [m1.pc, m1.fp]; exact hstep
    obtain ⟨s2, e2, d2⟩ := runOp_complete m1.fine hrd (hdec s.pc hpc2 hpc) (hsmall s.pc hpc)
      (by rw [m1.pc]; exact hpc) hsz (nextOk_of_run hsize hrun1) hex hmo
    have hstepC : step C s = .ok { s2 with steps := s2.steps + 1 } := by
      unfold step
      dsimp only
      rw [mapError_eq e1, ok_bind, hop]
      dsimp only
      rw [mapError_eq e2, ok_bind]
      rfl
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨sf, ef, hf, hsf, hinvf, hlef, hsame⟩ := ih fuel { s2 with steps := s2.steps + 1 }
      (let h := d2.fine; ⟨h.agree, h.dl, h.small, h.fp⟩) (hinv' s2 e2 d2.fine d2.le) d2.pc
      (by dsimp only; rw [d2.steps, m1.steps]; omega) (by omega)
      (by dsimp only; rw [d2.regs]; exact hrun1)
    have sp := step_spec (ins := prog.instructions ⟨s.pc, hpc2⟩) ⟨hs.agree.wf, hs.dl⟩ hs.fp hpc
      (fun op hop ↦ by
        obtain ⟨h, rfl⟩ := Array.getElem?_eq_some_iff.mp hop
        exact hdec s.pc hpc2 h) hstepC
    have hstepR : LeanVM.Semantics.step prog img ⟨g ^ s.pc, g ^ s.fp⟩ = some r1 := by
      rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute]
      exact hstep
    refine ⟨sf, ?_, hf, hsf, hinvf, Mem.le_trans m1.le (Mem.le_trans d2.le hlef),
      fun rd hF ↦ ⟨?_, fun r' hr' ↦ ?_⟩⟩
    · rw [loop.eq_def]
      dsimp only
      rw [ite_eq_right (fun h ↦ hne (by rw [h.1, h.2, hsize]; rfl)), ite_eq_right (by omega), hstepC,
        ok_bind]
      exact ef
    · rw [hstepR]
      change prog.fetch (g ^ s.pc) >>= executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ = _
      rw [show g ^ s.pc = addressOfIndex (⟨s.pc, hpc2⟩ : Fin (2 ^ prog.logSize)) from rfl,
        prog.fetch_gpow ⟨s.pc, hpc2⟩]
      exact (sp.exec sf.mem rd hlef hF).trans (congrArg some d2.regs)
    · rw [hstepR, Option.some.injEq] at hr'
      subst hr'
      rw [← d2.regs]
      exact hsame rd hF

/-! ## The run -/

/-- The reference memory by cell: `img`'s word, zero past it. -/
def refMem {κ : ℕ} (img : MemoryImage κ) (c : ℕ) : E := if h : c < 2 ^ κ then img ⟨c, h⟩ else 0

/-- The executor's initial memory: the public input in cells `0` and `1`. -/
def initMem (adv : Advice) (input : PublicInput) : Except Fault Mem :=
  ((⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ : Mem).put 0 input.word0).bind (·.put 1 input.word1)

/-- The executor's initial state on the memory `m`. -/
def initSt (C : Ctx) (adv : Advice) (m : Mem) : St :=
  ⟨m, Dlog.empty.grow (max (C.ops.size + 2) adv.mainFrame), 0, 0, adv.mainFrame, ∅, 0⟩

theorem refRd_img {κ : ℕ} (hκ : κ ≤ 28) (img : MemoryImage κ) : RefRd img.read (refMem img) := by
  intro c v hc h
  obtain ⟨i, hi, hv⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp h
  have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  have hci : c = i := gpow_inj (by omega) (by omega) hi
  subst hci
  refine ⟨by unfold maxCells; omega, ?_⟩
  unfold refMem
  rw [dite_eq_left i.isLt, ← hv]

theorem ctx_of_complete {prog : LeanIsaProgram} {adv : Advice}
    (hdec : ∀ i, Decodable (prog.instructions i)) : ∃ C, Ctx.of prog adv = .ok C := by
  have hops : (List.finRange (2 ^ prog.logSize)).mapM (fun i ↦ (decode (prog.instructions i)).elim
      (throw (i.val, Fault.badInstruction) : Except (ℕ × Fault) Op) pure) =
      .ok ((List.finRange (2 ^ prog.logSize)).map fun i ↦ (decode_complete (hdec i)).choose) :=
    exMapM_eq _ fun i _ ↦ by
      have h := (decode_complete (hdec i)).choose_spec
      generalize (decode_complete (hdec i)).choose = op at h ⊢
      rw [h]; rfl
  exact ⟨_, by unfold Ctx.of; rw [hops, ok_bind]; rfl⟩

theorem ctx_small {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (h : Ctx.of prog adv = .ok C) :
    ∀ (i : ℕ) (hi : i < C.ops.size), OpSmall C.ops[i] := by
  simp only [Ctx.of, bind_ok, pure_ok] at h
  obtain ⟨ops, hops, rfl⟩ := h
  have hf := exMapM_ok _ _ _ hops
  have hlen : ops.length = 2 ^ prog.logSize := by rw [← hf.length_eq, List.length_finRange]
  intro i hi
  have hi' : i < ops.length := by simpa using hi
  have h1 := forall₂_getElem hf (i := i) (by rw [List.length_finRange]; omega) hi'
  simp only [List.getElem_finRange, Fin.cast_mk] at h1
  cases hd : decode (prog.instructions ⟨i, by omega⟩) with
  | none => rw [hd] at h1; simp at h1
  | some op' =>
    rw [hd] at h1
    simp only [Option.elim, pure_ok] at h1
    simpa [← h1] using decode_small hd

theorem forIn_yield {ε : Type} :
    ∀ (l : List (ℕ × ℕ)) (f : ℕ × ℕ → PUnit.{1} → Except ε (ForInStep PUnit.{1})),
      (∀ x ∈ l, f x PUnit.unit = .ok (.yield PUnit.unit)) → forIn l PUnit.unit f = .ok PUnit.unit
  | [], _, _ => rfl
  | x :: l, f, h => by
    rw [List.forIn_cons, h x (List.mem_cons_self ..), ok_bind]
    exact forIn_yield l f fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- **The executor is complete** against a valid execution, given an invariant satisfying the
invariant rule: it runs the reference's instructions, and its memory is the least power of two
covering `used` at a state of the invariant. -/
theorem execute_complete_inv {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice} {κ n : ℕ}
    {img : MemoryImage κ} {Inv : St → Prop} (hκ : κ ≤ 28) (hn : n ≤ maxSteps)
    (hval : ValidExecution prog input ⟨κ, img, n⟩) (hdec : ∀ i, Decodable (prog.instructions i))
    (hmain : adv.mainFrame < maxCells)
    (hinit : ∀ C m, Ctx.of prog adv = .ok C → initMem adv input = .ok m → Inv (initSt C adv m))
    (hrule : ∀ C, Ctx.of prog adv = .ok C → InvRule prog img n C (refMem img) Inv) :
    ∃ t, execute prog input adv = .ok t ∧ t.stepCount = n ∧
      (∀ i, t.memory i = 0 ∨ t.memory i = refMem img i.val) ∧
      (∀ op, t.opcodeCount op = (⟨κ, img, n⟩ : Execution prog).opcodeCount op) ∧
      ∃ s, Inv s ∧ t.logMemorySize = Nat.log2 s.mem.used.nextPowerOfTwo := by
  obtain ⟨C, hC⟩ := ctx_of_complete (adv := adv) hdec
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have hrd := refRd_img hκ img
  obtain ⟨⟨-, -, h0, h1⟩, hrun⟩ := hval
  have hM0 : refMem img 0 = input.word0 := (hrd 0 _ (by norm_num) h0).2
  have hM1 : refMem img 1 = input.word1 := (hrd 1 _ (by norm_num) h1).2
  have hA0 : Agree ⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ (refMem img) :=
    ⟨⟨⟨fun c k h ↦ by simp [Mem.cellOf] at h, fun c h ↦ by simp [Mem.cellOf] at h⟩,
      fun c v h ↦ by simp [Mem.get] at h, fun c d k h ↦ by simp [Mem.cellOf] at h,
      fun c k h ↦ by simp [Mem.cellOf] at h, rfl,
      show max adv.mainFrame 2 ≤ maxCells by unfold maxCells at hmain ⊢; omega⟩,
      fun p hp ↦ by simp at hp⟩
  obtain ⟨m1, e1, a1, le1, -⟩ := hA0.put hM0 (by unfold maxCells; norm_num)
  obtain ⟨m2, e2, a2, le2, -⟩ := a1.put hM1 (by unfold maxCells; norm_num)
  have hinitm : initMem adv input = .ok m2 := by
    unfold initMem; rw [e1]; exact e2
  have hs0 : Fine (refMem img) (initSt C adv m2) :=
    ⟨a2, Dlog.ok_empty.grow _, Dlog.small_empty.grow (by unfold maxCells at hmain; omega),
      show 0 < maxCells by unfold maxCells; norm_num⟩
  obtain ⟨sf, ef, hf, hsf, hinvf, hlef, hsame⟩ := loop_complete hsize hdecC (ctx_small hC) hrd (hrule C hC) n maxSteps
    (initSt C adv m2) hs0 (hinit C m2 hC hinitm) (by rw [hsize]; exact Nat.one_le_two_pow)
    (Nat.zero_add n) hn
    (by
      show run prog img n ⟨g ^ 0, g ^ 0⟩ = _
      rw [show (⟨g ^ 0, g ^ 0⟩ : Registers K) = Registers.initial by rw [pow_zero]; rfl]
      exact hrun)
  have hlinks : ∀ p ∈ sf.mem.links, sf.mem.peek p.1 = sf.mem.peek p.2 := fun p hp ↦ by
    unfold Mem.peek
    rw [((hf.agree.links p hp).2).get_eq]
  refine ⟨⟨sf.mem.image.1, sf.mem.image.2, sf.steps⟩, ?_, hsf, fun i ↦ ?_, fun op ↦ ?_,
    sf, hinvf, rfl⟩
  · have ef' : loop C maxSteps ⟨m2, Dlog.empty.grow (max (C.ops.size + 2) adv.mainFrame), 0, 0,
        adv.mainFrame, ∅, 0⟩ = .ok sf := ef
    unfold execute
    rw [hC, ok_bind]
    dsimp only
    rw [ite_eq_right (not_le.mpr hmain), e1]
    change (Except.mapError _ (m1.put 1 input.word1) >>= _) = _
    rw [mapError_eq e2, ok_bind, ef', ok_bind, ite_eq_right (not_lt.mpr hf.agree.used),
      ← Array.forIn_toList, forIn_yield _ _ ?_, ok_bind]
    · rfl
    · rintro ⟨a, b⟩ hp
      dsimp only
      rw [ite_eq_right (not_not.mpr (hlinks _ (Array.mem_toList_iff.mp hp)))]
      rfl
  · show sf.mem.peek i.val = 0 ∨ sf.mem.peek i.val = refMem img i.val
    unfold Mem.peek
    cases h : sf.mem.get i.val with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (hf.agree.get _ _ h).symm
  · have hu2 : 2 ≤ sf.mem.used :=
      le_trans (le_max_right _ _) (le_trans le1.used (le_trans le2.used hlef.used))
    have hF := final_image hf.agree.wf hu2 hf.agree.used hlinks
    show opcodeCountInRun prog sf.mem.image.snd op sf.steps Registers.initial =
      opcodeCountInRun prog img op n Registers.initial
    rw [hsf, show (Registers.initial : Registers K) = ⟨g ^ 0, g ^ 0⟩ by rw [pow_zero]; rfl]
    exact opcodeCountInRun_congr op n _ (hsame _ hF)

/-- **The executor is complete** against a valid execution, given an invariant satisfying the
invariant rule. -/
theorem execute_complete {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice} {κ n : ℕ}
    {img : MemoryImage κ} {Inv : St → Prop} (hκ : κ ≤ 28) (hn : n ≤ maxSteps)
    (hval : ValidExecution prog input ⟨κ, img, n⟩) (hdec : ∀ i, Decodable (prog.instructions i))
    (hmain : adv.mainFrame < maxCells)
    (hinit : ∀ C m, Ctx.of prog adv = .ok C → initMem adv input = .ok m → Inv (initSt C adv m))
    (hrule : ∀ C, Ctx.of prog adv = .ok C → InvRule prog img n C (refMem img) Inv) :
    ∃ t, execute prog input adv = .ok t ∧ t.stepCount = n ∧
      ∀ i, t.memory i = 0 ∨ t.memory i = refMem img i.val :=
  let ⟨t, he, hn, hm, _⟩ := execute_complete_inv hκ hn hval hdec hmain hinit hrule
  ⟨t, he, hn, hm⟩

end

end LeanVM.Prover.Exec
