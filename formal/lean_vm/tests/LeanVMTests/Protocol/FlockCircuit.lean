import LeanVM.Protocol.ToArkLib.Flock.Words

/-!
# Product-gate circuit tests

* **A word circuit.** On a block of `2 ^ 8` positions: three input words at `0`, `32`, `64`, the
  constant at `96`, and the program `x + y + z`, then `+ x` (`61 + 31` gates from `97`). Its
  boundedness is proved from the gate-count contracts (`toy_bounded`) and checked by `decide`;
  its soundness is proved from the gadget specifications (`toy_sound`); the executable trace on
  concrete words gives the sum, satisfies the R1CS over `ZMod 2` and agrees with the
  mathematical trace.
* **What is rejected.** One flipped gate bit of the trace fails the R1CS.
* **The constant position is load-bearing.** The zero block satisfies every row (the rows are
  homogeneous) and is not the trace of its inputs: determinism needs `1` at the constant.
* **Boundedness is load-bearing.** A gate reading a later position: the circuit is not bounded,
  and the trace of an input fails the R1CS. Two gates at one position: not bounded either, and a
  block satisfying the R1CS fails the second gate.
-/

namespace LeanVMTests.Protocol.FlockCircuit

open LeanVM.Protocol ProductCircuit ProductCircuit.Start

/-! ## A word circuit -/

/-- The constant position. -/
def cpos : Pos 8 := pos 96

/-- The program: `x + y + z`, then `+ x`. Irreducible, so that no unification evaluates it. -/
@[irreducible] def toyProg : Builder 8 (Word 8) := do
  let s ← add3W (inW 0) (inW 32) (inW 64)
  addW s (inW 0)

/-- The input positions `0, …, 95`. -/
def toyInputs : Form 8 := BitVec.ofNat _ (2 ^ 96 - 1)

/-- The start: the inputs and the constant are available, gates from `97`. -/
def toyStart : Start 8 where
  avail := toyInputs ||| Form.var cpos
  base := 97
  fresh j hj := by
    rw [BitVec.getLsbD_or, getLsbD_var]
    simp only [toyInputs, BitVec.getLsbD_ofNat, cpos, pos_val (show 96 < 2 ^ 8 by decide),
      Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun _ ↦ ?_, by omega⟩
    rw [Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- The circuit of the program. -/
def toyCircuit : ProductCircuit 8 where
  cpos := cpos
  inputs := toyInputs
  gates := (toyProg.run ⟨97, #[]⟩).2.gates

theorem toyStart_avail (j : ℕ) (hj : j < 96) : toyStart.avail.getLsbD j = true := by
  simp only [toyStart, BitVec.getLsbD_or, toyInputs, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨by omega, hj⟩

theorem subW_in (b : ℕ) (hb : b + 32 ≤ 96) (n : ℕ) : toyStart.SubW (inW b) n :=
  subW_inW (by omega) (fun i hi ↦ toyStart_avail _ (by omega)) n

/-- The program records `92` gates and keeps the schedule bounded. -/
theorem toyProg_ok : toyStart.Ok 97 toyProg 92 toyStart.SubW := by
  unfold toyProg
  refine ok_bind (ok_add3W (subW_in 0 (by decide) _) (subW_in 32 (by decide) _)
    (subW_in 64 (by decide) _)) (by decide) fun s n hn hs ↦ ?_
  exact ok_addW hs (subW_in 0 (by decide) _)

/-- Bounded, from the contracts: no evaluation of the circuit. -/
theorem toy_bounded : toyCircuit.Bounded :=
  bounded_of_ok (S := toyStart) rfl toyProg_ok (by decide) rfl

#guard decide toyCircuit.Bounded

/-- Soundness: in a block satisfying the circuit's R1CS over `ZMod 2` with `1` at the constant,
the program's output word denotes `x + y + z + x` of the input words. -/
theorem toy_sound (w : Pos 8 → Bool)
    (hw : (toyCircuit.toBlockR1CS (ZMod 2)).Holds (liftBlock (ZMod 2) w)) {x y z : UInt32}
    (hx : Den w (inW 0) x) (hy : Den w (inW 32) y) (hz : Den w (inW 64) z) :
    Den w (toyProg.run ⟨97, #[]⟩).1 (x + y + z + x) := by
  have hs : Sound w toyProg (fun o ↦ Den w o (x + y + z + x)) := by
    unfold toyProg
    exact sound_bind (sound_add3W hx hy hz) (fun _ ↦ grows_addW _ _) fun _ hs ↦ sound_addW hs hx
  exact hs _ (gates_of_holds toy_bounded w hw)

/-! ## Executable checks -/

/-- The word `u` placed at the positions `b, …, b + 31`. -/
def wordAt (b : ℕ) (u : UInt32) : Form 8 := BitVec.ofNat _ u.toNat <<< b

/-- The input block of three words. -/
def toyIn (x y z : UInt32) : Form 8 := wordAt 0 x ||| wordAt 32 y ||| wordAt 64 z

/-- The value of an output word on a bitset block. -/
def wordValue (o : Word 8) (z : Form 8) : UInt32 :=
  (List.finRange 32).foldl
    (fun acc i ↦ if o[i].evalB z then acc ||| (1 <<< i.val.toUInt32) else acc) 0

/-- The trace of three concrete words. -/
def toyTrace : Form 8 := toyCircuit.trace (toyIn 0xDEADBEEF 0x01234567 0xFFFFFFFF)

/-- The output of the program on the trace. -/
def toyOut : UInt32 := wordValue (toyProg.run ⟨97, #[]⟩).1 toyTrace

#guard toyOut == 0xDEADBEEF + 0x01234567 + 0xFFFFFFFF + 0xDEADBEEF
#guard (toyCircuit.gates.size, (toyProg.run ⟨97, #[]⟩).2.next) == (92, 189)

/-- A bitset block as a function. -/
def toFun (z : Form 8) : Pos 8 → Bool := fun j ↦ z.getLsbD j

#guard decide ((toyCircuit.toBlockR1CS (ZMod 2)).Holds (liftBlock (ZMod 2) (toFun toyTrace)))
#guard (toFun toyTrace) cpos

/-- The mathematical trace is the executable one. -/
example : toFun toyTrace =
    toyCircuit.traceF (toFun (toyIn 0xDEADBEEF 0x01234567 0xFFFFFFFF)) :=
  trace_getLsbD _ _

/-! ## What is rejected -/

/-- One gate's bit of the trace flipped (position `150`). -/
def flipped : Form 8 := toyTrace ^^^ Form.var (pos 150)

#guard !decide ((toyCircuit.toBlockR1CS (ZMod 2)).Holds (liftBlock (ZMod 2) (toFun flipped)))

/-! ## The constant position is load-bearing -/

/-- The zero block satisfies every row, and differs from the trace of its inputs at the
constant. -/
example : (toyCircuit.toBlockR1CS (ZMod 2)).Holds (liftBlock (ZMod 2) (fun _ ↦ false)) ∧
    toyCircuit.traceF (fun _ ↦ false) ≠ fun _ ↦ false := by
  refine ⟨(holds_iff_gates _ _).mpr fun k ↦ ?_, fun h ↦ ?_⟩
  · have e : ∀ L : Form 8, L.eval (fun _ ↦ false) = false := fun L ↦ by
      apply toZ_injective
      rw [toZ_eval, Form.evalZ]
      simp [toZ]
    rw [e, e]; rfl
  · have := congrFun h toyCircuit.cpos
    rw [traceF_cpos toy_bounded] at this
    exact Bool.noConfusion this

/-! ## Boundedness is load-bearing -/

/-- Constant at `0`, input at `1`; the gate at `2` reads the later gate at `3`, which copies the
input. -/
def badCircuit : ProductCircuit 2 where
  cpos := 0
  inputs := Form.var 1
  gates := #[(2, ⟨Form.var 3, Form.var 0⟩), (3, ⟨Form.var 1, Form.var 0⟩)]

#guard !decide badCircuit.Bounded

/-- The trace of input `1` fails the R1CS: its gate `2` was evaluated before gate `3`. -/
example : ¬ (badCircuit.toBlockR1CS (ZMod 2)).Holds
    (liftBlock (ZMod 2) (badCircuit.traceF fun _ ↦ true)) := by decide +kernel

/-- Two gates at one position. -/
def dupCircuit : ProductCircuit 2 where
  cpos := 0
  inputs := Form.var 1
  gates := #[(2, ⟨Form.var 1, Form.var 0⟩), (2, ⟨Form.var 0, Form.var 0⟩)]

#guard !decide dupCircuit.Bounded

/-- Two gates at one position, the second reading the input: a block satisfying the R1CS with `1`
at the constant (the first gate's row wins) fails the second gate. So the soundness of the
lowering needs boundedness. -/
def dupCircuit' : ProductCircuit 2 where
  cpos := 0
  inputs := Form.var 1
  gates := #[(2, ⟨Form.var 0, Form.var 0⟩), (2, ⟨Form.var 1, Form.var 0⟩)]

/-- The block `1` at `0` and `2`, `0` elsewhere. -/
def dupBlock : Pos 2 → Bool := fun j ↦ decide (j = 0 ∨ j = 2)

example : (dupCircuit'.toBlockR1CS (ZMod 2)).Holds (liftBlock (ZMod 2) dupBlock) ∧
    dupBlock dupCircuit'.cpos = true ∧
    ¬ ∀ kg ∈ dupCircuit'.gates, dupBlock kg.1 = (kg.2.a.eval dupBlock && kg.2.b.eval dupBlock) := by
  refine ⟨by decide +kernel, by decide +kernel, fun h ↦ ?_⟩
  have := h (2, ⟨Form.var 1, Form.var 0⟩) (Array.mem_def.mpr (by simp [dupCircuit']))
  revert this
  decide +kernel

end LeanVMTests.Protocol.FlockCircuit
