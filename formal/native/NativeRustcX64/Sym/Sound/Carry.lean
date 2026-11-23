module

public import NativeRustcX64.Sym.Sound.Data

/-!
# One-operand `MUL`, `ADC` and `SBB` are sound

`OpOk` for `MUL` (RDX:RAX the product, CF and OF whether the high half is nonzero) and for `ADC`,
`SBB` (the carry flag in; the carry and overflow flags of the sum or difference with that carry
in): the symbolic step's operands, values and flags are Kraken's.
-/

namespace NativeRustcX64.Sym

public section

variable [Labels] {env : Env} {w : Width}

/-- The carry flag as a value is Kraken's coercion of the flag. -/
theorem low_carryBit (w : Width) (c : SBool) :
    low w ((Step.carryBit c).eval env) = ((c.eval env : Bool) : w.type) := by
  unfold Step.carryBit
  rw [eval_mkIte]
  cases c.eval env
  · simp only [Bool.false_eq_true, ite_false, Sym.eval, low_zero]
    rfl
  · simp only [ite_true, Sym.eval, low_one]
    rfl

theorem mulW_ok (hw : (w == .W8) = false) {src : RegOrMem w} {S S' : SState} {x : Exit}
    {m : MachineData} (p : Std.Rco Int64) (hwf : env.WF) (hm : Match env S m)
    (h : Step.mulW src S = some (S', x)) :
    ((Operation.mul src).interp p m (fun m' => .done ⟨m', p.upper⟩)
      (fun a m' => .done ⟨m', a⟩)).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.mulW, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, S₁, hS₁, S₂, hS₂, rfl, rfl⟩ := h
  have hA := hm.getR ha
  unfold Operation.interp
  refine hm.readRM hwf hb p ?_
  simp only [hw, Bool.false_eq_true, ↓reduceIte]
  intro sf zf af pf
  have hc : ∀ u, some (mkCmp .mulC w a b) = some u →
      ((m.regs.get (.low .rax w) * low w (b.eval env)).unsigned !=
        (m.regs.get (.low .rax w)).unsigned * (low w (b.eval env)).unsigned) = u.eval env := by
    intro _ h
    cases h
    rw [eval_mkCmp, hA]
    rfl
  have h₁ : (mkBin .mul w a b).eval env = ext w (m.regs.get (.low .rax w) * low w (b.eval env)) := by
    rw [eval_mkBin, hA]
    rfl
  have h₂ : (mkBin .mulhi w a b).eval env = ext w (BitVec.ofInt w.bits
      (((m.regs.get (.low .rax w)).unsigned * (low w (b.eval env)).unsigned) >>> w.bits)) := by
    rw [eval_mkBin, hA]
    rfl
  have hf : FlagsOk env ⟨some (mkCmp .mulC w a b), none, none, some (mkCmp .mulC w a b)⟩
      { cf := (m.regs.get (.low .rax w) * low w (b.eval env)).unsigned !=
          (m.regs.get (.low .rax w)).unsigned * (low w (b.eval env)).unsigned,
        pf, af, zf, sf,
        of := (m.regs.get (.low .rax w) * low w (b.eval env)).unsigned !=
          (m.regs.get (.low .rax w)).unsigned * (low w (b.eval env)).unsigned } :=
    ⟨hc, (fun _ h => by cases h), (fun _ h => by cases h), hc⟩
  exact done_fall (((hm.setR hS₁ h₁).setR hS₂ h₂).setFlags _ hf)

theorem ok_mul (src : RegOrMem w) : OpOk env (.mul src) := by
  intro S S' x m p hwf hm h _
  change Step.mul src S = some (S', x) at h
  cases w with
  | W8 => cases h
  | W16 => exact mulW_ok rfl p hwf hm h
  | W32 => exact mulW_ok rfl p hwf hm h
  | W64 => exact mulW_ok rfl p hwf hm h

theorem ok_adc (dst : Dst w) (src : Operand w) : OpOk env (.adc dst src) := by
  intro S S' x m p hwf hm h _
  change Step.adc dst src S = some (S', x) at h
  simp only [Step.adc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hcf : m.status.cf = c.eval env := hm.flags.1 c hc
  have hr : (mkBin .add w (mkBin .add w a b) (Step.carryBit c)).eval env =
      ext w (low w (a.eval env) + low w (b.eval env) + (m.status.cf : w.type)) := by
    rw [eval_mkBin, eval_mkBin, hcf]
    simp only [BinOp.apply, low_ext, low_carryBit]
  unfold Operation.interp
  refine hm.readOp hwf ha p ?_
  refine hm.readRM hwf hb p ?_
  refine (hm.setFlags _ (flagsOk_result env hr (rem := ⟨_, _, _⟩) ?_ ?_)).writeDst hwf hS hr p
    fun _ hm' => done_fall hm'
  · intro _ h
    cases h
    rw [eval_mkIteB, eval_mkCmp, eval_mkCmp, hcf]
    cases c.eval env <;> rfl
  · intro _ h
    cases h
    rw [eval_mkIteB, eval_mkCmp, eval_mkCmp, hcf]
    cases c.eval env <;> rfl

theorem ok_sbb (dst : Dst w) (src : Operand w) : OpOk env (.sbb dst src) := by
  intro S S' x m p hwf hm h _
  change Step.sbb dst src S = some (S', x) at h
  simp only [Step.sbb, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hcf : m.status.cf = c.eval env := hm.flags.1 c hc
  have hr : (mkBin .sub w (mkBin .sub w b a) (Step.carryBit c)).eval env =
      ext w (low w (b.eval env) - low w (a.eval env) - (m.status.cf : w.type)) := by
    rw [eval_mkBin, eval_mkBin, hcf]
    simp only [BinOp.apply, low_ext, low_carryBit]
  unfold Operation.interp
  refine hm.readOp hwf ha p ?_
  refine hm.readRM hwf hb p ?_
  refine (hm.setFlags _ (flagsOk_result env hr (rem := ⟨_, _, _⟩) ?_ ?_)).writeDst hwf hS hr p
    fun _ hm' => done_fall hm'
  · intro _ h
    cases h
    rw [eval_mkIteB, eval_mkCmp, eval_mkCmp, hcf]
    cases c.eval env <;> rfl
  · intro _ h
    cases h
    rw [eval_mkIteB, eval_mkCmp, eval_mkCmp, hcf]
    cases c.eval env <;> rfl

end

end NativeRustcX64.Sym
