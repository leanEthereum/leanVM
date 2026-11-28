module

public import NativeRustcVmArm.Bus.AccumulateSide.Exec
public import NativeRustcVmArm.Bus.AccumulateSide.Model
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Bus.Frame
public import NativeRustcVmArm.Ring.Track

/-!
# `accumulate_side`: what its proof shares

The frame is `12096` bytes below the entry's SP, X19 to X30 saved at `12000` to `12096`
(`slots`), the 72 bytes of stack arguments above it. Until the end the only output written is
the forms (`outs`); the total goes to `out` last (`outsO`).

The arguments the body keeps (the registers at the entry, the stack arguments) are a table
`sv m0`; where the body keeps them, registers and frame words, is a `Ring.Holds` description
(`Ring/Track.lean`), carried through blocks by `trackOk` and through calls by `callSafe`.

- `ev_satSub`, `ev_shr`, `ev_above`: the registers `eq_above`'s inlined head computes.
- `eqAbove_pre`, `eqAbove_ret`: `eq_eval_fn`'s call for `eq_above p point`.
- `Fr.blockA`: a block of the frame reading the stack arguments.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Verifier (Placement)

public section

/-! ## The frame -/

/-- The frame's bytes. -/
abbrev F : Nat := 12096

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(12000, .X29), (12008, .X30), (12016, .X28), (12024, .X27), (12032, .X26), (12040, .X25),
    (12048, .X24), (12056, .X23), (12064, .X22), (12072, .X21), (12080, .X20), (12088, .X19)]

/-- Every callee-saved register is saved. -/
abbrev keep : List XReg := []

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ F := by decide

/-- The forms: the outputs until the end. -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X1.toBitVec formsBytes q

/-- All the outputs. -/
@[expose] def outsO (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec 24 q ∨ outs m0 q

abbrev N : Nat := accumulateSideStack

theorem N_eq : N = 12800 := by decide
theorem le_ee : F + eqEvalFnStack ≤ N := by decide
theorem le_mul : F + ewMulStack ≤ N := by decide
theorem le_bf : F + blockFormStack ≤ N := by decide
theorem le_as : F + formBufAddScaledStack ≤ N := by decide
theorem le_pw : F + paddingWeightStack ≤ N := by decide
theorem le_ev : F + evaluateStack ≤ N := by decide
theorem ee_eq : eqEvalFnStack = 640 := by decide

/-! ## The arguments -/

/-- The arguments the body keeps: `0` to `7` the registers X0 to X7, `8` to `15` the stack
arguments from SP + 8 to SP + 64, `16` the fingerprints' count at SP, `17` the framework blocks'
count (the word at X6 + 8), `18` their placements' address, `19` the fingerprints the known part
reads (`min` of the two counts); `20`, `21` the layout's heights and rows, `22` the side's forms,
`23` the frame's `FormBuf`'s terms. -/
@[expose] def sv (m0 : MachineData) : Nat → UInt64
  | 0 => m0.regs.X0 | 1 => m0.regs.X1 | 2 => m0.regs.X2 | 3 => m0.regs.X3
  | 4 => m0.regs.X4 | 5 => m0.regs.X5 | 6 => m0.regs.X6 | 7 => m0.regs.X7
  | 8 => stackArg m0 8 | 9 => stackArg m0 16 | 10 => stackArg m0 24 | 11 => stackArg m0 32
  | 12 => stackArg m0 40 | 13 => stackArg m0 48 | 14 => stackArg m0 56 | 15 => stackArg m0 64
  | 16 => stackArg m0 0
  | 17 => NativeRustcVm.wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)
  | 18 => m0.regs.X6 + 16
  | 19 => if (stackArg m0 0).toNat <
      (NativeRustcVm.wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)).toNat
      then stackArg m0 0
      else NativeRustcVm.wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)
  | 20 => m0.regs.X5 + 24
  | 21 => m0.regs.X5 + 72
  | 22 => m0.regs.X2 * 5928 + m0.regs.X1
  | 23 => UInt64.ofBitVec (base m0 F + BitVec.ofNat 64 160)
  | _ => 0

/-! ## Descriptions -/

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
  {m : MachineData}

theorem Holds.reg (h : Holds rs V D m) {r : XReg} {i : Nat} (hp : (Sym.reg r, i) ∈ D) :
    m.regs.getXReg r = V i := by
  have := h _ hp
  simp only [tval, Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at this
  exact this

theorem Holds.load (h : Holds rs V D m) {o i : Nat} (hp : (Sym.load 0 o 8, i) ∈ D) :
    (Env.ofMachine m rs).load 0 o 8 = (V i).toBitVec := by
  have := h _ hp
  simp only [tval, Sym.eval] at this
  rw [← this]

/-- A location of region `0` or a register. -/
@[expose] def loc0 : Sym → Bool
  | .reg _ => true
  | .load 0 _ 8 => true
  | _ => false

theorem Holds.append {D' : List (Sym × Nat)} (h : Holds rs V D m) (h' : Holds rs V D' m) :
    Holds rs V (D ++ D') m := fun p hp ↦ (List.mem_append.mp hp).elim (h p) (h' p)

/-- **A description over another list of regions** with the same region `0`'s base. -/
theorem Holds.reg0 {rs' : List (BitVec 64 × Nat)} (h : Holds rs V D m)
    (hD : D.all (fun p ↦ loc0 p.1) = true) (h0 : (rs[0]?).map (·.1) = (rs'[0]?).map (·.1)) :
    Holds rs' V D m := by
  intro p hp
  rw [← h p hp]
  have hl := List.all_eq_true.mp hD p hp
  unfold tval
  congr 1
  match hs : p.1, hl with
  | .reg r, _ => rfl
  | .load 0 o 8, _ =>
    simp only [Sym.eval, Env.load, Env.base_ofMachine_eq, h0]
    rfl

end

/-! ## `eq_above`'s head -/

section
variable [Labels] (env : Env)

/-- `subs; csel lo`: the saturating difference. -/
theorem ev_satSub (a b : Sym) :
    ((Sym.ite (.cmp .ult .W64 a b) (.lit 0) (.bin .sub .W64 a b)).eval env).toNat =
      (a.eval env).toNat - (b.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]

/-- `lsr; cmp #63; csel hi`: `shr`. -/
theorem ev_shr (a s : Sym) :
    ((Sym.ite (.and (.not (.cmp .ult .W64 s (.lit 63))) (.not (.cmp .eq .W64 s (.lit 63))))
      (.lit 0) (.bin .lsrv .W64 a s)).eval env).toNat =
      (a.eval env).toNat >>> (s.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have hr := (a.eval env).isLt
  split <;> rename_i hc
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq] at hc
    have : 63 < (s.eval env).toNat := by
      obtain ⟨h1, h2⟩ := hc
      have h3 : (s.eval env).toNat ≠ 63 := fun h ↦ h2 (BitVec.eq_of_toNat_eq (by simpa using h))
      simp at h1; omega
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
    have : (s.eval env).toNat ≤ 63 := by
      by_cases h : (s.eval env).toNat < 63
      · omega
      · have := hc (by simpa using h); have := congrArg BitVec.toNat this; simp at this; omega
    simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (show (s.eval env).toNat < 64 by omega)]

/-- `add p, s, lsl #4; csel lo`: the point's rest, or `8`. -/
theorem ev_above (n p s z : Sym) (hz : z.eval env = 8#64) :
    (Sym.ite (.cmp .ult .W64 n s) z (.bin .add .W64 p (.un (.shift .LSL 4) .W64 s))).eval env =
      if (n.eval env).toNat < (s.eval env).toNat then 8#64
      else p.eval env + BitVec.ofNat 64 (16 * (s.eval env).toNat) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, UnOp.apply, shiftW, low_W64,
    ext_W64, BitVec.ult]
  by_cases hc : (n.eval env).toNat < (s.eval env).toNat
  · simp only [hc, decide_true, ↓reduceIte, hz]
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega

end

/-! ## `eq_eval_fn` for `eq_above` -/

/-- The elements from `a + 16 v`: those of the `n` from `a` past the first `v`. -/
theorem slice_above {m : MachineData} {a n : UInt64} {v : Nat} (hv : v ≤ n.toNat)
    {a' n' : UInt64} (ha' : a'.toBitVec = a.toBitVec + BitVec.ofNat 64 (16 * v))
    (hn' : n'.toNat = n.toNat - v) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [ha', hn', NativeRustcVmArm.Tables.TableTerms.ewsOf_sub m.dmem a.toBitVec
    (n := n.toNat) (by omega)]
  apply Array.ext (by simp) fun i h1 h2 ↦ by simp

theorem slice_nil {m : MachineData} {a n : UInt64} {v : Nat} (hv : n.toNat < v)
    {a' n' : UInt64} (hn' : n'.toNat = 0) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp; omega) fun i h1 h2 ↦ by simp at h1

/-- `x.get(..v).unwrap_or(x)`: the first `min v |x|` elements. -/
theorem slice_low {m : MachineData} {a n : UInt64} {v : Nat} {n' : UInt64}
    (hn' : n'.toNat = min v n.toNat) : slice m a n' = (slice m a n).extract 0 v := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp) fun i h1 h2 ↦ by simp

/-- **`eq_eval_fn`'s result** is `eq_above p` of the point (`pa`, `pn`). -/
theorem eqAbove_ret {st m' : MachineData} {p : Placement} {pa pn : UInt64}
    (h0 : st.regs.X0.toNat = pn.toNat - p.variableCount)
    (h1 : st.regs.X1.toNat = p.index >>> p.variableCount)
    (h2 : st.regs.X2.toBitVec = if pn.toNat < p.variableCount then 8#64
      else pa.toBitVec + BitVec.ofNat 64 (16 * p.variableCount))
    (h3 : st.regs.X3.toNat = pn.toNat - p.variableCount)
    (hq : EqEvalFnOfEqAbovePost st m') : ewRet m' = eqAbove p (slice st pa pn) := by
  have hsz : (slice st pa pn).size = pn.toNat := by simp [slice]
  have hext : slice st st.regs.X2 st.regs.X3 =
      (slice st pa pn).extract p.variableCount (slice st pa pn).size := by
    by_cases hlt : pn.toNat < p.variableCount
    · exact slice_nil (n' := st.regs.X3) hlt (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)] at h2
      exact slice_above (by omega) h2 h3
  rw [hq.1, h0, h1, hext]
  unfold eqAbove
  rw [hsz]

/-- **`eq_eval_fn`'s precondition** at a call from the frame. -/
theorem eqAbove_pre {st : MachineData} {p : Placement} {pa pn : UInt64}
    (hS : StackOk st eqEvalFnStack) (hpn : pn.toNat < 64)
    (hsl : SliceOk st pa pn eqEvalFnStack) (h8 : 8 ≤ (stackBelow st eqEvalFnStack).toNat)
    (h0 : st.regs.X0.toNat = pn.toNat - p.variableCount)
    (h2 : st.regs.X2.toBitVec = if pn.toNat < p.variableCount then 8#64
      else pa.toBitVec + BitVec.ofNat 64 (16 * p.variableCount))
    (h3 : st.regs.X3.toNat = pn.toNat - p.variableCount) : EqEvalFnOfEqAbovePre st := by
  refine ⟨hS, by rw [h0, h3]; omega, ?_⟩
  unfold SliceOk
  by_cases hlt : pn.toNat < p.variableCount
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)] at h2
    rw [h2, show st.regs.X3.toNat = 0 by omega, Nat.mul_zero]
    refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; simp⟩, ?_⟩
    unfold OffStack Apart
    left
    simpa using h8
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)] at h2
    rw [h2, h3]
    obtain ⟨⟨hm, hnw⟩, hap⟩ := hsl
    unfold NoWrap at hnw
    unfold OffStack Apart at hap
    rcases NativeRustcVm.toNat_add_ofNat_le (a := pa.toBitVec) (i := 16 * p.variableCount)
      (by omega) with ha | ⟨ha0, hae⟩
    · refine ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩
      · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
      · unfold NoWrap; rw [ha]; omega
      · unfold OffStack Apart; rw [ha]; omega
    · have hz : pn.toNat - p.variableCount = 0 := by omega
      rw [hz, Nat.mul_zero]
      refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; omega⟩, ?_⟩
      unfold OffStack Apart; rw [ha0]; omega

end

end NativeRustcVmArm.Bus.AccumulateSide
