module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Bus.GkrStep.Frame

/-!
# `gkr_step`'s calls from its frame

- `rs_call`: `read_scalars` into the frame's `2^step` elements at `o`.
- `leaf_call`: a call changing nothing but its stack (`prod_e`, `poly_eval`, `multilinear_eval`,
  `bit_length`).
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

omit [Host] in
/-- `cmp w, #0` of `okWord b`'s low half: `b` false. -/
theorem okWord_eq0 (b : Bool) :
    CmpOp.eq.apply .W32 (okWord b).toBitVec (BitVec.ofNat 64 0) = !b := by
  cases b <;> rfl

omit [Host] in
/-- `x + j` of the frame's byte `o`. -/
theorem add_loc (o j : Nat) :
    BinOp.apply .add .W64 (loc m0 o) (BitVec.ofNat 64 j) = loc m0 (o + j) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact NativeRustcVm.addr_add_add _ _ _

/-- The registers `gkr_step` keeps from its sumcheck on: X19 to X27. -/
structure Regs (m0 : MachineData) (c : EW) (n : Nat) (m : MachineData) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = m0.regs.X2
  x23 : (m.regs.getXReg .X23).toNat = n
  x24 : m.regs.getXReg .X24 = c.c0
  x25 : m.regs.getXReg .X25 = c.c1
  x26 : (m.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat)
  x27 : (m.regs.getXReg .X27).toBitVec = loc m0 1024

omit [Host] in
theorem Regs.call {c : EW} {n : Nat} {m m' : MachineData} (hr : Regs m0 c n m)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) : Regs m0 c n m' :=
  ⟨(hcs _ rfl).trans hr.x19, (hcs _ rfl).trans hr.x20, (hcs _ rfl).trans hr.x21,
    (hcs _ rfl).trans hr.x22, by rw [hcs _ rfl]; exact hr.x23, (hcs _ rfl).trans hr.x24,
    (hcs _ rfl).trans hr.x25, by rw [hcs _ rfl]; exact hr.x26, by rw [hcs _ rfl]; exact hr.x27⟩

omit [Host] in
theorem Regs.block [Labels] {c : EW} {n : Nat} {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState} (hr : Regs m0 c n m)
    (hm : Match (Env.ofMachine m rs) S m')
    (hk : [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27].all
      (fun r ↦ S.reg r == some (.reg r)) = true) : Regs m0 c n m' := by
  have K := Bus.KeepRegs.of_block hm hk
  exact ⟨(K _ (by simp)).trans hr.x19, (K _ (by simp)).trans hr.x20, (K _ (by simp)).trans hr.x21, (K _ (by simp)).trans hr.x22,
    by rw [K _ (by simp)]; exact hr.x23, (K _ (by simp)).trans hr.x24, (K _ (by simp)).trans hr.x25,
    by rw [K _ (by simp)]; exact hr.x26, by rw [K _ (by simp)]; exact hr.x27⟩

theorem two_pow_le (h : GkrStepPre a s0 g0 m0) : 16 * 2 ^ m0.regs.X1.toNat ≤ 64 := by
  rcases pre_step h with e | e <;> rw [e] <;> decide

/-- **`read_scalars(t, frame + o, 2^step)`**. -/
theorem rs_call (h : GkrStepPre a s0 g0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} {o : Nat} (ho : o + 64 ≤ 1296)
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0 = m0.regs.X0) (h1 : st.data.regs.X1.toBitVec = loc m0 o)
    (h2 : st.data.regs.X2.toNat = 2 ^ m0.regs.X1.toNat) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s)
    (cont : ∀ m2, Fr m0 1392 gkrStepStack slots keep (outs m0) m2 →
      m2.regs.X0 = okWord ((readScalars (2 ^ m0.regs.X1.toNat)).run s).isSome →
      (∀ ys s', (readScalars (2 ^ m0.regs.X1.toNat)).run s = some (ys, s') →
        NativeRustcVm.EWsAt m2.dmem (loc m0 o) ys.toList ∧
          TStateAt m2.dmem m0.regs.X0.toBitVec a s') →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data readScalarsStack) readScalarsStack q ∨
          (InRange (loc m0 o) (16 * 2 ^ m0.regs.X1.toNat) q ∨
            InRange m0.regs.X0.toBitVec tstateBytes q)) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have cx := ctx h
  have hat := Fr.at_ cx hfr (outs_not_rc h)
  have hn := two_pow_le h
  refine Fr.callLocal (o := o) (n := 16 * 2 ^ m0.regs.X1.toNat)
    (X := fun q ↦ InRange (loc m0 o) (16 * 2 ^ m0.regs.X1.toNat) q ∨
      InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr hS.2.1 le_rs keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrs s) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ ?_, hq.2.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfr.stackOk hS rfl le_rs, cx.rcAt hat le_rs, by rw [h0]; exact hts,
      by rw [h0]; exact cx.tstateOk hat le_rs, ?_⟩
    rw [h0, h1, h2]
    exact cx.outOk hat le_rs (o := o) (by omega)
  · rw [h0, h1, h2] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨hx0, hok, hnext, -, -⟩ := hq2
    rw [h2] at hx0 hok hnext
    rw [h1] at hok
    rw [h0] at hnext
    exact cont m2 hfr2 hx0 (fun ys s' he ↦ ⟨hok ys s' he, hnext ys s' he⟩) hcs2 hs2

/-- **A leaf call** from the frame: its contract changes its stack only. -/
theorem leaf_call (h : GkrStepPre a s0 g0 m0) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} (hle : 1392 + N' ≤ gkrStepStack)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → Changes m m' N' 0 0 ∧ Saved m m')
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, Fr m0 1392 gkrStepStack slots keep (outs m0) m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Changes st.data m2 N' 0 0 → Kept st.data.dmem m2.dmem →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.callSpec hfr (pre_stack h).2.1 hle keep_callee slots_le (outs_not_frame h) hspec hpc hP
    (fun _ hq ↦ ⟨Bus.changes_zero (hQ _ _ hq).1, (hQ _ _ hq).2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ cont m2 hfr2 hq2 hcs2 (hQ _ _ hq2).1 (hQ _ _ hq2).2.2.2

end

end NativeRustcVmArm.Bus.GkrStep
