module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.FoldRound.Read4

/-!
# `fold_round`: the frame's words, `EW::mul`

`FW d m0 L`: the frame holds the words `L` (offset, value). Kept by calls writing below the frame
(`fw_call`), by blocks writing elsewhere (`fw_block`); a block's write (`fw_write`); read back by a
block (`fw_load`). `mul_call`: `EW::mul` from a state of the frame, the product in X0, X1.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

@[expose] public section

/-- The frame's words `L`. -/
def FW (d : Mem 64) (m0 : MachineData) (L : List (Nat × UInt64)) : Prop :=
  ∀ o v, (o, v) ∈ L → NativeRustcVm.WordAt d (loc m0 o) v

end

public section

section
variable {m0 : MachineData}

theorem FW.nil (d : Mem 64) (m0 : MachineData) : FW d m0 [] := fun _ _ h ↦ by cases h

theorem FW.cons {d : Mem 64} {o : Nat} {v : UInt64} {L : List (Nat × UInt64)}
    (h : NativeRustcVm.WordAt d (loc m0 o) v) (hL : FW d m0 L) : FW d m0 ((o, v) :: L) := by
  intro o' v' hp
  rcases List.mem_cons.mp hp with hp | hp
  · cases hp; exact h
  · exact hL o' v' hp

theorem FW.sub {d : Mem 64} {L L' : List (Nat × UInt64)} (h : FW d m0 L) (hs : ∀ p ∈ L', p ∈ L) :
    FW d m0 L' := fun o v hp ↦ h o v (hs _ hp)

end

section
variable [Labels] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **Across a call** writing below the frame and in the outputs. -/
theorem fw_call (h : FoldRoundPre a s0 w m0) {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 208 + N' ≤ foldRoundStack) {d' : Mem 64}
    (hs : SameOutside st.dmem d' fun q ↦ InRange (stackBelow st N') N' q ∨ outs m0 q)
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 208) (hw : FW st.dmem m0 L) :
    FW d' m0 L := fun o v hp ↦ by
  have := Fr.bytes_keep (o' := 0) (n' := 0) hf (pre_hN h) (ctx h).frame_outs hle (by decide)
    (NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inl hq
      · exact .inr (.inr hq)) (o := o) (bs := NativeRustcVm.wordBytes v)
    (by rw [NativeRustcVm.length_wordBytes]; exact hL _ hp) (.inr (by omega)) (hw o v hp)
  exact this

/-- **Across a block** whose writes miss the words. -/
theorem fw_block {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) (hwf : env.WF)
    (h0 : env.regions[0]? = some (base m0 208, 208)) {L : List (Nat × UInt64)}
    (hmiss : L.all (fun p ↦ missFrame S p.1 8 && decide (p.1 + 8 ≤ 208)) = true)
    (hw : FW env.mem0 m0 L) : FW m.dmem m0 L := fun o v hp ↦ by
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hmiss
  obtain ⟨h1, h2⟩ := hmiss _ hp
  exact bytes_block hm hwf h0 h1 h2 (NativeRustcVm.length_wordBytes _) (hw o v hp)

/-- **A block's write** of `v` at offset `o` of the frame. -/
theorem fw_write {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (h0 : env.regions[0]? = some (base m0 208, 208)) {o : Nat} (ho : o + 8 ≤ 208) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (loc m0 o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write h0 ho hw
  rw [wordBytes_reg] at this
  exact this

omit [Labels] in
/-- **A word read back** by a block of the frame. -/
theorem fw_load {env : Env} (hb0 : env.base 0 = base m0 208) {L : List (Nat × UInt64)}
    (hw : FW env.mem0 m0 L) {o : Nat} {v : UInt64} (hp : (o, v) ∈ L) :
    env.load 0 o 8 = v.toBitVec :=
  load_word (by rw [hb0]; exact hw o v hp)

end

/-! ## `EW::mul` -/

section
variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`EW::mul`** from a state of the frame: the product in X0, X1; memory changed below the
frame only. -/
theorem mul_call (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState}
    {next : Int64} {R : MachineState → Prop} (hf : FFr m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, FFr m0 m2 →
      m2.regs.X0 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c0 →
      m2.regs.X1 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (InRange (stackBelow st.data ewMulStack) ewMulStack) →
      Kept st.data.dmem m2.dmem → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.leaf hf (pre_hN h) (by decide) (fun _ h ↦ by cases h) slots_le (ctx h).frame_outs hmul
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ hq ↦ .inl hq, hq.2.2.2⟩) hpc
    ((ctx h).stackOk hf (by decide)) fun m2 hf2 hq hcs ↦
      cont m2 hf2 hq.1 hq.2.1 hcs hq.2.2.1 hq.2.2.2.2.2

end

end

end NativeRustcVmArm.Whir.FoldRound
