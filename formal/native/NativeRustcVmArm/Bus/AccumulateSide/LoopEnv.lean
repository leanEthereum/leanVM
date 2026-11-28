module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop6

/-!
# `accumulate_side`: the table loop's indexed layout reads
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- Layout heights and rows occupy the first 120 bytes. -/
theorem layout_ok (h : Pre L rows bl Fm SL m0) : ROk m0 0 (m0.regs.X5.toBitVec, 120) := by
  have hr := ROk.sub (o := 0) (n' := 120) h.layOk (by unfold layoutBytes; omega) (by decide)
  simpa only [NativeRustcVm.addr_add_zero] using hr

/-- The owner's scaled index, which cannot wrap. -/
theorem owner_index {env : Env} {o : Nat} (ho : o < 6)
    (hx : (Sym.reg .X20).eval env = o.toUInt64.toBitVec) :
    ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X20)).eval env).toNat = 8 * o := by
  change (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 ((Sym.reg .X20).eval env)).toNat = _
  rw [hx]
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Match the bounded owner and both pointer aliases used by `b33`. -/
theorem matchQ (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L32 m) :
    Match (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]) sQ m := by
  have hh := St.lift (D := L32) hst (by decide) 0 [(m0.regs.X5.toBitVec, 120)]
  refine match_ofMachine (sregions := [(F + 0, true), (120, false)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, trivial⟩
    (sp_eval hst.fr.sp _ _) trivial trivial ⟨?_, trivial⟩ ⟨?_, ?_, trivial⟩
  · dsimp only
    rw [Holds.evc hh (s := .reg .X20) (i := 96) (by decide)]
    change (blk (BA L rows bl) j).owner.toUInt64.toNat < 6
    rw [blk_eq hj]
    change bl[j].owner.toUInt64.toNat < 6
    have hb := (h.bown bl[j] (List.getElem_mem hj)).1
    change bl[j].owner < 6 at hb
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact hb
  · dsimp only
    rw [Holds.evc hh (s := .load 0 48 8) (i := 20) (by decide)]
    rfl
  · dsimp only
    rw [Holds.evc hh (s := .load 0 40 8) (i := 21) (by decide)]
    rfl

/-- An indexed word of the layout still has the entry's value. -/
theorem layout_load (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L32 m) {c : Nat}
    (hc : c + 8 * (blk (BA L rows bl) j).owner + 8 ≤ 120) :
    (Sym.loadx 1 c (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X20)) 8).eval
      (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]) =
      (NativeRustcVm.wordOf m0.dmem (m0.regs.X5.toBitVec +
        BitVec.ofNat 64 (c + 8 * (blk (BA L rows bl) j).owner))).toBitVec := by
  have hh := St.lift (D := L32) hst (by decide) 0 [(m0.regs.X5.toBitVec, 120)]
  have ho : (blk (BA L rows bl) j).owner < 6 := by
    rw [blk_eq hj]
    exact (h.bown bl[j] (List.getElem_mem hj)).1
  have hx : (Sym.reg .X20).eval (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]) =
      (blk (BA L rows bl) j).owner.toUInt64.toBitVec := Holds.evc hh (i := 96) (by decide)
  change (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]).load 1
    (c + ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X20)).eval _).toNat) 8 = _
  rw [owner_index ho hx]
  change (Sym.load 1 (c + 8 * (blk (BA L rows bl) j).owner) 8).eval _ = _
  rw [load_rk rfl, word_in h hst.fr h.layOk (NativeRustcVm.Apart.symm h.fL)
    (by unfold layoutBytes; omega)]

/-- Every owner's stored padding span takes the nonempty slice branch. -/
theorem padding_guard {env : Env} {o : Nat} (ho : o < 6)
    (h21 : env.regs .X21 =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toBitVec)
    (h22 : env.regs .X22 =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toBitVec) :
    SBool.eval env (.not (.ite
      (.not (.cmp .ult .W64 (.bin .add .W64 (.reg .X21) (.reg .X22)) (.reg .X22)))
      (.not (.cmp .ult .W64 (.bin .add .W64 (.reg .X21) (.reg .X22)) (.lit 154)))
      (.lit true))) = true := by
  simp only [SBool.eval, Sym.eval, h21, h22]
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The padding start's scaled address. -/
theorem padding_addr {env : Env} {o : Nat} (ho : o < 6)
    (h22 : env.regs .X22 =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toBitVec) :
    (Sym.bin .add .W64 (.label NativeRustcVmArm.Vm.Symbols.rodata5Label)
      (.un (.shift .LSL 4) .W64 (.reg .X22))).eval env =
      NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 *
        (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat) := by
  simp only [Sym.eval, h22, BinOp.apply, low_W64, ext_W64]
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

end NativeRustcVmArm.Bus.AccumulateSide
