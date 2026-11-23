module

public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Mid
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.IterB

/-!
# `each_row` with `next_level`'s closure: folding a row, its `What`s

At `b11` the row's lanes are at 600 (`lanes_of`'s `Some(n)`): `b12` calls `fold_row` on them with
the query and the rounds, `b13` keeps the folded value in X29, X25 and calls `subspace_at_table`
on the table at 104 and the query, the `What`s at 1624 (`iterB`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

variable [Host] {k : Nat}

/-- **From `b11` to `b14`.** -/
theorem iterB (hp : Placed code k) (hfold : Spec (label NativeRustcVmArm.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hpre : EachRowNextPre rows op m0) {m : MachineData} (h : Mid rows m0 j m)
    {lanes : Array EW} (hls : lanes.size ≤ 64) (hx0 : m.regs.X0 = 1)
    (hx1 : m.regs.X1 = lanes.size.toUInt64)
    (hlanes : EWsAt m.dmem (fb m0 + BitVec.ofNat 64 600) lanes.toList) {R : MachineState → Prop}
    (cont : ∀ m', Mid rows m0 j m' →
      (⟨m'.regs.getXReg .X29, m'.regs.getXReg .X25⟩ : EW) =
        foldRow lanes ((qsOf m0)[j]'h.hjq) (eachRowArgs m0).2 →
      BufWordsAt m'.dmem (fb m0 + BitVec.ofNat 64 1624) rootCap
        (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)).toList →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b14Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b11Offset)⟩ := by
  have hl := lay hpre
  have hstk := hpre.1.1
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  have hrdin := hpre.1.2.2.2.2.2.2.2
  have aprd := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk11 run_b11 hwf hm fun st8 hm8 hpc8 ↦ ?_
  have hpc8' : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b12Offset) := by
    simp only [PcOk] at hpc8
    sym_simp at hpc8
    simp only [Env.ofMachine_regs, show (m.regs.getXReg .X0) = 1 from hx0] at hpc8
    exact hpc8
  refine exec_at hk12 run_b12 hwf hpc8' hm8 fun st9 hm9 hpc9 ↦ ?_
  have hd9 : st9.data.dmem = m.dmem := hm9.dmem_eq hwf rfl
  have hmid9 : Mid rows m0 j st9.data :=
    h.block hm hm9 hwf rfl rfl (by decide)
  have e9x0 : st9.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 600 :=
    (hm9.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 600)
  have e9x1 : st9.data.regs.X1 = lanes.size.toUInt64 := ((rv hm9 (r := .X1) rfl).trans rfl).trans hx1
  have e9x2 : st9.data.regs.X2 = (qsOf m0)[j]'h.hjq :=
    ((rv hm9 (r := .X2) rfl).trans rfl).trans h.x26
  have hl64 : (Env.ofMachine m [(fb m0, 2000)]).load 0 64 8 = m0.regs.X5.toBitVec :=
    Ring.load_word (h.fr.slots (64, .X5) (by simp [slots]))
  have hl72 : (Env.ofMachine m [(fb m0, 2000)]).load 0 72 8 = m0.regs.X6.toBitVec :=
    Ring.load_word (h.fr.slots (72, .X6) (by simp [slots]))
  have e9x3 : st9.data.regs.X3 = m0.regs.X5 := (rv hm9 (r := .X3) rfl).trans
    (by show UInt64.ofBitVec ((Env.ofMachine m [(fb m0, 2000)]).load 0 64 8) = _; rw [hl64])
  have e9x4 : st9.data.regs.X4 = m0.regs.X6 := (rv hm9 (r := .X4) rfl).trans
    (by show UInt64.ofBitVec ((Env.ofMachine m [(fb m0, 2000)]).load 0 72 8) = _; rw [hl72])
  -- `fold_row`
  have hrd : WhirIn st9.data m0.regs.X5.toBitVec (roundBytes * m0.regs.X6.toNat) foldRowStack :=
    whirIn_input hpre hmid9.fr hrdin (by decide)
  have hP9 : FoldRowPre st9.data := by
    unfold FoldRowPre
    rw [e9x0, e9x3, e9x4]
    refine ⟨hmid9.fr.stackOk hstk (by decide) (by decide),
      whirIn_frame hpre hmid9.fr (by decide) (by decide) (by decide), hrd, ?_, hpre.1.2.2.2.2.2.2.1⟩
    have := Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hrdin.2
    unfold Apart at this ⊢
    rw [hl.frame_toNat (by decide)]
    rw [hl.base_F] at this
    have hlb : lanesBytes = 1024 := rfl
    omega
  refine call_then hpc9 hfold hP9 fun ⟨d10, pc10⟩ hpc10 ⟨hval, hch, hsv⟩ ↦ ?_
  simp only at hpc10
  subst hpc10
  rw [e9x0] at hch
  have hs10 : SameOutside st9.data.dmem d10.dmem (HitN m0) :=
    EachRow.hit_of_call hl hmid9.fr.sp (N' := foldRowStack) (o := 600) (n := 1024) (by decide)
      le_rfl (by decide) hch
  have hmid10 := hmid9.call hpre hs10 hsv
  have hfoldv : (⟨d10.regs.X0, d10.regs.X1⟩ : EW) =
      foldRow lanes ((qsOf m0)[j]'h.hjq) (eachRowArgs m0).2 := by
    refine hval.trans ?_
    rw [e9x0, e9x1, e9x2, e9x3, e9x4]
    have hn : min lanes.size.toUInt64.toNat laneCap = lanes.toList.length := by
      rw [natCast_toUInt64_toNat (by omega), Array.length_toList]
      exact Nat.min_eq_left hls
    rw [hn]
    unfold ewSlice
    rw [hd9, NativeRustcVm.ewsOf_of_ewsAt hlanes, Array.toArray_toList,
      EachRowOfFinalLevel.roundsOf_congr (input_same' hpre h.fr hrdin aprd)]
    rfl
  -- `b10`, `subspace_at_table`
  obtain ⟨hwf10, hm10⟩ := frame_env hpre hmid10.fr
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk13 run_b13 hwf10 hm10 fun st11 hm11 hpc11 ↦ ?_
  have hmid11 : Mid rows m0 j st11.data := hmid10.block hm10 hm11 hwf10 rfl rfl (by decide)
  have hd11 : st11.data.dmem = d10.dmem := hm11.dmem_eq hwf10 rfl
  let env10 := Env.ofMachine d10 [(fb m0, 2000)]
  have hlow := hmid10.low
  have hl24 : env10.load 0 56 8 = (fb m0 + BitVec.ofNat 64 104) := Ring.load_word hlow.w56
  have hl16 : env10.load 0 24 8 = (tableOf m0).size.toUInt64.toBitVec := Ring.load_word hlow.w24
  have hts : (tableOf m0).size ≤ 31 := by
    have := hlow.tab.1
    rw [Array.length_toList] at this
    exact this
  have e11x0 : st11.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 1624 :=
    (hm11.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 1624)
  have e11x1 : st11.data.regs.X1.toBitVec = fb m0 + BitVec.ofNat 64 104 :=
    (hm11.regs .X1 _ rfl).trans hl24
  have e11x2 : st11.data.regs.X2 = (tableOf m0).size.toUInt64 :=
    (rv hm11 (r := .X2) rfl).trans (by show UInt64.ofBitVec (env10.load 0 24 8) = _; rw [hl16])
  have e11x3 : st11.data.regs.X3 = (qsOf m0)[j]'h.hjq :=
    ((rv hm11 (r := .X3) rfl).trans rfl).trans hmid10.x26
  have hts' : (tableOf m0).size.toUInt64.toNat = (tableOf m0).size := natCast_toUInt64_toNat (by omega)
  have hP11 : SubspaceAtTablePre st11.data := by
    unfold SubspaceAtTablePre
    rw [e11x0, e11x1, e11x2, hts']
    refine ⟨hmid11.fr.stackOk hstk (by decide) (by decide), hts,
      whirIn_frame hpre hmid11.fr (by show 104 + 16 * _ ≤ 2000; omega) (by decide) (by decide),
      whirIn_frame hpre hmid11.fr (by decide) (by decide) (by decide), Or.inr ?_⟩
    rw [hl.frame_toNat (by decide), hl.frame_toNat (by decide)]
    omega
  refine call_then hpc11 hsat hP11 fun ⟨d12, pc12⟩ hpc12 ⟨hval12, hch12, hsv12⟩ ↦ ?_
  simp only at hpc12
  subst hpc12
  rw [e11x0] at hch12
  have hs12 : SameOutside st11.data.dmem d12.dmem (HitN m0) :=
    EachRow.hit_of_call hl hmid11.fr.sp (N' := subspaceAtTableStack) (o := 1624) (n := 256)
      (by decide) (by decide) (by decide) hch12
  have hmid12 := hmid11.call hpre hs12 hsv12
  refine cont d12 hmid12 ?_ ?_
  · rw [hsv12.1 .X29 rfl, hsv12.1 .X25 rfl, (rv hm11 (r := .X29) rfl).trans rfl,
      (rv hm11 (r := .X25) rfl).trans rfl]
    exact hfoldv
  · rw [e11x0, e11x1, e11x2, e11x3, hts', hd11] at hval12
    have hp : pairsOf d10.dmem (fb m0 + BitVec.ofNat 64 104) (tableOf m0).size =
        (tableOf m0).toList := by
      have := EachRow.pairsOf_of_pairsAt hlow.tab.2.2
      have e : off (fb m0 + BitVec.ofNat 64 96) 8 = fb m0 + BitVec.ofNat 64 104 :=
        NativeRustcVm.addr_add_add _ _ _
      rw [e, Array.length_toList] at this
      exact this
    rw [hp, Array.toArray_toList] at hval12
    exact hval12

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
