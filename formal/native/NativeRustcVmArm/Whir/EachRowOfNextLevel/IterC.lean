module

public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.IterB

/-!
# `each_row` with `next_level`'s closure: `What` `μ`, `novel_eval`

At `b14` the `What`s are at 1624: `b14` reads `μ` through its address at 48 and, below the
`What`s' count, `b15` reads `What` `μ` into X27 (else `0`); `b16` calls `novel_eval` on the high
part and the `What`s, its `Option<EW>` at 1880 (`iterC`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- A scaled index register, as the executor computes it. -/
theorem idx_eval [Labels] {env : Env} {r : XReg} {n : Nat} (h : env.regs r = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 61) :
    ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg r)).eval env).toNat = 8 * n := by
  simp only [Sym.eval, UnOp.apply, h]
  simp [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq, BitVec.toNat_ofInt]
  omega

/-- **A block** from any environment over the entry's memory, without writes, keeping SP and the
loop's registers. -/
theorem Mid.blockE [Labels] {m m' : MachineData} {env : Env} {S S' : SState}
    (h : Mid rows m0 j m) (hm : Match env S m) (hm' : Match env S' m') (hwf : env.WF)
    (hd : m.dmem = env.mem0) (hmem : S'.mem = []) (hsp : S'.sp = S.sp)
    (hk : ∀ r ∈ loopRegs, m'.regs.getXReg r = m.regs.getXReg r) : Mid rows m0 j m' := by
  have hd' : m'.dmem = m.dmem := (hm'.dmem_eq hwf hmem).trans hd.symm
  refine ⟨Ring.Fr.ofBlock h.fr hm hm' hwf hd hmem hsp (by simp), hd' ▸ h.low, h.hj, h.hjq,
    hd' ▸ h.bat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk .X19 (by simp [loopRegs]), h.x19]
  · rw [hk .X20 (by simp [loopRegs]), h.x20]
  · rw [hk .X21 (by simp [loopRegs]), h.x21]
  · rw [hk .X22 (by simp [loopRegs]), h.x22]
  · rw [hk .X23 (by simp [loopRegs]), h.x23]
  · rw [hk .X24 (by simp [loopRegs]), h.x24]
  · rw [hk .X26 (by simp [loopRegs]), h.x26]

variable [Host] {k : Nat}

/-- **From `b14` to `b17`.** -/
theorem iterC (hp : Placed code k) (hnov : Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (hpre : EachRowNextPre rows op m0) {m : MachineData} (h : Mid rows m0 j m) {F : EW}
    (hF : (⟨m.regs.getXReg .X29, m.regs.getXReg .X25⟩ : EW) = F)
    (hW : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1624) rootCap
      (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)).toList) {R : MachineState → Prop}
    (cont : ∀ m', Mid rows m0 j m' → (⟨m'.regs.getXReg .X29, m'.regs.getXReg .X25⟩ : EW) = F →
      m'.regs.getXReg .X27 =
        (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)).getD m0.regs.X4.toNat 0 →
      OptEWAt m'.dmem (fb m0 + BitVec.ofNat 64 1880)
        (some (novelEval (highOf m0) (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)))) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b17Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b14Offset)⟩ := by
  have hl := lay hpre
  have hstk := hpre.1.1
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  have hpre' := hpre
  obtain ⟨-, -, hmuin, hmu, hhlen, hhigh, -, -, -, -, apmu, -, -, -, -, aphigh, -⟩ := hpre'
  have hbt : (fb m0).toNat = m0.regs.SP.toNat - 2000 := hl.base_F
  obtain ⟨W, hWdef⟩ : ∃ W, W = subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq) := ⟨_, rfl⟩
  rw [← hWdef] at hW cont
  have hWs : W.size ≤ 31 := by have := hW.1; rw [Array.length_toList] at this; exact this
  have hult : (W.size.toUInt64.toBitVec).ult (BitVec.ofNat 64 32) = true := by
    rw [toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)]
    simp
    omega
  have hWs' : W.size.toUInt64.toNat = W.size := natCast_toUInt64_toNat (by omega)
  have hwords : WordsAt m.dmem (fb m0 + BitVec.ofNat 64 1632) W.toList := by
    have := hW.2.2
    rwa [show fb m0 + BitVec.ofNat 64 1624 + 8#64 = fb m0 + BitVec.ofNat 64 1632 from
      NativeRustcVm.addr_add_add _ _ _] at this
  -- `b14`
  let env := Env.ofMachine m [(fb m0, 2000), ((nextEnv m0 0).toBitVec, 8)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ h.fr.kept _ (hmuin.1.1 i hi), hmuin.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
        (Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hmuin.2)))
  have hl48 : env.load 0 48 8 = (nextEnv m0 0).toBitVec := Ring.load_word h.low.w48
  have hm : Match env muS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show env.load 0 48 8 = (nextEnv m0 0).toBitVec + BitVec.ofInt 64 0
        rw [hl48]
        simp, trivial⟩
  have hmuv : env.load 1 0 8 = m0.regs.X4.toBitVec := by
    rw [Ring.load_eq_wordOf]
    show (NativeRustcVm.wordOf m.dmem ((nextEnv m0 0).toBitVec + BitVec.ofNat 64 0)).toBitVec = _
    have hsame := input_same' hpre h.fr hmuin apmu
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
      have := hsame i (by omega); exact this, hmu]
  have hl1624 : env.load 0 1624 8 = W.size.toUInt64.toBitVec := by
    have := hW.2.1
    rw [Array.length_toList] at this
    exact Ring.load_word this
  have hl16 : env.load 0 16 8 = fb m0 + BitVec.ofNat 64 1632 := Ring.load_word h.low.w16
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk14 run_b14 hwf hm fun st14 hm14 hpc14 ↦ ?_
  have hd14 : st14.data.dmem = m.dmem := hm14.dmem_eq hwf rfl
  have k14 : ∀ r, (after b14 muS).reg r = some (.reg r) →
      st14.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (rv hm14 (by rw [← after_eq run_b14]; exact hr)).trans rfl
  have hmid14 : Mid rows m0 j st14.data :=
    h.blockE hm hm14 hwf rfl rfl rfl fun r hr ↦ k14 r (by
      rw [after_eq run_b14]
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have e14x3 : st14.data.regs.X3.toBitVec = fb m0 + BitVec.ofNat 64 1632 := by
    refine (hm14.regs .X3 _ rfl).trans ?_
    sym_simp
    rw [hl1624, hult, hl16]
    rfl
  have e14x4 : st14.data.regs.X4 = W.size.toUInt64 := by
    refine (rv hm14 (r := .X4) rfl).trans ?_
    sym_simp
    rw [hl1624, hult]
    rfl
  have e14x8 : st14.data.regs.getXReg .X8 = m0.regs.X4 :=
    (rv hm14 (r := .X8) rfl).trans (by show UInt64.ofBitVec (env.load 1 0 8) = _; rw [hmuv])
  have hF14 : (⟨st14.data.regs.getXReg .X29, st14.data.regs.getXReg .X25⟩ : EW) = F := by
    rw [k14 .X29 rfl, k14 .X25 rfl]; exact hF
  -- `b16`, from either path
  have at16 : ∀ (d : MachineData), Mid rows m0 j d → d.dmem = m.dmem →
      d.regs.X3.toBitVec = fb m0 + BitVec.ofNat 64 1632 → d.regs.X4 = W.size.toUInt64 →
      (⟨d.regs.getXReg .X29, d.regs.getXReg .X25⟩ : EW) = F →
      d.regs.getXReg .X27 = W.getD m0.regs.X4.toNat 0 →
      Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b16Offset)⟩ := by
    intro d hd hdd e3 e4 hFd h27
    obtain ⟨hwf16, hm16⟩ := frame_env hpre hd.fr
    let env16 := Env.ofMachine d [(fb m0, 2000)]
    have hl40 : env16.load 0 40 8 = (nextEnv m0 1).toBitVec := Ring.load_word hd.low.w40
    have hl32 : env16.load 0 32 8 = (nextEnv m0 2).toBitVec := Ring.load_word hd.low.w32
    have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_then hk16 run_b16 hwf16 hm16 fun st16 hm16' hpc16 ↦ ?_
    have hmid16 : Mid rows m0 j st16.data := hd.block hm16 hm16' hwf16 rfl rfl (by decide)
    have hd16 : st16.data.dmem = d.dmem := hm16'.dmem_eq hwf16 rfl
    have e0 : st16.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 1880 :=
      (hm16'.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 1880)
    have e1 : st16.data.regs.X1 = nextEnv m0 1 :=
      (rv hm16' (r := .X1) rfl).trans (by show UInt64.ofBitVec (env16.load 0 40 8) = _; rw [hl40])
    have e2 : st16.data.regs.X2 = nextEnv m0 2 :=
      (rv hm16' (r := .X2) rfl).trans (by show UInt64.ofBitVec (env16.load 0 32 8) = _; rw [hl32])
    have e3' : st16.data.regs.X3.toBitVec = fb m0 + BitVec.ofNat 64 1632 :=
      (hm16'.regs .X3 _ rfl).trans e3
    have e4' : st16.data.regs.X4 = W.size.toUInt64 := ((rv hm16' (r := .X4) rfl).trans rfl).trans e4
    have hP : NovelEvalPre st16.data := by
      unfold NovelEvalPre
      rw [e0, e1, e2, e3', e4', hWs']
      exact ⟨hmid16.fr.stackOk hstk (by decide) (by decide),
        ⟨⟨fun i hi ↦ hmid16.fr.kept _ (hhigh.1.1 i hi), hhigh.1.2⟩,
          hmid16.fr.apart hstk.2.1 hhigh.2 (by decide)⟩,
        whirIn_frame hpre hmid16.fr (by show 1632 + 8 * _ ≤ 2000; omega) (by decide) (by decide),
        whirIn_frame hpre hmid16.fr (by decide) (by decide) (by decide)⟩
    refine call_then hpc16 hnov hP fun ⟨d17, pc17⟩ hpc17 ⟨hval, hch, hsv⟩ ↦ ?_
    simp only at hpc17
    subst hpc17
    rw [e0] at hch
    have hs17 : SameOutside st16.data.dmem d17.dmem (HitN m0) :=
      EachRow.hit_of_call hl hmid16.fr.sp (N' := novelEvalStack) (o := 1880) (n := 24)
        (by decide) (by decide) (by decide) hch
    have hmid17 := hmid16.call hpre hs17 hsv
    have k17 : ∀ r, calleeSaved r = true → (after b16 frameS).reg r = some (.reg r) →
        d17.regs.getXReg r = d.regs.getXReg r := fun r hc hr ↦ by
      rw [hsv.1 r hc]
      exact (rv hm16' (by rw [← after_eq run_b16]; exact hr)).trans rfl
    refine cont d17 hmid17 (by rw [k17 .X29 rfl rfl, k17 .X25 rfl rfl]; exact hFd)
      (by rw [k17 .X27 rfl rfl]; exact h27) ?_
    rw [e0, e1, e2, e3', e4', hWs'] at hval
    simp only [hhlen, ↓reduceIte] at hval
    have hsl : slice st16.data (nextEnv m0 1) (nextEnv m0 2) = highOf m0 := by
      unfold slice
      rw [hd16, hdd, NativeRustcVm.ewsOf_congr (input_same' hpre h.fr hhigh aphigh)]
      rfl
    have hws : wordSlice st16.data (fb m0 + BitVec.ofNat 64 1632) W.size = W := by
      unfold wordSlice
      rw [hd16, hdd]
      have := NativeRustcVm.wordsOf_of_wordsAt hwords
      rw [Array.length_toList] at this
      rw [this, Array.toArray_toList]
    rw [hsl, hws] at hval
    exact hval
  simp only [PcOk] at hpc14
  sym_simp at hpc14
  rw [hmuv, hl1624, hult] at hpc14
  have hmu4 : m0.regs.X4.toNat ≤ 30 := hpre.1.2.2.2.2.2.1
  by_cases hlt : m0.regs.X4.toNat < W.size
  · -- `What` `μ`
    have hc : (m0.regs.X4.toBitVec.ult W.size.toUInt64.toBitVec) = true := by
      simp only [BitVec.ult, UInt64.toNat_toBitVec, hWs']
      simpa using hlt
    simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc14
    have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
    obtain ⟨hwf15, hm15⟩ := frame_env hpre hmid14.fr
    let env15 := Env.ofMachine st14.data [(fb m0, 2000)]
    have hx8 : env15.regs .X8 = BitVec.ofNat 64 m0.regs.X4.toNat := by
      show (st14.data.regs.getXReg .X8).toBitVec = _
      rw [e14x8]
      simp
    have hm15' : Match env15 whatS st14.data :=
      match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
        (by rw [hmid14.fr.sp]; simp [Sym.eval])
        ⟨by show st14.data.regs.X3.toBitVec = _; rw [e14x3]; simp [Sym.eval], trivial⟩ trivial
        ⟨by
          show (env15.regs .X8).toNat < 31
          rw [hx8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega, trivial⟩ trivial
    refine exec_at hk15 run_b15 hwf15 hpc14 hm15' fun st15 hm15 hpc15 ↦ ?_
    have hd15 : st15.data.dmem = st14.data.dmem := hm15.dmem_eq hwf15 rfl
    have hmid15 : Mid rows m0 j st15.data := hmid14.blockE hm15' hm15 hwf15 rfl rfl rfl
      fun r hr ↦ (rv hm15 (v := .reg r) (by
        simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans rfl
    simp only [PcOk] at hpc15
    have hb15 : b15.length = NativeRustcVmArm.Vm.EachRowOfNextLevel.b15Length := NativeRustcVmArm.Vm.EachRowOfNextLevel.b15_length
    rw [hb15] at hpc15
    obtain ⟨d15, pc15⟩ := st15
    simp only at hpc15
    subst hpc15
    refine at16 d15 hmid15 (hd15.trans hd14) ((hm15.regs .X3 _ rfl).trans ?_)
      (((rv hm15 (r := .X4) rfl).trans rfl).trans e14x4) ?_ ?_
    · show (Sym.ptr 0 1632).eval env15 = _
      exact EachRow.eval_ptr0 _ _ _ _ 1632
    · rw [(rv hm15 (r := .X29) rfl).trans rfl, (rv hm15 (r := .X25) rfl).trans rfl]
      exact hF14
    · refine (rv hm15 (r := .X27) rfl).trans ?_
      show UInt64.ofBitVec (env15.load 0 (1632 + ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64
        (.reg .X8)).eval env15).toNat) 8) = _
      rw [idx_eval hx8 (by omega)]
      have hwm := NativeRustcVm.wordsAt_getElem hwords (i := m0.regs.X4.toNat)
        (by rw [Array.length_toList]; exact hlt)
      rw [NativeRustcVm.addr_add_add, ← hd14] at hwm
      rw [Ring.load_word hwm, UInt64.ofBitVec_toBitVec, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hlt]
      simp
  · -- past the `What`s
    have hc : (m0.regs.X4.toBitVec.ult W.size.toUInt64.toBitVec) = false := by
      simp only [BitVec.ult, UInt64.toNat_toBitVec, hWs']
      simpa using hlt
    simp only [hc, Bool.not_false, ↓reduceIte] at hpc14
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b16Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b16Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_9_at]
      at hpc14
    obtain ⟨d14, pc14⟩ := st14
    simp only at hpc14
    subst hpc14
    refine at16 d14 hmid14 hd14 e14x3 e14x4 hF14 ?_
    refine (rv hm14 (r := .X27) rfl).trans ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
