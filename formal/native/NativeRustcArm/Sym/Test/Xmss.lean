module

public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.Sym

/-!
# The executor on `xmss_verify`'s first blocks

Its first block (the prologue: callee-saved registers stored by `STP` with pre-index writeback,
the 5872-byte frame allocated with stack probes `ldr xzr, [sp]`, `memset`'s arguments, `bl memset`)
and its second (64- and 32-bit loads from the signature, stack stores of 64-bit pairs and of a
32-bit word, a 32-bit `mov`), copied from rustc's assembly as Kraken terms. Region 0 is the stack
frame below SP at entry, region 1 the signature X0 points to.
-/

namespace NativeRustcArm.Sym.Test.Xmss

set_option Elab.async false

/-- The prologue, ending in `bl memset`. -/
def entry : List Directive := [
  @Kraken.Directive.label Instr ConstExpr NativeRustcArm.Xmss.XmssVerify.entryLabel,  -- xmss_verify:
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X29) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X30) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (-96 : Int64)) (@Option.some Index Index.Pre)))))),  -- stp x29, x30, [sp, #-96]!
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X28) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X27) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (16 : Int64)) (@Option.none Index)))))),  -- stp x28, x27, [sp, #16]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X26) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X25) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (32 : Int64)) (@Option.none Index)))))),  -- stp x26, x25, [sp, #32]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X24) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X23) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (48 : Int64)) (@Option.none Index)))))),  -- stp x24, x23, [sp, #48]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X22) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X21) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (64 : Int64)) (@Option.none Index)))))),  -- stp x22, x21, [sp, #64]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X20) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X19) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (80 : Int64)) (@Option.none Index)))))),  -- stp x20, x19, [sp, #80]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ADD_e RegWidth.W64 (RegOrSp.low (XRegOrSp.reg XReg.X29) RegWidth.W64) (RegOrSp.low XRegOrSp.SP RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (0 : Int64)) ImmShift.S0)))),  -- mov x29, sp
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.SUB_e RegWidth.W64 (RegOrSp.low XRegOrSp.SP RegWidth.W64) (RegOrSp.low XRegOrSp.SP RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (1 : Int64)) ImmShift.S12)))),  -- sub sp, sp, #1, lsl #12
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low XRegOrXzr.XZR RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (0 : Int64)) (@Option.none Index))))))),  -- ldr xzr, [sp]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.SUB_e RegWidth.W64 (RegOrSp.low XRegOrSp.SP RegWidth.W64) (RegOrSp.low XRegOrSp.SP RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (1680 : Int64)) ImmShift.S0)))),  -- sub sp, sp, #1680
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ADD_e RegWidth.W64 (RegOrSp.low (XRegOrSp.reg XReg.X19) RegWidth.W64) (RegOrSp.low XRegOrSp.SP RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (44 : Int64)) ImmShift.S0)))),  -- add x19, sp, #44
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low XRegOrXzr.XZR RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (0 : Int64)) (@Option.none Index))))))),  -- ldr xzr, [sp]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ORR_s RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X20) RegWidth.W64) (RegOrZr.low XRegOrXzr.XZR RegWidth.W64) (@ShiftRegExpr.mk RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X0) RegWidth.W64) (0 : Int64) ShiftType.LSL))),  -- mov x20, x0
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ADD_e RegWidth.W64 (RegOrSp.low (XRegOrSp.reg XReg.X21) RegWidth.W64) (RegOrSp.low XRegOrSp.SP RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (1 : Int64)) ImmShift.S12)))),  -- add x21, sp, #1, lsl #12
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ADD_e RegWidth.W64 (RegOrSp.low (XRegOrSp.reg XReg.X0) RegWidth.W64) (RegOrSp.low (XRegOrSp.reg XReg.X19) RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (4 : Int64)) ImmShift.S0)))),  -- add x0, x19, #4
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W32 (@Operation.ORR_s RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X1) RegWidth.W32) (RegOrZr.low XRegOrXzr.XZR RegWidth.W32) (@ShiftRegExpr.mk RegWidth.W32 (RegOrZr.low XRegOrXzr.XZR RegWidth.W32) (0 : Int64) ShiftType.LSL))),  -- mov w1, wzr
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W32 (@Operation.MOVZ RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X2) RegWidth.W32) (ConstExpr.int64 (2400 : Int64)) (@MovShift.LSL0 RegWidth.W32))),  -- mov w2, #2400
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.ADD_e RegWidth.W64 (RegOrSp.low (XRegOrSp.reg XReg.X21) RegWidth.W64) (RegOrSp.low (XRegOrSp.reg XReg.X21) RegWidth.W64) (ExtOrImmReg.imm (ImmExpr.mk (ConstExpr.int64 (1296 : Int64)) ImmShift.S0)))),  -- add x21, x21, #1296
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (Operation.BL (ConstExpr.label NativeRustcArm.Common.Memset.entryLabel)))  -- bl memset
]

/-- The block after `memset` returns. -/
def afterMemset : List Directive := [
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X8) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1056 : Int64)) (@Option.none Index))))))),  -- ldr x8, [x20, #1056]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X9) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1064 : Int64)) (@Option.none Index))))))),  -- ldr x9, [x20, #1064]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X10) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1072 : Int64)) (@Option.none Index))))))),  -- ldr x10, [x20, #1072]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X12) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1080 : Int64)) (@Option.none Index))))))),  -- ldr x12, [x20, #1080]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X24) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1088 : Int64)) (@Option.none Index))))))),  -- ldr x24, [x20, #1088]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X11) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1048 : Int64)) (@Option.none Index))))))),  -- ldr x11, [x20, #1048]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X8) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X9) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (8 : Int64)) (@Option.none Index)))))),  -- stp x8, x9, [sp, #8]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X8) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1024 : Int64)) (@Option.none Index))))))),  -- ldr x8, [x20, #1024]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X9) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1032 : Int64)) (@Option.none Index))))))),  -- ldr x9, [x20, #1032]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W32 (@Operation.ORR_s RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X23) RegWidth.W32) (RegOrZr.low XRegOrXzr.XZR RegWidth.W32) (@ShiftRegExpr.mk RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X24) RegWidth.W32) (0 : Int64) ShiftType.LSL))),  -- mov w23, w24
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.STP RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X10) RegWidth.W64) (RegOrZr.low (XRegOrXzr.reg XReg.X12) RegWidth.W64) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (24 : Int64)) (@Option.none Index)))))),  -- stp x10, x12, [sp, #24]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W32 (@Operation.MOVZ RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X12) RegWidth.W32) (ConstExpr.int64 (1120 : Int64)) (@MovShift.LSL0 RegWidth.W32))),  -- mov w12, #1120
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W64 (@Operation.LDR RegWidth.W64 (RegOrZr.low (XRegOrXzr.reg XReg.X10) RegWidth.W64) (AddrOrLit.addr (AddrExpr.mk (RegOrSp.low (XRegOrSp.reg XReg.X20) RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (1040 : Int64)) (@Option.none Index))))))),  -- ldr x10, [x20, #1040]
  @Kraken.Directive.instr Instr ConstExpr (Instr.mk RegWidth.W32 (@Operation.STR RegWidth.W32 (RegOrZr.low (XRegOrXzr.reg XReg.X24) RegWidth.W32) (AddrExpr.mk (RegOrSp.low XRegOrSp.SP RegWidth.W64) (AddrOff.imm (ImmAddrExpr.mk (ConstExpr.int64 (44 : Int64)) (@Option.none Index))))))  -- str w24, [sp, #44]
]

/-- At entry: SP the top of the 5872-byte frame (region 0), X0 the signature (region 1). -/
def atEntry : SState := init [(5872, true), (2400, false)] (.ptr 0 5872) [(.X0, .ptr 1 0)]

sym_block entry_exec := exec entry atEntry

/-- After `memset`: SP the frame's base, X19 and X20 as the prologue left them. -/
def atReturn : SState :=
  init [(5872, true), (2400, false)] (.ptr 0 0) [(.X19, .ptr 0 44), (.X20, .ptr 1 0)]

sym_block afterMemset_exec := exec afterMemset atReturn

open NativeRustcArm in
/-- The prologue calls `memset` with the return address after the `bl` in X30, X0 the frame at
offset 48, W1 zero, X2 2400; SP the frame's base; the entry's X30 saved at the frame's top. -/
theorem entry_spec [Host] {k : Nat} (hk : entry.IsInfixAt Host.prog k) {env : Env}
    (hwf : env.WF) {m : MachineData} (hm : Match env atEntry m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Labels.label NativeRustcArm.Common.Memset.entryLabel ∧
      retOf st.data = Host.addrOf (k + entry.length) ∧
      (st.data.regs.getXReg .X0).toBitVec = env.base 0 + 48#64 ∧
      (st.data.regs.getXReg .X1).toBitVec = 0#64 ∧
      (st.data.regs.getXReg .X2).toBitVec = 2400#64 ∧
      st.data.regs.SP.toBitVec = env.base 0 ∧
      (st.data.regs.getXReg .X20).toBitVec = env.base 1 ∧
      Mem.loadInt st.data.dmem (env.base 0 + 5784#64) 8 = some ((env.regs .X30).toNat : Int))
      ⟨m, Host.addrOf k⟩ := by
  refine NativeRustcArm.Eventually.mono (exec_sound hk entry_exec hwf hm) fun st ⟨hm', hpc⟩ =>
    ⟨hpc.1, hpc.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm'.regs .X0 _ rfl]
    rfl
  · rw [hm'.regs .X1 _ rfl]
    rfl
  · rw [hm'.regs .X2 _ rfl]
    rfl
  · rw [hm'.sp]
    simp [Sym.eval]
  · rw [hm'.regs .X20 _ rfl]
    simp [Sym.eval]
  · rw [hm'.read hwf (r := 0) (o := 5784) (n := 8) rfl (by decide) (by decide)]
    rfl

end NativeRustcArm.Sym.Test.Xmss
