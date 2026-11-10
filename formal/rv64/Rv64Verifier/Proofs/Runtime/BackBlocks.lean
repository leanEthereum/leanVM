import Rv64Verifier.Proofs.Runtime.CopyBlocks

/-!
# The blocks of `memmove`'s backward copy

When the destination is above the source and they overlap, `memmove` (`0x8001228c`) copies from
the end (`compiler_builtins::mem::impls::copy_backward`): a byte loop for fewer than 16 bytes;
otherwise the bytes down to the destination end's multiple of 8, then doublewords down, aligned
loads when the source is then aligned too, else shifted together from aligned loads of the source
with two fills of the stack buffer; then the rest, a byte at a time. Each block's expectation,
checked by the symbolic executor with sub-doubleword accesses at any address (`cfgA`).
-/

namespace Rv64Verifier.Runtime.Backward
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Forward
open Rv64Verifier.Runtime.Memcpy (keepE)

/-- At `0x8001228c`. -/
def entryE (T F : Word) : Expect where
  steps := 3
  pc := .ite .geu (.bin .sub (.reg .x10) (.reg .x11)) (.reg .x12) (.c T) (.c F)
  regs := [(.x2, (.bin .add (.reg .x2) (.c 0xfffffffffffffff0))), (.x13, (.bin .sub (.reg .x10) (.reg .x11)))] ++ keepE [.x2, .x13]
  mem := []
  writes := []
  obl := []


/-- At `0x80012298`. -/
def b1E (T F : Word) : Expect where
  steps := 4
  pc := .ite .ltu (.reg .x12) (.c 16) (.c T) (.c F)
  regs := [(.x13, (.c 16)), (.x14, (.bin .add (.reg .x11) (.reg .x12))), (.x17, (.bin .add (.reg .x10) (.reg .x12)))] ++ keepE [.x13, .x14, .x17]
  mem := []
  writes := []
  obl := []


/-- At `0x800122a8`. -/
def b2E (T F : Word) : Expect where
  steps := 4
  pc := .ite .geu (.bin .and (.reg .x17) (.c 0xfffffffffffffff8)) (.reg .x17) (.c T) (.c F)
  regs := [(.x5, (.bin .sub (.c 0) (.bin .and (.reg .x17) (.c 7)))), (.x13, (.bin .and (.reg .x17) (.c 0xfffffffffffffff8))), (.x15, (.bin .and (.reg .x17) (.c 7)))] ++ keepE [.x5, .x13, .x15]
  mem := []
  writes := []
  obl := []


/-- At `0x800122b8`. -/
def b3E (T : Word) : Expect where
  steps := 3
  pc := .c T
  regs := [(.x6, (.reg .x17)), (.x16, (.bin .add (.bin .add (.reg .x11) (.reg .x12)) (.c 0xffffffffffffffff)))] ++ keepE [.x6, .x16]
  mem := []
  writes := []
  obl := []


/-- At `0x800122dc`. -/
def b4E (T F : Word) : Expect where
  steps := 7
  pc := .ite .eq (.bin .and (.bin .add (.reg .x14) (.reg .x5)) (.c 7)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.bin .add (.reg .x14) (.reg .x5)) (.c 7))), (.x7, (.bin .sub (.reg .x13) (.bin .and (.bin .sub (.reg .x12) (.reg .x15)) (.c 0xfffffffffffffff8)))), (.x14, (.bin .add (.reg .x14) (.reg .x5))), (.x15, (.bin .sub (.reg .x12) (.reg .x15))), (.x16, (.bin .sub (.c 0) (.bin .and (.bin .sub (.reg .x12) (.reg .x15)) (.c 0xfffffffffffffff8))))] ++ keepE [.x6, .x7, .x14, .x15, .x16]
  mem := []
  writes := []
  obl := []


/-- At `0x800122f8`. -/
def sb0E (T F : Word) : Expect where
  steps := 5
  pc := .ite .geu (.reg .x6) (.c 4) (.c T) (.c F)
  regs := [(.x28, (.c 0)), (.x29, (.bin .sub (.reg .x14) (.reg .x6))), (.x30, (.c 4))] ++ keepE [.x28, .x29, .x30]
  mem := [(⟨some (.reg .x2), 8⟩, (.c 0))]
  writes := [⟨some (.reg .x2), 8⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]


/-- At `0x8001230c`. -/
def st2E (T F : Word) : Expect where
  steps := 2
  pc := .ite .ne (.bin .and (.reg .x14) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x30, (.bin .and (.reg .x14) (.c 2)))] ++ keepE [.x30]
  mem := []
  writes := []
  obl := []


/-- At `0x80012314`. -/
def st1E (T F : Word) : Expect where
  steps := 2
  pc := .ite .eq (.bin .and (.reg .x14) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x30, (.bin .and (.reg .x14) (.c 1)))] ++ keepE [.x30]
  mem := []
  writes := []
  obl := []


/-- At `0x8001231c`. -/
def sbbE (T : Word) : Expect where
  steps := 5
  pc := .c T
  regs := [(.x28, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28))), (.x30, (.bin (.ldx .bu) (.ld (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 7)))), (.x31, (.bin .add (.reg .x2) (.c 8)))] ++ keepE [.x28, .x30, .x31]
  mem := [(⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .b (.ld (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 7)) (.bin (.ldx .bu) (.ld (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)), 0⟩ 1, .valid ⟨some (.bin .add (.reg .x29) (.reg .x28)), 0⟩ 1]


/-- At `0x80012330`. -/
def seE (T F : Word) : Expect where
  steps := 4
  pc := .ite .geu (.bin .add (.reg .x7) (.c 8)) (.reg .x13) (.c T) (.c F)
  regs := [(.x7, (.bin .sll (.reg .x6) (.c 3))), (.x28, (.ld (.bin .add (.reg .x2) (.c 8)))), (.x30, (.bin .add (.reg .x7) (.c 8)))] ++ keepE [.x7, .x28, .x30]
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]


/-- At `0x80012340`. -/
def slpreE (T : Word) : Expect where
  steps := 4
  pc := .c T
  regs := [(.x12, (.bin .and (.bin .sub (.c 0) (.reg .x7)) (.c 56))), (.x29, (.bin .add (.reg .x11) (.bin .sub (.reg .x12) (.reg .x6)))), (.x31, (.bin .sub (.reg .x12) (.reg .x6)))] ++ keepE [.x12, .x29, .x31]
  mem := []
  writes := []
  obl := []


/-- At `0x80012350`. -/
def sloopE (T F : Word) : Expect where
  steps := 12
  pc := .ite .ltu (.reg .x30) (.bin .add (.bin .add (.reg .x17) (.c 0xfffffffffffffff8)) (.reg .x5)) (.c T) (.c F)
  regs := [(.x11, (.bin .add (.bin .add (.reg .x17) (.c 0xfffffffffffffff8)) (.reg .x5))), (.x17, (.bin .add (.reg .x17) (.c 0xfffffffffffffff8))), (.x28, (.ld (.bin .add (.bin .add (.reg .x29) (.reg .x5)) (.c 0xfffffffffffffff8)))), (.x29, (.bin .add (.reg .x29) (.c 0xfffffffffffffff8))), (.x31, (.bin .add (.reg .x17) (.reg .x5)))] ++ keepE [.x11, .x17, .x28, .x29, .x31]
  mem := [(⟨some (.bin .add (.reg .x17) (.reg .x5)), 0xfffffffffffffff8⟩, (.bin .or (.bin .srl (.ld (.bin .add (.bin .add (.reg .x29) (.reg .x5)) (.c 0xfffffffffffffff8))) (.reg .x7)) (.bin .sll (.reg .x28) (.reg .x12))))]
  writes := [⟨some (.bin .add (.reg .x17) (.reg .x5)), 0xfffffffffffffff8⟩]
  obl := [.valid ⟨some (.bin .add (.reg .x17) (.reg .x5)), 0xfffffffffffffff8⟩ 8, .valid ⟨some (.bin .add (.reg .x29) (.reg .x5)), 0xfffffffffffffff8⟩ 8]


/-- At `0x80012380`. -/
def slafterE (T : Word) : Expect where
  steps := 2
  pc := .c T
  regs := [(.x29, (.bin .add (.reg .x29) (.reg .x5)))] ++ keepE [.x29]
  mem := []
  writes := []
  obl := []


/-- At `0x80012574`. -/
def slskipE (T : Word) : Expect where
  steps := 1
  pc := .c T
  regs := [(.x11, (.reg .x13))] ++ keepE [.x11]
  mem := []
  writes := []
  obl := []


/-- At `0x80012578`. -/
def saE (T F : Word) : Expect where
  steps := 10
  pc := .ite .ne (.bin .and (.bin .sub (.c 8) (.reg .x6)) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x5, (.bin .add (.bin .add (.reg .x29) (.reg .x6)) (.c 0xfffffffffffffff8))), (.x6, (.bin .and (.bin .sub (.c 8) (.reg .x6)) (.c 1))), (.x12, (.c 0)), (.x17, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6))), (.x29, (.bin .sub (.c 8) (.reg .x6))), (.x30, (.bin .add (.reg .x2) (.c 8)))] ++ keepE [.x5, .x6, .x12, .x17, .x29, .x30]
  mem := [(⟨some (.reg .x2), 8⟩, (.c 0))]
  writes := [⟨some (.reg .x2), 8⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]


/-- At `0x800125a0`. -/
def sat2E (T F : Word) : Expect where
  steps := 2
  pc := .ite .ne (.bin .and (.reg .x29) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x29) (.c 2)))] ++ keepE [.x6]
  mem := []
  writes := []
  obl := []


/-- At `0x800125a8`. -/
def sat4E (T F : Word) : Expect where
  steps := 2
  pc := .ite .eq (.bin .and (.reg .x29) (.c 4)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x29) (.c 4)))] ++ keepE [.x6]
  mem := []
  writes := []
  obl := []


/-- At `0x800125b0`. -/
def sawE (T : Word) : Expect where
  steps := 4
  pc := .c T
  regs := [(.x5, (.bin (.ldx .w) (.ld (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 7)))), (.x12, (.bin .add (.reg .x17) (.reg .x12)))] ++ keepE [.x5, .x12]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .w (.ld (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 7)) (.bin (.ldx .w) (.ld (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .add (.reg .x17) (.reg .x12)), 0⟩ 4, .valid ⟨some (.bin .add (.reg .x5) (.reg .x12)), 0⟩ 4]


/-- At `0x800125c0`. -/
def sfinE (T : Word) : Expect where
  steps := 7
  pc := .c T
  regs := [(.x12, (.bin .or (.bin .srl (.ld (.bin .add (.reg .x2) (.c 8))) (.reg .x7)) (.bin .sll (.reg .x28) (.bin .and (.bin .sub (.c 0) (.reg .x7)) (.c 56))))), (.x17, (.bin .sll (.reg .x28) (.bin .and (.bin .sub (.c 0) (.reg .x7)) (.c 56))))] ++ keepE [.x12, .x17]
  mem := [(⟨some (.reg .x11), 0xfffffffffffffff8⟩, (.bin .or (.bin .srl (.ld (.bin .add (.reg .x2) (.c 8))) (.reg .x7)) (.bin .sll (.reg .x28) (.bin .and (.bin .sub (.c 0) (.reg .x7)) (.c 56)))))]
  writes := [⟨some (.reg .x11), 0xfffffffffffffff8⟩]
  obl := [.valid ⟨some (.reg .x11), 0xfffffffffffffff8⟩ 8, .valid ⟨some (.reg .x2), 8⟩ 8]


/-- At `0x800125dc`. -/
def tailbE (T : Word) : Expect where
  steps := 3
  pc := .c T
  regs := [(.x12, (.bin .and (.reg .x15) (.c 7))), (.x14, (.bin .add (.reg .x14) (.reg .x16))), (.x17, (.bin .add (.reg .x13) (.reg .x16)))] ++ keepE [.x12, .x14, .x17]
  mem := []
  writes := []
  obl := []


/-- At `0x800125e8`. -/
def btailE (T F : Word) : Expect where
  steps := 2
  pc := .ite .geu (.bin .sub (.reg .x17) (.reg .x12)) (.reg .x17) (.c T) (.c F)
  regs := [(.x11, (.bin .sub (.reg .x17) (.reg .x12)))] ++ keepE [.x11]
  mem := []
  writes := []
  obl := []


/-- At `0x800125f0`. -/
def btpreE (T : Word) : Expect where
  steps := 1
  pc := .c T
  regs := [(.x14, (.bin .add (.reg .x14) (.c 0xffffffffffffffff)))] ++ keepE [.x14]
  mem := []
  writes := []
  obl := []


/-- At `0x800124c8`. -/
def bcoE (T F : Word) : Expect where
  steps := 1
  pc := .ite .geu (.reg .x7) (.reg .x13) (.c T) (.c F)
  regs := [] ++ keepE []
  mem := []
  writes := []
  obl := []


/-- At `0x800124cc`. -/
def bcopreE (T : Word) : Expect where
  steps := 3
  pc := .c T
  regs := [(.x11, (.bin .add (.bin .add (.reg .x15) (.reg .x11)) (.c 0xfffffffffffffff8))), (.x12, (.reg .x13))] ++ keepE [.x11, .x12]
  mem := []
  writes := []
  obl := []


/-- At `0x800124d8`. -/
def bcoloopE (T F : Word) : Expect where
  steps := 6
  pc := .ite .ltu (.reg .x7) (.bin .add (.reg .x12) (.c 0xfffffffffffffff8)) (.c T) (.c F)
  regs := [(.x5, (.bin .add (.reg .x12) (.c 0xfffffffffffffff8))), (.x11, (.bin .add (.reg .x11) (.c 0xfffffffffffffff8))), (.x12, (.bin .add (.reg .x12) (.c 0xfffffffffffffff8))), (.x17, (.ld (.reg .x11)))] ++ keepE [.x5, .x11, .x12, .x17]
  mem := [(⟨some (.reg .x12), 0xfffffffffffffff8⟩, (.ld (.reg .x11)))]
  writes := [⟨some (.reg .x12), 0xfffffffffffffff8⟩]
  obl := [.valid ⟨some (.reg .x12), 0xfffffffffffffff8⟩ 8, .valid ⟨some (.reg .x11), 0⟩ 8]


/-- At `0x80012680`. -/
def sabE (T F : Word) : Expect where
  steps := 5
  pc := .ite .eq (.bin .and (.reg .x29) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x29) (.c 2))), (.x12, (.c 1))] ++ keepE [.x6, .x12]
  mem := [(⟨some (.bin .and (.reg .x17) (.c 0xfffffffffffffff8)), 0⟩, (.stx .b (.ld (.bin .and (.reg .x17) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x17) (.c 7)) (.bin (.ldx .bu) (.ld (.bin .and (.reg .x5) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x5) (.c 7)))))]
  writes := [⟨some (.bin .and (.reg .x17) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.reg .x17), 0⟩ 1, .valid ⟨some (.reg .x5), 0⟩ 1]


/-- At `0x80012694`. -/
def sahE (T F : Word) : Expect where
  steps := 7
  pc := .ite .ne (.bin .and (.reg .x29) (.c 4)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x29) (.c 4))), (.x12, (.bin (.w .add) (.reg .x12) (.c 2))), (.x30, (.bin .add (.reg .x17) (.reg .x12)))] ++ keepE [.x6, .x12, .x30]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .h (.ld (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 7)) (.bin (.ldx .h) (.ld (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x5) (.reg .x12)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x17) (.reg .x12)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .add (.reg .x17) (.reg .x12)), 0⟩ 2, .valid ⟨some (.bin .add (.reg .x5) (.reg .x12)), 0⟩ 2]


/-- At `0x8001253c`. -/
def sbwE (T F : Word) : Expect where
  steps := 5
  pc := .ite .eq (.bin .and (.reg .x14) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x28, (.c 4)), (.x30, (.bin .and (.reg .x14) (.c 2)))] ++ keepE [.x28, .x30]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .w (.ld (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 7)) (.bin (.ldx .w) (.ld (.bin .and (.reg .x29) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x29) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 4, .valid ⟨some (.reg .x29), 0⟩ 4]


/-- At `0x80012550`. -/
def sbhE (T F : Word) : Expect where
  steps := 8
  pc := .ite .ne (.bin .and (.reg .x14) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x28, (.bin (.w .add) (.reg .x28) (.c 2))), (.x30, (.bin .and (.reg .x14) (.c 1))), (.x31, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)))] ++ keepE [.x28, .x30, .x31]
  mem := [(⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .h (.ld (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 7)) (.bin (.ldx .h) (.ld (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x29) (.reg .x28)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x28)), 0⟩ 2, .valid ⟨some (.bin .add (.reg .x29) (.reg .x28)), 0⟩ 2]

/-- The byte loops copying down (`0x800122c4`, `0x800125f4`): the byte at `rs` to `rd - 1`, both
pointers down by one, `rt` the byte and `rt'` the new `rd`, back unless `rd - 1` reached `rl`. -/
def bloopE (rd rs rt rt' rl : Reg) (T F : Word) : Expect where
  steps := 6
  pc := .ite .ltu (.reg rl) (.bin .add (.reg rd) (.c 0xffffffffffffffff)) (.c T) (.c F)
  regs := [(rd, (.bin .add (.reg rd) (.c 0xffffffffffffffff))), (rt, (.bin (.ldx .bu) (.ld (.bin .and (.reg rs) (.c 0xfffffffffffffff8))) (.bin .and (.reg rs) (.c 7)))), (rs, (.bin .add (.reg rs) (.c 0xffffffffffffffff))), (rt', (.bin .add (.reg rd) (.c 0xffffffffffffffff)))] ++ keepE [rd, rt, rs, rt']
  mem := [(⟨some (.bin .and (.bin .add (.reg rd) (.c 0xffffffffffffffff)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .b (.ld (.bin .and (.bin .add (.reg rd) (.c 0xffffffffffffffff)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg rd) (.c 0xffffffffffffffff)) (.c 7)) (.bin (.ldx .bu) (.ld (.bin .and (.reg rs) (.c 0xfffffffffffffff8))) (.bin .and (.reg rs) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg rd) (.c 0xffffffffffffffff)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.reg rd), 0xffffffffffffffff⟩ 1, .valid ⟨some (.reg rs), 0⟩ 1]

theorem mm_entry : Spec 0x8001228c (entryE 0x80012388 0x80012298) :=
  spec_ofA 18595 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_b1 : Spec 0x80012298 (b1E 0x800125e8 0x800122a8) :=
  spec_ofA 18598 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_b2 : Spec 0x800122a8 (b2E 0x800122dc 0x800122b8) :=
  spec_ofA 18602 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_b3 : Spec 0x800122b8 (b3E 0x800122c4) :=
  spec_ofA 18606 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_b4 : Spec 0x800122dc (b4E 0x800124c8 0x800122f8) :=
  spec_ofA 18615 7 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sb0 : Spec 0x800122f8 (sb0E 0x8001253c 0x8001230c) :=
  spec_ofA 18622 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_st2 : Spec 0x8001230c (st2E 0x80012550 0x80012314) :=
  spec_ofA 18627 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_st1 : Spec 0x80012314 (st1E 0x80012330 0x8001231c) :=
  spec_ofA 18629 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sbb : Spec 0x8001231c (sbbE 0x80012330) :=
  spec_ofA 18631 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_se : Spec 0x80012330 (seE 0x80012574 0x80012340) :=
  spec_ofA 18636 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_slpre : Spec 0x80012340 (slpreE 0x80012350) :=
  spec_ofA 18640 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sloop : Spec 0x80012350 (sloopE 0x80012350 0x80012380) :=
  spec_ofA 18644 12 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_slafter : Spec 0x80012380 (slafterE 0x80012578) :=
  spec_ofA 18656 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_slskip : Spec 0x80012574 (slskipE 0x80012578) :=
  spec_ofA 18781 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sa : Spec 0x80012578 (saE 0x80012680 0x800125a0) :=
  spec_ofA 18782 10 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sat2 : Spec 0x800125a0 (sat2E 0x80012694 0x800125a8) :=
  spec_ofA 18792 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sat4 : Spec 0x800125a8 (sat4E 0x800125c0 0x800125b0) :=
  spec_ofA 18794 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_saw : Spec 0x800125b0 (sawE 0x800125c0) :=
  spec_ofA 18796 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sfin : Spec 0x800125c0 (sfinE 0x800125dc) :=
  spec_ofA 18800 7 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_tailb : Spec 0x800125dc (tailbE 0x800125e8) :=
  spec_ofA 18807 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_btail : Spec 0x800125e8 (btailE 0x8001260c 0x800125f0) :=
  spec_ofA 18810 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_btpre : Spec 0x800125f0 (btpreE 0x800125f4) :=
  spec_ofA 18812 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_bco : Spec 0x800124c8 (bcoE 0x800125dc 0x800124cc) :=
  spec_ofA 18738 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_bcopre : Spec 0x800124cc (bcopreE 0x800124d8) :=
  spec_ofA 18739 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_bcoloop : Spec 0x800124d8 (bcoloopE 0x800124d8 0x800124f0) :=
  spec_ofA 18742 6 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sab : Spec 0x80012680 (sabE 0x800125a8 0x80012694) :=
  spec_ofA 18848 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sah : Spec 0x80012694 (sahE 0x800125b0 0x800126b0) :=
  spec_ofA 18853 7 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sbw : Spec 0x8001253c (sbwE 0x80012314 0x80012550) :=
  spec_ofA 18767 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sbh : Spec 0x80012550 (sbhE 0x8001231c 0x80012570) :=
  spec_ofA 18772 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_coj : Spec 0x800124f0 (jmpE 0x800125dc) :=
  spec_ofA 18748 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_saj : Spec 0x800126b0 (jmpE 0x800125c0) :=
  spec_ofA 18860 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_sbj : Spec 0x80012570 (jmpE 0x80012330) :=
  spec_ofA 18780 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_ret : Spec 0x8001260c retE :=
  spec_ofA 18819 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_hloop : Spec 0x800122c4 (bloopE .x6 .x16 .x7 .x28 .x13 0x800122c4 0x800122dc) :=
  spec_ofA 18609 6 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem mm_btloop : Spec 0x800125f4 (bloopE .x17 .x14 .x12 .x13 .x11 0x800125f4 0x8001260c) :=
  spec_ofA 18813 6 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end Rv64Verifier.Runtime.Backward
