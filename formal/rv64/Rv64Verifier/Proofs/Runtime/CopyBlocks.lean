import Rv64Verifier.Proofs.Runtime.Sub
import Rv64Verifier.Proofs.Runtime.Memcpy

/-!
# The blocks of a forward copy

`memcpy` and the forward half of `memmove` are the same code at different addresses
(`compiler_builtins::mem::impls::copy_forward`): a byte loop for fewer than 16 bytes; otherwise
the bytes up to the destination's next multiple of 8, then doublewords, loaded aligned when the
source is then aligned too, else shifted together from aligned loads of the source (through an
8-byte stack buffer filled by word, halfword and byte loads at any alignment); then the rest, a
byte at a time.

Each block's expectation is written once here with its targets as parameters (`FwdCode` names
them), and checked at both places by the symbolic executor with sub-doubleword accesses at any
address (`cfgA`, `Config.anyAlign`). Copies of the blocks at `memcpy`'s addresses are in the
comments.
-/

namespace Rv64Verifier.Runtime.Forward
open RiscvZkvm.Rv64 Rv64Verifier.Sym
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg decE tailCE)

def cfgA : Config := { noAlias := true, anyAlign := true }

/-- A block of `n` words of the image at `e`, from one kernel check with `cfgA`. -/
theorem spec_ofA {x : Expect} {e : Word} (i n : Nat)
    (hrun : (symRun cfgA ((Image.code.words.drop i).take n) e n).any (·.meets cfgA x) = true)
    (hpc : e.toNat = Image.code.base.toNat + 4 * i) (h4 : e.toNat % 4 = 0)
    (hr : e.toNat + 4 * n < 2 ^ 64) : Spec e x :=
  BlockSpec.of_expect hrun (CodeAt.slice Image.code i n e hpc h4 hr) (fun _ h ↦ h) fun _ _ _ h ↦ h

/-- At `0x80011ff8` in `memcpy`. -/
def spE (T : Word) : Expect where
  steps := 1
  pc := .c T
  regs := [(.x2, (.bin .add (.reg .x2) (.c 0xfffffffffffffff0)))] ++ keepE [.x2]
  mem := []
  writes := []
  obl := []

/-- At `0x80011ffc` in `memcpy`. -/
def sizeE (T F : Word) : Expect where
  steps := 2
  pc := .ite .ltu (.reg .x12) (.c 16) (.c T) (.c F)
  regs := [(.x13, (.c 16))] ++ keepE [.x13]
  mem := []
  writes := []
  obl := []

/-- At `0x8001212c` in `memcpy`. -/
def smallE (T F : Word) : Expect where
  steps := 3
  pc := .ite .ltu (.reg .x10) (.bin .add (.reg .x10) (.reg .x12)) (.c T) (.c F)
  regs := [(.x13, (.reg .x10)), (.x14, (.bin .add (.reg .x10) (.reg .x12)))] ++ keepE [.x13, .x14]
  mem := []
  writes := []
  obl := []

/-- At `0x80012138` in `memcpy`. -/
def jmpE (T : Word) : Expect where
  steps := 1
  pc := .c T
  regs := [] ++ keepE []
  mem := []
  writes := []
  obl := []

/-- At `0x80012004` in `memcpy`. -/
def headE (T F : Word) : Expect where
  steps := 4
  pc := .ite .geu (.reg .x10) (.bin .add (.reg .x10) (.bin .and (.bin .sub (.c 0) (.reg .x10)) (.c 7))) (.c T) (.c F)
  regs := [(.x13, (.bin .and (.bin .sub (.c 0) (.reg .x10)) (.c 7))), (.x14, (.bin .add (.reg .x10) (.bin .and (.bin .sub (.c 0) (.reg .x10)) (.c 7))))] ++ keepE [.x13, .x14]
  mem := []
  writes := []
  obl := []

/-- At `0x80012014` in `memcpy`. -/
def headPreE (T : Word) : Expect where
  steps := 3
  pc := .c T
  regs := [(.x15, (.reg .x13)), (.x16, (.reg .x10)), (.x17, (.reg .x11))] ++ keepE [.x15, .x16, .x17]
  mem := []
  writes := []
  obl := []

/-- At `0x80012038` in `memcpy`. -/
def setupE (T F : Word) : Expect where
  steps := 6
  pc := .ite .eq (.bin .and (.bin .add (.reg .x11) (.reg .x13)) (.c 7)) (.c 0) (.c T) (.c F)
  regs := [(.x11, (.bin .add (.reg .x11) (.reg .x13))), (.x12, (.bin .sub (.reg .x12) (.reg .x13))), (.x13, (.bin .add (.reg .x14) (.bin .and (.bin .sub (.reg .x12) (.reg .x13)) (.c 0xfffffffffffffff8)))), (.x15, (.bin .and (.bin .sub (.reg .x12) (.reg .x13)) (.c 0xfffffffffffffff8))), (.x16, (.bin .and (.bin .add (.reg .x11) (.reg .x13)) (.c 7)))] ++ keepE [.x11, .x12, .x13, .x15, .x16]
  mem := []
  writes := []
  obl := []

/-- At `0x8001213c` in `memcpy`. -/
def coE (T F : Word) : Expect where
  steps := 1
  pc := .ite .geu (.reg .x14) (.reg .x13) (.c T) (.c F)
  regs := [] ++ keepE []
  mem := []
  writes := []
  obl := []

/-- At `0x80012140` in `memcpy`. -/
def coPreE (T : Word) : Expect where
  steps := 1
  pc := .c T
  regs := [(.x16, (.reg .x11))] ++ keepE [.x16]
  mem := []
  writes := []
  obl := []

/-- At `0x80012144` in `memcpy`. -/
def coLoopE (T F : Word) : Expect where
  steps := 5
  pc := .ite .ltu (.bin .add (.reg .x14) (.c 8)) (.reg .x13) (.c T) (.c F)
  regs := [(.x14, (.bin .add (.reg .x14) (.c 8))), (.x16, (.bin .add (.reg .x16) (.c 8))), (.x17, (.ld (.reg .x16)))] ++ keepE [.x14, .x16, .x17]
  mem := [(⟨some (.reg .x14), 0⟩, (.ld (.reg .x16)))]
  writes := [⟨some (.reg .x14), 0⟩]
  obl := [.valid ⟨some (.reg .x14), 0⟩ 8, .valid ⟨some (.reg .x16), 0⟩ 8]

/-- At `0x80012158` in `memcpy`. -/
def tailBE (T F : Word) : Expect where
  steps := 4
  pc := .ite .geu (.reg .x13) (.bin .add (.reg .x13) (.bin .and (.reg .x12) (.c 7))) (.c T) (.c F)
  regs := [(.x11, (.bin .add (.reg .x11) (.reg .x15))), (.x12, (.bin .and (.reg .x12) (.c 7))), (.x14, (.bin .add (.reg .x13) (.bin .and (.reg .x12) (.c 7))))] ++ keepE [.x11, .x12, .x14]
  mem := []
  writes := []
  obl := []

/-- At `0x80012180` in `memcpy`. -/
def retE : Expect where
  steps := 2
  pc := (.bin .and (.reg .x1) (.c 0xfffffffffffffffe))
  regs := [(.x2, (.bin .add (.reg .x2) (.c 16)))] ++ keepE [.x2]
  mem := []
  writes := []
  obl := []

/-- At `0x80012050` in `memcpy`. -/
def sh0E (T F : Word) : Expect where
  steps := 8
  pc := .ite .ne (.bin .and (.bin .sub (.c 8) (.reg .x16)) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x5, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x16))), (.x6, (.bin .sub (.c 8) (.reg .x16))), (.x7, (.bin .and (.bin .sub (.c 8) (.reg .x16)) (.c 1))), (.x17, (.c 0))] ++ keepE [.x5, .x6, .x7, .x17]
  mem := [(⟨some (.reg .x2), 8⟩, (.c 0))]
  writes := [⟨some (.reg .x2), 8⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]

/-- At `0x80012070` in `memcpy`. -/
def pt2E (T F : Word) : Expect where
  steps := 2
  pc := .ite .ne (.bin .and (.reg .x6) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x7, (.bin .and (.reg .x6) (.c 2)))] ++ keepE [.x7]
  mem := []
  writes := []
  obl := []

/-- At `0x80012078` in `memcpy`. -/
def pt4E (T F : Word) : Expect where
  steps := 2
  pc := .ite .eq (.bin .and (.reg .x6) (.c 4)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x6) (.c 4)))] ++ keepE [.x6]
  mem := []
  writes := []
  obl := []

/-- At `0x80012080` in `memcpy`. -/
def pwE (T : Word) : Expect where
  steps := 4
  pc := .c T
  regs := [(.x6, (.bin (.ldx .w) (.ld (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 7)))), (.x17, (.bin .add (.reg .x5) (.reg .x17)))] ++ keepE [.x6, .x17]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .w (.ld (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 7)) (.bin (.ldx .w) (.ld (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .add (.reg .x5) (.reg .x17)), 0⟩ 4, .valid ⟨some (.bin .add (.reg .x11) (.reg .x17)), 0⟩ 4]

/-- At `0x80012090` in `memcpy`. -/
def peE (T F : Word) : Expect where
  steps := 5
  pc := .ite .geu (.bin .add (.reg .x14) (.c 8)) (.reg .x13) (.c T) (.c F)
  regs := [(.x5, (.ld (.bin .add (.reg .x2) (.c 8)))), (.x6, (.bin .add (.reg .x14) (.c 8))), (.x7, (.bin .sub (.reg .x11) (.reg .x16))), (.x17, (.bin .sll (.reg .x16) (.c 3)))] ++ keepE [.x5, .x6, .x7, .x17]
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]

/-- At `0x800120a4` in `memcpy`. -/
def lpreE (T : Word) : Expect where
  steps := 2
  pc := .c T
  regs := [(.x6, (.bin .and (.bin .sub (.c 0) (.reg .x17)) (.c 56)))] ++ keepE [.x6]
  mem := []
  writes := []
  obl := []

/-- At `0x800120ac` in `memcpy`. -/
def loopE (T F : Word) : Expect where
  steps := 10
  pc := .ite .ltu (.bin .add (.reg .x14) (.c 16)) (.reg .x13) (.c T) (.c F)
  regs := [(.x5, (.ld (.bin .add (.reg .x7) (.c 8)))), (.x7, (.bin .add (.reg .x7) (.c 8))), (.x14, (.bin .add (.reg .x14) (.c 8))), (.x28, (.bin .or (.bin .sll (.ld (.bin .add (.reg .x7) (.c 8))) (.reg .x6)) (.bin .srl (.reg .x5) (.reg .x17)))), (.x29, (.bin .add (.reg .x14) (.c 16)))] ++ keepE [.x5, .x7, .x14, .x28, .x29]
  mem := [(⟨some (.reg .x14), 0⟩, (.bin .or (.bin .sll (.ld (.bin .add (.reg .x7) (.c 8))) (.reg .x6)) (.bin .srl (.reg .x5) (.reg .x17))))]
  writes := [⟨some (.reg .x14), 0⟩]
  obl := [.valid ⟨some (.reg .x14), 0⟩ 8, .valid ⟨some (.reg .x7), 8⟩ 8]

/-- At `0x800120d4` in `memcpy`. -/
def afterE (T F : Word) : Expect where
  steps := 5
  pc := .ite .geu (.reg .x16) (.c 4) (.c T) (.c F)
  regs := [(.x6, (.c 0)), (.x7, (.bin .add (.reg .x7) (.c 8))), (.x28, (.c 4))] ++ keepE [.x6, .x7, .x28]
  mem := [(⟨some (.reg .x2), 8⟩, (.c 0))]
  writes := [⟨some (.reg .x2), 8⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]

/-- At `0x800120e8` in `memcpy`. -/
def qt2E (T F : Word) : Expect where
  steps := 2
  pc := .ite .ne (.bin .and (.reg .x11) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x16, (.bin .and (.reg .x11) (.c 2)))] ++ keepE [.x16]
  mem := []
  writes := []
  obl := []

/-- At `0x800120f0` in `memcpy`. -/
def qt1E (T F : Word) : Expect where
  steps := 2
  pc := .ite .eq (.bin .and (.reg .x11) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x16, (.bin .and (.reg .x11) (.c 1)))] ++ keepE [.x16]
  mem := []
  writes := []
  obl := []

/-- At `0x800120f8` in `memcpy`. -/
def qbE (T : Word) : Expect where
  steps := 5
  pc := .c T
  regs := [(.x6, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6))), (.x7, (.bin .add (.reg .x2) (.c 8))), (.x16, (.bin (.ldx .bu) (.ld (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 7))))] ++ keepE [.x6, .x7, .x16]
  mem := [(⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .b (.ld (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 7)) (.bin (.ldx .bu) (.ld (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)), 0⟩ 1, .valid ⟨some (.bin .add (.reg .x7) (.reg .x6)), 0⟩ 1]

/-- At `0x8001210c` in `memcpy`. -/
def finE (T : Word) : Expect where
  steps := 8
  pc := .c T
  regs := [(.x5, (.bin .srl (.reg .x5) (.reg .x17))), (.x16, (.bin .or (.bin .sll (.ld (.bin .add (.reg .x2) (.c 8))) (.bin .and (.bin .sub (.c 0) (.reg .x17)) (.c 56))) (.bin .srl (.reg .x5) (.reg .x17)))), (.x17, (.bin .and (.bin .sub (.c 0) (.reg .x17)) (.c 56)))] ++ keepE [.x5, .x16, .x17]
  mem := [(⟨some (.reg .x14), 0⟩, (.bin .or (.bin .sll (.ld (.bin .add (.reg .x2) (.c 8))) (.bin .and (.bin .sub (.c 0) (.reg .x17)) (.c 56))) (.bin .srl (.reg .x5) (.reg .x17))))]
  writes := [⟨some (.reg .x14), 0⟩]
  obl := [.valid ⟨some (.reg .x14), 0⟩ 8, .valid ⟨some (.reg .x2), 8⟩ 8]

/-- At `0x80012188` in `memcpy`. -/
def pbE (T F : Word) : Expect where
  steps := 5
  pc := .ite .eq (.bin .and (.reg .x6) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x7, (.bin .and (.reg .x6) (.c 2))), (.x17, (.c 1))] ++ keepE [.x7, .x17]
  mem := [(⟨some (.bin .and (.reg .x5) (.c 0xfffffffffffffff8)), 0⟩, (.stx .b (.ld (.bin .and (.reg .x5) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x5) (.c 7)) (.bin (.ldx .bu) (.ld (.bin .and (.reg .x11) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x11) (.c 7)))))]
  writes := [⟨some (.bin .and (.reg .x5) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.reg .x5), 0⟩ 1, .valid ⟨some (.reg .x11), 0⟩ 1]

/-- At `0x8001219c` in `memcpy`. -/
def phE (T F : Word) : Expect where
  steps := 7
  pc := .ite .ne (.bin .and (.reg .x6) (.c 4)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin .and (.reg .x6) (.c 4))), (.x7, (.bin (.ldx .h) (.ld (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 7)))), (.x17, (.bin (.w .add) (.reg .x17) (.c 2))), (.x28, (.bin .add (.reg .x5) (.reg .x17)))] ++ keepE [.x6, .x7, .x17, .x28]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .h (.ld (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 7)) (.bin (.ldx .h) (.ld (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x11) (.reg .x17)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x5) (.reg .x17)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .add (.reg .x5) (.reg .x17)), 0⟩ 2, .valid ⟨some (.bin .add (.reg .x11) (.reg .x17)), 0⟩ 2]

/-- At `0x800121bc` in `memcpy`. -/
def qwE (T F : Word) : Expect where
  steps := 5
  pc := .ite .eq (.bin .and (.reg .x11) (.c 2)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.c 4)), (.x16, (.bin .and (.reg .x11) (.c 2)))] ++ keepE [.x6, .x16]
  mem := [(⟨some (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .w (.ld (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 7)) (.bin (.ldx .w) (.ld (.bin .and (.reg .x7) (.c 0xfffffffffffffff8))) (.bin .and (.reg .x7) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .add (.reg .x2) (.c 8)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.reg .x2), 8⟩ 4, .valid ⟨some (.reg .x7), 0⟩ 4]

/-- At `0x800121d0` in `memcpy`. -/
def qhE (T F : Word) : Expect where
  steps := 8
  pc := .ite .ne (.bin .and (.reg .x11) (.c 1)) (.c 0) (.c T) (.c F)
  regs := [(.x6, (.bin (.w .add) (.reg .x6) (.c 2))), (.x16, (.bin .and (.reg .x11) (.c 1))), (.x28, (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)))] ++ keepE [.x6, .x16, .x28]
  mem := [(⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8)), 0⟩, (.stx .h (.ld (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 7)) (.bin (.ldx .h) (.ld (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 0xfffffffffffffff8))) (.bin .and (.bin .add (.reg .x7) (.reg .x6)) (.c 7)))))]
  writes := [⟨some (.bin .and (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)) (.c 0xfffffffffffffff8)), 0⟩]
  obl := [.valid ⟨some (.bin .or (.bin .add (.reg .x2) (.c 8)) (.reg .x6)), 0⟩ 2, .valid ⟨some (.bin .add (.reg .x7) (.reg .x6)), 0⟩ 2]

/-- The addresses of a forward copy's blocks. -/
structure FwdCode where
  size : Word
  small : Word
  jmp : Word
  bytes : Word
  ret : Word
  head : Word
  headPre : Word
  headLoop : Word
  setup : Word
  co : Word
  coPre : Word
  coLoop : Word
  tail : Word
  sh0 : Word
  pt2 : Word
  pt4 : Word
  pw : Word
  pe : Word
  lpre : Word
  loop : Word
  after : Word
  qt2 : Word
  qt1 : Word
  qb : Word
  fin : Word
  pb : Word
  ph : Word
  pj : Word
  qw : Word
  qh : Word
  qj : Word

/-- The blocks are at their addresses. -/
structure FwdCode.Ok (C : FwdCode) : Prop where
  size : Spec C.size (sizeE C.small C.head)
  small : Spec C.small (smallE C.bytes C.jmp)
  jmp : Spec C.jmp (jmpE C.ret)
  bytesExit : C.bytes + 24 = C.ret ∨ Spec (C.bytes + 24) (jmpE C.ret)
  head : Spec C.head (headE C.setup C.headPre)
  headPre : Spec C.headPre (headPreE C.headLoop)
  headLoop : C.headLoop + 24 = C.setup
  lbu1 : Image.code.fetch C.headLoop = some (.base (.LBU .x5 .x17 0))
  dec1 : Spec (C.headLoop + 4) (decE C.headLoop .x15)
  sb1 : Image.code.fetch (C.headLoop + 8) = some (.base (.SB .x16 .x5 0))
  tail1 : Spec (C.headLoop + 12) (tailCE C.headLoop .x15 .x16 .x17)
  lbu2 : Image.code.fetch C.bytes = some (.base (.LBU .x14 .x11 0))
  dec2 : Spec (C.bytes + 4) (decE C.bytes .x12)
  sb2 : Image.code.fetch (C.bytes + 8) = some (.base (.SB .x13 .x14 0))
  tail2 : Spec (C.bytes + 12) (tailCE C.bytes .x12 .x13 .x11)
  setup : Spec C.setup (setupE C.co C.sh0)
  co : Spec C.co (coE C.tail C.coPre)
  coPre : Spec C.coPre (coPreE C.coLoop)
  coLoop : Spec C.coLoop (coLoopE C.coLoop C.tail)
  tail : Spec C.tail (tailBE C.ret C.bytes)
  ret : Spec C.ret retE
  sh0 : Spec C.sh0 (sh0E C.pb C.pt2)
  pt2 : Spec C.pt2 (pt2E C.ph C.pt4)
  pt4 : Spec C.pt4 (pt4E C.pe C.pw)
  pw : Spec C.pw (pwE C.pe)
  pe : Spec C.pe (peE C.after C.lpre)
  lpre : Spec C.lpre (lpreE C.loop)
  loop : Spec C.loop (loopE C.loop C.after)
  after : Spec C.after (afterE C.qw C.qt2)
  qt2 : Spec C.qt2 (qt2E C.qh C.qt1)
  qt1 : Spec C.qt1 (qt1E C.fin C.qb)
  qb : Spec C.qb (qbE C.fin)
  fin : Spec C.fin (finE C.tail)
  pb : Spec C.pb (pbE C.pt4 C.ph)
  ph : Spec C.ph (phE C.pw C.pj)
  pj : Spec C.pj (jmpE C.pe)
  qw : Spec C.qw (qwE C.qt1 C.qh)
  qh : Spec C.qh (qhE C.qb C.qj)
  qj : Spec C.qj (jmpE C.fin)

/-! ## Reading a block -/

theorem keepOf {x : Expect} {u v : MachineState} (h : x.Holds u v) {L : List (Reg × E)}
    {l : List Reg} (hx : x.regs = L ++ keepE l) (R : List Reg) (hR : ∀ r ∈ R, r ∉ l := by decide) :
    ∀ r ∈ R, v.getReg r = u.getReg r :=
  fun r hr ↦ keepE_reg h (fun _ hp ↦ hx ▸ List.mem_append_right _ hp) (hR r hr)

theorem pcIte {x : Expect} {u v : MachineState} (h : x.Holds u v) {op : CmpOp} {a b : E}
    {T F : Word} (hx : x.pc = .ite op a b (.c T) (.c F)) :
    v.pc = if op.eval (a.eval u) (b.eval u) then T else F := by
  rw [h.1, hx]; rfl

theorem pcC {x : Expect} {u v : MachineState} (h : x.Holds u v) {T : Word} (hx : x.pc = .c T) :
    v.pc = T := by
  rw [h.1, hx]; rfl

theorem memOf {x : Expect} {u v : MachineState} (h : x.Holds u v) {k : Addr} {e : E}
    (hx : x.mem = [(k, e)]) : v.getMem (k.eval u) = e.eval u :=
  h.2.2.1 _ (by rw [hx]; exact List.mem_singleton_self _)

theorem frameOf {x : Expect} {u v : MachineState} (h : x.Holds u v) {k : Addr}
    (hx : x.writes = [k]) (a : Word) (ha : a ≠ k.eval u) : v.getMem a = u.getMem a :=
  h.frame a (by rw [hx]; simpa using ha)

theorem sameOf {x : Expect} {u v : MachineState} (h : x.Holds u v) (hx : x.writes = [])
    (a : Word) : v.getMem a = u.getMem a :=
  h.frame a (by rw [hx]; simp)

end Rv64Verifier.Runtime.Forward
