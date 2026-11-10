import Rv64Verifier.Sym.Facts
import Rv64Verifier.Image

/-!
# `walk`'s block at `0x800038a8`, in two

The generated block reads the claim's value at `sp + 1344` after storing it there through `s5`
(`= sp + 1344`), which its `noAlias` side conditions rule out. Split after the stores through
`s5`, each half's reads miss its own writes.
-/

namespace Rv64Verifier.Blocks.F4S

open Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64

def cfg : Config := { noAlias := true }

def c800038a8 : Expect :=
  { steps := 7,
      pc := Rv64Verifier.Sym.E.c 0x00000000800038c4#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10,
                Rv64Verifier.Sym.E.ld
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))
                    (Rv64Verifier.Sym.E.c 0x0000000000000010#64))),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
               (RiscvZkvm.Rv64.Reg.x14, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x14)),
               (RiscvZkvm.Rv64.Reg.x15, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x15)),
               (RiscvZkvm.Rv64.Reg.x16, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x16)),
               (RiscvZkvm.Rv64.Reg.x17, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x17)),
               (RiscvZkvm.Rv64.Reg.x18, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
               (RiscvZkvm.Rv64.Reg.x19, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19)),
               (RiscvZkvm.Rv64.Reg.x20, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20)),
               (RiscvZkvm.Rv64.Reg.x21, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
               (RiscvZkvm.Rv64.Reg.x22, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22)),
               (RiscvZkvm.Rv64.Reg.x23, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23)),
               (RiscvZkvm.Rv64.Reg.x24, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
               (RiscvZkvm.Rv64.Reg.x25, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25)),
               (RiscvZkvm.Rv64.Reg.x26, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26)),
               (RiscvZkvm.Rv64.Reg.x27, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                 off := 0x0000000000000010#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))
                   (Rv64Verifier.Sym.E.c 0x0000000000000010#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                 off := 0x0000000000000000#64 },
               Rv64Verifier.Sym.E.ld (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                 off := 0x0000000000000008#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))
                   (Rv64Verifier.Sym.E.c 0x0000000000000008#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x0000000000000538#64 },
               Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26))],
      writes := [{ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                   off := 0x0000000000000010#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                   off := 0x0000000000000000#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                   off := 0x0000000000000008#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x0000000000000538#64 }],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000010#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000010#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000010#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000010#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000000#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000010#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000000#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000000#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000008#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000008#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
                  off := 0x0000000000000008#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000000#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000538#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
                  off := 0x0000000000000008#64 }] }

theorem c800038a8_spec : BlockSpec Image.code 0x00000000800038a8#64 7
    (fun s ↦ Oblig.all s c800038a8.obl) c800038a8.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 7) (x := c800038a8)
    (words := (Image.code.words.drop 3626).take 7) (by decide +kernel)
    (CodeAt.slice Image.code 3626 7 0x00000000800038a8#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800038a8: 7 steps, then pc := 0x800038c4
     x10 := [x24 + 16]
     [x21 + 16] := [x24 + 16]
     [x21] := [x24]
     [x21 + 8] := [x24 + 8]
     [x2 + 1336] := x26
     needs valid8 x21 + 16, x24 + 16 ≠ x2 + 1336, x24 + 16 ≠ x21 + 8, x24 + 16 ≠ x21, valid8 x24 + 16, valid8 x21, x24 ≠ x2 + 1336, x24 ≠ x21 + 8, valid8 x24, valid8 x2...
-/

theorem c800038a8_x10 {s t : MachineState} (h : c800038a8.Holds s t) :
    t.getReg .x10 = s.getMem (s.getReg .x24 + 16) :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem c800038a8_keeps {s t : MachineState} (h : c800038a8.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem c800038a8_m_x21_16 {s t : MachineState} (h : c800038a8.Holds s t) :
    t.getMem (s.getReg .x21 + 16) = s.getMem (s.getReg .x24 + 16) :=
  h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038a8_m_x21_0 {s t : MachineState} (h : c800038a8.Holds s t) :
    t.getMem (s.getReg .x21) = s.getMem (s.getReg .x24) :=
  h.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038a8_m_x21_8 {s t : MachineState} (h : c800038a8.Holds s t) :
    t.getMem (s.getReg .x21 + 8) = s.getMem (s.getReg .x24 + 8) :=
  h.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038a8_m_x2_1336 {s t : MachineState} (h : c800038a8.Holds s t) :
    t.getMem (s.getReg .x2 + 1336) = s.getReg .x26 :=
  h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038a8_pc {s t : MachineState} (h : c800038a8.Holds s t) : t.pc = 0x800038c4 :=
  h.pc_eq rfl


def c800038c4 : Expect :=
  { steps := 18,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.bin
                (Rv64Verifier.Sym.BinOp.add)
                (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20))
                (Rv64Verifier.Sym.E.c 0xffffffffffffffff#64))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x0000000080003894#64)
              (Rv64Verifier.Sym.E.c 0x000000008000390c#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10,
                Rv64Verifier.Sym.E.ld
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                    (Rv64Verifier.Sym.E.c 0x0000000000000540#64))),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
               (RiscvZkvm.Rv64.Reg.x14, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x14)),
               (RiscvZkvm.Rv64.Reg.x15, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x15)),
               (RiscvZkvm.Rv64.Reg.x16, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x16)),
               (RiscvZkvm.Rv64.Reg.x17, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x17)),
               (RiscvZkvm.Rv64.Reg.x18, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
               (RiscvZkvm.Rv64.Reg.x19, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19)),
               (RiscvZkvm.Rv64.Reg.x20,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20))
                  (Rv64Verifier.Sym.E.c 0xffffffffffffffff#64)),
               (RiscvZkvm.Rv64.Reg.x21, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
               (RiscvZkvm.Rv64.Reg.x22, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22)),
               (RiscvZkvm.Rv64.Reg.x23, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23)),
               (RiscvZkvm.Rv64.Reg.x24,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))
                  (Rv64Verifier.Sym.E.c 0x0000000000000018#64)),
               (RiscvZkvm.Rv64.Reg.x25, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25)),
               (RiscvZkvm.Rv64.Reg.x26,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
               (RiscvZkvm.Rv64.Reg.x27,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27))
                  (Rv64Verifier.Sym.E.c 0x0000000000000038#64)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000020#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000540#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000028#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000548#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000030#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000550#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000000#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000520#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000008#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000528#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000010#64 },
               Rv64Verifier.Sym.E.ld
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.add)
                   (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                   (Rv64Verifier.Sym.E.c 0x0000000000000530#64))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                 off := 0x0000000000000018#64 },
               Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26))],
      writes := [{ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000020#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000028#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000030#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000000#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000008#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000010#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                   off := 0x0000000000000018#64 }],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000020#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000000#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000030#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000028#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000540#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000028#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000000#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000030#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000548#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000030#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000550#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000550#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000550#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000550#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000000#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000550#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000000#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000520#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000520#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000520#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000008#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000520#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000008#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000528#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000528#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000528#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000010#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000530#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000530#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
                  off := 0x0000000000000018#64 }
                8] }

theorem c800038c4_spec : BlockSpec Image.code 0x00000000800038c4#64 18
    (fun s ↦ Oblig.all s c800038c4.obl) c800038c4.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 18) (x := c800038c4)
    (words := (Image.code.words.drop 3633).take 18) (by decide +kernel)
    (CodeAt.slice Image.code 3633 18 0x00000000800038c4#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800038c4: 18 steps, then pc := if x20 - 1 ≠ 0 then 0x80003894 else 0x8000390c
     x10 := [x2 + 1344]
     x20 := x20 - 1
     x24 := x24 + 24
     x26 := x26 + 1
     x27 := x27 + 56
     [x27 + 32] := [x2 + 1344]
     [x27 + 40] := [x2 + 1352]
     [x27 + 48] := [x2 + 1360]
     [x27] := [x2 + 1312]
     [x27 + 8] := [x2 + 1320]
     [x27 + 16] := [x2 + 1328]
     [x27 + 24] := x26
     needs valid8 x27 + 32, x2 + 1344 ≠ x27 + 24, x2 + 1344 ≠ x27 + 16, x2 + 1344 ≠ x27 + 8, x2 + 1344 ≠ x27, x2 + 1344 ≠ x27 + 48, x2 + 1344 ≠ x27 + 40, valid8 x2 + 13...
-/

theorem c800038c4_x10 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getReg .x10 = s.getMem (s.getReg .x2 + 1344) :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem c800038c4_x20 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getReg .x20 = s.getReg .x20 - 1 :=
  h.reg_eq .x20 rfl (by rv_eval [])

theorem c800038c4_x24 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getReg .x24 = s.getReg .x24 + 24 :=
  h.reg_eq .x24 rfl (by rv_eval [])

theorem c800038c4_x26 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getReg .x26 = s.getReg .x26 + 1 :=
  h.reg_eq .x26 rfl (by rv_eval [])

theorem c800038c4_x27 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getReg .x27 = s.getReg .x27 + 56 :=
  h.reg_eq .x27 rfl (by rv_eval [])

theorem c800038c4_keeps {s t : MachineState} (h : c800038c4.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x21, .x22, .x23, .x25, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem c800038c4_m_x27_32 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 32) = s.getMem (s.getReg .x2 + 1344) :=
  h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_40 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 40) = s.getMem (s.getReg .x2 + 1352) :=
  h.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_48 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 48) = s.getMem (s.getReg .x2 + 1360) :=
  h.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_0 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27) = s.getMem (s.getReg .x2 + 1312) :=
  h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_8 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 8) = s.getMem (s.getReg .x2 + 1320) :=
  h.mem_eq 4 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_16 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 16) = s.getMem (s.getReg .x2 + 1328) :=
  h.mem_eq 5 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_m_x27_24 {s t : MachineState} (h : c800038c4.Holds s t) :
    t.getMem (s.getReg .x27 + 24) = s.getReg .x26 :=
  h.mem_eq 6 (by decide) (by rv_eval []) (by rv_eval [])

theorem c800038c4_pc_taken {s t : MachineState} (h : c800038c4.Holds s t) (hc : s.getReg .x20 - 1 ≠ (0 : Word)) :
    t.pc = 0x80003894 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem c800038c4_pc_not_taken {s t : MachineState} (h : c800038c4.Holds s t) (hc : s.getReg .x20 - 1 = (0 : Word)) :
    t.pc = 0x8000390c :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem c800038c4_frame {s t : MachineState} (h : c800038c4.Holds s t) (hb : (s.getReg .x27).toNat + 56 ≤ 2 ^ 64) :
    MemFrame s t (s.getReg .x27) 56 :=
  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])


end Rv64Verifier.Blocks.F4S
