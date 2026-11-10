import Rv64Verifier.Sym.Facts
import Rv64Verifier.Image

/-!
# Sub-blocks of `Bytecode::new`'s loop

Pieces of `main`'s blocks between `0x80000520` and `0x800009b0` around the halfword and byte
accesses the generated blocks (`Blocks/F3.lean`) make only at an 8-aligned base: each access is
stepped by hand, and the instructions before and after it are checked here, as `rv64-gen` checks a
block.
-/

namespace Rv64Verifier.Proofs.Main.NB

open Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64

def cfg : Config := { noAlias := true }

def g80000524 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.bin
                (Rv64Verifier.Sym.BinOp.add)
                (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10))
                (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25))
              (Rv64Verifier.Sym.E.c 0x0000000080000520#64)
              (Rv64Verifier.Sym.E.c 0x000000008000052c#64),
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
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10))
                  (Rv64Verifier.Sym.E.c 0x0000000000000004#64)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000524_spec : BlockSpec Image.code 0x0000000080000524#64 2
    (fun s ↦ Oblig.all s g80000524.obl) g80000524.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000524)
    (words := (Image.code.words.drop 329).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 329 2 0x0000000080000524#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000524: 2 steps, then pc := if x10 + 4 ≠ x25 then 0x80000520 else 0x8000052c
     x10 := x10 + 4
-/

theorem g80000524_x10 {s t : MachineState} (h : g80000524.Holds s t) :
    t.getReg .x10 = s.getReg .x10 + 4 :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem g80000524_keeps {s t : MachineState} (h : g80000524.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000524_pc_taken {s t : MachineState} (h : g80000524.Holds s t) (hc : s.getReg .x10 + 4 ≠ s.getReg .x25) :
    t.pc = 0x80000520 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem g80000524_pc_not_taken {s t : MachineState} (h : g80000524.Holds s t) (hc : s.getReg .x10 + 4 = s.getReg .x25) :
    t.pc = 0x8000052c :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem g80000524_mem_same {s t : MachineState} (h : g80000524.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g8000059c : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.c 0x00000000800005a4#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x16))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9))
                    (Rv64Verifier.Sym.E.c 0x0000000000000001#64))),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g8000059c_spec : BlockSpec Image.code 0x000000008000059c#64 2
    (fun s ↦ Oblig.all s g8000059c.obl) g8000059c.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g8000059c)
    (words := (Image.code.words.drop 359).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 359 2 0x000000008000059c#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x8000059c: 2 steps, then pc := 0x800005a4
     x12 := x16 + (x9 <<< 1)
-/

theorem g8000059c_x12 {s t : MachineState} (h : g8000059c.Holds s t) :
    t.getReg .x12 = s.getReg .x16 + (s.getReg .x9 * (2 : Word)) :=
  h.reg_eq .x12 rfl (by rv_eval [])

theorem g8000059c_keeps {s t : MachineState} (h : g8000059c.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g8000059c_pc {s t : MachineState} (h : g8000059c.Holds s t) : t.pc = 0x800005a4 :=
  h.pc_eq rfl

theorem g8000059c_mem_same {s t : MachineState} (h : g8000059c.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800005bc : Expect :=
  { steps := 6,
      pc := Rv64Verifier.Sym.E.c 0x00000000800005d4#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.srl)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.mul)
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19))
                        (Rv64Verifier.Sym.E.ld (Rv64Verifier.Sym.E.c 0x00000000a0000018#64)))
                      (Rv64Verifier.Sym.E.c 0x0000000000000031#64))
                    (Rv64Verifier.Sym.E.c 0x0000000000000002#64))),
               (RiscvZkvm.Rv64.Reg.x12,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.srl)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.mul)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19))
                    (Rv64Verifier.Sym.E.ld (Rv64Verifier.Sym.E.c 0x00000000a0000018#64)))
                  (Rv64Verifier.Sym.E.c 0x0000000000000031#64)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800005bc_spec : BlockSpec Image.code 0x00000000800005bc#64 6
    (fun s ↦ Oblig.all s g800005bc.obl) g800005bc.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 6) (x := g800005bc)
    (words := (Image.code.words.drop 367).take 6) (by decide +kernel)
    (CodeAt.slice Image.code 367 6 0x00000000800005bc#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800005bc: 6 steps, then pc := 0x800005d4
     x11 := x8 + (((x19 * [0xa0000018]) >>> 49) <<< 2)
     x12 := (x19 * [0xa0000018]) >>> 49
-/

theorem g800005bc_x11 {s t : MachineState} (h : g800005bc.Holds s t) :
    t.getReg .x11 = s.getReg .x8 + (((s.getReg .x19 * s.getMem (0xa0000018)) >>> 49) * (4 : Word)) :=
  h.reg_eq .x11 rfl (by rv_eval [])

theorem g800005bc_x12 {s t : MachineState} (h : g800005bc.Holds s t) :
    t.getReg .x12 = (s.getReg .x19 * s.getMem (0xa0000018)) >>> 49 :=
  h.reg_eq .x12 rfl (by rv_eval [])

theorem g800005bc_keeps {s t : MachineState} (h : g800005bc.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800005bc_pc {s t : MachineState} (h : g800005bc.Holds s t) : t.pc = 0x800005d4 :=
  h.pc_eq rfl

theorem g800005bc_mem_same {s t : MachineState} (h : g800005bc.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800005d8 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.eq)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000620#64)
              (Rv64Verifier.Sym.E.c 0x00000000800005dc#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800005d8_spec : BlockSpec Image.code 0x00000000800005d8#64 1
    (fun s ↦ Oblig.all s g800005d8.obl) g800005d8.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g800005d8)
    (words := (Image.code.words.drop 374).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 374 1 0x00000000800005d8#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800005d8: 1 steps, then pc := if x13 = 0 then 0x80000620 else 0x800005dc
-/

theorem g800005d8_keeps {s t : MachineState} (h : g800005d8.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800005d8_pc_taken {s t : MachineState} (h : g800005d8.Holds s t) (hc : s.getReg .x13 = (0 : Word)) :
    t.pc = 0x80000620 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hc)))

theorem g800005d8_pc_not_taken {s t : MachineState} (h : g800005d8.Holds s t) (hc : s.getReg .x13 ≠ (0 : Word)) :
    t.pc = 0x800005dc :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hc (beq_iff_eq.mp h))))

theorem g800005d8_mem_same {s t : MachineState} (h : g800005d8.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800005e4 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.geu)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
              (Rv64Verifier.Sym.E.c 0x0000000080000ed4#64)
              (Rv64Verifier.Sym.E.c 0x00000000800005e8#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800005e4_spec : BlockSpec Image.code 0x00000000800005e4#64 1
    (fun s ↦ Oblig.all s g800005e4.obl) g800005e4.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g800005e4)
    (words := (Image.code.words.drop 377).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 377 1 0x00000000800005e4#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800005e4: 1 steps, then pc := if x11 ≥ᵤ x18 then 0x80000ed4 else 0x800005e8
-/

theorem g800005e4_keeps {s t : MachineState} (h : g800005e4.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800005e4_pc_taken {s t : MachineState} (h : g800005e4.Holds s t) (hc : (s.getReg .x18).toNat ≤ (s.getReg .x11).toNat) :
    t.pc = 0x80000ed4 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bnot_of_false (decide_eq_false (Nat.not_lt.mpr hc)))))

theorem g800005e4_pc_not_taken {s t : MachineState} (h : g800005e4.Holds s t) (hc : (s.getReg .x11).toNat < (s.getReg .x18).toNat) :
    t.pc = 0x800005e8 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ of_decide_eq_false (false_of_bnot h) hc)))

theorem g800005e4_mem_same {s t : MachineState} (h : g800005e4.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800005f8 : Expect :=
  { steps := 7,
      pc := Rv64Verifier.Sym.E.c 0x0000000080000614#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.and)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.add)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.sltu)
                          (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.xor)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12))
                              (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22)))
                          (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                        (Rv64Verifier.Sym.E.c 0xffffffffffffffff#64))
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.add)
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12))
                        (Rv64Verifier.Sym.E.c 0x0000000000000001#64)))
                    (Rv64Verifier.Sym.E.c 0x0000000000000002#64))),
               (RiscvZkvm.Rv64.Reg.x12,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.and)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.sltu)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.xor)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.add)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12))
                          (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22)))
                      (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                    (Rv64Verifier.Sym.E.c 0xffffffffffffffff#64))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12))
                    (Rv64Verifier.Sym.E.c 0x0000000000000001#64))),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800005f8_spec : BlockSpec Image.code 0x00000000800005f8#64 7
    (fun s ↦ Oblig.all s g800005f8.obl) g800005f8.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 7) (x := g800005f8)
    (words := (Image.code.words.drop 382).take 7) (by decide +kernel)
    (CodeAt.slice Image.code 382 7 0x00000000800005f8#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800005f8: 7 steps, then pc := 0x80000614
     x11 := x8 + ((((((x12 + 1) ^^^ x22) <ᵤ 1) - 1) &&& (x12 + 1)) <<< 2)
     x12 := ((((x12 + 1) ^^^ x22) <ᵤ 1) - 1) &&& (x12 + 1)
-/

theorem g800005f8_keeps {s t : MachineState} (h : g800005f8.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800005f8_pc {s t : MachineState} (h : g800005f8.Holds s t) : t.pc = 0x80000614 :=
  h.pc_eq rfl

theorem g800005f8_mem_same {s t : MachineState} (h : g800005f8.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000618 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x14))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x00000000800005e0#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000620#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
                  (Rv64Verifier.Sym.E.c 0x0000000000000002#64)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000618_spec : BlockSpec Image.code 0x0000000080000618#64 2
    (fun s ↦ Oblig.all s g80000618.obl) g80000618.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000618)
    (words := (Image.code.words.drop 390).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 390 2 0x0000000080000618#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000618: 2 steps, then pc := if x14 ≠ 0 then 0x800005e0 else 0x80000620
     x13 := x11 + 2
-/

theorem g80000618_x13 {s t : MachineState} (h : g80000618.Holds s t) :
    t.getReg .x13 = s.getReg .x11 + 2 :=
  h.reg_eq .x13 rfl (by rv_eval [])

theorem g80000618_keeps {s t : MachineState} (h : g80000618.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000618_pc_taken {s t : MachineState} (h : g80000618.Holds s t) (hc : s.getReg .x14 ≠ (0 : Word)) :
    t.pc = 0x800005e0 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem g80000618_pc_not_taken {s t : MachineState} (h : g80000618.Holds s t) (hc : s.getReg .x14 = (0 : Word)) :
    t.pc = 0x80000620 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem g80000618_mem_same {s t : MachineState} (h : g80000618.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000628 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
              (Rv64Verifier.Sym.E.ld
                (Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                  (Rv64Verifier.Sym.E.c 0x0000000000000068#64)))
              (Rv64Verifier.Sym.E.c 0x000000008000057c#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000630#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.ld
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                    (Rv64Verifier.Sym.E.c 0x0000000000000068#64))),
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
      mem := [],
      writes := [],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000068#64 }
                8] }

theorem g80000628_spec : BlockSpec Image.code 0x0000000080000628#64 2
    (fun s ↦ Oblig.all s g80000628.obl) g80000628.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000628)
    (words := (Image.code.words.drop 394).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 394 2 0x0000000080000628#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000628: 2 steps, then pc := if x18 ≠ [x2 + 104] then 0x8000057c else 0x80000630
     x11 := [x2 + 104]
     needs valid8 x2 + 104
-/

theorem g80000628_x11 {s t : MachineState} (h : g80000628.Holds s t) :
    t.getReg .x11 = s.getMem (s.getReg .x2 + 104) :=
  h.reg_eq .x11 rfl (by rv_eval [])

theorem g80000628_keeps {s t : MachineState} (h : g80000628.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000628_pc_taken {s t : MachineState} (h : g80000628.Holds s t) (hc : s.getReg .x18 ≠ s.getMem (s.getReg .x2 + 104)) :
    t.pc = 0x8000057c :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem g80000628_pc_not_taken {s t : MachineState} (h : g80000628.Holds s t) (hc : s.getReg .x18 = s.getMem (s.getReg .x2 + 104)) :
    t.pc = 0x80000630 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem g80000628_mem_same {s t : MachineState} (h : g80000628.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800006d4 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ltu)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x14))
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
              (Rv64Verifier.Sym.E.c 0x0000000080000694#64)
              (Rv64Verifier.Sym.E.c 0x00000000800006d8#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800006d4_spec : BlockSpec Image.code 0x00000000800006d4#64 1
    (fun s ↦ Oblig.all s g800006d4.obl) g800006d4.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g800006d4)
    (words := (Image.code.words.drop 437).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 437 1 0x00000000800006d4#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800006d4: 1 steps, then pc := if x14 <ᵤ x18 then 0x80000694 else 0x800006d8
-/

theorem g800006d4_keeps {s t : MachineState} (h : g800006d4.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800006d4_pc_taken {s t : MachineState} (h : g800006d4.Holds s t) (hc : (s.getReg .x14).toNat < (s.getReg .x18).toNat) :
    t.pc = 0x80000694 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hc)))

theorem g800006d4_pc_not_taken {s t : MachineState} (h : g800006d4.Holds s t) (hc : (s.getReg .x18).toNat ≤ (s.getReg .x14).toNat) :
    t.pc = 0x800006d8 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ Nat.not_lt.mpr hc (of_decide_eq_true h))))

theorem g800006d4_mem_same {s t : MachineState} (h : g800006d4.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000820 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.c 0x000000008000082c#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
               (RiscvZkvm.Rv64.Reg.x27,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [],
      writes := [],
      obl := [] }

theorem g80000820_spec : BlockSpec Image.code 0x0000000080000820#64 2
    (fun s ↦ Oblig.all s g80000820.obl) g80000820.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000820)
    (words := (Image.code.words.drop 520).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 520 2 0x0000000080000820#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000820: 2 steps, then pc := 0x8000082c
     x27 := x23 + 1
-/

theorem g80000820_x27 {s t : MachineState} (h : g80000820.Holds s t) :
    t.getReg .x27 = s.getReg .x23 + 1 :=
  h.reg_eq .x27 rfl (by rv_eval [])

theorem g80000820_keeps {s t : MachineState} (h : g80000820.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000820_pc {s t : MachineState} (h : g80000820.Holds s t) : t.pc = 0x8000082c :=
  h.pc_eq rfl

theorem g80000820_mem_same {s t : MachineState} (h : g80000820.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000870 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.geu)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13))
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
              (Rv64Verifier.Sym.E.c 0x0000000080000ed4#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000874#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000870_spec : BlockSpec Image.code 0x0000000080000870#64 1
    (fun s ↦ Oblig.all s g80000870.obl) g80000870.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g80000870)
    (words := (Image.code.words.drop 540).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 540 1 0x0000000080000870#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000870: 1 steps, then pc := if x13 ≥ᵤ x18 then 0x80000ed4 else 0x80000874
-/

theorem g80000870_keeps {s t : MachineState} (h : g80000870.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000870_pc_taken {s t : MachineState} (h : g80000870.Holds s t) (hc : (s.getReg .x18).toNat ≤ (s.getReg .x13).toNat) :
    t.pc = 0x80000ed4 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bnot_of_false (decide_eq_false (Nat.not_lt.mpr hc)))))

theorem g80000870_pc_not_taken {s t : MachineState} (h : g80000870.Holds s t) (hc : (s.getReg .x13).toNat < (s.getReg .x18).toNat) :
    t.pc = 0x80000874 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ of_decide_eq_false (false_of_bnot h) hc)))

theorem g80000870_mem_same {s t : MachineState} (h : g80000870.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000884 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.c 0x000000008000088c#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
               (RiscvZkvm.Rv64.Reg.x14,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x14))
                    (Rv64Verifier.Sym.E.c 0x0000000000000001#64))),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000884_spec : BlockSpec Image.code 0x0000000080000884#64 2
    (fun s ↦ Oblig.all s g80000884.obl) g80000884.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000884)
    (words := (Image.code.words.drop 545).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 545 2 0x0000000080000884#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000884: 2 steps, then pc := 0x8000088c
     x14 := x19 + (x14 <<< 1)
-/

theorem g80000884_x14 {s t : MachineState} (h : g80000884.Holds s t) :
    t.getReg .x14 = s.getReg .x19 + (s.getReg .x14 * (2 : Word)) :=
  h.reg_eq .x14 rfl (by rv_eval [])

theorem g80000884_keeps {s t : MachineState} (h : g80000884.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000884_pc {s t : MachineState} (h : g80000884.Holds s t) : t.pc = 0x8000088c :=
  h.pc_eq rfl

theorem g80000884_mem_same {s t : MachineState} (h : g80000884.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000890 : Expect :=
  { steps := 4,
      pc := Rv64Verifier.Sym.E.c 0x0000000080000848#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
               (RiscvZkvm.Rv64.Reg.x14,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.ld (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
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
      mem := [({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
                 off := 0x0000000000000000#64 },
               Rv64Verifier.Sym.E.bin
                 (Rv64Verifier.Sym.BinOp.add)
                 (Rv64Verifier.Sym.E.ld (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)))
                 (Rv64Verifier.Sym.E.c 0x0000000000000001#64))],
      writes := [{ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
                   off := 0x0000000000000000#64 }],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
                  off := 0x0000000000000000#64 }
                8] }

theorem g80000890_spec : BlockSpec Image.code 0x0000000080000890#64 4
    (fun s ↦ Oblig.all s g80000890.obl) g80000890.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 4) (x := g80000890)
    (words := (Image.code.words.drop 548).take 4) (by decide +kernel)
    (CodeAt.slice Image.code 548 4 0x0000000080000890#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000890: 4 steps, then pc := 0x80000848
     x14 := [x13] + 1
     [x13] := [x13] + 1
     needs valid8 x13
-/

theorem g80000890_x14 {s t : MachineState} (h : g80000890.Holds s t) :
    t.getReg .x14 = s.getMem (s.getReg .x13) + 1 :=
  h.reg_eq .x14 rfl (by rv_eval [])

theorem g80000890_keeps {s t : MachineState} (h : g80000890.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000890_m_x13_0 {s t : MachineState} (h : g80000890.Holds s t) :
    t.getMem (s.getReg .x13) = s.getMem (s.getReg .x13) + 1 :=
  h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])

theorem g80000890_pc {s t : MachineState} (h : g80000890.Holds s t) : t.pc = 0x80000848 :=
  h.pc_eq rfl

theorem g80000890_frame {s t : MachineState} (h : g80000890.Holds s t) (hb : (s.getReg .x13).toNat + 8 ≤ 2 ^ 64) :
    MemFrame s t (s.getReg .x13) 8 :=
  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])

def g80000910 : Expect :=
  { steps := 4,
      pc := Rv64Verifier.Sym.E.c 0x0000000080000920#64,
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
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.ld
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.add)
                      (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                      (Rv64Verifier.Sym.E.c 0x00000000000000f8#64)))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22))
                    (Rv64Verifier.Sym.E.c 0x0000000000000001#64))),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.sll)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
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
               (RiscvZkvm.Rv64.Reg.x22,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
               (RiscvZkvm.Rv64.Reg.x23, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23)),
               (RiscvZkvm.Rv64.Reg.x24, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
               (RiscvZkvm.Rv64.Reg.x25, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25)),
               (RiscvZkvm.Rv64.Reg.x26, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26)),
               (RiscvZkvm.Rv64.Reg.x27, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [],
      writes := [],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000000f8#64 }
                8] }

theorem g80000910_spec : BlockSpec Image.code 0x0000000080000910#64 4
    (fun s ↦ Oblig.all s g80000910.obl) g80000910.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 4) (x := g80000910)
    (words := (Image.code.words.drop 580).take 4) (by decide +kernel)
    (CodeAt.slice Image.code 580 4 0x0000000080000910#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000910: 4 steps, then pc := 0x80000920
     x10 := [x2 + 248] + (x22 <<< 1)
     x11 := x22 <<< 1
     x22 := x22 + 1
     needs valid8 x2 + 248
-/

theorem g80000910_x10 {s t : MachineState} (h : g80000910.Holds s t) :
    t.getReg .x10 = s.getMem (s.getReg .x2 + (248 : Word)) + (s.getReg .x22 * (2 : Word)) :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem g80000910_x11 {s t : MachineState} (h : g80000910.Holds s t) :
    t.getReg .x11 = s.getReg .x22 * (2 : Word) :=
  h.reg_eq .x11 rfl (by rv_eval [])

theorem g80000910_x22 {s t : MachineState} (h : g80000910.Holds s t) :
    t.getReg .x22 = s.getReg .x22 + 1 :=
  h.reg_eq .x22 rfl (by rv_eval [])

theorem g80000910_keeps {s t : MachineState} (h : g80000910.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000910_pc {s t : MachineState} (h : g80000910.Holds s t) : t.pc = 0x80000920 :=
  h.pc_eq rfl

theorem g80000910_mem_same {s t : MachineState} (h : g80000910.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000924 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.c 0x0000000080000928#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x0000000000000100#64 },
               Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22))],
      writes := [{ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x0000000000000100#64 }],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000100#64 }
                8] }

theorem g80000924_spec : BlockSpec Image.code 0x0000000080000924#64 1
    (fun s ↦ Oblig.all s g80000924.obl) g80000924.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g80000924)
    (words := (Image.code.words.drop 585).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 585 1 0x0000000080000924#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000924: 1 steps, then pc := 0x80000928
     [x2 + 256] := x22
     needs valid8 x2 + 256
-/

theorem g80000924_keeps {s t : MachineState} (h : g80000924.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000924_m_x2_256 {s t : MachineState} (h : g80000924.Holds s t) :
    t.getMem (s.getReg .x2 + 256) = s.getReg .x22 :=
  h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])

theorem g80000924_pc {s t : MachineState} (h : g80000924.Holds s t) : t.pc = 0x80000928 :=
  h.pc_eq rfl

theorem g80000924_frame {s t : MachineState} (h : g80000924.Holds s t) (hb : (s.getReg .x2).toNat + 264 ≤ 2 ^ 64) :
    MemFrame s t (s.getReg .x2 + 256) 8 :=
  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])

def g8000092c : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.c 0x0000000080000930#64,
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
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24))
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20))),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g8000092c_spec : BlockSpec Image.code 0x000000008000092c#64 1
    (fun s ↦ Oblig.all s g8000092c.obl) g8000092c.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g8000092c)
    (words := (Image.code.words.drop 587).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 587 1 0x000000008000092c#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x8000092c: 1 steps, then pc := 0x80000930
     x10 := x24 + x20
-/

theorem g8000092c_x10 {s t : MachineState} (h : g8000092c.Holds s t) :
    t.getReg .x10 = s.getReg .x24 + s.getReg .x20 :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem g8000092c_keeps {s t : MachineState} (h : g8000092c.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g8000092c_pc {s t : MachineState} (h : g8000092c.Holds s t) : t.pc = 0x80000930 :=
  h.pc_eq rfl

theorem g8000092c_mem_same {s t : MachineState} (h : g8000092c.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000934 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.eq)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000948#64)
              (Rv64Verifier.Sym.E.c 0x000000008000093c#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12)),
               (RiscvZkvm.Rv64.Reg.x13, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13)),
               (RiscvZkvm.Rv64.Reg.x14,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000934_spec : BlockSpec Image.code 0x0000000080000934#64 2
    (fun s ↦ Oblig.all s g80000934.obl) g80000934.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g80000934)
    (words := (Image.code.words.drop 589).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 589 2 0x0000000080000934#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000934: 2 steps, then pc := if x11 = 0 then 0x80000948 else 0x8000093c
     x14 := x20 + 1
-/

theorem g80000934_x14 {s t : MachineState} (h : g80000934.Holds s t) :
    t.getReg .x14 = s.getReg .x20 + 1 :=
  h.reg_eq .x14 rfl (by rv_eval [])

theorem g80000934_keeps {s t : MachineState} (h : g80000934.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000934_pc_taken {s t : MachineState} (h : g80000934.Holds s t) (hc : s.getReg .x11 = (0 : Word)) :
    t.pc = 0x80000948 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hc)))

theorem g80000934_pc_not_taken {s t : MachineState} (h : g80000934.Holds s t) (hc : s.getReg .x11 ≠ (0 : Word)) :
    t.pc = 0x8000093c :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hc (beq_iff_eq.mp h))))

theorem g80000934_mem_same {s t : MachineState} (h : g80000934.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000960 : Expect :=
  { steps := 5,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.eq)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000958#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000974#64),
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
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
               (RiscvZkvm.Rv64.Reg.x11, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)),
               (RiscvZkvm.Rv64.Reg.x12,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x12))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
               (RiscvZkvm.Rv64.Reg.x13,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x13))
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
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
                  (Rv64Verifier.Sym.E.c 0x0000000000000001#64)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000960_spec : BlockSpec Image.code 0x0000000080000960#64 5
    (fun s ↦ Oblig.all s g80000960.obl) g80000960.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 5) (x := g80000960)
    (words := (Image.code.words.drop 600).take 5) (by decide +kernel)
    (CodeAt.slice Image.code 600 5 0x0000000080000960#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000960: 5 steps, then pc := if x11 = 0 then 0x80000958 else 0x80000974
     x10 := x10 + 1
     x12 := x12 + 1
     x13 := x13 + 1
     x20 := x20 + 1
-/

theorem g80000960_x10 {s t : MachineState} (h : g80000960.Holds s t) :
    t.getReg .x10 = s.getReg .x10 + 1 :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem g80000960_x12 {s t : MachineState} (h : g80000960.Holds s t) :
    t.getReg .x12 = s.getReg .x12 + 1 :=
  h.reg_eq .x12 rfl (by rv_eval [])

theorem g80000960_x13 {s t : MachineState} (h : g80000960.Holds s t) :
    t.getReg .x13 = s.getReg .x13 + 1 :=
  h.reg_eq .x13 rfl (by rv_eval [])

theorem g80000960_x20 {s t : MachineState} (h : g80000960.Holds s t) :
    t.getReg .x20 = s.getReg .x20 + 1 :=
  h.reg_eq .x20 rfl (by rv_eval [])

theorem g80000960_keeps {s t : MachineState} (h : g80000960.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x14, .x15, .x16, .x17, .x18, .x19, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000960_pc_taken {s t : MachineState} (h : g80000960.Holds s t) (hc : s.getReg .x11 = (0 : Word)) :
    t.pc = 0x80000958 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hc)))

theorem g80000960_pc_not_taken {s t : MachineState} (h : g80000960.Holds s t) (hc : s.getReg .x11 ≠ (0 : Word)) :
    t.pc = 0x80000974 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hc (beq_iff_eq.mp h))))

theorem g80000960_mem_same {s t : MachineState} (h : g80000960.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g80000988 : Expect :=
  { steps := 5,
      pc := Rv64Verifier.Sym.E.c 0x000000008000099c#64,
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
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.srl)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.sll)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.or)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.sll)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10))
                          (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11)))
                      (Rv64Verifier.Sym.E.c 0x0000000000000030#64))
                    (Rv64Verifier.Sym.E.c 0x0000000000000030#64))),
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
               (RiscvZkvm.Rv64.Reg.x21,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.or)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10))
                    (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g80000988_spec : BlockSpec Image.code 0x0000000080000988#64 5
    (fun s ↦ Oblig.all s g80000988.obl) g80000988.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 5) (x := g80000988)
    (words := (Image.code.words.drop 610).take 5) (by decide +kernel)
    (CodeAt.slice Image.code 610 5 0x0000000080000988#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x80000988: 5 steps, then pc := 0x8000099c
     x10 := x18 + ((((x10 <<< 8) ||| x11) <<< 48) >>> 48)
     x21 := (x10 <<< 8) ||| x11
-/

theorem g80000988_x10 {s t : MachineState} (h : g80000988.Holds s t) :
    t.getReg .x10 = s.getReg .x18 + ((((s.getReg .x10 * (256 : Word)) ||| s.getReg .x11) * (0x1000000000000 : Word)) >>> 48) :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem g80000988_x21 {s t : MachineState} (h : g80000988.Holds s t) :
    t.getReg .x21 = (s.getReg .x10 * (256 : Word)) ||| s.getReg .x11 :=
  h.reg_eq .x21 rfl (by rv_eval [])

theorem g80000988_keeps {s t : MachineState} (h : g80000988.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g80000988_pc {s t : MachineState} (h : g80000988.Holds s t) : t.pc = 0x8000099c :=
  h.pc_eq rfl

theorem g80000988_mem_same {s t : MachineState} (h : g80000988.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800009a0 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
              (Rv64Verifier.Sym.E.c 0x0000000000000000#64)
              (Rv64Verifier.Sym.E.c 0x0000000080000928#64)
              (Rv64Verifier.Sym.E.c 0x00000000800009a4#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800009a0_spec : BlockSpec Image.code 0x00000000800009a0#64 1
    (fun s ↦ Oblig.all s g800009a0.obl) g800009a0.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g800009a0)
    (words := (Image.code.words.drop 616).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 616 1 0x00000000800009a0#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800009a0: 1 steps, then pc := if x11 ≠ 0 then 0x80000928 else 0x800009a4
-/

theorem g800009a0_keeps {s t : MachineState} (h : g800009a0.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800009a0_pc_taken {s t : MachineState} (h : g800009a0.Holds s t) (hc : s.getReg .x11 ≠ (0 : Word)) :
    t.pc = 0x80000928 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem g800009a0_pc_not_taken {s t : MachineState} (h : g800009a0.Holds s t) (hc : s.getReg .x11 = (0 : Word)) :
    t.pc = 0x800009a4 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem g800009a0_mem_same {s t : MachineState} (h : g800009a0.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800009a4 : Expect :=
  { steps := 2,
      pc := Rv64Verifier.Sym.E.c 0x00000000800009ac#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.ld
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                    (Rv64Verifier.Sym.E.c 0x00000000000000f0#64))),
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
               (RiscvZkvm.Rv64.Reg.x22,
                Rv64Verifier.Sym.E.ld
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.add)
                    (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                    (Rv64Verifier.Sym.E.c 0x0000000000000100#64))),
               (RiscvZkvm.Rv64.Reg.x23, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23)),
               (RiscvZkvm.Rv64.Reg.x24, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
               (RiscvZkvm.Rv64.Reg.x25, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25)),
               (RiscvZkvm.Rv64.Reg.x26, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26)),
               (RiscvZkvm.Rv64.Reg.x27, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [],
      writes := [],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000100#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000000f0#64 }
                8] }

theorem g800009a4_spec : BlockSpec Image.code 0x00000000800009a4#64 2
    (fun s ↦ Oblig.all s g800009a4.obl) g800009a4.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 2) (x := g800009a4)
    (words := (Image.code.words.drop 617).take 2) (by decide +kernel)
    (CodeAt.slice Image.code 617 2 0x00000000800009a4#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800009a4: 2 steps, then pc := 0x800009ac
     x11 := [x2 + 240]
     x22 := [x2 + 256]
     needs valid8 x2 + 256, valid8 x2 + 240
-/

theorem g800009a4_x11 {s t : MachineState} (h : g800009a4.Holds s t) :
    t.getReg .x11 = s.getMem (s.getReg .x2 + 240) :=
  h.reg_eq .x11 rfl (by rv_eval [])

theorem g800009a4_x22 {s t : MachineState} (h : g800009a4.Holds s t) :
    t.getReg .x22 = s.getMem (s.getReg .x2 + 256) :=
  h.reg_eq .x22 rfl (by rv_eval [])

theorem g800009a4_keeps {s t : MachineState} (h : g800009a4.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800009a4_pc {s t : MachineState} (h : g800009a4.Holds s t) : t.pc = 0x800009ac :=
  h.pc_eq rfl

theorem g800009a4_mem_same {s t : MachineState} (h : g800009a4.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

def g800009b0 : Expect :=
  { steps := 1,
      pc := Rv64Verifier.Sym.E.ite
              (Rv64Verifier.Sym.CmpOp.ne)
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22))
              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x11))
              (Rv64Verifier.Sym.E.c 0x0000000080000910#64)
              (Rv64Verifier.Sym.E.c 0x00000000800009b4#64),
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x10)),
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
      mem := [],
      writes := [],
      obl := [] }

theorem g800009b0_spec : BlockSpec Image.code 0x00000000800009b0#64 1
    (fun s ↦ Oblig.all s g800009b0.obl) g800009b0.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := g800009b0)
    (words := (Image.code.words.drop 620).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 620 1 0x00000000800009b0#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

/- 0x800009b0: 1 steps, then pc := if x22 ≠ x11 then 0x80000910 else 0x800009b4
-/

theorem g800009b0_keeps {s t : MachineState} (h : g800009b0.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem g800009b0_pc_taken {s t : MachineState} (h : g800009b0.Holds s t) (hc : s.getReg .x22 ≠ s.getReg .x11) :
    t.pc = 0x80000910 :=
  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hc)))

theorem g800009b0_pc_not_taken {s t : MachineState} (h : g800009b0.Holds s t) (hc : s.getReg .x22 = s.getReg .x11) :
    t.pc = 0x800009b4 :=
  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ bne_iff_ne.mp h hc)))

theorem g800009b0_mem_same {s t : MachineState} (h : g800009b0.Holds s t) (a : Word) : t.getMem a = s.getMem a :=
  h.mem_same rfl a

end Rv64Verifier.Proofs.Main.NB
