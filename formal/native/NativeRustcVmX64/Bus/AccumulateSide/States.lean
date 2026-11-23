module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.AccumulateSide
public import NativeRustcVmX64.Code.Vm.Names

/-!
# `accumulate_side`'s symbolic states (x86-64)

Region 0 is the 12032-byte frame below the entry's RSP and the return address (`F = 12032`: six
pushes at `11984` to `12024`, RSP at offset `8` in the body, a callee's return address at `0`);
the eleven stack arguments above it are region 1 where a block reads them (`argAliases`: frame
offset `12040 + 8 i` is region 1's `8 i`). No state has the arguments beside an array the
contract does not set apart from them: `b2`, `b18` and `b23` run in two parts (`b2a`, `b2b`, …).

- `entryS` (`b0`), `slS` (`b15`): the side layout (region 2) at the first stack argument;
- `fS`: the frame; `aS`: the frame and the arguments;
- `kAS` (`b2a`): framework placement `i` (region 2, R12 + RBP); `kBS` (`b2b`): fingerprint `i`
  (region 1, RCX + RBP);
- `oS` (`b8`): framework placement (region 1, R12);
- `zS` (`b13`): the 136 bytes from RSP + RAX, of which a turn of the zeroing loop clears the last
  80 (region 0);
- `pS` (`b17`): the side layout's 88 bytes from its table placement `j` (region 2, the side layout
  + R12; the placement at its offset `72`);
- `bS` (`b18a`, `b20`): block (region 1, the blocks + R12);
- `tS` (`b21`): `TABLES` (region 1 at its label), the owner times five below `26`;
- `hS` (`b23a`): the layout's first 120 bytes (region 1), the owner below `6`;
- `outS` (`b30`, `b31`): the output (region 1, the frame word at `80`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Vm.AccumulateSide

@[expose] public section

/-- The frame's bytes. -/
abbrev F : Nat := 12032

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(12024, .rbp), (12016, .r15), (12008, .r14), (12000, .r13), (11992, .r12), (11984, .rbx)]


/-- The stack arguments' aliases: frame offset `12040 + 8 i` is region 1's `8 i`. -/
def argAliases : List (Sym × Nat × Int) :=
  (List.range 11).map fun i ↦ (.ptr 0 ((12040 + 8 * i : Nat) : Int), 1, ((8 * i : Nat) : Int))

/-- The side layout's address (the first stack argument). -/
abbrev slA : Sym := .load 1 0 8

/-- `b2`'s first 15 directives (to the fingerprints' address) and the rest. -/
def b2a : List Directive := b2.take 15
def b2b : List Directive := b2.drop 15
/-- `b18`'s first 4 directives (to the block's tuple) and the rest. -/
def b18a : List Directive := b18.take 4
def b18b : List Directive := b18.drop 4
/-- `b23`'s first 22 directives (to the layout's words) and the rest. -/
def b23a : List Directive := b23.take 22
def b23b : List Directive := b23.drop 22

def entryS : SState :=
  init [12040, 88, 888] [(.rsp, .ptr 0 12032)] [] [] (argAliases ++ [(slA, 2, 0)])
def fS : SState := init [12040] [(.rsp, .ptr 0 8)]
/-- The frame and ordinary loader slot at the raw indirect copy call. -/
def copyS : SState :=
  (init [12040, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")
def aS : SState := init [12040, 88] [(.rsp, .ptr 0 8)] [] [] argAliases
def slS : SState := init [12040, 88, 888] [(.rsp, .ptr 0 8)] [] [] (argAliases ++ [(slA, 2, 0)])
def kAS : SState :=
  init [12040, 88, 16] [(.rsp, .ptr 0 8)] [] []
    (argAliases ++ [(.bin .add .W64 (.reg .r12) (.reg .rbp), 2, 0)])
def kBS : SState :=
  init [12040, 16] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .rcx) (.reg .rbp), 1, 0)]
def oS : SState := init [12040, 16] [(.rsp, .ptr 0 8)] [] [] [(.reg .r12, 1, 0)]
def zS : SState := init [136] [] [] [] [(.bin .add .W64 (.reg .rsp) (.reg .rax), 0, 0)]
def pS : SState :=
  init [12040, 88, 88] [(.rsp, .ptr 0 8)] [] []
    (argAliases ++ [(.bin .add .W64 slA (.reg .r12), 2, 0)])
def bS : SState :=
  init [12040, 16] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.load 0 96 8) (.reg .r12), 1, 0)]
/-- The owner times five, as `leaq (%rsi,%rsi,4)` computes it. -/
def five : Sym := .bin .add .W64 (.reg .rsi) (.bin .mul .W64 (.reg .rsi) (.lit 4))
def tS : SState := init [12040, 240] [(.rsp, .ptr 0 8)] [(NativeRustcVmX64.Vm.Symbols.rodata4Label, 1)] [(five, 26)]
def hS : SState :=
  init [12040, 120] [(.rsp, .ptr 0 8)] [] [(.load 0 48 8, 6)] [(.load 0 104 8, 1, 0)]
def outS : SState := init [12040, 24] [(.rsp, .ptr 0 8)] [] [] [(.load 0 80 8, 1, 0)]

end

end NativeRustcVmX64.Bus.AccumulateSide
