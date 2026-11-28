module

public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.KeccakF
public import NativeRustcX64.Spec.Keccak
public meta import NativeRustcX64.Code.Common.KeccakF
public meta import NativeRustcX64.Spec.Keccak

/-!
# `keccak_f`'s blocks, run by the symbolic executor (x86-64)

The three blocks of `keccak_f` (`NativeRustcX64.Common.KeccakF`), each run from a symbolic state
whose region 0 is the 296-byte frame from 288 below the entry's RSP (its last 8 bytes the return
address):

- the prologue `b0` (`prologue`), from the entry, with the state as region 1;
- the body `b1`, split at the completed first round into `firstBody` and `secondBody`, with
  the current pair of round constants as region 1. The indexed address aliases its offset 8;
- the epilogue `b2` (`epilogue`), with the state as region 1 through the pointer at frame offset 216.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public section

/-- The prologue's start. -/
def startPro : SState := init [296, 200] [(.rsp, .ptr 0 288), (.rdi, .ptr 1 0)]

/-- The loop head's. -/
def startBody : SState :=
  init [296, 16] [(.rsp, .ptr 0 128)] [] []
    [(.bin .add .W64 (.load 0 176 8) (.label NativeRustcX64.roundConstantsLabel), 1, 8)]

/-- The second round, with its counter saved in the frame. -/
def startMid : SState :=
  init [296, 16] [(.rsp, .ptr 0 128)] [] []
    [(.bin .add .W64 (.load 0 176 8) (.label NativeRustcX64.roundConstantsLabel), 1, 8)]

def firstHalf : List Directive := Common.KeccakF.b1.take 245
def secondHalf : List Directive := Common.KeccakF.b1.drop 245

/-- The loop exit's. -/
def startEpi : SState := init [296, 200] [(.rsp, .ptr 0 128)] [] [] [(.load 0 216 8, 1, 0)]

end

sym_block prologue := exec Common.KeccakF.b0 startPro

sym_block firstBody := exec firstHalf startBody

sym_block secondBody := exec secondHalf startMid

sym_block epilogue := exec Common.KeccakF.b2 startEpi

end NativeRustcX64.KeccakF
