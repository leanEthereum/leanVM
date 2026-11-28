module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.HashPair
public meta import NativeRustcVmX64.Code.Vm.HashPair
public meta import NativeRustcX64.Sym

/-!
# `hash_pair`'s blocks, run by the symbolic executor (x86-64)

The frame: the 88 bytes from 80 below the entry's RSP (the callee's return address at 0, the
words at 16 to 79, the return address at 80). The entry block `b0` runs in three parts, as `left`
and `right` may overlap: `partL` (its first 6 directives: RSP lowered, `left`'s words loaded;
region 0 `left`, at RSI), `partR` (the next 4: `right`'s words loaded; region 0 `right`, at RDX)
and `partS` (the rest: the 8 words stored in the frame, the call of `keccak256_words`; region 0
the frame). `ret` (`b1`) raises RSP and returns.
-/

namespace NativeRustcVmX64.HashPairRun

open NativeRustcX64 NativeRustcX64.Sym Vm.HashPair

set_option Elab.async false

@[expose] public section

/-- `b0`'s first part. -/
def partLCode : List Directive := b0.take 6

/-- `b0`'s second part. -/
def partRCode : List Directive := (b0.drop 6).take 4

/-- `b0`'s third part. -/
def partSCode : List Directive := b0.drop 10

/-- Region 0 `left` at RSI. -/
def startL : SState := init [32] [(.rsi, .ptr 0 0)]

/-- Region 0 `right` at RDX. -/
def startR : SState := init [32] [(.rdx, .ptr 0 0)]

/-- Region 0 the frame, RSP at its offset 8. -/
def startS : SState := init [88] [(.rsp, .ptr 0 8)]

end

sym_block partL := exec partLCode startL
sym_block partR := exec partRCode startR
sym_block partS := exec partSCode startS
sym_block ret := exec b1 startS

end NativeRustcVmX64.HashPairRun
