module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.HashPair
public meta import NativeRustcVmArm.Code.Vm.HashPair
public meta import NativeRustcArm.Sym

/-!
# `hash_pair`'s blocks, run by the symbolic executor

Region 0 is the 80-byte frame. The entry block `b0` runs in two parts, as `left` and `right` may
overlap: `partL` (its first 7 directives: the frame, `left`'s words 0 to 3 loaded, 0 and 1
stored; region 1 `left`, at X1) and `partR` (the rest: `left`'s words 2 and 3 and `right`'s
stored, X30 saved, the call of `keccak256_words`; region 1 `right`, at X2). `ret` (`b1`) restores
X30 and returns.
-/

namespace NativeRustcVmArm.HashPairRun

open NativeRustcArm NativeRustcArm.Sym Vm.HashPair

set_option Elab.async false

@[expose] public section

/-- `b0`'s first part. -/
def partLCode : List Directive := b0.take 7

/-- `b0`'s second part. -/
def partRCode : List Directive := b0.drop 7

/-- The entry: SP the frame's top, region 1 `left` at X1. -/
def startL : SState := init [(80, true), (32, false)] (.ptr 0 80) [(.X1, .ptr 1 0)]

/-- SP the frame's base, region 1 `right` at X2. -/
def startR : SState := init [(80, true), (32, false)] (.ptr 0 0) [(.X2, .ptr 1 0)]

/-- SP the frame's base. -/
def startRet : SState := init [(80, true)] (.ptr 0 0)

end

sym_block partL := exec partLCode startL
sym_block partR := exec partRCode startR
sym_block ret := exec b1 startRet

end NativeRustcVmArm.HashPairRun
