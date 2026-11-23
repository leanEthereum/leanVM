module

public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.WotsLeaf.Steps
public import NativeRustcX64.WotsLeaf.Codeword.Digits
public import NativeRustcX64.Code.Xmss.WotsLeaf
public meta import NativeRustcX64.Code.Xmss.WotsLeaf
public meta import NativeRustcX64.WotsLeaf.FrameS

/-!
# The codeword's blocks, run by the symbolic executor

`b6`, `b8`, `b10` in the frame (`frameS []`), `b7` with RDX the digest's high word (`s7`). The
digits' loop `b9` (`.LWotsLeaf_3`) runs from `s9 j`, its turn `j < 29` (RAX `4 j`, RDI the frame's
byte `615 + 2 j`, literals): each turn stores the digits `2 j`, `2 j + 1` (`digitSym`) and the
checks `ok9` hold for every turn (`ok9_all`, decided by the kernel).
-/

namespace NativeRustcX64.WotsLeafProof.Codeword

open NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf

@[expose] public section

/-- At `b7`: RDX the digest's high word. -/
def s7 : SState := frameS [(.rdx, .load 0 120 8)]

/-- At turn `j` of the digits' loop. -/
def s9 (j : Nat) : SState := frameS [(.rax, .lit (4 * j)), (.rdi, .ptr 0 (615 + 2 * j))]

/-- The two digits a turn stores. -/
def coversDigits (ws : List Write) (j : Nat) : Bool :=
  (List.range 2).all fun t ↦ findWrite 0 (614 + 2 * j + t) ws == some (digitSym (2 * j + t), 0)

/-- What a turn of the loop does (decided on the literal state): its digits stored, its other
writes none, RSP and the registers it does not set kept, RAX and RDI the next turn's, the exit
back to the loop head but after the last turn. -/
def ok9 (j : Nat) : Bool :=
  match exec b9 (s9 j) with
  | some (S, x) =>
    coversDigits S.mem j && S.mem.length == 2 && blockOK S 0 &&
      Run.noWriteIn S 0 (614 + 2 * j) &&
      S.reg .rax == some (.lit (4 * (j + 1))) && S.reg .rdi == some (.ptr 0 (615 + 2 * (j + 1))) &&
      S.reg .rsi == some (.reg .rsi) && S.reg .rdx == some (.reg .rdx) &&
      x == .cond (.lit (j != 28)) NativeRustcX64.Xmss.WotsLeaf.label_3
  | none => false

end

set_option Elab.async false

sym_block run_b6 := exec b6 (frameS [])
sym_block run_b7 := exec b7 s7
sym_block run_b8 := exec b8 (frameS [])
sym_block run_b10 := exec b10 (frameS [])

public theorem ok9_all : ∀ j < 29, ok9 j = true := by decide +kernel

end NativeRustcX64.WotsLeafProof.Codeword
