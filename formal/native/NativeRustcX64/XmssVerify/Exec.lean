module

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Xmss.XmssVerify
public meta import NativeRustcX64.Code.Xmss.XmssVerify

/-!
# `xmss_verify`'s blocks, run by the symbolic executor (x86-64)

The symbolic states the proof starts blocks from, the executor's results (`run_b<k>`) and the
states they end in (`after`). Region 0 is the frame region (5816 bytes, RSP after the prologue at
its offset 24) unless said otherwise:
- `st0`, the entry (`b0`, ending in `callq memset`): RSP at 5808;
- `st1` (`b1`): region 1 the input words, R14 the context;
- `stC`, a turn of the loop copying the signature's words (`b2`): region 0 the 48 input bytes
  the turn reads, region 1 the 48 frame bytes it writes, as aliases of the indexed addresses;
- `stF known`, the frame with RSP at 24 and the registers `known` (`b3`–`b8`, `b10`–`b14`,
  `b16`, `b18`, `b20`–`b28`); `stR`, RSP at 8, after `wots_leaf` (`b6`, `b17`);
- `stN known`, a turn of a loop over a layer's path (`b9`, `b15`, `b19`): region 1 the path's
  node of the turn.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState := ((exec ds S).getD (S, .fall)).1

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]
  rfl

/-- The frame and the two ordinary-memory GOT slots. -/
def stG (sp : Int) (known : List (Reg64 × Sym)) : SState :=
  ((init [5816, 8, 8] ((.rsp, .ptr 0 sp) :: known) [] []
    [(.gotSlot "memcpy", 1, 0), (.gotSlot "memset", 2, 0)]).withKnownBytes
      1 0 8 (.label "memcpy")).withKnownBytes 2 0 8 (.label "memset")

/-- The entry. -/
def st0 : SState := stG 5808 []

/-- Block 1: the frame and the input words. -/
def st1 : SState := init [5816, 2472] [(.rsp, .ptr 0 24), (.r14, .ptr 1 (-1024))]

/-- The scaled index `R15 * 8` added to a register, as the executor builds the address. -/
def idx8 (r : Reg64) : Sym := mkAdd64 (.reg r) (mkBin .mul .W64 (.reg .r15) (.lit 8))

/-- A turn of the copy loop: region 0 the input bytes `R14 + 8 R15 + 1096 ..`, region 1 the frame
bytes `RSP + 8 R15 + 932 ..`. -/
def stC : SState := init [48, 48] [] [] [] [(idx8 .r14, 0, -1096), (idx8 .rsp, 1, -932)]

/-- The frame, RSP at its offset 24, with the registers `known`. -/
def stF (known : List (Reg64 × Sym)) : SState := stG 24 known

/-- After `wots_leaf`: RSP at the frame's offset 8. -/
def stR : SState := init [5816] [(.rsp, .ptr 0 8)]

/-- A turn over a layer's path: region 0 the frame below the layers, region 1 the turn's node,
and region 2 the memset GOT slot. -/
def stN (known : List (Reg64 × Sym)) : SState :=
  (init [3356, 16, 8] ((.rsp, .ptr 0 24) :: known) [] []
    [(.gotSlot "memset", 2, 0)]).withKnownBytes 2 0 8 (.label "memset")

def st3 : SState := stF [(.rbx, .ptr 0 956)]
def st4 : SState := stF [(.rbx, .ptr 0 184)]
def st5 : SState := stF [(.r15, .ptr 0 56)]
def st9 : SState := stN [(.r12, .ptr 1 0), (.r15, .ptr 0 184)]
def stH : SState := stF [(.r15, .ptr 0 184)]
def stH1 : SState := stF [(.r15, .ptr 0 184), (.r13, .ptr 0 608)]
def st15 : SState := stN [(.r14, .ptr 0 592), (.r12, .ptr 1 0)]
def st19 : SState :=
  stN [(.r14, .ptr 1 0), (.r13, .ptr 0 120), (.rbp, .ptr 0 608), (.r15, .ptr 0 184)]
def stH2 : SState := stF [(.r15, .ptr 0 184), (.rbp, .ptr 0 608)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 st0
sym_block run_b1 := exec b1 st1
sym_block run_b2 := exec b2 stC
sym_block run_b3 := exec b3 st3
sym_block run_b4 := exec b4 st4
sym_block run_b5 := exec b5 st5
sym_block run_b6 := exec b6 stR
sym_block run_b7 := exec b7 (stF [])
sym_block run_b8 := exec b8 (stF [])
sym_block run_b9 := exec b9 st9
sym_block run_b10 := exec b10 stH
sym_block run_b11 := exec b11 stH
sym_block run_b12 := exec b12 stH
sym_block run_b13 := exec b13 stH1
sym_block run_b14 := exec b14 stH1
sym_block run_b15 := exec b15 st15
sym_block run_b16 := exec b16 (stF [])
sym_block run_b17 := exec b17 stR
sym_block run_b18 := exec b18 (stF [])
sym_block run_b19 := exec b19 st19
sym_block run_b20 := exec b20 stH
sym_block run_b21 := exec b21 stH
sym_block run_b22 := exec b22 stH2
sym_block run_b23 := exec b23 stH2
sym_block run_b24 := exec b24 stH2
sym_block run_b25 := exec b25 (stF [])
sym_block run_b26 := exec b26 (stF [])
sym_block run_b27 := exec b27 (stF [])
sym_block run_b28 := exec b28 (stF [])

end NativeRustcX64.Xmss.XmssVerify
