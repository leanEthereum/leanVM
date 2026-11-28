module

public import NativeRustcX64.WotsLeaf.FrameS
public import NativeRustcX64.Code.Xmss.WotsLeaf
public meta import NativeRustcX64.WotsLeaf.FrameS
public meta import NativeRustcX64.Code.Xmss.WotsLeaf

/-!
# The chains' blocks, run by the symbolic executor

The chains' loop: `b15` (chain `i`'s digit and value; the value's 16 bytes as region 4, reached by
the alias of `values + (i << 4)`, `s15`), `b16`, `b14` (the chain's end stored at `1080 + 16 i`;
the frame's bytes `0 .. 96` as region 0, `16 i` at `456` as region 2, the end's slot as region 3,
`s14`), `b48`. A chain step: `b17`, `b18` (`P` as region 4; `buf_len` `0`), `b21`, the address
absorbed (`b24`, `b25`, `b26`, `b27`, `b23`), the clone (`b31`, `b32`), the payload absorbed
(`b35`, `b36`, `b37`, `b38`, `b34`), the final block (`b42`, `b43`, `b44`, `b45`, `b46`: the
padding and the lane XORs) and `b47`. The values the steps know: registers as literals and frame
pointers, `buf_len` as a literal write (`seeded`).
-/

namespace NativeRustcX64.WotsLeafProof.Chain

open NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf

@[expose] public section

/-- The frame with the literal writes `ws`. -/
def seeded (k : List (Reg64 × Sym)) (ws : List Write) (extra : List Nat := [])
    (aliases : List (Sym × Nat × Int) := []) : SState :=
  { frameS k extra [] aliases with mem := ws }

/-- A literal word at the frame's byte `o`. -/
def litW (o v : Nat) : Write := ⟨0, o, 8, .lit v⟩

/-- The address of chain `i`'s value: `values + (i << 4)`. -/
def valueKey : Sym := .bin .add .W64 (.load 0 2776 8) (.bin .shl .W64 (.reg .rdx) (.lit 4))

/-- At `b15`: chain `i`'s value as region 4, RDX below 58. -/
def s15 : SState := frameS [] [16] [(.reg .rdx, 58)] [(valueKey, (4, 0))]

/-- At `b14`: the frame's bytes `0 .. 96` (region 0), the call's return slot (region 1), `16 i`
at `456` (region 2), the chain's end slot (region 3). -/
def s14 : SState :=
  init [96, 8, 8, 16] [(.rsp, .ptr 0 0)] [] []
    [(.ptr 0 456, (2, 0)), (.bin .add .W64 (.ptr 0 0) (.load 2 0 8), (3, -1080))]

/-- At `b18`: `P` as region 4, `buf_len` `0`. -/
def s18 : SState := seeded [] [litW 448 0] [16] [(.load 0 104 8, (4, 0))]

end

set_option Elab.async false

sym_block run_b15 := exec b15 s15
sym_block run_b16 := exec b16 (frameS [])
sym_block run_b14 := exec b14 s14
sym_block run_b48 := exec b48 (frameS [])
sym_block run_b17 := exec b17 (frameS [(.rbx, .label "memset")])
sym_block run_b18 := exec b18 s18
sym_block run_b21 := exec b21 (frameS [])
sym_block run_b24 := exec b24 (frameS [(.rdi, .lit 16), (.r14, .lit 16), (.rbx, .ptr 0 472)])
sym_block run_b25 := exec b25 (frameS [(.rsi, .lit 32)])
sym_block run_b26 := exec b26 (frameS [(.rdi, .lit 16), (.r15, .lit 16), (.rbx, .ptr 0 472), (.r13, .label "memcpy")])
sym_block run_b27 := exec b27 (seeded [(.r15, .lit 16)] [litW 448 16])
sym_block run_b23 := exec b23 (frameS [(.r14, .lit 16), (.r15, .lit 16), (.rbx, .ptr 0 472)])
sym_block run_b31 := exec b31 (frameS [(.r12, .ptr 0 112), (.r13, .label "memcpy")])
sym_block run_b32 := exec b32 (seeded [] [litW 1040 32])
sym_block run_b35 := exec b35 (frameS [(.r15, .lit 32), (.r12, .lit 32), (.rbx, .ptr 0 672)])
sym_block run_b36 := exec b36 (frameS [(.rsi, .lit 64)])
sym_block run_b37 := exec b37 (frameS [(.r15, .lit 32), (.r14, .lit 32), (.rbx, .ptr 0 672), (.r13, .label "memcpy")])
sym_block run_b38 := exec b38 (seeded [(.r14, .lit 32)] [litW 1040 32])
sym_block run_b34 := exec b34 (frameS [(.r12, .lit 32), (.r14, .lit 32), (.rbx, .ptr 0 672)])
sym_block run_b42 := exec b42 (frameS [(.r13, .label "memcpy")])
sym_block run_b43 := exec b43 (frameS [(.r15, .lit 64)])
sym_block run_b44 := exec b44 (frameS [(.r15, .lit 64), (.rdx, .lit 136)])
sym_block run_b45 := exec b45 (frameS [(.r15, .lit 64), (.r14, .ptr 0 472), (.r13, .label "memcpy")])
sym_block run_b46 := exec b46 (frameS [(.r15, .lit 64), (.r12, .ptr 0 112)])
sym_block run_b47 := exec b47 (frameS [])

end NativeRustcX64.WotsLeafProof.Chain
