module

public import NativeRustcX64.Sym
public import NativeRustcX64.SphincsVerify.Frame
public import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Frame

/-!
# The tree region's blocks on x86-64, run by the symbolic executor

Each stretch between calls runs from a fresh state of the frame (`Run.match_frame`: region 0 the
frame, RSP its base, region 1 the slots below it, and regions 2 and 3 the loader slots), with
the live register-held function pointers seeded alongside each block's data registers
(`frameS`): the one-time leaf's blocks `b151` .. `b157` (each ending in a call) and the path's
checks `b158` .. `b161` (`wotsS`); a node's loop head `b162` (`nodeS p`: RCX the height, below 10,
`72(%rsp)` the layer's path from node `p`), then after each of its calls (`s2` .. `s9`); the exit
`b189`, `b191`, `b192`. `after ds S` is the state `exec ds S` ends in.
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- The frame's regions, RSP the base, the registers `k`. -/
def frameS (k : List (Reg64 × Sym)) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : SState :=
  Run.frameState ((.r14, .label "memcpy") :: k) [] bounds aliases

/-- R12 hasher A, RBP hasher B. -/
def kAB : List (Reg64 × Sym) := [(.r12, .ptr 0 4096), (.rbp, .ptr 0 576)]

/-- The one-time leaf's states: R12, RBP, R13 `base + 2048`. -/
def wotsS : SState := frameS (kAB ++ [(.r13, .ptr 0 2048), (.rbx, .label "memset")])

/-- A node's loop head: RCX the height, below 10, `72(%rsp)` the layer's path from node `p`. -/
def nodeS (p : Nat) : SState :=
  frameS (kAB ++ [(.rcx, .reg .rcx), (.rbx, .label "memset")]) [(.bin .shl .W64 (.reg .rcx) (.lit 4), 145)]
    [(.load 0 72 8, 0, ((24764 + 16 * p : Nat) : Int))]

/-- What `b161` stores at `72(%rsp)`: the layer's path's address, from the layer at
`96(%rsp)`. -/
def pathSym : Sym :=
  .bin .add .W64 (.ptr 0 24764)
    (.bin .shl .W64
      (.ite (.cmp .eq .W64 (.bin .and .W64 (.load 0 96 8) (.load 0 96 8)) (.lit 0))
        (.load 0 96 8)
        (.bin .add .W64
          (.bin .mul .W64
            (.bin .merge .W8 (.lit 0)
              (.ite (.not (.cmp .eq .W64 (.load 0 96 8) (.lit 1))) (.lit 1) (.lit 0)))
            (.lit 8))
          (.lit 8)))
      (.lit 4))

/-- After `memset`. -/
def s2 : SState := frameS kAB
/-- After the address's `memcpy`: RBX, R15 the bytes taken and left, R13 the address. -/
def s3 : SState := frameS (kAB ++ [(.rbx, .lit 32), (.r15, .lit 32), (.r13, .ptr 0 9344)])
/-- After the clone. -/
def s4 : SState := frameS kAB
/-- After the children's `memcpy`: R12, R15 the bytes taken and left, R13 the children. -/
def s5 : SState := frameS [(.rbp, .ptr 0 576), (.r12, .lit 32), (.r15, .lit 32), (.r13, .ptr 0 3072)]
/-- After the state's `memcpy`: RBX the final block's length. -/
def s6 : SState := frameS (kAB ++ [(.rbx, .lit 80)])
/-- After the block's `memset`: RBX, R13 the block. -/
def s7 : SState := frameS (kAB ++ [(.rbx, .lit 80), (.r13, .ptr 0 2048), (.r15, .label "memset")])
/-- After `keccak_f`, at the loop's test. -/
def s9 : SState := frameS (kAB ++ [(.r13, .ptr 0 2048), (.rbx, .label "memset")])

end

set_option Elab.async false

sym_block run_b151 := exec b151 wotsS
sym_block run_b152 := exec b152 wotsS
sym_block run_b153 := exec b153 wotsS
sym_block run_b154 := exec b154 wotsS
sym_block run_b155 := exec b155 wotsS
sym_block run_b156 := exec b156 wotsS
sym_block run_b157 := exec b157 wotsS
sym_block run_b158 := exec b158 wotsS
sym_block run_b159 := exec b159 (after b158 wotsS)
sym_block run_b160 := exec b160 (after b159 (after b158 wotsS))
sym_block run_b161 := exec b161 (after b160 (after b159 (after b158 wotsS)))
sym_block run_b162_0 := exec b162 (nodeS 0)
sym_block run_b162_8 := exec b162 (nodeS 8)
sym_block run_b162_16 := exec b162 (nodeS 16)
sym_block run_b163 := exec b163 s2
sym_block run_b166 := exec b166 (after b163 s2)
sym_block run_b168 := exec b168 (after b166 (after b163 s2))
sym_block run_b169 := exec b169 (after b168 (after b166 (after b163 s2)))
sym_block run_b170 := exec b170 (after b169 (after b168 (after b166 (after b163 s2))))
sym_block run_b171 := exec b171 s3
sym_block run_b167 := exec b167 (after b171 s3)
sym_block run_b174 := exec b174 (after b167 (after b171 s3))
sym_block run_b175 := exec b175 s4
sym_block run_b177 := exec b177 (after b175 s4)
sym_block run_b178 := exec b178 (after b177 (after b175 s4))
sym_block run_b179 := exec b179 (after b178 (after b177 (after b175 s4)))
sym_block run_b180 := exec b180 s5
sym_block run_b176 := exec b176 (after b180 s5)
sym_block run_b183 := exec b183 (after b176 (after b180 s5))
sym_block run_b184 := exec b184 s6
sym_block run_b185 := exec b185 (after b184 s6)
sym_block run_b186 := exec b186 s7
sym_block run_b187 := exec b187 s7
sym_block run_b188 := exec b188 s9
sym_block run_b189 := exec b189 (after b188 s9)
sym_block run_b191 := exec b191 (after b189 (after b188 s9))
sym_block run_b192 := exec b192 (after b191 (after b189 (after b188 s9)))

end NativeRustcX64.SphincsVerifyProof.Tree
