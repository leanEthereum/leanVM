module

public import NativeRustcX64.Spec.WotsLeaf
public import NativeRustcX64.Code.Xmss.WotsLeaf

/-!
# `wots_leaf` on x86-64: its map, its frame, its regions

rustc compiles `lean_xmss::wots::wots_leaf` (blocks `b0` to `b58` of
`NativeRustcX64.Xmss.WotsLeaf`, raw assembly `rustc/asm/signatures-x86_64.s`) with
`message_digest`, `codeword`, `chain` and `wots_leaf_hash` inlined, and in each chain step `th`'s
hasher inlined too (`memset`, the public parameter buffered, the address by `update`'s loop, the
clone, the payload by the loop, `finalize`'s final block and `keccak_f`); it calls `memset`,
`memcpy`, `Hasher::update`, `Hasher::finalize` and `keccak_f`.

## The frame

The prologue pushes RBP, R15, R14, R13, R12, RBX below the return address and allocates `2712`
more bytes: the frame is the `frameSize = 2760` bytes from `base = RSP₀ - 2760`, RSP stays `base`.
The saved registers are at `2712` (`savedBytes`), the return address at `2760` and the stack
arguments, the randomizer's and the chain values' addresses, at `2768` and `2776`. A call pushes
its return address at `base - 8`; the callees use at most `finalizeStack` bytes below it
(`wotsLeafStack`). Offsets from `base`:

- `8`: the layer, then `layer << 23` (the address's `hi`); `16 .. 48` scratch of the absorbing
  blocks; `48`: `(layer << 23) >> 16`; `52`: `e`; `56`: a step's position.
- `80`: the chain's current value (16 bytes). `96`: `out`; `104`: the public parameter's address.
- `112`: the message digest's address, then its digest (32 bytes); in a chain step hasher A (344
  bytes: state `112`, buffer `312`, `buf_len` `448`); the leaf's address; the result's 74 bytes.
- `456`: `16 i`; `464`: `i`; `472`: a step's address (16 bytes), then its final block (136).
- `614`: the codeword's 58 digits. `672`: a step's payload (the value, then `i` as a `u128`).
- `704`: hasher B (the clone; buffer `904`, `buf_len` `1040`). `1048`: the leaf (32 bytes).
- `1080`: the 58 chain ends (928 bytes). `2008`: the message digest's hasher (344 bytes).
- `2352`: the leaf's hasher (344 bytes). `2712`: the saved registers.

## The regions (blocks, directives of the function)

1. **Digest** `b0 .. b5` (directives `0 .. 47`): prologue, `memset` of the hasher at `2008`,
   `update` with `P`, the address at `112`, the message and the randomizer, `finalize` into `112`.
2. **Codeword** `b6 .. b10`, `b11`, `b12`: the digest's top bits (`b6`), the bit counts (`b7`),
   not a codeword: tag 0 and return (`b11`, `b12`); the digits (loop `b9`, `b10`).
3. **Chains**: chain `i` (`b15`, `b16`, `b14`), each step from its digit to 3 (`b17 .. b48`).
4. **Leaf** `b51 .. b57`, `b12`: the leaf's hasher, `finalize` into `1048`, the result written to
   `out`, the epilogue.
5. **Panics** `b49`, `b50`, `b58`: `slice_index_fail`, unreachable; so are `b19`, `b20`, `b28`,
   `b29`, `b39`, `b40` (a full buffer in an inlined `update`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-! ## The frame -/

/-- The frame: the 48 bytes of saved registers and `2712`. -/
def frameSize : Nat := 2760

/-- The bytes the executor's region 0 covers: the frame, the return address and the stack
arguments. -/
def regionSize : Nat := 2784

theorem wotsLeafStack_eq : wotsLeafStack = frameSize + 8 + finalizeStack := rfl

/-- The bytes the prologue pushes at `RSP₀ - 48`: RBX, R12, R13, R14, R15, RBP. -/
def savedBytes (m : MachineData) : List UInt8 :=
  wordsBytes ([Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].map fun r ↦ UInt64.ofBitVec (reg m r))

/-! ## A run -/

/-- A run of `wots_leaf`: the machine at its entry, the function's placement. -/
structure Run where
  m0 : MachineData
  k : Nat

namespace Run

variable (r : Run)

/-- The frame's base, RSP inside the function. -/
def base : BitVec 64 := rspOf r.m0 - BitVec.ofNat 64 frameSize

/-- The frame's byte `off`. -/
def off (off : Nat) : BitVec 64 := r.base + BitVec.ofNat 64 off

/-- The stack area: the frame, a call's return address and the callees' stack below it. -/
def StackArea : BitVec 64 → Prop := InRange (stackBelow r.m0 wotsLeafStack) wotsLeafStack

/-- `out`. -/
def out : BitVec 64 := reg r.m0 .rdi
/-- The public parameter. -/
def pp : List UInt8 := WotsLeafPre.pp r.m0
/-- The layer. -/
def layer : Nat := WotsLeafPre.layer r.m0
/-- The key index. -/
def e : UInt32 := WotsLeafPre.e r.m0
/-- The message. -/
def msg : List UInt8 := WotsLeafPre.message r.m0
/-- The randomizer. -/
def rnd : List UInt8 := WotsLeafPre.randomizer r.m0
/-- The chain values. -/
def values : List (List UInt8) := WotsLeafPre.values r.m0
/-- The address's `hi`, `layer_hi(layer, 0)`. -/
def hi : UInt32 := layerHi r.layer 0

/-- The address of the hash of type `t` at chain step `step`. -/
def addr (t : UInt8) (step : Nat) : List UInt8 := address ((tweak t r.hi r.e).withStep step)

/-- The message digest's 32 bytes. -/
def digest32 : List UInt8 := hashBytes (r.pp ++ r.addr 12 0 ++ r.msg ++ r.rnd)

/-- The result. -/
def result : Option (List UInt8 × List UInt8) := wotsLeaf r.pp r.layer r.e r.msg r.rnd r.values

/-- **The precondition**: the contract's. -/
def Pre [Labels] : Prop := WotsLeafPre r.m0

/-- **The frame's invariant**: RSP the frame's base, the saved registers in place, no byte changed
outside the stack area (the return address and the stack arguments among them), every mapped
byte still mapped. -/
def Frame (m : MachineData) : Prop :=
  reg m .rsp = r.base ∧ BytesAt m.dmem (r.off 2712) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem r.StackArea ∧ Kept r.m0.dmem m.dmem

/-- Register `x` holds `v`. -/
def RegIs (m : MachineData) (x : Reg64) (v : BitVec 64) : Prop := reg m x = v

/-- **Done**: returned to the caller with the result at `out`, its registers kept, memory changed
only at `out` and in the stack. -/
def Done [Labels] (st : MachineState) : Prop :=
  st.pc = retOf r.m0 ∧ rspOf st.data = rspOf r.m0 + 8#64 ∧ WotsLeafPost r.m0 st.data

/-- The pc of the function's directive `j`. -/
def pc [Host] (j : Nat) : Int64 := Host.addrOf (r.k + j)

end Run

/-! ## The callees and the regions -/

section
variable [Host]

/-- **The callees' contracts.** -/
abbrev Callees : Prop := WotsLeafCallees

/-- **A region**: placed at `r.k`, given the callees' contracts and the run's precondition, from
directive `j` of the function in a state `P r` the machine inevitably reaches `Q r`. -/
def RegionSpec (P : Run → MachineData → Prop) (j : Nat) (Q : Run → MachineState → Prop) : Prop :=
  ∀ r : Run, Placed Xmss.WotsLeaf.code r.k → Callees → r.Pre → ∀ m, P r m →
    Eventually (step1 Host.exe) (Q r) ⟨m, Host.addrOf (r.k + j)⟩

end

end

end NativeRustcX64.WotsLeafProof
