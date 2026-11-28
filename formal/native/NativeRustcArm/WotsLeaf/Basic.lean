module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.Spec.WotsLeaf
public import NativeRustcArm.Code.Xmss.WotsLeaf

/-!
# `wots_leaf` on AArch64: its map, its frame, its regions

rustc compiles `lean_xmss::wots::wots_leaf` (blocks `b0` to `b50` of `NativeRustcArm.Xmss.WotsLeaf`,
assembly `rustc/asm/signatures-aarch64.s`) with `message_digest`, `codeword`, `chain`
and `wots_leaf_hash` inlined, and in each chain step `th`'s hasher (`memset`, `PK` buffered, the
address by `update`'s loop, the clone, the payload by the loop, `finalize`'s final block and
`keccak_f`) inlined too; it calls `memset`, `memcpy`, `Hasher::update`, `Hasher::finalize` and
`keccak_f`.

## The frame

The prologue stores X29, X30, X28 ... X19 at `SP₀ - 96` (`savedBytes`) and allocates `2656` more
bytes: the frame is the `frameSize = 2752` bytes from `base = SP₀ - 2752`, SP stays `base`, X29 is
`base + 2656`. The callees use at most `finalizeStack` bytes below `base` (`wotsLeafStack`).
Offsets from `base`:

- `0`: `out` (from the codeword on); `8`: the chain values' address; `20`: `(layer << 23) >> 16`;
  `24`: `e`; `28`: `layer << 23` (the address's `hi`).
- `32`: the message digest's hasher (344 bytes).
- `380`: the codeword's 58 digits. `440`: the 58 chain ends (928 bytes).
- `1384`: the chain's current value (16 bytes); `1400`: a step's payload (the value, then the
  chain index as a `u128`).
- `1432`: hasher B (the clone of a step's hasher; buffer at `1632`, `buf_len` at `1768`).
- `1776`: hasher A (a step's hasher; buffer `1976`, `buf_len` `2112`); also the message digest's
  address and digest (32 bytes), the leaf's address, and the result's scratch.
- `2128`: the leaf's digest (32 bytes). `2160`: the leaf's hasher (344 bytes).
- `2504`: a step's address (16 bytes), then its final block (136 bytes, `x29 - 152`).
- `2656`: the saved registers.

## The regions (blocks, directives of the function)

1. **Digest** `b0 .. b5` (directives `0 .. 48`): prologue, `memset` of the hasher at `32`, `update`
   with `P`, the address at `1776`, the message and the randomizer, `finalize` into `1776`.
   Exit: `AtCheck` at `b6` (directive 48).
2. **Codeword** `b6 .. b10`, `b11`, `b12`: the digest's top bits (`b6`), the bit counts (`b7`),
   not a codeword: tag 0 and return (`b11`, `b12`); the digits (loop `b9`, `b10`). Exit:
   `AtChain 0 []` at `b14` (directive 184).
3. **Chains**: chain `i` (`b14`, `b13`, `b41`), each step from its digit to 3 (`b15 .. b40`).
   Exit: `AtLeaf` at `b44` (directive 603).
4. **Leaf** `b44 .. b49`, `b12`: the leaf's hasher, `finalize` into `2128`, the result written to
   `out`, the epilogue.
5. **Panics** `b42`, `b43`, `b50`: `slice_index_fail`, unreachable; so are `b17`, `b18`, `b25`,
   `b26`, `b34`, `b35` (a full buffer in an inlined `update`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-! ## The frame -/

/-- The frame: the 96 bytes of saved registers and `2656`. -/
def frameSize : Nat := 2752

theorem wotsLeafStack_eq : wotsLeafStack = frameSize + finalizeStack := rfl

/-- The bytes the prologue saves at `SP₀ - 96`: X29, X30, X28, X27, ..., X19. -/
def savedBytes (m : MachineData) : List UInt8 :=
  wordsBytes ([XReg.X29, .X30, .X28, .X27, .X26, .X25, .X24, .X23, .X22, .X21, .X20, .X19].map
    m.regs.getXReg)

/-! ## A run -/

/-- A run of `wots_leaf`: the machine at its entry, the function's placement. -/
structure Run where
  m0 : MachineData
  k : Nat

namespace Run

variable (r : Run)

/-- The frame's base, SP inside the function. -/
def base : BitVec 64 := r.m0.regs.SP.toBitVec - BitVec.ofNat 64 frameSize

/-- The frame's byte `off`. -/
def off (off : Nat) : BitVec 64 := r.base + BitVec.ofNat 64 off

/-- The stack area: the frame and the callees' stack below it. -/
def StackArea : BitVec 64 → Prop := InRange (stackBelow r.m0 wotsLeafStack) wotsLeafStack

/-- `out`. -/
def out : BitVec 64 := r.m0.regs.X0.toBitVec
/-- The public parameter. -/
def pp : List UInt8 := WotsLeafPre.pp r.m0
/-- The layer. -/
def layer : Nat := r.m0.regs.X2.toNat
/-- The key index. -/
def e : UInt32 := r.m0.regs.X3.toUInt32
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

/-- **The frame's invariant**: SP and X29, the saved registers in place, no byte changed outside
the stack area, every mapped byte still mapped. -/
def Frame (m : MachineData) : Prop :=
  m.regs.SP.toBitVec = r.base ∧ (m.regs.getXReg .X29).toBitVec = r.off 2656 ∧
    BytesAt m.dmem (r.off 2656) (savedBytes r.m0) ∧ SameOutside r.m0.dmem m.dmem r.StackArea ∧
    Kept r.m0.dmem m.dmem

/-- Register `x` holds `v`. -/
def RegIs (m : MachineData) (x : XReg) (v : BitVec 64) : Prop := (m.regs.getXReg x).toBitVec = v

/-- **Done**: returned to the caller with the result at `out`, its registers kept, memory changed
only at `out` and in the stack. -/
def Done [Labels] (st : MachineState) : Prop := st.pc = retOf r.m0 ∧ WotsLeafPost r.m0 st.data

/-- The pc of the function's directive `j`. -/
def pc [NativeRustcArm.Host] (j : Nat) : Int64 := NativeRustcArm.Host.addrOf (r.k + j)

end Run

/-! ## The callees and the regions -/

section
variable [NativeRustcArm.Host]


/-- **The callees' contracts.** -/
def Callees : Prop :=
  Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost ∧ Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost ∧
    Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost ∧
    Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre FinalizePost ∧
    Spec (label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost

/-- **A region**: placed at `r.k`, given the callees' contracts and the run's precondition, from
directive `j` of the function in a state `P r` the machine inevitably reaches `Q r`. -/
def RegionSpec (P : Run → MachineData → Prop) (j : Nat) (Q : Run → MachineState → Prop) : Prop :=
  ∀ r : Run, Placed Xmss.WotsLeaf.code r.k → Callees → r.Pre → ∀ m, P r m →
    Eventually (step1 NativeRustcArm.Host.exe) (Q r) ⟨m, NativeRustcArm.Host.addrOf (r.k + j)⟩

end

end

end NativeRustcArm.WotsLeafProof
