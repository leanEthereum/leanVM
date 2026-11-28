module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names
public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.Spec.Keccak
public import NativeRustc.Sphincs.SigMem
public import NativeRustcX64.Code.Sphincs.SphincsVerify

/-!
# `sphincs_verify` on x86-64: its map, its frame, its regions

rustc compiles `rustc/sphincs.rs`'s `sphincs_verify` (blocks `b0` to `b200` of
`NativeRustcX64.Sphincs.SphincsVerify`, raw assembly `rustc/asm/signatures-x86_64.s`)
with all of `lean_sphincs` inlined, `Hasher::update`'s loop and
`Hasher::finalize` included where the hasher is a local; it calls `memcpy`, `memset`,
`Hasher::update`, `Hasher::finalize` and `keccak_f` only. The regions and their interfaces follow
the AArch64 proof's (`NativeRustcArm.SphincsVerifyProof`): the same region states over the same
model (`Run.idx`, `Run.forsRoot`, `Run.chainEnds`, ...), with x86-64's registers and offsets.

## The frame

The prologue pushes RBP, R15, R14, R13, R12, RBX (48 bytes below the return address at `RSP₀`),
probes and allocates `7 · 4096 + 680` more bytes: RSP stays `base = RSP₀ - 29400`
(`frameSize`), the saved registers are at `base + 29352` (`savedBytes`: RBX, R12, R13, R14, R15,
RBP), the return address at `base + 29400`. A call pushes its return address at `base - 8`; the
callees use `finalizeStack` bytes below it at most; the bit loop pushes 16 bytes below `base`
(`sphincsStack`). The executor's frame: region 0 the frame with the return address (`frameRegion`
bytes from `base`, RSP `ptr 0 0`), region 1 the 16 bytes below it (the pushes' slots, aliased as
`ptr 0 (-8)` and `ptr 0 (-16)`). Offsets from `base` (`r.off`), the assembly's `N(%rsp)`:

- `8 .. 56`: the inlined absorptions' spills; `60`: the key pair's word (`BE32`), `64`: a step,
  `72`, `80`, `88`, `104`: the FORS tree's / the layer's spills (`88` the tree's word `BE64`,
  `104` the layer's word `BE32`, in the layers), `96` the layer, `112`: the public key's bytes
  (`PK.seed` at `112`, `PK.root` at `128`), `144`: `signed`, the current layer's message (16),
  `160` the height, `168 .. 200` a chain's spills, `176` the current layer's chain values'
  address, `200` the next layer, `208` its offset `4656 + 1028 (l + 1)`, `216` the key's leaf,
  `224 .. 568` the codeword's spills, `568` the index.
- `576`: hasher B (344 bytes, buffer at `776`, `buf_len` at `912`), also the encoder's digest and
  digits. `1600`: the message (32 bytes). `1632 .. 2048`: the paths being parsed, then a chain's
  value (`1632`) and step (`1648`). `2048`: scratch: `h_msg`'s 64 bytes, the addresses, the
  inlined `finalize`'s last block (136). `3072`: the codeword's digits (64), the children (32).
  `4096`: hasher A (buffer `4296`, `buf_len` `4432`), also the 24 leaves (`b55`). `8320`,
  `9344`, `10368`, `11392`: 1024-byte copies during the parse, then addresses and values
  (`11392`: the digests, the index, the leaves' copy at `11400`).
- `12416`: the raw signature `sigBytes w` (7740). `20156`: the 24 FORS roots (384). `20540`: the
  parsed signature in rustc's layout (`sigMem`, 7740 bytes: the openings, the paths at `24764`,
  the randomizer at `25180`, the layers from `25196`, 1028 each). `28280`: the 64 chain ends
  (1024). `29352`: the saved registers; `29400`: the return address.

## The regions (block, directive, what the Rust code does)

1. **Parse** `b0 .. b42` (0 .. 451): prologue; `memset` of the raw signature; the words' bytes
   (loop `b2`, the layers `b4`, `b6`, `b8`, the counters byte-reversed by `bswap`); `from_bytes`
   (loop `b10 .. b13`, 24 openings, three `memcpy`s each; the layers' 1024-byte copies), the
   parsed signature assembled at `20540` (`b38 .. b42`). Exit: `AtHMsg` at `b43` (451).
2. **Digest** `b43 .. b57` (451 .. 680): `h_msg`: hasher B (`576`) new, updated with `R`,
   `PK.seed`, `PK.root`, `M`, cloned to `4096` (`memcpy` 344), updated with `BE32(i)`, finalized
   to `11392`, twice (`h_msg` at `2048`); `digest_fields`: loop `b55` (24 turns, a FORS leaf of 10
   bits, stored at `4096 + 8 c`), the index from bytes 30 .. 33 (`b56`, at `11392`), the leaves
   copied to `11400`; `b57` the FORS loop's registers. Exit: `AtFors` at `b58` (680).
3. **FORS** `b58 .. b96` (680 .. 1088): tree `c` (R13, loop `b58 .. b96`): its leaf `th` with calls
   (`b58 .. b63`), then 10 nodes (loop `b65 .. b95`), each an inlined `th` (the address by the
   inlined `update` loop `b72 .. b77` on hasher A, `keccak_f` on a full buffer, slice checks
   panicking at `b193`, `b194`; the clone `b79`, the children by the loop `b83 .. b88` on hasher
   B; the inlined `finalize` `b90 .. b94`). The roots go to `20156`. Exit: `AtForsKey` at `b97`
   (1088).
4. **FORS key** `b97 .. b103` (1088 .. 1129): `th` of the roots with calls; `signed` at `144`.
   Exit: `AtLayer 0` at `b104` (1129).
5. **Layer** `l` (loop `b104 .. b191`):
   - **Encode** `b104 .. b115` (1129 .. 1538): the key from the index and `LAYER_HEIGHTS` (the
     rodata table `NativeRustcX64.layerHeightsLabel`), the encoder (`th` prefix with calls, cloned, the counter),
     `finalize`; the digits (loop `b113`), their sum (`b114`): a sum other than 128 returns 0
     (`b196`, `b197`); the digits at `3072` (`b115`). Exit: `AtChains l x` at `b117` (1548,
     chain 0).
   - **Chains** `b116 .. b150` (1538 .. 1893): chain `i` (`b117`, its end stored by `b116`), its
     steps (loop `b119 .. b149`), each an inlined `th` like a FORS node's; the ends go to
     `28280`. Exit: `AtWotsPk l ends` at `b151` (1893).
   - **Tree** `b151 .. b192`, `b190`, `b191` (1893 .. 2353): the one-time leaf (`th` of the ends,
     with calls), the path's slice check (`b158`, `b159`, panic `b200`), the height-0 case
     (`b160`, `b190`, unreachable), the fold (loop `b162 .. b188`), each node an inlined `th`;
     `b191` back to `b104` for the next layer, or `b192`: the comparison with `PK.root`. Exit:
     `AtLayer (l + 1)` at `b104` or `Done` (through the epilogue `b197`).
6. **Epilogue** `b196` (`xorl %eax, %eax`), `b197` (2370): RSP back, the registers popped,
   `retq`. **Panics** `b193 .. b195`, `b198 .. b200`: `slice_index_fail`, unreachable.

Each region's statement is a `RegionSpec` below; `NativeRustcX64.SphincsVerify.Compose` composes
them.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-! ## The frame -/

/-- The frame: the 48 bytes of pushed registers and `5 · 4096 + 1096`. -/
def frameSize : Nat := 48 + 5 * 4096 + 1096

/-- The executor's frame region: the frame and the return address above it. -/
def frameRegion : Nat := frameSize + 8

/-- The stack `sphincs_verify` uses below its return address: its frame, a callee's return
address and the deepest callee's stack (`Hasher::finalize`). -/
def sphincsStack : Nat := frameSize + 8 + finalizeStack

/-- The bytes the prologue pushes, from the lowest: RBX, R12, R13, R14, R15, RBP. -/
def savedBytes (m : MachineData) : List UInt8 :=
  wordsBytes ([Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].map fun x ↦ UInt64.ofBitVec (reg m x))


/-- `LAYER_HEIGHTS`' bytes: three `usize`s. -/
def lhBytes : List UInt8 := wordsBytes [8, 8, 10]

/-! ## A run -/

/-- A run of `sphincs_verify`: the machine at its entry, the raw key, message and signature bytes,
and the function's placement. -/
structure Run where
  m0 : MachineData
  pkB : List UInt8
  msgB : List UInt8
  sigB : List UInt8
  hpk : pkB.length = 32
  hmsg : msgB.length = 32
  hsig : sigB.length = 7740
  k : Nat

namespace Run

variable (r : Run)

/-- The frame's base, RSP inside the function. -/
def base : BitVec 64 := rspOf r.m0 - BitVec.ofNat 64 frameSize

/-- The frame's byte `off`, the assembly's `off(%rsp)`. -/
def off (off : Nat) : BitVec 64 := r.base + BitVec.ofNat 64 off

/-- The stack area: the bytes below the return address the function and its callees use. -/
def StackArea : BitVec 64 → Prop := InRange (stackBelow r.m0 sphincsStack) sphincsStack

/-- The public key's address (`rdi`). -/
def pkPtr : BitVec 64 := reg r.m0 .rdi
/-- The message's address (`rsi`). -/
def msgPtr : BitVec 64 := reg r.m0 .rsi
/-- The signature's address (`rdx`). -/
def sigPtr : BitVec 64 := reg r.m0 .rdx

/-- The public key. -/
def pk : PublicKey := PublicKey.fromBytes r.pkB
/-- The message. -/
def msg : List UInt8 := r.msgB
/-- The parsed signature. -/
def sig : Signature := sigOfBytes r.sigB
/-- `PK.seed`. -/
def seed : List UInt8 := r.pk.pkSeed
/-- The message digest's fields. -/
def digest : UInt64 × List Nat := messageDigest r.pk r.sig.randomizer r.msg
/-- The index. -/
def idx : UInt64 := r.digest.1
/-- The FORS leaves. -/
def leaves : List Nat := r.digest.2
/-- Layer `l`'s key. -/
def key (l : Nat) : OtsKey := OtsKey.ofIndex l r.idx
/-- Layer `l`'s signature. -/
def layerSig (l : Nat) : LayerSignature := r.sig.layers.getD l ⟨0, []⟩

/-- FORS tree `c`'s root, as `forsRecover` computes it. -/
def forsRoot (c : Nat) : List UInt8 :=
  pathFold (forsLeaf r.seed r.idx c (r.leaves.getD c 0) (r.sig.fors.getD c ⟨[], []⟩).secret)
    (r.leaves.getD c 0) (r.sig.fors.getD c ⟨[], []⟩).path fun z j pair ↦ forsNode r.seed r.idx c z j pair

/-- The FORS key, the first layer's message. -/
def forsPk : List UInt8 := forsRecover r.seed r.idx r.leaves r.sig.fors

/-- Layer `l`'s chain ends for the codeword `x`, as `wots_leaf` computes them. -/
def chainEnds (l : Nat) (x : List UInt8) : List (List UInt8) :=
  (List.range 64).map fun i ↦
    chain r.seed (r.key l) i (x.getD i 0).toNat (3 - (x.getD i 0).toNat) ((r.layerSig l).wots.getD i [])

/-- Layer `l`'s next message from its chain ends `e`: the one-time leaf folded up its path. -/
def layerRoot (l : Nat) (e : List (List UInt8)) : List UInt8 :=
  treeFold r.seed (r.key l) (wotsLeafHash r.seed (r.key l) e) (r.sig.path l)

/-- What verification returns from layer `l` on, its message `s`. -/
def resultFrom (l : Nat) (s : List UInt8) : Bool :=
  match layersFrom r.seed r.idx r.sig (List.range' l (3 - l)) s with
  | none => false
  | some root => root == r.pk.root

/-! ## The run's facts -/

/-- **The precondition**: the stack, round constants, `LAYER_HEIGHTS`, key/message/signature
buffers, and the two loader-provided GOT slots, separated from writable memory. -/
def Pre [Labels] : Prop :=
  StackOk r.m0 sphincsStack ∧ RcAt r.m0 sphincsStack ∧
    BytesAt r.m0.dmem (label NativeRustcX64.layerHeightsLabel).toBitVec lhBytes ∧ NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec 24 ∧
    Apart (label NativeRustcX64.layerHeightsLabel).toBitVec 24 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) ∧
    BytesAt r.m0.dmem r.pkPtr r.pkB ∧ NoWrap r.pkPtr 32 ∧
    Apart r.pkPtr 32 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) ∧
    BytesAt r.m0.dmem r.msgPtr r.msgB ∧ NoWrap r.msgPtr 32 ∧
    Apart r.msgPtr 32 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) ∧
    BytesAt r.m0.dmem r.sigPtr r.sigB ∧ NoWrap r.sigPtr 7740 ∧
    Apart r.sigPtr 7740 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) ∧
    GotAt r.m0 sphincsStack
      [(r.pkPtr, 32), (r.msgPtr, 32), (r.sigPtr, 7740), ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24)]
      ["memcpy", "memset"]

/-- **The frame's invariant**: RSP the base, the pushed registers in place, no byte changed
outside the stack area (the return address kept), every mapped byte still mapped. -/
def Frame (m : MachineData) : Prop :=
  rspOf m = r.base ∧ BytesAt m.dmem (r.off 21576) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem r.StackArea ∧ Kept r.m0.dmem m.dmem

/-- Register `x` holds `v`. -/
def RegIs (m : MachineData) (x : Reg64) (v : BitVec 64) : Prop := reg m x = v

/-- The frame's 8 bytes at `off` hold `v`. -/
def WordAt (m : MachineData) (off : Nat) (v : UInt64) : Prop := BytesAt m.dmem (r.off off) (wordBytes v)

/-- The frame's address `a`, as a word. -/
def addr (off : Nat) : UInt64 := UInt64.ofBitVec (r.off off)

/-- The key and the parsed signature in the frame. -/
def Inputs (m : MachineData) : Prop :=
  BytesAt m.dmem (r.off 112) r.pkB ∧ BytesAt m.dmem (r.off 12780) (sigMem r.sig)

/-- **Done**: returned to the caller, RSP 8 above, with `v` in RAX, no byte changed outside the
stack area, its registers and memory kept. -/
def Done (v : Bool) (st : MachineState) : Prop :=
  st.pc = retOf r.m0 ∧ rspOf st.data = rspOf r.m0 + 8#64 ∧
    reg st.data .rax = (if v then 1 else 0) ∧ SameOutside r.m0.dmem st.data.dmem r.StackArea ∧
    Saved r.m0 st.data

/-! ## The states between regions -/

/-- **At `b34`** (after the parse): R13 the randomizer (`base + 17420`); the key, the signature,
the message pointer at `8`; `184` the first layer's chain values' address. -/
def AtHMsg [Labels] (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .r13 (r.off 17420) ∧ r.WordAt m 8 (UInt64.ofBitVec r.msgPtr) ∧
    r.WordAt m 184 (r.addr 17436) ∧ RegIs m .rbp (Labels.label "memcpy").toBitVec

/-- **At `b49`, tree 0**: RSI the tree counter, R13 the address's tree word, EBP the key
pair's word, R12 hasher A, R14 `PK.seed`, R15 hasher B. -/
def AtFors [Labels] (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .rsi 0 ∧
    wordBytes (UInt64.ofBitVec (reg m .r13)) = be64 (r.key 0).tree ∧
    wordBytes (UInt64.ofBitVec (reg m .rbp)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0] ∧
    RegIs m .r12 (r.off 4072) ∧ RegIs m .r14 (r.off 112) ∧
    BytesAt m.dmem (r.off 80) (be64 (r.key 0).tree) ∧ BytesAt m.dmem (r.off 68) (be32 (r.key 0).leaf) ∧
    BytesAt m.dmem (r.off 10352) (wordsBytes (r.leaves.map Nat.toUInt64)) ∧
    r.WordAt m 552 r.idx ∧ r.WordAt m 184 (r.addr 17436) ∧
    RegIs m .rbx (Labels.label "memset").toBitVec ∧ RegIs m .r15 (r.off 560)

/-- **At `b88`**: R13 the tree's word, EBP the key pair's; the roots at `12396`. -/
def AtForsKey (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ wordBytes (UInt64.ofBitVec (reg m .r13)) = be64 (r.key 0).tree ∧
    wordBytes (UInt64.ofBitVec (reg m .rbp)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0] ∧
    BytesAt m.dmem (r.off 12396) ((List.range 24).map r.forsRoot).flatten ∧
    r.WordAt m 552 r.idx ∧ r.WordAt m 184 (r.addr 17436)

/-- **At `b95`, layer `l < 3`** with message `s`: the layer-loop registers, hashers,
message, chain values' address and index. -/
def AtLayer [Labels] (l : Nat) (s : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.Inputs m ∧
    RegIs m .rcx (BitVec.ofNat 64 (4656 + 1028 * l)) ∧ RegIs m .rsi (BitVec.ofNat 64 l) ∧
    RegIs m .rdx (label NativeRustcX64.layerHeightsLabel).toBitVec ∧ RegIs m .rbx 0 ∧ RegIs m .r12 (r.off 4072) ∧
    RegIs m .rbp (r.off 560) ∧ RegIs m .r13 (r.off 2024) ∧ RegIs m .r15 (r.off 144) ∧
    BytesAt m.dmem (r.off 144) s ∧ r.WordAt m 184 (r.addr (17436 + 1028 * l)) ∧
    r.WordAt m 552 r.idx ∧ RegIs m .r14 (Labels.label "memcpy").toBitVec

/-- The layer loop's spills a layer's chains and tree read: the layer, the next layer, its
offset, the height, the key's leaf, the layer's, the tree's and the key pair's words (`BE`), the
index, the layer's chain values' address. -/
def LayerSpills (l : Nat) (m : MachineData) : Prop :=
  r.WordAt m 96 l.toUInt64 ∧ r.WordAt m 192 (l + 1).toUInt64 ∧
    r.WordAt m 200 (4656 + 1028 * (l + 1)).toUInt64 ∧
    r.WordAt m 168 (layerHeights.getD l 0).toUInt64 ∧ r.WordAt m 208 (r.key l).leaf.toUInt64 ∧
    BytesAt m.dmem (r.off 104) (be32 l.toUInt32) ∧ BytesAt m.dmem (r.off 88) (be64 (r.key l).tree) ∧
    BytesAt m.dmem (r.off 68) (be32 (r.key l).leaf) ∧ r.WordAt m 552 r.idx ∧
    r.WordAt m 184 (r.addr (17436 + 1028 * l))

/-- **At `b108`, chain 0 of layer `l < 3`**, the codeword at `3048`, RAX zero,
R12 hasher A and R13 the chain input buffer. -/
def AtChains [Labels] (l : Nat) (x : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ x.length = 64 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .rax 0 ∧
    RegIs m .r12 (r.off 4072) ∧ RegIs m .r13 (r.off 8296) ∧
    BytesAt m.dmem (r.off 3048) x ∧
    RegIs m .rbx (Labels.label "memset").toBitVec ∧ RegIs m .r14 (Labels.label "memcpy").toBitVec

/-- **At `b142`, layer `l < 3`'s chain ends** at `20520`. -/
def AtWotsPk [Labels] (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  l < 3 ∧ e.flatten.length = 1024 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧
    RegIs m .r12 (r.off 4072) ∧ RegIs m .r13 (r.off 8296) ∧
    BytesAt m.dmem (r.off 20520) e.flatten ∧
    RegIs m .rbx (Labels.label "memset").toBitVec ∧ RegIs m .r14 (Labels.label "memcpy").toBitVec

end Run

/-! ## The callees and the regions -/

section
variable [Host]


/-- **The callees' contracts.** -/
def Callees : Prop :=
  Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost ∧ Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost ∧
    Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost ∧
    Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost ∧
    Spec (label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost

/-- **A region**: placed at `r.k`, given the callees' contracts and the run's precondition, from
directive `j` of the function in a state `P r` the machine inevitably reaches `Q r`. -/
def RegionSpec (P : Run → MachineData → Prop) (j : Nat) (Q : Run → MachineState → Prop) : Prop :=
  ∀ r : Run, Placed Sphincs.SphincsVerify.code r.k → Callees → r.Pre → ∀ m, P r m →
    Eventually (step1 Host.exe) (Q r) ⟨m, Host.addrOf (r.k + j)⟩

/-- The pc of the function's directive `j`. -/
def Run.pc (r : Run) (j : Nat) : Int64 := Host.addrOf (r.k + j)

/-- Region 1, the parse: from the entry to `b34`. -/
def ParseSpec : Prop :=
  RegionSpec (fun r m ↦ m = r.m0) NativeRustcX64.Sphincs.SphincsVerify.b0Offset fun r st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b34Offset ∧ r.AtHMsg st.data

/-- Region 2, the digest: from `b34` to `b49`. -/
def DigestSpec : Prop :=
  RegionSpec (fun r => r.AtHMsg) NativeRustcX64.Sphincs.SphincsVerify.b34Offset fun r st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b49Offset ∧ r.AtFors st.data

/-- Region 3, the FORS trees: from `b49` to `b88`. -/
def ForsSpec : Prop :=
  RegionSpec (fun r => r.AtFors) NativeRustcX64.Sphincs.SphincsVerify.b49Offset fun r st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b88Offset ∧ r.AtForsKey st.data

/-- Region 4, the FORS key: from `b88` to `b95`, layer 0. -/
def ForsKeySpec : Prop :=
  RegionSpec Run.AtForsKey NativeRustcX64.Sphincs.SphincsVerify.b88Offset fun r st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer 0 r.forsPk st.data

/-- Region 5a, a layer's encoding: from `b95` to `b108` with the codeword, or
returned 0 without one. -/
def EncodeSpec : Prop :=
  ∀ l s, RegionSpec (fun r ↦ r.AtLayer l s) NativeRustcX64.Sphincs.SphincsVerify.b95Offset fun r st ↦
    (encode r.seed (r.key l) s (r.layerSig l).counter = none ∧ r.Done false st) ∨
      ∃ x, encode r.seed (r.key l) s (r.layerSig l).counter = some x ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b108Offset ∧
        r.AtChains l x st.data

/-- Region 5b, a layer's chains: from `b108` to `b142`. -/
def ChainsSpec : Prop :=
  ∀ l x, RegionSpec (fun r ↦ r.AtChains l x) NativeRustcX64.Sphincs.SphincsVerify.b108Offset fun r st ↦
    st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b142Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data

/-- Region 5c, a layer's tree: from `b142` to the next layer at `b95`, or, after the last,
returned the comparison with `PK.root`. -/
def TreeSpec : Prop :=
  ∀ l e, RegionSpec (fun r ↦ r.AtWotsPk l e) NativeRustcX64.Sphincs.SphincsVerify.b142Offset fun r st ↦
    if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
    else st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data

end

end

end NativeRustcX64.SphincsVerifyProof
