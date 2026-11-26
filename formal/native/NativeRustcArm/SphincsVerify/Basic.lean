module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names
public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.Spec.Keccak
public import NativeRustc.Sphincs.Model
public import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# `sphincs_verify` on AArch64: its map, its frame, its regions

rustc compiles `rustc/sphincs.rs`'s `sphincs_verify(pk, msg, sig)` (blocks `b0` to `b183` of
`NativeRustcArm.Sphincs.SphincsVerify`, assembly `rustc/asm/signatures-aarch64.s`)
with all of `lean_sphincs` inlined, `Hasher::update`'s loop and `Hasher::finalize` included where
the hasher is a local; it calls `memcpy`, `memset`, `Hasher::update`, `Hasher::finalize` and
`keccak_f` only.

## The frame

The prologue stores X29, X30, X28 ... X19 at `SP₀ - 96` (`savedBytes`), probes and allocates
`5 · 4096 + 1040` more bytes: the frame is the `frameSize = 21616` bytes from `base = SP₀ - 21616`,
SP stays `base`, X29 is `base + 21520`. The callees use `finalizeStack` bytes below `base`, the most
of the three (`sphincsStack`). Offsets from `base`:

- `0 .. 56`: the layer loop's spills (`8` = `base + 19009`, `16` the next layer, `24` the next
  layer's offset `4656 + 1028 (l + 1)`, `32` the layer, `40` the key's leaf, `48` the height);
  `56 .. 424` the codeword's spills (`b102`); `392` the paths' address `base + 4708`, `400` the
  index, `408` the current layer's address `base + 5140 + 1028 l`, `416 .. 448` the FORS and layer
  loops' spills (`424` the key pair word, `432` the layer word, `440` the tree word).
- `448`: the public key's bytes (`PK.seed` at `448`, `PK.root` at `464`).
- `484`: the parsed signature in rustc's layout (`sigMem`, 7740 bytes): the 24 FORS openings
  (path, then secret: 176 each), the 26 path nodes (`4708`), the randomizer (`5124`), the three
  layers (64 chain values then the counter, 1028 each, from `5140`).
- `8224 .. 8640`: scratch of the parse (the paths being assembled) and chain value.
- `8640`: hasher A (344 bytes: state, buffer at `8840`, `buf_len` at `8976`), also the FORS
  openings during parse and the digest's 24 leaves (`b48`).
- `12864 .. 19008`: scratch: copies of the layers' chain values during the parse; the hash
  inputs (`13888`: an address and two children, `15936`: the codeword's digits, `16960`: `h_msg`'s
  64 bytes, then an address), `17984` the index and `17992` the 24 leaves.
- `19008`: hasher B (buffer `19208`, `buf_len` `19344`), also the codeword's digits.
  `20032`: `signed`, the current layer's message (16 bytes); `20048`: randomizer scratch;
  `20064`: the 24 FORS roots; `20464`: the 64 chain ends. `21520`: the saved registers.

## The regions

1. **Parse** `b0 .. b35`: prologue and stack probe loop (`b1`, 5 turns); `b2` copies `pk` to `448`
   and `R` to `20048`, keeps `sig` in X19 and `msg` in X21; `from_bytes` openings loop `b3 .. b6`
   (24 openings, three `memcpy`s each), `memset` of the paths (`b7`), per layer a 1024-byte copy
   loop (`b9`, `b17`, `b25`) and five 1024-byte `memcpy`s, then the parsed signature assembled at
   `484` (`b31 .. b35`). Exit: `AtHMsg` at `b36`.
2. **Digest** `b36 .. b49`: `h_msg` (using `X21 = msgPtr` for the message); `digest_fields` loop
   `b48` and index `b49`. Exit: `AtFors` at `b50`.
3. **FORS** `b50 .. b84`: 24 trees, 10 nodes each. Exit: `AtForsKey` at `b85`.
4. **FORS key** `b85 .. b91`: `th` of the roots; `signed` at `20032`. Exit: `AtLayer 0` at `b92`.
5. **Layer** `l` (`b92 .. b172`):
   - **Encode** `b92 .. b103`, `b178`: Exit `AtChains l x` at `b105` or `Done false`.
   - **Chains** `b104 .. b133`: Exit `AtWotsPk l ends` at `b134`.
   - **Tree** `b134 .. b173`: Exit `AtLayer (l + 1)` at `b92` or `Done`.
6. **Panics** `b174 .. b177`, `b180 .. b183`: `slice_index_fail`, unreachable.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-! ## The frame -/

/-- The frame: the 96 bytes of saved registers and `5 · 4096 + 1040`. -/
def frameSize : Nat := 96 + 5 * 4096 + 1040

/-- The stack `sphincs_verify` uses: its frame and the deepest callee's (`Hasher::finalize`). -/
def sphincsStack : Nat := frameSize + finalizeStack

/-- The bytes the prologue saves at `SP₀ - 96`: X29, X30, X28, X27, ..., X19. -/
def savedBytes (m : MachineData) : List UInt8 :=
  wordsBytes ([XReg.X29, .X30, .X28, .X27, .X26, .X25, .X24, .X23, .X22, .X21, .X20, .X19].map
    m.regs.getXReg)

/-- `LAYER_HEIGHTS`' bytes: three `usize`s. -/
def lhBytes : List UInt8 := wordsBytes [8, 8, 10]

/-- `u32`'s bytes in memory. -/
def le32 (x : UInt32) : List UInt8 := (be32 x).reverse

/-! ## The parsed signature in memory -/

/-- A FORS opening: its path, then its secret. -/
def openingMem (o : ForsTreeOpening) : List UInt8 := o.path.flatten ++ o.secret

/-- A layer's signature: its chain values, then its counter. -/
def layerMem (s : LayerSignature) : List UInt8 := s.wots.flatten ++ le32 s.counter

/-- **`LeanSphincsSignature` in rustc's layout**: the FORS openings, the paths, the randomizer,
the layers. -/
def sigMem (s : Signature) : List UInt8 :=
  (s.fors.map openingMem).flatten ++ (s.paths.flatten ++ (s.randomizer ++
    (s.layers.map layerMem).flatten))

/-! ## A run -/

/-- A run of `sphincs_verify`: the machine at its entry, the raw input byte slices (`pk`, `msg`,
`sig`) with their fixed lengths, and the function's placement. -/
structure Run where
  m0 : MachineData
  pkBytes : List UInt8
  msgBytes : List UInt8
  sigBytes : List UInt8
  hpk : pkBytes.length = 32
  hmsg : msgBytes.length = 32
  hsig : sigBytes.length = 7740
  k : Nat

namespace Run

variable (r : Run)

/-- The frame's base, SP inside the function. -/
def base : BitVec 64 := r.m0.regs.SP.toBitVec - BitVec.ofNat 64 frameSize

/-- The frame's byte `off`. -/
def off (off : Nat) : BitVec 64 := r.base + BitVec.ofNat 64 off

/-- The stack area: the frame and the callees' stack below it. -/
def StackArea : BitVec 64 → Prop := InRange (stackBelow r.m0 sphincsStack) sphincsStack

/-- The public key pointer (`X0`). -/
def pkPtr : BitVec 64 := r.m0.regs.X0.toBitVec

/-- The message pointer (`X1`). -/
def msgPtr : BitVec 64 := r.m0.regs.X1.toBitVec

/-- The signature pointer (`X2`). -/
def sigPtr : BitVec 64 := r.m0.regs.X2.toBitVec

/-- The public key. -/
def pk : PublicKey := PublicKey.fromBytes r.pkBytes
/-- The message. -/
def msg : List UInt8 := r.msgBytes
/-- The parsed signature. -/
def sig : Signature := Signature.fromBytes r.sigBytes
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

/-- **The precondition**: the stack, the round constants, `LAYER_HEIGHTS`, and the three raw-byte
input buffers (`pk`, `msg`, `sig`) in place, apart from the stack. -/
def Pre [Labels] : Prop :=
  StackOk r.m0 sphincsStack ∧ RcAt r.m0 sphincsStack ∧
    BytesAt r.m0.dmem (label NativeRustcArm.layerHeightsLabel).toBitVec lhBytes ∧
    NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec 24 ∧
    Apart (label NativeRustcArm.layerHeightsLabel).toBitVec 24 (stackBelow r.m0 sphincsStack) sphincsStack ∧
    BytesAt r.m0.dmem r.pkPtr r.pkBytes ∧ NoWrap r.pkPtr 32 ∧
    Apart r.pkPtr 32 (stackBelow r.m0 sphincsStack) sphincsStack ∧
    BytesAt r.m0.dmem r.msgPtr r.msgBytes ∧ NoWrap r.msgPtr 32 ∧
    Apart r.msgPtr 32 (stackBelow r.m0 sphincsStack) sphincsStack ∧
    BytesAt r.m0.dmem r.sigPtr r.sigBytes ∧ NoWrap r.sigPtr 7740 ∧
    Apart r.sigPtr 7740 (stackBelow r.m0 sphincsStack) sphincsStack

/-- **The frame's invariant**: SP and X29, the saved registers in place, no byte changed outside
the stack area, every mapped byte still mapped. -/
def Frame (m : MachineData) : Prop :=
  m.regs.SP.toBitVec = r.base ∧ (m.regs.getXReg .X29).toBitVec = r.off 21520 ∧
    BytesAt m.dmem (r.off 21520) (savedBytes r.m0) ∧ SameOutside r.m0.dmem m.dmem r.StackArea ∧
    Kept r.m0.dmem m.dmem

/-- Register `x` holds `v`. -/
def RegIs (m : MachineData) (x : XReg) (v : BitVec 64) : Prop := (m.regs.getXReg x).toBitVec = v

/-- The frame's 8 bytes at `off` hold `v`. -/
def WordAt (m : MachineData) (off : Nat) (v : UInt64) : Prop := BytesAt m.dmem (r.off off) (wordBytes v)

/-- The frame's address `a`, as a word. -/
def addr (off : Nat) : UInt64 := UInt64.ofBitVec (r.off off)

/-- The key, the parsed signature, and the paths' pointer spill in the frame. -/
def Inputs (m : MachineData) : Prop :=
  BytesAt m.dmem (r.off 448) r.pkBytes ∧ BytesAt m.dmem (r.off 484) (sigMem r.sig) ∧
    r.WordAt m 392 (r.addr 4708)

/-- **Done**: returned to the caller with `v` in X0, no byte changed outside the stack area, its
registers and memory kept. -/
def Done (v : Bool) (st : MachineState) : Prop :=
  st.pc = retOf r.m0 ∧ st.data.regs.X0 = (if v then 1 else 0) ∧
    SameOutside r.m0.dmem st.data.dmem r.StackArea ∧ Saved r.m0 st.data

/-! ## The states between regions -/

/-- **At `b7`** (the parse, after the FORS openings' loop): the key at `448`, the openings in
rustc's layout at `8640`, the randomizer at `20048`; X19 the raw signature pointer, X20 the key,
X21 the message pointer, X22 the parsed signature's base `484`. -/
def AtParse7 (m : MachineData) : Prop :=
  r.Frame m ∧ BytesAt m.dmem (r.off 448) r.pkBytes ∧
    BytesAt m.dmem (r.off 8640) ((r.sig.fors.map openingMem).flatten) ∧
    BytesAt m.dmem (r.off 20048) r.sig.randomizer ∧ RegIs m .X19 r.sigPtr ∧
    RegIs m .X20 (r.off 448) ∧ RegIs m .X21 r.msgPtr ∧ RegIs m .X22 (r.off 484)

/-- **At `b36`** (after the parse): X20 the key, X25 the parsed signature, X26 `4640`, X19
`base + 16960` (where `h_msg`'s bytes go), X21 the message pointer; the key and signature in place;
`408` the first layer's address. -/
def AtHMsg (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .X20 (r.off 448) ∧ RegIs m .X25 (r.off 484) ∧
    RegIs m .X26 4640 ∧ RegIs m .X19 (r.off 16960) ∧ RegIs m .X21 r.msgPtr ∧
    r.WordAt m 408 (r.addr 5140)

/-- **At `b50`** (after the digest): X21 the index, X19 its low byte, X24 the leaves' copy, X20
hasher A, X23 `base + 15936`; the 24 leaves at `17992`. -/
def AtFors (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .X21 r.idx.toBitVec ∧
    RegIs m .X19 (r.idx &&& 255).toBitVec ∧ RegIs m .X24 (r.off 17992) ∧
    RegIs m .X20 (r.off 8640) ∧ RegIs m .X23 (r.off 15936) ∧
    BytesAt m.dmem (r.off 17992) (wordsBytes (r.leaves.map Nat.toUInt64)) ∧
    r.WordAt m 408 (r.addr 5140)

/-- **At `b85`** (after the FORS trees): X20 the tree's word, W25 the key pair's, X23
`base + 15936`, X27 `base + 19008`; the 24 roots at `20064`; `400` the index. -/
def AtForsKey (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ wordBytes (m.regs.getXReg .X20) = be64 (r.key 0).tree ∧
    wordBytes (m.regs.getXReg .X25) = be32 (r.key 0).leaf ++ [0, 0, 0, 0] ∧
    RegIs m .X23 (r.off 15936) ∧ RegIs m .X27 (r.off 19008) ∧
    BytesAt m.dmem (r.off 20064) ((List.range 24).map r.forsRoot).flatten ∧
    r.WordAt m 400 r.idx ∧ r.WordAt m 408 (r.addr 5140)

/-- **At `b92`, layer `l < 3`** with message `s`: the loop's registers (X10 the layer, X8
`LAYER_HEIGHTS`, X11 the layer's offset `4656 + 1028 l`, X12 `8`, X23 `16`, W13 the encoding
type's word, X22 `base + 15936`, X19 `136`, X21 and X25 the hashers' buffers, X24 the digits' end
`base + 19009`, X27 `base + 19008`), `s` at `20032`, the spills `8`, `400`, `408`. -/
def AtLayer [Labels] (l : Nat) (s : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.Inputs m ∧ RegIs m .X10 (BitVec.ofNat 64 l) ∧
    RegIs m .X8 (label NativeRustcArm.layerHeightsLabel).toBitVec ∧
    RegIs m .X11 (BitVec.ofNat 64 (4656 + 1028 * l)) ∧ RegIs m .X12 8 ∧ RegIs m .X23 16 ∧
    RegIs m .X13 0x07000000 ∧ RegIs m .X22 (r.off 15936) ∧ RegIs m .X19 136 ∧
    RegIs m .X21 (r.off 19208) ∧ RegIs m .X24 (r.off 19009) ∧ RegIs m .X25 (r.off 8840) ∧
    RegIs m .X27 (r.off 19008) ∧ BytesAt m.dmem (r.off 20032) s ∧
    r.WordAt m 8 (r.addr 19009) ∧ r.WordAt m 400 r.idx ∧
    r.WordAt m 408 (r.addr (5140 + 1028 * l))

/-- The layer loop's spills a layer's chains and tree read: `base + 19009`, the next layer, its
offset, the layer, the key's leaf, the height, the index, the layer's address, the key pair's,
the layer's and the tree's words. -/
def LayerSpills (l : Nat) (m : MachineData) : Prop :=
  r.WordAt m 8 (r.addr 19009) ∧ r.WordAt m 16 (l + 1).toUInt64 ∧
    r.WordAt m 24 (4656 + 1028 * (l + 1)).toUInt64 ∧ r.WordAt m 32 l.toUInt64 ∧
    r.WordAt m 40 (r.key l).leaf.toUInt64 ∧ r.WordAt m 48 (layerHeights.getD l 0).toUInt64 ∧
    r.WordAt m 400 r.idx ∧ r.WordAt m 408 (r.addr (5140 + 1028 * l)) ∧
    BytesAt m.dmem (r.off 424) (be32 (r.key l).leaf) ∧
    BytesAt m.dmem (r.off 432) (be32 l.toUInt32) ∧
    BytesAt m.dmem (r.off 440) (be64 (r.key l).tree)

/-- **At `b105`, chain 0 of layer `l < 3`**, the codeword `x` at `15936`: X1 `0`, X19 `136`,
X21, X25 the hashers' buffers, X27 `base + 19008`. -/
def AtChains (l : Nat) (x : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ x.length = 64 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .X1 0 ∧
    RegIs m .X19 136 ∧ RegIs m .X21 (r.off 19208) ∧ RegIs m .X25 (r.off 8840) ∧
    RegIs m .X27 (r.off 19008) ∧ BytesAt m.dmem (r.off 15936) x

/-- **At `b134`, layer `l < 3`'s chain ends `e`** at `20464`: X19, X21, X25, X27 as in the chains. -/
def AtWotsPk (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  l < 3 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .X19 136 ∧
    RegIs m .X21 (r.off 19208) ∧ RegIs m .X25 (r.off 8840) ∧ RegIs m .X27 (r.off 19008) ∧
    BytesAt m.dmem (r.off 20464) e.flatten ∧ e.flatten.length = 1024

end Run

/-! ## The callees and the regions -/

section
variable [NativeRustcArm.Host]

/-- **The callees' contracts.** -/
def Callees : Prop :=
  Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost ∧
    Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost ∧
    Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost ∧
    Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre FinalizePost ∧
    Spec (label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost

/-- **A region**: placed at `r.k`, given the callees' contracts and the run's precondition, from
directive `j` of the function in a state `P r` the machine inevitably reaches `Q r`. -/
def RegionSpec (P : Run → MachineData → Prop) (j : Nat) (Q : Run → MachineState → Prop) : Prop :=
  ∀ r : Run, Placed Sphincs.SphincsVerify.code r.k → Callees → r.Pre → ∀ m, P r m →
    Eventually (step1 NativeRustcArm.Host.exe) (Q r) ⟨m, NativeRustcArm.Host.addrOf (r.k + j)⟩

/-- The pc of the function's directive `j`. -/
def Run.pc (r : Run) (j : Nat) : Int64 := NativeRustcArm.Host.addrOf (r.k + j)

/-- Region 1a, the parse's head: from the entry to `b7`. -/
def ParseHeadSpec : Prop :=
  RegionSpec (fun r m ↦ m = r.m0) NativeRustcArm.Sphincs.SphincsVerify.b0Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ r.AtParse7 st.data

/-- Region 1b, the parse's tail: from `b7` to `b36`. -/
def ParseTailSpec : Prop :=
  RegionSpec Run.AtParse7 NativeRustcArm.Sphincs.SphincsVerify.b7Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b36Offset ∧ r.AtHMsg st.data

/-- Region 1, the parse: from the entry to `b36`. -/
def ParseSpec : Prop :=
  RegionSpec (fun r m ↦ m = r.m0) NativeRustcArm.Sphincs.SphincsVerify.b0Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b36Offset ∧ r.AtHMsg st.data

/-- Region 2, the digest: from `b36` to `b50`. -/
def DigestSpec : Prop :=
  RegionSpec Run.AtHMsg NativeRustcArm.Sphincs.SphincsVerify.b36Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b50Offset ∧ r.AtFors st.data

/-- Region 3, the FORS trees: from `b50` to `b85`. -/
def ForsSpec : Prop :=
  RegionSpec Run.AtFors NativeRustcArm.Sphincs.SphincsVerify.b50Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset ∧ r.AtForsKey st.data

/-- Region 4, the FORS key: from `b85` to `b92`, layer 0. -/
def ForsKeySpec : Prop :=
  RegionSpec Run.AtForsKey NativeRustcArm.Sphincs.SphincsVerify.b85Offset
    fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset ∧ r.AtLayer 0 r.forsPk st.data

/-- Region 5a, a layer's encoding: from `b92` to `b105` with the codeword, or returned 0 without one. -/
def EncodeSpec : Prop :=
  ∀ l s, RegionSpec (fun r ↦ r.AtLayer l s) NativeRustcArm.Sphincs.SphincsVerify.b92Offset fun r st ↦
    (encode r.seed (r.key l) s (r.layerSig l).counter = none ∧ r.Done false st) ∨
      ∃ x, encode r.seed (r.key l) s (r.layerSig l).counter = some x ∧
        st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset ∧ r.AtChains l x st.data

/-- Region 5b, a layer's chains: from `b105` to `b134`. -/
def ChainsSpec : Prop :=
  ∀ l x, RegionSpec (fun r ↦ r.AtChains l x) NativeRustcArm.Sphincs.SphincsVerify.b105Offset fun r st ↦
    st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data

/-- Region 5c, a layer's tree: from `b134` to the next layer at `b92`, or, after the last,
returned the comparison with `PK.root`. -/
def TreeSpec : Prop :=
  ∀ l e, RegionSpec (fun r ↦ r.AtWotsPk l e) NativeRustcArm.Sphincs.SphincsVerify.b134Offset fun r st ↦
    if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
    else st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data

end

end

end NativeRustcArm.SphincsVerifyProof
