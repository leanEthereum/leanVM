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

rustc compiles `rustc/sphincs.rs`'s `sphincs_verify` (blocks `b0` to `b192` of
`NativeRustcArm.Sphincs.SphincsVerify`, assembly `rustc/asm/signatures-aarch64.s`)
with all of `lean_sphincs` inlined, `Hasher::update`'s loop and `Hasher::finalize` included where
the hasher is a local; it calls `memcpy`, `memset`, `Hasher::update`, `Hasher::finalize` and
`keccak_f` only.

## The frame

The prologue stores X29, X30, X28 ... X19 at `SP₀ - 96` (`savedBytes`), probes and allocates
`7 · 4096 + 608` more bytes: the frame is the `frameSize = 29376` bytes from `base = SP₀ - 29376`,
SP stays `base`, X29 is `base + 29280`. The callees use `finalizeStack` bytes below `base`, the most
of the three (`sphincsStack`). Offsets from `base`:

- `0 .. 48`: the layer loop's spills (`[sp]` = `base + 26769`, `+8` the next layer, `+16` the next
  layer's offset `4656 + 1028 (l + 1)`, `+24` the layer, `+32` the key's leaf, `+40` the height);
  `48 .. 408` the codeword's spills (`b111`); `376` the paths' address `base + 12468`, `384` the
  index, `392` the current layer's address `base + 12900 + 1028 l`, `400 .. 432` the FORS and layer
  loops' spills (`408` the key pair word, `416` the layer word, `424` the tree word).
- `432`: the message (32 bytes, words 4 .. 7). `468`: the signature's raw bytes `sigBytes w`
  (7740). `8208`: the public key's bytes `pkBytes w` (`PK.seed` at `8208`, `PK.root` at `8224`).
- `8244`: the parsed signature in rustc's layout (`sigMem`, 7740 bytes): the 24 FORS openings
  (path, then secret: 176 each), the 26 path nodes (`12468`), the randomizer (`12884`), the three
  layers (64 chain values then the counter, 1028 each, from `12900`).
- `15984 .. 16400`: scratch of the parse (the paths being assembled). `16400`: hasher A (344
  bytes: state, buffer at `16600`, `buf_len` at `16736`), also the digest's 24 leaves (`b57`).
- `20624 .. 26768`: scratch: copies of the layers' chain values during the parse; the hash
  inputs (`21648`: an address and two children, `23696`: the codeword's digits, `24720`: `h_msg`'s
  64 bytes, then an address), `25744` the index and `25752` the 24 leaves.
- `26768`: hasher B (buffer `26968`, `buf_len` `27104`), also the codeword's digits.
  `27792`: `signed`, the current layer's message (16 bytes); `27824`: the 24 FORS roots;
  `28224`: the 64 chain ends. `27808`: a 16-byte scratch value (the randomizer;
  `15984`: the chain's current value). `29280`: the saved registers.

## The regions (block, assembly line, what the Rust code does)

1. **Parse** `b0 .. b44` (lines 82 .. 634): prologue and stack probe loop (`b1`, 7 turns);
   `memset` of the raw signature; the words' bytes: loops `b4` (words 8 .. 535), `b6`, `b8`,
   `b10` (the layers' words, the counters byte-reversed by `rev`); `from_bytes`: loop `b12 .. b15`
   (24 openings, three `memcpy`s each), `memset` of the paths, per layer a 1024-byte copy loop
   (`b18`, `b26`, `b34`) and five 1024-byte `memcpy`s, then the parsed signature assembled at
   `8244` (`b40 .. b44`). Exit: `AtHMsg` at `b45`.
2. **Digest** `b45 .. b58` (lines 635 .. 810): `h_msg`: a new hasher, `update` with `R`,
   `PK.seed`, `PK.root`, `M`, cloned (`memcpy` 344) and updated with `BE32(i)` and finalized, twice;
   `digest_fields`: loop `b57` (24 turns: a FORS leaf of 10 bits), the index from bytes 30 .. 33
   (`b58`), the leaves copied to `25752`. Exit: `AtFors` at `b59`.
3. **FORS** `b59 .. b93` (lines 811 .. 1341): tree `c` (outer loop `b60 .. b93`, X19): its leaf
   `th` with calls (`b60 .. b65`), then 10 nodes (inner loop `b67 .. b92`, X28), each an inlined
   `th`: `memset` of hasher A, `PK.seed` buffered (`b68 .. b70`), the address by the inlined
   `update` loop `b71 .. b78` (`memcpy` into the buffer, `keccak_f` on a full buffer, slice checks
   panicking at `b183`), the clone (`b79`), the children by the loop `b80 .. b87` (on hasher B),
   the inlined `finalize` (`b88 .. b91`: the state copied, the final block padded and absorbed,
   `keccak_f`, 16 bytes read). The roots go to `27824`. Exit: `AtForsKey` at `b94`.
4. **FORS key** `b94 .. b100` (lines 1342 .. 1404): `th` of the roots with calls; `signed` at
   `27792`. Exit: `AtLayer 0` at `b101`.
5. **Layer** `l` (loop `b101 .. b181`, X10):
   - **Encode** `b101 .. b112`, `b187` (lines 1405 .. 1803, 2878): the key from the index and
     `LAYER_HEIGHTS` (the rodata table `NativeRustcArm.layerHeightsLabel`), the encoder (`th` prefix with calls, cloned,
     the counter), `finalize`; loop `b110` (16 turns, 4 digits each) and the sum (`b111`); a sum
     other than 128 returns 0 (`b187`, `b188`). Exit: `AtChains l x` at `b114` (chain 0).
   - **Chains** `b113 .. b142` (lines 1804 .. 2255): chain `i` (loop on X28 through `b114`,
     `b113`), its steps from its digit to 3 (loop `b116 .. b141`, X19), each an inlined `th` like
     a FORS node's (`b116 .. b140`, the value 16 bytes); the ends go to `28224`. Exit:
     `AtWotsPk l ends` at `b143`.
   - **Tree** `b143 .. b182` (lines 2256 .. 2853): the one-time leaf (`th` of the ends, with
     calls), the path's slice check (`b149`, `b150`, panic `b192`), the height-0 case (`b151`,
     `b180`, unreachable), the fold (loop `b153 .. b178`, X19), each node an inlined `th`; `b181`
     back to `b101` for the next layer, or `b182`: the comparison with `PK.root`. Exit: `AtLayer
     (l + 1)` at `b101` or `Done` (through the epilogue `b188`).
6. **Panics** `b183 .. b186`, `b189 .. b192`: `slice_index_fail`, unreachable.

Each region's statement is a `RegionSpec` below; `NativeRustcArm.SphincsVerify.Compose` composes
them (its hypotheses), the regions' modules prove them.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-! ## The frame -/

/-- The frame: the 96 bytes of saved registers and `7 · 4096 + 608`. -/
def frameSize : Nat := 96 + 7 * 4096 + 608

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

/-- A run of `sphincs_verify`: the machine at its entry, the input words, the function's
placement. -/
structure Run where
  m0 : MachineData
  w : Nat → UInt64
  k : Nat

namespace Run

variable (r : Run)

/-- The frame's base, SP inside the function. -/
def base : BitVec 64 := r.m0.regs.SP.toBitVec - BitVec.ofNat 64 frameSize

/-- The frame's byte `off`. -/
def off (off : Nat) : BitVec 64 := r.base + BitVec.ofNat 64 off

/-- The stack area: the frame and the callees' stack below it. -/
def StackArea : BitVec 64 → Prop := InRange (stackBelow r.m0 sphincsStack) sphincsStack

/-- The input's address: the context's byte 1024. -/
def input : BitVec 64 := r.m0.regs.X0.toBitVec + BitVec.ofNat 64 1024

/-- The public key. -/
def pk : PublicKey := PublicKey.fromBytes (pkBytes r.w)
/-- The message. -/
def msg : List UInt8 := messageBytes r.w
/-- The parsed signature. -/
def sig : Signature := Signature.fromBytes (sigBytes r.w)
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

/-- **The precondition**: the stack, the round constants, `LAYER_HEIGHTS` and the 977 input words
in place, apart from the stack. -/
def Pre [Labels] : Prop :=
  StackOk r.m0 sphincsStack ∧ RcAt r.m0 sphincsStack ∧
    BytesAt r.m0.dmem (label NativeRustcArm.layerHeightsLabel).toBitVec lhBytes ∧ NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec 24 ∧
    Apart (label NativeRustcArm.layerHeightsLabel).toBitVec 24 (stackBelow r.m0 sphincsStack) sphincsStack ∧
    BytesAt r.m0.dmem r.input (wordsBytes ((List.range 977).map r.w)) ∧ NoWrap r.input (8 * 977) ∧
    Apart r.input (8 * 977) (stackBelow r.m0 sphincsStack) sphincsStack

/-- **The frame's invariant**: SP and X29, the saved registers in place, no byte changed outside
the stack area, every mapped byte still mapped. -/
def Frame (m : MachineData) : Prop :=
  m.regs.SP.toBitVec = r.base ∧ (m.regs.getXReg .X29).toBitVec = r.off 29280 ∧
    BytesAt m.dmem (r.off 29280) (savedBytes r.m0) ∧ SameOutside r.m0.dmem m.dmem r.StackArea ∧
    Kept r.m0.dmem m.dmem

/-- Register `x` holds `v`. -/
def RegIs (m : MachineData) (x : XReg) (v : BitVec 64) : Prop := (m.regs.getXReg x).toBitVec = v

/-- The frame's 8 bytes at `off` hold `v`. -/
def WordAt (m : MachineData) (off : Nat) (v : UInt64) : Prop := BytesAt m.dmem (r.off off) (wordBytes v)

/-- The frame's address `a`, as a word. -/
def addr (off : Nat) : UInt64 := UInt64.ofBitVec (r.off off)

/-- The key, the message and the parsed signature in the frame. -/
def Inputs (m : MachineData) : Prop :=
  BytesAt m.dmem (r.off 8208) (pkBytes r.w) ∧ BytesAt m.dmem (r.off 8244) (sigMem r.sig) ∧
    r.WordAt m 376 (r.addr 12468)

/-- **Done**: returned to the caller with `v` in X0, no byte changed outside the stack area, its
registers and memory kept. -/
def Done (v : Bool) (st : MachineState) : Prop :=
  st.pc = retOf r.m0 ∧ st.data.regs.X0 = (if v then 1 else 0) ∧
    SameOutside r.m0.dmem st.data.dmem r.StackArea ∧ Saved r.m0 st.data

/-! ## The states between regions -/

/-- **At `b16`** (the parse, after the FORS openings' loop): the message, the raw signature, the
key, the openings in rustc's layout at `16400`, the randomizer at `27808`; X19 the key,
X20 the raw signature. -/
def AtParse16 (m : MachineData) : Prop :=
  r.Frame m ∧ BytesAt m.dmem (r.off 432) r.msg ∧ BytesAt m.dmem (r.off 468) (sigBytes r.w) ∧
    BytesAt m.dmem (r.off 8208) (pkBytes r.w) ∧
    BytesAt m.dmem (r.off 16400) ((r.sig.fors.map openingMem).flatten) ∧
    BytesAt m.dmem (r.off 27808) r.sig.randomizer ∧ RegIs m .X19 (r.off 8208) ∧
    RegIs m .X20 (r.off 468)

/-- **At `b45`** (after the parse): X19 the key, X23 the parsed signature, X24 `4640`, X21
`base + 24720` (where `h_msg`'s bytes go); the message, the key, the signature in place; `392` the
first layer's address. -/
def AtHMsg (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .X19 (r.off 8208) ∧ RegIs m .X23 (r.off 8244) ∧
    RegIs m .X24 4640 ∧ RegIs m .X21 (r.off 24720) ∧ BytesAt m.dmem (r.off 432) r.msg ∧
    r.WordAt m 392 (r.addr 12900)

/-- **At `b59`** (after the digest): X22 the index, X20 its low byte, X24 the leaves' copy, X21
hasher A, X23 `base + 21648`; the 24 leaves at `25752`. -/
def AtFors (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ RegIs m .X22 r.idx.toBitVec ∧
    RegIs m .X20 (r.idx &&& 255).toBitVec ∧ RegIs m .X24 (r.off 25752) ∧
    RegIs m .X21 (r.off 16400) ∧ RegIs m .X23 (r.off 21648) ∧
    BytesAt m.dmem (r.off 25752) (wordsBytes (r.leaves.map Nat.toUInt64)) ∧
    r.WordAt m 392 (r.addr 12900)

/-- **At `b94`** (after the FORS trees): X27 the tree's word, W26 the key pair's, X23
`base + 21648`; the 24 roots at `27824`; `384` the index. -/
def AtForsKey (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ wordBytes (m.regs.getXReg .X27) = be64 (r.key 0).tree ∧
    wordBytes (m.regs.getXReg .X26) = be32 (r.key 0).leaf ++ [0, 0, 0, 0] ∧
    RegIs m .X23 (r.off 21648) ∧
    BytesAt m.dmem (r.off 27824) ((List.range 24).map r.forsRoot).flatten ∧
    r.WordAt m 384 r.idx ∧ r.WordAt m 392 (r.addr 12900)

/-- **At `b101`, layer `l < 3`** with message `s`: the loop's registers (X10 the layer, X8
`LAYER_HEIGHTS`, X11 and X12 the layer's address and offset, X13 `8`, X22 `16`, W14 the encoding
type's word, X20 `base + 21648`, X26 `136`, X21 and X25 the hashers' buffers, X23 the digits' end
`base + 26769`), `s` at `27792`, the spills `0` and `384`. -/
def AtLayer [Labels] (l : Nat) (s : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.Inputs m ∧ RegIs m .X10 (BitVec.ofNat 64 l) ∧
    RegIs m .X8 (label NativeRustcArm.layerHeightsLabel).toBitVec ∧ RegIs m .X11 (r.off (12900 + 1028 * l)) ∧
    RegIs m .X12 (BitVec.ofNat 64 (4656 + 1028 * l)) ∧ RegIs m .X13 8 ∧ RegIs m .X22 16 ∧
    RegIs m .X14 0x07000000 ∧ RegIs m .X20 (r.off 21648) ∧ RegIs m .X26 136 ∧
    RegIs m .X21 (r.off 26968) ∧ RegIs m .X23 (r.off 26769) ∧ RegIs m .X25 (r.off 16600) ∧
    BytesAt m.dmem (r.off 27792) s ∧ r.WordAt m 0 (r.addr 26769) ∧ r.WordAt m 384 r.idx

/-- The layer loop's spills a layer's chains and tree read: the next layer, its offset, the layer,
the key's leaf, the height, the index, the layer's address, the key pair's, the layer's and the
tree's words. -/
def LayerSpills (l : Nat) (m : MachineData) : Prop :=
  r.WordAt m 0 (r.addr 26769) ∧ r.WordAt m 8 (l + 1).toUInt64 ∧
    r.WordAt m 16 (4656 + 1028 * (l + 1)).toUInt64 ∧ r.WordAt m 24 l.toUInt64 ∧
    r.WordAt m 32 (r.key l).leaf.toUInt64 ∧ r.WordAt m 40 (layerHeights.getD l 0).toUInt64 ∧
    r.WordAt m 384 r.idx ∧ r.WordAt m 392 (r.addr (12900 + 1028 * l)) ∧
    BytesAt m.dmem (r.off 408) (be32 (r.key l).leaf) ∧ BytesAt m.dmem (r.off 416) (be32 l.toUInt32) ∧
    BytesAt m.dmem (r.off 424) (be64 (r.key l).tree)

/-- **At `b114`, chain 0 of layer `l < 3`**, the codeword `x` at `23696`: X0 `0`, X8 the layer's
chain values, X21, X25 the hashers' buffers, X26 `136`. -/
def AtChains (l : Nat) (x : List UInt8) (m : MachineData) : Prop :=
  l < 3 ∧ x.length = 64 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .X0 0 ∧
    RegIs m .X8 (r.off (12900 + 1028 * l)) ∧ RegIs m .X21 (r.off 26968) ∧
    RegIs m .X25 (r.off 16600) ∧ RegIs m .X26 136 ∧ BytesAt m.dmem (r.off 23696) x

/-- **At `b143`, layer `l < 3`'s chain ends `e`** at `28224`: X21, X25, X26 as in the chains. -/
def AtWotsPk (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  l < 3 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .X21 (r.off 26968) ∧
    RegIs m .X25 (r.off 16600) ∧ RegIs m .X26 136 ∧ BytesAt m.dmem (r.off 28224) e.flatten ∧
    e.flatten.length = 1024

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
  ∀ r : Run, Placed Sphincs.SphincsVerify.code r.k → Callees → r.Pre → ∀ m, P r m →
    Eventually (step1 NativeRustcArm.Host.exe) (Q r) ⟨m, NativeRustcArm.Host.addrOf (r.k + j)⟩

/-- The pc of the function's directive `j`. -/
def Run.pc (r : Run) (j : Nat) : Int64 := NativeRustcArm.Host.addrOf (r.k + j)

/-- Region 1a, the parse's head: from the entry to `b16` (directive 215). -/
def ParseHeadSpec : Prop :=
  RegionSpec (fun r m ↦ m = r.m0) NativeRustcArm.Sphincs.SphincsVerify.b0Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b16Offset ∧ r.AtParse16 st.data

/-- Region 1b, the parse's tail: from `b16` to `b45` (directive 536). -/
def ParseTailSpec : Prop :=
  RegionSpec Run.AtParse16 NativeRustcArm.Sphincs.SphincsVerify.b16Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b45Offset ∧ r.AtHMsg st.data

/-- Region 1, the parse: from the entry to `b45` (directive 536). -/
def ParseSpec : Prop :=
  RegionSpec (fun r m ↦ m = r.m0) NativeRustcArm.Sphincs.SphincsVerify.b0Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b45Offset ∧ r.AtHMsg st.data

/-- Region 2, the digest: from `b45` to `b59` (directive 712). -/
def DigestSpec : Prop :=
  RegionSpec Run.AtHMsg NativeRustcArm.Sphincs.SphincsVerify.b45Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b59Offset ∧ r.AtFors st.data

/-- Region 3, the FORS trees: from `b59` to `b94` (directive 1243). -/
def ForsSpec : Prop :=
  RegionSpec Run.AtFors NativeRustcArm.Sphincs.SphincsVerify.b59Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b94Offset ∧ r.AtForsKey st.data

/-- Region 4, the FORS key: from `b94` to `b101` (directive 1306), layer 0. -/
def ForsKeySpec : Prop :=
  RegionSpec Run.AtForsKey NativeRustcArm.Sphincs.SphincsVerify.b94Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b101Offset ∧ r.AtLayer 0 r.forsPk st.data

/-- Region 5a, a layer's encoding: from `b101` to `b114` (directive 1715) with the codeword, or
returned 0 without one. -/
def EncodeSpec : Prop :=
  ∀ l s, RegionSpec (fun r ↦ r.AtLayer l s) NativeRustcArm.Sphincs.SphincsVerify.b101Offset fun r st ↦
    (encode r.seed (r.key l) s (r.layerSig l).counter = none ∧ r.Done false st) ∨
      ∃ x, encode r.seed (r.key l) s (r.layerSig l).counter = some x ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset ∧
        r.AtChains l x st.data

/-- Region 5b, a layer's chains: from `b114` to `b143` (directive 2157). -/
def ChainsSpec : Prop :=
  ∀ l x, RegionSpec (fun r ↦ r.AtChains l x) NativeRustcArm.Sphincs.SphincsVerify.b114Offset fun r st ↦
    st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data

/-- Region 5c, a layer's tree: from `b143` to the next layer at `b101`, or, after the last,
returned the comparison with `PK.root`. -/
def TreeSpec : Prop :=
  ∀ l e, RegionSpec (fun r ↦ r.AtWotsPk l e) NativeRustcArm.Sphincs.SphincsVerify.b143Offset fun r st ↦
    if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
    else st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b101Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data

end

end

end NativeRustcArm.SphincsVerifyProof
