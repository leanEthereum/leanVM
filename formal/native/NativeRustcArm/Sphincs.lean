module

public import NativeRustcArm.Rodata.Names
public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.End
public import NativeRustcArm.SphincsVerify.Placed
public import NativeRustcArm.SphincsVerify.Digest.Spec
public import NativeRustcArm.SphincsVerify.Digest.ForsKeySpec
public import NativeRustcArm.SphincsVerify.Encode.Spec
public import NativeRustcArm.SphincsVerify.Chains.Spec
public import NativeRustcArm.SphincsVerify.Tree.Spec
public import NativeRustcArm.SphincsVerify.Parse.Head
public import NativeRustcArm.SphincsVerify.ParseTail.Spec
public import NativeRustcArm.SphincsVerify.Fors.Region
public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset
public import NativeRustcArm.KeccakF.Spec
public import NativeRustcArm.Hasher.Update
public import NativeRustcArm.Hasher.Finalize
public import NativeRustcArm.Restrict

/-!
# The rustc-compiled leanSPHINCS verifier on AArch64 is correct

`NativeRustcArm.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry on raw
byte buffers `pk` (32 bytes at X0), `msg` (32 bytes at X1) and `sig` (7740 bytes at X2), with its
ABI stack, round constants and `LAYER_HEIGHTS` in place, the machine returns
`Sphincs.verifyWithKeccak` of the decoded input in X0 and preserves its callee-saved registers, SP
and every byte outside its stack. `verify_decode_bytes` connects the byte model to that Statement
specification for every input. `verify_confined` removes every data-memory byte outside the stated
regions.

`callees`: the callees' contracts for this program; the regions' statements are the regions'
theorems (`NativeRustcArm.SphincsVerify.*`), composed by `run_correct`.
-/

namespace NativeRustcArm.SphincsVerifier

open NativeRustc NativeRustc.Keccak NativeRustcArm.SphincsVerifyProof Native.Keccak

@[expose] public section

/-! ## Statement vocabulary and byte sizes -/

/-- Canonical byte length of a leanSPHINCS public key (`PK.seed || PK.root`). -/
abbrev pkSize : Nat := 32

/-- Canonical byte length of a leanSPHINCS message. -/
abbrev msgSize : Nat := 32

/-- Canonical byte length of a leanSPHINCS signature. -/
abbrev sigSize : Nat := 7740

/-- Byte length of the three-entry `LAYER_HEIGHTS` table (`[8, 8, 10]` as 64-bit words). -/
abbrev layerHeightsSize : Nat := 24

/-- Byte length of the 24 Keccak-f[1600] round constants (192 bytes). -/
abbrev roundConstsSize : Nat := rcBytes.length

/-- Total stack bytes below entry SP used by `sphincs_verify` and its callees (22,192 bytes). -/
abbrev sphincsStackSize : Nat := sphincsStack

/-- The 24 bytes of `LAYER_HEIGHTS` in `.rodata`. -/
abbrev layerHeightsBytes : List UInt8 := lhBytes

/-- The 192 bytes of Keccak round constants in `.rodata`. -/
abbrev roundConstsBytes : List UInt8 := rcBytes

/-- Address of the Keccak round constants table in `.rodata`. -/
abbrev roundConstsAddr [Labels] : BitVec 64 := rcAddr

/-- Lowest address of the `stackSize`-byte stack frame below entry SP. -/
abbrev stackBottomAddr (m : MachineData) (stackSize : Nat) : BitVec 64 := stackBelow m stackSize

/-- Caller's 64-bit return PC from entry link register `X30`. -/
abbrev returnAddrOf (m : MachineData) : Int64 := retOf m

/-- Keccak round constants sit at `roundConstsAddr`, do not wrap, and are disjoint from the stack. -/
abbrev RoundConstsOk [Labels] (m : MachineData) (stackSize : Nat) : Prop := RcAt m stackSize

/-- AAPCS64 callee-saved registers (`X19`..`X29`) and `SP` are unchanged and mapped memory is preserved. -/
abbrev CalleeSavedAndMemKept (m m' : MachineData) : Prop := Saved m m'

/-- Byte ranges `[a, a + n)` and `[a', a' + n')` are disjoint. -/
abbrev Disjoint (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop := Apart a n a' n'

/-- Address `addr` lies in at least one `(base, byteLen)` region of `areas`. -/
abbrev InRegions (areas : List (BitVec 64 × Nat)) (addr : BitVec 64) : Prop := ReadRegions areas addr

end

public section

theorem sphincsStackSize_eq : sphincsStackSize = 22192 := rfl
theorem roundConstsSize_eq : roundConstsSize = 192 := by
  rw [show roundConstsSize = (Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC).length from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl
theorem layerHeightsBytes_length : layerHeightsBytes.length = layerHeightsSize := by decide

-- Loaded program: an abstract Kraken host whose instruction stream is the ingested
-- `sphincs_verify` bundle (`sphincs_verify`, `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
-- `Hasher::finalize`, and rodata).
variable [NativeRustcArm.Host] (hHostProg : NativeRustcArm.Host.prog = Sphincs.code)
include hHostProg

/-- **The callees' contracts** in `sphincs_verify`'s program. -/
theorem callees : Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hHostProg)
  have hkf := keccakF_spec (placed_keccakF hHostProg)
  ⟨hmemcpy, Mem.Memset.memset_spec (placed_memset hHostProg),
    Hasher.Update.update_spec (placed_update hHostProg) hmemcpy hkf,
    Hasher.Finalize.finalize_spec (placed_finalize hHostProg) hmemcpy hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct** (AArch64). -/
theorem verify_correct
    -- 1. Logical byte inputs and their fixed canonical lengths.
    (pkBytes msgBytes sigBytes : List UInt8)
    (hPkLen : pkBytes.length = pkSize)
    (hMsgLen : msgBytes.length = msgSize)
    (hSigLen : sigBytes.length = sigSize)
    -- 2. Initial CPU state and ABI stack (16-byte aligned SP with `sphincsStackSize` bytes below SP;
    --    return address is in X30).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 3. Read-only program data (.rodata): Keccak round constants and LAYER_HEIGHTS table,
    --    in memory, non-wrapping, and disjoint from the stack region.
    (hRoundConsts : RoundConstsOk initState sphincsStackSize)
    (hLayerHeightsBytes : BytesAt initState.dmem
      (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsBytes)
    (hLayerHeightsNoWrap : NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsSize)
    (hLayerHeightsDisjointStack : Disjoint (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    -- 4. Caller input buffers in memory, pointed to by AAPCS64 registers (X0, X1, X2),
    --    each non-wrapping and disjoint from the stack region.
    (hPkInMem : BytesAt initState.dmem initState.regs.X0.toBitVec pkBytes)
    (hPkNoWrap : NoWrap initState.regs.X0.toBitVec pkSize)
    (hPkDisjointStack : Disjoint initState.regs.X0.toBitVec pkSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    (hMsgInMem : BytesAt initState.dmem initState.regs.X1.toBitVec msgBytes)
    (hMsgNoWrap : NoWrap initState.regs.X1.toBitVec msgSize)
    (hMsgDisjointStack : Disjoint initState.regs.X1.toBitVec msgSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    (hSigInMem : BytesAt initState.dmem initState.regs.X2.toBitVec sigBytes)
    (hSigNoWrap : NoWrap initState.regs.X2.toBitVec sigSize)
    (hSigDisjointStack : Disjoint initState.regs.X2.toBitVec sigSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize) :
    -- Statement: starting at `sphincs_verify`'s entry in `initState`, every execution under
    -- `Host.exe` terminates in finitely many steps (`Eventually (step1 Host.exe)`) at a
    -- `finalState` satisfying:
    Eventually (step1 NativeRustcArm.Host.exe)
      (fun finalState ↦
        -- A. Control-flow return:
        --    PC reaches the caller's link register (X30) from entry.
        finalState.pc = returnAddrOf initState ∧
        -- B. Functional correctness (return value in X0):
        --    X0 is 1 iff the mathematical leanSPHINCS verifier accepts the decoded raw bytes.
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes)
          (Native.SphincsVerifier.decodeMsg msgBytes)
          (Native.SphincsVerifier.decodeSig sigBytes) then 1 else 0) ∧
        -- C. Memory framing (write confinement):
        --    Every byte outside the `sphincsStackSize` bytes below entry SP is unchanged
        --    (including input buffers and .rodata).
        SameOutside initState.dmem finalState.data.dmem
          (InRange (stackBottomAddr initState sphincsStackSize) sphincsStackSize) ∧
        -- D. Callee-saved ABI preservation:
        --    AAPCS64 callee-saved registers (X19..X29) and SP are unchanged, and no mapped
        --    data-memory byte becomes unmapped.
        CalleeSavedAndMemKept initState finalState.data)
      -- Entry machine state: registers and data memory `initState`, PC at `sphincs_verify`.
      ⟨initState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  rw [← NativeRustc.Sphincs.verify_decode_bytes pkBytes msgBytes sigBytes hPkLen hMsgLen hSigLen]
  have hp := placed hHostProg
  have hl := hp.label NativeRustcArm.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcArm.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
  exact run_correct
    ⟨initState, pkBytes, msgBytes, sigBytes, hPkLen, hMsgLen, hSigLen,
      NativeRustcArm.Sphincs.SphincsVerify.programOffset⟩
    hp (callees hHostProg)
    ⟨hStackOk, hRoundConsts, hLayerHeightsBytes, hLayerHeightsNoWrap, hLayerHeightsDisjointStack,
      hPkInMem, hPkNoWrap, hPkDisjointStack, hMsgInMem, hMsgNoWrap, hMsgDisjointStack,
      hSigInMem, hSigNoWrap, hSigDisjointStack⟩
    (parseSpec_of Parse.parseHead_spec ParseTail.parseTail_spec) digest_spec fors_spec forsKey_spec
    encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined
    -- 1. Logical byte inputs and their fixed canonical lengths.
    (pkBytes msgBytes sigBytes : List UInt8)
    (hPkLen : pkBytes.length = pkSize)
    (hMsgLen : msgBytes.length = msgSize)
    (hSigLen : sigBytes.length = sigSize)
    -- 2. Initial CPU state and ABI stack (16-byte aligned SP with `sphincsStackSize` bytes below SP;
    --    return address is in X30).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 3. Read-only program data (.rodata): Keccak round constants and LAYER_HEIGHTS table,
    --    in memory, non-wrapping, and disjoint from the stack region.
    (hRoundConsts : RoundConstsOk initState sphincsStackSize)
    (hLayerHeightsBytes : BytesAt initState.dmem
      (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsBytes)
    (hLayerHeightsNoWrap : NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsSize)
    (hLayerHeightsDisjointStack : Disjoint (label NativeRustcArm.layerHeightsLabel).toBitVec layerHeightsSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    -- 4. Caller input buffers in memory, pointed to by AAPCS64 registers (X0, X1, X2),
    --    each non-wrapping and disjoint from the stack region.
    (hPkInMem : BytesAt initState.dmem initState.regs.X0.toBitVec pkBytes)
    (hPkNoWrap : NoWrap initState.regs.X0.toBitVec pkSize)
    (hPkDisjointStack : Disjoint initState.regs.X0.toBitVec pkSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    (hMsgInMem : BytesAt initState.dmem initState.regs.X1.toBitVec msgBytes)
    (hMsgNoWrap : NoWrap initState.regs.X1.toBitVec msgSize)
    (hMsgDisjointStack : Disjoint initState.regs.X1.toBitVec msgSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize)
    (hSigInMem : BytesAt initState.dmem initState.regs.X2.toBitVec sigBytes)
    (hSigNoWrap : NoWrap initState.regs.X2.toBitVec sigSize)
    (hSigDisjointStack : Disjoint initState.regs.X2.toBitVec sigSize
      (stackBottomAddr initState sphincsStackSize) sphincsStackSize) :
    -- Allowed data-memory footprint of `sphincs_verify` (everything else will be unmapped):
    let allowedRegions := [
      -- Stack frame below entry SP (return address lives in X30, not on the stack).
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize),
      -- Caller input buffers (pk: 32 B, msg: 32 B, sig: 7740 B).
      (initState.regs.X0.toBitVec, pkSize), (initState.regs.X1.toBitVec, msgSize),
      (initState.regs.X2.toBitVec, sigSize),
      -- Read-only program tables (.rodata: Keccak round constants and LAYER_HEIGHTS).
      (roundConstsAddr, roundConstsSize),
      ((label NativeRustcArm.layerHeightsLabel).toBitVec, layerHeightsBytes.length)]
    -- Restricted entry state: identical registers, data memory masked down to `allowedRegions`.
    let confinedState := { initState with dmem := restrictMemory initState.dmem allowedRegions }
    -- Statement:
    -- 1. Read/write confinement setup: every address outside `allowedRegions` is unmapped (`none`),
    --    so any out-of-footprint load or store would fail Kraken's memory semantics.
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    -- 2. Execution under the restricted memory still terminates in finitely many steps and
    --    satisfies the full correctness, framing, and ABI postcondition:
    Eventually (step1 NativeRustcArm.Host.exe)
      (fun finalState ↦
        -- A. Control-flow return (PC reaches entry X30).
        finalState.pc = returnAddrOf confinedState ∧
        -- B. Functional correctness (return value in X0).
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes)
          (Native.SphincsVerifier.decodeMsg msgBytes)
          (Native.SphincsVerifier.decodeSig sigBytes) then 1 else 0) ∧
        -- C. Memory framing (no writes outside the `sphincsStackSize` bytes below entry SP).
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        -- D. Callee-saved ABI preservation (X19..X29, SP, and mapped memory kept).
        CalleeSavedAndMemKept confinedState finalState.data)
      -- Entry machine state: restricted memory `confinedState`, PC at `sphincs_verify`.
      ⟨confinedState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  dsimp only
  let allowedRegions := [(stackBottomAddr initState sphincsStackSize, sphincsStackSize),
      (initState.regs.X0.toBitVec, pkSize), (initState.regs.X1.toBitVec, msgSize),
      (initState.regs.X2.toBitVec, sigSize),
      (roundConstsAddr, roundConstsSize),
      ((label NativeRustcArm.layerHeightsLabel).toBitVec, layerHeightsBytes.length)]
  let confinedState : MachineData := { initState with dmem := restrictMemory initState.dmem allowedRegions }
  have hs : StackOk confinedState sphincsStackSize :=
    ⟨hStackOk.1, hStackOk.2.1, hStackOk.2.2.restrict (by simp [allowedRegions, stackBelow])⟩
  have hr : RoundConstsOk confinedState sphincsStackSize :=
    ⟨hRoundConsts.1.restrict (by simp [allowedRegions]), hRoundConsts.2⟩
  refine ⟨fun addr hOut => restrictMemory_outside initState.dmem hOut, ?_⟩
  exact verify_correct hHostProg pkBytes msgBytes sigBytes hPkLen hMsgLen hSigLen
    confinedState hs hr
    (hLayerHeightsBytes.restrict (by simp [allowedRegions])) hLayerHeightsNoWrap hLayerHeightsDisjointStack
    (hPkInMem.restrict (by simp [allowedRegions, hPkLen])) hPkNoWrap hPkDisjointStack
    (hMsgInMem.restrict (by simp [allowedRegions, hMsgLen])) hMsgNoWrap hMsgDisjointStack
    (hSigInMem.restrict (by simp [allowedRegions, hSigLen])) hSigNoWrap hSigDisjointStack

end

end NativeRustcArm.SphincsVerifier
