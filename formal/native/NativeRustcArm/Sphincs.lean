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

/-- Address of the `LAYER_HEIGHTS` table in `.rodata`. -/
abbrev layerHeightsAddr [Labels] : BitVec 64 := (label NativeRustcArm.layerHeightsLabel).toBitVec

/-- Lowest address of the `stackSize`-byte stack frame below entry SP. -/
abbrev stackBottomAddr (m : MachineData) (stackSize : Nat) : BitVec 64 := stackBelow m stackSize

/-- Caller's 64-bit return PC from entry link register `X30`. -/
abbrev returnAddrOf (m : MachineData) : Int64 := retOf m

/-- AAPCS64 callee-saved registers (`X19`..`X29`) and `SP` are unchanged and mapped memory is preserved. -/
abbrev CalleeSavedAndMemKept (m m' : MachineData) : Prop := Saved m m'

/-- Byte ranges `[a, a + n)` and `[a', a' + n')` are disjoint. -/
abbrev Disjoint (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop := Apart a n a' n'

/-- Address `addr` lies in at least one `(base, byteLen)` region of `areas`. -/
abbrev InRegions (areas : List (BitVec 64 × Nat)) (addr : BitVec 64) : Prop := ReadRegions areas addr

/-- Non-wrapping read-only byte buffer at `addr`, disjoint from the entry stack span. -/
def ReadOnlyBuf (dmem : DataMem) (addr : BitVec 64) (bytes : List UInt8)
    (initState : MachineData) (stackSpan : Nat) : Prop :=
  BytesAt dmem addr bytes ∧ NoWrap addr bytes.length ∧
    Disjoint addr bytes.length (stackBottomAddr initState sphincsStackSize) stackSpan

end

public section

theorem sphincsStackSize_eq : sphincsStackSize = 22192 := rfl
theorem roundConstsSize_eq : roundConstsSize = 192 := by
  rw [show roundConstsSize = (Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC).length from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl
theorem layerHeightsBytes_length : layerHeightsBytes.length = layerHeightsSize := by decide

private theorem ReadOnlyBuf.restrict {d : DataMem} {addr : BitVec 64} {bytes : List UInt8}
    {initState : MachineData} {stackSpan : Nat}
    (h : ReadOnlyBuf d addr bytes initState stackSpan)
    {areas : List (BitVec 64 × Nat)} (ha : (addr, bytes.length) ∈ areas) :
    ReadOnlyBuf (restrictMemory d areas) addr bytes { initState with dmem := restrictMemory d areas } stackSpan :=
  ⟨h.1.restrict ha, h.2.1, h.2.2⟩

/-- **The callees' contracts** for `sphincs_verify` under a multi-section `ElfHost`. -/
theorem callees [ElfHost]
    {secMemcpy kMemcpy secMemset kMemset secKeccakF kKeccakF secUpdate kUpdate secFinalize kFinalize : Nat}
    (hpMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    (hpMemset : PlacedIn Common.Memset.code secMemset kMemset)
    (hpKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    (hpUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    (hpFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize) : Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec_elf hpMemcpy
  have hkf := keccakF_spec_elf hpKeccakF
  ⟨hmemcpy, Mem.Memset.memset_spec_elf hpMemset,
    Hasher.Update.update_spec_elf hpUpdate hmemcpy hkf,
    Hasher.Finalize.finalize_spec_elf hpFinalize hmemcpy hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct** (AArch64). -/
theorem verify_correct
    -- 1. Loaded program: a multi-section AArch64 `ElfHost` containing `sphincs_verify` and its
    --    five callees (`memcpy`, `memset`, `keccak_f`, `Hasher::update`, `Hasher::finalize`).
    [ElfHost]
    {secVerify kVerify secMemcpy kMemcpy secMemset kMemset secKeccakF kKeccakF secUpdate kUpdate secFinalize kFinalize : Nat}
    (hpVerify : PlacedIn Sphincs.SphincsVerify.code secVerify kVerify)
    (hpMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    (hpMemset : PlacedIn Common.Memset.code secMemset kMemset)
    (hpKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    (hpUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    (hpFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize)
    -- 2. Canonical byte inputs (32 B pk, 32 B msg, 7740 B sig).
    (pkBytes : Vector UInt8 pkSize)
    (msgBytes : Vector UInt8 msgSize)
    (sigBytes : Vector UInt8 sigSize)
    -- 3. Initial CPU state and ABI stack (16-byte aligned SP with `sphincsStackSize` bytes below SP;
    --    return address is in link register X30).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 4. Read-only program data (.rodata) and caller input buffers (X0, X1, X2),
    --    each present in memory, non-wrapping, and disjoint from the entry stack span.
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes
      initState sphincsStackSize)
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes
      initState sphincsStackSize)
    (hPkBuf : ReadOnlyBuf initState.dmem initState.regs.X0.toBitVec pkBytes.toList
      initState sphincsStackSize)
    (hMsgBuf : ReadOnlyBuf initState.dmem initState.regs.X1.toBitVec msgBytes.toList
      initState sphincsStackSize)
    (hSigBuf : ReadOnlyBuf initState.dmem initState.regs.X2.toBitVec sigBytes.toList
      initState sphincsStackSize) :
    -- Statement: starting at `sphincs_verify`'s entry in `initState`, every execution under
    -- `ElfHost.exe` terminates in finitely many steps (`Eventually (elfStep1 ElfHost.exe)`) at a
    -- `finalState` satisfying:
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        -- A. Control-flow return:
        --    PC reaches the caller's link register (X30) from entry.
        finalState.pc = returnAddrOf initState ∧
        -- B. Functional correctness (return value in X0):
        --    X0 is 1 iff the mathematical leanSPHINCS verifier accepts the decoded raw bytes.
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
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
  have hPkLen : pkBytes.toList.length = pkSize := pkBytes.length_toList
  have hMsgLen : msgBytes.toList.length = msgSize := msgBytes.length_toList
  have hSigLen : sigBytes.toList.length = sigSize := sigBytes.length_toList
  rw [← NativeRustc.Sphincs.verify_decode_bytes pkBytes.toList msgBytes.toList sigBytes.toList
    hPkLen hMsgLen hSigLen]
  have hl := hpVerify.label NativeRustcArm.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcArm.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
  have hrc : RcAt initState sphincsStack := by
    obtain ⟨hb, hw, ha⟩ := hRoundConsts
    exact ⟨hb, by simpa [roundConstsSize_eq] using hw, by simpa [roundConstsSize_eq] using ha⟩
  obtain ⟨hlhb, hlhw, hlha⟩ := hLayerHeights
  obtain ⟨hpkb, hpkw, hpka⟩ := hPkBuf
  obtain ⟨hmsgb, hmsgw, hmsga⟩ := hMsgBuf
  obtain ⟨hsigb, hsigw, hsiga⟩ := hSigBuf
  rw [layerHeightsBytes_length] at hlhw hlha
  rw [hPkLen] at hpkw hpka
  rw [hMsgLen] at hmsgw hmsga
  rw [hSigLen] at hsigw hsiga
  exact run_correct
    ⟨initState, pkBytes.toList, msgBytes.toList, sigBytes.toList, hPkLen, hMsgLen, hSigLen,
      secVerify, kVerify⟩
    hpVerify (callees hpMemcpy hpMemset hpKeccakF hpUpdate hpFinalize)
    ⟨hStackOk, hrc, hlhb, hlhw, hlha, hpkb, hpkw, hpka, hmsgb, hmsgw, hmsga, hsigb, hsigw, hsiga⟩
    (parseSpec_of Parse.parseHead_spec ParseTail.parseTail_spec) digest_spec fors_spec forsKey_spec
    encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined
    -- 1. Loaded program: a multi-section AArch64 `ElfHost` containing `sphincs_verify` and its
    --    five callees (`memcpy`, `memset`, `keccak_f`, `Hasher::update`, `Hasher::finalize`).
    [ElfHost]
    {secVerify kVerify secMemcpy kMemcpy secMemset kMemset secKeccakF kKeccakF secUpdate kUpdate secFinalize kFinalize : Nat}
    (hpVerify : PlacedIn Sphincs.SphincsVerify.code secVerify kVerify)
    (hpMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    (hpMemset : PlacedIn Common.Memset.code secMemset kMemset)
    (hpKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    (hpUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    (hpFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize)
    -- 2. Canonical byte inputs (32 B pk, 32 B msg, 7740 B sig).
    (pkBytes : Vector UInt8 pkSize)
    (msgBytes : Vector UInt8 msgSize)
    (sigBytes : Vector UInt8 sigSize)
    -- 3. Initial CPU state and ABI stack (16-byte aligned SP with `sphincsStackSize` bytes below SP;
    --    return address is in link register X30).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 4. Read-only program data (.rodata) and caller input buffers (X0, X1, X2),
    --    each present in memory, non-wrapping, and disjoint from the entry stack span.
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes
      initState sphincsStackSize)
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes
      initState sphincsStackSize)
    (hPkBuf : ReadOnlyBuf initState.dmem initState.regs.X0.toBitVec pkBytes.toList
      initState sphincsStackSize)
    (hMsgBuf : ReadOnlyBuf initState.dmem initState.regs.X1.toBitVec msgBytes.toList
      initState sphincsStackSize)
    (hSigBuf : ReadOnlyBuf initState.dmem initState.regs.X2.toBitVec sigBytes.toList
      initState sphincsStackSize) :
    -- Allowed data-memory footprint of `sphincs_verify` (everything else will be unmapped):
    let allowedRegions := [
      -- Stack frame below entry SP (return address lives in X30, not on the stack).
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize),
      -- Caller input buffers (pk: 32 B, msg: 32 B, sig: 7740 B).
      (initState.regs.X0.toBitVec, pkSize), (initState.regs.X1.toBitVec, msgSize),
      (initState.regs.X2.toBitVec, sigSize),
      -- Read-only program tables (.rodata: Keccak round constants and LAYER_HEIGHTS).
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize)]
    -- Restricted entry state: identical registers, data memory masked down to `allowedRegions`.
    let confinedState := { initState with dmem := restrictMemory initState.dmem allowedRegions }
    -- Statement:
    -- 1. Read/write confinement setup: every address outside `allowedRegions` is unmapped (`none`),
    --    so any out-of-footprint load or store would fail Kraken's memory semantics.
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    -- 2. Execution under the restricted memory still terminates in finitely many steps and
    --    satisfies the full correctness, framing, and ABI postcondition:
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        -- A. Control-flow return (PC reaches entry X30).
        finalState.pc = returnAddrOf confinedState ∧
        -- B. Functional correctness (return value in X0).
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
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
      (layerHeightsAddr, layerHeightsSize)]
  let confinedState : MachineData := { initState with dmem := restrictMemory initState.dmem allowedRegions }
  have hs : StackOk confinedState sphincsStackSize :=
    ⟨hStackOk.1, hStackOk.2.1, hStackOk.2.2.restrict (by simp [allowedRegions, stackBelow])⟩
  refine ⟨fun addr hOut => restrictMemory_outside initState.dmem hOut, ?_⟩
  exact verify_correct hpVerify hpMemcpy hpMemset hpKeccakF hpUpdate hpFinalize
    pkBytes msgBytes sigBytes confinedState hs
    (hRoundConsts.restrict (by simp [allowedRegions]))
    (hLayerHeights.restrict (by simp [allowedRegions, layerHeightsBytes_length]))
    (hPkBuf.restrict (by simp [allowedRegions, pkBytes.length_toList]))
    (hMsgBuf.restrict (by simp [allowedRegions, msgBytes.length_toList]))
    (hSigBuf.restrict (by simp [allowedRegions, sigBytes.length_toList]))

end

end NativeRustcArm.SphincsVerifier
