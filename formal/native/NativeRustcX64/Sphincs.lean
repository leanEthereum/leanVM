module

public import NativeRustcX64.Rodata.Names
public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.End
public import NativeRustcX64.SphincsVerify.Placed
public import NativeRustcX64.SphincsVerify.Parse.Spec
public import NativeRustcX64.SphincsVerify.Digest.Spec
public import NativeRustcX64.SphincsVerify.Fors.Spec
public import NativeRustcX64.SphincsVerify.Encode.Spec
public import NativeRustcX64.SphincsVerify.Chains.Spec
public import NativeRustcX64.SphincsVerify.Tree.Spec
public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset
public import NativeRustcX64.KeccakF.Spec
public import NativeRustcX64.Hasher.Update
public import NativeRustcX64.Hasher.Finalize
public import NativeRustcX64.Restrict

/-!
# The rustc-compiled leanSPHINCS verifier on x86-64 is correct

`NativeRustcX64.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry with
the raw public key (`rdi`, 32 bytes), message (`rsi`, 32 bytes), and signature (`rdx`, 7740 bytes),
with its ABI stack, round constants, `LAYER_HEIGHTS` and loader-provided GOT slots in place, the
machine returns `Sphincs.verifyWithKeccak` of the decoded inputs in RAX, RSP 8 above, preserving
its callee-saved registers and every byte outside its stack. `verify_decode_bytes` connects the
byte model to that Statement specification for every input. `verify_confined` removes every
data-memory byte outside the stated regions.

`callees`: the callees' contracts for this program; `verify_correct` composes them with the
regions' statements (`NativeRustcX64.SphincsVerify.End`).
-/

namespace NativeRustcX64.SphincsVerifier

open NativeRustc NativeRustc.Keccak NativeRustcX64.SphincsVerifyProof Native.Keccak LeanVM.Protocol.KeccakHash

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

/-- Byte length of the x86-64 return address pushed at entry RSP. -/
abbrev retAddrSize : Nat := 8

/-- Byte length of a single 64-bit GOT slot. -/
abbrev gotSlotSize : Nat := 8

/-- Total stack bytes below entry RSP used by `sphincs_verify` and its callees (22,304 bytes). -/
abbrev sphincsStackSize : Nat := sphincsStack

/-- The 24 bytes of `LAYER_HEIGHTS` in `.rodata`. -/
abbrev layerHeightsBytes : List UInt8 := lhBytes

/-- The 192 bytes of Keccak round constants in `.rodata`. -/
abbrev roundConstsBytes : List UInt8 := rcBytes

/-- Address of the Keccak round constants table in `.rodata`. -/
abbrev roundConstsAddr [Labels] : BitVec 64 := rcAddr

/-- Address of the `LAYER_HEIGHTS` table in `.rodata`. -/
abbrev layerHeightsAddr [Labels] : BitVec 64 := (label NativeRustcX64.layerHeightsLabel).toBitVec

/-- Lowest address of the `stackSize`-byte stack frame below entry RSP. -/
abbrev stackBottomAddr (m : MachineData) (stackSize : Nat) : BitVec 64 := stackBelow m stackSize

/-- GOT slots for `symbols` hold their target addresses, do not wrap, are pairwise disjoint,
and are disjoint from the entry stack span (no disjointness from read-only inputs or `.rodata` needed). -/
abbrev GotSlotsOk [Labels] (m : MachineData) (stackSize : Nat)
    (symbols : List Label) : Prop :=
  GotAt m stackSize [] symbols

/-- System V callee-saved registers (`rbx`, `rbp`, `r12`..`r15`) are unchanged and mapped memory is preserved. -/
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

theorem sphincsStackSize_eq : sphincsStackSize = 22304 := rfl
theorem roundConstsSize_eq : roundConstsSize = 192 := by
  rw [show roundConstsSize = (Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC).length from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl
theorem layerHeightsBytes_length : layerHeightsBytes.length = layerHeightsSize := by decide

private theorem wordBytes_getElem_eq_byteOf (x : BitVec 64) {i : Nat} (hi : i < 8) :
    (wordBytes (UInt64.ofBitVec x))[i]'(by simp [wordBytes, hi]) = Sym.byteOf x i := by
  rw [Sym.byteOf_mod]
  simp only [wordBytes, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofBitVec,
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have hmod : (8 * i) % 64 = 8 * i := Nat.mod_eq_of_lt (by omega)
  simp [hmod]

private theorem retOf_of_bytesAt_retAddr {m : MachineData} {retAddr : Int64}
    (hRet : BytesAt m.dmem (rspOf m) (wordBytes (UInt64.ofBitVec retAddr.toBitVec))) :
    retOf m = retAddr := by
  have hload : Mem.loadInt m.dmem (rspOf m) 8 = some (retAddr.toBitVec.toNat : Int) := by
    have h1 := Sym.loadInt_of_get? m.dmem (rspOf m) 8 (fun i => Sym.byteOf retAddr.toBitVec i) (by
      intro i hi
      have hb := hRet i (by simp [wordBytes, hi])
      rwa [wordBytes_getElem_eq_byteOf retAddr.toBitVec hi] at hb)
    have h2 := Sym.ofBytes_byteOf retAddr.toBitVec 0 8
    simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      Nat.mod_eq_of_lt retAddr.toBitVec.isLt] at h2
    rw [h1, h2]
  rw [retOf_of_loadInt hload, Int64.ofBitVec_toBitVec]

private theorem ReadOnlyBuf.restrict {d : DataMem} {addr : BitVec 64} {bytes : List UInt8}
    {initState : MachineData} {stackSpan : Nat}
    (h : ReadOnlyBuf d addr bytes initState stackSpan)
    {areas : List (BitVec 64 × Nat)} (ha : (addr, bytes.length) ∈ areas) :
    ReadOnlyBuf (restrictMemory d areas) addr bytes { initState with dmem := restrictMemory d areas } stackSpan :=
  ⟨h.1.restrict ha, h.2.1, h.2.2⟩

/-- **The callees' contracts** in an `ElfHost` containing all five callees. -/
theorem callees [ElfHost]
    {secMemcpy kMemcpy : Nat} (hMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    {secMemset kMemset : Nat} (hMemset : PlacedIn Common.Memset.code secMemset kMemset)
    {secKeccakF kKeccakF : Nat} (hKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    {secUpdate kUpdate : Nat} (hUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    {secFinalize kFinalize : Nat} (hFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize) :
    Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec_elf hMemcpy
  have hmemset := Mem.Memset.memset_spec_elf hMemset
  have hkf := keccakF_spec_elf hKeccakF
  ⟨hmemcpy, hmemset, Hasher.Update.update_spec_elf hUpdate hmemcpy hkf,
    Hasher.Finalize.finalize_spec_elf hFinalize hmemcpy hmemset hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct** (x86-64). -/
theorem verify_correct
    -- 1. Loaded program: a multi-section ELF host containing `sphincs_verify` and its five callees.
    [ElfHost]
    {secVerify kVerify : Nat} (hVerify : PlacedIn Sphincs.SphincsVerify.code secVerify kVerify)
    {secMemcpy kMemcpy : Nat} (hMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    {secMemset kMemset : Nat} (hMemset : PlacedIn Common.Memset.code secMemset kMemset)
    {secKeccakF kKeccakF : Nat} (hKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    {secUpdate kUpdate : Nat} (hUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    {secFinalize kFinalize : Nat} (hFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize)
    -- 2. Canonical byte inputs (32 B pk, 32 B msg, 7740 B sig).
    (pkBytes : Vector UInt8 pkSize)
    (msgBytes : Vector UInt8 msgSize)
    (sigBytes : Vector UInt8 sigSize)
    -- 3. Initial CPU state, explicit return address at entry RSP, and ABI stack
    --    (`sphincsStackSize` bytes below RSP plus `retAddrSize`-byte return address at RSP).
    (initState : MachineData)
    (retAddr : Int64)
    (hStackOk : StackOk initState sphincsStackSize)
    (hRetAddr : BytesAt initState.dmem (rspOf initState) (wordBytes (UInt64.ofBitVec retAddr.toBitVec)))
    -- 4. Read-only program data (.rodata) and caller input buffers (rdi, rsi, rdx),
    --    each present in memory, non-wrapping, and disjoint from the entry stack span.
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes
      initState (sphincsStackSize + retAddrSize))
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes
      initState (sphincsStackSize + retAddrSize))
    (hPkBuf : ReadOnlyBuf initState.dmem (reg initState .rdi) pkBytes.toList
      initState (sphincsStackSize + retAddrSize))
    (hMsgBuf : ReadOnlyBuf initState.dmem (reg initState .rsi) msgBytes.toList
      initState (sphincsStackSize + retAddrSize))
    (hSigBuf : ReadOnlyBuf initState.dmem (reg initState .rdx) sigBytes.toList
      initState (sphincsStackSize + retAddrSize))
    -- 5. Loader-populated GOT slots for memcpy and memset, pairwise disjoint and apart from the stack.
    (hGotSlots : GotSlotsOk initState sphincsStackSize ["memcpy", "memset"]) :
    -- Statement: starting at `sphincs_verify`'s entry in `initState`, every execution under
    -- `ElfHost.exe` terminates in finitely many steps (`Eventually (elfStep1 ElfHost.exe)`) at a
    -- `finalState` satisfying:
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        -- A. Control-flow return and ABI stack cleanup:
        --    PC reaches `retAddr` and `ret` pops the 8-byte return address from RSP.
        finalState.pc = retAddr ∧
        rspOf finalState.data = rspOf initState + 8#64 ∧
        -- B. Functional correctness (return value in RAX):
        --    RAX is 1 iff the mathematical leanSPHINCS verifier accepts the decoded raw bytes.
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        -- C. Memory framing (write confinement):
        --    Every byte outside the `sphincsStackSize` bytes strictly below entry RSP is unchanged
        --    (including the return address at RSP, input buffers, .rodata, and GOT slots).
        SameOutside initState.dmem finalState.data.dmem
          (InRange (stackBottomAddr initState sphincsStackSize) sphincsStackSize) ∧
        -- D. Callee-saved ABI preservation:
        --    System V callee-saved registers (rbx, rbp, r12..r15) are unchanged and no mapped
        --    data-memory byte becomes unmapped.
        CalleeSavedAndMemKept initState finalState.data)
      -- Entry machine state: registers and data memory `initState`, PC at `sphincs_verify`.
      ⟨initState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  have hPkLen : pkBytes.toList.length = pkSize := pkBytes.length_toList
  have hMsgLen : msgBytes.toList.length = msgSize := msgBytes.length_toList
  have hSigLen : sigBytes.toList.length = sigSize := sigBytes.length_toList
  have hRet : retOf initState = retAddr := retOf_of_bytesAt_retAddr hRetAddr
  rw [← hRet, ← NativeRustc.Sphincs.verify_decode_bytes pkBytes.toList msgBytes.toList sigBytes.toList
    hPkLen hMsgLen hSigLen]
  have hl := hVerify.label NativeRustcX64.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcX64.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
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
    hVerify (callees hMemcpy hMemset hKeccakF hUpdate hFinalize)
    ⟨hStackOk, hrc, hlhb, hlhw, hlha, hpkb, hpkw, hpka, hmsgb, hmsgw, hmsga, hsigb, hsigw, hsiga,
      hGotSlots⟩
    Parse.parse_spec digest_spec fors_spec forsKey_spec encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined
    -- 1. Loaded program: a multi-section ELF host containing `sphincs_verify` and its five callees.
    [ElfHost]
    {secVerify kVerify : Nat} (hVerify : PlacedIn Sphincs.SphincsVerify.code secVerify kVerify)
    {secMemcpy kMemcpy : Nat} (hMemcpy : PlacedIn Common.Memcpy.code secMemcpy kMemcpy)
    {secMemset kMemset : Nat} (hMemset : PlacedIn Common.Memset.code secMemset kMemset)
    {secKeccakF kKeccakF : Nat} (hKeccakF : PlacedIn Common.KeccakF.code secKeccakF kKeccakF)
    {secUpdate kUpdate : Nat} (hUpdate : PlacedIn Common.Update.code secUpdate kUpdate)
    {secFinalize kFinalize : Nat} (hFinalize : PlacedIn Common.Finalize.code secFinalize kFinalize)
    -- 2. Canonical byte inputs (32 B pk, 32 B msg, 7740 B sig).
    (pkBytes : Vector UInt8 pkSize)
    (msgBytes : Vector UInt8 msgSize)
    (sigBytes : Vector UInt8 sigSize)
    -- 3. Initial CPU state, explicit return address at entry RSP, and ABI stack
    --    (`sphincsStackSize` bytes below RSP plus `retAddrSize`-byte return address at RSP).
    (initState : MachineData)
    (retAddr : Int64)
    (hStackOk : StackOk initState sphincsStackSize)
    (hRetAddr : BytesAt initState.dmem (rspOf initState) (wordBytes (UInt64.ofBitVec retAddr.toBitVec)))
    -- 4. Read-only program data (.rodata) and caller input buffers (rdi, rsi, rdx),
    --    each present in memory, non-wrapping, and disjoint from the entry stack span.
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes
      initState (sphincsStackSize + retAddrSize))
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes
      initState (sphincsStackSize + retAddrSize))
    (hPkBuf : ReadOnlyBuf initState.dmem (reg initState .rdi) pkBytes.toList
      initState (sphincsStackSize + retAddrSize))
    (hMsgBuf : ReadOnlyBuf initState.dmem (reg initState .rsi) msgBytes.toList
      initState (sphincsStackSize + retAddrSize))
    (hSigBuf : ReadOnlyBuf initState.dmem (reg initState .rdx) sigBytes.toList
      initState (sphincsStackSize + retAddrSize))
    -- 5. Loader-populated GOT slots for memcpy and memset, pairwise disjoint and apart from the stack.
    (hGotSlots : GotSlotsOk initState sphincsStackSize ["memcpy", "memset"]) :
    -- Allowed data-memory footprint of `sphincs_verify` (everything else will be unmapped):
    let allowedRegions := [
      -- Stack frame plus 8-byte return address at entry RSP.
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize + retAddrSize),
      -- Caller input buffers (pk: 32 B, msg: 32 B, sig: 7740 B).
      (reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
      -- Read-only program tables (.rodata: Keccak round constants and LAYER_HEIGHTS).
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize),
      -- Dynamic-linker GOT slots for memcpy and memset (8 B each).
      (gotAddr "memcpy", gotSlotSize), (gotAddr "memset", gotSlotSize)]
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
        -- A. Control-flow return and ABI stack cleanup.
        finalState.pc = retAddr ∧
        rspOf finalState.data = rspOf confinedState + 8#64 ∧
        -- B. Functional correctness (return value in RAX).
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        -- C. Memory framing (no writes outside the `sphincsStackSize` bytes below entry RSP).
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        -- D. Callee-saved ABI preservation (rbx, rbp, r12..r15 and mapped memory kept).
        CalleeSavedAndMemKept confinedState finalState.data)
      -- Entry machine state: restricted memory `confinedState`, PC at `sphincs_verify`.
      ⟨confinedState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  dsimp only
  let allowedRegions := [(stackBottomAddr initState sphincsStackSize, sphincsStackSize + retAddrSize),
      (reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize),
      (gotAddr "memcpy", gotSlotSize), (gotAddr "memset", gotSlotSize)]
  let confinedState : MachineData := { initState with dmem := restrictMemory initState.dmem allowedRegions }
  have hs : StackOk confinedState sphincsStackSize :=
    ⟨hStackOk.1, hStackOk.2.1, hStackOk.2.2.restrict (by simp [allowedRegions, stackBelow, rspOf])⟩
  have hRetConfined : BytesAt confinedState.dmem (rspOf confinedState)
      (wordBytes (UInt64.ofBitVec retAddr.toBitVec)) := by
    intro i hi
    have hi8 : i < 8 := by simpa [wordBytes] using hi
    have haddr : rspOf initState + BitVec.ofNat 64 i =
        stackBottomAddr initState sphincsStackSize + BitVec.ofNat 64 (sphincsStackSize + i) := by
      simp only [stackBottomAddr, stackBelow]
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    show (restrictMemory initState.dmem allowedRegions).get? (rspOf initState + BitVec.ofNat 64 i) = _
    rw [haddr, restrictMemory_inside initState.dmem (n := sphincsStackSize + retAddrSize)
      (by simp [allowedRegions]) (by unfold retAddrSize; omega), ← haddr]
    exact hRetAddr i hi
  refine ⟨fun addr hOut => restrictMemory_outside initState.dmem hOut, ?_⟩
  exact verify_correct hVerify hMemcpy hMemset hKeccakF hUpdate hFinalize
    pkBytes msgBytes sigBytes confinedState retAddr hs hRetConfined
    (hRoundConsts.restrict (by simp [allowedRegions]))
    (hLayerHeights.restrict (by simp [allowedRegions, layerHeightsBytes_length]))
    (hPkBuf.restrict (by simp [allowedRegions, pkBytes.length_toList]))
    (hMsgBuf.restrict (by simp [allowedRegions, msgBytes.length_toList]))
    (hSigBuf.restrict (by simp [allowedRegions, sigBytes.length_toList])) (by
      refine ⟨?_, hGotSlots.2⟩
      intro l hl
      obtain ⟨hb, hn, hs, ha⟩ := hGotSlots.1 l hl
      refine ⟨hb.restrict ?_, hn, hs, ha⟩
      simp only [Int.toBytes_length]
      simp at hl
      rcases hl with rfl | rfl <;> simp [allowedRegions])

end

end NativeRustcX64.SphincsVerifier
