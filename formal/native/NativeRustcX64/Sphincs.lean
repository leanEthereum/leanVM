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

open NativeRustc NativeRustc.Keccak NativeRustcX64.SphincsVerifyProof Native.Keccak

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

/-- Lowest address of the `stackSize`-byte stack frame below entry RSP. -/
abbrev stackBottomAddr (m : MachineData) (stackSize : Nat) : BitVec 64 := stackBelow m stackSize

/-- Caller's 64-bit return PC read from the 8 bytes at entry RSP. -/
abbrev returnAddrOf (m : MachineData) : Int64 := retOf m

/-- Keccak round constants sit at `roundConstsAddr`, do not wrap, and are disjoint from the stack. -/
abbrev RoundConstsOk [Labels] (m : MachineData) (stackSize : Nat) : Prop := RcAt m stackSize

/-- GOT slots for `symbols` hold their target addresses, do not wrap, and are disjoint from the stack and `areas`. -/
abbrev GotSlotsOk [Labels] (m : MachineData) (stackSize : Nat)
    (areas : List (BitVec 64 × Nat)) (symbols : List Label) : Prop :=
  GotAt m stackSize areas symbols

/-- System V callee-saved registers (`rbx`, `rbp`, `r12`..`r15`) are unchanged and mapped memory is preserved. -/
abbrev CalleeSavedAndMemKept (m m' : MachineData) : Prop := Saved m m'

/-- Byte ranges `[a, a + n)` and `[a', a' + n')` are disjoint. -/
abbrev Disjoint (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop := Apart a n a' n'

/-- Address `addr` lies in at least one `(base, byteLen)` region of `areas`. -/
abbrev InRegions (areas : List (BitVec 64 × Nat)) (addr : BitVec 64) : Prop := ReadRegions areas addr

end

public section

theorem sphincsStackSize_eq : sphincsStackSize = 22304 := rfl
theorem roundConstsSize_eq : roundConstsSize = 192 := by
  rw [show roundConstsSize = (Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC).length from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl
theorem layerHeightsBytes_length : layerHeightsBytes.length = layerHeightsSize := by decide

-- Loaded program: an abstract Kraken host whose instruction stream is the ingested
-- `sphincs_verify` bundle (`sphincs_verify`, `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
-- `Hasher::finalize`, and rodata).
variable [Host] (hHostProg : Host.prog = Sphincs.code)
include hHostProg

/-- **The callees' contracts** in `sphincs_verify`'s program. -/
theorem callees : Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hHostProg)
  have hmemset := Mem.Memset.memset_spec (placed_memset hHostProg)
  have hkf := keccakF_spec (placed_keccakF hHostProg)
  ⟨hmemcpy, hmemset, Hasher.Update.update_spec (placed_update hHostProg) hmemcpy hkf,
    Hasher.Finalize.finalize_spec (placed_finalize hHostProg) hmemcpy hmemset hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct** (x86-64). -/
theorem verify_correct
    -- 1. Logical byte inputs and their fixed canonical lengths.
    (pkBytes msgBytes sigBytes : List UInt8)
    (hPkLen : pkBytes.length = pkSize)
    (hMsgLen : msgBytes.length = msgSize)
    (hSigLen : sigBytes.length = sigSize)
    -- 2. Initial CPU state and ABI stack (`sphincsStackSize` bytes below RSP plus `retAddrSize`-byte
    --    return address at RSP).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 3. Read-only program data (.rodata): Keccak round constants and LAYER_HEIGHTS table,
    --    in memory, non-wrapping, and disjoint from the stack region.
    (hRoundConsts : RoundConstsOk initState sphincsStackSize)
    (hLayerHeightsBytes : BytesAt initState.dmem
      (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsBytes)
    (hLayerHeightsNoWrap : NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsSize)
    (hLayerHeightsDisjointStack : Disjoint (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    -- 4. Caller input buffers in memory, pointed to by System V ABI registers (rdi, rsi, rdx),
    --    each non-wrapping and disjoint from the stack region.
    (hPkInMem : BytesAt initState.dmem (reg initState .rdi) pkBytes)
    (hPkNoWrap : NoWrap (reg initState .rdi) pkSize)
    (hPkDisjointStack : Disjoint (reg initState .rdi) pkSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    (hMsgInMem : BytesAt initState.dmem (reg initState .rsi) msgBytes)
    (hMsgNoWrap : NoWrap (reg initState .rsi) msgSize)
    (hMsgDisjointStack : Disjoint (reg initState .rsi) msgSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    (hSigInMem : BytesAt initState.dmem (reg initState .rdx) sigBytes)
    (hSigNoWrap : NoWrap (reg initState .rdx) sigSize)
    (hSigDisjointStack : Disjoint (reg initState .rdx) sigSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    -- 5. Loader-populated GOT slots for memcpy and memset, pairwise disjoint and apart from
    --    the stack, input buffers, and LAYER_HEIGHTS.
    (hGotSlots : GotSlotsOk initState sphincsStackSize
      [(reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, layerHeightsSize)] ["memcpy", "memset"]) :
    -- Statement: starting at `sphincs_verify`'s entry in `initState`, every execution under
    -- `Host.exe` terminates in finitely many steps (`Eventually (step1 Host.exe)`) at a
    -- `finalState` satisfying:
    Eventually (step1 Host.exe)
      (fun finalState ↦
        -- A. Control-flow return and ABI stack cleanup:
        --    PC reaches the 8-byte return address read from entry RSP, and `ret` pops it.
        finalState.pc = returnAddrOf initState ∧
        rspOf finalState.data = rspOf initState + 8#64 ∧
        -- B. Functional correctness (return value in RAX):
        --    RAX is 1 iff the mathematical leanSPHINCS verifier accepts the decoded raw bytes.
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes)
          (Native.SphincsVerifier.decodeMsg msgBytes)
          (Native.SphincsVerifier.decodeSig sigBytes) then 1 else 0) ∧
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
  rw [← NativeRustc.Sphincs.verify_decode_bytes pkBytes msgBytes sigBytes hPkLen hMsgLen hSigLen]
  have hp := placed hHostProg
  have hl := hp.label NativeRustcX64.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcX64.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
  exact run_correct
    ⟨initState, pkBytes, msgBytes, sigBytes, hPkLen, hMsgLen, hSigLen,
      NativeRustcX64.Sphincs.SphincsVerify.programOffset⟩
    hp (callees hHostProg)
    ⟨hStackOk, hRoundConsts, hLayerHeightsBytes, hLayerHeightsNoWrap, hLayerHeightsDisjointStack,
      hPkInMem, hPkNoWrap, hPkDisjointStack, hMsgInMem, hMsgNoWrap, hMsgDisjointStack,
      hSigInMem, hSigNoWrap, hSigDisjointStack, hGotSlots⟩
    Parse.parse_spec digest_spec fors_spec forsKey_spec encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined
    -- 1. Logical byte inputs and their fixed canonical lengths.
    (pkBytes msgBytes sigBytes : List UInt8)
    (hPkLen : pkBytes.length = pkSize)
    (hMsgLen : msgBytes.length = msgSize)
    (hSigLen : sigBytes.length = sigSize)
    -- 2. Initial CPU state and ABI stack (`sphincsStackSize` bytes below RSP plus `retAddrSize`-byte
    --    return address at RSP).
    (initState : MachineData)
    (hStackOk : StackOk initState sphincsStackSize)
    -- 3. Read-only program data (.rodata): Keccak round constants and LAYER_HEIGHTS table,
    --    in memory, non-wrapping, and disjoint from the stack region.
    (hRoundConsts : RoundConstsOk initState sphincsStackSize)
    (hLayerHeightsBytes : BytesAt initState.dmem
      (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsBytes)
    (hLayerHeightsNoWrap : NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsSize)
    (hLayerHeightsDisjointStack : Disjoint (label NativeRustcX64.layerHeightsLabel).toBitVec layerHeightsSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    -- 4. Caller input buffers in memory, pointed to by System V ABI registers (rdi, rsi, rdx),
    --    each non-wrapping and disjoint from the stack region.
    (hPkInMem : BytesAt initState.dmem (reg initState .rdi) pkBytes)
    (hPkNoWrap : NoWrap (reg initState .rdi) pkSize)
    (hPkDisjointStack : Disjoint (reg initState .rdi) pkSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    (hMsgInMem : BytesAt initState.dmem (reg initState .rsi) msgBytes)
    (hMsgNoWrap : NoWrap (reg initState .rsi) msgSize)
    (hMsgDisjointStack : Disjoint (reg initState .rsi) msgSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    (hSigInMem : BytesAt initState.dmem (reg initState .rdx) sigBytes)
    (hSigNoWrap : NoWrap (reg initState .rdx) sigSize)
    (hSigDisjointStack : Disjoint (reg initState .rdx) sigSize
      (stackBottomAddr initState sphincsStackSize) (sphincsStackSize + retAddrSize))
    -- 5. Loader-populated GOT slots for memcpy and memset, pairwise disjoint and apart from
    --    the stack, input buffers, and LAYER_HEIGHTS.
    (hGotSlots : GotSlotsOk initState sphincsStackSize
      [(reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, layerHeightsSize)] ["memcpy", "memset"]) :
    -- Allowed data-memory footprint of `sphincs_verify` (everything else will be unmapped):
    let allowedRegions := [
      -- Stack frame plus 8-byte return address at entry RSP.
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize + retAddrSize),
      -- Caller input buffers (pk: 32 B, msg: 32 B, sig: 7740 B).
      (reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
      -- Read-only program tables (.rodata: Keccak round constants and LAYER_HEIGHTS).
      (roundConstsAddr, roundConstsSize),
      ((label NativeRustcX64.layerHeightsLabel).toBitVec, layerHeightsBytes.length),
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
    Eventually (step1 Host.exe)
      (fun finalState ↦
        -- A. Control-flow return and ABI stack cleanup.
        finalState.pc = returnAddrOf confinedState ∧
        rspOf finalState.data = rspOf confinedState + 8#64 ∧
        -- B. Functional correctness (return value in RAX).
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes)
          (Native.SphincsVerifier.decodeMsg msgBytes)
          (Native.SphincsVerifier.decodeSig sigBytes) then 1 else 0) ∧
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
      ((label NativeRustcX64.layerHeightsLabel).toBitVec, layerHeightsBytes.length),
      (gotAddr "memcpy", gotSlotSize), (gotAddr "memset", gotSlotSize)]
  let confinedState : MachineData := { initState with dmem := restrictMemory initState.dmem allowedRegions }
  have hs : StackOk confinedState sphincsStackSize :=
    ⟨hStackOk.1, hStackOk.2.1, hStackOk.2.2.restrict (by simp [allowedRegions, stackBelow, rspOf])⟩
  have hr : RoundConstsOk confinedState sphincsStackSize :=
    ⟨hRoundConsts.1.restrict (by simp [allowedRegions]), hRoundConsts.2⟩
  refine ⟨fun addr hOut => restrictMemory_outside initState.dmem hOut, ?_⟩
  exact verify_correct hHostProg pkBytes msgBytes sigBytes hPkLen hMsgLen hSigLen
    confinedState hs hr
    (hLayerHeightsBytes.restrict (by simp [allowedRegions])) hLayerHeightsNoWrap hLayerHeightsDisjointStack
    (hPkInMem.restrict (by simp [allowedRegions, hPkLen])) hPkNoWrap hPkDisjointStack
    (hMsgInMem.restrict (by simp [allowedRegions, hMsgLen])) hMsgNoWrap hMsgDisjointStack
    (hSigInMem.restrict (by simp [allowedRegions, hSigLen])) hSigNoWrap hSigDisjointStack (by
      refine ⟨?_, hGotSlots.2⟩
      intro l hl
      obtain ⟨hb, hn, hs, ha⟩ := hGotSlots.1 l hl
      refine ⟨hb.restrict ?_, hn, hs, ha⟩
      simp only [Int.toBytes_length]
      simp at hl
      rcases hl with rfl | rfl <;> simp [allowedRegions])

end

end NativeRustcX64.SphincsVerifier
