module

public import NativeRustcVmArm.Code.Vm.Seed.Names
public import NativeRustcVmArm.Spec.Top
public import NativeRustcVmArm.Top.Seed.Exec

/-!
# `seed`: where things are

The facts `SeedPre` gives as numbers (`Geo`, `geo_of`): the frame of 240 bytes at `frameOf m0`
(the state from its byte 8), the stack, the public input, the output, the round constants and
the bytecode. What the states after `memset` (`S1`) and after `memcpy` (`S2`) hold. The blocks'
places (`hb<k>`) and the label (`lbl_entry`); `lsl #3` (`evalUBFM_lsl3`); the state permuted
(`seed_state`).
-/

namespace NativeRustcVmArm.Top.Seed

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Seed NativeVm.Model
open NativeRustcVm (WordsAt Region)

public section

/-- `lsl x, #3`. -/
theorem evalUBFM_lsl3 (x : BitVec 64) :
    (evalUBFM (w := .W64) x 61 60 : BitVec 64) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalUBFM, BitVec.toNat_shiftLeft, BitVec.take]
  simp only [show RegWidth.W64.bits = 64 from rfl]
  simp
  omega

/-- The state `seed` permutes: the IV, the public input, zeros. -/
theorem seed_state (iv : LeanVM.Protocol.Digest) (P : Vector UInt64 4) :
    (Vector.ofFn (n := 25) fun i ↦
      if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then P[i.val - 4] else 0).toList =
      iv.toList ++ P.toList ++ List.replicate 17 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_ofFn]
  have hl : (iv.toList ++ P.toList).length = 8 := by simp
  have h25 : i < 25 := by simpa using h1
  by_cases ha : i < 4
  · simp only [ha, ↓reduceDIte]
    rw [List.getElem_append_left (by rw [hl]; omega), List.getElem_append_left (by simp; omega)]
    simp
  · by_cases hb : i < 8
    · simp only [ha, hb, ↓reduceDIte]
      rw [List.getElem_append_left (by rw [hl]; omega),
        List.getElem_append_right (by simp; omega)]
      simp
    · simp only [ha, hb, ↓reduceDIte]
      rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_replicate]

/-- The slots `seed`'s prologue fills. -/
theorem slotsIn : SlotsIn slots 208 240 := by simp [SlotsIn, slots]

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Seed.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Seed.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Seed.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Seed.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Seed.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Seed.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Seed.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Seed.entryOffset) NativeRustcVmArm.Vm.Seed.entry_at

end

/-- The frame's address. -/
@[expose] public def frameOf (m0 : MachineData) : BitVec 64 :=
  m0.regs.SP.toBitVec - BitVec.ofNat 64 240

/-- `SeedPre`'s addresses as numbers. -/
public structure Geo [Labels] (m0 : MachineData) : Prop where
  s : 928 ≤ m0.regs.SP.toBitVec.toNat
  al : m0.regs.SP.toBitVec.toNat % 16 = 0
  F : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 240
  F8 : (frameOf m0 + BitVec.ofNat 64 8).toNat = m0.regs.SP.toBitVec.toNat - 232
  F72 : (frameOf m0 + BitVec.ofNat 64 72).toNat = m0.regs.SP.toBitVec.toNat - 168
  sb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 seedStack).toNat = m0.regs.SP.toBitVec.toNat - 928
  pub : m0.regs.X3.toBitVec.toNat + 32 ≤ m0.regs.SP.toBitVec.toNat - 928 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X3.toBitVec.toNat
  pubN : m0.regs.X3.toBitVec.toNat + 32 ≤ 2 ^ 64
  out : m0.regs.X0.toBitVec.toNat + 200 ≤ m0.regs.SP.toBitVec.toNat - 928 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X0.toBitVec.toNat
  outN : m0.regs.X0.toBitVec.toNat + 200 ≤ 2 ^ 64
  rc : rcAddr.toNat + 192 ≤ m0.regs.SP.toBitVec.toNat - 928 ∨
    m0.regs.SP.toBitVec.toNat ≤ rcAddr.toNat
  rcN : rcAddr.toNat + 192 ≤ 2 ^ 64
  bc : 0 < m0.regs.X2.toBitVec.toNat →
    m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toBitVec.toNat ≤ m0.regs.SP.toBitVec.toNat - 928 ∨
      m0.regs.SP.toBitVec.toNat ≤ m0.regs.X1.toBitVec.toNat
  bcN : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toBitVec.toNat ≤ 2 ^ 64
  n32 : 9 + 8 * m0.regs.X2.toBitVec.toNat < 2 ^ 32

public section

theorem geo_of [Labels] {m0 : MachineData} (hpre : SeedPre m0) : Geo m0 := by
  obtain ⟨⟨hal, hsN, -⟩, ⟨-, hrcN, hrcA⟩, hn32, ⟨-, hbcN⟩, ⟨-, hpubN⟩,
    ⟨-, houtN⟩, hdP, hdO, hbcA⟩ := hpre
  have hS : seedStack = 928 := rfl
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs928 : 928 ≤ m0.regs.SP.toBitVec.toNat := hsN
  have hF : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 240 := toNat_subAddr (by omega)
  have hsb : (stackBelow m0 seedStack).toNat = m0.regs.SP.toBitVec.toNat - 928 :=
    toNat_subAddr (by rw [hS]; omega)
  have hPS : NativeRustcVm.Apart (stackBelow m0 seedStack) seedStack m0.regs.X3.toBitVec 32 :=
    (List.pairwise_pair (R := fun r r' : Region ↦ NativeRustcVm.Apart r.addr r.size r'.addr
      r'.size)).mp hdP
  have hOS : NativeRustcVm.Apart (stackBelow m0 seedStack) seedStack m0.regs.X0.toBitVec 200 :=
    (List.pairwise_pair (R := fun r r' : Region ↦ NativeRustcVm.Apart r.addr r.size r'.addr
      r'.size)).mp hdO
  unfold NativeRustcVm.Apart at hPS hOS hbcA
  unfold NativeRustcArm.Apart at hrcA
  unfold NativeRustcArm.NoWrap at hrcN
  rw [hsb, hS] at hPS hOS hrcA hbcA
  have e2 : m0.regs.X2.toNat = m0.regs.X2.toBitVec.toNat := rfl
  have hbcN' : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toBitVec.toNat ≤ 2 ^ 64 := hbcN
  have hpubN' : m0.regs.X3.toBitVec.toNat + 32 ≤ 2 ^ 64 := hpubN
  have houtN' : m0.regs.X0.toBitVec.toNat + 200 ≤ 2 ^ 64 := houtN
  have hn32' : 9 + 8 * m0.regs.X2.toBitVec.toNat < 2 ^ 32 := hn32
  refine ⟨hs928, hal, hF, ?_, ?_, hsb, by omega, hpubN', by omega, houtN', by omega, hrcN,
    fun h ↦ by have := hbcA (by omega); omega, hbcN', hn32'⟩
  · rw [toNat_addr (by omega), hF]; omega
  · rw [toNat_addr (by omega), hF]; omega

end

/-- After `memset`: the body of the frame, the output and the public input's addresses in X20,
X19, the IV at the frame's byte 8, zeros at its bytes 72 to 207. -/
public structure S1 (m0 m : MachineData) : Prop where
  body : Body m0 240 slots (InStack m0 928) m
  x19 : m.regs.X19 = m0.regs.X3
  x20 : m.regs.X20 = m0.regs.X0
  iv : ∀ w : List UInt64, w.length = m0.regs.X2.toBitVec.toNat →
    WordsAt m0.dmem m0.regs.X1.toBitVec w →
    WordsAt m.dmem (frameOf m0 + BitVec.ofNat 64 8) (fiatShamirIv w.toArray).toList
  zeros : BytesAt m.dmem (frameOf m0 + BitVec.ofNat 64 72) (List.replicate (8 * 17) 0)

/-- After `memcpy`: the body of the frame, the output written, the seed at the output. -/
public structure S2 (m0 m : MachineData) : Prop where
  body : Body m0 240 slots (fun q ↦ InStack m0 928 q ∨ InRange m0.regs.X0.toBitVec 200 q) m
  out : ∀ w : List UInt64, w.length = m0.regs.X2.toBitVec.toNat →
    WordsAt m0.dmem m0.regs.X1.toBitVec w → ∀ P : Vector UInt64 4,
    WordsAt m0.dmem m0.regs.X3.toBitVec P.toList →
    WordsAt m.dmem m0.regs.X0.toBitVec (seed w.toArray P).toList

end NativeRustcVmArm.Top.Seed
