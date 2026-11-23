module

public import NativeRustcVmArm.Keccak.Common
public import NativeRustcVm.Keccak.Words

/-!
# `keccak256_words::<hash_words's closure>`: what holds between its blocks

From the machine state `m0` at the entry (`out`, `count`, `len`, the slice `ws` of `n` words in X0
to X4): the frame (`frame`, 288 bytes below the entry's SP); the words the slice holds at entry
(`word`, zero past `n`); the whole blocks' count `nb = len / 136`. `Ctx m0 m`: SP the frame, X19 to
X24 the function's values (`out`, `len`, `ws`, `min(count, n) = n`, `17 nb`, `nb`), the frame's
slots the entry's X19 to X30, memory the entry's outside the stack the function uses, every
mapped byte mapped. `Lanes m0 m f`: the 25 lanes at the frame's byte 8 hold `f`. `pre A base j`:
the lanes `A` with words `base` to `base + j - 1` XORed into the first `j`.

`ctx_step` and `lanes_step` carry them over a block that writes one lane.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Protocol.KeccakHash
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep)

@[expose] public section

/-- The frame's base: SP in the body. -/
def frame (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 288

/-- The whole blocks' count. -/
def nb (m0 : MachineData) : Nat := m0.regs.X2.toNat / 136

/-- Word `i` of the slice at entry, zero past it. -/
def word (m0 : MachineData) (i : Nat) : UInt64 :=
  littleEndianLane (bytesOf m0.dmem m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)) i

/-- The frame slots that hold the entry's registers. -/
def savedSlots : List (Nat × XReg) :=
  [(208, .X29), (216, .X30), (224, .X26), (232, .X25), (240, .X24), (248, .X23), (256, .X22),
    (264, .X21), (272, .X20), (280, .X19)]

/-- The registers every block of the body keeps. -/
def ctxRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28]

/-- **What holds throughout the body.** -/
structure Ctx (m0 m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frame m0
  x19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec
  x20 : (m.regs.getXReg .X20).toBitVec = m0.regs.X2.toBitVec
  x21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X3.toBitVec
  x22 : (m.regs.getXReg .X22).toBitVec = m0.regs.X4.toBitVec
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (17 * nb m0)
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (nb m0)
  x27 : m.regs.getXReg .X27 = m0.regs.getXReg .X27
  x28 : m.regs.getXReg .X28 = m0.regs.getXReg .X28
  saved : AllOf (fun p : Nat × XReg => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.getXReg p.2).toBitVec) savedSlots
  same : SameOutside m0.dmem m.dmem
    (InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack) NativeRustcVmArm.keccak256WordsStack)
  kept : Kept m0.dmem m.dmem

/-- The 25 lanes at the frame's byte 8 hold `f`. -/
def Lanes (m0 m : MachineData) (f : Nat → UInt64) : Prop :=
  ∀ i < 25, WordAt m.dmem (frame m0 + BitVec.ofNat 64 (8 + 8 * i)) (f i).toBitVec

/-- The lanes `A` with the words `w (base + i)` XORed into the first `j`. -/
def pre (A : KeccakState) (w : Nat → UInt64) (base j : Nat) (i : Nat) : UInt64 :=
  if i < j then Keccak.lane A i ^^^ w (base + i) else Keccak.lane A i

end

public section

theorem lanes_congr {m0 m : MachineData} {f g : Nat → UInt64} (h : Lanes m0 m f)
    (hfg : ∀ i < 25, f i = g i) : Lanes m0 m g := fun i hi => hfg i hi ▸ h i hi

theorem pre_zero (A : KeccakState) (w : Nat → UInt64) (base : Nat) :
    pre A w base 0 = Keccak.lane A := by
  funext i
  simp [pre]

theorem pre_succ (A : KeccakState) (w : Nat → UInt64) (base j : Nat) {x : UInt64}
    (hx : x = Keccak.lane A j ^^^ w (base + j)) :
    (fun i => if i = j then x else pre A w base j i) = pre A w base (j + 1) := by
  funext i
  unfold pre
  by_cases h : i = j
  · subst h
    simp [hx]
  · simp only [h, ↓reduceIte]
    by_cases h' : i < j
    · simp [h', show i < j + 1 by omega]
    · simp [h', show ¬ i < j + 1 by omega]

theorem pre_17 (A : KeccakState) (w : Nat → UInt64) (base : Nat) {i : Nat} (hi : i < 25) :
    pre A w base 17 i = Keccak.lane (Native.Keccak.Proof.xorRate A fun k => w (base + k)) i := by
  rw [Native.Keccak.Proof.lane_xorRate _ _ hi, pre]

theorem stack_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack) :
    (stackBelow m0 NativeRustcVmArm.keccak256WordsStack).toNat = m0.regs.SP.toNat - 688 := by
  have := h.2.1
  simp only [stackBelow, NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack]
    at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

theorem frame_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack) :
    (frame m0).toNat = m0.regs.SP.toNat - 288 := by
  have := h.2.1
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at this
  simp only [frame]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

theorem sp_lt {m0 : MachineData} : m0.regs.SP.toNat < 2 ^ 64 := m0.regs.SP.toNat_lt

theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack) :
    NoWrap (frame m0) 288 := by
  have := h.2.1
  have := @sp_lt m0
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
  unfold NoWrap
  rw [frame_toNat h]
  omega

theorem frame_aligned {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack) :
    (frame m0).toNat % 16 = 0 := by
  have := h.1
  have := h.2.1
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
  rw [frame_toNat h]
  omega

/-- The frame is in the stack the function uses. -/
theorem inStack_of_frame {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack)
    {p : BitVec 64} (hp : InRange (frame m0) 288 p) :
    InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack)
      NativeRustcVmArm.keccak256WordsStack p := by
  have := h.2.1
  have := @sp_lt m0
  have hs := stack_toNat h
  have hf := frame_toNat h
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
  rw [inRange_iff (by omega)] at hp
  rw [inRange_iff (by omega)]
  omega

/-- The frame is mapped. -/
theorem frame_mapped {m0 m : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack)
    (hk : Kept m0.dmem m.dmem) : Mapped m.dmem (frame m0) 288 := by
  intro i hi
  have := h.2.2 (400 + i) (by simp only [NativeRustcVmArm.keccak256WordsStack,
    NativeRustcVmArm.keccakFStack]; omega)
  refine hk _ ?_
  have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 NativeRustcVmArm.keccak256WordsStack +
      BitVec.ofNat 64 (400 + i) = frame m0 + BitVec.ofNat 64 i := by
    simp only [frame, NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack]
    bv_omega
  rwa [e] at this

theorem firstOverlap_none_of_below {r o n lim : Nat} {ws : List Write}
    (h : ∀ w ∈ ws, w.r = r → w.off + w.n ≤ lim) (ho : lim ≤ o) : firstOverlap r o n ws = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [firstOverlap]
    split
    · rename_i hc
      have := h w List.mem_cons_self hc.1
      omega
    · exact ih fun w' hw' => h w' (List.mem_cons_of_mem _ hw')

variable [Labels] {env : Env} {S S₀ : SState} {m m₀ : MachineData}

/-- **`Ctx` after a block** that writes only below the saved slots of the frame and keeps SP and
X19 to X24. -/
theorem ctx_step {m0 m m' : MachineData} (hstk : StackOk m0 NativeRustcVmArm.keccak256WordsStack)
    (hc : Ctx m0 m) {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m rs vars) S m') (hwf : (Env.ofMachine m rs vars).WF)
    (hb : rs[0]? = some (frame m0, 288)) (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs)
    (hall : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 208) : Ctx m0 m' := by
  have hreg : ∀ r ∈ ctxRegs, (m'.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec :=
    fun r hr => (hm.regs r _ (mem_of_allOf (P := fun r => S.reg r = some (.reg r)) hregs hr)).trans
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm.sp, hsp]
    simp [Sym.eval, Env.base_ofMachine_eq, hb]
  · rw [hreg .X19 (by simp [ctxRegs])]; exact hc.x19
  · rw [hreg .X20 (by simp [ctxRegs])]; exact hc.x20
  · rw [hreg .X21 (by simp [ctxRegs])]; exact hc.x21
  · rw [hreg .X22 (by simp [ctxRegs])]; exact hc.x22
  · rw [hreg .X23 (by simp [ctxRegs])]; exact hc.x23
  · rw [hreg .X24 (by simp [ctxRegs])]; exact hc.x24
  · exact (UInt64.toBitVec_inj.mp (hreg .X27 (by simp [ctxRegs]))).trans hc.x27
  · exact (UInt64.toBitVec_inj.mp (hreg .X28 (by simp [ctxRegs]))).trans hc.x28
  · have hsv := hc.saved
    have hb' : (Env.ofMachine m rs vars).regions[0]? = some (frame m0, 288) := hb
    have hk : ∀ o, 208 ≤ o → firstOverlap 0 o 8 S.mem = none := fun o ho =>
      firstOverlap_none_of_below (fun w hw _ => (hall w hw).2) ho
    simp only [AllOf, savedSlots] at hsv ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := hsv
    exact ⟨wordAt_keep hm hb' (by decide) (hk _ (by decide)) s0,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s1,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s2,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s3,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s4,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s5,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s6,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s7,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s8,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s9, trivial⟩
  · intro p hp
    refine (NativeRustcArm.KeccakF.same_region hm hwf hb
      (fun w hw => ⟨(hall w hw).1, by have := (hall w hw).2; omega⟩) p
      fun h => hp (inStack_of_frame hstk h)).trans (hc.same p hp)
  · exact fun p h => hm.kept hwf p (hc.kept p h)

/-- **The lanes after a block that writes lane `j`**: lane `j` the written value, the others
kept. -/
theorem lanes_step {m0 : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 288)) {j : Nat} (hj : j < 25) {v : Sym}
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, v⟩]) {f : Nat → UInt64}
    (hl : ∀ i < 25, WordAt env.mem0 (frame m0 + BitVec.ofNat 64 (8 + 8 * i)) (f i).toBitVec)
    {x : UInt64} (hv : v.eval env = x.toBitVec) :
    Lanes m0 m (fun i => if i = j then x else f i) := by
  intro i hi
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    exact wordAt_of_eq (wordAt_write hm hb (by omega) (by rw [hmem]; simp [firstOverlap])) hv
  · simp only [h, ↓reduceIte]
    refine wordAt_keep hm hb (by omega) ?_ (hl i hi)
    rw [hmem]
    simp only [firstOverlap]
    split
    · omega
    · rfl

end

end NativeRustcVmArm.WordsHash
