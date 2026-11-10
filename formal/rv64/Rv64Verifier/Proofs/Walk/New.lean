import Rv64Verifier.Proofs.Walk.Start

/-!
# `walk`: `Transcript::new`

From `keccak_f`'s call at `0x800010e4` to `next_scalars`' at `0x80001130`: the seed permuted in
place (`keccakStep`), copied to `S - 800` (`copyStep`), the waiting scalars zeroed at `S - 928`
(`zeroStep`), the proof's address stored at `tp` and the 328 bytes from `S - 928` copied into the
sponge (`spongeStep`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The seed as a state. -/
def seedState (s : MachineState) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦ UInt64.ofBitVec (seedWord s i)

/-- The registers the start keeps: the proof, the public input's words, the result, the
`Bytecode`. -/
structure Regs (s u : MachineState) : Prop where
  x19 : u.getReg .x19 = s.getMem (s.getReg .x12 + 8)
  x20 : u.getReg .x20 = s.getMem (s.getReg .x12 + 24)
  x21 : u.getReg .x21 = s.getMem (s.getReg .x12)
  x22 : u.getReg .x22 = s.getMem (s.getReg .x12 + 16)
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x11

theorem Regs.keep {s u v : MachineState} (h : Regs s u)
    (hk : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24], v.getReg r = u.getReg r) : Regs s v :=
  ⟨(hk _ (by decide)).trans h.x19, (hk _ (by decide)).trans h.x20, (hk _ (by decide)).trans h.x21,
    (hk _ (by decide)).trans h.x22, (hk _ (by decide)).trans h.x23, (hk _ (by decide)).trans h.x24⟩

theorem Seed.regs {s u : MachineState} (h : Seed s u) : Regs s u :=
  ⟨h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

theorem mem_six {r : Reg} (h : r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24]) : r ∈ calleeSaved := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The stack below the frame, `m` bytes for a callee. -/
theorem calleeStack {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {m : Nat}
    (hm : m ≤ 8736) (hm8 : m % 8 = 0) : StackOk u m :=
  (hpre.stack.sub 2656 h.sp (by rw [stack_eq]; omega) (by decide) hm8 (by decide)
    (by decide)).toStackOk

theorem stackLo_callee {s u : MachineState} (h : Inv s u) (m : Nat) :
    stackLo u m = s.getReg .x2 - 2656 - BitVec.ofNat 64 m := by
  simp only [stackLo, h.sp]

/-- A callee's byte frame in the frame (`n` bytes from `S - k`) and its `m`-byte stack below. -/
theorem stepOfBytes {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u) {k n m : Nat}
    (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2656) (hm : m ≤ 8736)
    (hf : DFrame u v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 k) n ∨
      Within a (stackLo u m) m)
    (sp : v.getReg .x2 = u.getReg .x2) : Step s u v (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  rw [stackLo_callee h] at hf
  have hd : DFrame u v (Below s u v (s.getReg .x2 - BitVec.ofNat 64 k) n) := hf.mono fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1, hm]))
  have he : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1, hk1, hk2, hm])
  exact ⟨hd, ⟨he ▸ h.heap.lo, he ▸ h.heap.hi⟩, he.ge, sp⟩

/-! ## `keccak_f` of the seed -/

structure Permuted (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  x9 : v.getReg .x9 = s.getReg .x13
  state : stateAt v (s.getReg .x2 - 1344) = keccakF1600 (seedState s)

theorem keccakStep (hK : Contracts.KeccakFSpec) {s u : MachineState} (hpre : WalkPre s)
    (hpc : u.pc = 0x800010e4) (h : Seed s u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x800010f0 ∧ Permuted s v) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hro := hpre.stack.rodata
  rw [stackLo_eq, stack_eq] at hro
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800010e4_spec hpc trivial
  have k₀ := b800010e4_keeps h₀
  have hm₀ := b800010e4_mem_same h₀
  have x2₀ : w₀.getReg .x2 = s.getReg .x2 - 2656 := (k₀ .x2 (by decide)).trans h.inv.sp
  have x10₀ : w₀.getReg .x10 = s.getReg .x2 - 1344 := by
    rw [b800010e4_x10 h₀, h.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have I₀ := h.inv.same hm₀ (k₀ .x2 (by decide))
  have hkp : Contracts.KeccakFPre w₀ := {
    state := by rw [x10₀]; valid_sub hval [hb1]
    stack := calleeStack hpre I₀ (by decide) (by decide)
    stateStack := by rw [x10₀, stackLo_callee I₀]; addr_omega [hb1]
    tables := keccakTables_of_rodata (I₀.rodata hpre)
    tablesState := by rw [x10₀]; addr_omega [hb1, hro]
    tablesStack := by rw [stackLo_callee I₀]; addr_omega [hb1, hro] }
  obtain ⟨v, hr₁, ⟨hpc₁, hp₁, post₁⟩ | hd⟩ := hK.call hr₀ (b800010e4_pc h₀) hkp
  swap
  · exact ⟨v, hr₁, Or.inr hd⟩
  have val := stateAt_keccakF post₁.value
  rw [x10₀] at val
  have fr := post₁.frame
  rw [x10₀] at fr
  have st : Step s w₀ v (s.getReg .x2 - BitVec.ofNat 64 1344) 200 :=
    stepOfBytes hpre I₀ (by omega) (by omega) (by decide)
      ((DFrame.of_two fr).mono fun _ ha ↦ ha) (hp₁.reg .x2)
  have hs : stateAt w₀ (s.getReg .x2 - 1344) = seedState s := by
    apply Vector.ext
    intro j hj
    simp only [stateAt, seedState, Vector.getElem_ofFn]
    rw [hm₀, show s.getReg .x2 - 1344 + BitVec.ofNat 64 (8 * j) =
      s.getReg .x2 - BitVec.ofNat 64 (1344 - 8 * j) by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]]
    exact congrArg UInt64.ofBitVec (h.seed j hj)
  refine ⟨v, hr₁, Or.inl ⟨by rw [hpc₁, returnAddress_eq, b800010e4_x1 h₀]; decide, {
    inv := I₀.after hpre (inFrame hpre (by omega) (by omega)) st
    regs := h.regs.keep fun r hr ↦ by rw [hp₁.reg r (mem_six hr), k₀ r (mem_of_mem hr _)]
    x9 := by rw [hp₁.reg .x9, k₀ .x9 (by decide), h.x9]
    state := by rw [val, hs] }⟩⟩

/-! ## `memcpy` of the state, `memset` of the waiting scalars -/

structure Copied (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  x9 : v.getReg .x9 = s.getReg .x13
  state : stateAt v (s.getReg .x2 - 800) = keccakF1600 (seedState s)

theorem copyStep (hMC : MemcpySpec 0x800126e4) {s u : MachineState} (hpre : WalkPre s)
    (hpc : u.pc = 0x800010f0) (h : Permuted s u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x80001104 ∧ Copied s v) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800010f0_spec hpc trivial
  have k₀ := b800010f0_keeps h₀
  have hm₀ := b800010f0_mem_same h₀
  have I₀ := h.inv.same hm₀ (k₀ .x2 (by decide))
  have x10₀ : w₀.getReg .x10 = s.getReg .x2 - 800 := by
    rw [b800010f0_x10 h₀, h.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₀ : w₀.getReg .x11 = s.getReg .x2 - 1344 := by
    rw [b800010f0_x11 h₀, h.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x12₀ : (w₀.getReg .x12).toNat = 200 := by rw [b800010f0_x12 h₀]; rfl
  have hmc : MemcpyPre w₀ := {
    dst := by rw [x10₀, x12₀]; addr_omega [hb1, hb2]
    src := by rw [x11₀, x12₀]; addr_omega [hb1, hb2]
    apart := by rw [x10₀, x11₀, x12₀]; addr_omega [hb1]
    stack := calleeStack hpre I₀ (by decide) (by decide)
    dstStack := by rw [x10₀, x12₀, stackLo_callee I₀]; addr_omega [hb1]
    srcStack := by rw [x11₀, x12₀, stackLo_callee I₀]; addr_omega [hb1] }
  obtain ⟨v, hr₁, ⟨hpc₁, hp₁, post₁⟩ | hd⟩ := hMC.call hr₀ (b800010f0_pc h₀) hmc
  swap
  · exact ⟨v, hr₁, Or.inr hd⟩
  have by₁ := post₁.bytes
  have fr₁ := post₁.frame
  rw [x10₀, x11₀, x12₀] at by₁
  rw [x10₀, x12₀] at fr₁
  have st : Step s w₀ v (s.getReg .x2 - BitVec.ofNat 64 800) 200 :=
    stepOfBytes hpre I₀ (by omega) (by omega) (by decide)
      ((DFrame.of_byteFrame fr₁).mono fun _ ha ↦ ha) (hp₁.reg .x2)
  refine ⟨v, hr₁, Or.inl ⟨by rw [hpc₁, returnAddress_eq, b800010f0_x1 h₀]; decide, {
    inv := I₀.after hpre (inFrame hpre (by omega) (by omega)) st
    regs := h.regs.keep fun r hr ↦ by rw [hp₁.reg r (mem_six hr), k₀ r (mem_of_mem hr _)]
    x9 := by rw [hp₁.reg .x9, k₀ .x9 (by decide), h.x9]
    state := ?_ }⟩⟩
  rw [← h.state]
  refine stateAt_congr fun j hj ↦ ?_
  rw [getMem_eq_of_bytesAt by₁ (by addr_omega [hb1, hb3]) (by addr_omega [hb1, hb3]) (by omega)
    (by omega), hm₀]

structure Zeroed (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  x9 : v.getReg .x9 = s.getReg .x13
  state : stateAt v (s.getReg .x2 - 800) = keccakF1600 (seedState s)
  zeros : ∀ j < 16, v.getMem (s.getReg .x2 - 928 + BitVec.ofNat 64 (8 * j)) = 0

theorem zeroStep (hMS : MemsetSpec 0x800126f4) {s u : MachineState} (hpre : WalkPre s)
    (hpc : u.pc = 0x80001104) (h : Copied s u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x80001118 ∧ Zeroed s v) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80001104_spec hpc trivial
  have k₀ := b80001104_keeps h₀
  have hm₀ := b80001104_mem_same h₀
  have I₀ := h.inv.same hm₀ (k₀ .x2 (by decide))
  have x10₀ : w₀.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b80001104_x10 h₀, h.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x12₀ : (w₀.getReg .x12).toNat = 128 := by rw [b80001104_x12 h₀]; rfl
  obtain ⟨v, hr₁, ⟨hpc₁, hp₁, post₁⟩ | hd⟩ := hMS.call hr₀ (b80001104_pc h₀)
    (show Mapped _ _ by rw [x10₀, x12₀]; addr_omega [hb1, hb2])
  swap
  · exact ⟨v, hr₁, Or.inr hd⟩
  have by₁ := post₁.bytes
  have fr₁ := post₁.frame
  rw [x10₀, x12₀, b80001104_x11 h₀] at by₁
  rw [x10₀, x12₀] at fr₁
  have st : Step s w₀ v (s.getReg .x2 - BitVec.ofNat 64 928) 128 :=
    stepOfBytes hpre I₀ (m := 0) (by omega) (by omega) (by decide)
      ((DFrame.of_byteFrame fr₁).mono fun _ ha ↦ Or.inl ha) (hp₁.reg .x2)
  refine ⟨v, hr₁, Or.inl ⟨by rw [hpc₁, returnAddress_eq, b80001104_x1 h₀]; decide, {
    inv := I₀.after hpre (inFrame hpre (by omega) (by omega)) st
    regs := h.regs.keep fun r hr ↦ by rw [hp₁.reg r (mem_six hr), k₀ r (mem_of_mem hr _)]
    x9 := by rw [hp₁.reg .x9, k₀ .x9 (by decide), h.x9]
    state := ?_
    zeros := fun j hj ↦ Transcript.Duplex.getMem_zero_of_bytesAt (by decide) by₁
      (by addr_omega [hb1, hb3]) (by omega) (by omega) }⟩⟩
  rw [← h.state]
  refine stateAt_congr fun j hj ↦ ?_
  rw [st.word hpre (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj]), hm₀]

end Rv64Verifier.Proofs.Walk
