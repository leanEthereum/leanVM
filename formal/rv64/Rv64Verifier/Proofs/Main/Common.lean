import Rv64Verifier.Proofs.Main.Stages
import Rv64Verifier.Proofs.Runtime.Step
import Rv64Verifier.Proofs.Runtime.Memcpy
import Rv64Verifier.Blocks.F3

/-!
# What `main`'s stages share

The aborts (`abort`: each `halt(ABORT)` and the trap after it are dead ends), the stack below
`msp` (`rtStack_msp`), `MInv` across a step whose writes miss the frame's saved registers, the
input and `.rodata` (`MInv.frame`), bytes of doublewords (`bytesAt_add`, `bytesAt_dwords`), and a
byte store at any address (`sb_step`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Blocks.F3

/-! ## Aborts -/

theorem halt_at {A E : Word} {k : Nat} {x : Sym.Expect}
    (hs : Sym.BlockSpec Image.code A k (fun s ↦ Sym.Oblig.all s x.obl) x.Holds)
    (hobl : ∀ s, Sym.Oblig.all s x.obl) (hpc : ∀ s t, x.Holds s t → t.pc = E)
    (h5 : ∀ s t, x.Holds s t → t.getReg .x5 = 0) (h10 : ∀ s t, x.Holds s t → t.getReg .x10 = 2)
    (hf : Image.code.fetch E = some (.base .ECALL)) {u : MachineState} (hu : u.pc = A) :
    ∃ v, Reaches Image.code u v ∧ Dead Image.code v := by
  obtain ⟨v, hr, hx⟩ := Sym.BlockSpec.reaches hs hu (hobl u)
  exact ⟨v, hr, dead_of_halt (by rw [hpc u v hx]; exact hf) (h5 u v hx)
    (by rw [h10 u v hx]; decide)⟩

theorem ecall_e18 : Image.code.fetch 0x80000e20 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e28 : Image.code.fetch 0x80000e30 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e38 : Image.code.fetch 0x80000e40 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e48 : Image.code.fetch 0x80000e50 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e58 : Image.code.fetch 0x80000e60 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e68 : Image.code.fetch 0x80000e70 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e78 : Image.code.fetch 0x80000e80 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e88 : Image.code.fetch 0x80000e90 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_e98 : Image.code.fetch 0x80000ea0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_ea8 : Image.code.fetch 0x80000eb0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_eb8 : Image.code.fetch 0x80000ec0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_ec8 : Image.code.fetch 0x80000ed0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_ed8 : Image.code.fetch 0x80000ee0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

theorem ecall_ee8 : Image.code.fetch 0x80000ef0 = some (.base .ECALL) :=
  fetch_of (by decide +kernel)

/-- `main`'s `halt(ABORT)`s, and the trap at `0x80000ed4`. -/
theorem abort {u : MachineState}
    (hu : u.pc ∈ ([0x80000e18, 0x80000e28, 0x80000e38, 0x80000e48, 0x80000e58, 0x80000e68,
      0x80000e78, 0x80000e88, 0x80000e98, 0x80000ea8, 0x80000eb8, 0x80000ec8, 0x80000ed4,
      0x80000ed8, 0x80000ee8] : List Word)) :
    ∃ v, Reaches Image.code u v ∧ Dead Image.code v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact halt_at b80000e18_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e18_pc h)
      (fun _ _ h ↦ b80000e18_x5 h) (fun _ _ h ↦ b80000e18_x10 h) ecall_e18 h
  · exact halt_at b80000e28_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e28_pc h)
      (fun _ _ h ↦ b80000e28_x5 h) (fun _ _ h ↦ b80000e28_x10 h) ecall_e28 h
  · exact halt_at b80000e38_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e38_pc h)
      (fun _ _ h ↦ b80000e38_x5 h) (fun _ _ h ↦ b80000e38_x10 h) ecall_e38 h
  · exact halt_at b80000e48_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e48_pc h)
      (fun _ _ h ↦ b80000e48_x5 h) (fun _ _ h ↦ b80000e48_x10 h) ecall_e48 h
  · exact halt_at b80000e58_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e58_pc h)
      (fun _ _ h ↦ b80000e58_x5 h) (fun _ _ h ↦ b80000e58_x10 h) ecall_e58 h
  · exact halt_at b80000e68_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e68_pc h)
      (fun _ _ h ↦ b80000e68_x5 h) (fun _ _ h ↦ b80000e68_x10 h) ecall_e68 h
  · exact halt_at b80000e78_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e78_pc h)
      (fun _ _ h ↦ b80000e78_x5 h) (fun _ _ h ↦ b80000e78_x10 h) ecall_e78 h
  · exact halt_at b80000e88_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e88_pc h)
      (fun _ _ h ↦ b80000e88_x5 h) (fun _ _ h ↦ b80000e88_x10 h) ecall_e88 h
  · exact halt_at b80000e98_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000e98_pc h)
      (fun _ _ h ↦ b80000e98_x5 h) (fun _ _ h ↦ b80000e98_x10 h) ecall_e98 h
  · exact halt_at b80000ea8_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000ea8_pc h)
      (fun _ _ h ↦ b80000ea8_x5 h) (fun _ _ h ↦ b80000ea8_x10 h) ecall_ea8 h
  · exact halt_at b80000eb8_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000eb8_pc h)
      (fun _ _ h ↦ b80000eb8_x5 h) (fun _ _ h ↦ b80000eb8_x10 h) ecall_eb8 h
  · exact halt_at b80000ec8_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000ec8_pc h)
      (fun _ _ h ↦ b80000ec8_x5 h) (fun _ _ h ↦ b80000ec8_x10 h) ecall_ec8 h
  · exact ⟨u, Reaches.refl u, dead_of_fetch (by rw [h]; exact Option.isNone_iff_eq_none.mp (by decide +kernel))⟩
  · exact halt_at b80000ed8_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000ed8_pc h)
      (fun _ _ h ↦ b80000ed8_x5 h) (fun _ _ h ↦ b80000ed8_x10 h) ecall_ed8 h
  · exact halt_at b80000ee8_spec (fun _ ↦ trivial) (fun _ _ h ↦ b80000ee8_pc h)
      (fun _ _ h ↦ b80000ee8_x5 h) (fun _ _ h ↦ b80000ee8_x10 h) ecall_ee8 h

/-! ## The stack below `msp` -/

theorem validRange_of {a : Word} {n : Nat} (h1 : 0xa0000000 ≤ a.toNat)
    (h2 : a.toNat + 8 * n ≤ 0xc0000000) (h3 : a.toNat % 8 = 0) : ValidMemRange a n := by
  intro i hi
  exact (Sym.validAccess_eight _).mpr (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-- A callee's stack of up to `walkStack` bytes below `msp`. -/
theorem rtStack_msp {u : MachineState} (hsp : u.getReg .x2 = msp) {k : Nat} (hk : k ≤ walkStack)
    (h8 : k % 8 = 0) : RtStack u k := by
  simp only [walkStack] at hk
  have hlo : (stackLo u k).toNat = 0xbffffdb0 - k := by
    simp only [stackLo, hsp]; addr_omega [hk]
  refine ⟨⟨validRange_of (by omega) (by omega) (by omega), by rw [hsp]; decide⟩, ?_, ?_, ?_⟩
  · simp only [heapEnd]; omega
  · addr_omega [hlo, hk]
  · addr_omega [hlo, hk]

theorem stackOk_msp {u : MachineState} (hsp : u.getReg .x2 = msp) {k : Nat} (hk : k ≤ walkStack)
    (h8 : k % 8 = 0) : StackOk u k :=
  (rtStack_msp hsp hk h8).toStackOk

/-! ## `MInv` across a step -/

theorem rodataWords_aligned' : (rodataWords.all fun q ↦ q.1.toNat % 8 == 0) = true := by
  decide +kernel

/-- What `main` keeps: its saved registers, the input and `.rodata`. -/
@[rv_addr] def Kept (words : List Word) (a : Word) : Prop :=
  Within a (msp + 472) 104 ∨ Within a inputBase (8 * words.length) ∨ Within a rodataBase rodataSize

theorem MInv.frame {s u v : MachineState} {words : List Word} {W : Word → Prop}
    (h : MInv s words u) (hW : ByteFrame u v W) (hsp : v.getReg .x2 = msp) (hheap : HeapOk v)
    (hk : ∀ a, W a → ¬ Kept words a) : MInv s words v where
  fits := h.fits
  sp := hsp
  slots := by
    intro p hp
    rw [← h.slots p hp]
    have hb : 472 ≤ p.1 ∧ p.1 + 8 ≤ 576 := by
      revert hp; simp only [mainSlots, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        decide
    obtain ⟨h1, h2⟩ := hb
    exact hW.getMem fun i hi hw ↦ hk _ hw (Or.inl (by addr_omega [h1, h2, hi]))
  input := by
    intro i hi
    rw [← h.input i hi]
    have hf := h.fits
    have hib : inputBase.toNat = 0x10000000 := rfl
    exact hW.getMem fun j hj hw ↦ hk _ hw (Or.inr (Or.inl (by addr_omega [hi, hj, hf, hib])))
  heap := hheap
  rodata := by
    intro p hp
    have hw' := within_of_mem_rodataWords hp
    have h8 : p.1.toNat % 8 = 0 := by
      simpa using List.all_eq_true.mp rodataWords_aligned' p hp
    rw [hW.getMem fun i hi hw ↦ hk _ hw (Or.inr (Or.inr (by addr_omega [hw', h8, hi])))]
    exact h.rodata p hp

theorem inputBase_eq : inputBase = 0x10000000 := rfl

/-- A heap address is not `Kept`. -/
theorem not_kept_heap {words : List Word} (hf : words.length ≤ inputWords) {a : Word}
    (h : heapStart ≤ a.toNat ∧ a.toNat < heapEnd) : ¬ Kept words a := by
  intro hk
  simp only [Kept, inputBase_eq] at hk
  rcases hk with hk | hk | hk <;> addr_omega [hk, h, hf]

theorem not_kept_next {words : List Word} (hf : words.length ≤ inputWords) {a : Word}
    (h : Within a nextAddr 8) : ¬ Kept words a := by
  intro hk
  simp only [Kept, inputBase_eq] at hk
  rcases hk with hk | hk | hk <;> addr_omega [hk, h, hf]

/-- A callee's stack below `msp` is not `Kept`. -/
theorem not_kept_stack {words : List Word} (hf : words.length ≤ inputWords) {u : MachineState}
    (hsp : u.getReg .x2 = msp) {k : Nat} (hk : k ≤ walkStack) {a : Word}
    (h : Within a (stackLo u k) k) : ¬ Kept words a := by
  intro hk'
  simp only [Kept, inputBase_eq] at hk'
  simp only [stackLo, hsp] at h
  rcases hk' with hk' | hk' | hk' <;> addr_omega [hk', h, hf, hk]

/-! ## Bytes -/

theorem bytesAt_add (s : MachineState) (a : Word) (m n : Nat) :
    bytesAt s a (m + n) = bytesAt s a m ++ bytesAt s (a + BitVec.ofNat 64 m) n := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

theorem toLeBytes_eq (w : Word) :
    Model.toLeBytes w = (List.range 8).map fun i ↦ extractByte w i := by
  simp only [Model.toLeBytes, extractByte, Nat.mul_comm]

/-- The bytes of `k` aligned doublewords. -/
theorem bytesAt_dwords (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) :
    ∀ k, a.toNat + 8 * k < 2 ^ 64 → bytesAt s a (8 * k) =
      ((List.range k).map fun i ↦ s.getMem (a + BitVec.ofNat 64 (8 * i))).flatMap Model.toLeBytes
  | 0, _ => rfl
  | k + 1, hk => by
    rw [show 8 * (k + 1) = 8 * k + 8 by ring, bytesAt_add, bytesAt_dwords s ha k (by omega),
      List.range_succ, List.map_append, List.flatMap_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hb : (a + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [toLeBytes_eq]
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    exact byteAt_add hb hi

/-! ## A byte store -/

theorem sb_step {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hf : Image.code.fetch s.pc = some (.base (.SB rs1 rs2 off)))
    (hv : isValidMemAddr (s.getReg rs1 + signExtend12 off) = true) :
    ∃ t, Reaches Image.code s t ∧ t.pc = s.pc + 4 ∧ (∀ r, t.getReg r = s.getReg r) ∧
      byteAt t (s.getReg rs1 + signExtend12 off) = (s.getReg rs2).truncate 8 ∧
      ByteFrame s t (· = s.getReg rs1 + signExtend12 off) := by
  obtain ⟨t, hst, hpc, hr, hb, hu⟩ := step_sb hf hv
  refine ⟨t, ⟨1, hst⟩, hpc, hr, by rw [hb]; simp, fun a ha ↦ ?_, hu⟩
  rw [hb]
  simp [ha]

end Rv64Verifier.Proofs.Main
