import Rv64Verifier.Proofs.Main.IvHash

/-!
# The IV, and `IvStage`

`0x800003f4` hashes `TAG` and the table's bytes into `msp + 320` (`keccak_hash`, `iv_hash`);
`iv_stage` chains the prologue, the buffer, `TAG`, the copy and the hash.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Blocks.F3 Rv64Verifier.Contracts

theorem bytesAt_contracts (s : MachineState) (a : Word) (n : Nat) :
    Contracts.bytesAt s a n = Runtime.bytesAt s a n := rfl

/-- **`keccak_hash`, to `AfterIv`.** -/
theorem iv_hash {s u : MachineState} {words : List Word} (h : IvC s words u) :
    ∃ v, Reaches Image.code u v ∧ (AfterIv s words v ∨ Dead Image.code v) := by
  have hsp := h.inv.sp
  have hbuf := h.buf
  have hhi := h.inv.heap.hi
  simp only [heapStart, heapEnd] at hbuf hhi
  set n := (words.getD 0 0).toNat with hn
  set p := u.getReg .x9 with hp
  have hfit := h.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.len
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800003f4_spec h.pc trivial
  have k₁ := b800003f4_keeps h₁
  have m₁ := b800003f4_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hinv₁ := h.inv.same m₁ hsp₁
  have e10 : t₁.getReg .x10 = msp + 320 := by rw [b800003f4_x10 h₁, hsp]
  have e11 : t₁.getReg .x11 = p := b800003f4_x11 h₁
  have t12 : (t₁.getReg .x12).toNat = 8 * n + 9 := by
    rw [k₁ .x12 (by decide), h.x12, BitVec.toNat_ofNat]; omega
  obtain ⟨t₂, hr₂, hout⟩ := Hash.keccakHash t₁ (b800003f4_pc h₁) {
    out := ⟨by rw [e10]; decide, fun i hi ↦ by
      rw [e10]; exact Mapped.valid (n := 32) (by simp only [Runtime.Mapped]; decide) hi⟩
    outAligned := by rw [e10]; decide
    data := by rw [e11, t12]; simp only [Runtime.Mapped]; omega
    stack := stackOk_msp hsp₁ (by decide) (by decide)
    outStack := by rw [e10]; simp only [stackLo, hsp₁]; addr_omega []
    dataStack := by rw [e11, t12]; simp only [stackLo, hsp₁]; addr_omega [hbuf, hhi]
    tables := Transcript.keccakTables_of_rodata hinv₁.rodata
    tablesStack := by simp only [stackLo, hsp₁]; addr_omega [] }
  rcases hout with ⟨hpc₂, hpres₂, hpost₂⟩ | hd
  swap
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr hd⟩
  have hsp₂ : t₂.getReg .x2 = msp := (hpres₂.reg .x2).trans hsp₁
  have hW : ∀ a, ¬ (Within a (t₁.getReg .x10) 32 ∨
      Within a (stackLo t₁ keccakHashStack) keccakHashStack) → t₂.getMem a = t₁.getMem a :=
    fun a ha ↦ hpost₂.frame a (fun h' ↦ ha (Or.inl h')) (fun h' ↦ ha (Or.inr h'))
  have hnx : t₂.getMem nextAddr = t₁.getMem nextAddr := hW _ fun hw ↦ by
    rw [e10] at hw; simp only [stackLo, hsp₁] at hw; rcases hw with hw | hw <;> addr_omega [hw]
  have hheap : HeapOk t₂ := ⟨by simp only [heapNext, hnx, m₁]; exact h.inv.heap.lo,
    by simp only [heapNext, hnx, m₁]; exact h.inv.heap.hi⟩
  have hinv₂ : MInv s words t₂ := hinv₁.frameD hW hsp₂ hheap fun a ha ↦ by
    rcases ha with ha | ha
    · rw [e10] at ha
      intro hk; simp only [Kept, inputBase_eq] at hk
      rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
    · exact not_kept_stack h.inv.fits hsp₁ (by decide) ha
  have keep : ∀ k : Nat, k + 8 ≤ 320 → t₂.getMem (msp + BitVec.ofNat 64 k) =
      u.getMem (msp + BitVec.ofNat 64 k) := by
    intro k hk
    rw [hW _ fun hw ↦ by
      rw [e10] at hw; simp only [stackLo, hsp₁] at hw; rcases hw with hw | hw <;> addr_omega [hw, hk],
      m₁]
  refine ⟨t₂, hr₁.trans hr₂, Or.inl ⟨hinv₂, ?_, hlen, ?_, ?_, ?_, ?_⟩⟩
  · rw [hpc₂, returnAddress, b800003f4_x1 h₁]; decide
  · rw [hpres₂.reg .x19, k₁ .x19 (by decide), h.x19]
  · have k88 : t₂.getMem (msp + 88) = u.getMem (msp + 88) := keep 88 (by decide)
    rw [k88]; exact h.ptr
  · have k96 : t₂.getMem (msp + 96) = u.getMem (msp + 96) := keep 96 (by decide)
    rw [k96]; exact h.rest
  · have := hpost₂.value
    rw [e10, e11, t12, bytesAt_contracts, bytesAt_contracts, bytesAt_same m₁, Nat.add_comm,
      h.bytes] at this
    exact this

/-- **The prologue and the IV.** -/
theorem iv_stage : IvStage := by
  intro s words hpc hpre hfit
  obtain ⟨u₁, hr₁, hA | hd⟩ := iv_entry hpc hpre hfit
  swap
  · exact ⟨u₁, hr₁, Or.inr hd⟩
  obtain ⟨u₂, hr₂, hB | hd⟩ := iv_alloc hA
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨u₃, hr₃, hT⟩ := iv_tag hB
  obtain ⟨u₄, hr₄, hC | hd⟩ := iv_copy hT
  swap
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩
  obtain ⟨u₅, hr₅, hv⟩ := iv_hash hC
  exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), hv⟩

end Rv64Verifier.Proofs.Main
