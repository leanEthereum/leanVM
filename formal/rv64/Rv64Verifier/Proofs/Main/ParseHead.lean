import Rv64Verifier.Proofs.Main.HeapSame
import Rv64Verifier.Proofs.Main.IvHash
import Rv64Verifier.Proofs.Bytecode.Digest

/-!
# The `Bytecode` and the public input

`0x80000a20` moves the four `Vec`s and the table's length into the `Bytecode` at `msp + 104` and
copies the IV to `msp + 208` (`memcpy`); `0x80000a9c` reads the public input into `msp + 240`
(`Input::digest`) (`parse_head : ParseHead`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Blocks.F3

theorem bytesAt_dframe {s t : MachineState} {p : Word} {n : Nat}
    (h : ∀ i < n, t.getMem ((p + BitVec.ofNat 64 i) &&& ~~~7#64) =
      s.getMem ((p + BitVec.ofNat 64 i) &&& ~~~7#64)) : bytesAt t p n = bytesAt s p n :=
  bytesAt_eq_iff.mpr fun i hi ↦ by rw [byteAt_eq, byteAt_eq, h i hi]

/-- `newRust`'s length and IV. -/
theorem newRust_len_iv {table : List Word} {bc : Model.BytecodeRust}
    (h : Model.newRust table = some bc) :
    bc.len = table.length ∧ bc.fiatShamirIv = Model.fiatShamirIvRust table := by
  unfold Model.newRust at h
  obtain ⟨st, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl⟩

theorem tbl_length {words : List Word} (h : (words.getD 0 0).toNat + 1 ≤ words.length) :
    (tbl words).length = (words.getD 0 0).toNat := by
  simp only [tbl, List.length_take, List.length_drop]; omega

theorem ptr_add32 (n : Nat) :
    inputBase + BitVec.ofNat 64 (8 * (n + 1)) + 32 = inputBase + BitVec.ofNat 64 (8 * (n + 5)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (32 : Word).toNat = 32 := rfl
  omega

/-- **The `Bytecode` and the public input.** -/
theorem parse_head : ParseHead := by
  intro s words u h
  have hsp := h.inv.sp
  have hfit := h.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.len
  set n := (words.getD 0 0).toNat with hn
  obtain ⟨bc, hnew, hv⟩ := h.vecs
  have hhi := h.inv.heap.hi
  -- the assembly
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80000a20_spec h.pc (by rv_eval [hsp, msp]; decide)
  have k₁ := b80000a20_keeps h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hfr₁ := b80000a20_frame h₁ (by rw [hsp]; decide)
  have hbf₁ : ByteFrame u t₁ (Within · (u.getReg .x2 + 104) 104) :=
    ByteFrame.of_memFrame hfr₁ (by rw [hsp]; decide) (by decide) (h₁.unaligned (by rv_eval [hsp, msp]))
  have K01 : ∀ a : Word, ¬ Within a (msp + 104) 104 → t₁.getMem a = u.getMem a := by
    intro a ha; exact hfr₁ a (by rw [hsp]; exact ha)
  have hnx₁ : t₁.getMem nextAddr = u.getMem nextAddr := K01 _ (by addr_omega [])
  have heap₁ : HeapOk t₁ := ⟨by simp only [heapNext, hnx₁]; exact h.inv.heap.lo,
    by simp only [heapNext, hnx₁]; exact hhi⟩
  have hinv₁ : MInv s words t₁ := h.inv.frame hbf₁ hsp₁ heap₁ fun a ha hk ↦ by
    rw [hsp] at ha; simp only [Kept, inputBase_eq] at hk
    rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
  have hs₁ : HeapSame u t₁ := fun a ha ↦ K01 a (by simp only [heapEnd] at ha; addr_omega [ha])
  -- the IV's copy
  have e10 : t₁.getReg .x10 = msp + 208 := by rw [b80000a20_x10 h₁, hsp]
  have e11 : t₁.getReg .x11 = msp + 320 := by rw [b80000a20_x11 h₁, hsp]
  have e12 : (t₁.getReg .x12).toNat = 32 := by rw [b80000a20_x12 h₁]; rfl
  obtain ⟨t₂, hr₂, hout⟩ := Runtime.memcpy t₁ (b80000a20_pc h₁) {
    dst := by rw [e10, e12]; simp only [Runtime.Mapped]; decide
    src := by rw [e11, e12]; simp only [Runtime.Mapped]; decide
    apart := by rw [e10, e11, e12]; addr_omega []
    stack := stackOk_msp hsp₁ (by decide) (by decide)
    dstStack := by rw [e10, e12]; simp only [stackLo, hsp₁]; addr_omega []
    srcStack := by rw [e11, e12]; simp only [stackLo, hsp₁]; addr_omega [] }
  rcases hout with ⟨hpc₂, hpres₂, hpost₂⟩ | hd
  swap
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr hd⟩
  have hsp₂ : t₂.getReg .x2 = msp := (hpres₂.reg .x2).trans hsp₁
  have hW₂ : ∀ a, (Within a (t₁.getReg .x10) (t₁.getReg .x12).toNat ∨
      Within a (stackLo t₁ memcpyStack) memcpyStack) ↔
      (Within a (msp + 208) 32 ∨ Within a (msp - 16) 16) := by
    intro a; rw [e10, e12]; simp only [stackLo, hsp₁, memcpyStack]; rfl
  have K12 : ∀ a : Word, (∀ i < 8, ¬ (Within (a + BitVec.ofNat 64 i) (msp + 208) 32 ∨
      Within (a + BitVec.ofNat 64 i) (msp - 16) 16)) → t₂.getMem a = t₁.getMem a :=
    fun a ha ↦ hpost₂.frame.getMem fun i hi hw ↦ ha i hi ((hW₂ _).mp hw)
  have hnx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr :=
    K12 _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi]
  have heap₂ : HeapOk t₂ := ⟨by simp only [heapNext, hnx₂]; exact heap₁.lo,
    by simp only [heapNext, hnx₂]; exact heap₁.hi⟩
  have hinv₂ : MInv s words t₂ := hinv₁.frame hpost₂.frame hsp₂ heap₂ fun a ha hk ↦ by
    rw [hW₂] at ha; simp only [Kept, inputBase_eq] at hk
    rcases ha with ha | ha <;> rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
  have hs₂ : HeapSame t₁ t₂ := fun a ha ↦ K12 a fun i hi hw ↦ by
    simp only [heapEnd] at ha; rcases hw with hw | hw <;> addr_omega [hw, hi, ha]
  -- `Input::digest`
  have hpc₂' : t₂.pc = 0x80000a9c := by rw [hpc₂, returnAddress, b80000a20_x1 h₁]; decide
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80000a9c_spec hpc₂' trivial
  have k₃ := b80000a9c_keeps h₃
  have m₃ := b80000a9c_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hsp₂]
  have f10 : t₃.getReg .x10 = msp + 240 := by rw [b80000a9c_x10 h₃, hsp₂]
  have f11 : t₃.getReg .x11 = msp + 88 := by rw [b80000a9c_x11 h₃, hsp₂]
  have g88 : t₃.getMem (msp + 88) = u.getMem (msp + 88) := by
    rw [m₃, K12 _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi],
      K01 _ (by addr_omega [])]
  have g96 : t₃.getMem (msp + 88 + 8) = u.getMem (msp + 96) := by
    rw [m₃, K12 _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi],
      K01 _ (by addr_omega [])]
    rfl
  have hptr := h.ptr
  have hrest := h.rest
  obtain ⟨t₄, hr₄, hout⟩ := digest_spec t₃ (b80000a9c_pc h₃) {
    out := by rw [f10]; simp only [Runtime.Mapped]; decide
    outAlign := by rw [f10]; decide
    self := by rw [f11]; simp only [Runtime.Mapped]; decide
    selfAlign := by rw [f11]; decide
    stack := stackOk_msp hsp₃ (by decide) (by decide)
    outSelf := by rw [f10, f11]; addr_omega []
    outStack := by rw [f10]; simp only [stackLo, hsp₃]; addr_omega []
    selfStack := by rw [f11]; simp only [stackLo, hsp₃]; addr_omega []
    words := fun h4 ↦ by
      simp only [inputLen, inputPtr, f11, g96] at h4 ⊢
      rw [g88, hptr]
      have hib : inputBase.toNat = 0x10000000 := rfl
      refine ⟨?_, ?_, ?_⟩
      · simp only [Runtime.Mapped]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hib]; omega
      · rw [BitVec.toNat_add, BitVec.toNat_ofNat, hib]; omega
      · simp only [stackLo, hsp₃]; addr_omega [hib, hfit, hlen, hn] }
  rcases hout with ⟨hpc₄, hpres₄, hp₄⟩ | hd
  swap
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩
  have hsp₄ : t₄.getReg .x2 = msp := (hpres₄.reg .x2).trans hsp₃
  have K34 : ∀ a, ¬ Within a (msp + 240) 32 → ¬ Within a (msp + 88) 16 →
      ¬ Within a (msp - 96) 96 → t₄.getMem a = t₃.getMem a := by
    intro a h1 h2 h3
    exact hp₄.frame a (by rw [f10]; exact h1) (by rw [f11]; exact h2)
      (by simp only [stackLo, hsp₃, digestStack]; exact h3)
  have hn4 : t₄.getMem nextAddr = u.getMem nextAddr := by
    rw [K34 _ (by addr_omega []) (by addr_omega []) (by addr_omega []), m₃, hnx₂, hnx₁]
  have heap₄ : HeapOk t₄ := ⟨by simp only [heapNext, hn4]; exact h.inv.heap.lo,
    by simp only [heapNext, hn4]; exact hhi⟩
  have hinv₃ := hinv₂.same m₃ hsp₃
  have hinv₄ : MInv s words t₄ := hinv₃.frameD
      (W := fun a ↦ Within a (msp + 240) 32 ∨ Within a (msp + 88) 16 ∨ Within a (msp - 96) 96)
      (fun a ha ↦ K34 a (fun h' ↦ ha (Or.inl h')) (fun h' ↦ ha (Or.inr (Or.inl h')))
        (fun h' ↦ ha (Or.inr (Or.inr h'))))
      hsp₄ heap₄ fun a ha hk ↦ by
        simp only [Kept, inputBase_eq] at hk
        rcases ha with ha | ha | ha <;> rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
  have hs₄ : HeapSame u t₄ := fun a ha ↦ by
    simp only [heapEnd] at ha
    rw [K34 a (by addr_omega [ha]) (by addr_omega [ha]) (by addr_omega [ha]), m₃,
      hs₂ a (by simp only [heapEnd]; exact ha), hs₁ a (by simp only [heapEnd]; exact ha)]
  -- the `Bytecode`'s header, from `t₁` on
  have D : ∀ a : Word, (msp + 104).toNat ≤ a.toNat → a.toNat + 8 ≤ (msp + 208).toNat →
      t₄.getMem a = t₁.getMem a := by
    intro a h1 h2
    rw [K34 a (by addr_omega [h1, h2]) (by addr_omega [h1, h2]) (by addr_omega [h1, h2]), m₃,
      K12 a fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2]]
  have a104 := b80000a20_m_x2_104 h₁
  have a112 := b80000a20_m_x2_112 h₁
  have a120 := b80000a20_m_x2_120 h₁
  have a128 := b80000a20_m_x2_128 h₁
  have a136 := b80000a20_m_x2_136 h₁
  have a144 := b80000a20_m_x2_144 h₁
  have a152 := b80000a20_m_x2_152 h₁
  have a160 := b80000a20_m_x2_160 h₁
  have a168 := b80000a20_m_x2_168 h₁
  have a176 := b80000a20_m_x2_176 h₁
  have a184 := b80000a20_m_x2_184 h₁
  have a192 := b80000a20_m_x2_192 h₁
  have a200 := b80000a20_m_x2_200 h₁
  rw [hsp] at a104 a112 a120 a128 a136 a144 a152 a160 a168 a176 a184 a192 a200
  have p0 : vecPtr t₄ (msp + 104) = vecPtr u (msp + 400) := by
    unfold vecPtr
    rw [D _ (by decide) (by decide), show (msp + 104 + 8 : Word) = msp + 112 by decide, a112]
    exact congrArg u.getMem (by decide)
  have l0 : vecLen t₄ (msp + 104) = vecLen u (msp + 400) := by
    unfold vecLen
    rw [D _ (by decide) (by decide), show (msp + 104 + 16 : Word) = msp + 120 by decide, a120]
    exact congrArg u.getMem (by decide)
  have p1 : vecPtr t₄ (msp + 104 + 24) = vecPtr u (msp + 424) := by
    unfold vecPtr
    rw [D _ (by decide) (by decide), show (msp + 104 + 24 + 8 : Word) = msp + 136 by decide, a136]
    exact congrArg u.getMem (by decide)
  have l1 : vecLen t₄ (msp + 104 + 24) = vecLen u (msp + 424) := by
    unfold vecLen
    rw [D _ (by decide) (by decide), show (msp + 104 + 24 + 16 : Word) = msp + 144 by decide, a144]
    exact congrArg u.getMem (by decide)
  have p2 : vecPtr t₄ (msp + 104 + 48) = vecPtr u (msp + 448) := by
    unfold vecPtr
    rw [D _ (by decide) (by decide), show (msp + 104 + 48 + 8 : Word) = msp + 160 by decide, a160]
    exact congrArg u.getMem (by decide)
  have l2 : vecLen t₄ (msp + 104 + 48) = vecLen u (msp + 448) := by
    unfold vecLen
    rw [D _ (by decide) (by decide), show (msp + 104 + 48 + 16 : Word) = msp + 168 by decide, a168]
    exact congrArg u.getMem (by decide)
  have p3 : vecPtr t₄ (msp + 104 + 72) = vecPtr u (msp + 240) := by
    unfold vecPtr
    rw [D _ (by decide) (by decide), show (msp + 104 + 72 + 8 : Word) = msp + 184 by decide, a184]
    exact congrArg u.getMem (by decide)
  have l3 : vecLen t₄ (msp + 104 + 72) = vecLen u (msp + 240) := by
    unfold vecLen
    rw [D _ (by decide) (by decide), show (msp + 104 + 72 + 16 : Word) = msp + 192 by decide, a192]
    exact congrArg u.getMem (by decide)
  have hb₀ := hv.blocksBuf
  have hb₁ := hv.wordsBuf
  have hb₂ := hv.positionsBuf
  have hb₃ := hv.bytesBuf
  simp only [Buf, heapStart] at hb₀ hb₁ hb₂ hb₃
  have hlo := h.inv.heap.lo
  simp only [heapStart, heapEnd] at hhi hlo
  obtain ⟨hlenbc, hivbc⟩ := newRust_len_iv hnew
  have hiv : bytesAt t₄ (msp + 104 + 104) 32 = bc.fiatShamirIv := by
    rw [hivbc, ← h.iv]
    have c1 : bytesAt t₄ (msp + 104 + 104) 32 = bytesAt t₂ (msp + 208) 32 := by
      rw [show (msp + 104 + 104 : Word) = msp + 208 by decide]
      refine bytesAt_dframe fun i hi ↦ ?_
      have ha := toNat_alignDown (msp + 208 + BitVec.ofNat 64 i)
      rw [K34 _ (by addr_omega [ha, hi]) (by addr_omega [ha, hi]) (by addr_omega [ha, hi]), m₃]
    have c2 := hpost₂.bytes
    rw [e10, e11, e12] at c2
    rw [c1, c2]
    exact hbf₁.bytesAt fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hi]
  have hr : readBytecode t₄ (msp + 104) = bc := by
    have e : readBytecode t₄ (msp + 104) =
        ⟨bc.len, bc.fiatShamirIv, bc.blocks, bc.words, bc.positions, bc.bytes⟩ := by
      unfold readBytecode
      rw [hiv, p0, l0, p1, l1, p2, l2, p3, l3,
        blocksAt_heap hs₄ (by simp only [heapEnd]; rcases hb₀.2 with h0 | h0 <;> [left; right] <;> omega),
        wordsAt_heap hs₄ (by simp only [heapEnd]; rcases hb₁.2 with h0 | h0 <;> [left; right] <;> omega),
        halvesAt_heap hs₄ (by simp only [heapEnd]; rcases hb₂.2 with h0 | h0 <;> [left; right] <;> omega),
        halvesAt_heap hs₄ (by simp only [heapEnd]; rcases hb₃.2 with h0 | h0 <;> [left; right] <;> omega),
        hv.blocks, hv.words, hv.positions, hv.bytes, hlenbc, tbl_length hlen,
        D _ (by decide) (by decide), show (msp + 104 + 96 : Word) = msp + 200 by decide, a200,
        h.n]
    rw [e]
  have l4 := hp₄.len
  simp only [inputLen, f11] at l4
  rw [g96, hrest] at l4
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨hinv₄, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hpc₄, returnAddress, b80000a9c_x1 h₃]; decide
  · have e := hp₄.ptr
    simp only [inputPtr, f11] at e
    rw [e, g88, hptr, ptr_add32]
  · have e := hp₄.rest
    simp only [inputLen, f11] at e
    have l4' : (4 : Word).toNat ≤ (u.getMem (msp + 96)).toNat := by rw [hrest]; exact l4
    rw [show (msp + 96 : Word) = msp + 88 + 8 by decide, e, g96, AddrOmega.sub_le _ _ l4', hrest]
    have : (4 : Word).toNat = 4 := rfl
    omega
  · rw [hr]; exact hnew
  · have b₀ := hv.blocksBuf
    have b₁ := hv.wordsBuf
    have b₂ := hv.positionsBuf
    have b₃ := hv.bytesBuf
    simp only [Buf, heapNext] at b₀ b₁ b₂ b₃
    have e₀ := hv.blocksLe
    have e₁ := hv.wordsLe
    have e₂ := hv.positionsLe
    have e₃ := hv.bytesLe
    simp only [heapNext] at e₀ e₁ e₂ e₃
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Buf, heapNext, hn4]
    · rw [p0, l0]; exact b₀
    · rw [show (msp + 128 : Word) = msp + 104 + 24 by decide, p1, l1]; exact b₁
    · rw [show (msp + 152 : Word) = msp + 104 + 48 by decide, p2, l2]; exact b₂
    · rw [show (msp + 176 : Word) = msp + 104 + 72 by decide, p3, l3]; exact b₃
    · rw [p0]; exact e₀
    · rw [show (msp + 128 : Word) = msp + 104 + 24 by decide, p1]; exact e₁
    · rw [show (msp + 152 : Word) = msp + 104 + 48 by decide, p2]; exact e₂
    · rw [show (msp + 176 : Word) = msp + 104 + 72 by decide, p3]; exact e₃
  · have w := hp₄.words
    rw [f10, f11] at w
    simp only [inputPtr] at w
    rw [g88, hptr, readWords_eq_map, readWords_eq_map] at w
    rw [show (32 : Nat) = 8 * 4 from rfl, bytesAt_dwords t₄ (by decide) 4 (by decide), w]
    congr 1
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]; omega
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    have e : inputBase + BitVec.ofNat 64 (8 * (n + 1)) + BitVec.ofNat 64 (8 * i) =
        inputBase + BitVec.ofNat 64 (8 * (n + 1 + i)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (n + 1) + 8 * i = 8 * (n + 1 + i) by ring]
    rw [e, hinv₃.input (n + 1 + i) (by omega)]

end Rv64Verifier.Proofs.Main
