import Rv64Verifier.Proofs.Bus.VbbTail6

/-!
# `verify_bus_balance` past the GKR loop: `claims.push`'s `grow_one`

`grow_one` (`0x8000c0a4`) on the claims' `Vec` at `S - 840` (`growOneCall`) copies their bytes to
a new buffer: the claims hold there (`ClaimsAt.grow`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- A call of `grow_one` on the `Vec<ColumnClaim>` at `S - 840`. -/
theorem growOneCall (hG : GrowOneFreshSpec 0x8000c0a4 56 8) {s u₀ u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x8000c0a4)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 840)
    (hraw : RawVecOk u (s.getReg .x2 - BitVec.ofNat 64 840) 56 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 840) 16) ∧ Inv s v ∧
      (vecCap u (s.getReg .x2 - BitVec.ofNat 64 840)).toNat + 1 ≤
        (vecCap v (s.getReg .x2 - BitVec.ofNat 64 840)).toNat ∧
      bytesAt v (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 840))
          ((vecCap u (s.getReg .x2 - BitVec.ofNat 64 840)).toNat * 56) =
        bytesAt u (vecPtr u (s.getReg .x2 - BitVec.ofNat 64 840))
          ((vecCap u (s.getReg .x2 - BitVec.ofNat 64 840)).toNat * 56) ∧
      NewBuf u v (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 840))
        ((vecCap v (s.getReg .x2 - BitVec.ofNat 64 840)).toNat * 56) 8) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := growOneStack) hpre h (n := 16) (k := 840) (by omega)
    (by omega) (by omega) (by decide)
  have pre : GrowOnePre 56 8 u := {
    heap := h.heap
    self := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3])
    raw := h10 ▸ hraw
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := h10 ▸ o2
    selfStack := h10 ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, hfresh⟩ | hd⟩ := hG.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u growOneStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 160) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have st : StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 840) 16) := by
    refine ⟨fun x hx' ↦ post.frame.getMem fun i hi hw ↦ hx' i hi ?_, post.heap, post.mono,
      hp.reg .x2⟩
    rw [hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw))
  have hcap := post.cap
  have hby := post.bytes
  rw [h10] at hcap hby hfresh
  exact ⟨v, hrv, Or.inl ⟨hpcv, hp, st,
    h.afterR hpre (frameW_slot hpre (by omega) (by omega)) st.toR, hcap, hby, hfresh⟩⟩

/-- Claims whose bytes were copied to a new buffer, their points kept. -/
theorem ClaimsAt.grow {s u v : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s u v A) (hA : FrameW s A) {cap ptr len cap' ptr' : Word}
    {cs : List ColumnClaim} (h : ClaimsAt s u cap ptr len cs) (hle : cap.toNat ≤ cap'.toNat)
    (hby : bytesAt v ptr' (cap.toNat * 56) = bytesAt u ptr (cap.toNat * 56))
    (hb : NewBuf u v ptr' (cap'.toNat * 56) 8) (hu : heapNext s ≤ heapNext u) :
    ClaimsAt s v cap' ptr' len cs := by
  have hbu := h.buf
  have hm := st.mono
  have hlo := hpre.heap.lo
  have hl := h.len
  have hle' := h.le
  refine ⟨by omega, ?_, hl, fun i hi ↦ ?_⟩
  · simp only [NewBuf] at hb ⊢
    exact ⟨hb.1, hb.2.imp (by omega) fun h' ↦ ⟨by omega, by omega⟩⟩
  have hpa : ptr'.toNat % 8 = 0 := hb.1
  have hqa : ptr.toNat % 8 = 0 := hbu.1
  have wd (j : Nat) (hj : j + 8 ≤ 56) (hj8 : j % 8 = 0) :
      v.getMem (ptr' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j) =
        u.getMem (ptr + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact getMem_eq_of_bytesAt hby hpa hqa (by omega) (by omega)
  have C := h.claims i hi
  have e0 : v.getMem (ptr' + BitVec.ofNat 64 (56 * i)) = u.getMem (ptr + BitVec.ofNat 64 (56 * i)) := by
    have := wd 0 (by omega) (by omega)
    rwa [add_ofNat_zero, add_ofNat_zero] at this
  obtain ⟨hl', hbuf'⟩ := C.vec.bound
  refine ⟨C.vec.transfer e0 (wd 8 (by omega) (by omega)) (wd 16 (by omega) (by omega)) hm
    (st.eListAt hpre hA hbuf' hl'), ?_, ?_⟩
  · rw [show ptr' + BitVec.ofNat 64 (56 * i) + 24 =
      ptr' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 24 from rfl, wd 24 (by omega) (by omega)]
    exact C.column
  · rw [← C.value]
    have a40 (q : Word) : q + 32 + 8 = q + BitVec.ofNat 64 40 := by rw [BitVec.add_assoc]; rfl
    have a48 (q : Word) : q + 32 + 16 = q + BitVec.ofNat 64 48 := by rw [BitVec.add_assoc]; rfl
    refine eAt_congr (wd 32 (by omega) (by omega)) ?_ ?_
    · rw [a40, a40]; exact wd 40 (by omega) (by omega)
    · rw [a48, a48]; exact wd 48 (by omega) (by omega)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
