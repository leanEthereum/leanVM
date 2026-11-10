import Rv64Verifier.Proofs.Bus.VbbTail33

/-!
# `verify_bus_balance`'s side loop: the selectors' callees

`try_allocate_in` and `reserve` on the frame's slots (`tryAllocC`, `reserveC`), and `eq_above` into
`S - 248` on a point below `NEXT` (`eqAboveC`), each keeping `Cur`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.MultilinearContracts

/-- What a callee writing `n` bytes at `S - k` may write. -/
def CallW (s u v : MachineState) (k n : Nat) (a : Word) : Prop :=
  Within a (s.getReg .x2 - BitVec.ofNat 64 k) n ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
    Within a nextAddr 8 ∨ Fresh u v a

/-- A callee's step that writes `n ≤ 216` bytes at `S - k` in `S - [320, 104)` keeps `Cur`. -/
theorem Cur.call {s z h u v : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) {k n : Nat} (hk : 104 + n ≤ k)
    (hk2 : k ≤ 320) (fr : DFrame u v (CallW s u v k n)) (hv : HeapOk v)
    (hm : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : Cur s z h v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact C.next hpre hsz ⟨fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha)), hv, hm, sp⟩ fun a ha ↦ Or.inl (by
      simp only [SlotW]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1, hk, hk2])))))))

/-- `try_allocate_in(S - 248, n, _, 8, 24)`. -/
theorem tryAllocC (hT : TryAllocZeroedSpec) {s z h u₀ u : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x800049ac) (h10 : u.getReg .x10 = s.getReg .x2 - 248) (h13 : u.getReg .x13 = 8)
    (h14 : u.getReg .x14 = 24) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (CallW s u v 248 24) ∧ heapNext u ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 248) = 0 → v.getMem (s.getReg .x2 - 240) = u.getReg .x11 ∧
        NewBuf u v (v.getMem (s.getReg .x2 - 232)) ((u.getReg .x11).toNat * 24) 8)) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have h := C.inv
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := tryAllocStack) hpre h (n := 24) (k := 248) (by omega)
    (by omega) (by omega) (by decide)
  have pre : TryAllocPre .x13 .x14 u := {
    heap := h.heap
    out := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by addr_omega [hb1]) (by addr_omega [hb1, hb3])
    align := by rw [h13]; decide
    size := by rw [h14]; decide
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := h10 ▸ o2
    outStack := h10 ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, -⟩ | hd⟩ := hT.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u tryAllocStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 48) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : DFrame u v (CallW s u v 248 24) := fun x hx ↦ post.frame.getMem fun i hi hw ↦ hx i hi (by
    rw [hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw)))
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, C.call hpre hsz (k := 248) (n := 24) (by omega) (by omega) fr
    post.heap post.mono (hp.reg .x2), fr, post.mono, fun h0 ↦ ?_⟩⟩
  have hok := post.ok (by rw [h10]; exact h0)
  rw [h10, h13, h14] at hok
  have e8 : s.getReg .x2 - 248 + 8 = s.getReg .x2 - 240 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 248 + 16 = s.getReg .x2 - 232 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e8, e16] at hok
  exact hok

/-- `reserve` of the `Vec<E>` at `S - k`, `k` in `S - [320, 128]`. -/
theorem reserveC (hR : ReserveFreshSpec 0x80008a10 24 8) {s z h u₀ u : MachineState}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80008a10) {k : Nat} (hk : 128 ≤ k)
    (hk2 : k ≤ 320) (hk8 : k % 8 = 0) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k)
    (hvec : VecOk u (s.getReg .x2 - BitVec.ofNat 64 k) 24 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (CallW s u v k 16) ∧ heapNext u ≤ heapNext v ∧
      (vecLen u (s.getReg .x2 - BitVec.ofNat 64 k)).toNat + (u.getReg .x11).toNat ≤
        (vecCap v (s.getReg .x2 - BitVec.ofNat 64 k)).toNat ∧
      VecOk v (s.getReg .x2 - BitVec.ofNat 64 k) 24 8 ∧
      vecLen v (s.getReg .x2 - BitVec.ofNat 64 k) = vecLen u (s.getReg .x2 - BitVec.ofNat 64 k) ∧
      ((vecPtr v (s.getReg .x2 - BitVec.ofNat 64 k) = vecPtr u (s.getReg .x2 - BitVec.ofNat 64 k) ∧
        vecCap v (s.getReg .x2 - BitVec.ofNat 64 k) = vecCap u (s.getReg .x2 - BitVec.ofNat 64 k)) ∨
       NewBuf u v (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 k))
        ((vecCap v (s.getReg .x2 - BitVec.ofNat 64 k)).toNat * 24) 8)) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have h := C.inv
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := reserveStack) hpre h (n := 24) (k := k) (by omega)
    (by omega) hk8 (by decide)
  have pre : ReservePre 24 8 u := {
    heap := h.heap
    self := by rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3, hk8, hk2])
    vec := h10 ▸ hvec
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := h10 ▸ o2
    selfStack := h10 ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, hfr⟩ | hd⟩ := hR.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u reserveStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 160) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : DFrame u v (CallW s u v k 16) := fun x hx ↦ post.frame.getMem fun i hi hw ↦ hx i hi (by
    rw [hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw)))
  have pc' := post.cap
  have pv := post.vec
  have pl := post.len
  rw [h10] at pc' pv pl hfr
  exact ⟨v, hrv, Or.inl ⟨hpcv, hp, C.call hpre hsz (k := k) (n := 16) (by omega) hk2 fr post.heap
    post.mono (hp.reg .x2), fr, post.mono, pc', pv, pl, hfr⟩⟩

/-- `eq_above(S - 248, _, _, p, l)`, the point's `l` elements at `p` below `NEXT`. -/
theorem eqAboveC (hEA : EqAboveSpec) {s z h u₀ u : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x8000e12c) (h10 : u.getReg .x10 = s.getReg .x2 - 248)
    (hp8 : (u.getReg .x13).toNat % 8 = 0)
    (hp : (u.getReg .x14).toNat = 0 ∨ heapStart ≤ (u.getReg .x13).toNat)
    (hpl : (u.getReg .x13).toNat + 24 * (u.getReg .x14).toNat ≤ heapNext u) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (CallW s u v 248 24) ∧ heapNext u ≤ heapNext v ∧
      eAt v (s.getReg .x2 - 248) = PlacementRust.eqAbove ⟨(u.getReg .x11).toNat, u.getReg .x12⟩
        (eListAt u (u.getReg .x13) (u.getReg .x14).toNat)) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have h := C.inv
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at ha hx
  have hh := h.heap.hi
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := eqAboveStack) hpre h (n := 24) (k := 248) (by omega)
    (by omega) (by omega) (by decide)
  have hsl : stackLo u eqAboveStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 1136) := by
    simp only [stackLo, eqAboveStack, Contracts.mulStack, h.sp]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  simp only [heapNext, heapEnd, heapStart] at hh hpl hp ha
  have pre : EqAbovePre u := {
    heap := h.heap
    ret := by rw [h10]; exact regionRange o1 (Nat.le_refl _) (by addr_omega [hb1]) (by addr_omega [hb1, hb3])
    point := by
      rcases hp with h0 | h0
      · intro i hi; omega
      · exact heapRange hp8 (by simp only [heapStart]; omega)
          (by simp only [heapEnd]; omega)
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    retFree := h10 ▸ o2
    pointFree := ⟨Or.inl (by simp only [heapNext]; omega), by addr_omega [hpl, hh, hx]⟩
    retStack := h10 ▸ o3
    pointStack := by rw [hsl]; addr_omega [hpl, hh, ha, hb1]
    rodata := h.rodata hpre }
  obtain ⟨v, hrv, ⟨hpcv, hpv, post⟩ | hd⟩ := hEA.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v (CallW s u v 248 24) := fun x hx' ↦ post.frame x fun i hi hw ↦ hx' i hi (by
    simp only [EqAboveW] at hw
    rw [hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw)))
  have hval := post.value
  rw [h10] at hval
  exact ⟨v, hrv, Or.inl ⟨hpcv, hpv, C.call hpre hsz (k := 248) (n := 24) (by omega) (by omega) fr
    post.heap post.mono (hpv.reg .x2), fr, post.mono, hval⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
