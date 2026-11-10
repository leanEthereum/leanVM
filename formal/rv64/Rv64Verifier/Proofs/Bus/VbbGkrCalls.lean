import Rv64Verifier.Proofs.Bus.VbbGkrCtx

/-!
# `verify_bus_balance`: the GKR loop's calls

Each from any site past the prologue, its result in the frame at `S - k`; each returns a `StepR`
writing only the result, and what it computes, or reaches a dead end.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Contracts


section Keep
variable {s v w : MachineState} {A : Word → Prop}

/-- A `Vec<E>` held in registers, its buffer allocated since the entry, keeps what it holds. -/
theorem NewVecR.keepG (hpre : BusBalancePre s) (st : StepR s v w A) (hA : FrameW s A)
    {c p l : Word} {xs : List E} (h : NewVecR s v c p l xs) : NewVecR s w c p l xs := by
  have hb := h.buf
  have hl := h.le
  have hm := st.mono
  refine ⟨hl, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩, ?_⟩
  rw [← h.elems]
  refine eListAt_congr fun i hi ↦ ?_
  have hc : 24 * i + 24 ≤ c.toNat * 24 := by omega
  have hbd : p.toNat + c.toNat * 24 ≤ 2 ^ 64 := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi
      simp only [heapNext, heapEnd] at *; omega
  have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (p + BitVec.ofNat 64 (24 * i) +
      BitVec.ofNat 64 j) = v.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
    st.bufWord hpre hA hb (by addr_omega [hbd, hc, hj]) (by addr_omega [hbd, hc, hj])
  exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

/-- An `E` in the frame at `S - j`, apart from what a step writes, keeps its value. -/
theorem StepR.eAtFrame (hpre : BusBalancePre s) (st : StepR s v w A) {j : Nat} (hj1 : 24 ≤ j)
    (hj2 : j ≤ 1344) (hA : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 24 → ¬ A y) :
    eAt w (s.getReg .x2 - BitVec.ofNat 64 j) = eAt v (s.getReg .x2 - BitVec.ofNat 64 j) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have wd (i : Nat) (hi : i + 8 ≤ 24) : w.getMem (s.getReg .x2 - BitVec.ofNat 64 j +
      BitVec.ofNat 64 i) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 i) :=
    st.word hpre (fun y hy ↦ hA y (by addr_omega [hy, hb1, hj1, hj2, hi]))
      (Or.inl (by addr_omega [hb1, hj1, hj2, hi]))
  exact eAt_congr (by simpa using wd 0 (by omega)) (wd 8 (by omega)) (wd 16 (by omega))

end Keep

/-- A call of `poly_eval` on three coefficients at `a`, the point at `S - j`, the result at
`S - k`. -/
theorem polyEvalCall (hPE : MultilinearContracts.PolyEvalSpec) {s u₀ u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x8000cef4)
    {k j : Nat} {a : Word} (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k)
    (h11 : u.getReg .x11 = a) (h12 : u.getReg .x12 = 3)
    (h13 : u.getReg .x13 = s.getReg .x2 - BitVec.ofNat 64 j)
    (hk1 : 128 ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) (hj1 : 128 ≤ j) (hj2 : j ≤ 1344)
    (hj8 : j % 8 = 0) (hkj : k + 24 ≤ j ∨ j + 24 ≤ k) (hav : ValidMemRange a 9)
    (hak : Apart a 72 (s.getReg .x2 - BitVec.ofNat 64 k) 24)
    (has : Apart a 72 (s.getReg .x2 - BitVec.ofNat 64 2464) 1120) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepR s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 k) 24) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 k) =
        polyEvalRust (eListAt u a 3) (eAt u (s.getReg .x2 - BitVec.ofNat 64 j)) ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T → TranscriptAt v (s.getReg .x12) T) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, -, o3⟩ := frameSlot (m := MultilinearContracts.polyEvalStack) hpre h (n := 24)
    (by omega) hk2 hk8 (by decide)
  obtain ⟨p1, -, p3⟩ := frameSlot (m := MultilinearContracts.polyEvalStack) hpre h (n := 24)
    (k := j) (by omega) hj2 hj8 (by decide)
  have hsl : stackLo u MultilinearContracts.polyEvalStack = s.getReg .x2 - BitVec.ofNat 64 2464 := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hst := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at hst
  have rs : RtStack u MultilinearContracts.polyEvalStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have pre : MultilinearContracts.PolyEvalPre u := {
    ret := by rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3, hk8, hk2])
    coeffs := by rw [h11, h12]; exact hav
    point := by rw [h13]; exact regionRange p1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3, hj8, hj2])
    stack := rs.toStackOk
    retCoeffs := by
      rw [h10, h11, h12]
      have : (3 : Word).toNat = 3 := rfl
      simp only [Apart] at hak ⊢; omega
    retPoint := by rw [h10, h13]; addr_omega [hb1, hkj, hk2, hj2]
    retStack := by rw [h10]; exact o3
    coeffsStack := by
      rw [h11, h12, hsl]
      have : (3 : Word).toNat = 3 := rfl
      have : MultilinearContracts.polyEvalStack = 1120 := rfl
      simp only [Apart] at has ⊢; omega
    pointStack := by rw [h13]; exact p3
    rodata := h.rodata hpre
    retRodata := by rw [h10]; simp only [rodataSize] at hst ⊢; addr_omega [hst, hrb, hb1, hk1, hk2]
    stackRodata := by rw [hsl]; simp only [rodataSize] at hst ⊢; addr_omega [hst, hrb, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hPE.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 k) 24 ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 2464) 1120 := fun x hx ↦
    post.frame x (fun h1 ↦ hx 0 (by decide) (Or.inl (by rw [add_ofNat_zero]; rwa [h10] at h1)))
      (fun h2 ↦ hx 0 (by decide) (Or.inr (by rw [add_ofNat_zero]; rwa [hsl] at h2)))
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1, hk1, hk2])
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨fr.mono fun x hx ↦ ?_, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩,
    hn.ge, hp.reg .x2⟩, ?_⟩⟩
  · rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hb1])))
  · have := post.value
    rw [h10, h11, h12, h13] at this
    refine ⟨this, fun T hT ↦ h.transcript hpre ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩
      (fr.mono fun x hx ↦ Or.inl (by rcases hx with hx | hx <;> addr_omega [hx, hb1, hk1, hk2])) hT⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
