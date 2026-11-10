import Rv64Verifier.Proofs.Walk.Mid13

/-!
# `walk`: R13, from `stack_offsets`' call to the placements built

`r13`: `soCall`, `ofAlloc`, `plAlloc` (with the scatter loop), the placements' loop (`plLoop`), to
`0x800033f0` (`AtR14`), the values those of `placementsRust` (`plc_eq`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.MultilinearContracts

/-- R13: from `0x800032b8` to `0x800033f0`. -/
theorem r13 (hSO : StackOffsetsSpec) (hTA : TryAllocZeroedSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {G BK : Word} (hpre : WalkPre s)
    (hpc : u.pc = 0x800032b8) (h : AtR13 OI s u A k R Q B lo lo2 lo3 G BK) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800033f0 ∧ ∃ PL, AtR14 OI s t A k R Q B lo lo2 lo3 PL)) := by
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, SO, h₁⟩⟩ := soCall hSO hpre hpc h
  · exact ⟨t₁, hr₁, Or.inl hd⟩
  obtain ⟨t₂, hr₂, hd | ⟨-, OF, h₂⟩⟩ := ofAlloc hTA hpre hpc₁ h₁
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  obtain ⟨t₃, hr₃, hd | ⟨-, PL, h₃⟩⟩ := plAlloc hTA hpre h₂
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  have Bs := h₃.base
  have hk := kapPre_ne A k (le_refl 6)
  have hlK : (kapPre A k 6).length = 165 := by rw [kapPre_length A k 6 (le_refl 6), kapLen_six]
  obtain ⟨c1, c2, c3, c4⟩ := Bs.kv.bounds hk
  rw [hlK] at c4
  have kb := Bs.kbelow
  have hhu := Bs.k11.at11.base.inv.heap.hi
  simp only [heapStart, heapEnd] at c2 hhu
  have ol := h₃.oflo
  have op := h₃.ofpl
  have ph := h₃.plhi
  obtain ⟨t, hr, pct, rg, fr, vals⟩ := plLoop h₃.plal h₃.ofal c1 c2 (by omega) (by omega) op
    (by omega) (kapPre_le Bs.k11.at11.base.ok)
    (fun i hi ↦ Bs.kv.vals i (by rw [hlK]; exact hi)) h₃.ov h₃.x11 h₃.x12 h₃.x14 h₃.x27 h₃.x19
    h₃.x24 _ 0 t₃ rfl h₃.pl0
  have hn : heapNext t = heapNext t₃ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw; addr_omega [hy, hw, ph, hhu]) (by decide))
  have hv : HeapOk t := ⟨hn ▸ Bs.k11.at11.base.inv.heap.lo, hn ▸ Bs.k11.at11.base.inv.heap.hi⟩
  obtain ⟨e1, e2, e3⟩ := plc_eq A k
  refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inr ⟨pct, PL, {
    base := Bs.keep hpre fr (fun a ha ↦ by
      simp only [Within] at ha
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn]; omega⟩))) hv hn.ge (rg .x2 (by decide))
    plal := h₃.plal
    pllo := by omega
    plhi := by rw [hn]; exact ph
    plvals := by
      rw [e1]
      exact List.map_congr_left fun i hi ↦ vals i (List.mem_range.mp hi)
    x8 := by rw [rg .x8 (by decide), h₃.x8, e3]
    x9 := by rw [rg .x9 (by decide), h₃.x9, h₃.x8, e3]
    x19 := by rw [rg .x19 (by decide), h₃.x19, e2]
    x21 := by rw [rg .x21 (by decide)]; exact h₃.x21
    x22 := by rw [rg .x22 (by decide)]; exact h₃.x22
    x24 := by rw [rg .x24 (by decide)]; exact h₃.x24
    x18 := by rw [rg .x18 (by decide)]; exact h₃.x18
    x23 := by rw [rg .x23 (by decide)]; exact h₃.x23
    x26 := by rw [rg .x26 (by decide)]; exact h₃.x26 }⟩⟩

end Rv64Verifier.Proofs.Walk
