import Rv64Verifier.Proofs.Pcs.VsoTailAtFr

/-!
# `verify_stacked_opening`'s level tail: slots and buffers the frames keep

A doubleword `S - o` of the frame misses `Zu`, `Zt`, `Zh` (`Zu.slot`, `Zt.slot`, `Zh.slot`) when
`o` lies outside their slots (`zuFree`, `ztFree`, `zhFree`); the heap allocated since the entry
and before the opening (`Zu.heap`), the fold rounds' end (`Zt.heap`) or the head (`Zh.heap`)
misses them too.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The offsets of `Zu`'s slots. -/
def zuFree (o : ℕ) : Prop :=
  8 ≤ o ∧ o ≤ 1040 ∧ o % 8 = 0 ∧ (o < 976 ∨ 1008 < o) ∧ (o < 960 ∨ 968 < o) ∧ o ≠ 904 ∧
    (o < 824 ∨ 832 < o) ∧ o ≠ 784 ∧ (o < 520 ∨ 536 < o) ∧ (o < 472 ∨ 488 < o) ∧
    (o < 440 ∨ 464 < o) ∧ (o < 328 ∨ 384 < o) ∧ (o < 136 ∨ 160 < o)

/-- The offsets of `Zt`'s slots. -/
def ztFree (o : ℕ) : Prop :=
  8 ≤ o ∧ o ≤ 1040 ∧ o % 8 = 0 ∧ (o < 912 ∨ 1032 < o) ∧ o ≠ 904 ∧ o ≠ 896 ∧ o ≠ 872 ∧
    (o < 824 ∨ 832 < o) ∧ o ≠ 808 ∧ (o < 784 ∨ 792 < o) ∧ (o < 112 ∨ 640 < o)

/-- The offsets of `Zh`'s slots. -/
def zhFree (o : ℕ) : Prop := ztFree o ∧ o ≠ 856 ∧ (o < 672 ∨ 688 < o)

theorem Zu.slot {s u r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {o : ℕ}
    (ho : zuFree o) :
    ∀ i < 8, ¬ Zu s u r (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  simp only [zuFree] at ho
  intro i hi hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hi, hb, ho]
    | addr_omega [hw, hi, hb, ho, hS, hIs]
    | addr_omega [hw, hi, hb, ho, hnx]
    | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hb, ho, hhi])

theorem Zt.slot {s t r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {o : ℕ}
    (ho : ztFree o) :
    ∀ i < 8, ¬ Zt s t r (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  simp only [ztFree] at ho
  intro i hi hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hi, hb, ho]
    | addr_omega [hw, hi, hb, ho, hS, hIs]
    | addr_omega [hw, hi, hb, ho, hnx]
    | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hb, ho, hhi])

theorem Zh.slot {s h r : MachineState} (hpre : VsoPre s) (hr : HeapOk r)
    (hF : (vecCap h (s.getReg .x2 - 688)).toNat * 24 = 0 ∨
      (vecPtr h (s.getReg .x2 - 688)).toNat + (vecCap h (s.getReg .x2 - 688)).toNat * 24 ≤
        heapNext r) {o : ℕ}
    (ho : zhFree o) :
    ∀ i < 8, ¬ Zh s h r (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  simp only [zhFree, ztFree] at ho
  intro i hi hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hi, hb, ho]
    | addr_omega [hw, hi, hb, ho, hS, hIs]
    | addr_omega [hw, hi, hb, ho, hnx]
    | addr_omega [hw.2, hi, hb, ho, hhi]
    | (rcases hF with h0 | h0
       · simp only [Within] at hw; omega
       · addr_omega [hw, hi, hb, ho, h0, hhi])

/-- A byte of the heap allocated since the entry, before `lo`, misses `Zu`. -/
theorem Zu.heap {s u r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {y : Word}
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat < heapNext u) (hur : heapNext u ≤ heapNext r) :
    ¬ Zu s u r y := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hb, h2, hhi, hur]
    | (rcases hIf.1 with h0 | h0
       · addr_omega [hw, hS, h0, h1]
       · addr_omega [hw, hS, h0, h2, hhi, hur])

theorem Zt.heap {s t r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {y : Word}
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat < heapNext t) (htr : heapNext t ≤ heapNext r) :
    ¬ Zt s t r y := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hb, h2, hhi, htr]
    | (rcases hIf.1 with h0 | h0
       · addr_omega [hw, hS, h0, h1]
       · addr_omega [hw, hS, h0, h2, hhi, htr])

/-- What the level writes from the Merkle checks' end `m` to the rows' end `r`. -/
def Zm (s m r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 904) 8 ∨
    Within a (s.getReg .x2 - 832) 8 ∨
    Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 536) 24 ∨
    Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 384) 24 ∨
    Within a nextAddr 8 ∨
    Fresh m r a

theorem Zm.i1 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 2464) 1424) : Zm s m r a := by
  unfold Zm
  exact Or.inl hz

theorem Zm.i2 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 904) 8) : Zm s m r a := by
  unfold Zm
  iterate 1 apply Or.inr
  exact Or.inl hz

theorem Zm.i3 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 832) 8) : Zm s m r a := by
  unfold Zm
  iterate 2 apply Or.inr
  exact Or.inl hz

theorem Zm.i4 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 784) 8) : Zm s m r a := by
  unfold Zm
  iterate 3 apply Or.inr
  exact Or.inl hz

theorem Zm.i5 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 536) 24) : Zm s m r a := by
  unfold Zm
  iterate 4 apply Or.inr
  exact Or.inl hz

theorem Zm.i6 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 464) 24) : Zm s m r a := by
  unfold Zm
  iterate 5 apply Or.inr
  exact Or.inl hz

theorem Zm.i7 {s m r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 384) 24) : Zm s m r a := by
  unfold Zm
  iterate 6 apply Or.inr
  exact Or.inl hz

theorem Zm.i8 {s m r : MachineState} {a : Word}
    (hz : Within a nextAddr 8) : Zm s m r a := by
  unfold Zm
  iterate 7 apply Or.inr
  exact Or.inl hz

theorem Zm.i9 {s m r : MachineState} {a : Word}
    (hz : Fresh m r a) : Zm s m r a := by
  unfold Zm
  iterate 8 apply Or.inr
  exact hz

theorem Merkled.ym {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    {rows : List E} (hpre : VsoPre s) (_hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame m r (Zm s m r) ∧ heapNext m ≤ heapNext r := by
  have hb := bounds hpre
  have m1 := hsl.mono
  have m2 : heapNext t' ≤ heapNext k := hk.mono
  have m3 := hr.mono
  refine ⟨((hsl.fr.mono fun a ha ↦ ?_).trans (hk.fr.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
    (hr.fr.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha
    · exact Zm.i7 ha
    · exact Zm.i1 (by addr_omega [ha, hb])
    · exact Zm.i3 ha
    · exact Zm.i8 ha
    · simp only [Fresh] at ha; exact Zm.i9 ⟨ha.1, by omega⟩
  · rcases ha with ha | ha | ha | ha
    · exact Zm.i5 ha
    · exact Zm.i1 (by addr_omega [ha, hb])
    · exact Zm.i8 ha
    · simp only [Fresh] at ha; exact Zm.i9 ⟨by omega, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Zm.i2 ha
    · exact Zm.i4 ha
    · exact Zm.i6 ha
    · exact Zm.i7 ha
    · exact Zm.i1 ha
    · exact Zm.i8 ha
    · simp only [Fresh] at ha; exact Zm.i9 ⟨by omega, ha.2⟩

/-- The offsets of `Zm`'s slots. -/
def zmFree (o : ℕ) : Prop :=
  8 ≤ o ∧ o ≤ 1040 ∧ o % 8 = 0 ∧ o ≠ 904 ∧ o ≠ 832 ∧ o ≠ 784 ∧ (o < 520 ∨ 536 < o) ∧
    (o < 448 ∨ 464 < o) ∧ (o < 368 ∨ 384 < o)

theorem Zm.slot {s m r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {o : ℕ}
    (ho : zmFree o) :
    ∀ i < 8, ¬ Zm s m r (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  simp only [zmFree] at ho
  intro i hi hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hi, hb, ho]
    | addr_omega [hw, hi, hb, ho, hnx]
    | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hb, ho, hhi])

/-- The offsets of `X1`'s slots. -/
def x1Free (o : ℕ) : Prop :=
  8 ≤ o ∧ o ≤ 1040 ∧ o % 8 = 0 ∧ (o < 976 ∨ 1008 < o) ∧ o ≠ 904 ∧ o ≠ 832 ∧ o ≠ 784 ∧
    (o < 520 ∨ 536 < o) ∧ (o < 440 ∨ 464 < o) ∧ (o < 328 ∨ 384 < o) ∧ (o < 136 ∨ 160 < o)

theorem X1.slot {s w r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {o : ℕ}
    (ho : x1Free o) :
    ∀ i < 8, ¬ X1 s w r (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  simp only [x1Free] at ho
  intro i hi hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hi, hb, ho]
    | addr_omega [hw, hi, hb, ho, hS, hIs]
    | addr_omega [hw, hi, hb, ho, hnx]
    | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hb, ho, hhi])

theorem X1.heap {s w r : MachineState} (hpre : VsoPre s) (hr : HeapOk r) {y : Word}
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat < heapNext w) (hwr : heapNext w ≤ heapNext r) :
    ¬ X1 s w r y := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals first
    | addr_omega [hw, hb, h2, hhi, hwr]
    | (rcases hIf.1 with h0 | h0
       · addr_omega [hw, hS, h0, h1]
       · addr_omega [hw, hS, h0, h2, hhi, hwr])

end Rv64Verifier.Proofs.Pcs.Vso
