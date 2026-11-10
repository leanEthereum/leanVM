import Rv64Verifier.Proofs.Pcs.VsoTailCtx

/-!
# `verify_stacked_opening`'s level tail: the frames from the head, the fold rounds' end and the
opening to the rows' end

`Zh`, `Zt`, `Zu`: what the level writes from its head `h`, the fold rounds' end `t` and the
opening `u` to the rows' end `r` (`Merkled.yh`, `Merkled.yt`, `Merkled.yu`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- What the level writes from the opening `u` to the rows' end `r`. -/
def Zu (s u r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 1008) 40 ∨
    Within a (s.getReg .x2 - 968) 16 ∨
    Within a (s.getReg .x2 - 904) 8 ∨
    Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 536) 24 ∨
    Within a (s.getReg .x2 - 488) 24 ∨
    Within a (s.getReg .x2 - 464) 32 ∨
    Within a (s.getReg .x2 - 384) 64 ∨
    Within a (s.getReg .x2 - 160) 32 ∨
    Within a (s.getReg .x10 + 8) 352 ∨
    Within a nextAddr 8 ∨
    Fresh u r a

theorem Zu.i1 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 2464) 1424) : Zu s u r a := by
  unfold Zu
  exact Or.inl hz

theorem Zu.i2 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 1008) 40) : Zu s u r a := by
  unfold Zu
  iterate 1 apply Or.inr
  exact Or.inl hz

theorem Zu.i3 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 968) 16) : Zu s u r a := by
  unfold Zu
  iterate 2 apply Or.inr
  exact Or.inl hz

theorem Zu.i4 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 904) 8) : Zu s u r a := by
  unfold Zu
  iterate 3 apply Or.inr
  exact Or.inl hz

theorem Zu.i5 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 832) 16) : Zu s u r a := by
  unfold Zu
  iterate 4 apply Or.inr
  exact Or.inl hz

theorem Zu.i6 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 784) 8) : Zu s u r a := by
  unfold Zu
  iterate 5 apply Or.inr
  exact Or.inl hz

theorem Zu.i7 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 536) 24) : Zu s u r a := by
  unfold Zu
  iterate 6 apply Or.inr
  exact Or.inl hz

theorem Zu.i8 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 488) 24) : Zu s u r a := by
  unfold Zu
  iterate 7 apply Or.inr
  exact Or.inl hz

theorem Zu.i9 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 464) 32) : Zu s u r a := by
  unfold Zu
  iterate 8 apply Or.inr
  exact Or.inl hz

theorem Zu.i10 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 384) 64) : Zu s u r a := by
  unfold Zu
  iterate 9 apply Or.inr
  exact Or.inl hz

theorem Zu.i11 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 160) 32) : Zu s u r a := by
  unfold Zu
  iterate 10 apply Or.inr
  exact Or.inl hz

theorem Zu.i12 {s u r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x10 + 8) 352) : Zu s u r a := by
  unfold Zu
  iterate 11 apply Or.inr
  exact Or.inl hz

theorem Zu.i13 {s u r : MachineState} {a : Word}
    (hz : Within a nextAddr 8) : Zu s u r a := by
  unfold Zu
  iterate 12 apply Or.inr
  exact Or.inl hz

theorem Zu.i14 {s u r : MachineState} {a : Word}
    (hz : Fresh u r a) : Zu s u r a := by
  unfold Zu
  iterate 13 apply Or.inr
  exact hz

/-- What the level writes from the fold rounds' end `t` to `r`. -/
def Zt (s t r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 1032) 128 ∨
    Within a (s.getReg .x2 - 968) 16 ∨
    Within a (s.getReg .x2 - 904) 8 ∨
    Within a (s.getReg .x2 - 896) 8 ∨
    Within a (s.getReg .x2 - 872) 8 ∨
    Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 808) 8 ∨
    Within a (s.getReg .x2 - 792) 16 ∨
    Within a (s.getReg .x2 - 640) 536 ∨
    Within a (s.getReg .x10 + 8) 352 ∨
    Within a nextAddr 8 ∨
    Fresh t r a

theorem Zt.i1 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 2464) 1424) : Zt s t r a := by
  unfold Zt
  exact Or.inl hz

theorem Zt.i2 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 1032) 128) : Zt s t r a := by
  unfold Zt
  iterate 1 apply Or.inr
  exact Or.inl hz

theorem Zt.i3 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 968) 16) : Zt s t r a := by
  unfold Zt
  iterate 2 apply Or.inr
  exact Or.inl hz

theorem Zt.i4 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 904) 8) : Zt s t r a := by
  unfold Zt
  iterate 3 apply Or.inr
  exact Or.inl hz

theorem Zt.i5 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 896) 8) : Zt s t r a := by
  unfold Zt
  iterate 4 apply Or.inr
  exact Or.inl hz

theorem Zt.i6 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 872) 8) : Zt s t r a := by
  unfold Zt
  iterate 5 apply Or.inr
  exact Or.inl hz

theorem Zt.i7 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 832) 16) : Zt s t r a := by
  unfold Zt
  iterate 6 apply Or.inr
  exact Or.inl hz

theorem Zt.i8 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 808) 8) : Zt s t r a := by
  unfold Zt
  iterate 7 apply Or.inr
  exact Or.inl hz

theorem Zt.i9 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 792) 16) : Zt s t r a := by
  unfold Zt
  iterate 8 apply Or.inr
  exact Or.inl hz

theorem Zt.i10 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 640) 536) : Zt s t r a := by
  unfold Zt
  iterate 9 apply Or.inr
  exact Or.inl hz

theorem Zt.i11 {s t r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x10 + 8) 352) : Zt s t r a := by
  unfold Zt
  iterate 10 apply Or.inr
  exact Or.inl hz

theorem Zt.i12 {s t r : MachineState} {a : Word}
    (hz : Within a nextAddr 8) : Zt s t r a := by
  unfold Zt
  iterate 11 apply Or.inr
  exact Or.inl hz

theorem Zt.i13 {s t r : MachineState} {a : Word}
    (hz : Fresh t r a) : Zt s t r a := by
  unfold Zt
  iterate 12 apply Or.inr
  exact hz

/-- What the level writes from its head `h` to `r`. -/
def Zh (s h r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 1032) 128 ∨
    Within a (s.getReg .x2 - 968) 16 ∨
    Within a (s.getReg .x2 - 904) 8 ∨
    Within a (s.getReg .x2 - 896) 8 ∨
    Within a (s.getReg .x2 - 872) 8 ∨
    Within a (s.getReg .x2 - 856) 8 ∨
    Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 808) 8 ∨
    Within a (s.getReg .x2 - 792) 16 ∨
    Within a (s.getReg .x2 - 688) 24 ∨
    Within a (s.getReg .x2 - 640) 536 ∨
    Within a (s.getReg .x10 + 8) 352 ∨
    Within a nextAddr 8 ∨
    heapNext h ≤ a.toNat ∧ a.toNat < heapNext r ∨
    Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24)

theorem Zh.i1 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 2464) 1424) : Zh s h r a := by
  unfold Zh
  exact Or.inl hz

theorem Zh.i2 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 1032) 128) : Zh s h r a := by
  unfold Zh
  iterate 1 apply Or.inr
  exact Or.inl hz

theorem Zh.i3 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 968) 16) : Zh s h r a := by
  unfold Zh
  iterate 2 apply Or.inr
  exact Or.inl hz

theorem Zh.i4 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 904) 8) : Zh s h r a := by
  unfold Zh
  iterate 3 apply Or.inr
  exact Or.inl hz

theorem Zh.i5 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 896) 8) : Zh s h r a := by
  unfold Zh
  iterate 4 apply Or.inr
  exact Or.inl hz

theorem Zh.i6 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 872) 8) : Zh s h r a := by
  unfold Zh
  iterate 5 apply Or.inr
  exact Or.inl hz

theorem Zh.i7 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 856) 8) : Zh s h r a := by
  unfold Zh
  iterate 6 apply Or.inr
  exact Or.inl hz

theorem Zh.i8 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 832) 16) : Zh s h r a := by
  unfold Zh
  iterate 7 apply Or.inr
  exact Or.inl hz

theorem Zh.i9 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 808) 8) : Zh s h r a := by
  unfold Zh
  iterate 8 apply Or.inr
  exact Or.inl hz

theorem Zh.i10 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 792) 16) : Zh s h r a := by
  unfold Zh
  iterate 9 apply Or.inr
  exact Or.inl hz

theorem Zh.i11 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 688) 24) : Zh s h r a := by
  unfold Zh
  iterate 10 apply Or.inr
  exact Or.inl hz

theorem Zh.i12 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x2 - 640) 536) : Zh s h r a := by
  unfold Zh
  iterate 11 apply Or.inr
  exact Or.inl hz

theorem Zh.i13 {s h r : MachineState} {a : Word}
    (hz : Within a (s.getReg .x10 + 8) 352) : Zh s h r a := by
  unfold Zh
  iterate 12 apply Or.inr
  exact Or.inl hz

theorem Zh.i14 {s h r : MachineState} {a : Word}
    (hz : Within a nextAddr 8) : Zh s h r a := by
  unfold Zh
  iterate 13 apply Or.inr
  exact Or.inl hz

theorem Zh.i15 {s h r : MachineState} {a : Word}
    (hz : heapNext h ≤ a.toNat ∧ a.toNat < heapNext r) : Zh s h r a := by
  unfold Zh
  iterate 14 apply Or.inr
  exact Or.inl hz

theorem Zh.i16 {s h r : MachineState} {a : Word}
    (hz : Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24)) :
    Zh s h r a := by
  unfold Zh
  iterate 15 apply Or.inr
  exact hz


theorem Merkled.yu {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    {rows : List E} (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame u r (Zu s u r) ∧ heapNext u ≤ heapNext r := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  obtain ⟨F0, m0⟩ := hm.frU hpre
  obtain ⟨F1, m1⟩ := hm.frW hpre hsl hk hr
  refine ⟨(F0.mono fun a ha ↦ ?_).trans (F1.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zu.i12 ha
    · exact Zu.i1 ha
    · exact Zu.i3 ha
    · exact Zu.i5 ha
    · exact Zu.i8 ha
    · exact Zu.i9 (by addr_omega [ha, hb])
    · exact Zu.i10 (by addr_omega [ha, hb])
    · exact Zu.i13 ha
    · simp only [Fresh] at ha; exact Zu.i14 ⟨ha.1, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zu.i12 (by addr_omega [ha, hS])
    · exact Zu.i1 ha
    · exact Zu.i2 ha
    · exact Zu.i4 ha
    · exact Zu.i5 (by addr_omega [ha, hb])
    · exact Zu.i6 ha
    · exact Zu.i7 ha
    · exact Zu.i9 ha
    · exact Zu.i10 ha
    · exact Zu.i11 ha
    · exact Zu.i13 ha
    · simp only [Fresh] at ha; exact Zu.i14 ⟨by omega, ha.2⟩

theorem Merkled.yt {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    {rows : List E} (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame t r (Zt s t r) ∧ heapNext t ≤ heapNext r := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  obtain ⟨Fu, mu⟩ := hm.yu hpre hsl hk hr
  have mt := hm.op.mono
  refine ⟨(hm.op.fr.mono fun a ha ↦ ?_).trans (Fu.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zt.i2 ha
    · exact Zt.i5 ha
    · exact Zt.i6 ha
    · exact Zt.i8 ha
    · exact Zt.i9 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i1 ha
    · exact Zt.i12 ha
    · simp only [W] at ha; exact Zt.i11 ha
    · simp only [Fresh] at ha; exact Zt.i13 ⟨ha.1, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zt.i1 ha
    · exact Zt.i2 (by addr_omega [ha, hb])
    · exact Zt.i3 ha
    · exact Zt.i4 ha
    · exact Zt.i7 ha
    · exact Zt.i9 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i10 (by addr_omega [ha, hb])
    · exact Zt.i11 ha
    · exact Zt.i12 ha
    · simp only [Fresh] at ha; exact Zt.i13 ⟨by omega, ha.2⟩

theorem Merkled.yh {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    {rows : List E} (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame h r (Zh s h r) ∧ heapNext h ≤ heapNext r := by
  obtain ⟨Ft, mt⟩ := hm.yt hpre hsl hk hr
  have hf := hm.op.fo
  have mh : heapNext h ≤ heapNext t := hf.mono
  refine ⟨(hf.fr.mono fun a ha ↦ ?_).trans (Ft.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zh.i7 ha
    · exact Zh.i8 ha
    · exact Zh.i10 ha
    · exact Zh.i11 ha
    · exact Zh.i12 ha
    · exact Zh.i1 ha
    · exact Zh.i14 ha
    · exact Zh.i15 ⟨ha.1, lt_of_lt_of_le ha.2 mt⟩
    · simp only [W] at ha; exact Zh.i13 ha
    · exact Zh.i16 ha
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Zh.i1 ha
    · exact Zh.i2 ha
    · exact Zh.i3 ha
    · exact Zh.i4 ha
    · exact Zh.i5 ha
    · exact Zh.i6 ha
    · exact Zh.i8 ha
    · exact Zh.i9 ha
    · exact Zh.i10 ha
    · exact Zh.i12 ha
    · exact Zh.i13 ha
    · exact Zh.i14 ha
    · simp only [Fresh] at ha; exact Zh.i15 ⟨by omega, ha.2⟩

end Rv64Verifier.Proofs.Pcs.Vso
