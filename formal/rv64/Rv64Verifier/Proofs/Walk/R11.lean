import Rv64Verifier.Proofs.Walk.App11

/-!
# `walk`: R11, `kappas`, from `0x80003038` to `0x800031dc`

`kapTable`: one table (`kapCheck`, `vec![h; w]`, `kapReserve`, `kapCopy`). `r11`: the head, then the
six tables, `kappas` holding `kapPre A k 6` (`kapPre_six`: `kappasRust`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- One table of `kappas`. -/
theorem kapTable (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    (hRS : ReserveFreshSpec 0x8000d628 8 8) (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 i : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x800030c8)
    (h : Kap11 OI s u A k R Q B lo lo2 i) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = (if i + 1 = 6 then 0x800031dc else 0x800030c8) ∧
        Lat11 OI s t A k R Q B lo lo2 (i + 1))) := by
  obtain ⟨c, hr, hpcc, mc, kc, x10, x21, x24⟩ := kapCheck hpre hpc h
  have tmp : ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨
      (t.pc = 0x800031a4 ∧ ∃ T, Tmp11 OI s t A k R Q B lo lo2 i T)) := by
    split_ifs at hpcc with h0
    · exact kapTmpB hTA hpre h hpcc mc kc x10 x24 h0
    · exact kapTmpA hTA hRF hpre h hpcc mc kc x10 x21 x24
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, T, h₁⟩⟩ := tmp
  · exact ⟨t₁, hr.trans hr₁, Or.inl hd⟩
  obtain ⟨t₂, hr₂, hd | ⟨hpc₂, h₂⟩⟩ := kapReserve hRS hpre hpc₁ h₁
  · exact ⟨t₂, hr.trans (hr₁.trans hr₂), Or.inl hd⟩
  obtain ⟨t₃, hr₃, ht₃⟩ := kapCopy hMC hpre hpc₂ h₂
  exact ⟨t₃, hr.trans (hr₁.trans (hr₂.trans hr₃)), ht₃⟩

/-- R11: from `0x80003038` to `0x800031dc`, `kappas` built. -/
theorem r11 (hAS : AllocSpec) (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    (hRS : ReserveFreshSpec 0x8000d628 8 8) (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80003038)
    (h : AtR11 OI s u A k R Q B lo) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800031dc ∧ Lat11 OI s t A k R Q B lo (heapNext u) 6)) := by
  obtain ⟨u₀, hr₀, hd | ⟨hpc₀, h₀⟩⟩ := r11head hAS hpre hpc h
  · exact ⟨u₀, hr₀, Or.inl hd⟩
  have key : ∀ d i v, 6 - i = d → v.pc = 0x800030c8 →
      Kap11 OI s v A k R Q B lo (heapNext u) i → ∃ t, Reaches Image.code v t ∧ (Dead Image.code t ∨
        (t.pc = 0x800031dc ∧ Lat11 OI s t A k R Q B lo (heapNext u) 6)) := by
    intro d
    induction d with
    | zero => intro i v hd _ hv; have := hv.lt; omega
    | succ d ih =>
      intro i v hd hpcv hv
      obtain ⟨t, hr, hd' | ⟨hpct, ht⟩⟩ := kapTable hTA hRF hRS hMC hpre hpcv hv
      · exact ⟨t, hr, Or.inl hd'⟩
      by_cases h6 : i + 1 = 6
      · simp only [h6, ↓reduceIte] at hpct
        rw [h6] at ht
        exact ⟨t, hr, Or.inr ⟨hpct, ht⟩⟩
      · simp only [h6, ↓reduceIte] at hpct
        obtain ⟨t', hr', ht'⟩ := ih (i + 1) t (by omega) hpct (ht.kap11 (by have := ht.le; omega))
        exact ⟨t', hr.trans hr', ht'⟩
  obtain ⟨t, hr, ht⟩ := key 6 0 u₀ rfl hpc₀ h₀
  exact ⟨t, hr₀.trans hr, ht⟩

end Rv64Verifier.Proofs.Walk
