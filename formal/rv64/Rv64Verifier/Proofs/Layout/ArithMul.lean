import Rv64Verifier.Proofs.Layout.ArithInit

/-!
# `flushes_arith`: the product sums, `multiply` true

Each lane of `TOWER_LANES` is a first summand (`mulInit*`) and then a site per further summand
(`mulSite_*`); `0x800059d4` moves the last lane's sum to `sp' + 392` and jumps to the `memcpy` from
`sp' + 344`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- `TOWER_LANES`' sums, in the code's order of summands. -/
def lane0 : FormRust :=
  ((({} : FormRust).add (prodRust 5 8 0)).add (prodRust 6 10 0)).add (prodRust 7 9 0)
def lane1 : FormRust :=
  (((({} : FormRust).add (prodRust 5 9 0)).add (prodRust 6 8 0)).add (prodRust 6 10 0)).add
    (prodRust 7 9 0) |>.add (prodRust 7 10 0)
def lane2 : FormRust :=
  (((({} : FormRust).add (prodRust 5 10 0)).add (prodRust 6 9 0)).add (prodRust 7 8 0)).add
    (prodRust 7 10 0)

theorem mulLane0 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005658) (f : FHeld s z fl L0) (hL0 : L0 ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005734 ∧ Inv s w ∧ L0 ≤ heapNext w ∧
      w.getReg .x9 = s.getReg .x2 - 376 ∧ w.getReg .x18 = 0xa00000b0 ∧ w.getReg .x19 = 8 ∧
      FHeld s w fl L0 ∧ Held w (s.getReg .x2 - 400) lane0 L0 (heapNext w)) ∨
      Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hLs := c.mono
  obtain ⟨z₁, hr₁, ⟨hpc₁, c₁, hn₁, x9₁, x18₁, x19₁, f₁, b₁⟩ | hd⟩ :=
    mulInit1 hP hA hpre c hr hpc f hL0
  swap
  · exact ⟨z₁, hr₁, Or.inr hd⟩
  obtain ⟨z₂, hr₂, ⟨hpc₂, c₂, hn₂, x9₂, x18₂, x19₂, b₂, K₂⟩ | hd⟩ :=
    mulSite_800056a4 hP hA hpre c₁ hr₁ hpc₁
      (by rw [x9₁]) (by rw [x18₁])
      b₁ hLs (by omega)
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  have f₂ := K₂.2 _ _ f₁ (by omega)
  obtain ⟨z₃, hr₃, ⟨hpc₃, c₃, hn₃, x9₃, x18₃, x19₃, b₃, K₃⟩ | hd⟩ :=
    mulSite_800056ec hP hA hpre c₂ hr₂ hpc₂
      (by rw [x9₂, x9₁]) (by rw [x18₂, x18₁])
      b₂ hLs (by omega)
  swap
  · exact ⟨z₃, hr₃, Or.inr hd⟩
  have f₃ := K₃.2 _ _ f₂ (by omega)
  refine ⟨z₃, hr₃, Or.inl ⟨hpc₃, c₃, by omega, by rw [x9₃, x9₂, x9₁], by rw [x18₃, x18₂, x18₁],
    by rw [x19₃, x19₂, x19₁], f₃, heldMono b₃ hL0 (Nat.le_refl _)⟩⟩

theorem mulLane1 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005734) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (h19 : z.getReg .x19 = 8) (f : FHeld s z fl L0)
    (hL0 : L0 ≤ heapNext z) (bs : Held z (s.getReg .x2 - 400) lane0 L0 (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800058a8 ∧ Inv s w ∧ L0 ≤ heapNext w ∧
      w.getReg .x9 = s.getReg .x2 - 376 ∧ w.getReg .x18 = 0xa00000b0 ∧ w.getReg .x19 = 8 ∧
      FHeld s w fl L0 ∧ Held w (s.getReg .x2 - 136) lane0 L0 (heapNext w) ∧
      Held w (s.getReg .x2 - 400) lane1 L0 (heapNext w)) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hLs := c.mono
  obtain ⟨z₁, hr₁, ⟨hpc₁, c₁, hn₁, x9₁, x18₁, x19₁, f₁, b₁, r₁⟩ | hd⟩ :=
    mulInit2 hP hA hpre c hr hpc h9 h18 h19 f hL0 bs
  swap
  · exact ⟨z₁, hr₁, Or.inr hd⟩
  obtain ⟨z₂, hr₂, ⟨hpc₂, c₂, hn₂, x9₂, x18₂, x19₂, b₂, K₂⟩ | hd⟩ :=
    mulSite_80005788 hP hA hpre c₁ hr₁ hpc₁
      (by rw [x9₁]) (by rw [x18₁])
      b₁ hLs (by omega)
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  have f₂ := K₂.2 _ _ f₁ (by omega)
  have r₂ := K₂.1 _ _ _ _ r₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, ⟨hpc₃, c₃, hn₃, x9₃, x18₃, x19₃, b₃, K₃⟩ | hd⟩ :=
    mulSite_800057d0 hP hA hpre c₂ hr₂ hpc₂
      (by rw [x9₂, x9₁]) (by rw [x18₂, x18₁])
      b₂ hLs (by omega)
  swap
  · exact ⟨z₃, hr₃, Or.inr hd⟩
  have f₃ := K₃.2 _ _ f₂ (by omega)
  have r₃ := K₃.1 _ _ _ _ r₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₄, hr₄, ⟨hpc₄, c₄, hn₄, x9₄, x18₄, x19₄, b₄, K₄⟩ | hd⟩ :=
    mulSite_80005818 hP hA hpre c₃ hr₃ hpc₃
      (by rw [x9₃, x9₂, x9₁]) (by rw [x18₃, x18₂, x18₁])
      b₃ hLs (by omega)
  swap
  · exact ⟨z₄, hr₄, Or.inr hd⟩
  have f₄ := K₄.2 _ _ f₃ (by omega)
  have r₄ := K₄.1 _ _ _ _ r₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₅, hr₅, ⟨hpc₅, c₅, hn₅, x9₅, x18₅, x19₅, b₅, K₅⟩ | hd⟩ :=
    mulSite_80005860 hP hA hpre c₄ hr₄ hpc₄
      (by rw [x9₄, x9₃, x9₂, x9₁]) (by rw [x18₄, x18₃, x18₂, x18₁])
      b₄ hLs (by omega)
  swap
  · exact ⟨z₅, hr₅, Or.inr hd⟩
  have f₅ := K₅.2 _ _ f₄ (by omega)
  have r₅ := K₅.1 _ _ _ _ r₄ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  refine ⟨z₅, hr₅, Or.inl ⟨hpc₅, c₅, by omega, by rw [x9₅, x9₄, x9₃, x9₂, x9₁],
    by rw [x18₅, x18₄, x18₃, x18₂, x18₁], by rw [x19₅, x19₄, x19₃, x19₂, x19₁], f₅,
    heldMono r₅ (Nat.le_refl _) (by omega), heldMono b₅ hL0 (Nat.le_refl _)⟩⟩

theorem mulLane2 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x800058a8) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (h19 : z.getReg .x19 = 8) (f : FHeld s z fl L0)
    (hL0 : L0 ≤ heapNext z) (r0 : Held z (s.getReg .x2 - 136) lane0 L0 (heapNext z))
    (bs : Held z (s.getReg .x2 - 400) lane1 L0 (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800059d4 ∧ Inv s w ∧ L0 ≤ heapNext w ∧
      FHeld s w fl L0 ∧ Held w (s.getReg .x2 - 136) lane0 L0 (heapNext w) ∧
      Held w (s.getReg .x2 - 112) lane1 L0 (heapNext w) ∧
      Held w (s.getReg .x2 - 400) lane2 L0 (heapNext w)) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hLs := c.mono
  obtain ⟨z₁, hr₁, ⟨hpc₁, c₁, hn₁, x9₁, x18₁, x19₁, f₁, b₁, q₁, r₁⟩ | hd⟩ :=
    mulInit3 hP hA hpre c hr hpc h9 h18 h19 f hL0 bs r0
  swap
  · exact ⟨z₁, hr₁, Or.inr hd⟩
  obtain ⟨z₂, hr₂, ⟨hpc₂, c₂, hn₂, x9₂, x18₂, b₂, K₂⟩ | hd⟩ :=
    mulSite_800058fc hP hA hpre c₁ hr₁ hpc₁
      (by rw [x9₁]) (by rw [x18₁])
      b₁ hLs (by omega)
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  have f₂ := K₂.2 _ _ f₁ (by omega)
  have q₂ := K₂.1 _ _ _ _ q₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r₂ := K₂.1 _ _ _ _ r₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, ⟨hpc₃, c₃, hn₃, x9₃, x18₃, b₃, K₃⟩ | hd⟩ :=
    mulSite_80005944 hP hA hpre c₂ hr₂ hpc₂
      (by rw [x9₂, x9₁]) (by rw [x18₂, x18₁])
      b₂ hLs (by omega)
  swap
  · exact ⟨z₃, hr₃, Or.inr hd⟩
  have f₃ := K₃.2 _ _ f₂ (by omega)
  have q₃ := K₃.1 _ _ _ _ q₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r₃ := K₃.1 _ _ _ _ r₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₄, hr₄, ⟨hpc₄, c₄, hn₄, x9₄, x18₄, b₄, K₄⟩ | hd⟩ :=
    mulSite_8000598c hP hA hpre c₃ hr₃ hpc₃
      (by rw [x9₃, x9₂, x9₁]) (by rw [x18₃, x18₂, x18₁])
      b₃ hLs (by omega)
  swap
  · exact ⟨z₄, hr₄, Or.inr hd⟩
  have f₄ := K₄.2 _ _ f₃ (by omega)
  have q₄ := K₄.1 _ _ _ _ q₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r₄ := K₄.1 _ _ _ _ r₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  exact ⟨z₄, hr₄, Or.inl ⟨hpc₄, c₄, by omega, f₄, heldMono q₄ (Nat.le_refl _) (by omega),
    heldMono r₄ (Nat.le_refl _) (by omega), heldMono b₄ hL0 (Nat.le_refl _)⟩⟩

end Rv64Verifier.Layout.Arith
