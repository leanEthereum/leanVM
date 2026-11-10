import Rv64Verifier.Proofs.Walk.R6L

/-!
# `walk`: a cell's three values

From the cell loop's head (`0x80001d74`): the limb closure for the cell's two limbs (into
`sp + 952`, `sp + 1024`) and `constant(ZERO)` (into `sp + 1096`), to the block that moves them to
the values array (`0x80001df0`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- Limb `j`'s form of cell `c` on side `σ`, from the cell's lanes `e` (even) and `d` (odd). -/
def limbForm (σ : Nat) (e d : Option Nat) : LayoutMirror.FormRust :=
  LayoutMirror.layoutLimbRust (e.map (sideLanes σ + ·)) (d.map (sideLanes σ + ·)) (10 + σ)
    (sideMissing σ)

theorem KR.keeps' {s u t : MachineState} {σ c : Nat} {l : List Reg} (h : KR s u σ c)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ q ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27] : List Reg),
      q ∈ l := by decide) : KR s t σ c :=
  h.keeps fun q hq ↦ hk q (hl q hq)

/-- At `0x80001df0`: the cell's limbs at `sp + 952`, `sp + 1024`, `constant(ZERO)` at
`sp + 1096`, their buffers in order from `h0`. -/
structure Vals (s t : MachineState) (σ c : Nat) (h0 h1 h2 : Nat) : Prop where
  v0 : SF t (s.getReg .x2 - 1704) (limbForm σ (LayoutMirror.keccakCellLanesAt false c).1
    (LayoutMirror.keccakCellLanesAt true c).1) h0 h1
  v1 : SF t (s.getReg .x2 - 1632) (limbForm σ (LayoutMirror.keccakCellLanesAt false c).2
    (LayoutMirror.keccakCellLanesAt true c).2) h1 h2
  v2 : SF t (s.getReg .x2 - 1560) (LayoutMirror.constantRust 0) h2 (heapNext t)
  le : h0 ≤ h1 ∧ h1 ≤ h2 ∧ h2 ≤ heapNext t

set_option maxRecDepth 8192 in
theorem values (hL : Rv64Verifier.Layout.LimbSpec) (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F) (r : KR s u σ c) (hσ : σ < 2) (hc : c < 13)
    (hpc : u.pc = 0x80001d74) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001df0 ∧ KM OI s t A k R Q B σ F ∧ KR s t σ c ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      ∃ h1 h2, Vals s t σ c (heapNext u) h1 h2) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  have x9 := r.x9
  have x19 := r.x19
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001d74_spec hpc (by
    rv_eval [sp, x9, x19]
    and_intros <;> valid_access hval [hb1, hc])
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have K₁ := KM.scr hpre h (MemFrame.dframe (b80001d74_frame h₁ (by rw [sp]; addr_omega [hb1])))
    (fun a ha ↦ Or.inr (Or.inl (by
      rw [e 1240 1416 (by decide)] at ha; simp only [Within] at ha ⊢; addr_omega [ha, hb1])))
    (b80001d74_keeps h₁ .x2 (by decide))
  have r₁ := r.keeps' (b80001d74_keeps h₁)
  have hu₁ := K₁.2.2
  have fr₁ := MemFrame.dframe (b80001d74_frame h₁ (by rw [sp]; addr_omega [hb1]))
  have mk (y : Word) (hy : (s.getReg .x2 - 1392).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat ∨
      (s.getReg .x2 - 2656).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 1416).toNat) :
      u₁.getMem y = u.getMem y :=
    fr₁ y (fun x hx hw ↦ by rw [e 1240 1416 (by decide)] at hw; simp only [Within] at hx hw
                            addr_omega [hx, hw, hy, hb1]) (by addr_omega [hy, hb1])
  have aE : u.getReg .x19 - 16 = s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * c) := by
    rw [x19]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have aE8 : u.getReg .x19 - 8 = s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * c) + 8 := by
    rw [x19]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have aO : u.getReg .x9 - 16 = s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * c) := by
    rw [x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have aO8 : u.getReg .x9 - 8 = s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * c) + 8 := by
    rw [x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have scr (o : Word) (ho : o = s.getReg .x2 - 1704 ∨ o = s.getReg .x2 - 1632 ∨
      o = s.getReg .x2 - 1560 ∨ o = s.getReg .x2 - 416) : InScr s o ∧ InSlot s o 24 := by
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · rcases ho with rfl | rfl | rfl | rfl <;> simp only [Within, Scr] at hx ⊢ <;> addr_omega [hx, hb1]
    · rcases ho with rfl | rfl | rfl | rfl <;> simp only [InSlot] <;> addr_omega [hb1, hb3]
  have env₀ : u₁.getMem (s.getReg .x2 - 1416) = s.getReg .x2 - 272 ∧
      u₁.getMem (s.getReg .x2 - 1408) = s.getReg .x2 - 296 ∧
      u₁.getMem (s.getReg .x2 - 1400) = s.getReg .x2 - 248 :=
    ⟨by rw [← e 1240 1416 (by decide), b80001d74_m_x2_1240 h₁, r.x25],
      by rw [show s.getReg .x2 - 1408 = u.getReg .x2 + 1248 from (e 1248 1408 (by decide)).symm,
        b80001d74_m_x2_1248 h₁, e 2360 296 (by decide)],
      by rw [show s.getReg .x2 - 1400 = u.getReg .x2 + 1256 from (e 1256 1400 (by decide)).symm,
        b80001d74_m_x2_1256 h₁, e 2408 248 (by decide)]⟩
  have le₁ := cellLanes_le false hc
  have lo₁ := cellLanes_le true hc
  obtain ⟨t₁, hr₁', ⟨hpc₁, hp₁, K₁', D₁, nf₁, fv₁⟩ | hd⟩ := limbCall hL hpre K₁.1 hσ
    (b80001d74_pc h₁) (by rw [b80001d74_x10 h₁, e 952 1704 (by decide)])
    (scr _ (Or.inl rfl)).1 (scr _ (Or.inl rfl)).2
    (by rw [b80001d74_x11 h₁, e 1240 1416 (by decide)])
    env₀
    (K₁.1.even c hc).1 (K₁.1.odd c hc).1 le₁.1 lo₁.1
    (by rw [b80001d74_x12 h₁, aE, mk _ (by addr_omega [hb1, hc])])
    (by rw [b80001d74_x13 h₁, aE8, mk _ (by addr_omega [hb1, hc])])
    (by rw [b80001d74_x14 h₁, aO, mk _ (by addr_omega [hb1, hc])])
    (by rw [b80001d74_x15 h₁, aO8, mk _ (by addr_omega [hb1, hc])])
  swap
  · exact ⟨t₁, hr₁.trans hr₁', Or.inr hd⟩
  have R₁ := hr₁.trans hr₁'
  have S₁ := SF.ofNew nf₁ fv₁
  rw [hu₁] at S₁
  have q₁ := r₁.pres hp₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁'.m.inv.sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001db0_spec
    (by rw [hpc₁, returnAddress_eq, b80001d74_x1 h₁]; decide) (by
      rv_eval [sp₁, q₁.x9, q₁.x19]
      and_intros <;> valid_access hval [hb1, hc])
  have m₂ := b80001db0_mem_same h₂
  have K₂ := KM.scr hpre K₁' (Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (b80001db0_keeps h₂ .x2 (by decide))
  have r₂ := q₁.keeps' (b80001db0_keeps h₂)
  have S₂ := S₁.frame (Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) (by addr_omega [hb1]) nf₁.heap K₂.2.2.ge
  have e₁ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₁.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₁ hNM
  have bE : t₁.getReg .x19 = s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * c) + 16 := by
    rw [q₁.x19]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have bE8 : t₁.getReg .x19 + 8 = s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * c) + 16 + 8 := by
    rw [q₁.x19]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have bO : t₁.getReg .x9 = s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * c) + 16 := by
    rw [q₁.x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have bO8 : t₁.getReg .x9 + 8 = s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * c) + 16 + 8 := by
    rw [q₁.x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have env₁ : t₁.getMem (s.getReg .x2 - 1416) = s.getReg .x2 - 272 ∧
      t₁.getMem (s.getReg .x2 - 1408) = s.getReg .x2 - 296 ∧
      t₁.getMem (s.getReg .x2 - 1400) = s.getReg .x2 - 248 := by
    have fr := nf₁.frame
    have kk (y : Word) (hy : (s.getReg .x2 - 1416).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 1392).toNat) :
        t₁.getMem y = u₁.getMem y :=
      fr y (fun x hx hw ↦ by
        rcases hw with hw | hw | hw | hw
        · simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1]
        · rw [stackLo_callee K₁.1.m.inv] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1]
        · simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1]
        · simp only [Fresh] at hw; have hh := nf₁.heap.hi; simp only [Within, heapEnd] at hx hh
          addr_omega [hx, hw, hy, hb1, hh]) (by addr_omega [hy, hb1])
    exact ⟨by rw [kk _ (by addr_omega [hb1])]; exact env₀.1,
      by rw [kk _ (by addr_omega [hb1])]; exact env₀.2.1, by rw [kk _ (by addr_omega [hb1])]; exact env₀.2.2⟩
  obtain ⟨t₂, hr₂', ⟨hpc₂, hp₂, K₂', D₂, nf₂, fv₂⟩ | hd⟩ := limbCall hL hpre K₂.1 hσ
    (b80001db0_pc h₂) (by rw [b80001db0_x10 h₂, e₁ 1024 1632 (by decide)])
    (scr _ (Or.inr (Or.inl rfl))).1 (scr _ (Or.inr (Or.inl rfl))).2
    (by rw [b80001db0_x11 h₂, e₁ 1240 1416 (by decide)])
    ⟨by rw [m₂]; exact env₁.1, by rw [m₂]; exact env₁.2.1, by rw [m₂]; exact env₁.2.2⟩
    (K₂.1.even c hc).2 (K₂.1.odd c hc).2 le₁.2 lo₁.2
    (by rw [b80001db0_x12 h₂, bE, m₂])
    (by rw [b80001db0_x13 h₂, bE8, m₂])
    (by rw [b80001db0_x14 h₂, bO, m₂])
    (by rw [b80001db0_x15 h₂, bO8, m₂])
  swap
  · exact ⟨t₂, R₁.trans (hr₂.trans hr₂'), Or.inr hd⟩
  have R₂ := R₁.trans (hr₂.trans hr₂')
  have S₂' := SF.ofNew nf₂ fv₂
  rw [K₂.2.2] at S₂'
  have q₂ := r₂.pres hp₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := K₂'.m.inv.sp
  have I₂ := K₂.1.m.inv
  have S₁₂ := SF.call hpre I₂ S₂ nf₂.frame (by decide)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (by addr_omega [hb1]) K₂.2.2.ge nf₂.heap nf₂.mono
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80001dd0_spec
    (by rw [hpc₂, returnAddress_eq, b80001db0_x1 h₂]; decide) (by
      rv_eval [q₂.x26]
      valid_access hval [hb1])
  have x26₂ := q₂.x26
  have f₃ : Rv64Verifier.Layout.DFrame t₂ u₃ (Within · (s.getReg .x2 - 416) 8) := by
    have := MemFrame.dframe (b80001dd0_frame h₃ (by rw [x26₂]; addr_omega [hb1]))
    rwa [x26₂, show s.getReg .x2 - 512 + 96 = s.getReg .x2 - 416 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
  have K₃ := KM.scr hpre K₂' f₃ (fun a ha ↦ Or.inr (Or.inr (Or.inl (by
      simp only [Within] at ha ⊢; addr_omega [ha, hb1])))) (b80001dd0_keeps h₃ .x2 (by decide))
  have r₃ := q₂.keeps' (b80001dd0_keeps h₃)
  have hh₂ := nf₂.heap
  have T₁ := S₁₂.frame f₃ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (fun x hx1 hx2 hw ↦ by
      have a := hh₂.hi; have b := nf₂.mono; have c := K₂.2.2
      simp only [Within] at hw; simp only [heapEnd] at a; addr_omega [hw, hx2, hb1, a, b, c])
    (by addr_omega [hb1]) hh₂ K₃.2.2.ge
  have T₂ := S₂'.frame f₃ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (fun x hx1 hx2 hw ↦ by
      have a := hh₂.hi
      simp only [Within] at hw; simp only [heapEnd] at a; addr_omega [hw, hx2, hb1, a])
    (by addr_omega [hb1]) hh₂ K₃.2.2.ge
  have z₃ : u₃.getMem (s.getReg .x2 - 416) = 0 := by
    rw [show s.getReg .x2 - 416 = t₂.getReg .x26 + 96 by
      rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact b80001dd0_m_x26_96 h₃
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := K₃.1.m.inv.sp
  have e₃ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₂.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₂ hNM
  obtain ⟨t₃, hr₃', ⟨hpc₃, hp₃, K₃', D₃, nf₃, fv₃⟩ | hd⟩ := termCall hT hpre K₃.1
    (b80001dd0_pc h₃) (by rw [b80001dd0_x10 h₃, e₃ 1096 1560 (by decide)])
    (scr _ (Or.inr (Or.inr (Or.inl rfl)))).1 (scr _ (Or.inr (Or.inr (Or.inl rfl)))).2
    (by rw [b80001dd0_x11 h₃, e₃ 2240 416 (by decide)]) (scr _ (Or.inr (Or.inr (Or.inr rfl)))).2 z₃
    (b80001dd0_x12 h₃) ⟨by decide, by decide, by decide⟩
  swap
  · exact ⟨t₃, R₂.trans (hr₃.trans hr₃'), Or.inr hd⟩
  have I₃ := K₃.1.m.inv
  have S₃ := SF.ofNew nf₃ fv₃
  rw [Rv64Verifier.Layout.MemoryCols.eAt_zero (I₃.rodata hpre)] at S₃
  have hh₃ := nf₃.heap
  have U₁ := SF.call hpre I₃ T₁ nf₃.frame (by decide)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (by addr_omega [hb1]) (by have := nf₂.mono; have := K₃.2.2; have := K₂.2.2; omega) hh₃ nf₃.mono
  have U₂ := SF.call hpre I₃ T₂ nf₃.frame (by decide)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (by addr_omega [hb1]) K₃.2.2.ge hh₃ nf₃.mono
  refine ⟨t₃, R₂.trans (hr₃.trans hr₃'), Or.inl ⟨by rw [hpc₃, returnAddress_eq, b80001dd0_x1 h₃]; decide,
    K₃', r₃.pres hp₃, by rw [D₃, K₃.2.1, D₂, K₂.2.1, D₁, K₁.2.1], heapNext t₁, heapNext t₂,
    ⟨U₁, U₂, by rw [K₃.2.2] at S₃; exact S₃, ?_⟩⟩⟩
  have := nf₁.mono; have := nf₂.mono; have := nf₃.mono; have := K₃.2.2; have := K₂.2.2
  omega

end Rv64Verifier.Proofs.Walk
