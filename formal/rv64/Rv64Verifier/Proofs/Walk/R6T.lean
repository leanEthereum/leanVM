import Rv64Verifier.Proofs.Walk.R6S

/-!
# `walk`: the cell loop's setup

From the first `keccak_cell_lanes` call (`AtR6a`): the even lanes into `sp + 1312`, the odd ones
into `sp + 1728`, the block at `0x80001b30` writing both sides' tuples and `O_M`'s address, then
side 0's start, to the loop's head (`0x80001d74`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- `keccak_cell_lanes(odd)` into the 416 bytes at `o`, past `sp + 576`, apart from the `Flushes`:
`walk`'s state, the `Flushes`, the heights' lengths kept. -/
theorem cellLanesCall (hCL : Rv64Verifier.Layout.CellLanesSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {F : LayoutMirror.FlushesRust} {o : Word}
    (hpre : WalkPre s) (m : M6 OI s u A k R Q B) (fl : FlAt s u F B)
    (lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0)
    (hpc : u.pc = 0x80004d10) (x10 : u.getReg .x10 = o)
    (ho : (s.getReg .x2 - 1344).toNat ≤ o.toNat ∧ o.toNat + 416 ≤ (s.getReg .x2 - 512).toNat ∧
      o.toNat % 8 = 0) (x11 : u.getReg .x11 = 0 ∨ u.getReg .x11 = 1) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M6 OI s t A k R Q B ∧ FlAt s t F B ∧
      (t.getMem (s.getReg .x2 - 2520) = 6 ∧ t.getMem (s.getReg .x2 - 2504) = 0) ∧
      Rv64Verifier.Layout.CellLanesPost u t ∧
      ∀ y, (y.toNat + 8 ≤ o.toNat ∨ o.toNat + 416 ≤ y.toNat) →
        (s.getReg .x2 - 2656).toNat ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat →
        t.getMem y = u.getMem y) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have I := m.inv
  have hn : Rv64Verifier.Layout.cellLanesStack ≤ 8736 := by decide
  obtain ⟨o1, o2, o3⟩ := ho
  have pre : Rv64Verifier.Layout.CellLanesPre u := {
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact Or.inr ⟨by addr_omega [hb1, o1], by addr_omega [hb1, hb2, o2]⟩
    outAligned := by rw [x10]; exact o3
    outStack := by rw [x10, stackLo_callee I]; addr_omega [hb1, hn, o1, o2]
    odd := x11 }
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hd⟩ := hCL u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have fr := post.frame
  rw [x10] at fr
  have keep (y : Word) (hy : y.toNat + 8 ≤ o.toNat ∨ o.toNat + 416 ≤ y.toNat)
      (h1 : (s.getReg .x2 - 2656).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) :
      t.getMem y = u.getMem y :=
    fr y (fun x hx hw ↦ by
      rcases hw with hw | hw
      · simp only [Within] at hx hw; omega
      · rw [stackLo_callee I] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hy, h1, hb1, hn])
      (by addr_omega [h2, hb1])
  have hnx : heapNext t = heapNext u := by
    simp only [heapNext]
    rw [fr nextAddr (fun x hx hw ↦ by
      rcases hw with hw | hw
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1, o1]
      · rw [stackLo_callee I] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn])
      (by decide)]
  have hh := I.heap
  have M := m.step hpre (fr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1, o1, o2])
      · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre I hn ha)))))
    ⟨hnx ▸ hh.lo, hnx ▸ hh.hi⟩ hnx.ge (hp .x2 (by decide))
  have FL := fl.frame hpre fr (fun x hx hw ↦ by
      rcases hw with hw | hw
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1, o1, o2]
      · rw [stackLo_callee I] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn])
    (fun x hx hw ↦ by
      have := (fl.ok.deep_below hx).2; have hu := hh.hi
      simp only [heapEnd, heapNext] at this hu
      rcases hw with hw | hw
      · simp only [Within] at hw; addr_omega [hw, this, hu, hb1, o1]
      · rw [stackLo_callee I] at hw; simp only [Within] at hw; addr_omega [hw, this, hu, hb1, hn])
    hh hnx.ge
  refine ⟨t, hr, Or.inl ⟨hpct, hp, M, FL.1, ⟨?_, ?_⟩, post, keep⟩⟩
  · rw [keep _ (by addr_omega [hb1, o1]) (by addr_omega [hb1]) (by addr_omega [hb1])]; exact lens.1
  · rw [keep _ (by addr_omega [hb1, o1]) (by addr_omega [hb1]) (by addr_omega [hb1])]; exact lens.2

set_option maxRecDepth 8192 in
/-- From the first `keccak_cell_lanes` call to the loop's head, side 0, cell 0. -/
theorem setup (hCL : Rv64Verifier.Layout.CellLanesSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s)
    (h : AtR6a OI s u A k R Q B) (hpc : u.pc = 0x80004d10) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d74 ∧ KM OI s t A k R Q B 0 keccakHead ∧
      KR s t 0 0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t₁, r₁, ⟨p₁, hp₁, M₁, F₁, L₁, P₁, K₁⟩ | d⟩ := cellLanesCall hCL hpre h.m h.fl h.lens hpc h.x10
    (by addr_omega [hb1, hb3]) (Or.inl h.x11)
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  have hd0 : decide (u.getReg .x11 = 1) = false := by rw [h.x11]; rfl
  have E := P₁.cells
  rw [h.x10, hd0] at E
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001b1c_spec
    (by rw [p₁, returnAddress_eq, h.x1]; decide) (by rv_eval [])
  have m₂ := b80001b1c_mem_same g₂
  have k₂ := b80001b1c_keeps g₂
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.inv.sp
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have hh₁ := M₁.inv.heap
  have M₂ := M₁.step hpre (Rv64Verifier.Layout.DFrame.of_same m₂ _) ⟨hn₂ ▸ hh₁.lo, hn₂ ▸ hh₁.hi⟩
    hn₂.ge (k₂ .x2 (by decide))
  have F₂ := F₁.frame hpre (Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) hh₁ hn₂.ge
  obtain ⟨t₂, r₃, ⟨p₃, hp₃, M₃, F₃, L₃, P₃, K₃⟩ | d⟩ := cellLanesCall hCL hpre M₂ F₂.1
    ⟨by rw [m₂]; exact L₁.1, by rw [m₂]; exact L₁.2⟩ (b80001b1c_pc g₂)
    (by rw [b80001b1c_x10 g₂, spAdd hpre sp₁ (by decide : (1728 : Word).toNat + (928 : Word).toNat = 2656)])
    (by addr_omega [hb1, hb3]) (Or.inr (b80001b1c_x11 g₂))
  swap
  · exact ⟨t₂, r₁.trans (r₂.trans r₃), Or.inr d⟩
  have hd1 : decide (u₂.getReg .x11 = 1) = true := by rw [b80001b1c_x11 g₂]; rfl
  have O := P₃.cells
  rw [b80001b1c_x10 g₂, spAdd hpre sp₁ (by decide : (1728 : Word).toNat + (928 : Word).toNat = 2656),
    hd1] at O
  have R₃ := r₁.trans (r₂.trans r₃)
  have pr (r : Reg) (hr : r ∈ calleeSaved) (hr2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x12, .x13, .x14, .x15,
      .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) : t₂.getReg r = u.getReg r := by
    rw [hp₃ r hr, k₂ r hr2, hp₁ r hr]
  have x26₂ : t₂.getReg .x26 = s.getReg .x2 - 512 := by rw [pr .x26 (by decide) (by decide)]; exact h.x26
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₃.inv.sp
  have x9₂ : t₂.getReg .x9 = 1 := by rw [hp₃ .x9 (by decide)]; exact b80001b1c_x9 g₂
  obtain ⟨u₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b80001b30_spec
    (by rw [p₃, returnAddress_eq, b80001b1c_x1 g₂]; decide) (by
      rv_eval [sp₂, x26₂]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | (intro he; have := congrArg BitVec.toNat he; addr_omega [hb1, this]))
  have fr₄ : Rv64Verifier.Layout.DFrame t₂ u₄ fun a ↦ Within a (s.getReg .x2 - 496) 72 ∨
      Within a (s.getReg .x2 - 2472) 8 := Expect.ldframe g₄ (by
    rv_eval [sp₂, x26₂]
    simp only [Within]
    and_intros <;> addr_omega [hb1])
  have k₄ := b80001b30_keeps g₄
  have keep (y : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 2472).toNat ∨
      (s.getReg .x2 - 2464).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 496).toNat ∨
      (s.getReg .x2 - 424).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) :
      u₄.getMem y = t₂.getMem y :=
    fr₄ y (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hy, hb1])
      (by addr_omega [hy, hb1])
  have hn₄ : heapNext u₄ = heapNext t₂ := by
    simp only [heapNext]
    rw [fr₄ nextAddr (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by decide)]
  have hh₂ := M₃.inv.heap
  have M₄ := M₃.step hpre (fr₄.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ha)))))
    ⟨hn₄ ▸ hh₂.lo, hn₄ ▸ hh₂.hi⟩ hn₄.ge (k₄ .x2 (by decide))
  have F₄ := F₃.frame hpre fr₄ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
    (fun x hx hw ↦ by
      have := (F₃.ok.deep_below hx).2; have hu := hh₂.hi
      simp only [heapEnd, heapNext] at this hu
      simp only [Within] at hw; rcases hw with hw | hw <;> addr_omega [hw, this, hu, hb1])
    hh₂ hn₄.ge
  have e26 (N M : Word) (hNM : N.toNat + M.toNat = 512) : t₂.getReg .x26 + N = s.getReg .x2 - M := by
    rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have z0 : s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * 0) = s.getReg .x2 - 496 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have kb : KMb OI s u₄ A k R Q B 0 keccakHead := {
    m := M₄
    fl := F₄.1
    lens := by rw [keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1])]; exact L₃
    even := fun i hi ↦ by
      obtain ⟨a1, a2⟩ := E i hi
      rw [show s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i + 16) =
        s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i) + 16 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]] at a2
      refine ⟨OptAt.congr (OptAt.congr a1 ?_ ?_) (keep _ ?_) (keep _ ?_),
        OptAt.congr (OptAt.congr a2 ?_ ?_) (keep _ ?_) (keep _ ?_)⟩
      all_goals first
        | (rw [K₃ _ (by addr_omega [hb1, hi]) (by addr_omega [hb1, hi]) (by addr_omega [hb1, hi]), m₂])
        | addr_omega [hb1, hi]
    odd := fun i hi ↦ by
      obtain ⟨a1, a2⟩ := O i hi
      rw [show s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i + 16) =
        s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i) + 16 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]] at a2
      exact ⟨OptAt.congr a1 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi])),
        OptAt.congr a2 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi]))⟩
    p184 := by
      rw [← spAdd hpre sp₂ (by decide : (184 : Word).toNat + (2472 : Word).toNat = 2656)]
      exact b80001b30_m_x2_184 g₄
    tside := by rw [z0, ← e26 16 496 (by decide)]; exact b80001b30_m_x26_16 g₄
    tlanes := by
      rw [z0, show s.getReg .x2 - 496 + 8 = t₂.getReg .x26 + 24 by
        rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact b80001b30_m_x26_24 g₄
    tflag := by
      rw [z0, show s.getReg .x2 - 496 + 16 = t₂.getReg .x26 + 32 by
        rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80001b30_m_x26_32 g₄,
        pr .x19 (by decide) (by decide), h.x19]; rfl
    tmissing := by
      rw [z0]
      refine ⟨?_, ?_⟩
      · rw [show s.getReg .x2 - 496 + 24 = t₂.getReg .x26 + 40 by
          rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80001b30_m_x26_40 g₄, x9₂]
      · rw [show s.getReg .x2 - 496 + 24 + 8 = t₂.getReg .x26 + 48 by
          rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80001b30_m_x26_48 g₄]; rfl
    next := fun _ ↦ ⟨by rw [← e26 56 456 (by decide), b80001b30_m_x26_56 g₄, x9₂],
      by rw [← e26 64 448 (by decide), b80001b30_m_x26_64 g₄],
      by rw [← e26 72 440 (by decide), b80001b30_m_x26_72 g₄, pr .x21 (by decide) (by decide), h.x21],
      by rw [← e26 80 432 (by decide), b80001b30_m_x26_80 g₄]⟩ }
  have e₂ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₂.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₂ hNM
  obtain ⟨t, rt, pt, K, KR⟩ := sideStart hpre kb (by decide) (b80001b30_pc g₄)
    (b80001b30_x10 g₄) (b80001b30_x15 g₄) (by rw [b80001b30_x8 g₄, e₂ 2456 200 (by decide)])
    (by rw [k₄ .x18 (by decide), pr .x18 (by decide) (by decide)]; exact h.x18)
    (by rw [b80001b30_x20 g₄, e₂ 2480 176 (by decide)]) (by rw [b80001b30_x25 g₄, e₂ 2384 272 (by decide)])
    (by rw [k₄ .x26 (by decide)]; exact x26₂)
  exact ⟨t, R₃.trans (r₄.trans rt), Or.inl ⟨pt, K, KR⟩⟩

end Rv64Verifier.Proofs.Walk
