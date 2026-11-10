import Rv64Verifier.Proofs.Walk.R7C

/-!
# `walk`: `tables()`, from `flushes_keccak()` to the tables' buffer (R6's tail and R7)

The padding loop's 25 lanes (`lanes`), its entry (`entry`), `alloc(8, 480)` for the six tables
(`exit`), and the whole stretch from `0x80001f00` to `0x80002024` (`r7`), where `M8` holds: the
KECCAK `Table` finished at `sp + 952`, the tables' buffer `Bb` at `sp + 200`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- `tables()` under way: `walk`'s state, the heights' lengths, the tables' buffer `Bb` (at
`sp + 200`), and the finished tables `L` (a frame slot and the table it holds), all they reach in
`[B, W)` and apart from `Bb`, each table's 72 bytes in the frame. -/
structure M8 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) (W : Nat)
    (L : List (Word × LayoutMirror.TableRust)) : Prop where
  m : M6 OI s u A k R Q B
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0
  bb : B ≤ Bb.toNat ∧ Bb.toNat % 8 = 0 ∧ Bb.toNat + 480 ≤ W ∧ W ≤ heapNext u
  slot : u.getMem (s.getReg .x2 - 2456) = Bb
  tabs : ∀ e ∈ L, InSlot s e.1 72 ∧ TableAt u e.1 e.2 ∧
    ∀ x, tableDeep u e.1 x → B ≤ x.toNat ∧ x.toNat < W ∧ ¬ Within x Bb 480

theorem LP.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} {l : Nat} (hpre : WalkPre s)
    (h : LP OI s u A k R Q B D P l) (hm : ∀ a, v.getMem a = u.getMem a)
    (sp : v.getReg .x2 = u.getReg .x2) : LP OI s v A k R Q B D P l := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have fr := Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False)
  exact ⟨h.k7.step hpre fr (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
      ⟨hn ▸ h.k7.m.inv.heap.lo, hn ▸ h.k7.m.inv.heap.hi⟩ hn.ge sp,
    h.hv.frame fr (fun _ _ h ↦ h) (by addr_omega [hb1]) hn.ge,
    fun j hj ↦ by rw [hm]; exact h.lanes j hj,
    fun i hi ↦ by rw [eAt_congr (hm _) (hm _) (hm _)]; exact h.pad i hi⟩

/-- The padding loop from its head after `l` lanes to its exit. -/
theorem lanes {OI : MachineState → Word → List (List Opening) → Prop} {s : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} (hpre : WalkPre s) (n : Nat) :
    ∀ (l : Nat) (u : MachineState), l + n = 25 → LP OI s u A k R Q B D P l → LR s u P l →
      u.pc = 0x80001fe0 → ∃ t, Reaches Image.code u t ∧ t.pc = 0x80002004 ∧
        LP OI s t A k R Q B D P 25 := by
  induction n with
  | zero =>
    intro l u hl h r hpc
    subst hl
    obtain ⟨t, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001fe0_spec hpc trivial
    exact ⟨t, r₁, b80001fe0_pc_taken g₁ (by rw [r.x11]; rfl),
      h.same hpre (b80001fe0_mem_same g₁) (b80001fe0_keeps g₁ .x2 (by decide))⟩
  | succ n ih =>
    intro l u hl h r hpc
    obtain ⟨t, r₁, p₁, h₁, x₁⟩ := lane hpre h r (by omega) hpc
    obtain ⟨t', r₂, p₂, h₂⟩ := ih (l + 1) t (by omega) h₁ x₁ p₁
    exact ⟨t', r₁.trans r₂, p₂, h₂⟩

set_option maxRecDepth 8192 in
/-- The loop's entry: the iterator's words, `padding[KECCAK_OUT..]`'s start. -/
theorem entry {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} (hpre : WalkPre s)
    (h : K7L OI s u A k R Q B D P) (x8 : u.getReg .x8 = P + 2208) (x9 : u.getReg .x9 = P)
    (x18 : u.getReg .x18 = 2208) (x23 : u.getReg .x23 = s.getReg .x2 - 896) (hpc : u.pc = 0x80001fbc) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001fe0 ∧ LP OI s t A k R Q B D P 0 ∧ LR s t P 0 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := h.k7.m.inv.sp
  have hu := h.k7.m.inv.heap.hi
  have zb := h.z.buf
  simp only [heapEnd] at hu
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001fbc_spec hpc (by
    rv_eval [sp₀]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80001fbc_keeps g₁
  have fr₁ : Rv64Verifier.Layout.DFrame u u₁ fun x ↦ Within x (s.getReg .x2 - 920) 24 ∨
      Within x (s.getReg .x2 - 696) 16 :=
    Expect.ldframe g₁ (by
      rv_eval [sp₀]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]; rw [fr₁ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by decide)]
  have K₁ := h.k7.step hpre fr₁ (fun x hx ↦ Or.inl (by
      simp only [Within] at hx ⊢; rcases hx with hx | hx <;> addr_omega [hx, hb1]))
    (fun x hx ↦ by
      simp only [K7W, Within] at hx ⊢
      rcases hx with hx | hx <;> refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> addr_omega [hx, hb1, hu, zb])
    ⟨hn₁ ▸ h.k7.m.inv.heap.lo, hn₁ ▸ h.k7.m.inv.heap.hi⟩ hn₁.ge (k₁ .x2 (by decide))
  have keep (y : Word) (hy : y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨
      ((s.getReg .x2 - 896).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 696).toNat) ∨
      ((s.getReg .x2 - 680).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ 2 ^ 64)) : u₁.getMem y = u.getMem y :=
    fr₁ y (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> rcases hy with hy | hy | hy <;>
        addr_omega [hx, hw, hy, hb1]) (by rcases hy with hy | hy | hy <;> addr_omega [hy, hb1])
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001fd8_spec
    (b80001fbc_pc_not_taken g₁ (by rw [x18]; decide)) trivial
  have k₂ := b80001fd8_keeps g₂
  have m₂ := b80001fd8_mem_same g₂
  have L₁ : LP OI s u₁ A k R Q B D P 0 :=
    ⟨K₁, h.z.h.frame fr₁ (fun x hx hw ↦ by
        simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by addr_omega [hb1])
        hn₁.ge,
      fun j hj ↦ by rw [keep _ (by addr_omega [hb1, hj])]; exact h.lanes j hj,
      fun i hi ↦ by
        rw [eAt_congr (keep _ (by addr_omega [hb1, hi, zb, hu])) (keep _ (by addr_omega [hb1, hi, zb, hu]))
          (keep _ (by addr_omega [hb1, hi, zb, hu])), h.z.zero i hi]
        simp only [padE]; split <;> first | rfl | omega⟩
  refine ⟨u₂, r₁.trans r₂, b80001fd8_pc g₂, L₁.same hpre m₂ (k₂ .x2 (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [k₂ .x8 (by decide), k₁ .x8 (by decide), x8]
  · rw [b80001fd8_x10 g₂, k₁ .x9 (by decide), x9]; rfl
  · rw [b80001fd8_x11 g₂]; rfl
  · rw [k₂ .x23 (by decide), k₁ .x23 (by decide), x23]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]

set_option maxRecDepth 8192 in
/-- `alloc(8, 480)` for the six tables, its pointer to `sp + 200`: the KECCAK `Table` is finished. -/
theorem exit7 (hAS : AllocSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} (hpre : WalkPre s)
    (h : LP OI s u A k R Q B D P 25) (hpc : u.pc = 0x80002004) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002024 ∧ ∃ Bb, M8 OI s t A k R Q B Bb (heapNext t)
      [(s.getReg .x2 - 1704, kTable)] ∧ t.getReg .x8 = 8) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80002004_spec hpc trivial
  have k₁ := b80002004_keeps g₁
  have L₁ := h.same hpre (b80002004_mem_same g₁) (k₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := L₁.k7.m.inv.sp
  have hu := L₁.k7.m.inv.heap.hi
  have hlo := L₁.k7.m.inv.heap.lo
  have hb := L₁.hv.buf
  have hBD := L₁.k7.buf
  simp only [heapEnd, heapStart] at hu hlo
  obtain ⟨u₂, r₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hAS.call (Reaches.refl u₁) (b80002004_pc g₁)
    ⟨L₁.k7.m.inv.heap, by rw [b80002004_x10 g₁]; decide⟩
  swap
  · exact ⟨u₂, r₁.trans r₂, Or.inr hd⟩
  have hal := post₂.aligned
  have hab := post₂.above
  have hnx := post₂.next
  rw [b80002004_x10 g₁] at hal
  rw [b80002004_x11 g₁] at hnx
  rw [show (8 : Word).toNat = 8 from rfl] at hal
  rw [show (480 : Word).toNat = 480 from rfl] at hnx
  set Bb := u₂.getReg .x10 with hBb
  have fr₂ : Rv64Verifier.Layout.DFrame u₁ u₂ (Within · nextAddr 8) := fun a ha _ ↦
    post₂.mem a fun he ↦ ha a (by simp only [Within]; omega) (by rw [he]; simp only [Within]; omega)
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := (hp₂.reg .x2).trans sp₁
  obtain ⟨u₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80002018_spec
    (by rw [hpc₂, returnAddress_eq, b80002004_x1 g₁]; decide) (by
      rv_eval [sp₂]
      valid_access hval [hb1])
  have fr₃ : Rv64Verifier.Layout.DFrame u₂ u₃ fun x ↦ Within x (s.getReg .x2 - 2456) 8 :=
    Expect.ldframe g₃ (by
      rv_eval [sp₂]
      simp only [Within]
      addr_omega [hb1])
  have hBb0 : Bb ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [show (0 : Word).toNat = 0 from rfl] at this; omega
  have p₃ := b80002018_pc_taken g₃ hBb0
  have fr : Rv64Verifier.Layout.DFrame u₁ u₃ fun x ↦ Within x nextAddr 8 ∨
      Within x (s.getReg .x2 - 2456) 8 := fr₂.union fr₃
  have hn₃ : heapNext u₃ = heapNext u₂ := by
    simp only [heapNext]; rw [fr₃ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have hh₂ := post₂.heap
  have mono : heapNext u₁ ≤ heapNext u₃ := by rw [hn₃, hnx]; omega
  have K₃ := L₁.k7.step hpre fr (fun x hx ↦ by
      rcases hx with hx | hx
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hx)))))
    (fun x hx ↦ by
      simp only [K7W, Within, nextAddr] at hx ⊢
      rcases hx with hx | hx <;> refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> addr_omega [hx, hb1, hu, hBD])
    ⟨hn₃ ▸ hh₂.lo, hn₃ ▸ hh₂.hi⟩ mono ((b80002018_keeps g₃ .x2 (by decide)).trans (hp₂.reg .x2))
  have keep (y : Word) (hy : y.toNat + 8 ≤ heapNext u₁) : u₃.getMem y = u₁.getMem y :=
    fr y (fun x hx hw ↦ by
      simp only [Within, nextAddr, heapNext] at hx hw hy hu
      rcases hw with hw | hw <;> addr_omega [hx, hw, hy, hb1, hu]) (by omega)
  have hv₃ := L₁.hv.frame fr (fun x hx hw ↦ by
    simp only [Within, nextAddr] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by addr_omega [hb1])
    mono
  have hcap : vecCap u₃ (s.getReg .x2 - 1704) = vecCap u₁ (s.getReg .x2 - 1704) := by
    simp only [vecCap]
    exact fr _ (fun x hx hw ↦ by
      simp only [Within, nextAddr] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by addr_omega [hb1])
  have hraw := L₁.hv.vec.raw
  simp only [RawVecOk, Buf, L₁.hv.ptr] at hraw
  have e24 : s.getReg .x2 - 1704 + 24 = s.getReg .x2 - 1680 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hpad : vecEs u₃ (s.getReg .x2 - 1704) = kPad := by
    simp only [vecEs, hv₃.ptr, hv₃.len, show (BitVec.ofNat 64 92).toNat = 92 from rfl]
    apply List.ext_getElem (by rw [eListAt_length, kPad_length])
    intro i h1 h2
    rw [eListAt_length] at h1
    rw [eListAt_getElem, ← List.getD_eq_getElem _ (0 : E) h2, kPad_getD i h1,
      eAt_congr (keep _ (by addr_omega [hb, h1])) (keep _ (by addr_omega [hb, h1])) (keep _ (by addr_omega [hb, h1])),
      L₁.pad i h1]
  refine ⟨u₃, r₁.trans (r₂.trans r₃), Or.inl ⟨p₃, Bb, {
    m := K₃.m
    lens := K₃.lens
    bb := ⟨by omega, hal, by rw [hn₃, hnx], le_refl _⟩
    slot := by rw [← spAdd hpre sp₂ (N := 200) (M := 2456) (by decide), b80002018_m_x2_200 g₃]
    tabs := fun e he ↦ ?_ }, ?_⟩⟩
  · simp only [List.mem_singleton] at he
    subst he
    refine ⟨by simp only [InSlot]; addr_omega [hb1, hb3], ⟨hv₃.vec, hpad, by rw [e24]; exact K₃.ok, by rw [e24]; exact K₃.val⟩, fun x hx ↦ ?_⟩
    simp only [tableDeep, hv₃.ptr, hcap, e24] at hx
    rcases hx with hx | hx
    · simp only [Within] at hx
      rcases hraw.2 with h0 | h0
      · omega
      · simp only [Within]; omega
    · have := K₃.deep x hx
      simp only [Within]; omega
  · rw [b80002018_keeps g₃ .x8 (by decide), hp₂.reg .x8, b80002004_x8 g₁]

/-- From `flushes_keccak()`'s end (`0x80001f00`) to the first `flushes_arith` call (`0x80002024`):
the KECCAK `Table` finished at `sp + 952`, the tables' buffer allocated. -/
theorem r7 (hFE : MultilinearContracts.FromElemSpec) (hMS : MemsetSpec 0x800126f4)
    (hK : Contracts.KeccakFSpec) (hMC : MemcpySpec 0x800126e4) (hAS : AllocSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s)
    (h : KM OI s u A k R Q B 1 LayoutMirror.flushesKeccakRust) (hpc : u.pc = 0x80001f00) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002024 ∧ ∃ Bb, M8 OI s t A k R Q B Bb (heapNext t)
      [(s.getReg .x2 - 1704, kTable)] ∧ t.getReg .x8 = 8) ∨ Dead Image.code t) := by
  obtain ⟨t₁, r₁, ⟨p₁, P, K₁, z₁⟩ | d⟩ := tail1 hFE hpre h hpc
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  obtain ⟨t₂, r₂, ⟨p₂, K₂, z₂, a₂, b₂, c₂⟩ | d⟩ := tail2 hMS hpre K₁ z₁ p₁
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inr d⟩
  obtain ⟨t₃, r₃, ⟨p₃, L₃, x8, x9, x18, x23⟩ | d⟩ := tail3 hK hMC hpre K₂ z₂ a₂ b₂ c₂ p₂
  swap
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
  obtain ⟨t₄, r₄, p₄, L₄, R₄⟩ := entry hpre L₃ x8 x9 x18 x23 p₃
  obtain ⟨t₅, r₅, p₅, L₅⟩ := lanes hpre 25 0 t₄ rfl L₄ R₄ p₄
  obtain ⟨t₆, r₆, H⟩ := exit7 hAS hpre L₅ p₅
  exact ⟨t₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), H⟩

end Rv64Verifier.Proofs.Walk
