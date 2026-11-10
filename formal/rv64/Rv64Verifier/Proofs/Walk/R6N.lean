import Rv64Verifier.Proofs.Walk.R6K

/-!
# `walk`: the cell loop of one side

One iteration from the loop's head (`0x80001d74`) to the latch (`0x80001d60`) is `cellStep`; the
latch increments the cell and its pointers, and leaves to `0x80001b90` after cell 12 (`cells`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- The layout functions the cell loop calls. -/
structure LoopSpecs : Prop where
  limb : Rv64Verifier.Layout.LimbSpec
  term : Rv64Verifier.Layout.TermSpec
  prod : Rv64Verifier.Layout.ProdSpec
  col : Rv64Verifier.Layout.ColSpec
  memory : Rv64Verifier.Layout.MemorySpec
  addScaled : Rv64Verifier.Layout.AddScaledSpec
  counted : Rv64Verifier.Layout.CountedSpec

/-- One cell: the loop's head to the latch. -/
theorem cell (hS : LoopSpecs)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F) (r : KR s u σ c) (hσ : σ < 2) (hc : c < 13)
    (hpc : u.pc = 0x80001d74) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d60 ∧
      KM OI s t A k R Q B σ (cellStep σ F c) ∧ KR s t σ c) ∨ Dead Image.code t) := by
  obtain ⟨t₁, r₁, ⟨p₁, K₁, R₁, D₁, h1, h2, V⟩ | d⟩ := values hS.limb hS.term hpre h r hσ hc hpc
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  have deep : ∀ x, flushesDeep t₁ (s.getReg .x2 - 1488) x → x.toNat < heapNext u := fun x hx ↦
    (h.fl.ok.deep_below (by rw [← D₁]; exact hx)).2
  obtain ⟨t₂, r₂, p₂, W⟩ := toVA hpre K₁ R₁ p₁ hσ deep V
  by_cases hm : σ = 0 ∨ c = 0
  · obtain ⟨t, r, ht⟩ := memPath hS.prod hS.memory hpre W hσ hc hm p₂
    exact ⟨t, r₁.trans (r₂.trans r), ht⟩
  · have hs1 : σ = 1 := by omega
    have hc1 : 1 ≤ c := by omega
    subst hs1
    simp only [Nat.one_ne_zero, ↓reduceIte] at p₂
    obtain ⟨t₃, r₃, ⟨p₃, h4, h5, h6, J₁⟩ | d⟩ := toI1 hS.prod hS.col hpre W h.m.bufQ.2.2.2 hc hc1 p₂
    swap
    · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
    obtain ⟨t₄, r₄, ⟨p₄, h7, h8, J₂⟩ | d⟩ := toI2 hS.prod hS.addScaled hpre J₁ hc p₃
    swap
    · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
    obtain ⟨t, r, ht⟩ := ifTail hS.addScaled hS.term hS.counted hpre J₂ hc hc1 p₄
    exact ⟨t, r₁.trans (r₂.trans (r₃.trans (r₄.trans r))), ht⟩

/-- At `0x80001b90`, a side done: the registers the side start reads or keeps. -/
structure KX (s u : MachineState) : Prop where
  x8 : u.getReg .x8 = s.getReg .x2 - 200
  x18 : u.getReg .x18 = 13
  x20 : u.getReg .x20 = s.getReg .x2 - 176
  x25 : u.getReg .x25 = s.getReg .x2 - 272
  x26 : u.getReg .x26 = s.getReg .x2 - 512

set_option maxRecDepth 8192 in
/-- The latch: the next cell's head, or after cell 12 the side's end. -/
theorem latch {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F) (r : KR s u σ c) (hc : c < 13)
    (hpc : u.pc = 0x80001d60) :
    ∃ t, Reaches Image.code u t ∧ KM OI s t A k R Q B σ F ∧
      ((c + 1 < 13 ∧ t.pc = 0x80001d74 ∧ KR s t σ (c + 1)) ∨
        (c + 1 = 13 ∧ t.pc = 0x80001b90 ∧ KX s t)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨t, rt, g⟩ := Sym.BlockSpec.reaches b80001d60_spec hpc (by rv_eval [])
  have kt := b80001d60_keeps g
  have K := KM.scr hpre h (Rv64Verifier.Layout.DFrame.of_same (b80001d60_mem_same g) (fun _ ↦ False))
    (fun _ h ↦ h.elim) (kt .x2 (by decide))
  have x23 : u.getReg .x23 + 1 = BitVec.ofNat 64 (c + 1) := by
    rw [r.x23]; apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Word).toNat = 1 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]; omega
  refine ⟨t, rt, K.1, ?_⟩
  by_cases h13 : c + 1 = 13
  · refine Or.inr ⟨h13, b80001d60_pc_taken g (by rw [x23, r.x18, h13]; rfl), ?_⟩
    exact ⟨by rw [kt .x8 (by decide)]; exact r.x8, by rw [kt .x18 (by decide)]; exact r.x18,
      by rw [kt .x20 (by decide)]; exact r.x20, by rw [kt .x25 (by decide)]; exact r.x25,
      by rw [kt .x26 (by decide)]; exact r.x26⟩
  · refine Or.inl ⟨by omega, b80001d60_pc_not_taken g (by
      rw [x23, r.x18]; intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat] at this; have h13' : (13 : Word).toNat = 13 := rfl; omega), ?_⟩
    exact {
      x8 := by rw [kt .x8 (by decide)]; exact r.x8
      x9 := by rw [b80001d60_x9 g, r.x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
      x18 := by rw [kt .x18 (by decide)]; exact r.x18
      x19 := by rw [b80001d60_x19 g, r.x19]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
      x20 := by rw [kt .x20 (by decide)]; exact r.x20
      x21 := by rw [kt .x21 (by decide)]; exact r.x21
      x22 := by
        rw [b80001d60_x22 g, r.x22]; apply BitVec.eq_of_toNat_eq
        have h8 : (8 : Word).toNat = 8 := rfl
        have ha : (0xa00001b8 : Word).toNat = 0xa00001b8 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8, ha]; omega
      x23 := by rw [b80001d60_x23 g, x23]
      x25 := by rw [kt .x25 (by decide)]; exact r.x25
      x26 := by rw [kt .x26 (by decide)]; exact r.x26
      x27 := by rw [kt .x27 (by decide)]; exact r.x27 }

/-- The cells from `c` on: the loop's head at cell `c` to the side's end. -/
theorem cells (hS : LoopSpecs)
    {OI : MachineState → Word → List (List Opening) → Prop} {s : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} (hpre : WalkPre s) (hσ : σ < 2) :
    ∀ n c (F : LayoutMirror.FlushesRust) (u : MachineState), c + n + 1 = 13 →
      KM OI s u A k R Q B σ F → KR s u σ c → u.pc = 0x80001d74 →
      ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001b90 ∧
        KM OI s t A k R Q B σ ((List.range' c (n + 1)).foldl (cellStep σ) F) ∧ KX s t) ∨
        Dead Image.code t) := by
  intro n
  induction n with
  | zero =>
    intro c F u hn h r hpc
    obtain ⟨t₁, r₁, ⟨p₁, K₁, R₁⟩ | d⟩ := cell hS hpre h r hσ (by omega) hpc
    swap
    · exact ⟨t₁, r₁, Or.inr d⟩
    obtain ⟨t, rt, K, ⟨hlt, -⟩ | ⟨-, pt, X⟩⟩ := latch hpre K₁ R₁ (by omega) p₁
    · omega
    · exact ⟨t, r₁.trans rt, Or.inl ⟨pt, by simpa only [List.range'_succ, List.range'_zero,
        List.foldl_cons, List.foldl_nil] using K, X⟩⟩
  | succ m ih =>
    intro c F u hn h r hpc
    obtain ⟨t₁, r₁, ⟨p₁, K₁, R₁⟩ | d⟩ := cell hS hpre h r hσ (by omega) hpc
    swap
    · exact ⟨t₁, r₁, Or.inr d⟩
    obtain ⟨t₂, r₂, K₂, ⟨-, p₂, R₂⟩ | ⟨h13, -⟩⟩ := latch hpre K₁ R₁ (by omega) p₁
    · obtain ⟨t, rt, ht⟩ := ih (c + 1) (cellStep σ F c) t₂ (by omega) K₂ R₂ p₂
      refine ⟨t, r₁.trans (r₂.trans rt), ?_⟩
      rw [List.range'_succ, List.foldl_cons]
      exact ht
    · omega

end Rv64Verifier.Proofs.Walk
