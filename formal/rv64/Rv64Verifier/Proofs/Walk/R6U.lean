import Rv64Verifier.Proofs.Walk.R6T

/-!
# `walk`: `flushes_keccak`'s cell loop

From the first `keccak_cell_lanes` call (`AtR6a`) through both sides' thirteen cells to
`0x80001f00`, the `Flushes` at `sp + 1168` holding `flushes_keccak()`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

theorem cellStep0 : cellStep 0 = LayoutMirror.keccakCellRust 0 LayoutMirror.keccakInRust
    LayoutMirror.KeccakCol.oddIn (some LayoutMirror.KeccakCol.free) := by
  funext F c; rfl

theorem cellStep1 : cellStep 1 = LayoutMirror.keccakCellRust 1 LayoutMirror.keccakOutRust
    LayoutMirror.KeccakCol.oddOut none := by
  funext F c; rfl

theorem kfold_eq : (List.range' 0 (12 + 1)).foldl (cellStep 1)
    ((List.range' 0 (12 + 1)).foldl (cellStep 0) keccakHead) = LayoutMirror.flushesKeccakRust := by
  rw [cellStep0, cellStep1, show 12 + 1 = LayoutMirror.keccakCellsRust from rfl,
    ← List.range_eq_range', keccakHead_eq]
  unfold LayoutMirror.flushesKeccakRust
  simp only [List.foldl_cons, List.foldl_nil]

/-- `flushes_keccak`'s cell loop, both sides. -/
theorem keccakLoop (hS : LoopSpecs) (hCL : Rv64Verifier.Layout.CellLanesSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s)
    (h : AtR6a OI s u A k R Q B) (hpc : u.pc = 0x80004d10) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001f00 ∧
      KM OI s t A k R Q B 1 LayoutMirror.flushesKeccakRust) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨t₀, r₀, ⟨p₀, K₀, R₀⟩ | d⟩ := setup hCL hpre h hpc
  swap
  · exact ⟨t₀, r₀, Or.inr d⟩
  obtain ⟨t₁, r₁, ⟨p₁, K₁, X₁⟩ | d⟩ := cells hS hpre (by decide) 12 0 keccakHead t₀ rfl K₀ R₀ p₀
  swap
  · exact ⟨t₁, r₀.trans r₁, Or.inr d⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.m.inv.sp
  have a200 : t₁.getReg .x2 + 200 = s.getReg .x2 - 2456 := spAdd hpre sp₁ (by decide)
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001b90_spec p₁ (by
    rv_eval [sp₁]
    valid_access hpre.stack.valid [hb1])
  have m₂ := b80001b90_mem_same g₂
  have k₂ := b80001b90_keeps g₂
  have K₂ := KM.scr hpre K₁ (Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₂ .x2 (by decide))
  have p₂ := b80001b90_pc_not_taken g₂ (by rw [a200, K₁.side]; rfl)
  obtain ⟨t₃, r₃, p₃, K₃, R₃⟩ := sideStart hpre (K₂.1.toKMb hpre) (by decide) p₂
    (b80001b90_x10 g₂) (b80001b90_x15 g₂) (by rw [k₂ .x8 (by decide)]; exact X₁.x8)
    (by rw [k₂ .x18 (by decide)]; exact X₁.x18) (by rw [k₂ .x20 (by decide)]; exact X₁.x20)
    (by rw [k₂ .x25 (by decide)]; exact X₁.x25) (by rw [k₂ .x26 (by decide)]; exact X₁.x26)
  obtain ⟨t₄, r₄, ⟨p₄, K₄, X₄⟩ | d⟩ := cells hS hpre (by decide) 12 0 ((List.range' 0 (12 + 1)).foldl (cellStep 0) keccakHead) t₃ rfl K₃ R₃ p₃
  swap
  · exact ⟨t₄, r₀.trans (r₁.trans (r₂.trans (r₃.trans r₄))), Or.inr d⟩
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := K₄.m.inv.sp
  obtain ⟨u₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b80001b90_spec p₄ (by
    rv_eval [sp₄]
    valid_access hpre.stack.valid [hb1])
  have K₅ := KM.scr hpre K₄ (Rv64Verifier.Layout.DFrame.of_same (b80001b90_mem_same g₅) (fun _ ↦ False))
    (fun _ h ↦ h.elim) (b80001b90_keeps g₅ .x2 (by decide))
  have p₅ := b80001b90_pc_taken g₅ (by rw [spAdd hpre sp₄ (N := 200) (M := 2456) (by decide), K₄.side]; decide)
  rw [kfold_eq] at K₅
  exact ⟨u₅, r₀.trans (r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅)))), Or.inl ⟨p₅, K₅.1⟩⟩

end Rv64Verifier.Proofs.Walk
