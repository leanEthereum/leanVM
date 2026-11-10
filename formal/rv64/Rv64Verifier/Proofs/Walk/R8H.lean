import Rv64Verifier.Proofs.Walk.R8G

/-!
# `walk`: `tables()`, the SET `Table` (R8)

From SET's `state_step` call (`mulStage`'s end) to DEREF's first `col` (`setStage`): `setHead`,
`setCols`, `setTerm`, `setBc`, `setTail`; the `Flushes` built is `flushes_set()`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- The SET `Table`. -/
def setT : LayoutMirror.TableRust := ⟨2, List.replicate 8 0, LayoutMirror.flushesSetRust⟩

theorem tablesRust_two : LayoutMirror.tablesRust[2]? = some setT := rfl

theorem setFlushes_eq :
    (((({} : LayoutMirror.FlushesRust).stateStep 0 1).bytecode 0 7 2 setOps).memoryCols
      (LayoutMirror.prodRust 1 2 0) 6 [3, 4, 5]) = LayoutMirror.flushesSetRust := rfl

/-- The registers DEREF starts from. -/
structure RD (s u : MachineState) : Prop where
  r8 : R8 u
  x18 : u.getReg .x18 = 7
  x23 : u.getReg .x23 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = 8
  x26 : u.getReg .x26 = 5
  x27 : u.getReg .x27 = 6

set_option maxRecDepth 8192 in
/-- **SET**: from its `state_step` call to DEREF's first `col(8, 0)` into `sp + 2432`; the SET
`Table` at `sp + 1168` joins the finished ones. -/
theorem setStage (hSS : Rv64Verifier.Layout.StateStepSpec) (hAS : AllocSpec)
    (hC : Rv64Verifier.Layout.ColSpec) (hT : Rv64Verifier.Layout.TermSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hK : Rv64Verifier.Layout.MemoryColsSpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (r : R8 u) (he : EmptyAt u (s.getReg .x2 - 928))
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x1 : u.getReg .x1 = 0x80002100)
    (hpc : u.pc = 0x80004a90) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧
      M8 OI s t A k R Q B Bb (heapNext t) (L4 s setT) ∧ RD s t ∧
      t.getReg .x10 = s.getReg .x2 - 224 ∧ t.getReg .x11 = 8 ∧ t.getReg .x12 = 0 ∧
      t.getReg .x1 = 0x80002308) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hW := h.bb.2.2.2
  obtain ⟨t₁, r₁, ⟨p₁, P, M₁, F₁, O₁, hP₁, R₁, a10, a25, a11, a12, a27, a1⟩ | d⟩ :=
    setHead hSS hAS hpre h (l3_apart hpre (by addr_omega [hb1])) r he x10 x1 hpc
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  obtain ⟨t₂, r₂, ⟨p₂, M₂, F₂, S₂, n₂, m₂, R₂, b10, b11, b12, b23, b26, b1, D₂⟩ | d⟩ :=
    setCols hC hpre M₁ F₁ O₁ hW hP₁ ⟨R₁.x8, R₁.x24, a25, a27⟩ a10 a11 a12 a1 p₁
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inr d⟩
  obtain ⟨t₃, r₃, ⟨p₃, M₃, F₃, V₃, VV₃, vp₃, vl₃, n₃, D₃, R₃, c10, c11, c12, c13, c18, c23, c26, c1⟩ | d⟩ :=
    setTerm hT hpre M₂ F₂ S₂ O₁.al (by omega) n₂ D₂ m₂ R₂ b10 b11 b12 b23 b26 b1 p₂
  swap
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
  have hl₃ : heapNext u ≤ heapNext t₃ := by omega
  obtain ⟨t₄, r₄, ⟨p₄, hp₄, M₄, F₄, mo₄⟩ | d⟩ :=
    setBc hBC hpre M₃ F₃ hW hl₃ V₃ VV₃ vp₃ vl₃ n₃ c10 c11 c12 c13 p₃
  swap
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
  have R₄ := R₃.pres hp₄
  obtain ⟨t₅, r₅, ⟨p₅, M₅, R8₅, e25, e10, e11, e12, e1, ek⟩ | d⟩ :=
    setTail hP hK hFE hpre M₄ F₄ hW (le_trans hl₃ mo₄) ⟨R₄.x8, R₄.x24⟩
      (by rw [hp₄.reg .x23]; exact c23) (by rw [p₄, returnAddress_eq, c1]; decide)
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr d⟩
  rw [setFlushes_eq] at M₅
  refine ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl ⟨p₅, M₅,
    ⟨R8₅, ?_, ?_, e25, ?_, ?_⟩, e10, e11, e12, e1⟩⟩
  · rw [ek .x18 (by decide), hp₄.reg .x18]; exact c18
  · rw [ek .x23 (by decide), hp₄.reg .x23]; exact c23
  · rw [ek .x26 (by decide), hp₄.reg .x26]; exact c26
  · rw [ek .x27 (by decide)]; exact R₄.x27

end Rv64Verifier.Proofs.Walk
