import Rv64Verifier.Proofs.Walk.Jp6

/-!
# `walk`: `tables()`, JUMP (R8)

From `AtJump` to `AtR9`: `jumpNpc`, `jumpNfp`, `jumpHead`, `jumpTerms`, `jumpBc`, `jumpCols`,
`jumpTail`; the `Flushes` built is `flushes_jump()`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

set_option maxRecDepth 8192 in
/-- **JUMP**: from its first `prod` call to the first `memcpy` of the tables into their buffer. -/
theorem jumpStage (hP : Rv64Verifier.Layout.ProdSpec) (hC : Rv64Verifier.Layout.ColSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec) (hSD : Rv64Verifier.Layout.StateDerivedSpec)
    (hAS : AllocSpec) (hT : Rv64Verifier.Layout.TermSpec) (hBC : Rv64Verifier.Layout.BytecodeSpec)
    (hK : Rv64Verifier.Layout.MemoryColsSpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtJump OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ (AtR9 OI s t A k R Q B Bb ∨ Dead Image.code t) := by
  obtain ⟨t₁, r₁, ⟨p₁, M₁, J₁, N₁, R₁, x24₁⟩ | d⟩ := jumpNpc hP hC hA hpre h
  swap
  · exact ⟨_, r₁, Or.inr d⟩
  obtain ⟨t₂, r₂, ⟨p₂, M₂, F₂, R₂⟩ | d⟩ := jumpNfp hP hC hA hSD hpre M₁ J₁ N₁ R₁ x24₁ p₁
  swap
  · exact ⟨_, r₁.trans r₂, Or.inr d⟩
  obtain ⟨t₃, r₃, ⟨p₃, P, D₃, pal, hWP, pnx, pdeep, m0, R₃, x20, x25, x24, x10, x11, x12, x1⟩ | d⟩ :=
    jumpHead hAS hC hpre M₂ F₂ R₂ p₂
  swap
  · exact ⟨_, r₁.trans (r₂.trans r₃), Or.inr d⟩
  obtain ⟨t₄, r₄, ⟨p₄, M₄, F₄, V, VV, vp, vl, pn₄, -, R₄, y20, y8, y24, y10, y11, y12, y13, y1⟩ | d⟩ :=
    jumpTerms hT hpre D₃ pal hWP pnx pdeep m0 R₃ x20 x25 x24 x10 x11 x12 x1 p₃
  swap
  · exact ⟨_, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
  obtain ⟨t₅, r₅, ⟨p₅, hp₅, M₅, F₅, -⟩ | d⟩ := jumpBc hBC hpre M₄ F₄ V VV vp vl pn₄ y10 y11 y12 y13 p₄
  swap
  · exact ⟨_, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr d⟩
  obtain ⟨t₆, r₆, ⟨p₆, M₆, F₆, R₆, z20, z8, z9, z24⟩ | d⟩ := jumpCols hP hK hpre M₅ F₅ (R₄.pres hp₅)
    (by rw [hp₅.reg .x20]; exact y20) (by rw [hp₅.reg .x8]; exact y8) (by rw [hp₅.reg .x24]; exact y24)
    (by rw [p₅, returnAddress_eq, y1]; decide)
  swap
  · exact ⟨_, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inr d⟩
  obtain ⟨t₇, r₇, ⟨p₇, M₇, a10, a11, a12, a1, a8, a9, a18, a20, R₇⟩ | d⟩ :=
    jumpTail hFE hpre M₆ F₆ R₆ z20 z8 z9 z24 p₆
  swap
  · exact ⟨_, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))), Or.inr d⟩
  rw [jumpFlushes_eq] at M₇
  exact ⟨t₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))),
    Or.inl ⟨p₇, M₇, a10, a11, a12, a1, a8, a9, a18, R₇.x19, a20, R₇.x21, R₇.x22, R₇.x27⟩⟩

end Rv64Verifier.Proofs.Walk
