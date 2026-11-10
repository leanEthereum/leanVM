import Rv64Verifier.Proofs.Walk.R22A

/-!
# `walk` past `verify_stacked_opening`: the `Err` block at `0x800041cc`

`err41cc`: the block writes `errNiche` to the result's first word and the error at its `a0`
(`8` or `16`), drops the claims' `Vec` (a no-op), and leaves by `errTailN₁`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
theorem err41cc (hDN : DropNopSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (E : Err41cc s u₀ u) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := E.rest.inv.sp
  have hR := hpre.out
  have hRb := hR.1
  have hRa := hR.2
  simp only [Mapped] at hRb
  have e10 : (s.getReg .x10 + u.getReg .x10).toNat = (s.getReg .x10).toNat + (u.getReg .x10).toNat ∧
      (u.getReg .x10).toNat ≤ 16 ∧ 8 ≤ (u.getReg .x10).toNat ∧ (u.getReg .x10).toNat % 8 = 0 := by
    rcases E.x10 with e | e <;> rw [e] <;> refine ⟨?_, by decide, by decide, by decide⟩ <;>
      addr_omega [hRb]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800041cc_spec E.pc (by
    rv_eval [sp, E.x23]
    refine ⟨Region.valid hR (by omega) (by omega) (by omega),
      Region.valid hR (by omega) (by omega) (by omega), by valid_access hval [hb1], ?_⟩
    intro he; have := congrArg BitVec.toNat he; omega)
  have fr : DFrame u u₁ (Within · (s.getReg .x10) 24) := h₁.dframe (by
    rv_eval [E.x23]
    simp only [Within]
    refine ⟨⟨le_refl _, by omega⟩, by omega, by omega⟩)
  have R₁ := E.rest.result hpre (n := 24) (by omega) fr (b800041cc_keeps h₁ .x2 (by decide))
  have he₁ : u₁.getMem (s.getReg .x10) = errNiche := by
    rw [← E.x23, b800041cc_m_x23_0 h₁]; rfl
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, m₂⟩ | hd⟩ := hDN.call hr₁ (b800041cc_pc h₁) trivial
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have R₂ := R₁.same m₂ (hp₂ .x2 (by decide))
  obtain ⟨t, hr₃, ht⟩ := errTailN₁ hDN hDL hpre h R₂
    (by rw [hpc₂, returnAddress_eq, b800041cc_x1 h₁]; decide) (by rw [m₂]; exact he₁)
  exact ⟨t, hr₂.trans hr₃, ht⟩

end Rv64Verifier.Proofs.Walk
