import Rv64Verifier.Proofs.Walk.R18J

/-!
# `walk` R18, the table claims: the loop

`outerStep`: one table, from the outer head to the next table's head or the exit. `r18`: from
`AtR18` to `ExitR18`, every table's claims appended, or the run dies.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

section Loop
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k : Nat} {P C L : Word}

/-- Table `k`'s values, from `0x8000387c` with room for them. -/
theorem tabRun (hCl : CloneSpecE) (hpre : WalkPre s)
    (T : TabR18 OI s u₀ w t u layout rows lir bus evs k P C L) (hpc : u.pc = 0x8000387c)
    (hroom : L.toNat + (evs.getD k ([], [])).2.length ≤ C.toNat)
    (hn : 0 < (evs.getD k ([], [])).2.length) :
    ∃ v, Reaches Image.code u v ∧
      ((∃ P C L, ExitR18 OI s u₀ w t v layout rows lir bus evs P C L) ∨
      (k + 1 < 6 ∧ ∃ P C L, LoopR18 OI s u₀ w t v layout rows lir bus evs (k + 1) P C L) ∨
      Dead Image.code v) := by
  obtain ⟨v₁, hr₁, I⟩ := tab387c hpre T hpc hroom hn
  obtain ⟨v₂, hr₂, hE | hd⟩ := innerLoop hCl hpre _ 0 v₁ rfl I
  · obtain ⟨v₃, hr₃, hX | ⟨hk, hL⟩⟩ := endStep hpre hE
    · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨_, _, _, hX⟩⟩
    · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨hk, _, _, _, hL⟩)⟩
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩

/-- One table. -/
theorem outerStep (hCl : CloneSpecE) (hG : GrowSpec) (hpre : WalkPre s)
    (H : LoopR18 OI s u₀ w t u layout rows lir bus evs k P C L) (hk6 : k < 6) :
    ∃ v, Reaches Image.code u v ∧
      ((∃ P C L, ExitR18 OI s u₀ w t v layout rows lir bus evs P C L) ∨
      (k + 1 < 6 ∧ ∃ P C L, LoopR18 OI s u₀ w t v layout rows lir bus evs (k + 1) P C L) ∨
      Dead Image.code v) := by
  obtain ⟨v₁, hr₁, hX | ⟨T, hpc, hc⟩ | ⟨T, hpc, hc⟩⟩ := outerHead hpre H hk6
  · exact ⟨v₁, hr₁, Or.inl ⟨_, _, _, hX⟩⟩
  · obtain ⟨v₂, hr₂, ⟨P', C', T', hpc', hroom⟩ | hd⟩ := tabGrow hG hpre T hpc hc
    · obtain ⟨v₃, hr₃, h₃⟩ := tabRun hCl hpre T' hpc' hroom (by omega)
      exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), h₃⟩
    · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  · have hLC := H.len
    obtain ⟨v₂, hr₂, ⟨T', hpc', hroom, hn⟩ | hE⟩ := tab3878 hpre T hpc hc
    · obtain ⟨v₃, hr₃, h₃⟩ := tabRun hCl hpre T' hpc' hroom hn
      exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), h₃⟩
    · obtain ⟨v₃, hr₃, hX | ⟨hk, hL⟩⟩ := endStep hpre hE
      · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨_, _, _, hX⟩⟩
      · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨hk, _, _, _, hL⟩)⟩

/-- The outer loop from table `k` on. -/
theorem outerLoop (hCl : CloneSpecE) (hG : GrowSpec) (hpre : WalkPre s) :
    ∀ m k P C L u, 6 - k = m → k < 6 →
      LoopR18 OI s u₀ w t u layout rows lir bus evs k P C L →
      ∃ v, Reaches Image.code u v ∧
        ((∃ P C L, ExitR18 OI s u₀ w t v layout rows lir bus evs P C L) ∨ Dead Image.code v) := by
  intro m
  induction m with
  | zero => intro k P C L u hm hk; omega
  | succ m ih =>
    intro k P C L u hm hk H
    obtain ⟨v, hr, hX | ⟨hk', P', C', L', H'⟩ | hd⟩ := outerStep hCl hG hpre H hk
    · exact ⟨v, hr, Or.inl hX⟩
    · obtain ⟨v', hr', h'⟩ := ih (k + 1) P' C' L' v (by omega) hk' H'
      exact ⟨v', hr.trans hr', h'⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-- R18: from `AtR18` to the exit, every table's claims appended, or the run dies. -/
theorem r18 (hCl : CloneSpecE) (hG : GrowSpec) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (H : AtR18 OI s u₀ w t layout rows lir bus evs) :
    ∃ v, Reaches Image.code t v ∧
      ((∃ P C L, ExitR18 OI s u₀ w t v layout rows lir bus evs P C L) ∨ Dead Image.code v) := by
  obtain ⟨u, hr, H₀⟩ := r18Entry hpre h H
  obtain ⟨v, hr', h'⟩ := outerLoop hCl hG hpre _ 0 _ _ _ u rfl (by decide) H₀
  exact ⟨v, hr.trans hr', h'⟩

end Loop

end Rv64Verifier.Proofs.Walk
