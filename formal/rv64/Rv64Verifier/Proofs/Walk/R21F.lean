import Rv64Verifier.Proofs.Walk.R21E
import Rv64Verifier.Proofs.Walk.Spec
import Rv64Verifier.Proofs.Walk.LayoutWithin

/-!
# `walk` from R21 to the return, and the tail

`r21`: from `AtR21`, `ring_switch`, `vec![ringswitch]`, `extend_desugared`,
`verify_stacked_opening`, then `finish` and the return (`r22`) or the `Err` block (`err41cc`).
`tail_of`: `walk_spec_of`'s `hTail` from R17 and R18 (proved), R19 and R20 (`hR19`: from R18's exit
to `AtR21`), and `r21`, for a front that also gives `PlApart` (`walk_spec_of'`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.PcsContracts

/-- R21 and R22: from `AtR21` to the return, or a dead end. -/
theorem r21 {OA : MachineState → Word → TState → Prop} (hRS : RingSwitchSpec) (hA : AllocSpec)
    (hE : ExtendSpecE) (hV : VsoSpec OA) (hDN : DropNopSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} (hB : OpenBridge OI OA)
    {s u₀ w t u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word}
    {cl : List ColumnClaim} {pt sl : List E} {ks ke : ℕ} (hpre : WalkPre s) (hO : OpenPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (hPl : PlApart s u₀) (hWi : LayoutWithin layout)
    (A : AtR21 OI s u₀ w t u layout rows lir bus evs P C L cl pt sl ks ke) :
    ∃ v, Reaches Image.code u v ∧ (Done OI s v ∨ Dead Image.code v) := by
  obtain ⟨v₁, hr₁, R | hd⟩ := r21ring hRS hpre A
  swap
  · exact ⟨v₁, hr₁, Or.inr hd⟩
  obtain ⟨v₂, hr₂, X | hd⟩ := r21alloc hA hpre h R
  swap
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨v₃, hr₃, V | hd⟩ := r21ext hE hpre h hPl hWi X
  swap
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  obtain ⟨v₄, hr₄, G | G | hd⟩ := r21vso hV hB hpre hO h V
  · obtain ⟨v, hr, hv⟩ := r22 hDN hDL hpre h G
    exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), hv⟩
  · obtain ⟨v, hr, hv⟩ := err41cc hDN hDL hpre h G
    exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), hv⟩
  · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩

/-- R19 and R20, from R18's exit to `AtR21`, the return or a dead end: what the other half of the
tail proves. -/
def R19R20 (OI : MachineState → Word → List (List Opening) → Prop) : Prop :=
  ∀ s u₀ w t u layout rows lir bus evs P C L, WalkPre s → AtR17 OI s u₀ layout rows lir bus →
    ExitR18 OI s u₀ w t u layout rows lir bus evs P C L →
    ∃ v, Reaches Image.code u v ∧
      ((∃ w' t' evs' P' C' L' cl pt sl ks ke,
        AtR21 OI s u₀ w' t' v layout rows lir bus evs' P' C' L' cl pt sl ks ke) ∨
        Done OI s v ∨ Dead Image.code v)

/-- **`walk_spec_of`'s `hTail`**, for an `AtR17` whose placements miss the bus claims' buffer and
whose layout's placements fit the stack. -/
theorem tail_of {OA : MachineState → Word → TState → Prop} (hD : DuplexSpec)
    (hP : MultilinearContracts.PowersSpec) (hDt : MultilinearContracts.DotSpec)
    (hTS : TableSumcheckSpec) (hDN : DropNopSpec) (hDL : DropLayoutSpec) (hCl : CloneSpecE)
    (hG : GrowSpec) (hRS : RingSwitchSpec) (hA : AllocSpec) (hE : ExtendSpecE) (hV : VsoSpec OA)
    {OI : MachineState → Word → List (List Opening) → Prop} (hB : OpenBridge OI OA)
    (hR19 : R19R20 OI) :
    ∀ s u (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
      (bus : BusResultRust), WalkPre s → OpenPre s → AtR17 OI s u layout rows lir bus →
      PlApart s u → ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  intro s u₀ layout rows lir bus hpre hO h hPl
  have hWi : LayoutWithin layout := by
    obtain ⟨-, len, lm, hb⟩ := h.build
    exact LayoutMirror.buildLayoutRust_within hb
  obtain ⟨u, hr, ⟨w, evs, H⟩ | hd | hd⟩ := r17 hD hP hDt hTS hDN hDL hpre h
  · obtain ⟨v, hr', ⟨P, C, L, X⟩ | hd⟩ := r18 hCl hG hpre h H
    swap
    · exact ⟨v, hr.trans hr', Or.inr hd⟩
    obtain ⟨v', hr'', ⟨w', t', evs', P', C', L', cl, pt, sl, ks, ke, A⟩ | hd | hd⟩ :=
      hR19 s u₀ w u v layout rows lir bus evs P C L hpre h X
    · obtain ⟨t, hrt, ht⟩ := r21 hRS hA hE hV hDN hDL hB hpre hO h hPl hWi A
      exact ⟨t, hr.trans (hr'.trans (hr''.trans hrt)), ht⟩
    · exact ⟨v', hr.trans (hr'.trans hr''), Or.inl hd⟩
    · exact ⟨v', hr.trans (hr'.trans hr''), Or.inr hd⟩
  · exact ⟨u, hr, Or.inl hd⟩
  · exact ⟨u, hr, Or.inr hd⟩

/-- `walk_spec_of`, the front also giving `PlApart`, the openings in place (`OpenPre`). -/
theorem walk_spec_of' {OI : MachineState → Word → List (List Opening) → Prop}
    (hFront : ∀ s, s.pc = 0x80000ef8 → WalkPre s → ∃ u, Reaches Image.code s u ∧
      ((∃ layout rows lir bus, AtR17 OI s u layout rows lir bus ∧ PlApart s u) ∨ Done OI s u ∨
        Dead Image.code u))
    (hTail : ∀ s u (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
      (bus : BusResultRust), WalkPre s → OpenPre s → AtR17 OI s u layout rows lir bus →
      PlApart s u → ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t)) :
    WalkSpecO OI := by
  intro s hpc ⟨hpre, hO⟩
  obtain ⟨u, hr, ⟨layout, rows, lir, bus, h, hPl⟩ | hd | hd⟩ := hFront s hpc hpre
  · obtain ⟨t, hr', ht | ht⟩ := hTail s u layout rows lir bus hpre hO h hPl
    · exact ⟨t, hr.trans hr', Or.inl ht⟩
    · exact ⟨t, hr.trans hr', Or.inr ht⟩
  · exact ⟨u, hr, Or.inl hd⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Walk
