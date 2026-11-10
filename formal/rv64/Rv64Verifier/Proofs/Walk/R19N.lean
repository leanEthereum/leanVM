import Rv64Verifier.Proofs.Walk.R19M
import Rv64Verifier.Proofs.Walk.R20I

/-!
# `walk` from `AtR17` to `ring_switch`'s call

`toR21`: R17 (`r17`), R18 (`r18`), R19 (`r19`), R20 (`r20`) in a row: from `AtR17` the code
reaches `AtR21`, returns (`Done`) or dies.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

theorem toR21 (hD : DuplexSpec) (hP : MultilinearContracts.PowersSpec)
    (hDt : MultilinearContracts.DotSpec) (hTS : TableSumcheckSpec) (hDN : DropNopSpec)
    (hDL : DropLayoutSpec) (hCl : CloneSpecE) (hGr : GrowSpec)
    (hFE : MultilinearContracts.FromElemSpec) (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10)
    (hS : MultilinearContracts.ScalerSpec) (hM : Contracts.MulSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hVK : VerifyKeccakSpecE)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ : MachineState}
    {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
    {bus : BusResultRust} (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus) :
    ∃ v, Reaches Image.code u₀ v ∧ ((∃ w t evs P C L cl pt sl ks ke,
      AtR21 OI s u₀ w t v layout rows lir bus evs P C L cl pt sl ks ke) ∨
      Done OI s v ∨ Dead Image.code v) := by
  obtain ⟨t, hr₁, ⟨w, evs, H⟩ | hd | hd⟩ := r17 hD hP hDt hTS hDN hDL hpre h
  rotate_left
  · exact ⟨t, hr₁, Or.inr (Or.inl hd)⟩
  · exact ⟨t, hr₁, Or.inr (Or.inr hd)⟩
  obtain ⟨u, hr₂, ⟨P, C, L, Ex⟩ | hd⟩ := r18 hCl hGr hpre h H
  swap
  · exact ⟨u, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  obtain ⟨v, hr₃, ⟨P', C', L', pub, A⟩ | hd⟩ := r19 hD hFE hCl hA hR hS hM hG hpre h Ex
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr hd)⟩
  obtain ⟨x, hr₄, ⟨P₂, C₂, L₂, cl, pt, sl, ks, ke, B⟩ | hd | hd⟩ := r20 hVK hG hDN hDL hpre h A
  · exact ⟨x, hr₁.trans (hr₂.trans (hr₃.trans hr₄)),
      Or.inl ⟨w, t, evs, P₂, C₂, L₂, cl, pt, sl, ks, ke, B⟩⟩
  · exact ⟨x, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl hd)⟩
  · exact ⟨x, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr hd)⟩

end Rv64Verifier.Proofs.Walk
