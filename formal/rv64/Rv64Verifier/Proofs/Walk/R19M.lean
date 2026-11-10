import Rv64Verifier.Proofs.Walk.R19L

/-!
# `walk` R19, the public input's claims: the loop

`r19step`: one claim, from the head to the next head or `AtR20`. `r19`: from `ExitR18` to
`AtR20`, the three claims pushed, or a dead end.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

section Loop
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {i : Nat} {c : E}
  {pt : Word}

/-- One claim: from the head to the next head or `AtR20`, or a dead end. -/
theorem r19step (hCl : CloneSpecE) (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10)
    (hS : MultilinearContracts.ScalerSpec) (hM : Contracts.MulSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt) :
    ∃ v, Reaches Image.code u v ∧ ((∃ P' C', i + 1 < 3 ∧
      HeadR19 OI s u₀ w t v layout rows lir bus evs P' C' L (i + 1) c pt) ∨
      (∃ P' C', AtR20 OI s u₀ w t v layout rows lir bus evs P' C' (L + 3)
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c)) ∨ Dead Image.code v) := by
  obtain ⟨x, hr₁, ⟨Q, A⟩ | hd⟩ := r19pA hCl hA hpre Hd
  swap
  · exact ⟨x, hr₁, Or.inr (Or.inr hd)⟩
  obtain ⟨z, hr₂, B₁ | hd⟩ := r19pB1 hR hS hpre Hd A
  swap
  · exact ⟨z, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  obtain ⟨y, hr₃, B | hd⟩ := r19pB2 hM hpre Hd B₁
  swap
  · exact ⟨y, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr hd)⟩
  obtain ⟨y₃, hr₄, ⟨P₁, C₁, cp, Ac⟩ | hd⟩ := r19pC1 hG hpre Hd B
  swap
  · exact ⟨y₃, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr hd)⟩
  obtain ⟨v, hr₅, ⟨hlt, H'⟩ | ⟨-, H'⟩⟩ := r19pC2 hpre h Hd Ac
  · exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl ⟨P₁, C₁, hlt, H'⟩⟩
  · exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inl ⟨P₁, C₁, H'⟩)⟩

/-- From the head with `n` claims to go, to `AtR20` or a dead end. -/
theorem r19loop (hCl : CloneSpecE) (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10)
    (hS : MultilinearContracts.ScalerSpec) (hM : Contracts.MulSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) :
    ∀ (n i : Nat) (u : MachineState) (P C : Word), i + n = 3 →
      HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt →
      ∃ v, Reaches Image.code u v ∧ ((∃ P' C', AtR20 OI s u₀ w t v layout rows lir bus evs P' C'
        (L + 3) (pubClaims layout (bytesAt s (s.getReg .x12) 32) c)) ∨ Dead Image.code v)
  | 0, i, u, P, C, hn, Hd => absurd Hd.hi (by omega)
  | n + 1, i, u, P, C, hn, Hd => by
    obtain ⟨v, hr, ⟨P', C', -, H'⟩ | ⟨P', C', H'⟩ | hd⟩ := r19step hCl hA hR hS hM hG hpre h Hd
    · obtain ⟨v', hr', hv'⟩ := r19loop hCl hA hR hS hM hG hpre h n (i + 1) v P' C' (by omega) H'
      exact ⟨v', hr.trans hr', hv'⟩
    · exact ⟨v, hr, Or.inl ⟨P', C', H'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-- R19: from `ExitR18` to `AtR20`, the public input's three claims pushed, or a dead end. -/
theorem r19 (hD : DuplexSpec) (hFE : MultilinearContracts.FromElemSpec) (hCl : CloneSpecE)
    (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10) (hS : MultilinearContracts.ScalerSpec)
    (hM : Contracts.MulSpec) (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus)
    (Ex : ExitR18 OI s u₀ w t u layout rows lir bus evs P C L) :
    ∃ v, Reaches Image.code u v ∧ ((∃ P' C' L' pub, AtR20 OI s u₀ w t v layout rows lir bus evs
      P' C' L' pub) ∨ Dead Image.code v) := by
  obtain ⟨v, hr, ⟨c, pt, Hd⟩ | hd⟩ := r19a hD hFE hpre h Ex
  swap
  · exact ⟨v, hr, Or.inr hd⟩
  obtain ⟨v', hr', ⟨P', C', H'⟩ | hd⟩ := r19loop hCl hA hR hS hM hG hpre h 3 0 v P C rfl Hd
  · exact ⟨v', hr.trans hr', Or.inl ⟨P', C', L + 3, _, H'⟩⟩
  · exact ⟨v', hr.trans hr', Or.inr hd⟩

end Loop

end Rv64Verifier.Proofs.Walk
