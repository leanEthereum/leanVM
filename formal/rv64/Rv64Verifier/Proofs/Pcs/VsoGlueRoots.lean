import Rv64Verifier.Proofs.Pcs.VsoGlueRootsPush

/-!
# `verify_stacked_opening`'s final level: `subspace_roots`

The rounds' loop from `RH` to `RX` by induction on the rounds left (`rootsLoop`), and
**`roots_spec`**: from `0x8000bbb0` (`QA`) to `0x8000bdc0` (`QR`), the roots `subspaceRootsRust n`
in a buffer allocated since, or a dead end.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts

/-- **The rounds' loop**: from round `k` at `0x8000bd1c` to `0x8000bdb4`, or a dead end. -/
theorem rootsLoop (hS : KSquareSpec) (hBM : BaseMulSpec) (hMM : MemmoveSpec 0x800126ec)
    (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s v w : MachineState} {a L : Word} {n : ℕ}
    (hpre : VsoPre s) :
    ∀ c k t st, n - k = c → RH s v w t a n k st L →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ ∃ rs, RX s v w t' a n rs L) := by
  intro c
  induction c with
  | zero => intro k t st hc h; have := h.klt; omega
  | succ c ih =>
    intro k t st hc h
    obtain ⟨u, r₁, hu⟩ := rootsMove hS hBM hMM hpre h
    rcases hu with hd | hu
    · exact ⟨u, r₁, Or.inl hd⟩
    obtain ⟨p, r₂, hp⟩ := rootsRoom hG hpre hu
    rcases hp with hd | hp
    · exact ⟨p, r₁.trans r₂, Or.inl hd⟩
    obtain ⟨q, r₃, hq⟩ := rootsPush hpre hp
    rcases hq with ⟨-, hq⟩ | ⟨-, hq⟩
    · obtain ⟨t', r₄, h'⟩ := ih (k + 1) q _ (by omega) hq
      exact ⟨t', r₁.trans (r₂.trans (r₃.trans r₄)), h'⟩
    · exact ⟨q, r₁.trans (r₂.trans r₃), Or.inr ⟨_, hq⟩⟩

/-- **`subspace_roots(n)`**, inlined in `induced_weight`: `0x8000bbb0` to `0x8000bdc0`. -/
theorem roots_spec (hA : AllocSpec) (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    (hS : KSquareSpec) (hBM : BaseMulSpec) (hMM : MemmoveSpec 0x800126ec)
    (hG : GrowOneFreshSpec 0x8000d7bc 8 8) : RootsSpec := by
  intro s v w a n hpre h
  obtain ⟨t, r₁, ht⟩ := rootsSetup hA hT hpre h
  rcases ht with hd | ⟨R, L, ht⟩
  · exact ⟨t, r₁, Or.inl hd⟩
  by_cases hn : n = 0
  · subst hn
    obtain ⟨t', r₂, h'⟩ := rootsZero hRF hpre ht
    exact ⟨t', r₁.trans r₂, h'⟩
  obtain ⟨t₂, r₂, h₂⟩ := rootsFill hRF hpre ht hn
  rcases h₂ with hd | h₂
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨t₃, r₃, h₃⟩ := rootsLoop hS hBM hMM hG hpre (n - 0) 0 t₂ _ rfl h₂
  rcases h₃ with hd | ⟨rs, h₃⟩
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl hd⟩
  obtain ⟨t₄, r₄, h₄⟩ := rootsExit hpre h₃
  exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr ⟨rs, h₄⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.roots_spec
