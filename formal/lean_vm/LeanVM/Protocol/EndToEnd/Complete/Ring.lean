/-
  LeanVM.Protocol.EndToEnd.Complete.Ring

  The honest run of ring switching: no prover message, six challenges, and the ring-switching
  claim the program opens on the stack is true of the honest stack and has a multilinear weight,
  for the true slices of `q_keccak`.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingMultilinear
public import LeanVM.Protocol.Whir.Complete.Script

/-!
# Completeness of ring switching

About the transcription of `crates/verifier/src/ring_switch.rs:8-54` (`RING_MAP_SHIFTS`,
`ring_map`, `ring_weight`, `ring_switch`) and `lib.rs:305-312` (the ring claim on the stack) at
leanVM `40f877dc` (`Verifier.ringSwitch`, `Verifier.ringSwitchClaim`;
`crates/pcs/src/ring_switch.rs`).

`ringSwitch point s` reads nothing: it draws the six coefficients `ch` of the staged map `Φ` and
returns the target `Σ_i x^i Φ(s_i)` and the weight `W(u) = Σ_k c_k eq(point^(2^k), u)`. The
program opens `⟨eqAbove · W(take), q⟩ = target` on the stack.

For the true slices `s_i = ẑ_i(point)` of `q_keccak` (`KeccakGkr.slicesTrue`, what the Keccak
reduction's completeness `follows_keccak` gives), every error `s_i - ẑ_i(point)` is zero, so the
claim holds (`ringClaim_holds_of_slicesTrue`, from `Front.ringClaim_holds_iff`: the pairing is
`Σ_i x^i Φ(ẑ_i(point))`, the target `Σ_i x^i Φ(s_i)`); its weight is multilinear
(`Front.isMultilinearFn_ringWeight`).

`follows_ringSwitch`: the honest prover, which only receives the challenges, follows the program,
and the claim it returns holds of the stack with a multilinear weight; `follows_ringSwitch_leanIsa`
at the verifier's layout and the leanISA instance's stack. No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **The ring claim of true slices holds**: when the 64 slice claims hold of the block at `off`
where the layout places `q_keccak`, the program's ring claim holds of the stack, for any
coefficients. -/
theorem ringClaim_holds_of_slicesTrue {layout : Verifier.Layout} {h₅ off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h₅ + 6, index := off })
    (hal : 2 ^ (h₅ + 6) ∣ off) (hfit : off + 2 ^ (h₅ + 6) ≤ 2 ^ μ) (q : Column μ)
    {pt sv ch : List E} (hs : slicesTrue h₅ (Front.qkAt off q) pt sv) (hch : ch.length = 6) :
    StackClaim.Holds μ (ringSwitchClaim layout (polyEval (sv.map (phiMap · ch)) gen)
      fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)) q := by
  obtain ⟨hpt, hsv, hsl⟩ := hs
  refine (Front.ringClaim_holds_iff hpl hal hfit q hpt hsv hch).mpr ?_
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have he : Front.ringErr h₅ (Front.qkAt off q) pt sv i = 0 := sub_eq_zero.mpr (hsl i i.isLt)
  rw [he, Front.phiMap_eq_frobMap, Ring.frobMap_zero, mul_zero]

/-- **The honest prover of ring switching**: it sends nothing; it receives the six coefficients
and returns what the program returns. -/
def hRing (point slices : List E) : Script (E × (List E → E)) := do
  let challenges ← Script.sampleN ringMapShifts.length
  let coefficients := ringCoefficients challenges
  return (polyEval (slices.map (phiMap · challenges)) gen,
    fun rPrime ↦ ringWeight point rPrime coefficients)

/-- **Completeness of ring switching.** For the true slices of the block where the layout places
`q_keccak`, aligned and inside a stack of `μ` variables, the honest prover follows `ringSwitch`
for every challenge, and the claim the program opens on the stack holds of it with a multilinear
weight. -/
theorem follows_ringSwitch {layout : Verifier.Layout} {h₅ off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h₅ + 6, index := off })
    (hal : 2 ^ (h₅ + 6) ∣ off) (hfit : off + 2 ^ (h₅ + 6) ≤ 2 ^ μ) {q : Column μ}
    (r : List E × List E) (hr : slicesTrue h₅ (Front.qkAt off q) r.1 r.2) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds μ (ringSwitchClaim layout b.1 b.2) q ∧
        IsMultilinearFn μ (ringSwitchClaim layout b.1 b.2).1)
      (hRing r.1 r.2) (ringSwitch r.1 r.2) cs := by
  simp only [hRing, ringSwitch, Script.bind_eq, VerifierProgram.bind_eq]
  refine Follows.bind (fun cs' a b h ↦ ?_) _ _ _ (Follows.sampleN_sampleN cs _)
  obtain ⟨rfl, rfl, hl⟩ := h
  have hch : a.length = 6 := hl
  exact ⟨rfl, rfl, ringClaim_holds_of_slicesTrue hpl hal hfit q hr hch,
    Front.isMultilinearFn_ringWeight _ _ _ _⟩

/-- **Completeness of ring switching at the verifier's layout**, for a stack of the leanISA
instance: the true slices of its `q_keccak` block (`τ_KECCAK + 6` variables at the block's
offset). -/
theorem follows_ringSwitch_leanIsa {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ
    prog s)}
    (r : List E × List E)
    (hr : slicesTrue (s.τ 5) (Front.qkAt ((blocks prog s).offset (keccakBlock prog s)) q) r.1 r.2)
    (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (Front.verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (Front.verifierLayout prog s) b.1 b.2).1)
      (hRing r.1 r.2) (ringSwitch r.1 r.2) cs :=
  have hlay := Front.ringLayoutHyp_verifierLayout prog s
  follows_ringSwitch hlay.placement hlay.aligned
    (by have := hlay.fits; rwa [Front.stackLog_verifierLayout] at this) r hr cs

end
end LeanVM.Protocol.EndToEnd.Complete
