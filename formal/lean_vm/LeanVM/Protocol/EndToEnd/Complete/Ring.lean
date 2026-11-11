/-
  LeanVM.Protocol.EndToEnd.Complete.Ring

  The honest run of ring switching: no prover message, a grind and sixteen challenges, and the
  ring-switching claim the program opens on the stack is true of the honest stack and has a
  multilinear weight, for the true slices of `q_keccak`.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingMultilinear
public import LeanVM.Protocol.EndToEnd.Front.RingFidelity
public import LeanVM.Protocol.RingVerifier
public import LeanVM.Protocol.Whir.Complete.Script

/-!
# Completeness of ring switching

About the transcription of `crates/verifier/src/ring_switch.rs:10-87` (`ring_psi`,
`ring_target`, `ring_coefficients`, `ring_weight`, `ring_switch`) and `lib.rs:341-347` (the ring
claim on the stack) at leanVM `f128` (`Verifier.ringSwitch`, `Verifier.ringSwitchClaim`;
`crates/pcs/src/ring_switch.rs`).

`ringSwitch point s` reads nothing: after a grind it draws sixteen challenges, `f` then `g`, of
the two-stage map `Φ(v) = Σ_p f_p Ψ(v)^(2^(8p))`, `Ψ(v) = Σ_b g_b v^(2^b)`, and returns the target
`Σ_i x^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` (`Ring.ringSwitch_eq`). The program opens
`⟨eqAbove · W(take), q⟩ = target` on the stack.

For the true slices `s_i = ẑ_i(point)` of `q_keccak` (`KeccakGkr.slicesTrue`, what the Keccak
reduction's completeness `follows_keccak` gives) the target is the pairing
`Σ_i x^i Φ(ẑ_i(point))` (`Front.ringClaim_holds_iff`, `Ring.ringTarget_eq`), so the claim holds
(`ringClaim_holds_of_slicesTrue`); its weight is multilinear (`Front.isMultilinearFn_ringWeight`).

`follows_ringSwitch`: the honest prover, which passes the grind and receives the challenges,
follows the program, and the claim it returns holds of the stack with a multilinear weight;
`follows_ringSwitch_leanIsa` at the verifier's layout and the leanISA instance's stack. No
mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **The ring claim of true slices holds**: when the 64 slice claims hold of the block at `off`
where the layout places `q_keccak`, the program's ring claim holds of the stack, for any sixteen
challenges. -/
theorem ringClaim_holds_of_slicesTrue {layout : Verifier.Layout} {h₅ off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h₅ + 6, index := off })
    (hal : 2 ^ (h₅ + 6) ∣ off) (hfit : off + 2 ^ (h₅ + 6) ≤ 2 ^ μ) (q : Column μ)
    {pt sv ch : List E} (hs : slicesTrue h₅ (Front.qkAt off q) pt sv) (hch : ch.length = 16) :
    StackClaim.Holds μ (ringSwitchClaim layout (Ring.ringTarget sv (ch.take 8) (ch.drop 8))
      fun rPrime ↦ ringWeight pt rPrime (Ring.ringCoefficients (ch.take 8) (ch.drop 8))) q := by
  obtain ⟨hpt, hsv, hsl⟩ := hs
  rw [Ring.take_eq_ofFn_fOf hch, Ring.drop_eq_ofFn_gOf hch]
  refine (Front.ringClaim_holds_iff hpl hal hfit q hpt _ _ _).mpr ?_
  have hsvf : sv = List.ofFn fun i : Fin 64 ↦ Front.sliceExt h₅ (Front.qkAt off q) pt i := by
    apply List.ext_getElem (by simp [hsv])
    intro i h1 h2
    have := hsl i (by simpa using h2)
    rw [List.getD_eq_getElem _ _ h1] at this
    rw [this, List.getElem_ofFn]
    rfl
  rw [hsvf, Ring.ringTarget_eq]

/-- **The honest prover of ring switching**: it sends nothing; it passes the grind, receives the
sixteen challenges and returns what the program returns. -/
def hRing (point slices : List E) : Script (E × (List E → E)) :=
  (Script.grindBits Whir.batchGrindingBits).bind fun _ ↦
  (Script.sampleN 16).bind fun ch ↦
  .ret (Ring.ringTarget slices (ch.take 8) (ch.drop 8),
    fun rPrime ↦ ringWeight point rPrime (Ring.ringCoefficients (ch.take 8) (ch.drop 8)))

attribute [local irreducible] Follows in
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
  rw [Ring.ringSwitch_eq, hRing]
  refine Follows.bind (fun cs₀ _ _ h ↦ ?_) _ _ _ (Follows.grindBits_grindP _ cs)
  subst h
  refine Follows.bind (fun cs' a b h ↦ ?_) _ _ _ (Follows.sampleN_sampleN _ 16)
  obtain ⟨rfl, rfl, hl⟩ := h
  exact Follows.ret_ret ⟨rfl, rfl, ringClaim_holds_of_slicesTrue hpl hal hfit q hr hl,
    Front.isMultilinearFn_ringWeight _ _ _ _⟩

attribute [local irreducible] Follows in
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
