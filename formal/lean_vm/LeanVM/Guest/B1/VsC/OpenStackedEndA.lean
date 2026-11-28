/-
  LeanVM.Guest.B1.VsC.OpenStackedEndA

  `open_stacked`'s placed completeness with its end bounded, which `verify_sub`'s windows need.
-/

module

public import LeanVM.Guest.B1.VsC.OpenStackedA

/-!
# `open_stacked`, placed, its end bounded

`OpenStackedEndA fs al cert k m`: `OpenStackedCompleteA`'s conclusion with iface's end bound, the
end within `2^36` of its cursor (at every cursor, so vsbnd's `EndLe c 36 e`), and the returned point buffers ending at most at the end
(`check_stack_terminal`'s `PtrsBelow` reads them below its frame). `CallAtA` does not bound its end, so the bound is a
separate statement beside `OpenStackedCompleteA`, which it gives (`OpenStackedEndA.toA`), and
`verify_sub`'s windows take it where they place `open_stacked`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) in
/-- **`open_stacked__L{m}` completes placed, its end within `2^36` of its cursor**, its point
buffers below its end. -/
def OpenStackedEndA (k m : ℕ) : Prop :=
  ∀ (r : ℕ) (root : Digest) (fsv : List E) (target : E) (ic it : ℕ) (xs : List E)
    (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ))
    (qs : List (ℕ × List ℕ)) (R : ℕ → Prop),
    1 ≤ r → r ≤ 4 → fsv.length = 5 → (∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp) →
    RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os [(root, stackShape (minOpenLog + m) r)]
      w s' roots' →
    OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs →
    (∀ i < xs.length, R (ic + i)) → (∀ n < 2 ^ winTabBits, R (it + n)) →
    ∀ fp c, fp + fs (openName (minOpenLog + m)) ≤ c → ∃ bp bp1 e : ℕ,
      CallAtA fs al cert k (openName (minOpenLog + m))
        (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic),
          ofK (addressOfIndex it)])
        [w.target, ofK (addressOfIndex bp), ofK (addressOfIndex bp1), w.inner, w.residual,
          ofK (addressOfIndex (ic + xs.length))] R
        (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
        (fun rd => ReadsAt rd (ofK (addressOfIndex bp)) (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0) ∧
          ReadsAt rd (ofK (addressOfIndex bp1)) (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1))
        (fun rd => ReadsAt rd (ofK (addressOfIndex ic)) xs ∧ WinTabs rd (ofK (addressOfIndex it)))
        (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
          t.Every (ExactAt coreProgram rd))
        (fs (openName (minOpenLog + m))) fp c e ∧
      bp + pointCap ≤ e ∧ bp1 + pointCap ≤ e ∧ e ≤ c + 2 ^ 36

/-- The bounded form gives `OpenStackedCompleteA`. -/
theorem OpenStackedEndA.toA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k m : ℕ}
    (h : OpenStackedEndA fs al cert k m) : OpenStackedCompleteA fs al cert k m := by
  intro r root fsv target ic it xs os w s' roots' qs R h1 h4 hl hc hrun hq hRx hRt fp c hfc
  obtain ⟨bp, bp1, e, hA, -⟩ := h r root fsv target ic it xs os w s' roots' qs R h1 h4 hl hc hrun hq hRx hRt fp c hfc
  exact ⟨bp, bp1, e, hA⟩

end
end LeanVM.Guest.B1.VsC
