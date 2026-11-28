/-
  LeanVM.Protocol.Whir.Sound.DescentGood

  The compiled descent of a good trace ends on level 0's tuple, whose stack is not bad.
-/

module

public import LeanVM.Protocol.Whir.Sound.DescentC
public import LeanVM.Protocol.Whir.Sound.StackA

/-!
# The compiled descent, good

`descendC_good`: at an admissible shape, for the committed words given as arrays (`OAs`, each
level's leaves' lanes, `hO`), the compiled descent (`descendTraceC`, one-error Newton decoding over
arrays) of a good trace returns a tuple of level 0's lanes, and the stack read off its array
(`stackA`) is not bad. It chains `descend_good` (the descent over the near-tuple decoder),
`descendTraceV_eq` (the descent over values is its evaluation), `descendTraceA_eq` (over arrays),
`descendTraceC_eq` (the compiled form) and `stackA_eq`, `stackV_valsT` (the stack).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Whir.Params

@[expose] public section

/-- **The compiled descent of a good trace ends on a good stack.** -/
theorem descendC_good {μ R : ℕ} (h : Whir.Admissible μ R) (Bad : Column μ → Prop)
    (tr : WhirTrace) (cs : List (ℕ × ℕ × Word)) {OAs : List AV}
    (hO : ∀ i j (v : Fin (codesOf μ R i).n), laneO i cs (codesOf μ R i).n j v =
      ((OAs.getD i #[]).getD v #[]).getD j 0)
    (hg : traceGood (codesOf μ R) 0 (lvl0Pred μ Bad) tr cs) :
    ∃ VA, descendTraceC μ R OAs tr 0 = some (laneBits, VA) ∧ ¬ Bad ⟨stackA μ VA⟩ := by
  obtain ⟨m, T, hd, hm, hμ, hb⟩ := descend_good h newtonNearDecoder Bad tr cs hg
  subst hm
  have hc := descendTraceC_eq μ R OAs tr 0
  rw [descendTraceA_eq (codesOf μ R) cs hO, descendTraceV_eq newtonValsDecoder, hd] at hc
  simp only [Option.map_some, valsS, toAVS] at hc
  refine ⟨_, hc, ?_⟩
  obtain ⟨level, rest, F⟩ := level0Facts (shapeOK_of_admissible h)
  have hn : 2 ^ (μ - laneBits) ≤ (codesOf μ R 0).n := by
    have := two_pow_le_n (codesOf μ R 0)
    rwa [F.hκ₀] at this
  rw [stackA_eq hμ hn, stackV_valsT hμ (codesOf μ R 0) hn]
  exact hb

end
end LeanVM.Protocol.Whir.Sound
