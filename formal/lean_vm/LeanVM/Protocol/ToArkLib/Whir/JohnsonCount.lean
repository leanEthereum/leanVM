/-
  LeanVM.Protocol.ToArkLib.Whir.JohnsonCount

  The Johnson count `jl n a r` in natural numbers, and the Johnson bound for set systems in that
  form.
-/

module

public import ArkLib.Data.Finset.PairwiseIntersection

/-!
# The Johnson count

Annex B of the leanVM specification (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`),
`thm:johnson-general`, and [CWYZ26], Lemma 3.2, in the integer form the Rust analysis
evaluates (`crates/pcs/src/whir_config/affine_mca.rs`, `johnson_list(n, a, r)`):

* `jl n a r = ⌊n (a - r) / (a² - n r)⌋`;
* `card_le_jl`: a family of sets of at least `a` points of an `n`-set, meeting pairwise in at most
  `r` points, has at most `jl n a r` members when `a² > n r`: ArkLib's Cauchy-Schwarz incidence
  count `Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le` (`|L| (a² - n r) ≤ n (a - r)`),
  divided.

It depends on Mathlib and one Mathlib-only ArkLib file, so that the affine-combiner files do.
-/

namespace LeanVM.Protocol.Whir

open Finset

@[expose] public section

/-- **The Johnson count** `⌊n (a - r) / (a² - n r)⌋` (`johnson_list(n, a, r)` in the Rust): at most
this many sets of at least `a` points of an `n`-set meet pairwise in at most `r` points, when
`a² > n r` (`card_le_jl`). -/
def jl (n a r : ℕ) : ℕ := n * (a - r) / (a * a - n * r)

section SetSystem

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- **Johnson bound, integer form** (Annex B, `thm:johnson-general`; [CWYZ26, Lemma 3.2]): a
family of sets of at least `a` points of an `n`-set, meeting pairwise in at most `r` points, has
at most `jl n a r` members when `a² > n r`. -/
theorem card_le_jl (L : Finset β) (T : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, a ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (T b ∩ T b').card ≤ r)
    (hgap : Fintype.card ι * r < a * a) :
    L.card ≤ jl (Fintype.card ι) a r :=
  (Nat.le_div_iff_mul_le (by omega)).mpr
    (Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le L T a r ha hr)

end SetSystem

end
end LeanVM.Protocol.Whir
