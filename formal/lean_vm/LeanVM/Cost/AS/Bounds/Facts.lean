module

public import LeanVM.Cost.Bounds.Layout
public import LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.Lite

/-!
# The announced sizes' facts

`decSizesL_facts`: the lite layout the announced sizes decode to meets the runner's assumptions
(`LayoutFacts`), its rate is `1` to `4` and its stack log-size within the verifier's range.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Parameters LeanVM.Protocol LeanVM.Extraction.Fast
open LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound

public section

theorem decSizesL_facts {bytecode : List K} {h : List EvP} {lay : LayoutLite} {ρ : ℕ}
    (hd : decSizesL bytecode h = some (lay, ρ)) :
    LayoutFacts lay ∧ 1 ≤ ρ ∧ ρ ≤ 4 ∧ Whir.minLogStack ≤ lay.stackLog ∧
      lay.stackLog ≤ Whir.maxLogStack := by
  unfold decSizesL at hd
  obtain ⟨ann, -, hd⟩ := Option.bind_eq_some_iff.mp hd
  unfold sizesOfL at hd
  dsimp only at hd
  split_ifs at hd with h1 h2
  obtain ⟨L, hL, hd⟩ := Option.bind_eq_some_iff.mp hd
  split_ifs at hd with h3
  rw [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  exact ⟨(buildLayoutLite_facts hL).1, h2.1, h2.2, h3.1, h3.2⟩

end

end LeanVM.Cost.Bounds.AS
