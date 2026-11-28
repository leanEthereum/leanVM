/-
  LeanVM.Protocol.Relation.Link.GroupLinks

  The drawn group's count when the pointers are one-hot and a link fails: the index claim less the
  index side's sum is a polynomial of degree `linkGroupError` in the draw, nonzero at some draw.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksDegSum

/-!
# A failing link

`f(v) = indexClaim(v) − Σ_{r Boolean} linkIdxAt(v, r)`, `v = (θ_0, drawn)`, is of total degree at
most `linkGroupError` (`polyFn_groupF`), and wherever it is nonzero the draw is doomed
(`groupDoom_of_claim`). `card_notDoom_of_groupF`: if it is nonzero at one draw, at most
`linkGroupError·|E|^N` draws escape (`card_not_doom_le`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset

@[expose] public section

open Classical

/-- The index claim less the index side's sum at the draw `v`. -/
def groupF (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ)
    (v : Fin (linkDrawn layout chunks + 1) → E) : E :=
  indexClaim layout chunks (List.ofFn v).tail -
    linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail []

/-- **The count from one draw where `groupF` is nonzero.** -/
theorem card_notDoom_of_groupF {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks)
    {x0 : Fin (linkDrawn layout chunks + 1) → E} (hx0 : groupF layout chunks q x0 ≠ 0) :
    (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks := by
  have hch' : Chunks.new chunks.width = some chunks := by rw [Chunks.new_width hch]; exact hch
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t :=
    fun t ht ↦ tableRows_le_height hA (hTlen ▸ ht)
  refine card_not_doom_le (polyFn_groupF q hch' hrows) hx0 (fun v hv ↦ ?_) le_rfl
  exact groupDoom_of_claim (sub_ne_zero.mp hv)

end

end LeanVM.Protocol.Relation
