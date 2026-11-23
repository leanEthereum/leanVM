/-
  LeanVM.Guest.B1.Gkr.GlCIter

  A radix-four layer's words (`GlIter`), what `verify_bus_gkr`'s buffers hold for layer `j`, and
  the layer's relation (`GlLay`) from them.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCLayer
public import LeanVM.Guest.B1.Gkr.GlCLayers

/-!
# A radix-four layer's words

`GlIter rd layers pts rounds o j`: the slot of `L = 2j + 2 - o`, its point in row `j + 1`, one
step of two levels, its words at the cursor, its round records `rounds·pos·g^y` for `y ≤ j / 4`
(record `y` after `2 (j % 4) + 8y` rounds), at an odd depth the row's zero cell, and the slot of
`L + 2` at the position `pos·g^(j/4 + 1)`. `glc_lay`: they give layer `j`'s relation.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **Layer `j`'s words.** -/
def GlIter (rd : Reader) (layers pts rounds : E) (o j : ℕ) : Prop :=
  ∃ (s : Fs) (cur : E) (st : GkrState) (pos : E) (D : GkStepD),
    GkSlot rd layers (2 * j + 2 - o) s cur st (pts * gen ^ (40 * (j + 1))) pos ∧
    D.Ok s st 2 ∧ TbReadsAt rd cur D.xs ∧
    (∀ y ≤ j / 4, RecAt rd (rounds * pos * gen ^ y) cur D.cs st.point
      (polyEval st.values s.squeeze.1) s.squeeze.2 (2 * (j % 4) + 8 * y)) ∧
    (o = 1 → LoadHolds rd (pts * gen ^ (40 * (j + 1))) (2 * j + 43) 0) ∧
    GkSlot rd layers (2 * j + 2 - o + 2) (D.s' s st 2) (cur * gen ^ D.xs.length) (D.st' s st 2)
      (pts * gen ^ (40 * (j + 2))) (pos * gen ^ (j / 4 + 1))

/-- **Layer `j`'s relation from its words.** -/
theorem glc_lay {rd : Reader} {o j : ℕ} (ho : o < 2) (hj : j < 2 ^ 28)
    {layers pts rounds gmu tabs stream : E} (h : GlIter rd layers pts rounds o j) :
    GlLay rd o layers rounds pts (gen ^ (2 - o)) gmu tabs stream j := by
  obtain ⟨s, cur, st, pos, D, h1, h2, h3, h4, h5, h6⟩ := h
  have hj4 : 4 * (j / 4) + j % 4 = j := Nat.div_add_mod j 4
  unfold GlLay
  have := glc_layer (rd := rd) (p := j % 4) (o := o) (m := j / 4) (Nat.mod_lt _ (by norm_num)) ho
    (by omega) (layers := layers) (rounds := rounds) (pts := pts) (gmu := gmu) (tabs := tabs)
    (stream := stream) (D := D) (by rw [hj4]; exact h1) h2 h3 h4 (by rw [hj4]; exact h5)
    (by rw [hj4]; exact h6)
  rwa [hj4] at this

end
end LeanVM.Guest.B1.Tables
