/-
  LeanVM.Guest.B1.Gkr.Layer

  A layer of `verify_bus_gkr`'s walk past the root-most: the layer slot and one step of two levels
  of the specification's GKR walk between two slots.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds

/-!
# A layer of two levels

A layer slot (`GkSlot`, `LAYER_SLOTS = 10` words a slot, in `layers`) carries the sponge's capacity,
the cursor, the three trees' values and the round position; the slot of point length `L` is at
`layers·g^(10 L)`. `LyB`: at the depth's parity `sh`, the radix-four layer `j` runs `gkrStep 2` from the slot of `L = 2j + 2 - sh`, its point in row `j + 1`
of the point triangle (`gkr_pts·g^(40(j + 1))`), to the slot of `L + 2`, its point in row `j + 2`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The layer slot -/

/-- **The slot of point length `L`** in `layers` (`LAYER_SLOTS = 10`): the carried capacity of the
sponge `s`, nothing waiting, the cursor, the three trees' values and the round position; the point
(of length `L`) is at `row`. -/
def GkSlot (rd : Reader) (layers : E) (L : ℕ) (s : Fs) (cur : E) (st : GkrState) (row pos : E) :
    Prop :=
  s.cap.length = 5 ∧ (∀ j < 5, LoadHolds rd layers (10 * L + j) (s.cap.getD j 0)) ∧ s.pend = [] ∧
    LoadHolds rd layers (10 * L + 5) cur ∧ st.values.length = 3 ∧
    (∀ t < 3, LoadHolds rd layers (10 * L + 6 + t) (st.values.getD t 0)) ∧
    st.point.length = L ∧ ReadsAt rd row st.point ∧ LoadHolds rd layers (10 * L + 9) pos

/-- **A layer of two levels**: the radix-four layer `j` at the depth's parity `sh`, from the slot of
`L = 2j + 2 - sh`, its point in row `j + 1` at `pts`, runs `gkrStep 2` to the slot of `L + 2`, its
point in row `j + 2`. -/
def LyB (rd : Reader) (sh : ℕ) (layers pts : E) (j : ℕ) : Prop :=
  ∀ (s : Fs) (cur : E) (st : GkrState) (pos : E),
    GkSlot rd layers (2 * j + 2 - sh) s cur st (pts * gen ^ (40 * (j + 1))) pos →
    ∃ (xs : List E) (st' : GkrState) (s' : Fs) (pos' : E),
      RunsTo (gkrStep 2 false st) s xs st' s' ∧ ReadsAt rd cur xs ∧
      GkSlot rd layers (2 * j + 2 - sh + 2) s' (cur * gen ^ xs.length) st'
        (pts * gen ^ (40 * (j + 2))) pos'

/-! ## Helpers -/

/-- A list of length `n` is its `n` entries. -/
theorem tb_eq_map_getD {l : List E} {n : ℕ} (h : l.length = n) :
    l = (List.range n).map (l.getD · 0) := by
  subst h
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The rate cells of nothing waiting are zeros. -/
theorem tb_rateOf_nil_getD (k : ℕ) : (rateOf []).getD k 0 = 0 := by
  rw [rateOf_eq_cells [] (by simp)]
  simp only [pendCells, List.flatMap_nil, List.nil_append, List.length_nil,
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A run of `13` values from `b`. -/
def lyOuts (b : ℕ) : List V := (List.range 13).map fun k ↦ .n (b + k)

/-- The capacity cells among a permutation's outputs from `b`. -/
def lyCap (b : ℕ) : List V := (List.range 5).map fun k ↦ .n (b + 8 + k)

/-- A permutation's thirteen outputs from `b`, and its capacity cells. -/
theorem ly_keccak {rd : Reader} {σ : Val} {ins : List V} {b : ℕ}
    (hk : (Atom.keccak ins (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, -, hout⟩ := keccakA_perm hk
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hP, ?_⟩
  simp only [lyCap, capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- The empty rate and a capacity as a permutation's inputs. -/
theorem ly_zero_rate {σ : Val} {z1 z2 z3 z4 : ℕ} (h1 : σ (.n z1) = 0) (h2 : σ (.n z2) = 0)
    (h3 : σ (.n z3) = 0) (h4 : σ (.n z4) = 0) (cap : List V) :
    (([.n z1, .n z1, .n z1, .n z1, .n z1, .n z2, .n z3, .n z4] ++ cap : List V).map σ) =
      rateOf [] ++ cap.map σ := by
  rw [List.map_append, tb_eq_map_getD (show (rateOf []).length = 8 by simp [rateOf])]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, tb_rateOf_nil_getD, h1, h2, h3, h4]

end
end LeanVM.Guest.B1.Tables
