/-
  LeanVM.Prover.WhirBasis

  The executable opening's weight table of the starting claim, built by scatter, is the
  specification's `basisTable`.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Prover.WhirTables
public import LeanVM.Protocol.EndToEnd.Front.RingFidelity

/-!
# The weight table of the stack claims

`toList_basisTableA`: the executable `basisTableA μ scales claims` is the specification's
`basisTable μ scales (claims.map ClaimDesc.denote)`. On the cube, a column claim's weight
`eq(stackPoint, ·)` is the equality kernel of its point on its block of the stack and zero
elsewhere (`onStack_boolPoint`); the ring claim's weight `eqAbove · ringWeight` is
`Φ(eq(point, ·))` on the block of `q_keccak` and zero elsewhere (`ringSwitchClaim_boolPoint`,
from `ringWeight_eq_sum`, `eqAt_frob` and `phiMap_eq_sum`). The scatter adds them in place
(`addSlice_spec`); a claim of another shape adds its weight's formula everywhere (`addFull`).
-/

namespace LeanVM.Prover.Enc

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Protocol
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-! ## Scatter -/

theorem ite_T {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_F {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem getD_modify_E (a : Array E) (i j : ℕ) (f : E → E) (hj : j < a.size) :
    (a.modify i f).getD j 0 = if i = j then f (a.getD j 0) else a.getD j 0 := by
  have hj' : j < (a.modify i f).size := by simpa using hj
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj', Array.getElem?_eq_getElem hj,
    Option.getD_some, Array.getElem_modify]

theorem addSlice_spec (off : ℕ) (vals : Array E) (s : E) : ∀ (n : ℕ) (acc : Array E),
    (addSlice off vals s n acc).size = acc.size ∧
    ∀ y < acc.size, (addSlice off vals s n acc).getD y 0 =
      acc.getD y 0 + if off ≤ y ∧ y < off + n then s * vals.getD (y - off) 0 else 0
  | 0, acc => ⟨rfl, fun y _ ↦ by simp [addSlice]⟩
  | n + 1, acc => by
    obtain ⟨h1, h2⟩ := addSlice_spec off vals s n (acc.modify (off + n) (· + s * vals.getD n 0))
    refine ⟨by rw [addSlice, h1, Array.size_modify], fun y hy ↦ ?_⟩
    rw [addSlice, h2 y (by simpa using hy), getD_modify_E _ _ _ _ hy]
    by_cases hyn : off + n = y
    · subst hyn
      simp only [↓reduceIte, Nat.add_sub_cancel_left]
      rw [ite_F (by omega), ite_T (by omega)]
      ring
    · simp only [hyn, ↓reduceIte]
      congr 1
      by_cases hc : off ≤ y ∧ y < off + n
      · rw [ite_T hc, ite_T (by omega)]
      · rw [ite_F hc, ite_F (by omega)]

theorem cubePoint_eq (m y : ℕ) : cubePoint m y = boolPoint m y := rfl

theorem addFull_spec (μ : ℕ) (w : List E → E) (s : E) (acc : Array E) :
    (addFull μ w s acc).size = acc.size ∧
      ∀ y < acc.size, (addFull μ w s acc).getD y 0 = acc.getD y 0 + s * w (boolPoint μ y) :=
  ⟨by simp [addFull], fun y hy ↦ by rw [addFull, getD_ofFn _ _ _ hy, cubePoint_eq]⟩

/-! ## The weights on the cube -/

theorem div_eq_iff_block {y v B : ℕ} :
    y / 2 ^ v = B ↔ B * 2 ^ v ≤ y ∧ y < B * 2 ^ v + 2 ^ v := by
  have hpos := Nat.two_pow_pos v
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self y _, ?_⟩
    have := Nat.lt_div_mul_add hpos (a := y)
    linarith
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.add_one_mul]; exact h2)

theorem boolPoint_split {μ v : ℕ} (hv : v ≤ μ) (y : ℕ) :
    boolPoint μ y = boolPoint v (y % 2 ^ v) ++ boolPoint (μ - v) (y / 2 ^ v) := by
  have h := boolPoint_add v (μ - v) (y % 2 ^ v) (y / 2 ^ v) (Nat.mod_lt _ (Nat.two_pow_pos v))
  rwa [Nat.mod_add_div, Nat.add_sub_cancel' hv] at h

/-- The selector part: equality of the high bits of `y` with the block of `index`. -/
theorem eqEval_selector {μ v y : ℕ} (hv : v ≤ μ) (hy : y < 2 ^ μ) (index : ℕ) :
    eqEval (boolPoint (μ - v) (index / 2 ^ v)) (boolPoint (μ - v) (y / 2 ^ v)) =
      if y / 2 ^ v = index / 2 ^ v % 2 ^ (μ - v) then 1 else 0 := by
  have hpow : 2 ^ μ = 2 ^ (μ - v) * 2 ^ v := by rw [← pow_add, Nat.sub_add_cancel hv]
  have hyv : y / 2 ^ v < 2 ^ (μ - v) := Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hpow]; exact hy)
  rw [← Front.boolPoint_mod (μ - v) (index / 2 ^ v),
    Complete.eqEval_boolPoint_boolPoint _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) hyv]
  by_cases h : y / 2 ^ v = index / 2 ^ v % 2 ^ (μ - v)
  · simp [h]
  · simp [h, Ne.symm h]

/-- Entry `j` of the equality kernel is `eq(point, j)`. -/
theorem eqKernel_getD_eqAt (point : List E) {j : ℕ} (hj : j < 2 ^ point.length) :
    (eqKernel point).getD j 0 = eqAt point j := by
  rw [getD_eqKernel point j hj, eqEval_comm, Front.eqEval_boolPoint_eqAt]

/-- The block condition and the offset in the block. -/
theorem block_ite {μ v y : ℕ} (index : ℕ) (a : ℕ → E) :
    (if y / 2 ^ v = index / 2 ^ v % 2 ^ (μ - v) then a (y % 2 ^ v) else 0) =
      if blockOff μ v index ≤ y ∧ y < blockOff μ v index + 2 ^ v then
        a (y - blockOff μ v index) else 0 := by
  rw [blockOff]
  by_cases h : y / 2 ^ v = index / 2 ^ v % 2 ^ (μ - v)
  · rw [ite_T h, ite_T (div_eq_iff_block.mp h)]
    congr 1
    rw [← h, Nat.mod_def, mul_comm]
  · rw [ite_F h, ite_F (fun h' ↦ h (div_eq_iff_block.mpr h'))]

/-- **A column claim's weight on the cube**: the equality kernel of its point on its block. -/
theorem onStack_boolPoint {layout : Layout} {c : ColumnClaim} {μ y : ℕ}
    (hlen : c.point.length = (layout.placement c.column).variableCount)
    (hv : (layout.placement c.column).variableCount ≤ μ) (hμ : layout.stackLog = μ) (hy : y <
        2 ^ μ) :
    (c.stackClaim layout).1 (boolPoint μ y) =
      if blockOff μ (layout.placement c.column).variableCount (layout.placement
          c.column).index ≤ y ∧
          y < blockOff μ (layout.placement c.column).variableCount (layout.placement
              c.column).index +
            2 ^ (layout.placement c.column).variableCount then
        (eqKernel c.point).getD
          (y - blockOff μ (layout.placement c.column).variableCount (layout.placement
              c.column).index) 0
      else 0 := by
  set pl := layout.placement c.column with hpl
  rw [← block_ite pl.index (fun j ↦ (eqKernel c.point).getD j 0)]
  simp only [ColumnClaim.stackClaim, Placement.stackPoint_eq_drop, ← hpl, hμ,
    Front.selectorPoint_eq_boolPoint, Front.drop_boolPoint]
  rw [boolPoint_split hv y, eqEval_append _ _ _ _ (by rw [hlen, length_boolPoint]),
    eqEval_selector hv hy, eqKernel_getD_eqAt _ (by rw [hlen]; exact Nat.mod_lt _ (by positivity)),
    ← Front.eqEval_boolPoint_eqAt, hlen]
  split <;> simp

/-- The ring's weight on a cube point of its own coordinates is `Φ(eq(point, ·))`. -/
theorem ringWeight_boolPoint {point ch : List E} {v : ℕ} (hlen : point.length = v)
    (h6 : ch.length = 6) {j : ℕ} (hj : j < 2 ^ v) :
    ringWeight point (boolPoint v j) (ringCoefficients ch) =
      phiMap ((eqKernel point).getD j 0) ch := by
  rw [Front.ringWeight_eq_sum, Front.length_ringCoefficients, Front.phiMap_eq_sum h6,
    eqKernel_getD_eqAt _ (by rw [hlen]; exact hj)]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [Front.eqAt_frob, ← Front.eqEval_boolPoint_eqAt, List.length_map, hlen]

/-- **The ring claim's weight on the cube**: `Φ(eq(point, ·))` on the block of `q_keccak`. -/
theorem ringSwitchClaim_boolPoint {layout : Layout} {target : E} {point ch : List E} {μ y : ℕ}
    (hlen : point.length = (layout.placement qkeccak).variableCount)
    (hv : (layout.placement qkeccak).variableCount ≤ μ) (h6 : ch.length = 6) (hy : y < 2 ^ μ) :
    (ringSwitchClaim layout target fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)).1
        (boolPoint μ y) =
      if blockOff μ (layout.placement qkeccak).variableCount (layout.placement qkeccak).index ≤ y ∧
          y < blockOff μ (layout.placement qkeccak).variableCount (layout.placement qkeccak).index +
            2 ^ (layout.placement qkeccak).variableCount then
        phiMap ((eqKernel point).getD
          (y - blockOff μ (layout.placement qkeccak).variableCount (layout.placement
              qkeccak).index) 0) ch
      else 0 := by
  set pl := layout.placement qkeccak with hpl
  rw [← block_ite pl.index (fun j ↦ phiMap ((eqKernel point).getD j 0) ch)]
  simp only [ringSwitchClaim, Placement.eqAbove, ← hpl, length_boolPoint,
    Front.selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow, Front.drop_boolPoint]
  rw [eqEval_selector hv hy, Front.take_boolPoint μ _ y hv, ← Front.boolPoint_mod,
    ringWeight_boolPoint hlen h6 (Nat.mod_lt _ (by positivity))]
  split <;> simp

/-! ## The scatter -/

theorem addClaim_spec {μ : ℕ} (s : E) (d : ClaimDesc) (acc : Array E) (hs : acc.size = 2 ^ μ) :
    (addClaim μ acc s d).size = 2 ^ μ ∧
      ∀ y < 2 ^ μ, (addClaim μ acc s d).getD y 0 = acc.getD y 0 + s * d.denote.1 (boolPoint μ y) := by
  cases d with
  | column layout c =>
    simp only [addClaim]
    split
    · rename_i h
      obtain ⟨hlen, hv, hμ⟩ := h
      obtain ⟨h1, h2⟩ := addSlice_spec (blockOff μ (layout.placement c.column).variableCount
        (layout.placement c.column).index) (eqTable c.point) s (eqTable c.point).size acc
      refine ⟨by rw [h1, hs], fun y hy ↦ ?_⟩
      rw [h2 y (by rw [hs]; exact hy), ClaimDesc.denote,
        show (fun x ↦ eqEval ((layout.placement c.column).stackPoint c.point layout.stackLog) x,
          c.value).1 (boolPoint μ y) = (c.stackClaim layout).1 (boolPoint μ y) from rfl,
        onStack_boolPoint hlen hv hμ hy,
        size_eqTable, hlen, mul_ite, mul_zero, getD_eqTable_eqKernel]
    · obtain ⟨h1, h2⟩ := addFull_spec μ (ClaimDesc.column layout c).denote.1 s acc
      exact ⟨by rw [h1, hs], fun y hy ↦ h2 y (by rw [hs]; exact hy)⟩
  | ring layout target point ch =>
    simp only [addClaim]
    split
    · rename_i h
      obtain ⟨hlen, hv, h6⟩ := h
      obtain ⟨h1, h2⟩ := addSlice_spec (blockOff μ (layout.placement qkeccak).variableCount
        (layout.placement qkeccak).index) ((eqTable point).map (phiMap · ch)) s
        ((eqTable point).map (phiMap · ch)).size acc
      refine ⟨by rw [h1, hs], fun y hy ↦ ?_⟩
      rw [h2 y (by rw [hs]; exact hy), ClaimDesc.denote,
        ringSwitchClaim_boolPoint hlen hv h6 hy, Array.size_map, size_eqTable, hlen,
        mul_ite, mul_zero]
      split_ifs with hb
      · rw [getD_map_of_lt _ _ _ 0 _ (by rw [size_eqTable, hlen]; omega), getD_eqTable_eqKernel]
      · rfl
    · obtain ⟨h1, h2⟩ := addFull_spec μ (ClaimDesc.ring layout target point ch).denote.1 s acc
      exact ⟨by rw [h1, hs], fun y hy ↦ h2 y (by rw [hs]; exact hy)⟩

theorem basisNat_aux (μ : ℕ) : ∀ (L : List (E × ClaimDesc)) (acc : Array E), acc.size = 2 ^ μ →
    (L.foldl (fun acc sd ↦ addClaim μ acc sd.1 sd.2) acc).size = 2 ^ μ ∧
      ∀ y < 2 ^ μ, (L.foldl (fun acc sd ↦ addClaim μ acc sd.1 sd.2) acc).getD y 0 =
        acc.getD y 0 + (L.map fun sd ↦ sd.1 * sd.2.denote.1 (boolPoint μ y)).sum
  | [], acc, hs => ⟨hs, fun y _ ↦ by simp⟩
  | sd :: L, acc, hs => by
    obtain ⟨h1, h2⟩ := addClaim_spec sd.1 sd.2 acc hs
    obtain ⟨h3, h4⟩ := basisNat_aux μ L _ h1
    refine ⟨h3, fun y hy ↦ ?_⟩
    rw [List.foldl_cons, h4 y hy, h2 y hy, List.map_cons, List.sum_cons, add_assoc]

theorem dot_map_eq_sum : ∀ (scales : List E) (claims : List ClaimDesc) (f : ClaimDesc → E),
    dot scales (claims.map f) = ((List.zip scales claims).map fun sd ↦ sd.1 * f sd.2).sum
  | [], _, _ => by simp [dot]
  | _ :: _, [], _ => by simp [dot]
  | a :: scales, c :: claims, f => by
    rw [List.map_cons, dot_cons, dot_map_eq_sum scales claims f]
    simp

/-- The batched weight on the cube, by scatter. -/
theorem basisNat_getD (μ : ℕ) (scales : List E) (claims : List ClaimDesc) {y : ℕ}
    (hy : y < 2 ^ μ) :
    (basisNat μ scales claims).getD y 0 =
      batchedBasis scales (claims.map ClaimDesc.denote) (boolPoint μ y) := by
  obtain ⟨_, h⟩ := basisNat_aux μ (List.zip scales claims) (Array.replicate (2 ^ μ) 0) (by simp)
  rw [basisNat, h y hy, batchedBasis, List.map_map, dot_map_eq_sum]
  simp [hy]

/-- **The weight table of the starting claim**, by scatter, is the specification's. -/
theorem toList_basisTableA (μ : ℕ) (scales : List E) (claims : List ClaimDesc) :
    (basisTableA μ scales claims).toList = basisTable μ scales (claims.map ClaimDesc.denote) := by
  have hsz : (basisTableA μ scales claims).size = 2 ^ μ := by
    unfold basisTableA; split <;> simp
  refine list_ext_getD (by simp [hsz, basisTable]) fun i hi ↦ ?_
  have hi' : i < 2 ^ μ := by simpa [hsz] using hi
  rw [toList_getD_E, basisTable, getD_tableOf _ _ _ hi', basisTableA]
  split
  · rename_i h6
    rw [getD_ofFn _ _ _ hi']
    simp only
    obtain ⟨n, rfl⟩ : ∃ n, μ = 6 + n := ⟨μ - 6, by omega⟩
    rw [show (6 + n - 6) = n by omega]
    have hy : i / 2 ^ 6 + 2 ^ n * (i % 2 ^ 6) < 2 ^ (6 + n) := by
      have := rotIndex_lt (k := 6) (n := n) hi'
      rwa [rotIndex, Nat.add_comm n 6] at this
    rw [basisNat_getD _ _ _ hy]
    have hb := boolPoint_rotIndex 6 n i hi'
    rw [Nat.add_comm n 6] at hb
    rw [← hb]
    rfl
  · rw [getD_ofFn _ _ _ hi']
    simp only [cubePoint_eq, batchedBasis, List.map_map]
    rfl

end
end LeanVM.Prover.Enc
