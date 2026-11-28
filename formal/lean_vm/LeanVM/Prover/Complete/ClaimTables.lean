/-
  LeanVM.Prover.Complete.ClaimTables

  The opening's weight table, built by scatter from the claims' descriptions, is the verifier's
  weights on the cube.
-/

module

public import LeanVM.Prover.Complete.WhirOpening
import LeanVM.Facts.Hotwire

/-!
# The claims' tables

The honest opening builds its weight table by adding each claim's weight to a table of the stack's
`2^μ` cells (`addClaim`, `basisTableA`). For a claim whose verifier weight `w` (a `StackClaim`'s
first part) takes the added values on the cube (`DescMatches`), the table is the verifier's batched
basis table (`toList_basisTableA`).

* `getD_foldModify`: the scatter loop adds its values on a window.
* `eqEval_boolPoint`: `eq` of two cube points is their indicator.
* `eqEval_stackPoint`: a placed claim's weight on the cube is its point's equality kernel on its
  block, zero elsewhere, for an aligned block inside the stack.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.EndToEnd LeanVM.Protocol.Tables LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-! ## The scatter loop -/

/-- The scatter loop: `val u` added at `index + u`, `u < n`. -/
theorem getD_foldModify (acc : Array E) (index : ℕ) (val : ℕ → E) :
    ∀ n, (Nat.fold n (fun u _ acc ↦ acc.modify (index + u) (· + val u)) acc).size = acc.size ∧
      ∀ y, (Nat.fold n (fun u _ acc ↦ acc.modify (index + u) (· + val u)) acc).getD y 0 =
        acc.getD y 0 + if index ≤ y ∧ y < index + n ∧ y < acc.size then val (y - index) else 0
  | 0 => ⟨by simp, fun y ↦ by simp only [Nat.fold_zero]; split <;> [omega; simp]⟩
  | n + 1 => by
    obtain ⟨hs, hg⟩ := getD_foldModify acc index val n
    have hsucc : Nat.fold (n + 1) (fun u _ acc ↦ acc.modify (index + u) (· + val u)) acc =
        (Nat.fold n (fun u _ acc ↦ acc.modify (index + u) (· + val u)) acc).modify (index + n)
          (· + val n) := by rw [Nat.fold_succ]
    rw [hsucc]
    set F := Nat.fold n (fun u _ acc ↦ acc.modify (index + u) (· + val u)) acc
    refine ⟨by simp [hs], fun y ↦ ?_⟩
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify] at hg ⊢
    by_cases hy : index + n = y
    · subst hy
      have h := hg (index + n)
      simp only [lt_irrefl, and_false, false_and, ↓reduceIte, add_zero] at h
      by_cases hb : index + n < acc.size
      · have hF : index + n < F.size := by rw [hs]; exact hb
        rw [Array.getElem?_eq_getElem hF] at h ⊢
        simp only [Option.getD_some, Option.map_some] at h ⊢
        rw [h]
        simp [hb]
      · rw [Array.getElem?_eq_none (by rw [hs]; omega), Array.getElem?_eq_none (by omega)]
        simp [hb]
    · simp only [hy, ↓reduceIte]
      rw [hg y]
      split_ifs <;> first | rfl | omega

/-! ## Equality on the cube -/

theorem selectorPoint_eq_boolPoint (s m : ℕ) : selectorPoint s m = boolPoint m s := by
  simp only [selectorPoint, boolPoint]
  refine List.map_congr_left fun i _ ↦ ?_
  rw [Hotwire.eOfNat_mod_two, Nat.testBit, Nat.one_and_eq_mod_two]
  by_cases h : s >>> i % 2 = 1 <;> simp [h]

/-- `eq` of two cube points is `1` exactly when they are equal. -/
theorem eqEval_boolPoint : ∀ (m s z : ℕ), s < 2 ^ m → z < 2 ^ m →
    eqEval (boolPoint m s) (boolPoint m z) = if s = z then 1 else 0
  | 0, s, z, hs, hz => by
    obtain rfl : s = 0 := by simpa using hs
    obtain rfl : z = 0 := by simpa using hz
    simp [boolPoint]
  | m + 1, s, z, hs, hz => by
    rw [boolPoint_succ, boolPoint_succ, eqEval_cons,
      eqEval_boolPoint m (s / 2) (z / 2) (by rw [pow_succ] at hs; omega)
        (by rw [pow_succ] at hz; omega)]
    have key : s = z ↔ s / 2 = z / 2 ∧ s % 2 = z % 2 :=
      ⟨fun h ↦ by subst h; simp, fun ⟨h1, h2⟩ ↦ by omega⟩
    have h1 : (1 : E) + 1 = 0 := one_add_one_E
    rcases Nat.mod_two_eq_zero_or_one s with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one z with b | b <;>
      by_cases hq : s / 2 = z / 2 <;> simp [Nat.testBit_zero, a, b, hq, key, h1]

/-- **A placed claim's weight on the cube**: its point's equality kernel on its block, zero
elsewhere, for an aligned block inside the stack. -/
theorem eqEval_stackPoint {μ : ℕ} {p : Placement} {point : List E}
    (hpt : point.length = p.variableCount) (hv : p.variableCount ≤ μ)
    (hdvd : 2 ^ p.variableCount ∣ p.index) (hin : p.index + 2 ^ p.variableCount ≤ 2 ^ μ)
    {y : ℕ} (hy : y < 2 ^ μ) :
    eqEval (p.stackPoint point μ) (boolPoint μ y) =
      if p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount then
        eqEval (boolPoint p.variableCount (y - p.index)) point
      else 0 := by
  obtain ⟨v, index⟩ := p
  simp only at hpt hv hdvd hin ⊢
  obtain ⟨k, rfl⟩ : ∃ k, μ = v + k := ⟨μ - v, by omega⟩
  obtain ⟨c, rfl⟩ := hdvd
  have hpos : 0 < 2 ^ v := Nat.two_pow_pos v
  have hb : boolPoint (v + k) y = boolPoint v (y % 2 ^ v) ++ boolPoint k (y / 2 ^ v) := by
    conv_lhs => rw [← Nat.mod_add_div y (2 ^ v)]
    exact boolPoint_add v k _ _ (Nat.mod_lt _ hpos)
  have hc : c < 2 ^ k := by
    rw [pow_add] at hin
    by_contra h
    have : 2 ^ k * 2 ^ v ≤ c * 2 ^ v := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hyk : y / 2 ^ v < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.add_comm]; exact hy
  rw [Placement.stackPoint, hb, Nat.add_sub_cancel_left, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel_left _ hpos, selectorPoint_eq_boolPoint,
    eqEval_append _ _ _ _ (by rw [hpt, length_boolPoint]), eqEval_boolPoint k c _ hc hyk]
  have hiff : c = y / 2 ^ v ↔ (2 ^ v * c ≤ y ∧ y < 2 ^ v * c + 2 ^ v) := by
    have hd := Nat.div_add_mod y (2 ^ v)
    have hm := Nat.mod_lt y hpos
    constructor
    · rintro rfl
      exact ⟨Nat.mul_div_le y _, by linarith⟩
    · rintro ⟨h1, h2⟩
      symm
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; exact h1
      · rw [Nat.succ_mul, mul_comm]; exact h2
  rw [show (if c = y / 2 ^ v then (1 : E) else 0) =
      if (2 ^ v * c ≤ y ∧ y < 2 ^ v * c + 2 ^ v) then 1 else 0 from by simp only [hiff]]
  split_ifs with h
  · rw [mul_one, eqEval_comm, Nat.mod_eq_sub_mul_div, ← hiff.mpr h]
  · rw [mul_zero]

/-! ## Descriptions that match the verifier's weights -/

/-- **The description `d` adds the weight `w`** to a table of the cube of `2^μ` cells: its values
on the cube, scaled. -/
def DescMatches (μ : ℕ) (d : ClaimDesc) (w : List E → E) : Prop :=
  ∀ (acc : Array E) (s : E), acc.size = 2 ^ μ → (addClaim acc s d).size = 2 ^ μ ∧
    ∀ y < 2 ^ μ, (addClaim acc s d).getD y 0 = acc.getD y 0 + s * w (boolPoint μ y)

/-- Only the weight's values on the cube matter. -/
theorem DescMatches.congr {μ : ℕ} {d : ClaimDesc} {w w' : List E → E} (h : DescMatches μ d w)
    (hw : ∀ y < 2 ^ μ, w (boolPoint μ y) = w' (boolPoint μ y)) : DescMatches μ d w' :=
  fun acc s hacc ↦ ⟨(h acc s hacc).1, fun y hy ↦ by rw [(h acc s hacc).2 y hy, hw y hy]⟩

private theorem fold_addClaim {μ : ℕ} : ∀ (scales : List E) (descs : List ClaimDesc)
    (claims : List StackClaim), List.Forall₂ (fun d c ↦ DescMatches μ d c.1) descs claims →
    scales.length = descs.length → ∀ acc : Array E, acc.size = 2 ^ μ →
    ((List.zip scales descs).foldl (fun acc (s, d) ↦ addClaim acc s d) acc).size = 2 ^ μ ∧
      ∀ y < 2 ^ μ, ((List.zip scales descs).foldl (fun acc (s, d) ↦ addClaim acc s d) acc).getD y 0
        = acc.getD y 0 + batchedBasis scales claims (boolPoint μ y)
  | [], [], [], _, _, acc, hacc => ⟨hacc, fun y _ ↦ by simp [batchedBasis]⟩
  | s :: scales, d :: descs, c :: claims, List.Forall₂.cons hd hrest, hlen, acc, hacc => by
    obtain ⟨h1, h2⟩ := hd acc s hacc
    obtain ⟨h3, h4⟩ := fold_addClaim scales descs claims hrest (by simpa using hlen) _ h1
    refine ⟨by simpa using h3, fun y hy ↦ ?_⟩
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [h4 y hy, h2 y hy]
    simp only [batchedBasis, List.map_cons, dot_cons]
    ring
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _, [], _ :: _, h, _, _, _ => by cases h
  | _, _ :: _, [], h, _, _, _ => by cases h

/-- **The opening's weight table is the verifier's batched basis table**, for descriptions that
match the claims' weights. -/
theorem toList_basisTableA {μ : ℕ} (hμ : 6 ≤ μ) (scales : List E) (descs : List ClaimDesc)
    (claims : List StackClaim) (hm : List.Forall₂ (fun d c ↦ DescMatches μ d c.1) descs claims)
    (hlen : scales.length = descs.length) :
    (basisTableA μ scales descs).toList = basisTable μ scales claims := by
  obtain ⟨hs, hg⟩ := fold_addClaim scales descs claims hm hlen (Array.replicate (2 ^ μ) 0)
    (by simp)
  obtain ⟨n, rfl⟩ : ∃ n, μ = 6 + n := ⟨μ - 6, by omega⟩
  apply List.ext_getElem (by simp [basisTableA, basisTable, LeanVM.Protocol.Tables.tableOf])
  intro i h1 h2
  have hi : i < 2 ^ (6 + n) := by simpa [basisTableA] using h1
  have hr : rotIndex 6 n i < 2 ^ (6 + n) := by rw [Nat.add_comm 6 n]; exact rotIndex_lt hi
  have hb := boolPoint_rotIndex 6 n i hi
  rw [Nat.add_comm n 6] at hb
  have hrot : i / 2 ^ 6 + 2 ^ (6 + n - 6) * (i % 2 ^ 6) = rotIndex 6 n i := by
    simp [rotIndex]
  have hl : (basisTableA (6 + n) scales descs).toList[i] =
      ((List.zip scales descs).foldl (fun acc (s, d) ↦ addClaim acc s d)
        (Array.replicate (2 ^ (6 + n)) 0)).getD (rotIndex 6 n i) 0 := by
    rw [Array.getElem_toList]
    simp only [basisTableA, Array.getElem_ofFn]
    rw [hrot]
  have hrhs : (basisTable (6 + n) scales claims)[i] =
      batchedBasis scales claims ((boolPoint (6 + n) i).drop laneBits ++
        (boolPoint (6 + n) i).take laneBits) := by
    simp only [basisTable, LeanVM.Protocol.Tables.tableOf, List.getElem_map, List.getElem_range]
  rw [hl, hrhs, hg _ hr, ← hb]
  simp [Array.getD_eq_getD_getElem?, hr]

/-- A part of a cell claim inside the stack of `2^μ` cells: its point over its placement's
variables, and the placement aligned and inside. -/
def PartOK (μ : ℕ) (part : Placement × List E × E) : Prop :=
  part.2.1.length = part.1.variableCount ∧ part.1.variableCount ≤ μ ∧
    2 ^ part.1.variableCount ∣ part.1.index ∧ part.1.index + 2 ^ part.1.variableCount ≤ 2 ^ μ

/-- **Cell claims**: the parts' equality kernels on their blocks. -/
theorem descMatches_cells {μ : ℕ} : ∀ (parts : List (Placement × List E × E)),
    (∀ part ∈ parts, PartOK μ part) →
    DescMatches μ (.cells parts) (fun x ↦
      (parts.map fun part ↦ part.2.2 * eqEval (part.1.stackPoint part.2.1 μ) x).sum)
  | [], _ => fun acc s hacc ↦ ⟨hacc, fun y _ ↦ by simp [addClaim]⟩
  | (p, point, scale) :: parts, hok => fun acc s hacc ↦ by
    obtain ⟨hpt, hv, hdvd, hin⟩ := hok _ List.mem_cons_self
    simp only at hpt hv hdvd hin
    have hstep : addClaim acc s (.cells ((p, point, scale) :: parts)) =
        addClaim (Nat.fold (eqTable point).size (fun u _ acc ↦
          acc.modify (p.index + u) (· + s * scale * (eqTable point).getD u 0)) acc) s
          (.cells parts) := rfl
    obtain ⟨h1, h2⟩ := getD_foldModify acc p.index (fun u ↦ s * scale * (eqTable point).getD u 0)
      (eqTable point).size
    obtain ⟨h3, h4⟩ := descMatches_cells parts (fun part hp ↦ hok part (List.mem_cons_of_mem _ hp))
      _ s (h1.trans hacc)
    rw [hstep]
    refine ⟨h3, fun y hy ↦ ?_⟩
    rw [h4 y hy, h2 y]
    simp only [List.map_cons, List.sum_cons]
    rw [eqEval_stackPoint hpt hv hdvd hin hy, size_eqTable, hpt]
    by_cases hb : p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount
    · have hb' : p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount ∧ y < acc.size :=
        ⟨hb.1, hb.2, by omega⟩
      simp only [hb', and_self, ↓reduceIte]
      rw [getD_eqTable _ _ (by rw [hpt]; omega), hpt]
      ring
    · have hb' : ¬ (p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount ∧ y < acc.size) :=
        fun h ↦ hb ⟨h.1, h.2.1⟩
      simp only [hb', hb, ↓reduceIte]
      ring

/-- **The out-of-domain claim**: the equality kernel of its point on the whole stack. -/
theorem descMatches_ood {μ : ℕ} {z : List E} (hz : z.length = μ) :
    DescMatches μ (.ood z) (fun x ↦ eqEval z x) := fun acc s hacc ↦ by
  obtain ⟨h1, h2⟩ := getD_foldModify acc 0 (fun y ↦ s * (eqTable z).getD y 0) (eqTable z).size
  have hstep : addClaim acc s (.ood z) = Nat.fold (eqTable z).size (fun u _ acc ↦
      acc.modify (0 + u) (· + s * (eqTable z).getD u 0)) acc := by
    simp only [addClaim, zero_add]
  rw [hstep]
  refine ⟨h1.trans hacc, fun y hy ↦ ?_⟩
  have hc : 0 ≤ y ∧ y < 0 + 2 ^ μ ∧ y < acc.size := ⟨Nat.zero_le _, by omega, by omega⟩
  rw [h2 y, size_eqTable, hz]
  simp only [hc, and_self, ↓reduceIte]
  rw [Nat.sub_zero,
    getD_eqTable _ _ (by rw [hz]; exact hy), hz, eqEval_comm]

/-! ## The placed claims' weights -/

theorem length_stackPoint {μ : ℕ} {p : Placement} {point : List E}
    (hpt : point.length = p.variableCount) (hv : p.variableCount ≤ μ) :
    (p.stackPoint point μ).length = μ := by
  simp [Placement.stackPoint, selectorPoint, hpt]; omega

/-- A placed claim's weight is multilinear on the stack. -/
theorem isMultilinearFn_stackPoint {μ : ℕ} {p : Placement} {point : List E}
    (hpt : point.length = p.variableCount) (hv : p.variableCount ≤ μ) :
    IsMultilinearFn μ (fun x ↦ eqEval (p.stackPoint point μ) x) := by
  have h := isMultilinearFn_eqEval (p.stackPoint point μ)
  rw [length_stackPoint hpt hv] at h
  exact h

/-- **A placed claim's weight paired with the stack** is its point's equality kernel paired with
the stack's block. -/
theorem sum_stackPoint {μ : ℕ} (val : ℕ → E) {p : Placement} {point : List E}
    (hpt : point.length = p.variableCount) (hv : p.variableCount ≤ μ)
    (hdvd : 2 ^ p.variableCount ∣ p.index) (hin : p.index + 2 ^ p.variableCount ≤ 2 ^ μ) :
    ∑ y ∈ range (2 ^ μ), eqEval (p.stackPoint point μ) (boolPoint μ y) * val y =
      ∑ u ∈ range (2 ^ p.variableCount),
        eqEval (boolPoint p.variableCount u) point * val (p.index + u) := by
  rw [sum_congr rfl fun y hy ↦ by rw [eqEval_stackPoint hpt hv hdvd hin (mem_range.mp hy)]]
  have hsub : (range (2 ^ p.variableCount)).map (addLeftEmbedding p.index) ⊆ range (2 ^ μ) := by
    intro y hy
    simp only [mem_map, mem_range, addLeftEmbedding_apply] at hy ⊢
    omega
  rw [← sum_subset hsub fun y hy hn ↦ by
    have : ¬ (p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount) := fun h ↦ hn (by
      simp only [mem_map, mem_range, addLeftEmbedding_apply]
      exact ⟨y - p.index, by omega, by omega⟩)
    simp [this], sum_map]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' := mem_range.mp hu
  have hc : p.index ≤ p.index + u ∧ p.index + u < p.index + 2 ^ p.variableCount :=
    ⟨by omega, by omega⟩
  simp only [addLeftEmbedding_apply, Nat.add_sub_cancel_left, hc, and_self, ↓reduceIte]

end

end LeanVM.Prover
