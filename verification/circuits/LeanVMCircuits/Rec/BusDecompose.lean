module

public import LeanVMCircuits.Rec.TableSum

@[expose] public section

/-!
`bus::verify_balance`'s decomposition of a side's leaf claim (`Side::decompose`).

A side of the bus is a layer of `2^n` leaves: block `b` of `2^κ_b` rows sits at place `q_b` among the blocks of its
height, its rows the leaves `2^κ_b q_b + z`, and every leaf no block covers is padding, `1`. The GKR leaves the claim
`Ṽ(ζ) = Σ_x eq(ζ, x) L(x)` on the layer. `AirLink.leaf_decompose`: it is `Σ_b sel_b(ζ) Σ_z eq(ζ[..κ_b], z) leaf_b(z)
+ (1 - Σ_b sel_b)`, block `b`'s selector `sel_b = eq_bits(q_b, ζ[κ_b..])` (`AirLink.sel`) and the padding the leftover
mass. A table's block carries `β + Σ_i w_i c_i(z)` over its row's coordinates (`AirLink.DCoord`: a constant, a column,
a product or scaled column, or a virtual coordinate the verifier evaluates itself, an `IntIndex` or `Public` one; a
`Sum`'s children each a term at its weight), so its part is its form at its row (`AirLink.blockQuad`: `BusForm`'s
accumulation, the constant `β` and each column's and product's weight) plus the virtual coordinates' share
(`AirLink.blockKnown`). `AirLink.side_decompose`: the leaf claim is the side's framework part (the framework blocks'
leaves at `ζ`, the tables' virtual coordinates and the padding mass, `AirLink.framework`) plus each table's form
(`AirLink.sideForm`, its blocks' forms at their selectors) summed over its rows against `eq(ζ[..τ_T], z)`.
`AirLink.totals_eq`: the totals `bus::verify_balance` derives, `framework + Ṽ(ζ)`, are so the forms' sums
(`AirLink.formSums`), in characteristic two. `AirLink.tableClaim_of_leaves`: where both sides' totals are so their
forms' sums, the table sumcheck runs over the bus point's first `N` coordinates with every owned table's `τ` at most
`N`, and no row breaks an identity, the totals' `σ_0 + ξ σ_1` is `AirLink.tableInst`'s sum at those forms:
`ChecksGiveTable`'s table conjunct from the GKR's leaf claims.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset

variable {n : ℕ} (ζ : Fin n → E)

/-- Block `q` of height `2^κ`'s selector: `eq_bits(q, ζ[κ..])`, `Arith::eq_bits` of its place on the variables above
its rows'. -/
noncomputable def sel (κ q : ℕ) : E :=
  ∏ j : Fin n, if κ ≤ (j : ℕ) then (if q.testBit ((j : ℕ) - κ) then ζ j else 1 + ζ j) else 1

/-- `eq(ζ, x)` on a block's row: its selector times `eq(ζ[..κ], z)`. -/
theorem rowEq_block {κ : ℕ} (q z : ℕ) (hz : z < 2 ^ κ) :
    rowEq ζ n (2 ^ κ * q + z) = sel ζ κ q * rowEq ζ κ z := by
  simp only [rowEq, sel, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_two_pow_mul_add q hz]
  by_cases h : (j : ℕ) < κ
  · simp [h, show ¬ κ ≤ (j : ℕ) by omega]
  · simp [h, show κ ≤ (j : ℕ) by omega, j.isLt]

theorem rowEq_succ {κ : ℕ} (hκ : κ < n) (Z : ℕ) :
    rowEq ζ (κ + 1) Z = rowEq ζ κ Z * (if Z.testBit κ then ζ ⟨κ, hκ⟩ else 1 + ζ ⟨κ, hκ⟩) := by
  simp only [rowEq]
  rw [← Finset.mul_prod_erase _ _ (mem_univ (⟨κ, hκ⟩ : Fin n)),
    ← Finset.mul_prod_erase (univ : Finset (Fin n)) (fun j : Fin n => if (j : ℕ) < κ then _ else 1)
      (mem_univ (⟨κ, hκ⟩ : Fin n))]
  simp only [lt_add_one, if_true, lt_irrefl, if_false, one_mul]
  rw [mul_comm]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hne : (j : ℕ) ≠ κ := fun h => (mem_erase.mp hj).1 (Fin.ext h)
  by_cases h : (j : ℕ) < κ
  · simp [h, show (j : ℕ) < κ + 1 by omega]
  · simp [h, show ¬ (j : ℕ) < κ + 1 by omega]

/-- `eq(ζ[..κ], ·)` sums to one over the rows. -/
theorem sum_rowEq : ∀ κ ≤ n, ∑ z ∈ range (2 ^ κ), rowEq ζ κ z = 1
  | 0, _ => by simp [rowEq]
  | κ + 1, h => by
    have hκ : κ < n := h
    rw [pow_succ, mul_two, sum_range_add]
    have e1 : ∀ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) z = rowEq ζ κ z * (1 + ζ ⟨κ, hκ⟩) := fun z hz => by
      rw [rowEq_succ ζ hκ, Nat.testBit_lt_two_pow (mem_range.mp hz)]
      simp
    have e2 : ∀ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) (2 ^ κ + z) = rowEq ζ κ z * ζ ⟨κ, hκ⟩ := fun z hz => by
      rw [rowEq_succ ζ hκ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (mem_range.mp hz)]
      simp only [Bool.not_false, if_true]
      congr 1
      simp only [rowEq]
      refine prod_congr rfl fun j _ => ?_
      by_cases hj : (j : ℕ) < κ
      · simp [hj, Nat.testBit_two_pow_add_gt hj]
      · simp [hj]
    rw [sum_congr rfl e1, sum_congr rfl e2, ← sum_mul, ← sum_mul, sum_rowEq κ (by omega), ← mul_add, one_mul,
      add_assoc, ← two_mul, two_E, zero_mul, add_zero]

/-- A side's leaf claim by its blocks: block `b` of `2^κ_b` rows at place `q_b`, its leaves `leaf_b`, every other leaf
of the `2^n` padding (`1`). -/
theorem leaf_decompose {m : ℕ} (κ q : Fin m → ℕ) (L : ℕ → E) (leaf : Fin m → ℕ → E) (hκ : ∀ b, κ b ≤ n)
    (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b, ∀ z < 2 ^ κ b, L (2 ^ κ b * q b + z) = leaf b z)
    (hpad : ∀ x < 2 ^ n, (∀ b, x ∉ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)) → L x = 1) :
    ∑ x ∈ range (2 ^ n), rowEq ζ n x * L x =
      ∑ b, sel ζ (κ b) (q b) * ∑ z ∈ range (2 ^ κ b), rowEq ζ (κ b) z * leaf b z + (1 - ∑ b, sel ζ (κ b) (q b)) := by
  set blk := fun b : Fin m => Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)
  have hsplit : ∑ x ∈ range (2 ^ n), rowEq ζ n x * L x =
      ∑ x ∈ range (2 ^ n), rowEq ζ n x * (L x - 1) + 1 := by
    have e : ∀ x ∈ range (2 ^ n), rowEq ζ n x * L x = rowEq ζ n x * (L x - 1) + rowEq ζ n x := fun x _ => by ring
    rw [sum_congr rfl e, sum_add_distrib, sum_rowEq ζ n le_rfl]
  have hsub : univ.biUnion blk ⊆ range (2 ^ n) := fun x hx => by
    obtain ⟨b, -, hb⟩ := mem_biUnion.mp hx
    exact mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp hb).2 (hin b))
  have hout : ∑ x ∈ range (2 ^ n), rowEq ζ n x * (L x - 1) = ∑ x ∈ univ.biUnion blk, rowEq ζ n x * (L x - 1) := by
    refine (sum_subset hsub fun x hx hnx => ?_).symm
    rw [hpad x (mem_range.mp hx) fun b hb => hnx (mem_biUnion.mpr ⟨b, mem_univ _, hb⟩), sub_self, mul_zero]
  have hblk : ∀ b, ∑ x ∈ blk b, rowEq ζ n x * (L x - 1) =
      sel ζ (κ b) (q b) * (∑ z ∈ range (2 ^ κ b), rowEq ζ (κ b) z * leaf b z - 1) := fun b => by
    simp only [blk]
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have e : ∀ z ∈ range (2 ^ κ b), rowEq ζ n (2 ^ κ b * q b + z) * (L (2 ^ κ b * q b + z) - 1) =
        sel ζ (κ b) (q b) * (rowEq ζ (κ b) z * leaf b z) - sel ζ (κ b) (q b) * rowEq ζ (κ b) z := fun z hz => by
      rw [rowEq_block ζ (q b) z (mem_range.mp hz), hleaf b z (mem_range.mp hz)]
      ring
    rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_rowEq ζ (κ b) (hκ b), mul_sub, mul_one]
  rw [hsplit, hout, sum_biUnion fun b _ b' _ hbb' => hdisj b b' hbb', sum_congr rfl fun b _ => hblk b]
  simp only [mul_sub, mul_one, sum_sub_distrib]
  ring

/-! A table's block as a form. -/

/-- A coordinate of a table's block at a row (`bus::Coord`): a constant, a column, a product or scaled column, or a
virtual coordinate the verifier evaluates itself (an `IntIndex` or `Public` one, its values by row). A `Sum`'s
children are terms at its weight. -/
inductive DCoord where
  | const (v : E)
  | col (c : ℕ)
  | prod (a b : ℕ)
  | scaled (k : E) (c : ℕ)
  | virt (f : ℕ → E)

/-- A coordinate's value at row `z`, its columns `row`. -/
noncomputable def DCoord.val (row : ℕ → E) (z : ℕ) : DCoord → E
  | .const v => v
  | .col c => row c
  | .prod a b => row a * row b
  | .scaled k c => k * row c
  | .virt f => f z

/-- A table block's leaf at row `z`: `β + Σ_i w_i c_i(z)`. -/
noncomputable def blockLeaf (β : E) (ts : List (E × DCoord)) (row : ℕ → E) (z : ℕ) : E :=
  β + (ts.map fun t => t.1 * t.2.val row z).sum

/-- A table block's form (`BusForm::accumulate`, before its selector): its constant `β` plus its constants' weights,
each column's weight (a scaled column's times its scale) and each product's. -/
noncomputable def blockQuad (β : E) (ts : List (E × DCoord)) : Quad where
  const := β + (ts.map fun t => match t.2 with
    | .const v => t.1 * v
    | _ => 0).sum
  lin := ts.filterMap fun t => match t.2 with
    | .col c => some (c, t.1)
    | .scaled k c => some (c, t.1 * k)
    | _ => none
  prods := ts.filterMap fun t => match t.2 with
    | .prod a b => some (a, b, t.1)
    | _ => none

/-- Its virtual coordinates' share at `ζ`: each one's weight times its values summed against `eq(ζ[..κ], ·)`. -/
noncomputable def blockKnown (κ : ℕ) (ts : List (E × DCoord)) : E :=
  (ts.map fun t => match t.2 with
    | .virt f => t.1 * ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * f z
    | _ => 0).sum

/-- A table block's leaf is its form at its row plus its virtual coordinates. -/
theorem blockLeaf_eq (β : E) (row : ℕ → E) (z : ℕ) :
    ∀ ts : List (E × DCoord), blockLeaf β ts row z = (blockQuad β ts).eval row +
      (ts.map fun t => match t.2 with
        | .virt f => t.1 * f z
        | _ => 0).sum
  | [] => by simp [blockLeaf, blockQuad, Quad.eval]
  | (w, c) :: ts => by
    have ih := blockLeaf_eq β row z ts
    simp only [blockLeaf, blockQuad, Quad.eval] at ih ⊢
    cases c <;> simp [DCoord.val] at ih ⊢ <;> linear_combination ih

theorem sum_list_comm {α : Type} (κ : ℕ) (h : ℕ → α → E) :
    ∀ ts : List α, ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * (ts.map (h z)).sum =
      (ts.map fun t => ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * h z t).sum
  | [] => by simp
  | t :: ts => by
    simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib, sum_list_comm κ h ts]

/-- A table block's part of the leaf claim: its form summed over its rows against `eq(ζ[..κ], ·)`, plus its virtual
coordinates' share. -/
theorem block_sum {κ : ℕ} (β : E) (ts : List (E × DCoord)) (row : ℕ → ℕ → E) :
    ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * blockLeaf β ts (row z) z =
      ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * (blockQuad β ts).eval (row z) + blockKnown ζ κ ts := by
  simp only [blockLeaf_eq, mul_add, sum_add_distrib, blockKnown]
  congr 1
  rw [sum_list_comm]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  rcases t with ⟨w, c⟩
  cases c <;> simp [mul_sum, mul_left_comm]

/-! A side: its framework part and its tables' forms. -/

/-- Forms add and scale. -/
noncomputable def Quad.add (p q : Quad) : Quad := ⟨p.const + q.const, p.lin ++ q.lin, p.prods ++ q.prods⟩

noncomputable def Quad.smul (a : E) (q : Quad) : Quad :=
  ⟨a * q.const, q.lin.map fun t => (t.1, a * t.2), q.prods.map fun t => (t.1, t.2.1, a * t.2.2)⟩

theorem Quad.eval_add (p q : Quad) (col : ℕ → E) : (p.add q).eval col = p.eval col + q.eval col := by
  simp only [Quad.add, Quad.eval, List.map_append, List.sum_append]
  ring

theorem Quad.eval_smul (a : E) (q : Quad) (col : ℕ → E) : (q.smul a).eval col = a * q.eval col := by
  simp only [Quad.smul, Quad.eval, List.map_map, Function.comp_def, mul_add]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  simp only [mul_assoc]

variable {m : ℕ} (κ q : Fin m → ℕ) (owner : Fin m → Option Table) (β : E) (ts : Fin m → List (E × DCoord))

/-- Table `T`'s form on a side (`forms[s][T]` after `Side::decompose`): each of its blocks' forms at the block's
selector. -/
noncomputable def sideForm (T : Table) : Quad :=
  ((List.finRange m).filter fun b => owner b == some T).foldr
    (fun b f => (Quad.smul (sel ζ (κ b) (q b)) (blockQuad β (ts b))).add f) ⟨0, [], []⟩

/-- A side's framework part (`Side::decompose`'s return): its framework blocks' leaves at `ζ`, its tables' virtual
coordinates, and the padding mass `1 - Σ_b sel_b`. -/
noncomputable def framework (leaf : Fin m → ℕ → E) : E :=
  ∑ b with owner b = none, sel ζ (κ b) (q b) * ∑ z ∈ range (2 ^ κ b), rowEq ζ (κ b) z * leaf b z +
    ∑ b with owner b ≠ none, sel ζ (κ b) (q b) * blockKnown ζ (κ b) (ts b) + (1 - ∑ b, sel ζ (κ b) (q b))

theorem sum_filter_list' {α M : Type} [AddCommMonoid M] (p : α → Bool) (F : α → M) :
    ∀ l : List α, ((l.filter p).map F).sum = (l.map fun j => if p j then F j else 0).sum
  | [] => rfl
  | j :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_list' p F l]
    split <;> simp_all

theorem sideForm_eval (T : Table) (col : ℕ → E) :
    (sideForm ζ κ q owner β ts T).eval col =
      ∑ b with owner b = some T, sel ζ (κ b) (q b) * (blockQuad β (ts b)).eval col := by
  have h : ∀ l : List (Fin m), (l.foldr (fun b f => (Quad.smul (sel ζ (κ b) (q b)) (blockQuad β (ts b))).add f)
      ⟨0, [], []⟩).eval col = (l.map fun b => sel ζ (κ b) (q b) * (blockQuad β (ts b)).eval col).sum := by
    intro l
    induction l with
    | nil => simp [Quad.eval]
    | cons b l ih => rw [List.foldr_cons, Quad.eval_add, Quad.eval_smul, ih, List.map_cons, List.sum_cons]
  rw [sideForm, h, sum_filter_list', Finset.sum_filter, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  simp only [beq_iff_eq]

/-- The decomposition (`Side::decompose`): a side's leaf claim `Σ_x eq(ζ, x) L(x)` is its framework part plus each
table's form summed over its rows against `eq(ζ[..τ_T], z)`, where each table block of `T` has `2^τ_T` rows, each
`β + Σ_i w_i c_i` over table `T`'s row (`blockLeaf`), and every table owning a block is among `Ts`. -/
theorem side_decompose (L : ℕ → E) (leaf : Fin m → ℕ → E) (τ : Table → ℕ) (row : Table → ℕ → ℕ → E)
    (Ts : Finset Table) (hκ : ∀ b, κ b ≤ n) (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b, ∀ z < 2 ^ κ b, L (2 ^ κ b * q b + z) = leaf b z)
    (hpad : ∀ x < 2 ^ n, (∀ b, x ∉ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)) → L x = 1)
    (hT : ∀ b T, owner b = some T → T ∈ Ts ∧ κ b = τ T ∧ ∀ z, leaf b z = blockLeaf β (ts b) (row T z) z) :
    ∑ x ∈ range (2 ^ n), rowEq ζ n x * L x = framework ζ κ q owner ts leaf +
      ∑ T ∈ Ts, ∑ z ∈ range (2 ^ τ T), rowEq ζ (τ T) z * (sideForm ζ κ q owner β ts T).eval (row T z) := by
  rw [leaf_decompose ζ κ q L leaf hκ hin hdisj hleaf hpad, framework,
    ← Finset.sum_filter_add_sum_filter_not univ (fun b => owner b = none)]
  set ownerT := fun b => (owner b).getD .emul
  have hown : ∀ b T, owner b = some T ↔ owner b ≠ none ∧ ownerT b = T := fun b T => by
    cases h : owner b <;> simp [ownerT, h]
  have hQ : ∀ b ∈ univ.filter (fun b => ¬ owner b = none), sel ζ (κ b) (q b) *
      ∑ z ∈ range (2 ^ κ b), rowEq ζ (κ b) z * leaf b z = sel ζ (κ b) (q b) * blockKnown ζ (κ b) (ts b) +
        sel ζ (κ b) (q b) * ∑ z ∈ range (2 ^ τ (ownerT b)), rowEq ζ (τ (ownerT b)) z *
          (blockQuad β (ts b)).eval (row (ownerT b) z) := by
    intro b hb
    obtain ⟨T, hTb⟩ := Option.ne_none_iff_exists'.mp (mem_filter.mp hb).2
    obtain ⟨-, hκT, hlf⟩ := hT b T hTb
    have hoT : ownerT b = T := ((hown b T).mp hTb).2
    rw [hoT, hκT, sum_congr rfl fun z _ => by rw [hlf z], block_sum, mul_add, add_comm]
  have hforms : ∑ T ∈ Ts, ∑ z ∈ range (2 ^ τ T), rowEq ζ (τ T) z * (sideForm ζ κ q owner β ts T).eval (row T z) =
      ∑ b with ¬ owner b = none, sel ζ (κ b) (q b) * ∑ z ∈ range (2 ^ τ (ownerT b)), rowEq ζ (τ (ownerT b)) z *
        (blockQuad β (ts b)).eval (row (ownerT b) z) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := ownerT) (t := Ts) fun b hb => by
      obtain ⟨T, hTb⟩ := Option.ne_none_iff_exists'.mp (mem_filter.mp hb).2
      rw [((hown b T).mp hTb).2]
      exact (hT b T hTb).1]
    refine sum_congr rfl fun T _ => ?_
    simp only [sideForm_eval, mul_sum]
    rw [sum_comm, filter_filter]
    refine sum_congr (Finset.filter_congr fun b _ => by rw [hown b T]) fun b hb => ?_
    have hoT : ownerT b = T := (mem_filter.mp hb).2.2
    rw [hoT]
    exact sum_congr rfl fun z _ => by ring
  have htab : ∑ b with ¬ owner b = none, sel ζ (κ b) (q b) * ∑ z ∈ range (2 ^ κ b), rowEq ζ (κ b) z * leaf b z =
      ∑ b with owner b ≠ none, sel ζ (κ b) (q b) * blockKnown ζ (κ b) (ts b) +
        ∑ T ∈ Ts, ∑ z ∈ range (2 ^ τ T), rowEq ζ (τ T) z * (sideForm ζ κ q owner β ts T).eval (row T z) := by
    rw [sum_congr rfl hQ, sum_add_distrib, hforms]
  rw [htab]
  ring

/-- The totals `bus::verify_balance` derives, `totals[s] = framework + values[s]`, at the side's true leaf claim
`values[s] = Σ_x eq(ζ, x) L(x)`: each table's form summed over its rows, the framework part cancelling in
characteristic two. -/
theorem totals_eq (L : ℕ → E) (leaf : Fin m → ℕ → E) (τ : Table → ℕ) (row : Table → ℕ → ℕ → E)
    (Ts : Finset Table) (hκ : ∀ b, κ b ≤ n) (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b, ∀ z < 2 ^ κ b, L (2 ^ κ b * q b + z) = leaf b z)
    (hpad : ∀ x < 2 ^ n, (∀ b, x ∉ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)) → L x = 1)
    (hT : ∀ b T, owner b = some T → T ∈ Ts ∧ κ b = τ T ∧ ∀ z, leaf b z = blockLeaf β (ts b) (row T z) z) :
    framework ζ κ q owner ts leaf + ∑ x ∈ range (2 ^ n), rowEq ζ n x * L x =
      ∑ T ∈ Ts, ∑ z ∈ range (2 ^ τ T), rowEq ζ (τ T) z * (sideForm ζ κ q owner β ts T).eval (row T z) := by
  rw [side_decompose ζ κ q owner β ts L leaf τ row Ts hκ hin hdisj hleaf hpad hT, ← add_assoc, ← two_mul, two_E,
    zero_mul, zero_add]

/-- The same over a committed witness's owned tables at their heights: the totals are `formSums` at the side's forms,
the bus parts `ChecksGiveTable`'s table conjunct reads. -/
theorem totals_eq_formSums (w : Witness) (L : ℕ → E) (leaf : Fin m → ℕ → E) (hκ : ∀ b, κ b ≤ n)
    (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b, ∀ z < 2 ^ κ b, L (2 ^ κ b * q b + z) = leaf b z)
    (hpad : ∀ x < 2 ^ n, (∀ b, x ∉ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)) → L x = 1)
    (hT : ∀ b T, owner b = some T → T ∈ owned ∧ κ b = tauOf w T ∧
      ∀ z, leaf b z = blockLeaf β (ts b) (fun c => emb (w.cols T z c)) z) (i : Fin 2) :
    framework ζ κ q owner ts leaf + ∑ x ∈ range (2 ^ n), rowEq ζ n x * L x =
      formSums w ζ (fun _ T => sideForm ζ κ q owner β ts T) i :=
  totals_eq ζ κ q owner β ts L leaf (tauOf w) (fun T z c => emb (w.cols T z c)) owned hκ hin hdisj hleaf hpad hT

/-- Non-vacuity of the decomposition's premises: one `EMUL` block of two rows carrying `β + a_0`, the whole layer of a
one-variable side. -/
example (β : E) (w : Witness) (hw : tauOf w .emul = 1) (ζ : Fin 1 → E) :
    framework ζ (fun _ : Fin 1 => 1) (fun _ => 0) (fun _ => some .emul) (fun _ => [(1, .col 0)])
        (fun _ z => blockLeaf β [(1, .col 0)] (fun c => emb (w.cols .emul z c)) z) +
      ∑ x ∈ range (2 ^ 1), rowEq ζ 1 x * blockLeaf β [(1, .col 0)] (fun c => emb (w.cols .emul x c)) x =
    formSums w ζ (fun _ T => sideForm ζ (fun _ : Fin 1 => 1) (fun _ => 0) (fun _ => some .emul) β
      (fun _ => [(1, .col 0)]) T) 0 :=
  totals_eq_formSums ζ _ _ _ β _ w _ _ (fun _ => le_rfl) (fun _ => by norm_num)
    (fun b b' h => absurd (Subsingleton.elim b b') h) (fun _ z _ => by simp)
    (fun x hx hn => absurd (mem_Ico.mpr ⟨Nat.zero_le x, by simpa using hx⟩) (hn 0))
    (fun _ T h => by
      cases h
      exact ⟨by simp [owned], hw.symm, fun _ => rfl⟩) 0

/-! The table sumcheck's input claim from the leaf claims. -/

/-- `eq(ζ[..τ], z)` reads only `ζ`'s first `τ` coordinates: the bus point and its first `N` coordinates, the table
sumcheck's, agree on it. -/
theorem rowEq_restrict {μ N : ℕ} (ζ : Fin μ → E) (ζ' : Fin N → E) (hN : N ≤ μ)
    (h : ∀ j : Fin N, ζ' j = ζ ⟨j, lt_of_lt_of_le j.isLt hN⟩) {τ : ℕ} (hτ : τ ≤ N) (z : ℕ) :
    rowEq ζ' τ z = rowEq ζ τ z := by
  set g : ℕ → E := fun j => if hj : j < μ then (if j < τ then (if z.testBit j then ζ ⟨j, hj⟩ else 1 + ζ ⟨j, hj⟩) else 1)
    else 1
  have e1 : rowEq ζ τ z = ∏ j ∈ range μ, g j := by
    rw [← Fin.prod_univ_eq_prod_range g μ]
    simp only [rowEq, g, Fin.is_lt, dif_pos, Fin.eta]
  have e2 : rowEq ζ' τ z = ∏ j ∈ range N, g j := by
    rw [← Fin.prod_univ_eq_prod_range g N]
    simp only [rowEq, g, lt_of_lt_of_le (Fin.is_lt _) hN, dif_pos]
    refine prod_congr rfl fun j _ => ?_
    rw [h j]
  rw [e1, e2]
  refine prod_subset (fun j hj => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hj) hN)) fun j hj hn => ?_
  have : ¬ j < τ := fun hlt => hn (mem_range.mpr (lt_of_lt_of_le hlt hτ))
  simp [g, this]

/-- The bus forms' sums at the bus point are their sums at its first `N` coordinates where every owned table's `τ` is
at most `N`. -/
theorem formSums_restrict {μ N : ℕ} (w : Witness) (ζ : Fin μ → E) (ζ' : Fin N → E) (hN : N ≤ μ)
    (h : ∀ j : Fin N, ζ' j = ζ ⟨j, lt_of_lt_of_le j.isLt hN⟩) (htau : ∀ T ∈ owned, tauOf w T ≤ N)
    (forms : Fin 2 → Table → Quad) (i : Fin 2) : formSums w ζ' forms i = formSums w ζ forms i := by
  simp only [formSums]
  refine sum_congr rfl fun T hT => sum_congr rfl fun z _ => ?_
  rw [rowEq_restrict ζ ζ' hN h (htau T hT)]

/-- The table sumcheck's input claim from the leaf claims: where both sides' totals are their forms' sums at the bus
point (`totals_eq_formSums`, at true leaf claims), the table sumcheck runs `N ≤ μ` rounds over its first `N`
coordinates with every owned table's `τ` at most `N`, and no row breaks an identity, the totals' `σ_0 + ξ σ_1` is the
honest instance's sum at those forms. -/
theorem tableClaim_of_leaves {μ N : ℕ} (w : Witness) (ζ : Fin μ → E) (ζ' : Fin N → E) (hN : N ≤ μ)
    (h : ∀ j : Fin N, ζ' j = ζ ⟨j, lt_of_lt_of_le j.isLt hN⟩) (htau : ∀ T ∈ owned, tauOf w T ≤ N)
    (forms : Fin 2 → Table → Quad) (ξ : E) (tot : Fin 2 → E) (htot : ∀ i, tot i = formSums w ζ forms i)
    (hv : ¬ Viol w) : tot 0 + ξ * tot 1 = (tableInst N w ζ' forms ξ).sum := by
  rw [tableInst_sum w ζ' forms ξ htau, tableSum, htot 0, htot 1, formSums_restrict w ζ ζ' hN h htau,
    formSums_restrict w ζ ζ' hN h htau]
  have hc : ∀ j : Fin allIds.length, coef w ζ' allIds[(j : ℕ)] = 0 := fun j => by
    refine sum_eq_zero fun z hz => ?_
    by_cases he : allIds[(j : ℕ)].2.eval (w.cols allIds[(j : ℕ)].1 z) = 0
    · rw [he]
      simp [emb_zero]
    · exact absurd ⟨allIds[(j : ℕ)], List.getElem_mem j.isLt, z, mem_range.mp hz, he⟩ hv
  simp [hc]

end LeanVMCircuits.Rec.AirLink
