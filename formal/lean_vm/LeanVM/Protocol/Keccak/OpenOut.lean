/-
  LeanVM.Protocol.Keccak.OpenOut

  Opening the committed middle state: `keccakOpen` on the first claim's segment `0`, a
  sumcheck over the slot, and the column claim on `q_keccak` it leaves.
-/

module

public import LeanVM.Protocol.Keccak.Layers

/-!
# The committed outputs' opening

`committed` claims `eq(r_seg, 0)·Σ_ℓ eq(r_lane, ℓ)·mid_ℓ(inst)` (`OpenTrue`), the middle state's
lanes being the slots `25 + ℓ` of `q_keccak` at the steps' point `inst`. `keccakOpen` with
`first = 1, count = 1` (`open`, `crates/verifier/src/keccak.rs:269-278`) proves it by a degree-two
sumcheck over the six slot bits of

  `Σ_o W(o) · Q(o)`,  `W(o) = slotW … o 0` (the slot weights at slice `0`),
  `Q(o) = stepMle inst (q(· + 2^h·o))`,

ending at the slot point `ρ` on `W̃(ρ)·Q̃(ρ)`; the verifier computes `W̃(ρ)` (the fold's slice
`0`), reads `word` and checks `W̃(ρ)·word`. `Q̃(ρ)` is the column's multilinear extension at
`inst ++ ρ` (`col_split`), the column claim it leaves.

* `cube_plainFamily`: a sum over the cube of a summand of degree `d` in each coordinate is a
  plain sumcheck family of degree `d`;
* `openOutSpec`: the sumcheck as a specification, from doom of `committed = Fo q []` to doom of
  `value = W̃(ρ)·Q̃_q(ρ)`, with the verifier's `W̃(ρ)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

@[expose] public section

/-! ## Sums over the cube -/

/-- The sum over the remaining cube of `φ`, the first coordinates bound to `acc`. -/
noncomputable def cubeSum (φ : List E → E) (n : ℕ) (acc : List E) : E :=
  ∑ u ∈ range (2 ^ (n - acc.length)), φ (acc ++ bitsE u (n - acc.length))

theorem cube_plainFamily {β : Type} (φ : β → List E → E) {d : ℕ} (n : ℕ)
    (hφ : ∀ q pre post, PolyLE d fun x ↦ φ q (pre ++ x :: post)) :
    PlainFamily (fun q acc ↦ cubeSum (φ q) n acc) d n := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by omega
  refine ⟨?_, ?_⟩
  · have e : ∀ x, cubeSum (φ q) n (acc ++ [x]) =
        ∑ u ∈ range (2 ^ (n - (acc.length + 1))), φ q (acc ++ x :: bitsE u (n - (acc.length + 1))) := by
      intro x
      simp only [cubeSum, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    exact PolyLE.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      φ q (acc ++ x :: bitsE u (n - (acc.length + 1)))) (PolyLE.sum _ fun u _ ↦ hφ q acc _)
      fun x ↦ (e x).symm
  · simp only [cubeSum, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsE_two_mul, bitsE_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

theorem cubeSum_nil (φ : List E → E) (n : ℕ) :
    cubeSum φ n [] = ∑ u ∈ range (2 ^ n), φ (bitsE u n) := by
  simp [cubeSum]

theorem cubeSum_full (φ : List E → E) {n : ℕ} {acc : List E} (h : acc.length = n) :
    cubeSum φ n acc = φ acc := by
  rw [cubeSum, h, Nat.sub_self]
  simp [bitsE]

/-- A product of two multilinear extensions has degree two in each coordinate. -/
theorem polyLE_mle_mul (f g : ℕ → E) (N M : ℕ) (pre post : List E) :
    PolyLE 2 fun x ↦ (∑ o ∈ range N, eqAt (pre ++ x :: post) o * f o) *
      ∑ o ∈ range M, eqAt (pre ++ x :: post) o * g o :=
  PolyLE.mul (polyLE_mle pre post N f) (polyLE_mle pre post M g)

/-! ## The column at a point -/

/-- **The column's multilinear extension**, step bits low and slot bits high. -/
theorem col_split {h : ℕ} {a s : List E} (ha : a.length = h) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ (h + s.length)), eqAt (a ++ s) n * F n =
      ∑ o ∈ range (2 ^ s.length), eqAt s o * ∑ x ∈ range (2 ^ h), eqAt a x * F (x + 2 ^ h * o) := by
  rw [pow_add, mul_comm, sum_range_mul]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hd : (2 ^ h * o + x) / 2 ^ h = o := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx', zero_add]
  have hmod : (2 ^ h * o + x) % 2 ^ h = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  rw [eqAt_append, ha, hd, eqAt_mod a, ha, hmod, show 2 ^ h * o + x = x + 2 ^ h * o by ring]
  ring

/-! ## The committed opening -/

variable (h : ℕ)

/-- The slot weights at slice `0`, extended over the slot bits. -/
noncomputable def Wo (segment lanesPt pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * slotW (eqKernel segment) (firstWeights lanesPt) 1 1 o 0

/-- The column's slots at the steps' point `inst`, extended over the slot bits. -/
noncomputable def Qo (col : ℕ → K) (inst pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * stepMle h inst (fun x ↦ col (x + 2 ^ h * o))

/-- The committed opening's sumcheck family. -/
noncomputable def Fo (col : ℕ → K) (inst segment lanesPt : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ Wo segment lanesPt pt * Qo h col inst pt) 6 acc

theorem Fo_plainFamily {β : Type} (qk : β → ℕ → K) (inst segment lanesPt : List E) :
    PlainFamily (fun q acc ↦ Fo h (qk q) inst segment lanesPt acc) 2 6 :=
  cube_plainFamily (fun q pt ↦ Wo segment lanesPt pt * Qo h (qk q) inst pt) 6
    fun _ pre post ↦ polyLE_mle_mul _ _ _ _ pre post

theorem slotW_out {segment lanesPt : List E} (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (o : ℕ) : slotW (eqKernel segment) (firstWeights lanesPt) 1 1 o 0 =
      if 25 ≤ o ∧ o < 50 then eqAt segment 0 * eqAt lanesPt (o - 25) else 0 := by
  rw [slotW]
  by_cases ho : 25 ≤ o ∧ o < 50
  · rw [ite_eq_left (show 25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64 by omega), ite_eq_left ho]
    have e1 : o / 25 - 1 = 0 := by omega
    have e2 : 64 * (o % 25) + 0 < 1600 := by omega
    rw [e1, eqKernel_getD, hs, ite_eq_left (by norm_num), firstWeights,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [keccakBits] using e2)]
    simp only [Option.map_some, Option.getD_some]
    have e3 : (64 * (o % 25) + 0) / 64 = o - 25 := by omega
    have e4 : (64 * (o % 25) + 0) % 64 = 0 := by omega
    rw [e3, e4, eqKernel_getD, hl, ite_eq_left (by omega), pow_zero, eOfNat_one, mul_one]
  · rw [ite_eq_right (show ¬ (25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64) by omega), ite_eq_right ho]

/-- Before the slot challenges, the family is the middle-state value `OpenTrue` speaks of. -/
theorem Fo_nil (col : ℕ → K) (inst : List E) {segment lanesPt : List E}
    (hs : segment.length = 1) (hl : lanesPt.length = 5) :
    Fo h col inst segment lanesPt [] =
      eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l := by
  rw [Fo, cubeSum_nil]
  have hu : ∀ u ∈ range (2 ^ 6), Wo segment lanesPt (bitsE u 6) * Qo h col inst (bitsE u 6) =
      slotW (eqKernel segment) (firstWeights lanesPt) 1 1 u 0 *
        stepMle h inst (fun x ↦ col (x + 2 ^ h * u)) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [Wo, Qo, sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']
  rw [Finset.sum_congr rfl hu, show 2 ^ 6 = 25 + (25 + 14) from rfl, Finset.sum_range_add,
    Finset.sum_range_add, Finset.mul_sum]
  have h1 : ∑ u ∈ range 25, slotW (eqKernel segment) (firstWeights lanesPt) 1 1 u 0 *
      stepMle h inst (fun x ↦ col (x + 2 ^ h * u)) = 0 :=
    Finset.sum_eq_zero fun u hu ↦ by
      rw [slotW_out hs hl, ite_eq_right (by have := Finset.mem_range.1 hu; omega), zero_mul]
  have h3 : ∑ u ∈ range 14, slotW (eqKernel segment) (firstWeights lanesPt) 1 1 (25 + (25 + u)) 0 *
      stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + (25 + u)))) = 0 :=
    Finset.sum_eq_zero fun u _ ↦ by rw [slotW_out hs hl, ite_eq_right (by omega), zero_mul]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [slotW_out hs hl, ite_eq_left (by omega), show 25 + l - 25 = l by omega, midMle]
  ring

theorem headD_eq_getD (r : List E) : r.headD 0 = r.getD 0 0 := by
  cases r <;> rfl

/-- **The verifier's slot weight** at slice `0` after the fold is `W̃(ρ)`. -/
theorem fold_out {P : ℕ} {inst segment lanesPt output : List E} (hi : inst.length = P + 4)
    (committed : E) {slot : List E} (hslot : slot.length = 6) :
    ((foldAll slot (keccakSlotWeights (P + 4) (firstClaim inst segment lanesPt output committed)
      1 1)).headD []).headD 0 = Wo segment lanesPt slot := by
  have hrows := slotWeights_length (P + 4) (firstClaim inst segment lanesPt output committed) 1 1
    (by norm_num)
  obtain ⟨-, -, h3⟩ := foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 1 1 (by norm_num) (by omega)
  rw [headD_eq_getD, h3 0 (by norm_num), Wo, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeights_getD _ _ 1 1 (by norm_num) (Finset.mem_range.1 ho), firstClaim_point,
    firstClaim_weights, show P + 4 - 4 = P by omega,
    List.drop_left' (by simp [hi])]

end
end LeanVM.Protocol.KeccakGkr
