/-
  LeanVM.Guest.B1.KeccakGkr.Flips

  A later claim's weights where `ι` can flip (lane `0`, positions `2^i - 1`): through `θ`'s
  transpose from its lane and slice tables (`laterWeights_low`), the slice table split at its top
  coordinate (`slice_weight`), and the layer's block that computes them (`lflipT_holds`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FormT

/-!
# The flips

* `laterWeights_low`: a later claim's weight at `2^i - 1` of lane `0` is the sum over
  `flipOffs i` of the lane weight times the slice weight;
* `eqAt_six`: the slice weight `eqAt a₆ z` is `eqAt a₅ (z % 32)` times the top coordinate's
  factor (`slice_weight`, G:2840-2846);
* `lflipT_holds`: the block `lflipT` (G:2805-2811) sums those products.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem sum_flatMap' {α : Type} (l : List α) (g : α → List E) :
    (l.flatMap g).sum = (l.map fun a ↦ (g a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A sum over `flipOffs`. -/
theorem flipOffs_sum (i : ℕ) (F : ℕ × ℕ → E) :
    ((flipOffs i).map F).sum = F (keccakPi 0, (2 ^ i - 1 + keccakRho.getD 0 0) % 64) +
      ∑ y ∈ range 5, (F (keccakPi (1 + 5 * y), (2 ^ i - 1 + keccakRho.getD (1 + 5 * y) 0) % 64) +
        F (keccakPi (4 + 5 * y), (2 ^ i + keccakRho.getD (4 + 5 * y) 0) % 64)) := by
  simp only [flipOffs, List.map_cons, List.sum_cons, List.map_flatMap]
  rw [← listSum_range]
  congr 1
  rw [sum_flatMap']
  simp only [List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **A later claim's weight at `2^i - 1`** (lane `0`): `θ`'s transpose through `ρ`, `π` on the
lane and slice tables, as `flipOffs` lists them. -/
theorem laterWeights_low (lanes a6 : List E) (ha : a6.length = 6) {i : ℕ} (hi : i < 7) :
    (laterWeights lanes (eqKernel a6)).getD (2 ^ i - 1) 0 =
      ((flipOffs i).map fun o ↦ lanes.getD o.1 0 * (eqKernel a6).getD o.2 0).sum := by
  have hz : 2 ^ i - 1 < 64 := by
    have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have hg := gOf_later lanes a6 ha (l := 0) (by omega) hz
  simp only [Nat.mul_zero, zero_add] at hg
  rw [laterWeights, keccakLinearTranspose_getD _ (by omega), thetaT,
    show (2 ^ i - 1) / 64 = 0 from Nat.div_eq_of_lt hz,
    show (2 ^ i - 1) % 64 = 2 ^ i - 1 from Nat.mod_eq_of_lt hz, hg,
    colL_later lanes a6 ha (by omega) hz, colL_later lanes a6 ha (by omega) (by omega),
    flipOffs_sum]
  have he : ∀ k, (eqKernel a6).getD (k % 64) 0 = eqAt a6 (k % 64) := by
    intro k
    rw [eqKernel_getD, ha]
    simp [Nat.mod_lt k (show 0 < 64 by norm_num)]
  have hs : (2 ^ i - 1 + 1) % 64 = 2 ^ i % 64 := by rw [Nat.sub_add_cancel h1]
  simp only [he, kLane, kRho]
  rw [add_assoc, ← Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun y _ ↦ ?_)
  simp only [show (0 % 5 + 1) % 5 = 1 from rfl, show (0 % 5 + 4) % 5 = 4 from rfl]
  rw [hs, Nat.mod_add_mod]

theorem flipOffs_length (i : ℕ) : (flipOffs i).length = 11 := by
  simp [flipOffs, List.length_flatMap]

theorem flipOffs_lt (i : ℕ) : ∀ o ∈ flipOffs i, o.1 < 25 ∧ o.2 < 64 := by
  intro o ho
  simp only [flipOffs, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at ho
  rcases ho with rfl | ⟨y, hy, rfl | rfl⟩
  · exact ⟨keccakPi_lt 0 (by norm_num), Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨keccakPi_lt _ (by omega), Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨keccakPi_lt _ (by omega), Nat.mod_lt _ (by norm_num)⟩

/-- **The slice weight split at the top coordinate** (`slice_weight`, G:2840-2846). -/
theorem eqAt_six (a6 : List E) (ha : a6.length = 6) {z : ℕ} (hz : z < 64) :
    eqAt a6 z = eqAt (a6.take 5) (z % 32) *
      (if z / 32 = 1 then a6.getD 5 0 else 1 + a6.getD 5 0) := by
  have hs : a6 = a6.take 5 ++ [a6.getD 5 0] := by
    apply List.ext_getElem (by simp [ha])
    intro k h1 h2
    rcases Nat.lt_or_ge k 5 with hk | hk
    · rw [List.getElem_append_left (by simp [ha]; omega), List.getElem_take]
    · rw [List.getElem_append_right (by simp [ha]; omega)]
      have : k = 5 := by simp [ha] at h1; omega
      subst this
      simp [List.getElem?_eq_getElem (show 5 < a6.length by omega)]
  conv_lhs => rw [hs]
  rw [eqAt_append, eqAt_mod (a6.take 5) z, eqAt_cons, eqAt_nil, mul_one]
  simp only [List.length_take, ha, show min 5 6 = 5 from rfl]
  have h32 : z / 2 ^ 5 % 2 = z / 32 := by
    rw [show (2 : ℕ) ^ 5 = 32 from rfl]; omega
  rw [h32, show (2 : ℕ) ^ 5 = 32 from rfl]

/-- **A flip's block**: over `flipOffs i`, the lane weight read at `lp` times the slice weight
`slices[z % 32]·top(z)`, summed into the value `b + 42`. -/
theorem lflipT_holds {lp : V} {sl : ℕ → ℕ} {top top1 i b : ℕ} {lanes : List E}
    (hl : lanes.length = 25) (hlp : ReadsAt rd (σ lp) lanes) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lflipT lp sl top top1 i b) next kret) :
    σ (.n (b + 42)) = ((flipOffs i).map fun o ↦
      lanes.getD o.1 0 * (σ (.n (sl (o.2 % 32))) * σ (.n (topOf top top1 o.2)))).sum ∧ next := by
  have hlt := flipOffs_lt i
  have hlen := flipOffs_length i
  obtain ⟨o, os, hos⟩ : ∃ o os, flipOffs i = o :: os := by
    rcases h' : flipOffs i with _ | ⟨o, os⟩
    · rw [h'] at hlen; simp at hlen
    · exact ⟨o, os, rfl⟩
  have hosl : os.length = 10 := by rw [hos] at hlen; simpa using hlen
  have hld : ∀ p ∈ flipOffs i, ∀ v, LoadHolds rd (σ lp) p.1 v → v = lanes.getD p.1 0 := by
    intro p hp v hv
    have := hlp p.1 (by rw [hl]; exact (hlt p hp).1)
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact (hlt p hp).1)]
    exact loadHolds_unique hv this
  rw [lflipT, hos] at h
  simp only at h
  rw [holdsList_append, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, m0, p0, hall, hn⟩ := h
  have T : ∀ (q : ℕ × ℕ), q ∈ flipOffs i → ∀ v w x : ℕ, LoadHolds rd (σ lp) q.1 (σ (.n v)) →
      σ (.n w) = σ (.n (sl (q.2 % 32))) * σ (.n (topOf top top1 q.2)) →
      σ (.n x) = σ (.n v) * σ (.n w) →
      σ (.n x) = lanes.getD q.1 0 * (σ (.n (sl (q.2 % 32))) * σ (.n (topOf top top1 q.2)))  := by
    intro q hq v w x hv hw hx
    rw [hx, hw, hld q hq _ hv]
  have hmem0 : o ∈ flipOffs i := by rw [hos]; exact List.mem_cons_self ..
  have hmem : ∀ k < 10, os.getD k default ∈ flipOffs i := by
    intro k hk
    rw [hos, List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_cons_of_mem _ (List.getElem_mem _)
  set F : ℕ × ℕ → E := fun q ↦
    lanes.getD q.1 0 * (σ (.n (sl (q.2 % 32))) * σ (.n (topOf top top1 q.2))) with hF
  have acc : ∀ k ≤ 10, σ (.n (b + 2 + 4 * k)) = F o + ((os.take k).map F).sum := by
    intro k hk
    induction k with
    | zero => simpa [F] using T o hmem0 b (b + 1) (b + 2) l0 m0 p0
    | succ k ih =>
      have hk' := hall k (by omega)
      obtain ⟨lk, mk, pk, ak, -⟩ := hk'
      have tk := T _ (hmem k (by omega)) _ _ _ lk mk pk
      rw [show b + 2 + 4 * (k + 1) = b + 6 + 4 * k by ring, ak, ih (by omega), tk,
        List.take_add_one, List.map_append, List.sum_append, add_assoc]
      congr 2
      rw [List.getElem?_eq_getElem (by omega)]
      simp [F, List.getElem?_eq_getElem (show k < os.length by omega)]
  refine ⟨?_, hn⟩
  have := acc 10 le_rfl
  rw [show b + 2 + 4 * 10 = b + 42 by ring, List.take_of_length_le (by simp [hosl])] at this
  rw [this, hos, List.map_cons, List.sum_cons]

/-- **A later claim's flip**: its weight at `2^i - 1` of lane `0` is the sum over `flipOffs i` of
the lane weight times `eqAt` of the first five slice coordinates and the top one's factor. -/
theorem laterWeights_flip (lanes a6 : List E) (ha : a6.length = 6) {i : ℕ} (hi : i < 7) :
    (laterWeights lanes (eqKernel a6)).getD (2 ^ i - 1) 0 =
      ((flipOffs i).map fun o ↦ lanes.getD o.1 0 * (eqAt (a6.take 5) (o.2 % 32) *
        (if o.2 / 32 = 1 then a6.getD 5 0 else 1 + a6.getD 5 0))).sum := by
  rw [laterWeights_low lanes a6 ha hi]
  refine congrArg List.sum (List.map_congr_left fun o ho ↦ ?_)
  have h64 := (flipOffs_lt i o ho).2
  have h64' : o.2 < 2 ^ 6 := by norm_num; omega
  rw [eqKernel_getD, ha, eqAt_six a6 ha h64]
  simp only [h64', ↓reduceIte]

end
end LeanVM.Guest.B1.VerifySub
