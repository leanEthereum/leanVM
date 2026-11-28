module

public import NativeVm.Math.Keccak.Pure

/-!
# Phase 6's model values, entry by entry

The arrays `Model.verifyKeccak` builds, each as a closed form of its entries' values (`EW.toE`), the
form the code tabulates them in: `eqKernel` (`eqKernel_getD`), `keccakInstanceWeights`
(`instanceWeights_getD`), the layer's `projected` and `iota` (`projected_sum`, `iota_sum`),
`keccakLinearTranspose` (`linearTranspose_getD`), `keccakSlotWeights` (`slotWeights_getD`) and the
fold of `keccakOpen`'s rows (`openRows_getD`). The constant tables the code holds are literals
(`keccakRCLit`, the lane tables), equal to the statement's.
-/

@[expose] public section

namespace NativeVm.Math.Keccak

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol Finset

/-! ## `eqKernel` -/

/-- `eqKernel`'s fold over a list of coordinates: its size and its entries. -/
theorem eqKernel_list (L : List EW) :
    (L.foldl (fun (out : Array EW) r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]).size =
        2 ^ L.length ∧
      ∀ i < 2 ^ L.length,
        ((L.foldl (fun (out : Array EW) r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]).getD i
          0).toE =
          ∏ k ∈ range L.length,
            (if i.testBit k then (L.getD k 0).toE else 1 + (L.getD k 0).toE) := by
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, fun i hi ↦ ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    simp
  | append_singleton L r ih =>
    obtain ⟨hs, hv⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    generalize L.foldl (fun (out : Array EW) r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1] =
      out at hs hv
    refine ⟨by rw [Array.size_append, Array.size_map, Array.size_map, hs, Nat.pow_succ]; omega,
      fun i hi ↦ ?_⟩
    have hL : ∀ k ∈ range L.length, (if i.testBit k then ((L ++ [r]).getD k 0).toE
        else 1 + ((L ++ [r]).getD k 0).toE) =
        (if i.testBit k then (L.getD k 0).toE else 1 + (L.getD k 0).toE) := fun k hk ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (mem_range.1 hk)]
    have hr : (L ++ [r]).getD L.length 0 = r := by simp
    rw [prod_range_succ, prod_congr rfl hL, hr, Array.getD_eq_getD_getElem?, Array.getElem?_append,
      Array.size_map, hs]
    by_cases h : i < 2 ^ L.length
    · have ho : i < out.size := hs ▸ h
      rw [← hv i h, Nat.testBit_lt_two_pow h]
      simp [h, Array.getElem?_eq_getElem ho, Array.getD_eq_getD_getElem?]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ L.length + j := ⟨i - 2 ^ L.length, by omega⟩
      have hj : j < 2 ^ L.length := by rw [Nat.pow_succ] at hi; omega
      have ho : j < out.size := hs ▸ hj
      have hb : ∀ k ∈ range L.length, (2 ^ L.length + j).testBit k = j.testBit k := fun k hk ↦
        Nat.testBit_two_pow_add_gt (mem_range.1 hk) j
      rw [prod_congr rfl fun k hk ↦ by rw [hb k hk], ← hv j hj, Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hj]
      simp [h, Array.getElem?_eq_getElem ho, Array.getD_eq_getD_getElem?]

theorem eqKernel_size (p : Array EW) : (eqKernel p).size = 2 ^ p.size := by
  rw [eqKernel, ← Array.foldl_toList, (eqKernel_list p.toList).1, Array.length_toList]

/-- Entry `i` of `eqKernel p`: coordinate `k` contributes `p_k` where bit `k` of `i` is set,
`1 + p_k` where it is clear. -/
theorem eqKernel_getD (p : Array EW) {i : Nat} (hi : i < 2 ^ p.size) :
    ((eqKernel p).getD i 0).toE =
      ∏ k ∈ range p.size, (if i.testBit k then (p.getD k 0).toE else 1 + (p.getD k 0).toE) := by
  rw [← Array.length_toList] at hi
  rw [eqKernel, ← Array.foldl_toList, (eqKernel_list p.toList).2 i hi, Array.length_toList]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem eqKernel_getD_out (p : Array EW) {i : Nat} (hi : 2 ^ p.size ≤ i) : (eqKernel p).getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [eqKernel_size]; exact hi),
    Option.getD_none]

/-! ## The instance weights -/

/-- Entry `b` of `powersFrom acc base n`. -/
theorem powersFrom_getD (acc base : E) :
    ∀ (n b : Nat), b < n → (Verifier.powersFrom acc base n).getD b 0 = acc * base ^ b
  | _ + 1, 0, _ => by simp [Verifier.powersFrom]
  | n + 1, b + 1, h => by
    rw [Verifier.powersFrom, List.getD_cons_succ, powersFrom_getD _ _ n b (by omega), pow_succ',
      mul_assoc]

theorem instanceWeights_size (s : EW) : (keccakInstanceWeights s).size = 16 := by
  rw [keccakInstanceWeights, Array.size_map, NativeVm.Equiv.rmfeEmbedW_eq]
  rfl

theorem instanceWeights_getD (s : EW) {e : Nat} (he : e < 16) :
    ((keccakInstanceWeights s).getD e 0).toE =
      ∑ b ∈ range 24, if testBitW (NativeVm.Equiv.rmfeEmbedWLit.getD e 0) b then s.toE ^ b else 0 := by
  have he' : e < NativeVm.Equiv.rmfeEmbedWLit.size := he
  rw [keccakInstanceWeights, NativeVm.Equiv.rmfeEmbedW_eq, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_eq_getElem he', Option.map_some, Option.getD_some,
    toE_sumE_filterMap, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he',
    Option.getD_some]
  refine sum_congr rfl fun b hb ↦ ?_
  rw [NativeVm.Equiv.Keccak.toE_getD, NativeVm.Equiv.toList_map_powers, Verifier.powers,
    powersFrom_getD _ _ Verifier.embedBits _ (mem_range.1 hb), one_mul]

/-! ## The layer's sums -/

/-- A masked sum over a zip of lists, by index. -/
theorem sumE_zip_filterMap (p : UInt64 → Bool) : ∀ (a : List EW) (b : List UInt64),
    Verifier.sumE (((a.zip b).filterMap fun x ↦ if p x.2 then some x.1 else none).map EW.toE) =
      ∑ i ∈ range (min a.length b.length), if p (b.getD i 0) then (a.getD i 0).toE else 0
  | [], _ => by simp [Verifier.sumE]
  | _ :: _, [] => by simp [Verifier.sumE]
  | x :: a, y :: b => by
    have ih := sumE_zip_filterMap p a b
    rw [Verifier.sumE, ← List.sum_eq_foldl] at ih ⊢
    rw [List.length_cons, List.length_cons, Nat.succ_min_succ, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← ih, List.zip_cons_cons, List.filterMap_cons]
    by_cases h : p y <;> simp [h, add_comm]

/-- An entry of a map over a range. -/
theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (d : α) {c : Nat} (hc : c < n) :
    ((Array.range n).map f).getD c d = f c := by
  simp [Array.getD_eq_getD_getElem?, hc]

/-- A masked sum over a zip of arrays, by index. -/
theorem toE_sumE_zip (p : UInt64 → Bool) (a : Array EW) (b : Array UInt64) :
    (sumE ((a.zip b).filterMap fun x ↦ if p x.2 then some x.1 else none)).toE =
      ∑ i ∈ range (min a.size b.size), if p (b.getD i 0) then (a.getD i 0).toE else 0 := by
  rw [NativeVm.Equiv.toE_sumE, Array.toList_filterMap, Array.toList_zip, sumE_zip_filterMap,
    Array.length_toList, Array.length_toList]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- The layer's `projected`, as `NativeVm.Equiv.Keccak.projected_eq` states it, regrouped by
instance. -/
theorem projected_sum (mu product : Array EW) :
    (sumE ((Array.range Verifier.productBits).map fun c ↦
      sumE ((mu.zip rmfeProjectW).filterMap fun x ↦
        if testBitW x.2 c then some x.1 else none) * product.getD c 0)).toE =
    ∑ i ∈ range (min mu.size 16), (mu.getD i 0).toE *
      ∑ c ∈ range 47, if testBitW (NativeVm.Equiv.rmfeProjectWLit.getD i 0) c then
        (product.getD c 0).toE else 0 := by
  rw [toE_sumE_range, Array.size_map, Array.size_range]
  rw [sum_congr rfl fun c hc ↦ by
    rw [getD_map_range _ _ _ (mem_range.1 hc), Equiv.EW.toE_mul,
      toE_sumE_zip (fun w ↦ testBitW w c),
      NativeVm.Equiv.rmfeProjectW_eq]]
  simp only [sum_mul, mul_sum, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun c _ ↦ ?_
  rfl

/-- `KECCAK_RC` as a literal array. -/
def keccakRCLit : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

theorem keccakRCW_eq : keccakRCW = keccakRCLit := by
  rfl

/-- The layer's `iota`, as the model states it. -/
theorem iota_sum (step : Nat) (segments weights : Array EW) :
    (sumE ((Array.range Verifier.keccakSegments).map fun segment ↦
      segments.getD segment 0 * sumE ((Array.range 64).filterMap fun z ↦
        if testBitW (keccakRCW.getD (Verifier.keccakDepth * (segment + 1) - step - 1) 0) z then
          some (weights.getD z 0) else none))).toE =
    ∑ seg ∈ range 2, (segments.getD seg 0).toE *
      ∑ z ∈ range 64, if testBitW (keccakRCLit.getD (12 * (seg + 1) - step - 1) 0) z then
        (weights.getD z 0).toE else 0 := by
  rw [toE_sumE_range, Array.size_map, Array.size_range]
  refine sum_congr rfl fun seg hs ↦ ?_
  rw [getD_map_range Verifier.keccakSegments _ _ (mem_range.1 hs), Equiv.EW.toE_mul,
    toE_sumE_filterMap, keccakRCW_eq]
  rfl

/-! ## The linear map -/

/-- `g` of `linear_transpose`: the weight on position `z` of lane `lane` of θ's output. -/
def ltG (w : Array EW) (lane z : Nat) : E :=
  (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0).toE

/-- A column of `g`. -/
def ltC (w : Array EW) (x z : Nat) : E := ∑ y ∈ range 5, ltG w (x + 5 * y) z

/-- A block array over two ranges, as a list. -/
theorem flatMap_range_toList {α : Type} (m : Nat) (f : Nat → Nat → α) (n : Nat) :
    ((Array.range n).flatMap fun x ↦ (Array.range m).map fun z ↦ f x z).toList =
      (List.range n).flatMap fun x ↦ (List.range m).map fun z ↦ f x z := by
  simp only [Array.toList_flatMap, Array.toList_map, Array.toList_range]

/-- A block list over two ranges: its length and its entry `m * x + z`. -/
theorem flatMap_range_list {α : Type} (m : Nat) (f : Nat → Nat → α) (n : Nat) :
    ((List.range n).flatMap fun x ↦ (List.range m).map fun z ↦ f x z).length = n * m ∧
      ∀ x < n, ∀ z < m,
        ((List.range n).flatMap fun x ↦ (List.range m).map fun z ↦ f x z)[m * x + z]? =
          some (f x z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hv⟩ := ih
    rw [List.range_succ, List.flatMap_append, List.length_append, hl, List.flatMap_singleton,
      List.length_map, List.length_range, Nat.succ_mul]
    refine ⟨rfl, fun x hx z hz ↦ ?_⟩
    rw [List.getElem?_append, hl]
    by_cases h : x < n
    · have : m * x + z < n * m := by
        have := Nat.mul_le_mul_left m (show x + 1 ≤ n by omega)
        rw [Nat.mul_succ] at this; rw [Nat.mul_comm n]; omega
      simp only [this, ↓reduceIte, hv x h z hz]
    · obtain rfl : x = n := by omega
      rw [Nat.mul_comm m x]
      simp only [show ¬ x * m + z < x * m by omega, ↓reduceIte, Nat.add_sub_cancel_left,
        List.getElem?_map, List.getElem?_range hz, Option.map_some]

theorem flatMap_range_size {α : Type} (n m : Nat) (f : Nat → Nat → α) :
    ((Array.range n).flatMap fun x ↦ (Array.range m).map fun z ↦ f x z).size = n * m := by
  rw [← Array.length_toList, flatMap_range_toList, (flatMap_range_list m f n).1]

theorem flatMap_range_getD {α : Type} (n m : Nat) (f : Nat → Nat → α) (d : α) {x z : Nat}
    (hx : x < n) (hz : z < m) :
    ((Array.range n).flatMap fun x ↦ (Array.range m).map fun z ↦ f x z).getD (m * x + z) d =
      f x z := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, flatMap_range_toList,
    (flatMap_range_list m f n).2 x hx z hz, Option.getD_some]

/-- The inner loop of `g`: lane `lane`'s block, positions `z < J`. -/
theorem setBlock {α : Type} (lane : Nat) (v : Nat → α) : ∀ (J : Nat) (g : Array α),
    ((List.range J).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (v z)) g).size = g.size ∧
      ∀ idx, ((List.range J).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (v z)) g)[idx]? =
        if 64 * lane ≤ idx ∧ idx < 64 * lane + J ∧ idx < g.size then some (v (idx - 64 * lane))
        else g[idx]?
  | 0, g => ⟨rfl, fun idx ↦ by
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    split <;> [omega; rfl]⟩
  | J + 1, g => by
    obtain ⟨hs, hv⟩ := setBlock lane v J g
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.size_setIfInBounds, hs]
    refine ⟨rfl, fun idx ↦ ?_⟩
    rw [Array.getElem?_setIfInBounds, hv, hs]
    by_cases h : 64 * lane + J = idx
    · subst h
      by_cases h' : 64 * lane + J < g.size
      · simp [h']
      · simp [h']
    · simp only [h, ↓reduceIte]
      congr 1
      apply propext
      omega

/-- `g` of `linear_transpose`, after the lanes `lane < n`. -/
theorem setLanes {α : Type} (v : Nat → Nat → α) : ∀ (n : Nat) (g : Array α),
    ((List.range n).foldl (fun g lane ↦ (List.range 64).foldl
      (fun g z ↦ g.setIfInBounds (64 * lane + z) (v lane z)) g) g).size = g.size ∧
      ∀ idx, ((List.range n).foldl (fun g lane ↦ (List.range 64).foldl
          (fun g z ↦ g.setIfInBounds (64 * lane + z) (v lane z)) g) g)[idx]? =
        if idx < 64 * n ∧ idx < g.size then some (v (idx / 64) (idx % 64)) else g[idx]?
  | 0, g => ⟨rfl, fun idx ↦ by
    simp only [List.range_zero, List.foldl_nil, Nat.mul_zero]
    split <;> [omega; rfl]⟩
  | n + 1, g => by
    obtain ⟨hs, hv⟩ := setLanes v n g
    rw [List.range_succ (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hv'⟩ := setBlock n (v n) 64
      ((List.range n).foldl (fun g lane ↦ (List.range 64).foldl
        (fun g z ↦ g.setIfInBounds (64 * lane + z) (v lane z)) g) g)
    rw [hs', hs]
    refine ⟨rfl, fun idx ↦ ?_⟩
    rw [hv', hv, hs]
    by_cases h : 64 * n ≤ idx ∧ idx < 64 * n + 64 ∧ idx < g.size
    · have h1 : idx / 64 = n := by omega
      have h2 : idx % 64 = idx - 64 * n := by omega
      simp only [h, show idx < 64 * (n + 1) ∧ idx < g.size by omega, and_self, ↓reduceIte, h1, h2]
    · simp only [h, ↓reduceIte]
      split_ifs <;> first | rfl | omega

theorem linearTranspose_size (w : Array EW) : (keccakLinearTranspose w).size = 1600 := by
  rw [keccakLinearTranspose]
  exact flatMap_range_size 25 64 _

theorem linearTranspose_getD (w : Array EW) {lane z : Nat} (hl : lane < 25) (hz : z < 64) :
    ((keccakLinearTranspose w).getD (64 * lane + z) 0).toE =
      ltG w lane z + ltC w ((lane % 5 + 1) % 5) z + ltC w ((lane % 5 + 4) % 5) ((z + 1) % 64) := by
  rw [keccakLinearTranspose]
  generalize hg : (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0)) g)
    (Array.replicate Verifier.keccakBits 0) = g
  have hgv : ∀ l < 25, ∀ x < 64, (g.getD (64 * l + x) 0).toE = ltG w l x := fun l hl x hx ↦ by
    obtain ⟨-, hv⟩ := setLanes (fun lane z ↦
      w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0) 25
      (Array.replicate Verifier.keccakBits 0)
    have h1 : (64 * l + x) / 64 = l := by omega
    have h2 : (64 * l + x) % 64 = x := by omega
    have hin : 64 * l + x < 64 * 25 ∧
        64 * l + x < (Array.replicate Verifier.keccakBits (0 : EW)).size := by
      rw [Array.size_replicate, show Verifier.keccakBits = 1600 from rfl]; omega
    rw [← hg, Array.getD_eq_getD_getElem?, hv]
    simp only [hin, and_self, ↓reduceIte, Option.getD_some]
    rw [h1, h2, ltG, NativeVm.Equiv.Keccak.keccakRhoW_getD]
  have hcv : ∀ c < 5, ∀ x < 64,
      (((Array.range 5).flatMap fun c ↦ (Array.range 64).map fun x ↦
        sumE ((Array.range 5).map fun y ↦ g.getD (64 * (c + 5 * y) + x) 0)).getD (64 * c + x)
          0).toE = ltC w c x := fun c hc x hx ↦ by
    rw [flatMap_range_getD 5 64 _ _ hc hx, toE_sumE_range, Array.size_map, Array.size_range, ltC]
    refine sum_congr rfl fun y hy ↦ ?_
    rw [getD_map_range _ _ _ (mem_range.1 hy), hgv _ (by have := mem_range.1 hy; omega) x hx]
  rw [flatMap_range_getD 25 64 _ _ hl hz, Equiv.EW.toE_add, Equiv.EW.toE_add, hgv lane hl z hz,
    hcv _ (by omega) z hz, hcv _ (by omega) _ (Nat.mod_lt _ (by decide))]

/-! ## The openings -/

/-- The weight `keccakSlotWeights` puts on slot `r`, position `z`. -/
def slotRow (logSteps : Nat) (claim : KeccakClaimW) (first count r z : Nat) : EW :=
  if 25 * first ≤ r ∧ r < 25 * (first + count) then
    (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)).getD (r / 25 - first) 0 *
      claim.weights.getD (64 * (r % 25) + z) 0
  else 0

/-- A write into one row keeps every row's size. -/
theorem modifySet_size (rows : Array (Array EW)) (R Z : Nat) (v : EW) (r : Nat) :
    ((rows.modify R fun row ↦ row.setIfInBounds Z v).getD r #[]).size =
      (rows.getD r #[]).size := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · cases rows[r]? <;> simp
  · rfl

/-- A write into one row, entry by entry. -/
theorem modifySet_getD (rows : Array (Array EW)) (R Z : Nat) (v : EW) (r z : Nat) :
    ((rows.modify R fun row ↦ row.setIfInBounds Z v).getD r #[]).getD z 0 =
      if R = r ∧ Z = z ∧ z < (rows.getD r #[]).size then v else (rows.getD r #[]).getD z 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hR : R = r
  · cases rows[r]? with
    | none => simp
    | some row =>
      simp only [hR, ↓reduceIte, Option.map_some, Option.getD_some, Array.getElem?_setIfInBounds,
        true_and]
      by_cases hZ : Z = z
      · by_cases hz : z < row.size <;> simp [hZ, hz]
      · simp [hZ]
  · simp [hR]

/-- The inner loop of `keccakSlotWeights` keeps every row's size. -/
theorem slotInner_size (B : Nat) (v : Nat → EW) : ∀ (J : Nat) (rows : Array (Array EW)),
    ((List.range J).foldl (fun rows j ↦
      rows.modify (B + j / 64) fun row ↦ row.setIfInBounds (j % 64) (v j)) rows).size =
        rows.size ∧
    ∀ r, (((List.range J).foldl (fun rows j ↦
      rows.modify (B + j / 64) fun row ↦ row.setIfInBounds (j % 64) (v j)) rows).getD r #[]).size =
        (rows.getD r #[]).size
  | 0, _ => ⟨rfl, fun _ ↦ rfl⟩
  | J + 1, rows => by
    obtain ⟨hs, hr⟩ := slotInner_size B v J rows
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_modify, hs]
    exact ⟨rfl, fun r ↦ by rw [modifySet_size, hr]⟩

/-- The inner loop of `keccakSlotWeights`: rows from `B`, the bits `j < J`. -/
theorem slotInner (B : Nat) (v : Nat → EW) : ∀ (J : Nat) (rows : Array (Array EW)),
    (∀ r < 64, (rows.getD r #[]).size = 64) → ∀ r < 64, ∀ z < 64,
    (((List.range J).foldl (fun rows j ↦
      rows.modify (B + j / 64) fun row ↦ row.setIfInBounds (j % 64) (v j)) rows).getD r #[]).getD
        z 0 =
      if B ≤ r ∧ 64 * (r - B) + z < J then v (64 * (r - B) + z) else (rows.getD r #[]).getD z 0
  | 0, rows, _, r, _, z, _ => by
    simp only [List.range_zero, List.foldl_nil]
    split <;> [omega; rfl]
  | J + 1, rows, hw, r, hr, z, hz => by
    have ih := slotInner B v J rows hw r hr z hz
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, modifySet_getD, ih,
      (slotInner_size B v J rows).2, hw r hr]
    by_cases hc : B + J / 64 = r ∧ J % 64 = z
    · have h1 : B ≤ r ∧ 64 * (r - B) + z < J + 1 := by omega
      have h2 : 64 * (r - B) + z = J := by omega
      rw [h2]
      split_ifs <;> first | rfl | omega
    · split_ifs <;> first | rfl | omega

/-- The outer loop of `keccakSlotWeights` keeps every row's size. -/
theorem slotOuter_size (first : Nat) (seg wt : Array EW) : ∀ (S : Nat) (rows : Array (Array EW)),
    ((List.range S).foldl (fun rows segment ↦ (List.range Verifier.keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (seg.getD segment 0 * wt.getD j 0)) rows) rows).size =
        rows.size ∧
    ∀ r, (((List.range S).foldl (fun rows segment ↦
      (List.range Verifier.keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (seg.getD segment 0 * wt.getD j 0)) rows) rows).getD r
            #[]).size = (rows.getD r #[]).size
  | 0, _ => ⟨rfl, fun _ ↦ rfl⟩
  | S + 1, rows => by
    obtain ⟨hs, hr⟩ := slotOuter_size first seg wt S rows
    rw [List.range_succ (n := S), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hr'⟩ := slotInner_size (25 * (first + S)) (fun j ↦ seg.getD S 0 * wt.getD j 0)
      Verifier.keccakBits
      ((List.range S).foldl (fun rows segment ↦ (List.range Verifier.keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (seg.getD segment 0 * wt.getD j 0)) rows) rows)
    exact ⟨hs'.trans hs, fun r ↦ (hr' r).trans (hr r)⟩

/-- The outer loop of `keccakSlotWeights`: segments `first + s`, `s < S`. -/
theorem slotOuter (first : Nat) (seg wt : Array EW) : ∀ (S : Nat) (rows : Array (Array EW)),
    (∀ r < 64, (rows.getD r #[]).size = 64) → ∀ r < 64, ∀ z < 64,
    (((List.range S).foldl (fun rows segment ↦ (List.range Verifier.keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (seg.getD segment 0 * wt.getD j 0)) rows) rows).getD r
          #[]).getD z 0 =
      if 25 * first ≤ r ∧ r < 25 * (first + S) then
        seg.getD (r / 25 - first) 0 * wt.getD (64 * (r % 25) + z) 0
      else (rows.getD r #[]).getD z 0
  | 0, rows, _, r, _, z, _ => by
    simp only [List.range_zero, List.foldl_nil]
    split <;> [omega; rfl]
  | S + 1, rows, hw, r, hr, z, hz => by
    have ih := slotOuter first seg wt S rows hw r hr z hz
    rw [List.range_succ (n := S), List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [slotInner (25 * (first + S)) (fun j ↦ seg.getD S 0 * wt.getD j 0) Verifier.keccakBits _
      (fun r hr ↦ by rw [(slotOuter_size first seg wt S rows).2 r, hw r hr]) r hr z hz, ih,
      show Verifier.keccakBits = 1600 from rfl]
    by_cases hc : 25 * (first + S) ≤ r ∧ 64 * (r - 25 * (first + S)) + z < 1600
    · have h1 : 25 * first ≤ r ∧ r < 25 * (first + (S + 1)) := by omega
      have h2 : r / 25 - first = S := by omega
      have h3 : 64 * (r - 25 * (first + S)) + z = 64 * (r % 25) + z := by omega
      rw [h2, h3]
      split_ifs <;> first | rfl | omega
    · split_ifs <;> first | rfl | omega

/-- `2^6` slots. -/
theorem qkeccakSlotBits_eq : Verifier.qkeccakSlotBits = 6 := by decide

/-- A row of `keccakSlotWeights`'s start. -/
theorem slotInit_getD {r : Nat} (hr : r < 64) :
    (Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 (0 : EW))).getD r #[] =
      Array.replicate 64 0 := by
  rw [qkeccakSlotBits_eq, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  simp [hr]

theorem slotWeights_size (logSteps : Nat) (claim : KeccakClaimW) (first count : Nat) :
    (keccakSlotWeights logSteps claim first count).size = 64 ∧
      ∀ r < 64, ((keccakSlotWeights logSteps claim first count).getD r #[]).size = 64 := by
  obtain ⟨hs, hr⟩ := slotOuter_size first
    (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)) claim.weights count
    (Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 0))
  rw [keccakSlotWeights]
  refine ⟨by rw [hs, Array.size_replicate, qkeccakSlotBits_eq]; rfl, fun r h ↦ ?_⟩
  rw [hr, slotInit_getD h, Array.size_replicate]

theorem slotWeights_getD (logSteps : Nat) (claim : KeccakClaimW) {first count : Nat}
    (_h : first + count ≤ 2) {r z : Nat} (hr : r < 64) (hz : z < 64) :
    ((keccakSlotWeights logSteps claim first count).getD r #[]).getD z 0 =
      slotRow logSteps claim first count r z := by
  -- `r < 64` bounds every write: `first + count ≤ 2` is not needed.
  rw [keccakSlotWeights, slotOuter first _ _ count _ (fun r h ↦ by
    rw [slotInit_getD h, Array.size_replicate]) r hr z hz, slotInit_getD hr, slotRow]
  simp [Array.getD_eq_getD_getElem?, hz]

/-- `foldPairs` entry by entry. -/
theorem foldPairs_eq (c : E) : ∀ (l : List E), Verifier.foldPairs c l =
    (List.range (l.length / 2)).map fun i ↦ l.getD (2 * i) 0 * (1 + c) + l.getD (2 * i + 1) 0 * c
  | [] => by simp [Verifier.foldPairs]
  | [_] => by simp [Verifier.foldPairs]
  | a :: b :: l => by
    rw [Verifier.foldPairs, foldPairs_eq c l,
      show (a :: b :: l).length / 2 = l.length / 2 + 1 by simp; omega, List.range_succ_eq_map]
    simp [Nat.mul_add, Function.comp_def]

/-- An entry of a list map over a range. -/
theorem listGetD_map_range {α : Type} (n : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- An entry of `zipWith` within both arrays. -/
theorem zipWith_getD (f : EW → EW → EW) (a b : Array EW) {z : Nat} (ha : z < a.size)
    (hb : z < b.size) : (Array.zipWith f a b).getD z 0 = f (a.getD z 0) (b.getD z 0) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_zipWith, Array.getElem?_eq_getElem ha,
    Array.getElem?_eq_getElem hb]

/-- The fold of `keccakOpen`'s rows over a list of challenges. -/
theorem openRows_list {z : Nat} (hz : z < 64) : ∀ (L : List EW) (rows : Array (Array EW)),
    rows.size = 2 ^ L.length → (∀ r < rows.size, (rows.getD r #[]).size = 64) →
    (((L.foldl (fun rows challenge ↦ (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) rows).getD 0 #[]).getD z 0).toE =
    ((L.map EW.toE).foldl (fun cur r ↦ Verifier.foldPairs r cur)
      ((List.range rows.size).map fun r ↦ ((rows.getD r #[]).getD z 0).toE)).headD 0
  | [], rows, hs, _ => by
    rw [List.length_nil, Nat.pow_zero] at hs
    simp [hs]
  | c :: L, rows, hs, hw => by
    have hs' : rows.size / 2 = 2 ^ L.length := by
      rw [hs, List.length_cons, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have h2 : ∀ i < rows.size / 2, 2 * i + 1 < rows.size := fun i hi ↦ by omega
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      openRows_list hz L _ (by rw [Array.size_map, Array.size_range, hs']) fun r hr ↦ by
        rw [Array.size_map, Array.size_range] at hr
        rw [getD_map_range _ _ _ hr, Array.size_zipWith, hw _ (by have := h2 r hr; omega),
          hw _ (h2 r hr), Nat.min_self]]
    congr 2
    rw [foldPairs_eq, List.length_map, List.length_range, Array.size_map, Array.size_range]
    refine List.map_congr_left fun i hi ↦ ?_
    have hi := List.mem_range.1 hi
    have h2i := h2 i hi
    rw [getD_map_range _ _ _ hi, zipWith_getD _ _ _ (by rw [hw _ (by omega)]; exact hz)
      (by rw [hw _ h2i]; exact hz), listGetD_map_range _ _ _ (by omega),
      listGetD_map_range _ _ _ h2i, Equiv.EW.toE_add, Equiv.EW.toE_mul, Equiv.EW.toE_add]
    ring

/-- **The fold of `keccakOpen`'s rows**: position `z` of the last row is the multilinear extension
of the rows' column `z` at the slot. -/
theorem openRows_getD (slot : Array EW) (rows : Array (Array EW)) (hs : rows.size = 2 ^ slot.size)
    (hw : ∀ r < rows.size, (rows.getD r #[]).size = 64) {z : Nat} (hz : z < 64) :
    (((slot.foldl (fun rows challenge ↦ (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) rows).getD 0 #[]).getD z 0).toE =
    Verifier.multilinearEval ((List.range rows.size).map fun r ↦ ((rows.getD r #[]).getD z 0).toE)
      (slot.toList.map EW.toE) := by
  rw [← Array.foldl_toList,
    openRows_list hz slot.toList rows (by rw [Array.length_toList]; exact hs) hw]
  rfl

end NativeVm.Math.Keccak
