module

public import LeanVM.Protocol.Extraction.Fast.FFT.Basis

/-!
# The transform plan of size `2^j`

`mkPlan j : FFTPlan`, the precomputations of the additive FFT of size `2^j`, built once:

* the conversion tables `tableUpTo j` (`(s_{i,·}, β_i)`, `O(j²)` products) and `tableInvUpTo j`
  (`(s_{i,·}, β_i^{-1})`), the `j` inverses **batched** (`batchInv`: one inversion and `3j`
  products, Montgomery's trick);
* the twiddles of every stage `i < j`, `Ŵ_i(x_{w·2^(i+1)})` for `w < 2^(j−i−1)`, **by additivity**
  (`spanTable`): `Ŵ_i` is additive and `x_{w·2^(i+1)} = Σ_{bit b of w} x^{i+1+b}`, so the
  `2^(j−i−1)` twiddles are the subset sums of the `j − i − 1` values `Ŵ_i(x^{i+1+b})`
  (`W_i` linearized, `evalLin`: `2i + 3` products each), by doubling: additions only.

`planFwd P`, `planInv P`: lean_vm's additive NTT (`novelFwd j 0`, `novelInv j`) with the plan's
twiddles, by `fwdStageFast` (the products `t·hi` first, each read by both outputs of its
butterfly: `N/2` products per stage, not `N`; `fwdStageFast_eq`) and `invStageFast`, the powers
`2^i`, `2^(i+1)` once per stage. The conversions read the powers `2^t` from the plan (`pows`;
`FFT/Convert.lean`), none computed per entry. **Proved** for `j ≤ 64`:
`planFwd_eq : planFwd (mkPlan j) c = novelFwd j 0 c`,
`planInv_eq : planInv (mkPlan j) y = novelInv j y`, `mkPlan_tableInv`, and
`mkPlan_twiddles : (mkPlan j).twiddles[i] = novelTwiddles j i`; so the transform's laws carry
over unchanged.
-/

namespace LeanVM.Extraction.Fast.FFT

open LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Words LeanVM.Extraction.Subspace
  LeanVM.Extraction.NovelProofs

public section

/-! ## The stages with given twiddles -/

/-- `novelFwdStage m i` with the twiddles `tw`. -/
@[expose] def fwdStageWith (m i : ℕ) (tw b : Array K) : Array K :=
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + (t + 1) * b.getD p.val 0
    else
      b.getD p.val 0 + t * b.getD (p.val + 2 ^ i) 0

/-- `novelInvStage m i` with the twiddles `tw`. -/
@[expose] def invStageWith (m i : ℕ) (tw b : Array K) : Array K :=
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + b.getD p.val 0
    else
      b.getD p.val 0 + t * (b.getD p.val 0 + b.getD (p.val + 2 ^ i) 0)

theorem novelFwdStage_eq_with (m i : ℕ) (b : Array K) :
    novelFwdStage m i b = fwdStageWith m i (novelTwiddles m i) b := rfl

theorem novelInvStage_eq_with (m i : ℕ) (b : Array K) :
    novelInvStage m i b = invStageWith m i (novelTwiddles m i) b := rfl

/-- **The forward stage, one product per butterfly**: the products `t·hi` first (at the low
positions), each read by both outputs `lo + t·hi` and `lo + t·hi + hi`; the powers `2^i`,
`2^(i+1)` once per stage. -/
@[expose] def fwdStageFast (m i : ℕ) (tw b : Array K) : Array K :=
  let H := 2 ^ i
  let H2 := 2 ^ (i + 1)
  let prod := Array.ofFn fun p : Fin (2 ^ m) ↦
    if p.val.testBit i then 0 else tw.getD (p.val / H2) 0 * b.getD (p.val + H) 0
  Array.ofFn fun p : Fin (2 ^ m) ↦
    if p.val.testBit i then
      let lo := p.val - H
      b.getD lo 0 + prod.getD lo 0 + b.getD p.val 0
    else
      b.getD p.val 0 + prod.getD p.val 0

/-- The inverse stage (one product per butterfly already), the powers once per stage. -/
@[expose] def invStageFast (m i : ℕ) (tw b : Array K) : Array K :=
  let H := 2 ^ i
  let H2 := 2 ^ (i + 1)
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / H2) 0
    if p.val.testBit i then
      b.getD (p.val - H) 0 + b.getD p.val 0
    else
      b.getD p.val 0 + t * (b.getD p.val 0 + b.getD (p.val + H) 0)

theorem invStageFast_eq (m i : ℕ) (tw b : Array K) : invStageFast m i tw b = invStageWith m i tw b :=
  rfl

theorem fwdStageFast_eq (m i : ℕ) (tw b : Array K) : fwdStageFast m i tw b = fwdStageWith m i tw b := by
  apply array_eq_of_getD (by simp [fwdStageFast, fwdStageWith])
  intro p hp
  have hp' : p < 2 ^ m := by simpa [fwdStageFast] using hp
  rw [fwdStageWith, getD_ofFn _ hp', fwdStageFast]
  dsimp only
  rw [getD_ofFn _ hp']
  obtain ⟨q, s', bit, hs, hbit, rfl⟩ := decompose i p
  interval_cases bit
  · simp only [nf_testBit0 hs, Bool.false_eq_true, ite_false]
    rw [getD_ofFn _ hp']
    simp only [nf_testBit0 hs, Bool.false_eq_true, ite_false]
  · have hm1 : 2 ^ (i + 1) * q + 2 ^ i * 1 + s' - 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 0 + s' := by
      omega
    have hlo : 2 ^ (i + 1) * q + 2 ^ i * 0 + s' < 2 ^ m := by omega
    simp only [nf_testBit1 hs, ite_true]
    rw [hm1, getD_ofFn _ hlo]
    simp only [nf_testBit0 hs, Bool.false_eq_true, ite_false]
    rw [nf_div2 hs (by norm_num : 0 < 2), nf_div2 hs (by norm_num : 1 < 2),
      show 2 ^ (i + 1) * q + 2 ^ i * 0 + s' + 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 1 + s' by ring]
    ring

/-! ## Subset sums by doubling -/

/-- The `2^n` subset sums `Σ_{b<n, bit b of w} c_b`, `w < 2^n`, by doubling. -/
@[expose] def spanTable (c : ℕ → K) : ℕ → Array K
  | 0 => #[0]
  | n + 1 =>
    let T := spanTable c n
    let cn := c n
    T ++ Array.ofFn fun w : Fin (2 ^ n) ↦ T.getD w.val 0 + cn

theorem size_spanTable (c : ℕ → K) (n : ℕ) : (spanTable c n).size = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [spanTable, Array.size_append, ih, Array.size_ofFn, pow_succ]; ring

/-- The subset sums of an additive function's values at the powers of two are its values. -/
theorem spanTable_getD (f : ℕ → K) (h0 : f 0 = 0)
    (hadd : ∀ b w, w < 2 ^ b → f (2 ^ b + w) = f (2 ^ b) + f w) (n : ℕ) :
    ∀ w < 2 ^ n, (spanTable (fun b ↦ f (2 ^ b)) n).getD w 0 = f w := by
  induction n with
  | zero =>
    intro w hw
    rw [show w = 0 by simpa using hw, h0]
    rfl
  | succ n ih =>
    intro w hw
    rw [spanTable, getD_append, size_spanTable]
    split
    · exact ih w (by assumption)
    · rename_i hlt
      have hw' : w - 2 ^ n < 2 ^ n := by rw [pow_succ] at hw; omega
      rw [getD_ofFn _ hw', ih _ hw', add_comm, ← hadd n _ hw', Nat.add_sub_cancel' (by omega)]

/-! ## Batched inversion -/

/-- The inverses of `l` and of `p` (the product so far), with one inversion: `b⁻¹ = (p·b)⁻¹·p`,
`p⁻¹ = (p·b)⁻¹·b`. -/
@[expose] def batchInvAux : List K → K → List K × K
  | [], p => ([], p⁻¹)
  | b :: rest, p =>
    let r := batchInvAux rest (p * b)
    (r.2 * p :: r.1, r.2 * b)

/-- **Batched inversion**: the inverses of a list, by one inversion and `3` products per entry. -/
@[expose] def batchInv (l : List K) : List K := (batchInvAux l 1).1

theorem batchInvAux_eq (l : List K) {p : K} (hp : p ≠ 0) (hl : ∀ b ∈ l, b ≠ 0) :
    batchInvAux l p = (l.map (·⁻¹), p⁻¹) := by
  induction l generalizing p with
  | nil => rfl
  | cons b rest ih =>
    have hb := hl b List.mem_cons_self
    rw [batchInvAux, ih (mul_ne_zero hp hb) fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)]
    simp only [List.map_cons, Prod.mk.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> field_simp

theorem batchInv_eq (l : List K) (hl : ∀ b ∈ l, b ≠ 0) : batchInv l = l.map (·⁻¹) := by
  rw [batchInv, batchInvAux_eq l one_ne_zero hl]

/-! ## The conversions with the powers of two precomputed -/

/-! ## The plan -/

/-- **The precomputations of the additive FFT of size `2^log`.** -/
structure FFTPlan where
  /-- `j`: the size is `2^j`. -/
  log : ℕ
  /-- `tableUpTo j`. -/
  table : List (Array K × K)
  /-- `tableInvUpTo j`. -/
  tableInv : List (Array K × K)
  /-- Stage `i`'s twiddles, `novelTwiddles j i`. -/
  twiddles : Array (Array K)
  /-- The powers `2^t`, `t < j`. -/
  pows : Array ℕ
  /-- Level `i`'s `(s_{i,·}, β_i)`, `i < j` (`linData i`), for the monomial-to-novel passes. -/
  convFwd : Array (Array K × K)
  /-- Level `i`'s `((s_{i,t}·β_i^{-1})_{t<i}, β_i^{-1})`, for the novel-to-monomial passes. -/
  convInv : Array (Array K × K)

/-- Stage `i`'s twiddles of size `2^j` from `(s_{i,·}, β_i^{-1})`: the subset sums of
`Ŵ_i(x^{i+1+b}) = W_i(x^{i+1+b})·β_i^{-1}`, `b < j − i − 1`. -/
@[expose] def stageTwiddles (j i : ℕ) (d : Array K × K) : Array K :=
  spanTable (fun b ↦ evalLin d.1 (K.ofBits (2 ^ b * 2 ^ (i + 1))) * d.2) (j - (i + 1))

/-- **The plan of size `2^j`.** -/
@[expose] def mkPlan (j : ℕ) : FFTPlan :=
  let tab := tableUpTo j
  let invs := batchInv (tab.map fun d ↦ d.2)
  let tabInv := List.zipWith (fun d b ↦ (d.1, b)) tab invs
  { log := j
    table := tab
    tableInv := tabInv
    twiddles := Array.ofFn fun i : Fin j ↦
      stageTwiddles j i.val (tabInv.getD (j - 1 - i.val) (#[], 0))
    pows := Array.ofFn fun t : Fin j ↦ 2 ^ t.val
    convFwd := Array.ofFn fun i : Fin j ↦ tab.getD (j - 1 - i.val) (#[], 0)
    convInv := Array.ofFn fun i : Fin j ↦
      let d := tabInv.getD (j - 1 - i.val) (#[], 0)
      (Array.ofFn fun t : Fin i.val ↦ d.1.getD t.val 0 * d.2, d.2) }

theorem mkPlan_pows {j t : ℕ} (ht : t < j) : (mkPlan j).pows.getD t 0 = 2 ^ t := by
  simp [mkPlan, Array.getD, ht]

theorem mkPlan_log (j : ℕ) : (mkPlan j).log = j := rfl

theorem zipWith_map_self (l : List (Array K × K)) (g : K → K) :
    List.zipWith (fun d b ↦ (d.1, b)) l ((l.map fun d ↦ d.2).map g) = l.map fun d ↦ (d.1, g d.2) := by
  induction l with
  | nil => rfl
  | cons d l ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem tableUpTo_ne_zero {j : ℕ} (hj : j ≤ 64) : ∀ b ∈ (tableUpTo j).map (fun d ↦ d.2), b ≠ 0 := by
  intro b hb
  rw [tableUpTo_eq, List.map_map] at hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi : i < j := by simpa using hi
  simp only [Function.comp, (linData_spec i).2.2.2]
  exact subspacePoly_basis_ne_zero' (by omega)

theorem mkPlan_tableInv {j : ℕ} (hj : j ≤ 64) : (mkPlan j).tableInv = tableInvUpTo j := by
  show List.zipWith _ _ (batchInv _) = _
  rw [batchInv_eq _ (tableUpTo_ne_zero hj), zipWith_map_self, tableInvUpTo]

theorem getD_reverse_range {α : Type} (g : ℕ → α) (d : α) {j i : ℕ} (hi : i < j) :
    ((List.range j).reverse.map g).getD (j - 1 - i) d = g i := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
  congr 1
  omega

/-- The twiddles by additivity are lean_vm's. -/
theorem mkPlan_convFwd {j i : ℕ} (hi : i < j) :
    (mkPlan j).convFwd.getD i (#[], 0) = linData i := by
  simp only [mkPlan]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  rw [tableUpTo_eq, getD_reverse_range _ _ hi]

theorem mkPlan_convInv {j i : ℕ} (hj : j ≤ 64) (hi : i < j) :
    (mkPlan j).convInv.getD i (#[], 0) =
      (Array.ofFn fun t : Fin i ↦ (linData i).1.getD t.val 0 * (linData i).2⁻¹, (linData i).2⁻¹) := by
  have h := mkPlan_tableInv hj
  simp only [mkPlan] at h ⊢
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  rw [h, tableInvUpTo, tableUpTo_eq, List.map_map, getD_reverse_range _ _ hi]
  rfl

theorem stageTwiddles_eq (j i : ℕ) :
    stageTwiddles j i ((linData i).1, (linData i).2⁻¹) = novelTwiddles j i := by
  set f : ℕ → K := fun w ↦ normSubspacePoly i (K.ofBits (w * 2 ^ (i + 1))) with hf
  have hc : (fun b ↦ evalLin (linData i).1 (K.ofBits (2 ^ b * 2 ^ (i + 1))) * (linData i).2⁻¹) =
      fun b ↦ f (2 ^ b) := by
    funext b
    obtain ⟨hs, _, hp, hβ⟩ := linData_spec i
    rw [evalLin_eq, hs, hp, eval_vanishing, hβ, hf]
    rfl
  have h0 : f 0 = 0 := by
    simp only [hf, Nat.zero_mul]
    exact normSubspacePoly_of_lt (Nat.two_pow_pos i)
  have hadd : ∀ b w, w < 2 ^ b → f (2 ^ b + w) = f (2 ^ b) + f w := by
    intro b w hw
    have hlt : w * 2 ^ (i + 1) < 2 ^ (b + (i + 1)) := by
      rw [Nat.pow_add 2 b (i + 1)]; exact Nat.mul_lt_mul_of_pos_right hw (Nat.two_pow_pos _)
    simp only [hf]
    rw [add_mul, ← pow_add, ofBits_two_pow_add hlt, normSubspacePoly_add]
  rw [stageTwiddles, hc]
  apply array_eq_of_getD (by rw [size_spanTable, novelTwiddles, Array.size_ofFn])
  intro w hw
  rw [size_spanTable] at hw
  rw [spanTable_getD f h0 hadd _ w hw, novelTwiddles, getD_ofFn _ hw]
  rfl

theorem mkPlan_twiddles {j i : ℕ} (hj : j ≤ 64) (hi : i < j) :
    (mkPlan j).twiddles.getD i #[] = novelTwiddles j i := by
  have h := mkPlan_tableInv hj
  simp only [mkPlan] at h ⊢
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  rw [h, tableInvUpTo, tableUpTo_eq, List.map_map, getD_reverse_range _ _ hi]
  exact stageTwiddles_eq j i

/-! ## The planned transforms -/

/-- **The forward transform by the plan**: `novelFwd j 0` with the plan's twiddles. -/
@[expose] def planFwd (P : FFTPlan) (c : Array K) : Array K :=
  (List.range P.log).foldr (fun i b ↦ fwdStageFast P.log i (P.twiddles.getD i #[]) b)
    (Array.ofFn fun p : Fin (2 ^ P.log) ↦ c.getD p.val 0)

/-- **The inverse transform by the plan**: `novelInv j` with the plan's twiddles. -/
@[expose] def planInv (P : FFTPlan) (y : Array K) : Array K :=
  (List.range P.log).foldl (fun b i ↦ invStageFast P.log i (P.twiddles.getD i #[]) b) y

theorem foldr_range_congr {f g : ℕ → Array K → Array K} {n : ℕ} (h : ∀ i < n, f i = g i)
    (init : Array K) : (List.range n).foldr f init = (List.range n).foldr g init := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_append, List.foldr_cons, List.foldr_cons,
      List.foldr_nil, List.foldr_nil, h n (by omega), ih fun i hi ↦ h i (by omega)]

theorem foldl_range_congr {f g : Array K → ℕ → Array K} {n : ℕ} (h : ∀ i < n, ∀ b, f b i = g b i)
    (init : Array K) : (List.range n).foldl f init = (List.range n).foldl g init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil, ih fun i hi ↦ h i (by omega), h n (by omega)]

theorem planFwd_eq {j : ℕ} (hj : j ≤ 64) (c : Array K) : planFwd (mkPlan j) c = novelFwd j 0 c := by
  rw [planFwd, novelFwd, mkPlan_log]
  show _ = (List.range j).foldr (fun i b ↦ novelFwdStage j i b)
    (Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD (p.val % 2 ^ j) 0)
  rw [show (Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD (p.val % 2 ^ j) 0) =
      Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD p.val 0 from
    congrArg Array.ofFn (funext fun p ↦ by rw [Nat.mod_eq_of_lt p.isLt])]
  refine foldr_range_congr (fun i hi ↦ ?_) _
  funext b
  rw [fwdStageFast_eq, novelFwdStage_eq_with, mkPlan_twiddles hj hi]

theorem planInv_eq {j : ℕ} (hj : j ≤ 64) (y : Array K) : planInv (mkPlan j) y = novelInv j y := by
  rw [planInv, novelInv, mkPlan_log]
  refine foldl_range_congr (fun i hi b ↦ ?_) _
  rw [invStageFast_eq, novelInvStage_eq_with, mkPlan_twiddles hj hi]

end

end LeanVM.Extraction.Fast.FFT
