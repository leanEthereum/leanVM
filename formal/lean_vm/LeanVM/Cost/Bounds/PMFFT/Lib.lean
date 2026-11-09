module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Extractor.PMEval

/-!
# Bounds of the PM decoder's FFT: the library

Bounds by sums of per-element prices (the passes' entries and the levels cost differently):

* `ofFnFrom_cost_sum`: `Array.ofFn` (`ofFnFrom`) at `Σ_a (B a + 16) + 5`;
* `foldr_cost_sum`, `listFoldl_cost_sum`: folds at `Σ_x (B x + 11) + 3`;
* `sum_mod_block`, `sum_range_ite_lt`: the sums of a price periodic in the index.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library

public section

variable (P : MachineProgram)

/-- `Array.ofFn` through `ofFnFrom`, entry `a` at most `B a`: `Σ_{i ≤ a < n} (B a + 16) + 5`. -/
theorem ofFnFrom_cost_sum (hP : Includes P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costDeps)
    {α : Type} [MachineEncoding α] {n : ℕ} (hn : n < 2 ^ 64) (f : Fin n → α) (fVal : MachineValue)
    (hf : ∀ a : Fin n, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ → ℕ)
    (hB : ∀ a : Fin n, appCost P fVal [encodeValue a] ≤ B a) :
    ∀ i, i ≤ n → machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costIdx
        [encodeValue n, fVal, encodeValue i] ≤ (∑ a ∈ Finset.Ico i n, (B a + 16)) + 5 := by
  intro i hi
  induction hk : n - i generalizing i with
  | zero =>
    rw [Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costEq P hP f fVal hf i,
      limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt hn]
    simp only [show ¬i < n by omega, ↓reduceDIte]
    omega
  | succ k ih =>
    rw [Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costEq P hP f fVal hf i]
    simp only [show i < n by omega, ↓reduceDIte]
    have h1 := ih (i + 1) (by omega) (by omega)
    have h2 := hB ⟨i, by omega⟩
    simp only at h2
    rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt hn, limbs_of_lt (by omega : i + 1 < 2 ^ 64),
      Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [max_self]
    omega

theorem ofFnFrom_cost_sum0 (hP : Includes P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costDeps)
    {α : Type} [MachineEncoding α] {n : ℕ} (hn : n < 2 ^ 64) (f : Fin n → α) (fVal : MachineValue)
    (hf : ∀ a : Fin n, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ → ℕ)
    (hB : ∀ a : Fin n, appCost P fVal [encodeValue a] ≤ B a) :
    machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c46.costIdx [encodeValue n, fVal, encodeValue 0] ≤
      (∑ a ∈ Finset.range n, (B a + 16)) + 5 := by
  have := ofFnFrom_cost_sum P hP hn f fVal hf B hB 0 (Nat.zero_le _)
  rwa [Finset.range_eq_Ico]

/-- `List.foldr` (`foldr.c23`), element `x` at most `B x` whatever the accumulator:
`Σ_x (B x + 11) + 3`. -/
theorem foldr_cost_sum (hP : Includes P Auto.List.foldr.c23.costDeps) {α β : Type} [MachineEncoding α]
    [MachineEncoding β] (f : α → β → β) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : α → ℕ)
    (init : β) : ∀ l : List α, (∀ a ∈ l, ∀ b : β, appCost P fVal [encodeValue a, encodeValue b] ≤ B a) →
      machineCost P Auto.List.foldr.c23.costIdx [fVal, encodeValue init, encodeValue l] ≤
        (l.map fun a ↦ B a + 11).sum + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c23.costEq_nil P hP f fVal hf]; simp
  | cons x l ih =>
    intro hB
    rw [Auto.List.foldr.c23.costEq_cons P hP f fVal hf]
    have h1 := ih fun a ha b ↦ hB a (by simp [ha]) b
    have h2 := hB x (by simp) (l.foldr f init)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- `List.foldl` (`listFoldl`), element `x` at most `B x` whatever the accumulator:
`Σ_x (B x + 11) + 3`. -/
theorem listFoldl_cost_sum (hP : Includes P listFoldl.costDeps) {α β : Type} [MachineEncoding α]
    [MachineEncoding β] (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : β → ℕ) :
    ∀ (l : List β) (init : α), (∀ acc : α, ∀ b ∈ l, appCost P fVal [encodeValue acc, encodeValue b] ≤ B b) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤
        (l.map fun b ↦ B b + 11).sum + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; simp
  | cons b l ih =>
    intro init hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    have h1 := ih (f init b) fun acc b' hb ↦ hB acc b' (by simp [hb])
    have h2 := hB init b (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A sum over `H·M` indices of a function of the index modulo `H`: `M` periods. -/
theorem sum_mod_block (g : ℕ → ℕ) (H M : ℕ) :
    ∑ m ∈ Finset.range (H * M), g (m % H) = M * ∑ x ∈ Finset.range H, g x := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]

/-- Two prices by the index below or from `h`. -/
theorem sum_range_ite_lt (a b h H : ℕ) (hh : h ≤ H) :
    ∑ x ∈ Finset.range H, (if x < h then a else b) = h * a + (H - h) * b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range h, (if x < h then a else b) = h * a := by
    rw [Finset.sum_congr rfl fun x hx ↦ by rw [ite_eq_left (Finset.mem_range.mp hx)]]
    simp
  have h2 : ∑ x ∈ Finset.range k, (if h + x < h then a else b) = k * b := by
    rw [Finset.sum_congr rfl fun x _ ↦ by rw [ite_eq_right (by omega)]]
    simp
  rw [h1, h2, Nat.add_sub_cancel_left]

end

end LeanVM.Cost.Bounds.PMFFT
