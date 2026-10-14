import Whir.PCSRewindExtractorAttempts
import Whir.FieldInverse

/-! Executable source-loop counters. A unit is one K or E addition or multiplication. E.scale charges its three K multiplications. The source K inverse uses its actual 64-bit exponentiation loop, not the decoder's E inverse. Comparisons, copies, input words and oracle calls are not field arithmetic. -/
namespace Whir.CountedCandidateCheck
open Concrete Protocol CausalGame SupportedCandidateExtraction

/-- Instrument a loop while retaining its actual source state. -/
def loop {S X : Type*} (step : S → X → S × Nat) : List X → S × Nat → S × Nat
  | [], state => state
  | x :: xs, state =>
    let next := step state.1 x
    loop step xs (next.1, state.2 + next.2)

theorem loop_value {S X : Type*} (step : S → X → S × Nat) (xs : List X) (s : S × Nat) :
    (loop step xs s).1 = xs.foldl (fun v x => (step v x).1) s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa [loop] using ih ((step s.1 x).1, s.2 + (step s.1 x).2)

theorem loop_constant_charge {S X : Type*} (step : S → X → S × Nat) (charge : X → Nat)
    (equal : ∀ s x, (step s x).2 = charge x) (xs : List X) (s : S × Nat) :
    (loop step xs s).2 = s.2 + (xs.map charge).sum := by
  induction xs generalizing s with
  | nil => simp [loop]
  | cons x xs ih => simp [loop, ih, equal, Nat.add_assoc]

theorem loop_bound {S X : Type*} (step : S → X → S × Nat) (P : S → Prop)
    (bound : Nat) (preserve : ∀ s x, P s → P (step s x).1)
    (charge : ∀ s x, P s → (step s x).2 ≤ bound)
    (xs : List X) (s : S × Nat) (valid : P s.1) :
    (loop step xs s).2 ≤ s.2 + xs.length * bound := by
  induction xs generalizing s with
  | nil => simp [loop]
  | cons x xs ih =>
    have h := ih ((step s.1 x).1, s.2 + (step s.1 x).2) (preserve _ _ valid)
    simp only [loop, List.length_cons]
    calc
      _ ≤ s.2 + (step s.1 x).2 + xs.length * bound := h
      _ ≤ s.2 + (xs.length + 1) * bound := by
        have hc := charge s.1 x valid
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-- Count the fixed source square-and-multiply body. -/
def powStep (exponent : Nat) (s : K × K) (i : Nat) : (K × K) × Nat :=
  ((kmul s.1 s.1, if exponent.testBit i then kmul s.2 s.1 else s.2),
    1 + if exponent.testBit i then 1 else 0)

def countedKpow (a : K) (exponent : Nat) : K × Nat :=
  let result := loop (powStep exponent) (List.range 64) ((a, 1), 0)
  (result.1.2, result.2)

theorem countedKpow_value (a : K) (exponent : Nat) :
    (countedKpow a exponent).1 = kpow a exponent := by
  unfold countedKpow
  dsimp only
  rw [loop_value]
  unfold kpow
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    ← apply_ite, List.forIn_pure_yield_eq_foldl, pure_bind]
  apply congrArg (fun s : K × K => s.2)
  apply congrArg (fun f => List.foldl f (a, 1) (List.range 64))
  funext s i
  unfold powStep
  split_ifs <;> rfl

def countedKinv (a : K) : K × Nat := countedKpow a (2 ^ 64 - 2)

theorem countedKinv_value (a : K) : (countedKinv a).1 = kinv a :=
  countedKpow_value a _

theorem countedKinv_cost (a : K) : (countedKinv a).2 ≤ 128 := by
  have h := loop_bound (powStep (2 ^ 64 - 2)) (fun _ => True) 2
    (by intros; trivial) (by intro s i _; simp only [powStep]; split_ifs <;> decide)
    (List.range 64) ((a, 1), 0) trivial
  simpa [countedKinv, countedKpow] using h

theorem countedKinv_exact_cost (a : K) : (countedKinv a).2 = 127 := by
  have h := loop_constant_charge (powStep (2 ^ 64 - 2))
    (fun i => 1 + if (2 ^ 64 - 2 : Nat).testBit i then 1 else 0)
    (by intros; rfl) (List.range 64) ((a, 1), 0)
  have concrete : ((List.range 64).map
      (fun i => 1 + if (2 ^ 64 - 2 : Nat).testBit i then 1 else 0)).sum = 127 := by decide
  rw [concrete] at h
  simpa only [countedKinv, countedKpow, Nat.zero_add] using h

/-- The arithmetic certificate applies to precisely the inverse being charged. -/
theorem countedKinv_field (a : K) :
    E.ofK (countedKinv a).1 = (E.ofK a)⁻¹ := by
  rw [countedKinv_value]
  exact FieldModel.ofK_kinv a

def rootsStep (s : Array K × Array K) (i : Nat) : (Array K × Array K) × Nat :=
  let layer := s.2.map fun x => kmul x (x ^^^ s.1[i]!)
  ((s.1.push layer[0]!, layer.extract 1 layer.size), 2 * s.2.size)

def countedRoots (n : Nat) : Array K × Nat :=
  let result := loop rootsStep (List.range n)
    ((#[1], tab n fun i => (1 : K) <<< UInt64.ofNat (i + 1)), 0)
  (result.1.1, result.2)

theorem countedRoots_value (n : Nat) : (countedRoots n).1 = subspaceRoots n := by
  unfold countedRoots
  dsimp only
  rw [loop_value]
  unfold subspaceRoots
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem countedRoots_cost (n : Nat) : (countedRoots n).2 ≤ 2 * n * n := by
  have h := loop_bound rootsStep (fun s => s.2.size ≤ n) (2 * n)
    (by intro s i hs; simpa [rootsStep, Array.size_extract] using
      (show min s.2.size s.2.size - 1 ≤ n by omega))
    (by intro s i hs; simpa [rootsStep] using Nat.mul_le_mul_left 2 hs)
    (List.range n) ((#[1], tab n fun i => (1 : K) <<< UInt64.ofNat (i + 1)), 0)
    (by simp [tab])
  simpa [countedRoots, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

def normalizationStep (roots : Array K) (s : Array K × K) (i : Nat) :
    (Array K × K) × Nat :=
  let inverse := countedKinv roots[i]!
  ((s.1.push (kmul s.2 inverse.1), kmul s.2 (s.2 ^^^ roots[i]!)), inverse.2 + 3)

def countedNormalization (n : Nat) (x : K) : Array K × Nat :=
  let roots := countedRoots n
  let result := loop (normalizationStep roots.1) (List.range n) ((#[], x), roots.2)
  (result.1.1, result.2)

theorem countedNormalization_value (n : Nat) (x : K) :
    (countedNormalization n x).1 = normalizedSubspaces n x := by
  unfold countedNormalization
  dsimp only
  rw [loop_value, countedRoots_value]
  unfold normalizedSubspaces
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  simp only [normalizationStep, countedKinv_value]
  rfl

theorem countedNormalization_cost (n : Nat) (x : K) :
    (countedNormalization n x).2 ≤ 2 * n * n + 131 * n := by
  have h := loop_bound (normalizationStep (countedRoots n).1) (fun _ => True) 131
    (by intros; trivial) (by
      intro s i _
      dsimp [normalizationStep]
      have h := countedKinv_cost (countedRoots n).1[i]!
      omega)
    (List.range n) ((#[], x), (countedRoots n).2) trivial
  have hr := countedRoots_cost n
  simp only [countedNormalization] at ⊢
  simp only [List.length_range] at h
  omega

/-- Each source scale evaluates three base-field multiplications. -/
def columnStep (out : Array E) (s : K) : Array E × Nat :=
  (out ++ out.map (fun x => x.scale s), 3 * out.size)

def countedColumn (n q : Nat) : Array E × Nat :=
  let normalized := countedNormalization n (UInt64.ofNat q)
  loop columnStep normalized.1.toList (#[E.one], normalized.2)

theorem countedColumn_value (n q : Nat) : (countedColumn n q).1 = column n q := by
  unfold countedColumn
  rw [loop_value, countedNormalization_value]
  unfold column
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  rw [← Array.foldl_toList]
  rfl

private theorem column_loop_cost (xs : List K) (a : Array E) (cost : Nat) :
    (loop columnStep xs (a, cost)).2 = cost + 3 * a.size * (2 ^ xs.length - 1) := by
  induction xs generalizing a cost with
  | nil => simp [loop]
  | cons x xs ih =>
    simp only [loop, columnStep, ih, Array.size_append, Array.size_map, List.length_cons,
      Nat.pow_succ]
    have positive : 0 < 2 ^ xs.length := by positivity
    have hsub : 2 ^ xs.length * 2 - 1 = 2 * (2 ^ xs.length - 1) + 1 := by omega
    rw [hsub]
    ring

theorem countedColumn_cost (n q : Nat) :
    (countedColumn n q).2 ≤ 2 * n * n + 131 * n + 3 * 2 ^ n := by
  simp only [countedColumn, column_loop_cost, Array.size_singleton,
    Nat.mul_one, Array.length_toList, countedNormalization_value,
    QueryRefinement.size_normalizedSubspaces]
  have h := countedNormalization_cost n (UInt64.ofNat q)
  omega

/-- Source dot materializes exactly min(a.size,b.size) products and additions. -/
def countedDot (a b : Array E) : E × Nat := (dot a b, 2 * min a.size b.size)

@[simp] theorem countedDot_value (a b : Array E) : (countedDot a b).1 = dot a b := rfl

theorem countedDot_source (a b : Array E) :
    let products := tab (min a.size b.size) fun i => a[i]! * b[i]!
    (countedDot a b).1 = products.foldl (· + ·) 0 ∧
      (countedDot a b).2 = 2 * products.size := by
  simp [countedDot, dot, ArrayLayout.size_tab]

def countedEncode (n rate : Nat) (a : Array E) : Array E × Nat :=
  let rows := tab (2 ^ (n + rate)) fun q =>
    let col := countedColumn n q
    let result := countedDot a col.1
    (result.1, col.2 + result.2)
  (rows.map Prod.fst, (rows.map Prod.snd).toList.sum)

theorem countedEncode_value (n rate : Nat) (a : Array E) :
    (countedEncode n rate a).1 = encode n rate a := by
  simp [countedEncode, countedDot, countedColumn_value, encode, tab, Array.map_map,
    Function.comp_def]

theorem countedEncode_cost (n rate : Nat) (a : Array E) :
    (countedEncode n rate a).2 ≤
      2 ^ (n + rate) * (2 * n * n + 131 * n + 5 * 2 ^ n) := by
  let charge := fun q => (countedColumn n q).2 + (countedDot a (countedColumn n q).1).2
  have h := List.sum_le_length_nsmul ((List.range (2 ^ (n + rate))).map charge)
    (2 * n * n + 131 * n + 5 * 2 ^ n) (by
      intro cost member
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
      dsimp [charge, countedDot]
      rw [countedColumn_value, QueryRefinement.size_column]
      have hc := countedColumn_cost n q
      have hm : min a.size (2 ^ n) ≤ 2 ^ n := Nat.min_le_right _ _
      omega)
  simpa [countedEncode, tab, charge, Array.map_map, Array.toList_map,
    Function.comp_def, Nat.mul_comm] using h

end Whir.CountedCandidateCheck
