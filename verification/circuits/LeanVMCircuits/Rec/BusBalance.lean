module

public import LeanVMCircuits.Rec.Bus
public import LeanVMCircuits.Rec.UnionSound

@[expose] public section

/-!
The bus's balance from its product check.

`BusBlocks::new` gives every slot a pull block at its own key and a push block at its `next` key, both carrying its
limbs (`SlotKey::column`, `FixedColumn::Next`). `bus::verify_balance` draws four challenges `A` and `β`, weighs each
tuple's coordinates by `eq(A, k)` (`fingerprint_weights`, the union's `UnionSound.eqAt`), and its GKR proves the
products of `β + fp_A(t)` over the pulls and over the pushes equal (one root for both trees).

`bus_balance_sound`: with tuples encoded injectively, if the pulls and pushes are not `Balanced`, they are different
multisets, and the points `(β, A)` of `S^5` at which the two products agree are at most a `4n/|S|` fraction
(`UnionSound.coverage_sound`, Schwartz-Zippel). `bus_copy_sound`: with `next` the classes' cycles (`classNext`) and
distinct keys, the points at which the products agree but two slots of one class carry different limbs are at most
that fraction (`copy_argument`).
-/

namespace LeanVMCircuits.Rec

open UnionSound Finset

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- The pulls: each slot's key and limbs. -/
def pulls (enc : ℕ × V → Tuple) (key : Fin n → ℕ) (v : Fin n → V) : Multiset Tuple :=
  (univ.val : Multiset (Fin n)).map fun s => enc (key s, v s)

/-- The pushes: each slot's `next` key and its limbs. -/
def pushes (enc : ℕ × V → Tuple) (key : Fin n → ℕ) (next : Fin n → Fin n) (v : Fin n → V) : Multiset Tuple :=
  (univ.val : Multiset (Fin n)).map fun s => enc (key (next s), v s)

/-- Equal pulls and pushes, their tuples encoded injectively, balance. -/
theorem balanced_of_eq (enc : ℕ × V → Tuple) (D : Set (ℕ × V)) (henc : Set.InjOn enc D) (key : Fin n → ℕ)
    (next : Fin n → Fin n) (v : Fin n → V) (hD : ∀ s, (key s, v s) ∈ D ∧ (key (next s), v s) ∈ D)
    (h : pulls enc key v = pushes enc key next v) : Balanced key next v := by
  classical
  intro x
  -- Both counts are the multiplicity of `x`'s encoding, or zero when `x` is not in `D`.
  by_cases hx : x ∈ D
  · have hcount : ∀ g : Fin n → ℕ × V, (∀ s, g s ∈ D) →
        (univ.filter fun s => g s = x).card = Multiset.count (enc x) ((univ.val : Multiset (Fin n)).map fun s => enc (g s)) := by
      intro g hg
      rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
      congr 1
      ext s
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h ▸ rfl, fun h => henc (hg s) hx h.symm⟩
    have e1 := hcount (fun s => (key s, v s)) fun s => (hD s).1
    have e2 := hcount (fun s => (key (next s), v s)) fun s => (hD s).2
    rw [e1, e2]
    unfold pulls pushes at h
    rw [h]
  · have h1 : (univ.filter fun s => (key s, v s) = x) = ∅ :=
      filter_eq_empty_iff.mpr fun s _ he => hx (he ▸ (hD s).1)
    have h2 : (univ.filter fun s => (key (next s), v s) = x) = ∅ :=
      filter_eq_empty_iff.mpr fun s _ he => hx (he ▸ (hD s).2)
    rw [h1, h2]

open Classical in
/-- The bus's product check: if the pulls and pushes do not balance, the points `(β, A)` of `S^5` at which the
products of `β + fp_A(t)` over them agree are at most a `4n/|S|` fraction. -/
theorem bus_balance_sound (enc : ℕ × V → Tuple) (D : Set (ℕ × V)) (henc : Set.InjOn enc D) (key : Fin n → ℕ)
    (next : Fin n → Fin n) (v : Fin n → V) (hD : ∀ s, (key s, v s) ∈ D ∧ (key (next s), v s) ∈ D)
    (hne : ¬ Balanced key next v) (S : Finset E) :
    (#{f ∈ Fintype.piFinset fun _ : Fin 5 => S |
        prodAt (pulls enc key v) (f 0) (Fin.tail f) = prodAt (pushes enc key next v) (f 0) (Fin.tail f)} : ℚ≥0) /
      (#S ^ 5 : ℚ≥0) ≤ 4 * n / #S := by
  have hP : Multiset.card (pulls enc key v) ≤ n := by simp [pulls]
  have hQ : Multiset.card (pushes enc key next v) ≤ n := by simp [pushes]
  exact_mod_cast coverage_sound _ _ n hP hQ (fun h => hne (balanced_of_eq enc D henc key next v hD h)) S

open Classical in
/-- The copy argument from the bus's product check: with `next` the classes' cycles and distinct keys, the points
`(β, A)` of `S^5` at which the products agree but two slots of one class carry different limbs are at most a `4n/|S|`
fraction. -/
theorem bus_copy_sound (enc : ℕ × V → Tuple) (D : Set (ℕ × V)) (henc : Set.InjOn enc D) (key : Fin n → ℕ)
    (hkey : Function.Injective key) (cls : Fin n → ℕ) (v : Fin n → V)
    (hD : ∀ s, (key s, v s) ∈ D ∧ (key (classNext cls s), v s) ∈ D) (S : Finset E) :
    (#{f ∈ Fintype.piFinset fun _ : Fin 5 => S |
        prodAt (pulls enc key v) (f 0) (Fin.tail f) = prodAt (pushes enc key (classNext cls) v) (f 0) (Fin.tail f) ∧
        ∃ i j, cls i = cls j ∧ v i ≠ v j} : ℚ≥0) / (#S ^ 5 : ℚ≥0) ≤ 4 * n / #S := by
  by_cases hb : Balanced key (classNext cls) v
  · -- Balanced, every class carries one value: no point is counted.
    have hempty : ({f ∈ Fintype.piFinset fun _ : Fin 5 => S |
        prodAt (pulls enc key v) (f 0) (Fin.tail f) = prodAt (pushes enc key (classNext cls) v) (f 0) (Fin.tail f) ∧
        ∃ i j, cls i = cls j ∧ v i ≠ v j} : Finset (Fin 5 → E)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun f _ ⟨_, i, j, hc, hv⟩ => hv ?_
      exact copy_argument key hkey cls v hb i j hc
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    positivity
  · refine le_trans ?_ (bus_balance_sound enc D henc key (classNext cls) v hD hb S)
    gcongr
    exact fun h => h.1

end LeanVMCircuits.Rec
