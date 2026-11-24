module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Bounds.Sizes.Transcript
public import LeanVM.Cost.Prices
public import LeanVM.Cost.FastLib
public meta import Lean.Elab.Tactic

/-!
# Bounds: sorted maps, amortized

A sorted map's insertion (`SortedMap.insert`, `carry`) merges equal-weight levels, a binary
counter: one insertion may merge every level, but `N` insertions merge `O(N log N)` entries in
all. The prices are bounded by a potential (Bentley–Saxe, Tarjan's banker's method):

* `potential D ls = Σ weight·(D − log₂ weight)`: a level's entries each still to be merged at most
  `D − log₂ weight` times, once every weight is below `2^D`;
* **`carry_amortized`**: if `carry` pays `a` per level it visits and `b` per entry it merges
  (`hnil`, `hne`, `heq`, read off a compiled `carry`'s recurrence), then
  `price + b·Φ(after) ≤ b·Φ(before) + b·w·(D − log₂ w) + a·(levels + 1)`, `w` the new level's
  weight: an insertion (`w = 1`) pays `b·D + a·(levels + 1)` amortized;
* the naturals a map compares and adds (positions, weights) up to `2^(D+1)` for `N < 2^D`
  insertions: their `limbCount` at most `limbsBelowTwoPow (D + 1) = (D + 1)/64 + 1` (`limbs_le_wl`), the tactic
  `limbs [hW]` adding a bound for every `limbCount t` of the goal;
* **`listFoldl_amortized`**: a fold whose step pays at most `A` amortized (its price plus the
  potential after, at most the potential before plus `A`) pays `(A + 11)·n + 3` from a start of
  potential `0`.

The compiled maps (one `searchIn`, `mergeNewer`, `Level.merge`, `carry` and `get?` per key and
value type) instantiate them through one bound each, from the compiled recurrence (`searchRec`,
`mergeNewerRec`, matched by unfolding): `searchIn_cost_of`, `mergeNewer_cost_of`,
`levelMerge_cost_of`, `carry_amortized_of`, `get_cost_of`; the instances are the preimage index
and the first answers (`Bounds/Transcript.lean`) and the replay's maps.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Extraction.Fast

public section

/-! ## The limbs of large naturals -/

/-- **A natural at most `2^E` has at most `E/64 + 1` limbs.** -/
theorem limbs_le_wl {t E : ℕ} (h : t ≤ 2 ^ E) : limbCount t ≤ limbsBelowTwoPow E := by
  unfold limbCount limbsBelowTwoPow
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have hlt : t < 2 ^ (E + 1) := by rw [pow_succ]; omega
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 ht)).2 hlt
    have : Nat.log2 t / 64 ≤ E / 64 := Nat.div_le_div_right (by omega)
    omega

/-- The bound `limbsBelowTwoPow (D + 1)` for the naturals up to twice `2^D`. -/
theorem limbs_le_wl_two {D : ℕ} : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ limbsBelowTwoPow (D + 1) :=
  fun _ h ↦ limbs_le_wl (by rw [pow_succ]; omega)

section Amortized

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- **The potential** of levels below `2^D`: each level's weight times `D − log₂ weight`, the
merges its entries may still take part in. -/
@[expose] def potential (D : ℕ) (ls : List (Level α β)) : ℕ :=
  (ls.map fun l ↦ l.weight * (D - Nat.log2 l.weight)).sum

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem potential_cons (D : ℕ) (l : Level α β) (ls : List (Level α β)) :
    potential D (l :: ls) = l.weight * (D - Nat.log2 l.weight) + potential D ls := by
  simp [potential]

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
@[simp] theorem potential_nil (D : ℕ) : potential D ([] : List (Level α β)) = 0 := rfl

/-- Every key of the levels satisfies `Q`. -/
@[expose] def KeysIn (Q : α → Prop) (ls : List (Level α β)) : Prop :=
  ∀ l ∈ ls, ∀ e ∈ l.entries, Q e.1

theorem keysIn_merge {Q : α → Prop} {l l' : Level α β} (h : KeysIn Q [l, l']) :
    ∀ e ∈ (l.merge l').entries, Q e.1 := by
  intro e he
  simp only [Level.merge, List.mem_toArray] at he
  rcases mem_mergeNewer he with h1 | h1
  · exact h l (by simp) e (by simpa using h1)
  · exact h l' (by simp) e (by simpa using h1)

/-- The key step of the potential: two levels of weight `2^e` merged, at most `2^(e+1)`
entries paid `b` each, are paid by the potential's drop. -/
theorem merge_potential_le (b D e s s' : ℕ) (hD : e + 1 ≤ D) (hs : s ≤ 2 ^ e) (hs' : s' ≤ 2 ^ e) :
    b * (s + s') + b * (2 ^ (e + 1) * (D - (e + 1))) ≤
      b * (2 ^ e * (D - e)) + b * (2 ^ e * (D - e)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hD
  have e1 : e + 1 + t - (e + 1) = t := by omega
  have e2 : e + 1 + t - e = t + 1 := by omega
  rw [e1, e2, pow_succ]
  have : b * (s + s') ≤ b * (2 * 2 ^ e) := Nat.mul_le_mul_left b (by omega)
  nlinarith

/-- **An insertion's carry, amortized**: `carry l ls` pays `a` per level it visits and `b` per
entry it merges; then its price and `b` times the potential after are at most `b` times the
potential before, `b·w·(D − log₂ w)` for the new level `l` of weight `w`, and `a` per level. -/
theorem carry_amortized (Q : α → Prop) (C : Level α β → List (Level α β) → ℕ) (a b D : ℕ)
    (hnil : ∀ l, l.weight ≤ 2 ^ D → C l [] ≤ a)
    (hne : ∀ l l' ls, l.weight ≤ 2 ^ D → l'.weight ≤ 2 ^ D → l.weight ≠ l'.weight →
      C l (l' :: ls) ≤ a)
    (heq : ∀ l l' ls, l.weight ≤ 2 ^ D → l.weight = l'.weight → KeysIn Q [l, l'] →
      C l (l' :: ls) ≤ a + b * (l.entries.size + l'.entries.size) + C (l.merge l') ls) :
    ∀ (ls : List (Level α β)) (l : Level α β), LevelsGood ls → LevelGood l →
      (∀ l' ∈ ls, l.weight ≤ l'.weight) → KeysIn Q (l :: ls) →
      l.weight + (ls.map (·.weight)).sum ≤ 2 ^ D →
      C l ls + b * potential D (carry l ls) ≤
        b * potential D ls + b * (l.weight * (D - Nat.log2 l.weight)) + a * (ls.length + 1) := by
  intro ls
  induction ls with
  | nil =>
    intro l _ _ _ _ hw
    have := hnil l (by simpa using hw)
    simp only [carry, potential_cons, potential_nil, List.length_nil]
    nlinarith
  | cons l' ls ih =>
    intro l hls hl hle hQ hw
    simp only [List.map_cons, List.sum_cons] at hw
    have hl'w : l'.weight ≤ 2 ^ D := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.weight)) (List.mem_cons_self (a := l') (l := ls)))
      simp only [List.map_cons, List.sum_cons] at this
      omega
    rw [carry]
    split
    · rename_i heqw
      obtain ⟨⟨e, he⟩, hs⟩ := hl
      obtain ⟨hpw, hgood⟩ := hls
      rw [List.map_cons, List.pairwise_cons] at hpw
      have hs' := (hgood l' (by simp)).2
      have hmw : (l.merge l').weight = 2 ^ (e + 1) := by
        simp only [Level.merge]; rw [pow_succ]; omega
      have hm : LevelGood (l.merge l') := by
        refine ⟨⟨e + 1, hmw⟩, ?_⟩
        simp only [Level.merge, List.size_toArray]
        have := length_mergeNewer_le l.entries.toList l'.entries.toList
        simp only [Array.length_toList] at this
        omega
      have hle' : ∀ l'' ∈ ls, (l.merge l').weight ≤ l''.weight := by
        intro l'' hl''
        have hlt := hpw.1 l''.weight (List.mem_map_of_mem hl'')
        obtain ⟨⟨f, hf⟩, -⟩ := hgood l'' (by simp [hl''])
        rw [hmw, hf]
        exact pow_two_le_of_lt (by rw [← he, ← hf, heqw]; exact hlt)
      have hQ2 : KeysIn Q [l, l'] := fun x hx ↦ hQ x (by simp at hx ⊢; tauto)
      have hQ' : KeysIn Q (l.merge l' :: ls) := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact keysIn_merge hQ2
        · exact hQ x (by simp [hx])
      have hw' : (l.merge l').weight + (ls.map (·.weight)).sum ≤ 2 ^ D := by
        simp only [Level.merge]; omega
      have ih' := ih (l.merge l') ⟨hpw.2, fun x hx ↦ hgood x (by simp [hx])⟩ hm hle' hQ' hw'
      have hc := heq l l' ls (by omega) heqw hQ2
      rw [hmw, Nat.log2_two_pow] at ih'
      rw [potential_cons, ← heqw, he, Nat.log2_two_pow]
      have hD : e + 1 ≤ D := by
        have : 2 ^ (e + 1) ≤ 2 ^ D := by rw [pow_succ]; omega
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
      have hkey := merge_potential_le b D e l.entries.size l'.entries.size hD (by omega) (by omega)
      simp only [List.length_cons]
      nlinarith
    · rename_i hne'
      have := hne l l' ls (by omega) hl'w hne'
      simp only [potential_cons, List.length_cons]
      nlinarith

/-- **An insertion, amortized**: the carry of a new level `l` of weight `1` and one entry (the
level `SortedMap.insert` makes) into a good map of fewer than `2^D` insertions pays
`b·D + a·(levels + 1)` amortized. -/
theorem insert_amortized (Q : α → Prop) (C : Level α β → List (Level α β) → ℕ) (a b D : ℕ)
    (hnil : ∀ l, l.weight ≤ 2 ^ D → C l [] ≤ a)
    (hne : ∀ l l' ls, l.weight ≤ 2 ^ D → l'.weight ≤ 2 ^ D → l.weight ≠ l'.weight →
      C l (l' :: ls) ≤ a)
    (heq : ∀ l l' ls, l.weight ≤ 2 ^ D → l.weight = l'.weight → KeysIn Q [l, l'] →
      C l (l' :: ls) ≤ a + b * (l.entries.size + l'.entries.size) + C (l.merge l') ls)
    (m : SortedMap α β) (hm : smGood m) (hQ : KeysIn Q m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level α β) (hw : l.weight = 1) (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, Q e.1) :
    C l m.levels + b * potential D (carry l m.levels) ≤
      b * potential D m.levels + b * D + a * (m.levels.length + 1) := by
  have hle : ∀ l' ∈ m.levels, l.weight ≤ l'.weight := by
    intro l' hl'
    obtain ⟨⟨e, he⟩, -⟩ := hm.2 l' hl'
    rw [he, hw]; exact Nat.one_le_two_pow
  have h := carry_amortized Q C a b D hnil hne heq m.levels l hm ⟨⟨0, hw⟩, by omega⟩ hle (by
      intro l' hl e he
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hk e he
      · exact hQ l' hl e he) (by unfold smWeightSum at hN; omega)
  have h1 : Nat.log2 1 = 0 := Nat.log2_two_pow (n := 0)
  rw [hw, h1, Nat.sub_zero, Nat.one_mul] at h
  exact h

/-- An insertion keeps the keys in `Q`. -/
theorem keysIn_insert {Q : α → Prop} {m : SortedMap α β} (hQ : KeysIn Q m.levels) {k : α}
    (hk : Q k) (v : β) : KeysIn Q (m.insert k v).levels := by
  unfold SortedMap.insert
  have : ∀ (ls : List (Level α β)) (l : Level α β), KeysIn Q (l :: ls) → KeysIn Q (carry l ls) := by
    intro ls
    induction ls with
    | nil => intro l h; simpa [carry] using h
    | cons l' ls ih =>
      intro l h
      rw [carry]
      split
      · refine ih _ fun x hx ↦ ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · exact keysIn_merge fun y hy ↦ h y (by simp at hy ⊢; tauto)
        · exact h x (by simp [hx])
      · exact h
  refine this _ _ fun l hl e he ↦ ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · simp at he; rw [he]; exact hk
  · exact hQ l hl e he

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
/-- A good map's levels: each of at most `2^D` entries and weight, and at most `D` of them, below
`2^D` insertions. -/
theorem smGood_levels_le {m : SortedMap α β} (hm : smGood m) {D : ℕ} (hN : smWeightSum m < 2 ^ D) :
    m.levels.length ≤ D ∧ ∀ l ∈ m.levels, l.entries.size ≤ l.weight ∧ l.weight ≤ 2 ^ D := by
  refine ⟨?_, fun l hl ↦ ⟨(hm.2 l hl).2, ?_⟩⟩
  · have := sm_two_pow_levels_le hm
    have h2 : 2 ^ m.levels.length ≤ 2 ^ D := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.weight)) hl)
    unfold smWeightSum at hN
    omega

end Amortized

/-! ## The compiled search and merge, for any key and value types -/

section Compiled

variable (P : MachineProgram) {κ β : Type} [Ord κ] [MachineEncoding κ] [MachineEncoding β]

/-- The price recurrence of `searchIn` compiled to function `i`, its keys compared by `compareLex`
(function `j`) with the closure `c`: its `costEq`'s right side. -/
@[expose] noncomputable def searchRec (i j c : ℕ) (t : Array (κ × β)) (k : κ) (lo hi : ℕ) : ℕ :=
  (max (limbCount lo) (limbCount hi) +
      if lo < hi then
        ((max (limbCount (lo + hi)) (max (limbCount lo) (limbCount hi)) + limbCount (lo + hi) +
              max (limbCount ((lo + hi) / 2)) (limbCount t.size) +
            if (lo + hi) / 2 < t.size then
              max (limbCount (lo + hi)) (max (limbCount lo) (limbCount hi)) + limbCount (lo + hi) + 8
            else 1) +
          Option.casesOn (motive := fun _ ↦ ℕ) t[(lo + hi) / 2]? 1 fun val ↦
            machineCost P j [.closure c [], encodeValue val.1, encodeValue k] +
              Ordering.casesOn (motive := fun _ ↦ ℕ) (compare val.1 k)
                (max (limbCount (lo + hi)) (max (limbCount lo) (limbCount hi)) + limbCount (lo + hi) +
                    max (limbCount ((lo + hi) / 2 + 1)) (limbCount ((lo + hi) / 2)) +
                  machineCost P i [encodeValue t, encodeValue k, encodeValue ((lo + hi) / 2 + 1),
                    encodeValue hi] + 8)
                4
                (max (limbCount (lo + hi)) (max (limbCount lo) (limbCount hi)) + limbCount (lo + hi) +
                  machineCost P i [encodeValue t, encodeValue k, encodeValue lo, encodeValue ((lo + hi) / 2)] +
                  7) + 7) + 7
      else 1) + 3

/-- **The binary search of `k`** (`searchIn` compiled to function `i`, of recurrence `searchRec`),
each comparison at most `C`: at most `S·(log₂(hi − lo) + 2)` for any `S ≥ C + 33 + 9·W`, `W` a bound
of the limbs of the positions (up to `2·H`). -/
theorem searchIn_cost_of (i j c : ℕ) (t : Array (κ × β)) (k : κ) (H W C S : ℕ)
    (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W) (hts : t.size ≤ H)
    (hEq : ∀ lo hi, machineCost P i [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] =
      searchRec P i j c t k lo hi)
    (hcmp : ∀ x : κ, machineCost P j [.closure c [], encodeValue x, encodeValue k] ≤ C)
    (hS : C + 33 + 9 * W ≤ S) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P i [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        S * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P i [encodeValue t, encodeValue k, encodeValue x.1, encodeValue x.2])
    (C + 33 + 9 * W) (C + 33 + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith [Nat.mul_le_mul_right (Nat.log2 (hi - lo) + 2) hS]
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [hEq, searchRec]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs [hW]
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [hEq, searchRec]
    simp only [show lo < hi by omega, ↓reduceIte]
    limbs [hW]
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none => left; dsimp only; split_ifs <;> omega
    | some v =>
      have hc := hcmp v.1
      dsimp only
      generalize compare v.1 k = o2
      cases o2
      · exact .inr ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega,
          by dsimp only; split_ifs <;> omega⟩
      · left; dsimp only; split_ifs <;> omega
      · exact .inr ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega,
          by dsimp only; split_ifs <;> omega⟩

/-- The price recurrence of `mergeNewer` compiled to function `i` on a nonempty first list, its keys
compared by `compareLex` (function `j`) with the closure `c`: its `costEq_cons`'s right side. -/
@[expose] noncomputable def mergeNewerRec (i j c : ℕ) (x : κ × β) (a b : List (κ × β)) : ℕ :=
  (List.casesOn (motive := fun _ ↦ ℕ) b 5 fun y b ↦
      machineCost P j [.closure c [], encodeValue x.1, encodeValue y.1] +
        Ordering.casesOn (motive := fun _ ↦ ℕ) (compare x.1 y.1)
          (machineCost P i [encodeValue a, encodeValue (y :: b)] + 11)
          (machineCost P i [encodeValue a, encodeValue b] + 7)
          (machineCost P i [encodeValue (x :: a), encodeValue b] + 11) + 9) + 6

/-- **`mergeNewer`** (compiled to function `i`, of recurrence `mergeNewerRec`), each comparison
with a key of the second list (of property `Q`) at most `C`: at most `C + 26` per entry and `3`. -/
theorem mergeNewer_cost_of (i j c : ℕ) (Q : κ → Prop) (C : ℕ)
    (hnil : ∀ b : List (κ × β), machineCost P i [encodeValue ([] : List (κ × β)), encodeValue b] = 3)
    (hcons : ∀ x (a b : List (κ × β)),
      machineCost P i [encodeValue (x :: a), encodeValue b] = mergeNewerRec P i j c x a b)
    (hcmp : ∀ x y : κ, Q y → machineCost P j [.closure c [], encodeValue x, encodeValue y] ≤ C) :
    ∀ (n : ℕ) (a b : List (κ × β)), a.length + b.length = n → (∀ e ∈ b, Q e.1) →
      machineCost P i [encodeValue a, encodeValue b] ≤ (C + 26) * n + 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => have := hnil b; omega
  | cons x a =>
    rw [hcons, mergeNewerRec]
    cases b with
    | nil => simp at hn ⊢; have : 1 ≤ n := (by omega); nlinarith
    | cons y b =>
      dsimp only
      have hc := hcmp x.1 y.1 (hb y (by simp))
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      generalize compare x.1 y.1 = o
      subst hn
      cases o <;> dsimp only <;> nlinarith

/-- **Two levels merged** (`Level.merge` compiled to function `i`, merging their entries with
function `im`, of price at most `c` per entry and `3`): at most `c + 4` per entry and `18 + W`, `W` a
bound of the weights' limbs. -/
theorem levelMerge_cost_of (i im : ℕ) (Q : κ → Prop) (c W : ℕ)
    (hEq : ∀ l l' : Level κ β, machineCost P i [encodeValue l, encodeValue l'] =
      max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) +
        3 * l.entries.size + 3 * l'.entries.size +
        machineCost P im [encodeValue l.entries.toList, encodeValue l'.entries.toList] +
        (mergeNewer l.entries.toList l'.entries.toList).length + 15)
    (hm : ∀ a b : List (κ × β), (∀ e ∈ a, Q e.1) → (∀ e ∈ b, Q e.1) →
      machineCost P im [encodeValue a, encodeValue b] ≤ c * (a.length + b.length) + 3)
    (l l' : Level κ β) (hQ : KeysIn Q [l, l']) (hw : limbCount l.weight ≤ W)
    (hw' : limbCount l'.weight ≤ W) (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P i [encodeValue l, encodeValue l'] ≤
      18 + W + (c + 4) * (l.entries.size + l'.entries.size) := by
  rw [hEq]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have h := hm l.entries.toList l'.entries.toList (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at h hlen
  nlinarith

/-- **An insertion, amortized** (`carry` compiled to function `i`, merging two levels with function
`iL` at most `18 + W` and `b` per entry): `b·D + (32 + 2·W)·(levels + 1)` plus the drop of `b` times
the potential. -/
theorem carry_amortized_of [Std.TransOrd κ] [Std.LawfulEqOrd κ] (i iL : ℕ) (Q : κ → Prop) (b D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hnil : ∀ l : Level κ β, machineCost P i [encodeValue l, encodeValue ([] : List (Level κ β))] = 7)
    (hcons : ∀ (l l' : Level κ β) ls, machineCost P i [encodeValue l, encodeValue (l' :: ls)] =
      (max (limbCount l.weight) (limbCount l'.weight) +
        if l.weight = l'.weight then
          machineCost P iL [encodeValue l, encodeValue l'] +
            machineCost P i [encodeValue (l.merge l'), encodeValue ls] + 5
        else 9) + 9)
    (hL : ∀ l l' : Level κ β, KeysIn Q [l, l'] → limbCount l.weight ≤ W → limbCount l'.weight ≤ W →
      limbCount (l.weight + l'.weight) ≤ W →
      machineCost P iL [encodeValue l, encodeValue l'] ≤ 18 + W + b * (l.entries.size + l'.entries.size))
    (m : SortedMap κ β) (hm : smGood m) (hQ : KeysIn Q m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level κ β) (hw : l.weight = 1) (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, Q e.1) :
    machineCost P i [encodeValue l, encodeValue m.levels] + b * potential D (carry l m.levels) ≤
      b * potential D m.levels + b * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized Q (fun l ls ↦ machineCost P i [encodeValue l, encodeValue ls]) (32 + 2 * W) b
    D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; have := hnil l; omega
  · intro l l' ls h1 h2 hne
    rw [hcons]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := hL l l' hQ2 (hW _ (by omega)) (hW _ (by omega)) (hW _ (by omega))
    rw [hcons]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

/-- **A lookup** (`SortedMap.get?` compiled to function `i`: the `findSome?` `f`, of price `hfs`,
over the levels with the closure `c`, which searches a level with function `j`), each level of at
most `H` entries and its search at most `S·(log₂ |entries| + 2)`: at most
`|levels|·(20 + S·(log₂ H + 2)) + 9`. -/
theorem get_cost_of (i f c j : ℕ) (m : SortedMap κ β) (k : κ) (H S : ℕ)
    (hEq : machineCost P i [encodeValue m, encodeValue k] =
      machineCost P f [.closure c [encodeValue k], encodeValue m.levels] + 6)
    (hfs : ∀ B, (∀ l ∈ m.levels, appCost P (.closure c [encodeValue k]) [encodeValue l] ≤ B) →
      machineCost P f [.closure c [encodeValue k], encodeValue m.levels] ≤ (B + 11) * m.levels.length + 3)
    (hc : ∀ l : Level κ β, machineCost P c [encodeValue k, encodeValue l] =
      machineCost P j [encodeValue l.entries, encodeValue k, encodeValue (0 : ℕ),
        encodeValue l.entries.size] + 8)
    (hs : ∀ l ∈ m.levels, machineCost P j [encodeValue l.entries, encodeValue k, encodeValue (0 : ℕ),
      encodeValue l.entries.size] ≤ S * (Nat.log2 (l.entries.size - 0) + 2))
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) :
    machineCost P i [encodeValue m, encodeValue k] ≤ m.levels.length * (20 + S * (Nat.log2 H + 2)) + 9 := by
  have := hfs (9 + S * (Nat.log2 H + 2)) fun l hl ↦ by
    rw [appCost_fn, List.length_singleton, List.singleton_append, hc]
    have := hs l hl
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : S * (Nat.log2 (l.entries.size - 0) + 2) ≤ S * (Nat.log2 H + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hEq]
  nlinarith

end Compiled

/-! ## A fold, amortized -/

section Fold

variable (P : MachineProgram) {α β : Type} [MachineEncoding α] [MachineEncoding β]

/-- **`List.foldl`, amortized** (`listFoldl`): a step at an accumulator of invariant `I acc r`
(`r` the elements left) pays at most `A` plus the drop of a potential `Φ`; then the fold pays at
most `Φ init + (A + 11)·n + 3`. -/
theorem listFoldl_amortized (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (A : ℕ) (Φ : α → ℕ)
    (I : α → ℕ → Prop) :
    ∀ (l : List β) (init : α), I init l.length →
      (∀ acc r, I acc (r + 1) → ∀ b ∈ l, I (f acc b) r ∧
        appCost P fVal [encodeValue acc, encodeValue b] + Φ (f acc b) ≤ Φ acc + A) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ Φ init + (A + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro init _ _; rw [listFoldl.costEq_nil P hP f fVal hf]; omega
  | cons b l ih =>
    intro init hI hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hB init l.length (by simpa using hI) b (by simp)
    have h1 := ih (f init b) hI' (fun acc r hacc b' hb ↦ hB acc r hacc b' (by simp [hb]))
    simp only [List.length_cons]
    nlinarith

end Fold

end

end LeanVM.Cost.Bounds
