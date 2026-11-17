module

public import Quantum.Sponge.Indifferentiability.Fix
public import Quantum.Sponge.Simulate

@[expose] public section

/-!
# The converters `C_1` and `C_2` as quantum programs

Section 5.2 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731). A call
`|t, y, e⟩ ↦ |t, y + C^f t, e⟩` of the oracle `C_1^f = toMsponge f` (or `C_2^g = toSponge g`) on
bounded messages `Msg X l` is made with `2 * l - 1` calls of `f` (`convCall`), uniformly in the
length of `t`, which is in superposition.

Both converters run the fold `fixGen op` (`op r c = c - r` gives `fixInv`, `op r b = r + b` gives
`fixFwd`). Ancilla rates `r_0, …, r_{l-2}` start at `0`. Call `k < l - 1` adds into `r_k` the
oracle on the list `fixQuery op k`, whose block `j` is `op ρ_j t_j` for the blocks `j ≤ k` of `t`,
with `ρ_0 = 0` and `ρ_{j+1} = r_j`; it is always a valid message. Call `l - 1` adds the oracle on
the whole list into `y`. The rates are then removed by the same calls in reverse, subtracting,
and the zero ancilla is dropped by `coGate`.

Each call is `lensCall`: copy the query and the target block into a fresh query register (an
isometry), call the oracle there, and read the copy back by the adjoint isometry.

## Main statements

* `runsAs_convCall` (`runsAs_c1Call`, `runsAs_c2Call`): against the oracle of `f`, the circuit
  runs as the call of `convOracle op f` (`toMsponge f`, `toSponge g`).
* `isQueryBound_convCall`: it makes at most `2 * l - 1` calls.
* `run_convertCalls` (`run_convertC1`, `run_convertC2`): substituting the circuit for every call
  of a program, against `f`, runs as the program against `convOracle op f`; `evalDistMap` and
  lossless versions.
* `isQueryBound_convertCalls`, `isTotalQueryBound_convertCalls`: `q` calls become
  `(2 * l - 1) * q`.
-/

open IPFunctor

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## The generic fold -/

section fold

variable {X : Type} [AddCommGroup X]

/-- The fold behind `fixFwd` and `fixInv`: block `c` enters the output list as `op r c` for the
current rate `r`, and the rate becomes `F` of the output list so far. -/
def fixGen (op : X → X → X) (F : List X → X) (t : List X) : X × List X :=
  t.foldl (fun p c ↦ (F (p.2 ++ [op p.1 c]), p.2 ++ [op p.1 c])) (0, [])

theorem fixGen_sub (F : List X → X) (t : List X) :
    fixGen (fun r c ↦ c - r) F t = fixInv F t :=
  rfl

theorem fixGen_add (F : List X → X) (t : List X) :
    fixGen (fun r b ↦ r + b) F t = fixFwd F t :=
  rfl

@[simp] theorem fixGen_nil (op : X → X → X) (F : List X → X) : fixGen op F [] = (0, []) :=
  rfl

theorem fixGen_append_singleton (op : X → X → X) (F : List X → X) (t : List X) (c : X) :
    fixGen op F (t ++ [c]) =
      (F ((fixGen op F t).2 ++ [op (fixGen op F t).1 c]),
        (fixGen op F t).2 ++ [op (fixGen op F t).1 c]) := by
  simp [fixGen, List.foldl_append]

theorem fixGen_fst_of_ne_nil (op : X → X → X) (F : List X → X) {t : List X} (ht : t ≠ []) :
    (fixGen op F t).1 = F (fixGen op F t).2 := by
  obtain ⟨t, c, rfl⟩ := List.eq_nil_or_concat t |>.resolve_left ht
  simp [fixGen_append_singleton]

/-- The output list of the fold for given rates `ρ`: block `j` is `op (ρ j) t_j`. -/
def fixOut (op : X → X → X) (ρ : ℕ → X) (t : List X) : List X :=
  t.mapIdx fun j c ↦ op (ρ j) c

omit [AddCommGroup X] in
theorem length_fixOut (op : X → X → X) (ρ : ℕ → X) (t : List X) :
    (fixOut op ρ t).length = t.length :=
  List.length_mapIdx

omit [AddCommGroup X] in
theorem fixOut_append_singleton (op : X → X → X) (ρ : ℕ → X) (t : List X) (c : X) :
    fixOut op ρ (t ++ [c]) = fixOut op ρ t ++ [op (ρ t.length) c] :=
  List.mapIdx_concat

omit [AddCommGroup X] in
/-- `fixOut` reads the rates only below the length of the list. -/
theorem fixOut_congr (op : X → X → X) {ρ ρ' : ℕ → X} {t : List X}
    (h : ∀ j < t.length, ρ j = ρ' j) : fixOut op ρ t = fixOut op ρ' t := by
  refine List.ext_getElem (by simp only [length_fixOut]) fun j h1 _ ↦ ?_
  simp only [fixOut, List.getElem_mapIdx]
  rw [h j (by rwa [length_fixOut] at h1)]

/-- With the rates of the fold, `fixOut` is the fold's output list. -/
theorem fixOut_eq_fixGen (op : X → X → X) (F : List X → X) {ρ : ℕ → X} {t : List X}
    (h : ∀ j < t.length, ρ j = (fixGen op F (t.take j)).1) : fixOut op ρ t = (fixGen op F t).2 := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t c ih =>
    have ih := ih fun j hj ↦ by
      rw [h j (by simp; omega), List.take_append_of_le_length hj.le]
    rw [fixOut_append_singleton, ih, fixGen_append_singleton, h t.length (by simp),
      List.take_append_of_le_length le_rfl, List.take_length]

end fold

/-! ## Lenses onto one block of a basis state -/

/-- A lens onto an `X`-valued component of a basis state. -/
structure BlockLens (X S : Type) where
  /-- The component. -/
  get : S → X
  /-- The state with the component replaced. -/
  set : S → X → S
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

/-- The lens onto the negated component. -/
def BlockLens.neg {X S : Type} [AddCommGroup X] (σ : BlockLens X S) : BlockLens X S where
  get s := -σ.get s
  set s v := σ.set s (-v)
  get_set s v := by rw [σ.get_set, neg_neg]
  set_get s := by rw [neg_neg, σ.set_get]
  set_set s v w := σ.set_set s (-v) (-w)

/-! ## The ancilla state and its classical evolution -/

section state

variable {X : Type} [AddCommGroup X] {l : ℕ}

/-- `C^f` for the fold `fixGen op`: `toMsponge` for `op r c = c - r`, `toSponge` for
`op r b = r + b`. -/
def convOracle (op : X → X → X) (f : Msg X l → X) : Msg X l → X :=
  fun t ↦ (fixGen op (extMsg f) t.1).1

theorem convOracle_sub (f : Msg X l → X) : convOracle (fun r c ↦ c - r) f = toMsponge f :=
  rfl

theorem convOracle_add (f : Msg X l → X) : convOracle (fun r b ↦ r + b) f = toSponge f :=
  rfl

/-- The basis of the converter's work register: the ancilla rates `r_0, …, r_{l-2}`, then the
query register `(t, y)` and the remainder. -/
abbrev FixState (X : Type) (l : ℕ) (E : Type) : Type :=
  (Fin (l - 1) → X) × ((Msg X l × X) × E)

/-- The rate before block `j`: `0` for `j = 0`, the ancilla `r_{j-1}` otherwise. -/
def ancRate {n : ℕ} (r : Fin n → X) : ℕ → X
  | 0 => 0
  | j + 1 => if h : j < n then r ⟨j, h⟩ else 0

/-- The query of call `k`: the output list of the blocks `j ≤ k` of `t` with the ancilla
rates. -/
def fixQuery (op : X → X → X) (k : ℕ) {E : Type} (s : FixState X l E) : Msg X l :=
  ⟨fixOut op (ancRate s.1) (s.2.1.1.1.take (k + 1)),
    List.ne_nil_of_length_pos (by
      rw [length_fixOut, List.length_take]
      have := List.length_pos_iff.2 s.2.1.1.2.1
      omega),
    by
      rw [length_fixOut, List.length_take]
      have := s.2.1.1.2.2
      omega⟩

/-- `fixQuery op k` reads only the ancillas `r_j` with `j < k`. -/
theorem fixQuery_congr (op : X → X → X) (k : ℕ) {E : Type} {r r' : Fin (l - 1) → X}
    (c : (Msg X l × X) × E) (h : ∀ j : Fin (l - 1), (j : ℕ) < k → r j = r' j) :
    fixQuery op k (r, c) = fixQuery op k (r', c) := by
  refine Subtype.ext (fixOut_congr op fun m hm ↦ ?_)
  rw [List.length_take] at hm
  cases m with
  | zero => rfl
  | succ j =>
    show (if h : j < l - 1 then r ⟨j, h⟩ else 0) = if h : j < l - 1 then r' ⟨j, h⟩ else 0
    split_ifs with hj
    · exact h _ (show j < k by omega)
    · rfl

/-- The rate of the fold of `f` after the blocks `j' ≤ j` of `t`. -/
def fixRate (op : X → X → X) (f : Msg X l → X) (t : List X) (j : ℕ) : X :=
  (fixGen op (extMsg f) (t.take (j + 1))).1

/-- The ancillas after the first `k` calls: the rates of the fold below `k`, zero above. -/
def fixRates (op : X → X → X) (f : Msg X l → X) (t : List X) (k : ℕ) : Fin (l - 1) → X :=
  fun j ↦ if (j : ℕ) < k then fixRate op f t j else 0

theorem fixRates_of_lt (op : X → X → X) (f : Msg X l → X) (t : List X) {k : ℕ}
    {j : Fin (l - 1)} (h : (j : ℕ) < k) : fixRates op f t k j = fixRate op f t j :=
  ite_eq_left h

theorem fixRates_self (op : X → X → X) (f : Msg X l → X) (t : List X) {k : ℕ}
    (h : k < l - 1) : fixRates op f t k ⟨k, h⟩ = 0 :=
  ite_eq_right (lt_irrefl k)

theorem fixRates_zero (op : X → X → X) (f : Msg X l → X) (t : List X) :
    fixRates op f t 0 = 0 :=
  funext fun _ ↦ ite_eq_right (Nat.not_lt_zero _)

theorem update_fixRates (op : X → X → X) (f : Msg X l → X) (t : List X) {k : ℕ}
    (h : k < l - 1) :
    Function.update (fixRates op f t k) ⟨k, h⟩ (fixRate op f t k) = fixRates op f t (k + 1) := by
  funext j
  by_cases hj : j = ⟨k, h⟩
  · subst hj
    rw [Function.update_self]
    exact (ite_eq_left (Nat.lt_succ_self k)).symm
  · have hj' : (j : ℕ) ≠ k := fun h' ↦ hj (Fin.ext h')
    rw [Function.update_of_ne hj]
    simp only [fixRates]
    split_ifs <;> first | rfl | omega

theorem update_fixRates_succ (op : X → X → X) (f : Msg X l → X) (t : List X) {k : ℕ}
    (h : k < l - 1) :
    Function.update (fixRates op f t (k + 1)) ⟨k, h⟩ 0 = fixRates op f t k := by
  funext j
  by_cases hj : j = ⟨k, h⟩
  · subst hj
    rw [Function.update_self]
    exact (ite_eq_right (lt_irrefl k)).symm
  · have hj' : (j : ℕ) ≠ k := fun h' ↦ hj (Fin.ext h')
    rw [Function.update_of_ne hj]
    simp only [fixRates]
    split_ifs <;> first | rfl | omega

/-- With the rates of the fold below `k`, the query of call `k` is the fold's output list on the
blocks `j ≤ k`. -/
theorem fixQuery_val (op : X → X → X) (f : Msg X l → X) (k : ℕ) {E : Type}
    {r : Fin (l - 1) → X} (t : Msg X l) (y : X) (e : E)
    (hr : ∀ j : Fin (l - 1), (j : ℕ) < k → r j = fixRate op f t.1 j) :
    (fixQuery op k (r, ((t, y), e))).1 = (fixGen op (extMsg f) (t.1.take (k + 1))).2 := by
  refine fixOut_eq_fixGen op _ fun m hm ↦ ?_
  have ht := t.2.2
  rw [List.length_take] at hm
  change m < min (k + 1) t.1.length at hm
  rw [List.take_take]
  cases m with
  | zero => rfl
  | succ j =>
    have hj : j < l - 1 := by omega
    show (if h : j < l - 1 then r ⟨j, h⟩ else 0) = _
    rw [dite_eq_left hj, hr ⟨j, hj⟩ (show j < k by omega), fixRate,
      Nat.min_eq_left (show j + 1 ≤ k + 1 by omega)]

/-- With the rates of the fold below `k`, the oracle on the query of call `k` is the next rate. -/
theorem apply_fixQuery (op : X → X → X) (f : Msg X l → X) (k : ℕ) {E : Type}
    {r : Fin (l - 1) → X} (t : Msg X l) (y : X) (e : E)
    (hr : ∀ j : Fin (l - 1), (j : ℕ) < k → r j = fixRate op f t.1 j) :
    f (fixQuery op k (r, ((t, y), e))) = fixRate op f t.1 k := by
  have hne : t.1.take (k + 1) ≠ [] := by simpa using t.2.1
  have h1 : f (fixQuery op k (r, ((t, y), e))) = extMsg f (fixQuery op k (r, ((t, y), e))).1 :=
    (extMsg_of_le f (fixQuery op k (r, ((t, y), e))).2.1
      (fixQuery op k (r, ((t, y), e))).2.2).symm
  rw [h1, fixQuery_val op f k t y e hr, fixRate, fixGen_fst_of_ne_nil op _ hne]

theorem fixRate_last (op : X → X → X) (f : Msg X l → X) (t : Msg X l) :
    fixRate op f t.1 (l - 1) = convOracle op f t := by
  have hl : 1 ≤ l := by
    have := List.length_pos_iff.2 t.2.1
    have := t.2.2
    omega
  rw [fixRate, Nat.sub_add_cancel hl, List.take_of_length_le t.2.2]
  rfl

/-- The lens onto the ancilla `r_i`. -/
def rateLens {E : Type} (i : Fin (l - 1)) : BlockLens X (FixState X l E) where
  get s := s.1 i
  set s v := (Function.update s.1 i v, s.2)
  get_set _ _ := Function.update_self ..
  set_get s := by simp
  set_set s v w := by simp

/-- The lens onto the response `y`. -/
def respLens {E : Type} : BlockLens X (FixState X l E) where
  get s := s.2.1.2
  set s v := (s.1, ((s.2.1.1, v), s.2.2))
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The target of call `k`: the ancilla `r_k` for `k < l - 1`, the response otherwise. -/
def fixLens {E : Type} (k : ℕ) : BlockLens X (FixState X l E) :=
  if h : k < l - 1 then rateLens ⟨k, h⟩ else respLens

omit [AddCommGroup X] in
theorem fixLens_of_lt {E : Type} {k : ℕ} (h : k < l - 1) :
    fixLens (X := X) (l := l) (E := E) k = rateLens ⟨k, h⟩ :=
  dite_eq_left h

omit [AddCommGroup X] in
theorem fixLens_of_not_lt {E : Type} {k : ℕ} (h : ¬k < l - 1) :
    fixLens (X := X) (l := l) (E := E) k = respLens :=
  dite_eq_right h

/-- The query of call `k` does not read the target of call `k`. -/
theorem fixQuery_set_fixLens (op : X → X → X) (k : ℕ) {E : Type} (s : FixState X l E) (v : X) :
    fixQuery op k ((fixLens k).set s v) = fixQuery op k s := by
  by_cases h : k < l - 1
  · rw [fixLens_of_lt h]
    exact fixQuery_congr op k (r := Function.update s.1 ⟨k, h⟩ v) (r' := s.1) s.2 fun j hj ↦
      Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hj)) _ _
  · rw [fixLens_of_not_lt h]
    rfl

/-- One call: add the oracle on the query `inp s` into the component `σ`. -/
def lensStep (f : Msg X l → X) {S : Type} (inp : S → Msg X l) (σ : BlockLens X S) (s : S) : S :=
  σ.set s (σ.get s + f (inp s))

/-- A sequence of calls. -/
def lensSteps (f : Msg X l → X) {S : Type} : List ((S → Msg X l) × BlockLens X S) → S → S
  | [] => id
  | c :: cs => lensSteps f cs ∘ lensStep f c.1 c.2

@[simp] theorem lensSteps_nil (f : Msg X l → X) {S : Type} :
    lensSteps f ([] : List ((S → Msg X l) × BlockLens X S)) = id :=
  rfl

@[simp] theorem lensSteps_cons (f : Msg X l → X) {S : Type} (c : (S → Msg X l) × BlockLens X S)
    (cs : List ((S → Msg X l) × BlockLens X S)) :
    lensSteps f (c :: cs) = lensSteps f cs ∘ lensStep f c.1 c.2 :=
  rfl

theorem lensSteps_append (f : Msg X l → X) {S : Type}
    (cs cs' : List ((S → Msg X l) × BlockLens X S)) :
    lensSteps f (cs ++ cs') = lensSteps f cs' ∘ lensSteps f cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.cons_append, lensSteps_cons, lensSteps_cons, ih]
    rfl

theorem lensStep_rateLens (f : Msg X l → X) {E : Type} (inp : FixState X l E → Msg X l)
    (i : Fin (l - 1)) (r : Fin (l - 1) → X) (c : (Msg X l × X) × E) :
    lensStep f inp (rateLens i) (r, c) = (Function.update r i (r i + f (inp (r, c))), c) :=
  rfl

theorem lensStep_neg_rateLens (f : Msg X l → X) {E : Type} (inp : FixState X l E → Msg X l)
    (i : Fin (l - 1)) (r : Fin (l - 1) → X) (c : (Msg X l × X) × E) :
    lensStep f inp (rateLens i).neg (r, c) =
      (Function.update r i (-(-r i + f (inp (r, c)))), c) :=
  rfl

theorem lensStep_respLens (f : Msg X l → X) {E : Type} (inp : FixState X l E → Msg X l)
    (r : Fin (l - 1) → X) (t : Msg X l) (y : X) (e : E) :
    lensStep f inp respLens (r, ((t, y), e)) = (r, ((t, y + f (inp (r, ((t, y), e)))), e)) :=
  rfl

/-- The `2 * l - 1` calls of the converter: calls `0, …, l - 1` forward, then `l - 2, …, 0`
subtracting. -/
def fixCalls (op : X → X → X) (E : Type) :
    List ((FixState X l E → Msg X l) × BlockLens X (FixState X l E)) :=
  (List.range l).map (fun k ↦ (fixQuery op k, fixLens k)) ++
    (List.range (l - 1)).reverse.map fun k ↦ (fixQuery op k, (fixLens k).neg)

theorem length_fixCalls (op : X → X → X) (E : Type) :
    (fixCalls (l := l) op E).length = 2 * l - 1 := by
  simp only [fixCalls, List.length_append, List.length_map, List.length_reverse,
    List.length_range]
  omega

theorem fixCalls_query_set (op : X → X → X) (E : Type) :
    ∀ c ∈ fixCalls (l := l) op E, ∀ s v, c.1 (c.2.set s v) = c.1 s := by
  intro c hc s v
  simp only [fixCalls, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
  · exact fixQuery_set_fixLens op k s v
  · exact fixQuery_set_fixLens op k s (-v)

theorem lensSteps_forward (op : X → X → X) (f : Msg X l → X) {E : Type} (t : Msg X l) (y : X)
    (e : E) {k : ℕ} (hk : k ≤ l - 1) :
    lensSteps f ((List.range k).map fun k ↦ (fixQuery op k, fixLens k)) (0, ((t, y), e)) =
      (fixRates op f t.1 k, ((t, y), e)) := by
  induction k with
  | zero => rw [List.range_zero, List.map_nil, fixRates_zero]; rfl
  | succ k ih =>
    have hk' : k < l - 1 := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, lensSteps_append,
      Function.comp_apply, lensSteps_cons, lensSteps_nil, id_eq]
    rw [ih (by omega), fixLens_of_lt hk', lensStep_rateLens,
      apply_fixQuery op f k (r := fixRates op f t.1 k) t y e fun j hj ↦
        fixRates_of_lt op f _ hj,
      fixRates_self op f t.1 hk', zero_add,
      update_fixRates op f t.1 hk']

theorem lensSteps_backward (op : X → X → X) (f : Msg X l → X) {E : Type} (t : Msg X l) (y : X)
    (e : E) {k : ℕ} (hk : k ≤ l - 1) :
    lensSteps f ((List.range k).reverse.map fun k ↦ (fixQuery op k, (fixLens k).neg))
      (fixRates op f t.1 k, ((t, y), e)) = (0, ((t, y), e)) := by
  induction k with
  | zero => rw [List.range_zero, List.reverse_nil, List.map_nil, fixRates_zero]; rfl
  | succ k ih =>
    have hk' : k < l - 1 := by omega
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.map_cons, lensSteps_cons,
      Function.comp_apply]
    rw [fixLens_of_lt hk', lensStep_neg_rateLens,
      apply_fixQuery op f k (r := fixRates op f t.1 (k + 1)) t y e fun j hj ↦
        fixRates_of_lt op f _ (by omega),
      fixRates_of_lt op f _ (Nat.lt_succ_self k), neg_add_cancel, neg_zero,
      update_fixRates_succ op f t.1 hk', ih (by omega)]

/-- **The calls of the converter compute `C^f`**: from zero ancillas, they add `convOracle op f t`
into the response and return the ancillas to zero. -/
theorem lensSteps_fixCalls (op : X → X → X) (f : Msg X l → X) {E : Type} (t : Msg X l) (y : X)
    (e : E) :
    lensSteps f (fixCalls op E) (0, ((t, y), e)) = (0, ((t, y + convOracle op f t), e)) := by
  have hr : List.range l = List.range (l - 1) ++ [l - 1] := by
    rw [← List.range_succ]
    congr 1
    have := List.length_pos_iff.2 t.2.1
    have := t.2.2
    omega
  rw [fixCalls, lensSteps_append, Function.comp_apply, hr, List.map_append, lensSteps_append,
    Function.comp_apply, lensSteps_forward op f t y e le_rfl]
  simp only [List.map_cons, List.map_nil, lensSteps_cons, lensSteps_nil, Function.comp_apply,
    id_eq]
  rw [fixLens_of_not_lt (lt_irrefl _), lensStep_respLens,
    apply_fixQuery op f (l - 1) (r := fixRates op f t.1 (l - 1)) t y e fun j hj ↦
      fixRates_of_lt op f _ hj,
    fixRate_last, lensSteps_backward op f t _ e le_rfl]

end state

/-! ## Calls of a fixed function as basis maps -/

section qrom

variable {M Y : Type} [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The basis map of a call of `H`: `|m, y, e⟩ ↦ |m, y + H m, e⟩`. -/
def qromCallMap (H : M → Y) {E A D : QReg} (ℓ : A ≃ (qromSpec M Y).In () × E) :
    A × D → QReg.of ((qromSpec M Y).Out () × E) × D :=
  fun q ↦ ((((ℓ q.1).1.1, (ℓ q.1).1.2 + H (ℓ q.1).1.1), (ℓ q.1).2), q.2)

/-- The oracle of `H`'s call is the basis map `qromCallMap`. -/
theorem branch_queryStep_qromCallMap (H : M → Y) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec M Y).In () × E) :
    ((additiveOracleRuntime H).queryStep () E ℓ).branch () =
      MatrixMap.conj (basisMatrix (qromCallMap H ℓ)) := by
  rw [branch_queryStep_of_basis (additiveOracleRuntime H) (i := ()) (r := ())
    (Prod.map (oracleEquiv H) (id : Unit → Unit)) (branch_frame_oracleQuery H Unit) E ℓ]
  rfl

theorem runsAs_qromQuery (H : M → Y) (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec M Y).In () × E) :
    RunsAs (additiveOracleRuntime H)
      (QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := qromSpec M Y) () E ℓ)
      (qromCallMap H ℓ) := by
  rw [RunsAs, QuantumRuntime.run₂_query, SubInstrument.bind, DSubInstrument.branch_bind_unit,
    SubInstrument.branch_pure_self, LinearMap.id_comp]
  exact branch_queryStep_qromCallMap H E ℓ

end qrom

theorem runsAs_pure {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {A : QReg} :
    RunsAs R (QuantumComp₂.pure (L := LocalSig.instruments.{v}) (A := A) ()) id := by
  rw [RunsAs, QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self, basisMatrix_id,
    MatrixMap.conj_one]

theorem isQueryBound_isoGate_spec {spec : QuantumOracleSpec.{0, 0}} {A B : QReg} (f : A → B)
    (hf : Function.Injective f) (b : spec.Port → ℕ) :
    (isoGate.{v} (spec := spec) f hf).IsQueryBound b :=
  fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩

theorem isQueryBound_coGate_spec {spec : QuantumOracleSpec.{0, 0}} {A B : QReg} (f : B → A)
    (hf : Function.Injective f) (b : spec.Port → ℕ) :
    (coGate.{v} (spec := spec) f hf).IsQueryBound b :=
  fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩

/-! ## The circuit -/

section circuit

variable {X : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] {l : ℕ}

/-- The query register and the cleared state that a lens call copies a state into. -/
def lensEnc {S : Type} (inp : S → Msg X l) (σ : BlockLens X S) (s : S) : (Msg X l × X) × S :=
  ((inp s, σ.get s), σ.set s 0)

omit [Fintype X] [DecidableEq X] in
theorem lensEnc_injective {S : Type} (inp : S → Msg X l) (σ : BlockLens X S) :
    Function.Injective (lensEnc inp σ) := fun a b h ↦ by
  have h1 : σ.get a = σ.get b := congrArg (fun p ↦ p.1.2) h
  have h2 : σ.set a 0 = σ.set b 0 := congrArg Prod.snd h
  calc a = σ.set (σ.set a 0) (σ.get a) := by rw [σ.set_set, σ.set_get]
    _ = σ.set (σ.set b 0) (σ.get b) := by rw [h1, h2]
    _ = b := by rw [σ.set_set, σ.set_get]

/-- **One call into a block**: copy the query `inp s` and the block `σ` into a fresh query
register (clearing the block), call the oracle there, and read the copy back. -/
noncomputable def lensCall {S : QReg} (inp : S → Msg X l) (σ : BlockLens X S) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec (Msg X l) X) S S Unit :=
  ((isoGate (B := QReg.of ((qromSpec (Msg X l) X).In () × S)) (lensEnc inp σ)
      (lensEnc_injective inp σ)).bind fun _ ↦
    QuantumComp₂.query (L := LocalSig.instruments.{v}) () S (Equiv.refl _)).bind fun _ ↦
    coGate (A := QReg.of ((qromSpec (Msg X l) X).Out () × S)) (lensEnc inp σ)
      (lensEnc_injective inp σ)

theorem runsAs_lensCall (f : Msg X l → X) {S : QReg} (inp : S → Msg X l) (σ : BlockLens X S)
    (hinp : ∀ s v, inp (σ.set s v) = inp s) :
    RunsAs (additiveOracleRuntime f) (lensCall.{v} inp σ) (Prod.map (lensStep f inp σ) id) := by
  unfold lensCall
  refine ((runsAs_isoGate _ _).bind (runsAs_qromQuery.{v} f S
    (A := QReg.of ((qromSpec (Msg X l) X).In () × S)) (Equiv.refl _))).bind_coGate _ _ _
    fun q ↦ ?_
  obtain ⟨s, d⟩ := q
  simp [qromCallMap, lensEnc, lensStep, hinp, σ.get_set, σ.set_set]

/-- A sequence of lens calls. -/
noncomputable def lensChain {S : QReg} : List ((S → Msg X l) × BlockLens X S) →
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec (Msg X l) X) S S Unit
  | [] => QuantumComp₂.pure ()
  | c :: cs => (lensCall c.1 c.2).bind fun _ ↦ lensChain cs

theorem runsAs_lensChain (f : Msg X l → X) {S : QReg} (cs : List ((S → Msg X l) × BlockLens X S))
    (hcs : ∀ c ∈ cs, ∀ s v, c.1 (c.2.set s v) = c.1 s) :
    RunsAs (additiveOracleRuntime f) (lensChain.{v} cs) (Prod.map (lensSteps f cs) id) := by
  induction cs with
  | nil => exact (runsAs_pure _).congr fun _ ↦ rfl
  | cons c cs ih =>
    exact ((runsAs_lensCall f c.1 c.2 (hcs c List.mem_cons_self)).bind
      (ih fun c' hc' ↦ hcs c' (List.mem_cons_of_mem _ hc'))).congr fun _ ↦ rfl

/-- The work register of the converter. -/
noncomputable abbrev fixReg (X : Type) [Fintype X] [DecidableEq X] (l : ℕ) (E : QReg) : QReg :=
  QReg.of (FixState X l E)

/-- The register of the response of a call beside its remainder. -/
noncomputable abbrev qromCallReg (X : Type) [Fintype X] [DecidableEq X] (l : ℕ) (E : QReg) :
    QReg :=
  QReg.of ((qromSpec (Msg X l) X).Out () × E)

/-- Adjoin zero ancillas to the call's input. -/
def ancIn {E A : QReg} (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) : A → fixReg X l E :=
  fun a ↦ (0, ℓ a)

theorem ancIn_injective {E A : QReg} (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    Function.Injective (ancIn ℓ) :=
  fun _ _ h ↦ ℓ.injective (congrArg Prod.snd h)

/-- The zero ancillas, which the contraction `coGate` removes. -/
def ancOut (E : QReg) : qromCallReg X l E → fixReg X l E :=
  fun c ↦ (0, c)

theorem ancOut_injective (E : QReg) : Function.Injective (ancOut (X := X) (l := l) E) :=
  fun _ _ h ↦ congrArg Prod.snd h

/-- **One call of `C^f`** by `2 * l - 1` calls of `f`: adjoin zero ancillas, make the calls
`fixCalls op`, and remove the ancillas. -/
noncomputable def convCall (op : X → X → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec (Msg X l) X) A (qromCallReg X l E) Unit :=
  ((isoGate (ancIn ℓ) (ancIn_injective ℓ)).bind fun _ ↦
    lensChain (S := fixReg X l E) (fixCalls op E)).bind fun _ ↦
    coGate (ancOut E) (ancOut_injective E)

/-- **The converter circuit runs as the call of `C^f`.** -/
theorem runsAs_convCall (op : X → X → X) (f : Msg X l → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    RunsAs (additiveOracleRuntime f) (convCall.{v} op E ℓ) (qromCallMap (convOracle op f) ℓ) := by
  unfold convCall
  refine ((runsAs_isoGate _ _).bind (runsAs_lensChain f _ (fixCalls_query_set op E))).bind_coGate
    _ _ _ fun q ↦ ?_
  obtain ⟨a, d⟩ := q
  exact congrArg (fun z ↦ (z, d)) (lensSteps_fixCalls op f (ℓ a).1.1 (ℓ a).1.2 (ℓ a).2)

/-- The circuit of `C_1^f = toMsponge f`. -/
noncomputable abbrev c1Call (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec (Msg X l) X) A (qromCallReg X l E) Unit :=
  convCall (fun r c ↦ c - r) E ℓ

/-- The circuit of `C_2^g = toSponge g`. -/
noncomputable abbrev c2Call (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec (Msg X l) X) A (qromCallReg X l E) Unit :=
  convCall (fun r b ↦ r + b) E ℓ

theorem runsAs_c1Call (f : Msg X l → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    RunsAs (additiveOracleRuntime f) (c1Call.{v} E ℓ) (qromCallMap (toMsponge f) ℓ) :=
  runsAs_convCall _ f E ℓ

theorem runsAs_c2Call (g : Msg X l → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    RunsAs (additiveOracleRuntime g) (c2Call.{v} E ℓ) (qromCallMap (toSponge g) ℓ) :=
  runsAs_convCall _ g E ℓ

/-! ### Query budget of the circuit -/

theorem isQueryBound_lensCall {S : QReg} (inp : S → Msg X l) (σ : BlockLens X S) :
    (lensCall.{v} inp σ).IsQueryBound fun _ ↦ 1 := by
  unfold lensCall
  exact (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
    (isQueryBound_isoGate_spec _ _ 0) fun _ ↦
      (QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos) fun _ ↦
    isQueryBound_coGate_spec _ _ 0).mono fun _ ↦ by simp

theorem isQueryBound_lensChain {S : QReg} (cs : List ((S → Msg X l) × BlockLens X S)) :
    (lensChain.{v} cs).IsQueryBound fun _ ↦ cs.length := by
  induction cs with
  | nil => exact QuantumComp₂.isQueryBound_pure _ _
  | cons c cs ih =>
    exact (QuantumComp₂.isQueryBound_bind (isQueryBound_lensCall c.1 c.2) fun _ ↦ ih).mono
      fun _ ↦ by simp only [Pi.add_apply, List.length_cons]; omega

/-- **The circuit makes `2 * l - 1` calls.** -/
theorem isQueryBound_convCall (op : X → X → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    (convCall.{v} op E ℓ).IsQueryBound fun _ ↦ 2 * l - 1 :=
  (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
    (isQueryBound_isoGate_spec _ _ 0) fun _ ↦ isQueryBound_lensChain _) fun _ ↦
    isQueryBound_coGate_spec _ _ 0).mono fun _ ↦ by simp [length_fixCalls]

end circuit

/-! ## Substitution -/

section substitution

variable {X : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] {l : ℕ}
  {L : LocalSig.{u, v}} {W : QReg → Type w}

/-- The tree that replaces a call through `ℓ`: `convCall`, ending at the call's response. -/
noncomputable def convTree (op : X → X → X) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E) :
    QuantumComp LocalSig.instruments.{v} (qromSpec (Msg X l) X)
      (fun t ↦ Subtype fun _ : ULift.{v} Unit ↦ qromCallReg X l E = t) A :=
  QuantumComp.bind (convCall op E ℓ) fun _ p ↦ QuantumComp.pure ⟨ULift.up (), p.1.symm⟩

/-- The substitution: a local operation becomes the instrument that `I` gives it, and a call
becomes `convTree`. -/
noncomputable def convSubst (op : X → X → X) (I : L.Interp) :
    CommandSubstitution (QuantumComp.toIPFunctor L (qromSpec (Msg X l) X))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (qromSpec (Msg X l) X))
  | _, .prim o => QuantumComp.primBind (L := LocalSig.instruments.{v})
      ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query _ E ℓ => convTree op E ℓ

/-- **The converted program**: every call of `C^f` becomes the circuit `convCall op`, and every
local operation the instrument that `I` gives it. -/
noncomputable def convertCalls (op : X → X → X) (I : L.Interp) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    QuantumComp LocalSig.instruments.{v} (qromSpec (Msg X l) X) W A :=
  IFreeM.substitute (convSubst op I) x

/-- `C_1`: every call of the Msponge `toMsponge f` becomes calls of the sponge `f`. -/
noncomputable abbrev convertC1 (I : L.Interp) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    QuantumComp LocalSig.instruments.{v} (qromSpec (Msg X l) X) W A :=
  convertCalls (fun r c ↦ c - r) I x

/-- `C_2`: every call of the sponge `toSponge g` becomes calls of the Msponge `g`. -/
noncomputable abbrev convertC2 (I : L.Interp) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    QuantumComp LocalSig.instruments.{v} (qromSpec (Msg X l) X) W A :=
  convertCalls (fun r b ↦ r + b) I x

/-! ### Query budget -/

/-- **Query budget.** If every path of `x` makes at most `q` calls, every path of the converted
program makes at most `(2 * l - 1) * q`. -/
theorem isQueryBound_convertCalls (op : X → X → X) (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertCalls.{u, v} op I x).IsQueryBound fun _ ↦ (2 * l - 1) * q := by
  intro j
  refine IFreeM.IsChargeBound.substitute_mul (convSubst op I) (2 * l - 1) (fun B c ↦ ?_) hx
  cases c with
  | prim o =>
    exact (QuantumComp.isQueryBoundAt_primBind_iff (L := LocalSig.instruments.{v}) _ _ j _).mpr
      fun _ ↦ trivial
  | query p E ℓ =>
    show (convTree op E ℓ).IsQueryBoundAt j ((2 * l - 1) * 1)
    exact (QuantumComp.IsQueryBoundAt.bind (isQueryBound_convCall op E ℓ j) fun _ _ ↦
      QuantumComp.isQueryBoundAt_pure _ _ 0).mono (by simp)

theorem isTotalQueryBound_convertCalls (op : X → X → X) (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertCalls.{u, v} op I x).IsTotalQueryBound ((2 * l - 1) * q) :=
  (QuantumComp.isTotalQueryBound_iff_isQueryBound (s := qromSpec (Msg X l) X)
    (convertCalls op I x) _).mpr (isQueryBound_convertCalls op I hx)

/-! ### Semantics -/

theorem branch_run_convTree_bind (R : QuantumRuntime (qromSpec (Msg X l) X)) (op : X → X → X)
    (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec (Msg X l) X).In () × E)
    (g : ∀ t, (Subtype fun _ : ULift.{v} Unit ↦ qromCallReg X l E = t) →
      QuantumComp LocalSig.instruments.{v} (qromSpec (Msg X l) X) W t) (q : Σ u, W u) :
    (R.run .instruments ((convTree op E ℓ).bind g)).branch q =
      (R.run .instruments (g _ ⟨ULift.up (), rfl⟩)).branch q ∘ₗ
        (R.run₂ .instruments (convCall.{v} op E ℓ)).branch () :=
  (congrArg (fun y ↦ (R.run .instruments y).branch q)
    (QuantumComp.bind_assoc (convCall op E ℓ) _ g)).trans
    (branch_run_bind_unit R .instruments _ _ q)

/-- **The converted program runs as the original against `C^f`.** Against the oracle of `f`,
`convertCalls op I x` runs to the same dependent subinstrument as `x` against
`convOracle op f`. -/
theorem run_convertCalls (op : X → X → X) (I : L.Interp) (f : Msg X l → X) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    (additiveOracleRuntime f).run .instruments (convertCalls op I x) =
      (additiveOracleRuntime (convOracle op f)).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind]
    exact congrArg (((I o).frame _).bind) (funext ih)
  | queryBind _ i E ℓ k ih =>
    cases i
    refine DSubInstrument.ext (funext fun q ↦ ?_)
    refine (branch_run_convTree_bind _ op E ℓ _ q).trans ?_
    have hs := runsAs_convCall.{v} op f E ℓ
    rw [RunsAs] at hs
    rw [hs, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit,
      branch_queryStep_qromCallMap, ← ih ()]
    rfl

theorem evalDistMap_convertCalls {β : Type*} [MeasurableSpace β] (op : X → X → X)
    (I : L.Interp) (f : Msg X l → X) {A : QReg} (x : QuantumComp L (qromSpec (Msg X l) X) W A)
    (ρ : SubState A) (g : (Σ u, W u) → β) :
    (additiveOracleRuntime f).evalDistMap .instruments (convertCalls op I x) ρ g =
      (additiveOracleRuntime (convOracle op f)).evalDistMap I x ρ g := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost, run_convertCalls]
  rfl

theorem lossless_run_convertCalls (op : X → X → X) (I : L.Interp) (f : Msg X l → X) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} (hx : x.Lossless I) :
    ((additiveOracleRuntime f).run .instruments (convertCalls op I x)).Lossless := by
  rw [run_convertCalls]
  exact lossless_run_additiveOracleRuntime I hx _

/-- **`C_1` runs as the Msponge**: against the sponge oracle `f`, `convertC1 I x` runs as `x`
against `C_1^f = toMsponge f`. -/
theorem run_convertC1 (I : L.Interp) (f : Msg X l → X) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    (additiveOracleRuntime f).run .instruments (convertC1 I x) =
      (additiveOracleRuntime (toMsponge f)).run I x :=
  run_convertCalls _ I f x

/-- **`C_2` runs as the sponge**: against the Msponge oracle `g`, `convertC2 I x` runs as `x`
against `C_2^g = toSponge g`. -/
theorem run_convertC2 (I : L.Interp) (g : Msg X l → X) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg X l) X) W A) :
    (additiveOracleRuntime g).run .instruments (convertC2 I x) =
      (additiveOracleRuntime (toSponge g)).run I x :=
  run_convertCalls _ I g x

theorem evalDistMap_convertC1 {β : Type*} [MeasurableSpace β] (I : L.Interp) (f : Msg X l → X)
    {A : QReg} (x : QuantumComp L (qromSpec (Msg X l) X) W A) (ρ : SubState A)
    (g : (Σ u, W u) → β) :
    (additiveOracleRuntime f).evalDistMap .instruments (convertC1 I x) ρ g =
      (additiveOracleRuntime (toMsponge f)).evalDistMap I x ρ g :=
  evalDistMap_convertCalls _ I f x ρ g

theorem evalDistMap_convertC2 {β : Type*} [MeasurableSpace β] (I : L.Interp) (g : Msg X l → X)
    {A : QReg} (x : QuantumComp L (qromSpec (Msg X l) X) W A) (ρ : SubState A)
    (h : (Σ u, W u) → β) :
    (additiveOracleRuntime g).evalDistMap .instruments (convertC2 I x) ρ h =
      (additiveOracleRuntime (toSponge g)).evalDistMap I x ρ h :=
  evalDistMap_convertCalls _ I g x ρ h

theorem isQueryBound_convertC1 (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertC1.{u, v} I x).IsQueryBound fun _ ↦ (2 * l - 1) * q :=
  isQueryBound_convertCalls _ I hx

theorem isQueryBound_convertC2 (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertC2.{u, v} I x).IsQueryBound fun _ ↦ (2 * l - 1) * q :=
  isQueryBound_convertCalls _ I hx

theorem isTotalQueryBound_convertC1 (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertC1.{u, v} I x).IsTotalQueryBound ((2 * l - 1) * q) :=
  isTotalQueryBound_convertCalls _ I hx

theorem isTotalQueryBound_convertC2 (I : L.Interp) {A : QReg}
    {x : QuantumComp L (qromSpec (Msg X l) X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertC2.{u, v} I x).IsTotalQueryBound ((2 * l - 1) * q) :=
  isTotalQueryBound_convertCalls _ I hx

end substitution

end Quantum.Sponge

end
