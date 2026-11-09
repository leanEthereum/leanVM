/-
  LeanVM.Guest.B1.KeccakGkr.EqFrame

  `eqtree_frame` (G:984-1002), inline: the equality weights of a point built level by level in
  frame cells; a generic template and its meaning, `eqAt`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Algebra
public import LeanVM.Guest.B1.KeccakGkr.Lib

/-!
# `eqtree_frame`

`eqtree_frame(point, out, n, count)` reads the coordinates `r_t = point[off + t]` and writes level
`t` of the tree: entry `i < 2^t` is the parent `i` times `1 + r_t`, entry `2^t + i` the parent
times `r_t` (the last level cut at `count`). In the core IR, from the value `b`: level `0` is
`r₀` (`b`), `1` (`b + 1`), `1 + r₀` (`b + 2`, entry `0`) and a copy of `r₀` (`b + 3`, entry `1`);
level `t ≥ 1` from its base `B` is `r_t`, `1`, `1 + r_t`, then per parent `i` the product with
`1 + r_t` and, while `i < k` (`k = 2^t` but at a cut last level), the product with `r_t`
(`eqfLevelT`). Entry `j` of level `t` is `eqAt (r₀ .. r_t) j` (`eqf_level`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Level `0` from `b`. -/
def eqfLevel0T (pt : V) (off b : ℕ) : List Stmt :=
  [.atom (.load (.n b) pt off), .atom (.const (.n (b + 1)) (word 1 0 0)),
    .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.copy (.n (b + 3)) (.n b))]

/-- The value of entry `j` of a level `t ≥ 1` from its base `B`, `k` products with `r_t`. -/
def eqfEnt (t B k j : ℕ) : ℕ :=
  if j < 2 ^ t then B + 3 + j + min j k else B + 4 + 2 * (j - 2 ^ t)

/-- Level `t ≥ 1` from `B`, its parents' values `pw`, `k` products with `r_t`. -/
def eqfLevelT (pt : V) (off t B k : ℕ) (pw : ℕ → ℕ) : List Stmt :=
  [.atom (.load (.n B) pt (off + t)), .atom (.const (.n (B + 1)) (word 1 0 0)),
    .atom (.add (.n (B + 2)) (.n (B + 1)) (.n B))] ++
  ((List.range (2 ^ t)).map fun i ↦ [.atom (.mul (.n (eqfEnt t B k i)) (.n (pw i)) (.n (B + 2)))] ++
    if i < k then [.atom (.mul (.n (B + 4 + 2 * i)) (.n (pw i)) (.n B))] else []).flatten

theorem eqfLevel0T_holds {pt : V} {off b : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (eqfLevel0T pt off b) next kret) :
    (LoadHolds rd (σ pt) off (σ (.n b)) ∧ ∀ j < 2, σ (.n (b + 2 + j)) = eqAt [σ (.n b)] j) ∧ next := by
  simp only [eqfLevel0T, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l, e1, e2, e3, hn⟩ := h
  refine ⟨⟨l, fun j hj => ?_⟩, hn⟩
  interval_cases j
  · simp [eqAt, e2, e1, word_one]
  · simp [eqAt, e3]

/-- **A level of the tree**: from its parents `eqAt rs j` (`j < 2^t`) and the coordinate `r_t`
read at `off + t`, its entries are `eqAt (rs ++ [r_t])`. -/
theorem eqfLevelT_holds {pt : V} {off t B k : ℕ} {pw : ℕ → ℕ} {rs : List E} (hrs : rs.length = t)
    (hpw : ∀ j < 2 ^ t, σ (.n (pw j)) = eqAt rs j) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (eqfLevelT pt off t B k pw) next kret) :
    (LoadHolds rd (σ pt) (off + t) (σ (.n B)) ∧
      ∀ j < 2 ^ (t + 1), (j < 2 ^ t ∨ j - 2 ^ t < k) →
        σ (.n (eqfEnt t B k j)) = eqAt (rs ++ [σ (.n B)]) j) ∧ next := by
  rw [eqfLevelT, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l, e1, e2, h⟩ := h
  obtain ⟨hall, hn⟩ := (holdsList_range_flatten (2 ^ t) _ (fun i => by split <;> rfl) _ _).mp h
  refine ⟨⟨l, fun j hj hk => ?_⟩, hn⟩
  have hB : σ (.n (B + 2)) = 1 + σ (.n B) := by rw [e2, e1, word_one]
  rw [eqAt_append, hrs]
  rcases Nat.lt_or_ge j (2 ^ t) with hlt | hge
  · have hi := hall j hlt
    simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hi
    rw [hi.1, hpw j hlt, hB, Nat.div_eq_of_lt hlt]
    simp [eqAt]
  · have hk' : j - 2 ^ t < k := by omega
    have hi := hall (j - 2 ^ t) (by rw [pow_succ] at hj; omega)
    simp only [hk', ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
      Atom.Holds] at hi
    have hent : eqfEnt t B k j = B + 4 + 2 * (j - 2 ^ t) := by
      simp [eqfEnt, show ¬ j < 2 ^ t by omega]
    rw [hent, hi.2.1, hpw _ (by rw [pow_succ] at hj; omega), eqAt_mod rs j, hrs,
      show j % 2 ^ t = j - 2 ^ t by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by rw [pow_succ] at hj; omega)],
      show j / 2 ^ t = 1 by
        exact Nat.div_eq_of_lt_le (by omega) (by rw [pow_succ] at hj; omega)]
    simp [eqAt]

/-- The base of level `t ≥ 1` of a tree from `b`: four values for level `0`, then per full level
`3 + 2^(s+1)·…`; only the last level can be cut, after every base. -/
def eqfBase (b : ℕ) : ℕ → ℕ
  | 0 => b
  | 1 => b + 4
  | t + 2 => eqfBase b (t + 1) + 3 + 2 * 2 ^ (t + 1)

/-- The products with `r_t` at level `t` of an `n`-level tree cut at `count`. -/
def eqfK (n count t : ℕ) : ℕ := if t + 1 = n then count - 2 ^ t else 2 ^ t

/-- The value of entry `j` of level `t`. -/
def eqfVal (b n count : ℕ) : ℕ → ℕ → ℕ
  | 0, j => b + 2 + j
  | t + 1, j => eqfEnt (t + 1) (eqfBase b (t + 1)) (eqfK n count (t + 1)) j

/-- The first `m + 1` levels of the tree. -/
def eqfTm (pt : V) (off n count b : ℕ) (m : ℕ) : List Stmt :=
  eqfLevel0T pt off b ++ ((List.range m).map fun s ↦
    eqfLevelT pt off (s + 1) (eqfBase b (s + 1)) (eqfK n count (s + 1)) (eqfVal b n count s)).flatten

/-- **`eqtree_frame(point·g^off, out, n, count)`** from the value `b`. -/
def eqfT (pt : V) (off n count b : ℕ) : List Stmt := eqfTm pt off n count b (n - 1)

theorem eqfTm_succ (pt : V) (off n count b m : ℕ) :
    eqfTm pt off n count b (m + 1) = eqfTm pt off n count b m ++
      eqfLevelT pt off (m + 1) (eqfBase b (m + 1)) (eqfK n count (m + 1)) (eqfVal b n count m) := by
  simp [eqfTm, List.range_succ, List.map_append, List.flatten_append]

/-- **The tree's levels**: the first `m + 1` coordinates read at `off ..`, and every entry of level
`m` (all of them below the last level, the first `count` at it) the equality weight. -/
theorem eqfTm_holds {pt : V} {off n count b : ℕ} (hn : n ≤ 30) (hc1 : 2 ^ (n - 1) ≤ count)
    (hc2 : count ≤ 2 ^ n) :
    ∀ (m : ℕ) {next : Prop} {kret : List E → Prop}, m < n →
    Stmt.HoldsList C rd σ (eqfTm pt off n count b m) next kret →
    (∃ rs : List E, rs.length = m + 1 ∧ (∀ t (ht : t < rs.length), LoadHolds rd (σ pt) (off + t) rs[t]) ∧
      ∀ j < 2 ^ (m + 1), (m + 1 < n ∨ j < count) → σ (.n (eqfVal b n count m j)) = eqAt rs j) ∧ next
  | 0, next, kret, _, h => by
    simp only [eqfTm, List.range_zero, List.map_nil, List.flatten_nil, List.append_nil] at h
    obtain ⟨⟨l, he⟩, hn'⟩ := eqfLevel0T_holds h
    refine ⟨⟨[σ (.n b)], rfl, fun t ht => ?_, fun j hj _ => he j hj⟩, hn'⟩
    simp at ht; subst ht; simpa using l
  | m + 1, next, kret, hm, h => by
    rw [eqfTm_succ, holdsList_append] at h
    obtain ⟨⟨rs, hl, hld, hent⟩, hlev⟩ := eqfTm_holds hn hc1 hc2 m (by omega) h
    have hpw : ∀ j < 2 ^ (m + 1), σ (.n (eqfVal b n count m j)) = eqAt rs j :=
      fun j hj => hent j (by simpa using hj) (Or.inl (by omega))
    obtain ⟨⟨l, hlv⟩, hnext⟩ := eqfLevelT_holds hl hpw hlev
    refine ⟨⟨rs ++ [σ (.n (eqfBase b (m + 1)))], by simp [hl], fun t ht => ?_, fun j hj hjc => ?_⟩,
      hnext⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at ht
      rcases Nat.lt_or_ge t rs.length with h1 | h1
      · rw [List.getElem_append_left h1]; exact hld t h1
      · have : t = m + 1 := by omega
        subst this
        rw [List.getElem_append_right (by omega)]
        simpa [hl] using l
    · show σ (.n (eqfEnt (m + 1) (eqfBase b (m + 1)) (eqfK n count (m + 1)) j)) = _
      refine hlv j hj ?_
      rcases Nat.lt_or_ge j (2 ^ (m + 1)) with h1 | h1
      · exact Or.inl h1
      · right
        unfold eqfK
        split
        · rcases hjc with h2 | h2
          · omega
          · omega
        · have : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
          omega

/-- **`eqtree_frame`**: the `n` coordinates read at `off ..`, and the last level's first `count`
entries are their equality weights. -/
theorem eqfT_holds {pt : V} {off n count b : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 30)
    (hc1 : 2 ^ (n - 1) ≤ count) (hc2 : count ≤ 2 ^ n) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (eqfT pt off n count b) next kret) :
    (∃ rs : List E, rs.length = n ∧ (∀ t (ht : t < rs.length), LoadHolds rd (σ pt) (off + t) rs[t]) ∧
      ∀ j < count, σ (.n (eqfVal b n count (n - 1) j)) = eqAt rs j) ∧ next := by
  obtain ⟨⟨rs, hl, hld, hent⟩, hnext⟩ := eqfTm_holds hn hc1 hc2 (n - 1) (by omega) h
  refine ⟨⟨rs, by omega, hld, fun j hj => hent j ?_ (Or.inr hj)⟩, hnext⟩
  rw [show n - 1 + 1 = n by omega]; omega

end
end LeanVM.Guest.B1.VerifySub

