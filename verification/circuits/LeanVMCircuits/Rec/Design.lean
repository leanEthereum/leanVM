module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Push

@[expose] public section

/-!
The design of a recursion tree (`rec::tree::design`), for every shape `Tree::new` accepts.

`Tree::new` takes a `TreeShape`: the leaves' shape and rate, the first level's arity `arity_0`, the nodes' arity, and a claim-set tree's capacities (`ClaimShape`, with an optional small `Tier`). The leaves' shape and the rates enter only the leaf verifier, the session and the commitment, so `Shape` keeps the arities and capacities. `Shape.check` is `Tree::new`'s refusal of arities and small tiers, `Shape.places` is `Place::all`, `Shape.start`, `Shape.stop`, `Shape.kindBits` and `Shape.shift` are `Design::new`'s tier ranges, kind bits and tier shift, `Shape.code` and `Shape.position` are `Design::code` and `Design::position`, `Shape.union` is `Design::union_shape`, `Shape.children` is what `Design::node` verifies, `Shape.vars` and `Shape.layout` are `Design::new`'s dense variables and statement layout, and `converge` is `Tree::converge` over an abstract heights oracle. `checkdesign` compares every one of these with the Rust design on a grid of shapes.

The theorems hold for every accepted shape: the tiers are contiguous blocks of places (`tier_iff`), kinds and positions are inverse (`position_code`, `code_position`), a kind's low bits are its index within its tier and its high bits the tier's (`code_div`, `code_mod`), only the first level has kind zero (`code_eq_zero`), every node reads children of a tier the tree has (`children_tier`) whose fixed polynomial the statement carries (`fixed_poly_present`), every dense polynomial's variables fit the statement's point (`vars_le_dense`), the statement's sections tile it (`section_unique`), a tier's capacity is within the tree's (`tierCapacity_le`), a set within a capacity has at most its items and the children's sets of a union fit its pool (`set_items_le`, `children_fit`, `declared_fit`), every circuit has proofs built from leaves (`all_built`), and `converge` returns heights at which every circuit fits, the least such above its start when heights grow with the tiers' (`converge_fits`, `converge_least`).
-/

namespace LeanVMCircuits.Rec.Design

/-! Shapes. -/

/-- `multiset::Capacity`: the claims stay strictly below `claims`, in at most `groups` groups. -/
structure Capacity where
  claims : ℕ
  groups : ℕ
  deriving DecidableEq, Repr

/-- `Capacity::items`: a header per group, the members two to a block (`(claims - 1 + groups)` halved, rounded up), and an end. -/
def Capacity.items (c : Capacity) : ℕ := c.groups + (c.claims - 1 + c.groups + 1) / 2 + 1

/-- `tree::Tier`: the small tier's arity and capacity. -/
structure Tier where
  arity : ℕ
  capacity : Capacity
  deriving DecidableEq, Repr

/-- `tree::ClaimShape`: the tree's capacity, and its small tier if it has two. -/
structure ClaimShape where
  capacity : Capacity
  small : Option Tier
  deriving DecidableEq, Repr

/-- `TreeShape` without the leaves' shape and the rates. -/
structure Shape where
  arity0 : ℕ
  arity : ℕ
  claims : Option ClaimShape
  deriving DecidableEq, Repr

/-- Why `Tree::new` refuses a shape before building anything: `TreeError::Arity` or `TreeError::SmallTier`. -/
inductive Refusal where
  | arity
  | smallTier
  deriving DecidableEq, Repr

/-- `Tree::new`'s checks, in its order. -/
def Shape.check (sh : Shape) : Option Refusal :=
  if sh.arity0 = 0 ∨ sh.arity < 2 then some .arity
  else match sh.claims with
    | some ⟨large, some s⟩ =>
      if 2 ≤ s.arity ∧ s.arity ≤ sh.arity ∧ s.capacity.claims ≤ large.claims ∧ s.capacity.groups ≤ large.groups then
        none
      else some .smallTier
    | _ => none

/-- A shape `Tree::new`'s checks accept. The rest of `Tree::new` (the leaves' shape, `converge`) is below. -/
structure Shape.Accepted (sh : Shape) : Prop where
  arity0 : 1 ≤ sh.arity0
  arity : 2 ≤ sh.arity
  small : ∀ large s, sh.claims = some ⟨large, some s⟩ →
    2 ≤ s.arity ∧ s.arity ≤ sh.arity ∧ s.capacity.claims ≤ large.claims ∧ s.capacity.groups ≤ large.groups

theorem check_eq_none (sh : Shape) : sh.check = none ↔ sh.Accepted := by
  obtain ⟨a0, a, cl⟩ := sh
  constructor
  · intro h
    simp only [Shape.check] at h
    split_ifs at h with h1
    refine ⟨?_, ?_, fun large s hs => ?_⟩
    · show 1 ≤ a0
      omega
    · show 2 ≤ a
      omega
    simp only at hs
    subst hs
    simp only at h
    split_ifs at h with h2
    exact h2
  · rintro ⟨h0, h1, hs⟩
    simp only [Shape.check]
    have h0' : 1 ≤ a0 := h0
    have h1' : 2 ≤ a := h1
    rw [if_neg (show ¬(a0 = 0 ∨ a < 2) by omega)]
    match cl, hs with
    | none, _ => rfl
    | some ⟨_, none⟩, _ => rfl
    | some ⟨large, some s⟩, hs => simp only; rw [if_pos (hs large s rfl)]

/-! Places. -/

/-- `design::Level`. -/
inductive Level where
  | first
  | node (a : ℕ)
  | wrap
  deriving DecidableEq, Repr

/-- `design::Place`. -/
structure Place where
  tier : ℕ
  level : Level
  deriving DecidableEq, Repr

/-- The nodes of arities `lo..=hi` in a tier. -/
def nodes (tier lo hi : ℕ) : List Place := (List.range' lo (hi + 1 - lo)).map fun a => ⟨tier, .node a⟩

/-- `Place::all`. -/
def Shape.places (sh : Shape) : List Place :=
  match sh.claims with
  | none => ⟨0, .first⟩ :: nodes 0 sh.arity sh.arity
  | some ⟨_, none⟩ => ⟨0, .first⟩ :: nodes 0 2 sh.arity
  | some ⟨_, some s⟩ => ⟨0, .first⟩ :: nodes 0 2 s.arity ++ [⟨0, .wrap⟩] ++ nodes 1 sh.arity sh.arity

/-- The tiers: two with a small tier, else one. -/
def Shape.nTiers (sh : Shape) : ℕ :=
  match sh.claims with
  | some ⟨_, some _⟩ => 2
  | _ => 1

/-- The circuits. -/
def Shape.size (sh : Shape) : ℕ :=
  match sh.claims with
  | none => 2
  | some ⟨_, none⟩ => sh.arity
  | some ⟨_, some s⟩ => s.arity + 2

/-- The end of the small tier's places. -/
def Shape.smallEnd (sh : Shape) : ℕ :=
  match sh.claims with
  | some ⟨_, some s⟩ => s.arity + 1
  | _ => sh.size

/-- The first place of a tier (`TierDesign::places.start`). -/
def Shape.start (sh : Shape) (t : ℕ) : ℕ := if t = 0 then 0 else sh.smallEnd

/-- The end of a tier's places (`TierDesign::places.end`). -/
def Shape.stop (sh : Shape) (t : ℕ) : ℕ := if t = 0 then sh.smallEnd else sh.size

/-- The place at a position, in closed form. -/
def Shape.placeAt (sh : Shape) (p : ℕ) : Place :=
  if p = 0 then ⟨0, .first⟩ else
  match sh.claims with
  | none => ⟨0, .node sh.arity⟩
  | some ⟨_, none⟩ => ⟨0, .node (p + 1)⟩
  | some ⟨_, some s⟩ =>
    if p < s.arity then ⟨0, .node (p + 1)⟩ else if p = s.arity then ⟨0, .wrap⟩ else ⟨1, .node sh.arity⟩

theorem nodes_length (t lo hi : ℕ) : (nodes t lo hi).length = hi + 1 - lo := by simp [nodes]

theorem nodes_getElem (t lo hi i : ℕ) (h : i < (nodes t lo hi).length) :
    (nodes t lo hi)[i] = ⟨t, .node (lo + i)⟩ := by
  simp [nodes]

theorem length_places (sh : Shape) (h : sh.Accepted) : sh.places.length = sh.size := by
  rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩
  · simp [Shape.places, Shape.size, nodes_length]
  · have ha : 2 ≤ a := h.arity
    simp [Shape.places, Shape.size, nodes_length]; omega
  · have := (h.small large s rfl).1
    simp [Shape.places, Shape.size, nodes_length]; omega

/-- `Place::all` is the closed form. -/
theorem nodes_getElem? (t lo hi i : ℕ) :
    (nodes t lo hi)[i]? = if i < hi + 1 - lo then some ⟨t, .node (lo + i)⟩ else none := by
  unfold nodes
  rw [List.getElem?_map]
  split_ifs with hi'
  · rw [List.getElem?_range' hi']; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem places_getElem? (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    sh.places[p]? = some (sh.placeAt p) := by
  obtain ⟨a0, a, cl⟩ := sh
  have ha : 2 ≤ a := h.arity
  rcases cl with _ | ⟨large, _ | s⟩
  · simp only [Shape.places, Shape.placeAt, Shape.size] at hp ⊢
    rcases p with _ | p
    · rfl
    · simp only [List.getElem?_cons_succ, nodes_getElem?, reduceCtorEq, if_false]
      rw [if_pos (show p < a + 1 - a by omega)]
      congr 3
      omega
  · simp only [Shape.places, Shape.placeAt, Shape.size] at hp ⊢
    rcases p with _ | p
    · rfl
    · simp only [List.getElem?_cons_succ, nodes_getElem?, reduceCtorEq, if_false]
      rw [if_pos (show p < a + 1 - 2 by omega)]
      congr 3
      omega
  · have hs := (h.small large s rfl).1
    simp only [Shape.places, Shape.placeAt, Shape.size] at hp ⊢
    rcases p with _ | p
    · rfl
    · simp only [reduceCtorEq, if_false, List.cons_append, List.getElem?_cons_succ, List.append_assoc,
        List.getElem?_append, nodes_length, List.getElem?_cons, nodes_getElem?, List.length_nil]
      split_ifs <;> first | rfl | omega | (congr 3; omega)

/-- `Place::all` is the closed form. -/
theorem places_getElem (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.places.length) :
    sh.places[p] = sh.placeAt p := by
  have hp' : p < sh.size := length_places sh h ▸ hp
  have := places_getElem? sh h p hp'
  rw [List.getElem?_eq_getElem hp] at this
  exact Option.some.inj this

/-- Every position's tier is a tier of the tree. -/
theorem tier_lt (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) : (sh.placeAt p).tier < sh.nTiers := by
  rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;>
    simp only [Shape.placeAt, Shape.nTiers] <;> split_ifs <;> simp

/-- The tiers are contiguous blocks of places, the small tier first: what `Design::new`'s ranges rely on. -/
theorem tier_iff (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) (t : ℕ) :
    (sh.placeAt p).tier = t ↔ t < sh.nTiers ∧ sh.start t ≤ p ∧ p < sh.stop t := by
  obtain ⟨a0, a, cl⟩ := sh
  have ha : 2 ≤ a := h.arity
  rcases cl with _ | ⟨large, _ | s⟩
  · simp only [Shape.placeAt, Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size] at hp ⊢
    split_ifs <;> (try dsimp only) <;> omega
  · simp only [Shape.placeAt, Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size] at hp ⊢
    split_ifs <;> (try dsimp only) <;> omega
  · simp only [Shape.placeAt, Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size] at hp ⊢
    split_ifs <;> (try dsimp only) <;> omega

/-- Every tier has a place, and the tiers end at the last place (`Design::new`'s assertion). -/
theorem tiers_cover (sh : Shape) (h : sh.Accepted) :
    sh.start 0 = 0 ∧ (∀ t < sh.nTiers, sh.start t < sh.stop t) ∧ sh.stop (sh.nTiers - 1) = sh.size ∧
      (sh.nTiers = 2 → sh.stop 0 = sh.start 1) := by
  obtain ⟨a0, a, cl⟩ := sh
  have ha : 2 ≤ a := h.arity
  rcases cl with _ | ⟨large, _ | s⟩
  · simp only [Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size]
    refine ⟨rfl, fun t ht => ?_, rfl, fun h2 => absurd h2 (by decide)⟩
    obtain rfl : t = 0 := by omega
    simp
  · simp only [Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size]
    refine ⟨rfl, fun t ht => ?_, rfl, fun h2 => absurd h2 (by decide)⟩
    obtain rfl : t = 0 := by omega
    simp; omega
  · have hs := (h.small large s rfl).1
    simp only [Shape.nTiers, Shape.start, Shape.stop, Shape.smallEnd, Shape.size]
    refine ⟨rfl, fun t ht => ?_, by simp, fun _ => rfl⟩
    split_ifs <;> omega

/-- The first level is position zero, and only it. -/
theorem first_iff (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    (sh.placeAt p).level = .first ↔ p = 0 := by
  rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;>
    simp only [Shape.placeAt] <;> split_ifs <;> simp_all

/-! Kinds. -/

/-- `log2_ceil_usize` of a tier's places: the bits of a kind's index within it. -/
def Shape.kindBits (sh : Shape) (t : ℕ) : ℕ := Nat.clog 2 (sh.stop t - sh.start t)

/-- The tier shift: the most kind bits of a tier. -/
def Shape.shift (sh : Shape) : ℕ := if sh.nTiers = 2 then max (sh.kindBits 0) (sh.kindBits 1) else sh.kindBits 0

/-- `Design::code`: a position's index within its tier, its tier above. -/
def Shape.code (sh : Shape) (p : ℕ) : ℕ :=
  let t := (sh.placeAt p).tier
  (t <<< sh.shift) ||| (p - sh.start t)

/-- `Design::position`. -/
def Shape.position (sh : Shape) (c : ℕ) : Option ℕ :=
  let t := c >>> sh.shift
  if t < sh.nTiers then
    let p := sh.start t + (c &&& ((1 <<< sh.shift) - 1))
    if sh.start t ≤ p ∧ p < sh.stop t then some p else none
  else none

/-- The bits `Design::kind_bits` holds a kind's word to past its index's: its tier's, `(tier << shift) >> kind_bits`. -/
def Shape.above (sh : Shape) (t : ℕ) : ℕ := (t <<< sh.shift) >>> sh.kindBits t

theorem nTiers_eq (sh : Shape) : sh.nTiers = 1 ∨ sh.nTiers = 2 := by
  unfold Shape.nTiers; split <;> simp

theorem nTiers_le (sh : Shape) : sh.nTiers ≤ 2 := by rcases nTiers_eq sh with h | h <;> omega

theorem kindBits_le_shift (sh : Shape) (t : ℕ) (ht : t < sh.nTiers) : sh.kindBits t ≤ sh.shift := by
  have := nTiers_eq sh
  unfold Shape.shift
  split_ifs with h2
  · rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · obtain rfl : t = 0 := by omega
    exact le_rfl

/-- A position's index within its tier is below two to its tier's kind bits. -/
theorem index_lt (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    p - sh.start (sh.placeAt p).tier < 2 ^ sh.kindBits (sh.placeAt p).tier := by
  obtain ⟨_, h1, h2⟩ := (tier_iff sh h p hp _).mp rfl
  exact lt_of_lt_of_le (by omega) (Nat.le_pow_clog (by norm_num) _)

/-- A kind is its tier times two to the shift plus its index within its tier. -/
theorem code_eq (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    sh.code p = (sh.placeAt p).tier * 2 ^ sh.shift + (p - sh.start (sh.placeAt p).tier) := by
  have hi := index_lt sh h p hp
  have hk := kindBits_le_shift sh _ (tier_lt sh h p hp)
  have hlt : p - sh.start (sh.placeAt p).tier < 2 ^ sh.shift :=
    lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk)
  unfold Shape.code
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]

/-- `Design::position` inverts `Design::code`. -/
theorem position_code (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    sh.position (sh.code p) = some p := by
  have hi := index_lt sh h p hp
  have ht := tier_lt sh h p hp
  have hk := kindBits_le_shift sh _ ht
  obtain ⟨_, h1, h2⟩ := (tier_iff sh h p hp _).mp rfl
  have hlt : p - sh.start (sh.placeAt p).tier < 2 ^ sh.shift :=
    lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk)
  have hpos : 0 < 2 ^ sh.shift := Nat.two_pow_pos _
  have hdiv : sh.code p / 2 ^ sh.shift = (sh.placeAt p).tier := by
    rw [code_eq sh h p hp, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hmod : sh.code p % 2 ^ sh.shift = p - sh.start (sh.placeAt p).tier := by
    rw [code_eq sh h p hp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  unfold Shape.position
  simp only [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, hdiv, hmod]
  rw [if_pos ht, if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- A kind `Design::position` names is that position's kind. -/
theorem code_position (sh : Shape) (h : sh.Accepted) (c p : ℕ) (hc : sh.position c = some p) :
    p < sh.size ∧ sh.code p = c := by
  unfold Shape.position at hc
  simp only [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod] at hc
  split_ifs at hc with ht hr
  obtain ⟨h1, h2⟩ := hr
  simp only [Option.some.injEq] at hc
  subst hc
  obtain ⟨_, _, hsz, _⟩ := tiers_cover sh h
  have hstop : ∀ t < sh.nTiers, sh.stop t ≤ sh.size := by
    intro t ht'
    unfold Shape.stop Shape.smallEnd Shape.size
    unfold Shape.nTiers at ht'
    rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;> simp only at ht' ⊢ <;> split_ifs <;> omega
  have hp : sh.start (c / 2 ^ sh.shift) + c % 2 ^ sh.shift < sh.size := lt_of_lt_of_le h2 (hstop _ ht)
  refine ⟨hp, ?_⟩
  have htier := (tier_iff sh h _ hp (c / 2 ^ sh.shift)).mpr ⟨ht, h1, h2⟩
  rw [code_eq sh h _ hp, htier, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.div_add_mod]

/-- Two positions of one kind are one. -/
theorem code_injective (sh : Shape) (h : sh.Accepted) (p q : ℕ) (hp : p < sh.size) (hq : q < sh.size)
    (he : sh.code p = sh.code q) : p = q := by
  have := position_code sh h p hp
  rw [he, position_code sh h q hq] at this
  exact (Option.some.inj this).symm

/-- A kind's bits past its tier's kind bits are its tier's (`Design::kind_bits`'s `eq_k_const`s). -/
theorem code_div (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    sh.code p / 2 ^ sh.kindBits (sh.placeAt p).tier = sh.above (sh.placeAt p).tier := by
  have hi := index_lt sh h p hp
  have hk := kindBits_le_shift sh _ (tier_lt sh h p hp)
  set t := (sh.placeAt p).tier
  set k := sh.kindBits t
  have hpow : 2 ^ sh.shift = 2 ^ (sh.shift - k) * 2 ^ k := by rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos _
  rw [code_eq sh h p hp, Shape.above, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hpow, ← Nat.mul_assoc,
    Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hi, Nat.zero_add, Nat.mul_div_cancel _ hpos]

/-- A kind's low bits are its index within its tier (the `top` bits that select its block). -/
theorem code_mod (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    sh.code p % 2 ^ sh.kindBits (sh.placeAt p).tier = p - sh.start (sh.placeAt p).tier := by
  have hi := index_lt sh h p hp
  have hk := kindBits_le_shift sh _ (tier_lt sh h p hp)
  set t := (sh.placeAt p).tier
  set k := sh.kindBits t
  have hpow : 2 ^ sh.shift = 2 ^ (sh.shift - k) * 2 ^ k := by rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [code_eq sh h p hp, hpow, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- Only the first level has kind zero, and a kind's index within the small tier is zero only for it. -/
theorem code_eq_zero (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) :
    (sh.code p = 0 ↔ p = 0) ∧ ((sh.placeAt p).tier = 0 → (p - sh.start 0 = 0 ↔ p = 0)) := by
  have hpos : 0 < 2 ^ sh.shift := Nat.two_pow_pos _
  have hs0 : sh.start 0 = 0 := rfl
  refine ⟨?_, fun _ => by omega⟩
  rw [code_eq sh h p hp]
  constructor
  · intro hz
    have ht : (sh.placeAt p).tier = 0 := by
      by_contra hne
      have : 1 ≤ (sh.placeAt p).tier * 2 ^ sh.shift := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hne hpos.ne')
      omega
    rw [ht, hs0] at hz
    omega
  · rintro rfl
    have : (sh.placeAt 0).tier = 0 := by simp [Shape.placeAt]
    rw [this, hs0]
    simp

/-- With fewer than `2 ^ 62` circuits, a tier's kind bits and the shift are at most 62. -/
theorem shift_le (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) :
    (∀ t < sh.nTiers, sh.kindBits t ≤ 62) ∧ sh.shift ≤ 62 := by
  have hn := nTiers_le sh
  have hk : ∀ t < sh.nTiers, sh.kindBits t ≤ 62 := by
    intro t htt
    have hle : sh.stop t - sh.start t ≤ 2 ^ 62 := by
      have : sh.stop t ≤ sh.size := by
        unfold Shape.stop Shape.smallEnd Shape.size
        unfold Shape.nTiers at htt
        rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;> simp only at htt ⊢ <;> split_ifs <;> omega
      omega
    exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hle
  refine ⟨hk, ?_⟩
  unfold Shape.shift
  split_ifs with h2
  · exact max_le (hk 0 (by omega)) (hk 1 (by omega))
  · exact hk 0 (by rcases nTiers_eq sh with h | h <;> omega)

/-- A kind fits a word whenever the tree has fewer than `2 ^ 62` circuits. -/
theorem code_lt (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) (hs : sh.size < 2 ^ 62) :
    sh.code p < 2 ^ 64 := by
  have ht := tier_lt sh h p hp
  have hn := nTiers_le sh
  have hsh := (shift_le sh h hs).2
  have h2 : 2 ^ sh.shift ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hsh
  have hi := index_lt sh h p hp
  have hkb := kindBits_le_shift sh _ ht
  have h1 : 2 ^ sh.kindBits (sh.placeAt p).tier ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (hkb.trans hsh)
  rw [code_eq sh h p hp]
  have : (sh.placeAt p).tier * 2 ^ sh.shift ≤ 1 * 2 ^ 62 := Nat.mul_le_mul (by omega) h2
  omega

/-! What a circuit verifies. -/

/-- What `Design::node` verifies at a position: how many children, of which tier. None for the first level, which verifies `arity0` leaves. -/
def Shape.children (sh : Shape) (p : ℕ) : Option (ℕ × ℕ) :=
  match (sh.placeAt p).level with
  | .first => none
  | .node a => some (a, 0)
  | .wrap => some (1, 1)

/-- Every node reads one to `arity` children of a tier the tree has: a node the small tier's, a wrap the large tier's, of which it reads one. -/
theorem children_tier (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) (a ct : ℕ)
    (hc : sh.children p = some (a, ct)) :
    ct < sh.nTiers ∧ 1 ≤ a ∧ a ≤ sh.arity ∧ (ct = 1 ↔ (sh.placeAt p).level = .wrap) := by
  obtain ⟨a0, a', cl⟩ := sh
  have ha : 2 ≤ a' := h.arity
  rcases cl with _ | ⟨large, _ | s⟩
  · simp only [Shape.children, Shape.placeAt, Shape.nTiers, Shape.size] at hc hp ⊢
    split_ifs at hc ⊢; simp_all; omega
  · simp only [Shape.children, Shape.placeAt, Shape.nTiers, Shape.size] at hc hp ⊢
    split_ifs at hc ⊢; simp_all; omega
  · obtain ⟨hs1, hs2, -⟩ := h.small large s rfl
    simp only [Shape.children, Shape.placeAt, Shape.nTiers, Shape.size] at hc hp ⊢
    split_ifs at hc ⊢ <;> simp_all <;> omega

/-- The first level is the only place without children. -/
theorem children_none (sh : Shape) (p : ℕ) : sh.children p = none ↔ (sh.placeAt p).level = .first := by
  unfold Shape.children
  split <;> simp_all

/-- Proofs of a circuit can be built from leaves: the first level's from leaves, a node's or wrap's from proofs of its child tier. -/
inductive Shape.Built (sh : Shape) : ℕ → Prop
  | first : sh.Built 0
  | child (p q a ct : ℕ) : p < sh.size → sh.children p = some (a, ct) → q < sh.size → (sh.placeAt q).tier = ct →
      sh.Built q → sh.Built p

/-- Every circuit of an accepted shape has proofs built from leaves: no kind is unreachable, and every proof's tree of children ends at leaves. -/
theorem all_built (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) : sh.Built p := by
  have h0 : (0 : ℕ) < sh.size := by
    obtain ⟨a0, a, cl⟩ := sh
    have ha : 2 ≤ a := h.arity
    unfold Shape.size; rcases cl with _ | ⟨large, _ | s⟩ <;> simp only <;> omega
  have hsmall : ∀ q < sh.size, ∀ a, sh.children q = some (a, 0) → sh.Built q := fun q hq a hc =>
    .child q 0 a 0 hq hc h0 (by simp [Shape.placeAt]) .first
  rcases hc : sh.children p with _ | ⟨a, ct⟩
  · have := (first_iff sh h p hp).mp ((children_none sh p).mp hc)
    subst this; exact .first
  · obtain ⟨hct, -, -, hw⟩ := children_tier sh h p hp a ct hc
    rcases Nat.lt_or_ge ct 1 with h1 | h1
    · obtain rfl : ct = 0 := by omega
      exact hsmall p hp a hc
    · -- A wrap: its child is the large tier's node, built from the first level.
      have := nTiers_le sh
      obtain rfl : ct = 1 := by omega
      have hn : sh.nTiers = 2 := by rcases nTiers_eq sh with h | h <;> omega
      obtain ⟨-, hne, hsz, -⟩ := tiers_cover sh h
      have hq : sh.size - 1 < sh.size := by omega
      have hstop : sh.stop 1 = sh.size := by simpa [hn] using hsz
      have hst : sh.start 1 < sh.stop 1 := hne 1 (by omega)
      have hqt : (sh.placeAt (sh.size - 1)).tier = 1 :=
        (tier_iff sh h _ hq 1).mpr ⟨by omega, by omega, by omega⟩
      have hqc : sh.children (sh.size - 1) = some (sh.arity, 0) := by
        obtain ⟨a0, a', cl⟩ := sh
        rcases cl with _ | ⟨large, _ | s⟩
        · simp [Shape.nTiers] at hn
        · simp [Shape.nTiers] at hn
        · have := (h.small large s rfl).1
          have e : s.arity + 2 - 1 = s.arity + 1 := by omega
          simp only [Shape.size, e, Shape.children, Shape.placeAt]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact .child p _ a 1 hp hc hq hqt (hsmall _ hq _ hqc)

/-! Unions and capacities. -/

/-- `union::CHUNK`. -/
def chunk : ℕ := 32

/-- `PoolShape::new`: chunks for runs together of at most `items` items, each run's last chunk wasting less than a chunk. -/
def poolChunks (items runs : ℕ) : ℕ := (items + chunk - 1) / chunk + runs

/-- `union::UnionShape`, its pools by their chunks. -/
structure UnionShape where
  arity : ℕ
  children : ℕ
  declared : ℕ
  optional : Bool
  deriving DecidableEq, Repr

/-- `UnionShape::new` and, optional, `UnionShape::optional`. -/
def UnionShape.new (c : Capacity) (a : ℕ) (optional : Bool) : UnionShape :=
  ⟨a, poolChunks (c.items + a - 1) a, poolChunks c.items 1, optional⟩

/-- `ClaimShape::tier_capacity`. -/
def ClaimShape.tierCapacity (c : ClaimShape) (t : ℕ) : Capacity :=
  match t, c.small with
  | 0, some s => s.capacity
  | _, _ => c.capacity

/-- `Design::union_shape`: none in a tree of outputs and for a wrap. -/
def Shape.union (sh : Shape) (p : ℕ) : Option UnionShape :=
  sh.claims.bind fun c =>
    match sh.placeAt p with
    | ⟨t, .first⟩ => some (.new (c.tierCapacity t) sh.arity0 false)
    | ⟨t, .node a⟩ => some (.new (c.tierCapacity t) a true)
    | ⟨_, .wrap⟩ => none

/-- A tier's capacity is within the tree's. -/
theorem tierCapacity_le (sh : Shape) (h : sh.Accepted) (c : ClaimShape) (hc : sh.claims = some c) (t : ℕ) :
    (c.tierCapacity t).claims ≤ c.capacity.claims ∧ (c.tierCapacity t).groups ≤ c.capacity.groups := by
  rcases c with ⟨large, _ | s⟩
  · cases t <;> simp [ClaimShape.tierCapacity]
  · obtain ⟨-, -, h1, h2⟩ := h.small large s hc
    cases t <;> simp [ClaimShape.tierCapacity, h1, h2]

theorem items_mono (a b : Capacity) (h1 : a.claims ≤ b.claims) (h2 : a.groups ≤ b.groups) : a.items ≤ b.items := by
  unfold Capacity.items; omega

/-- A claim set as `ClaimSet::items` writes it: each group's member count. -/
def setItems (groups : List ℕ) : ℕ := groups.length + (groups.map fun m => (m + 1) / 2).sum + 1

theorem halves_le (gs : List ℕ) : (gs.map fun m => (m + 1) / 2).sum ≤ (gs.sum + gs.length) / 2 := by
  induction gs with
  | nil => simp
  | cons m gs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- A set within a capacity (fewer claims than its bound, at most its groups) has at most its items. -/
theorem set_items_le (c : Capacity) (gs : List ℕ) (h1 : gs.sum < c.claims) (h2 : gs.length ≤ c.groups) :
    setItems gs ≤ c.items := by
  have := halves_le gs
  unfold setItems Capacity.items; omega

/-- Runs of these items, each from a chunk boundary, take this many chunks (`PoolFill::new`). -/
def runChunks (runs : List ℕ) : ℕ := (runs.map fun n => (n + chunk - 1) / chunk).sum

theorem runChunks_le (runs : List ℕ) : runChunks runs ≤ (runs.sum + chunk - 1) / chunk + runs.length := by
  unfold runChunks chunk
  induction runs with
  | nil => simp
  | cons n rs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The children's sets of a union, together within its capacity (their groups' claims fewer than its bound, their groups at most its), fit its children's pool. -/
theorem children_fit (c : Capacity) (sets : List (List ℕ)) (h1 : (sets.map List.sum).sum < c.claims)
    (h2 : (sets.map List.length).sum ≤ c.groups) (ha : 1 ≤ sets.length) (opt : Bool) :
    runChunks (sets.map setItems) ≤ (UnionShape.new c sets.length opt).children := by
  have hsum : (sets.map setItems).sum ≤ c.items + sets.length - 1 := by
    have hall := halves_le sets.flatten
    have hf : (sets.map setItems).sum =
        (sets.map List.length).sum + (sets.flatten.map fun m => (m + 1) / 2).sum + sets.length := by
      clear h1 h2 ha hall
      induction sets with
      | nil => simp
      | cons g gs ih => simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
          List.sum_append, List.length_cons, ih, setItems]; omega
    have hl : sets.flatten.length = (sets.map List.length).sum := List.length_flatten
    have hs : sets.flatten.sum = (sets.map List.sum).sum := by
      clear h1 h2 ha hall hf hl
      induction sets with
      | nil => simp
      | cons g gs ih => simp [ih]
    unfold Capacity.items; omega
  have := runChunks_le (sets.map setItems)
  simp only [List.length_map] at this
  unfold UnionShape.new poolChunks
  simp only
  unfold chunk at this ⊢
  omega

/-- A set within a union's capacity fits its declared pool. -/
theorem declared_fit (c : Capacity) (gs : List ℕ) (h1 : gs.sum < c.claims) (h2 : gs.length ≤ c.groups) (a : ℕ)
    (opt : Bool) : runChunks [setItems gs] ≤ (UnionShape.new c a opt).declared := by
  have := set_items_le c gs h1 h2
  unfold runChunks UnionShape.new poolChunks chunk
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Every union of the tree is at its tier's capacity, within the tree's. -/
theorem union_capacity (sh : Shape) (h : sh.Accepted) (p : ℕ) (u : UnionShape) (hu : sh.union p = some u) :
    ∃ c cap, sh.claims = some c ∧ u = UnionShape.new cap u.arity u.optional ∧ cap.claims ≤ c.capacity.claims ∧
      cap.groups ≤ c.capacity.groups := by
  unfold Shape.union at hu
  rcases hc : sh.claims with _ | c
  · rw [hc] at hu; simp at hu
  · rw [hc] at hu
    simp only [Option.bind_some] at hu
    generalize sh.placeAt p = pl at hu
    obtain ⟨t, l⟩ := pl
    obtain ⟨h1, h2⟩ := tierCapacity_le sh h c hc t
    rcases l with _ | a | _
    · simp only [Option.some.injEq] at hu
      subst hu
      exact ⟨c, _, rfl, rfl, h1, h2⟩
    · simp only [Option.some.injEq] at hu
      subst hu
      exact ⟨c, _, rfl, rfl, h1, h2⟩
    · simp at hu

/-! Dense variables and the statement. -/

/-- `CircuitId::MAX_K_LOG`, the matrix points' coordinates. -/
def maxKLog : ℕ := 14

/-- `N_FLOCKS`. -/
def nFlocks : ℕ := 21

/-- `DensePoly::ALL` the tree has: the fixed polynomial's wide twin only with two tiers. -/
def Shape.nPolys (sh : Shape) : ℕ := if sh.nTiers = 2 then 4 else 3

/-- `Design::new`'s `fixed_vars`: a tier's fixed stack's variables and its kind bits; zero for a tier the tree lacks. -/
def Shape.fixedVars (sh : Shape) (kappa : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < sh.nTiers then kappa t + sh.kindBits t else 0

/-- `DenseVars`: the bytecode's and image's variables `v0`, `v1` (the program's), each tier's fixed polynomial's. -/
def Shape.vars (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) : List ℕ :=
  [v0, v1, sh.fixedVars kappa 0, sh.fixedVars kappa 1]

/-- `StatementLayout`. -/
structure Layout where
  nDense : ℕ
  nPolys : ℕ
  nMatrix : ℕ
  nFlocks : ℕ
  deriving DecidableEq, Repr

/-- `Section::ALL`'s widths: kind, digest, dense point, dense values, rows, columns, matrices. -/
def Layout.widths (l : Layout) : List ℕ := [1, 2, l.nDense, l.nPolys, l.nMatrix, l.nMatrix, 2 * l.nFlocks]

/-- Where a section starts. -/
def Layout.start (l : Layout) (i : ℕ) : ℕ := (l.widths.take i).sum

/-- `StatementLayout::len`. -/
def Layout.len (l : Layout) : ℕ := l.widths.sum

/-- `Design::new`'s statement layout: the point of the most variables, the tree's polynomials. -/
def Shape.layout (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) : Layout :=
  ⟨(sh.vars v0 v1 kappa).foldr max 0, sh.nPolys, maxKLog, nFlocks⟩

theorem foldr_max_ge (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- Every dense polynomial's variables fit the statement's point, so `carried`'s prefixes are in range. -/
theorem vars_le_dense (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) (x : ℕ) (hx : x ∈ sh.vars v0 v1 kappa) :
    x ≤ (sh.layout v0 v1 kappa).nDense :=
  foldr_max_ge _ x hx

/-- A tier's fixed polynomial has its stack's variables and its kind bits, the `top` bits a child's fixed claim reads. -/
theorem fixed_vars (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) (t : ℕ) (ht : t < sh.nTiers) :
    (sh.vars v0 v1 kappa)[2 + t]? = some (kappa t + sh.kindBits t) := by
  have := nTiers_le sh
  have ht2 : t < 2 := by omega
  interval_cases t <;> simp [Shape.vars, Shape.fixedVars, ht]

/-- The fixed polynomial a node's child is read against (`Fixed` for the small tier, `Wide` for the large) is in the statement. -/
theorem fixed_poly_present (sh : Shape) (h : sh.Accepted) (p : ℕ) (hp : p < sh.size) (a ct : ℕ)
    (hc : sh.children p = some (a, ct)) : 2 + ct < sh.nPolys := by
  obtain ⟨hct, -⟩ := children_tier sh h p hp a ct hc
  unfold Shape.nPolys
  split_ifs with h2 <;> have := nTiers_le sh <;> omega

/-- A tree of one tier has no wide polynomial: no variables, no statement value. -/
theorem wide_absent (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) (h1 : sh.nTiers = 1) :
    sh.nPolys = 3 ∧ (sh.vars v0 v1 kappa)[3]? = some 0 := by
  simp [Shape.nPolys, Shape.vars, Shape.fixedVars, h1]

theorem start_succ (l : Layout) (i : ℕ) (hi : i < 7) : l.start (i + 1) = l.start i + l.widths.getD i 0 := by
  unfold Layout.start
  have : i < l.widths.length := by simp [Layout.widths]; omega
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]

theorem len_eq (l : Layout) : l.len = 3 + l.nDense + l.nPolys + 2 * l.nMatrix + 2 * l.nFlocks := by
  simp [Layout.len, Layout.widths]; omega

/-- The statement's sections tile it: every word is in exactly one section. -/
theorem section_unique (l : Layout) (w : ℕ) (hw : w < l.len) :
    ∃ i < 7, l.start i ≤ w ∧ w < l.start (i + 1) ∧ ∀ j < 7, l.start j ≤ w → w < l.start (j + 1) → j = i := by
  have hs : ∀ i, i < 7 → l.start i ≤ l.start (i + 1) := fun i hi => by rw [start_succ l i hi]; omega
  have h0 : l.start 0 = 0 := by simp [Layout.start]
  have h7 : l.start 7 = l.len := by simp [Layout.start, Layout.len, Layout.widths]
  have hmono : ∀ i j, i ≤ j → j ≤ 7 → l.start i ≤ l.start j := by
    intro i j hij hj
    induction j with
    | zero => obtain rfl : i = 0 := by omega
              exact le_rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · exact (ih (by omega) (by omega)).trans (hs j (by omega))
  -- The section is the last one starting at or before `w`.
  have hex : ∃ i, i < 7 ∧ l.start i ≤ w ∧ w < l.start (i + 1) := by
    by_contra hn
    push Not at hn
    have : ∀ i ≤ 7, l.start i ≤ w := by
      intro i hi
      induction i with
      | zero => omega
      | succ i ih => exact hn i (by omega) (ih (by omega))
    have := this 7 le_rfl
    omega
  obtain ⟨i, hi, h1, h2⟩ := hex
  refine ⟨i, hi, h1, h2, fun j hj hj1 hj2 => ?_⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hmono (j + 1) i (by omega) (by omega); omega
  · have := hmono (i + 1) j (by omega) (by omega); omega

/-- The kind is the statement's first word and the digest its next two. -/
theorem kind_digest_words (l : Layout) : l.start 0 = 0 ∧ l.start 1 = 1 ∧ l.start 2 = 3 := by
  simp [Layout.start, Layout.widths]

/-! Heights: `Tree::converge`. -/

section Converge

variable {α : Type} [SemilatticeSup α]

/-- One round: each tier's heights joined with each of its circuits' heights `H σ p` at the tiers' heights `σ`. -/
def step (members : ℕ → List ℕ) (H : (ℕ → α) → ℕ → α) (σ : ℕ → α) (t : ℕ) : α :=
  (members t).foldl (fun h p => h ⊔ H σ p) (σ t)

/-- `Tree::converge` from the tiers' heights `σ`, for `k` rounds: `fits` is `RecLayout::from_taus` succeeding, which `Design::new` requires of every tier at every round (`RecShape::new`), else `TooLarge`; a round that changes no tier's heights returns them; running out of rounds is `TooLarge`. -/
def converge [DecidableEq α] (n : ℕ) (members : ℕ → List ℕ) (H : (ℕ → α) → ℕ → α) (fits : α → Bool) :
    ℕ → (ℕ → α) → Option (ℕ → α)
  | 0, _ => none
  | k + 1, σ =>
    if (List.range n).all fun t => fits (σ t) then
      if (List.range n).all fun t => decide (step members H σ t = σ t) then some σ
      else converge n members H fits k (step members H σ)
    else none

theorem foldl_sup_le (f : ℕ → α) (l : List ℕ) (a b : α) :
    l.foldl (fun h p => h ⊔ f p) a ≤ b ↔ a ≤ b ∧ ∀ p ∈ l, f p ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, sup_le_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem le_step (members : ℕ → List ℕ) (H : (ℕ → α) → ℕ → α) (σ : ℕ → α) (t : ℕ) :
    σ t ≤ step members H σ t ∧ ∀ p ∈ members t, H σ p ≤ step members H σ t :=
  (foldl_sup_le _ _ _ _).mp le_rfl

/-- Heights `converge` returns fit (`RecLayout::from_taus` succeeds at each tier's), every circuit's heights are within its tier's, and they are at least where it started. -/
theorem converge_fits [DecidableEq α] (n : ℕ) (members : ℕ → List ℕ) (H : (ℕ → α) → ℕ → α) (fits : α → Bool) :
    ∀ k σ₀ σ, converge n members H fits k σ₀ = some σ →
      (∀ t < n, fits (σ t) = true) ∧ (∀ t < n, ∀ p ∈ members t, H σ p ≤ σ t) ∧ ∀ t < n, σ₀ t ≤ σ t := by
  intro k
  induction k with
  | zero => intro σ₀ σ h; simp [converge] at h
  | succ k ih =>
    intro σ₀ σ h
    simp only [converge] at h
    split_ifs at h with hf he
    · simp only [Option.some.injEq] at h
      subst h
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf he
      refine ⟨hf, fun t ht p hp => ?_, fun t _ => le_rfl⟩
      rw [← he t ht]
      exact (le_step members H σ₀ t).2 p hp
    · obtain ⟨h1, h2, h3⟩ := ih _ _ h
      exact ⟨h1, h2, fun t ht => (le_step members H σ₀ t).1.trans (h3 t ht)⟩

/-- When a circuit's heights grow with its tiers' heights, `converge` returns the least heights above its start at which every circuit fits: `Tree::converge`'s least fixed point. -/
theorem converge_least [DecidableEq α] (n : ℕ) (members : ℕ → List ℕ) (H : (ℕ → α) → ℕ → α) (fits : α → Bool)
    (hmono : ∀ σ τ : ℕ → α, (∀ t < n, σ t ≤ τ t) → ∀ t < n, ∀ p ∈ members t, H σ p ≤ H τ p)
    (τ : ℕ → α) (hτ : ∀ t < n, ∀ p ∈ members t, H τ p ≤ τ t) :
    ∀ k σ₀ σ, (∀ t < n, σ₀ t ≤ τ t) → converge n members H fits k σ₀ = some σ → ∀ t < n, σ t ≤ τ t := by
  intro k
  induction k with
  | zero => intro σ₀ σ _ h; simp [converge] at h
  | succ k ih =>
    intro σ₀ σ h0 h
    simp only [converge] at h
    split_ifs at h with hf he
    · simp only [Option.some.injEq] at h
      subst h
      exact h0
    · refine ih _ _ (fun t ht => ?_) h
      refine (foldl_sup_le _ _ _ _).mpr ⟨h0 t ht, fun p hp => ?_⟩
      exact (hmono σ₀ τ h0 t ht p hp).trans (hτ t ht p hp)

end Converge

end LeanVMCircuits.Rec.Design
