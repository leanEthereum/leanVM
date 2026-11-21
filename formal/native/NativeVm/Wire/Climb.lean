module

public import NativeVm.Wire.Read
public import LeanVM.Wire.UnpruneList

/-!
# The model's climb is the wire's

The Rust, and the model (`climbM`), read each level's carried siblings while climbing; the
transcription (`readCarriedSiblings`, then `climbLevels`) reads them all first. Which siblings a
level reads depends on its nodes' positions only, and the model's level-`k` nodes are
`levelNodes positions k` (`LeanVM.Wire.levelNodes_succ`), so both read the same digests and climb
alike (`climbM_agree`).
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Wire

variable {B : List UInt8}

/-- `n` digests from `c`. -/
def rdDigests (B : List UInt8) : Nat → Nat → Option (List Digest × Nat)
  | 0, c => some ([], c)
  | n + 1, c => do
    let (d, c) ← rdDigest B c
    let (ds, c) ← rdDigests B n c
    some (d :: ds, c)

theorem readDigests_drop (n : Nat) : ∀ {c : Nat}, c ≤ B.length →
    readDigests n (B.drop c) = (rdDigests B n c).map fun (v, c') ↦ (v, B.drop c') := by
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    simp only [readDigests, rdDigests, readDigest_drop hc]
    cases h : rdDigest B c with
    | none => rfl
    | some p =>
      obtain ⟨v, c'⟩ := p
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [ih (rdDigest_le h)]
      cases rdDigests B n c' with
      | none => rfl
      | some q => rfl

theorem rdDigests_le (n : Nat) : ∀ {c c' : Nat} {vs : List Digest}, c ≤ B.length →
    rdDigests B n c = some (vs, c') → c' ≤ B.length := by
  induction n with
  | zero => intro c c' vs hc h; cases h; exact hc
  | succ n ih =>
    intro c c' vs hc h
    simp only [rdDigests, Option.bind_eq_bind] at h
    cases h1 : rdDigest B c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨v, c1⟩ := p
      simp only [h1, Option.bind_some] at h
      cases h2 : rdDigests B n c1 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨vs', c2⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ ih (rdDigest_le h1) h2

/-! ## One level -/

/-- The keys of a keyed list. -/
abbrev keys (l : List (Nat × Digest)) : List Nat := l.map Prod.fst

/-- The nodes of `l` whose sibling is not a node of the level `nodes`. -/
def carriedKeys (nodes l : List (Nat × Digest)) : List Nat :=
  (keys l).filter fun v ↦ v ^^^ 1 ∉ keys nodes

/-- `climbLevel`'s sibling of `v`. -/
def sibOf (nodes carried : List (Nat × Digest)) (v : Nat) : Digest :=
  ((nodes.lookup (v ^^^ 1)).orElse fun _ ↦ carried.lookup v).getD default

theorem lookup_isSome_iff {l : List (Nat × Digest)} {a : Nat} :
    (l.lookup a).isSome ↔ a ∈ keys l := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, d⟩ := p
    rw [List.lookup_cons]
    by_cases h : a = k
    · subst h; simp
    · rw [beq_eq_false_iff_ne.2 h]
      simp [ih, h]

theorem sibsM_eq (nodes : List (Nat × Digest)) : ∀ (l : List (Nat × Digest)) {c : Nat},
    (keys l).Nodup → c ≤ B.length →
    sibsM B nodes l c = (rdDigests B (carriedKeys nodes l).length c).map fun (ds, c') ↦
      (l.map fun p ↦ (p.1, sibOf nodes ((carriedKeys nodes l).zip ds) p.1,
        (nodes.lookup (p.1 ^^^ 1)).isSome), c')
  | [], c, _, _ => rfl
  | (v, d0) :: l, c, hnd, hc => by
    have hnd' : (keys l).Nodup := (List.nodup_cons.1 hnd).2
    have hv : v ∉ keys l := (List.nodup_cons.1 hnd).1
    unfold sibsM
    cases hl : nodes.lookup (v ^^^ 1) with
    | some d =>
      have hmem : v ^^^ 1 ∈ keys nodes := lookup_isSome_iff.1 (by rw [hl]; rfl)
      have hck : carriedKeys nodes ((v, d0) :: l) = carriedKeys nodes l := by
        simp [carriedKeys, hmem]
      simp only [Option.bind_eq_bind]
      rw [sibsM_eq nodes l hnd' hc, hck]
      cases rdDigests B (carriedKeys nodes l).length c with
      | none => rfl
      | some q =>
        obtain ⟨ds, c'⟩ := q
        simp [sibOf, hl]
    | none =>
      have hmem : v ^^^ 1 ∉ keys nodes := fun h ↦ by
        have := lookup_isSome_iff.2 h; rw [hl] at this; cases this
      have hck : carriedKeys nodes ((v, d0) :: l) = v :: carriedKeys nodes l := by
        simp [carriedKeys, hmem]
      simp only [Option.bind_eq_bind]
      rw [hck, List.length_cons, rdDigests]
      simp only [Option.bind_eq_bind]
      cases h1 : rdDigest B c with
      | none => rfl
      | some p =>
        obtain ⟨dg, c1⟩ := p
        simp only [Option.bind_some]
        rw [sibsM_eq nodes l hnd' (rdDigest_le h1)]
        cases rdDigests B (carriedKeys nodes l).length c1 with
        | none => rfl
        | some q =>
          obtain ⟨ds, c'⟩ := q
          simp only [Option.map_some, Option.bind_some, List.map_cons, List.zip_cons_cons,
            Option.some.injEq, Prod.mk.injEq, and_true, List.cons.injEq]
          refine ⟨by simp [sibOf, hl], List.map_congr_left fun p hp ↦ ?_⟩
          have hpv : p.1 ≠ v := fun h ↦ hv (h ▸ List.mem_map_of_mem hp)
          simp [sibOf, List.lookup_cons, beq_eq_false_iff_ne.2 hpv]

theorem parentsOf_map (nodes : List (Nat × Digest)) (g : Nat × Digest → Nat × Digest × Bool) :
    parentsOf nodes (nodes.map g) = nodes.flatMap fun nd ↦ parentOf nd (g nd) := by
  induction nodes with
  | nil => rfl
  | cons nd nodes ih =>
    simp only [parentsOf, List.map_cons, List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]

theorem filter_map_eq_flatMap {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter p).map f = l.flatMap fun x ↦ if p x then [f x] else []
  | [] => rfl
  | x :: l => by
    rw [List.filter_cons, List.flatMap_cons, ← filter_map_eq_flatMap p f l]
    cases p x <;> simp

theorem keccak_id (x : List UInt8) :
    Id.run (keccak256With (m := Id) LeanVM.Semantics.keccakF1600 x) = keccak256 x := rfl

/-- **One level**: `climbLevel` with the carried digests `ds`, as the model computes it. -/
theorem climbLevel_eq (nodes : List (Nat × Digest)) (ds : List Digest) :
    let carried := (carriedSiblings (keys nodes)).zip ds
    let g := fun p : Nat × Digest ↦ (p.1, sibOf nodes carried p.1,
      (nodes.lookup (p.1 ^^^ 1)).isSome)
    Id.run (climbLevel (m := Id) LeanVM.Semantics.keccakF1600 nodes carried) =
      ((nodes.map g).map fun s ↦ (s.1, s.2.1), parentsOf nodes (nodes.map g)) := by
  intro carried g
  rw [parentsOf_map]
  simp only [climbLevel, Id.run, List.map_map]
  refine Prod.ext rfl ?_
  show Id.run (List.mapM _ _) = _
  rw [List.idRun_mapM]
  rw [filter_map_eq_flatMap]
  congr 1
  funext nd
  obtain ⟨v, d⟩ := nd
  have hk : (nodes.lookup (v ^^^ 1)).isSome = false ↔ v ^^^ 1 ∉ keys nodes := by
    rw [← lookup_isSome_iff]; cases (nodes.lookup (v ^^^ 1)).isSome <;> simp
  by_cases hv : v % 2 = 0
  · simp [parentOf, g, sibOf, hv, keccak_id]
  · by_cases hm : v ^^^ 1 ∈ keys nodes
    · have : (nodes.lookup (v ^^^ 1)).isSome = true := lookup_isSome_iff.2 hm
      simp [parentOf, g, hv, this, hm]
    · have : (nodes.lookup (v ^^^ 1)).isSome = false := hk.2 hm
      simp [parentOf, g, sibOf, hv, this, hm, keccak_id]

theorem keys_append (a b : List (Nat × Digest)) : keys (a ++ b) = keys a ++ keys b :=
  List.map_append

theorem keys_cons (a : Nat × Digest) (b : List (Nat × Digest)) : keys (a :: b) = a.1 :: keys b :=
  rfl

theorem keys_parentOf (nd : Nat × Digest) (sb : Nat × Digest × Bool) :
    keys (parentOf nd sb) = if nd.1 % 2 = 0 ∨ sb.2.2 = false then [nd.1 >>> 1] else [] := by
  unfold parentOf
  split <;> rfl

theorem keys_flatMap_parentOf (nodes : List (Nat × Digest)) (f : Nat → Digest) :
    ∀ l : List (Nat × Digest), keys (l.flatMap fun nd ↦
      parentOf nd (nd.1, f nd.1, (nodes.lookup (nd.1 ^^^ 1)).isSome)) =
      ((keys l).filter fun n ↦ n % 2 = 0 ∨ n ^^^ 1 ∉ keys nodes).map (· >>> 1)
  | [] => rfl
  | nd :: l => by
    rw [List.flatMap_cons, keys_append, keys_flatMap_parentOf nodes f l, keys_parentOf, keys_cons]
    have hk : (nodes.lookup (nd.1 ^^^ 1)).isSome = false ↔ nd.1 ^^^ 1 ∉ keys nodes := by
      rw [← lookup_isSome_iff]; cases (nodes.lookup (nd.1 ^^^ 1)).isSome <;> simp
    simp only [List.filter_cons]
    by_cases hc : nd.1 % 2 = 0 ∨ nd.1 ^^^ 1 ∉ keys nodes
    · have : nd.1 % 2 = 0 ∨ (nodes.lookup (nd.1 ^^^ 1)).isSome = false := by rwa [hk]
      rw [ite_yes this, ite_yes (decide_eq_true hc)]
      rfl
    · have : ¬(nd.1 % 2 = 0 ∨ (nodes.lookup (nd.1 ^^^ 1)).isSome = false) := by rwa [hk]
      simp only [this, hc, ite_false, decide_false, List.nil_append]
      rfl

/-- **The climb**: the model reads at each level what `readCarriedSiblings` reads there, and climbs
as `climbLevels` does. -/
theorem climbM_agree {positions : List Nat} (hpos : positions.Pairwise (· < ·)) (h : Nat) :
    ∀ (level : Nat) (nodes : List (Nat × Digest)) (c : Nat), c ≤ B.length →
      keys nodes = levelNodes positions level →
      (readCarriedSiblings positions level h (B.drop c) = none → climbM B h nodes c = none) ∧
      ∀ carried rest, readCarriedSiblings positions level h (B.drop c) = some (carried, rest) →
        ∃ c', c' ≤ B.length ∧ rest = B.drop c' ∧
          climbM B h nodes c = some (Id.run (climbLevels (m := Id) LeanVM.Semantics.keccakF1600
            carried nodes), c') := by
  induction h with
  | zero =>
    intro level nodes c hc _
    refine ⟨fun h ↦ (by cases h), fun carried rest h ↦ ?_⟩
    simp only [readCarriedSiblings, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, hc, rfl, rfl⟩
  | succ h ih =>
    intro level nodes c hc hkeys
    have hnd : (keys nodes).Nodup := by
      rw [hkeys]; exact (pairwise_lt_levelNodes (hpos.imp le_of_lt) level).imp ne_of_lt
    have hck : carriedKeys nodes nodes = carriedSiblings (levelNodes positions level) := by
      rw [carriedKeys, carriedSiblings, hkeys]
    simp only [readCarriedSiblings, climbM, Option.bind_eq_bind, readDigests_drop _ hc,
      sibsM_eq nodes nodes hnd hc, hck]
    cases hd : rdDigests B (carriedSiblings (levelNodes positions level)).length c with
    | none => simp
    | some q =>
      obtain ⟨ds, c1⟩ := q
      have hc1 := rdDigests_le _ hc hd
      simp only [Option.map_some, Option.bind_some]
      rw [← hkeys]
      have hk' : keys (parentsOf nodes (nodes.map fun p ↦ (p.1,
          sibOf nodes ((carriedSiblings (keys nodes)).zip ds) p.1,
          (nodes.lookup (p.1 ^^^ 1)).isSome))) = levelNodes positions (level + 1) := by
        rw [parentsOf_map, keys_flatMap_parentOf, hkeys]
        exact levelNodes_succ (hpos.imp le_of_lt) level
      obtain ⟨ihn, ihs⟩ := ih (level + 1) _ c1 hc1 hk'
      cases hr : readCarriedSiblings positions (level + 1) h (B.drop c1) with
      | none => simp [ihn hr]
      | some q =>
        obtain ⟨above, rest'⟩ := q
        obtain ⟨c', hc', hrest, hm⟩ := ihs above rest' hr
        refine ⟨fun h ↦ by simp at h, fun carried rest h ↦ ?_⟩
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨c', hc', hrest, ?_⟩
        rw [hm]
        simp only [Option.bind_some, climbLevels, Id.run_bind]
        rw [climbLevel_eq]
        rfl


end NativeVm.Wire
