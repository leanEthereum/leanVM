module

public import NativeRustcVm.Wire.Rep
public import NativeRustcVm.Wire.ModelFacts
public import NativeVm.Wire.Sort
public import NativeVm.Wire.ClimbFacts
public import NativeVm.Wire.Read
public import NativeVm.Model.Transcript

/-!
# `phaseM` as `phase_m` runs it

The model's phase (`NativeVm.Wire.phaseM`) step by step, as the code reads it: the six reads
(`phaseM_eq`), then the checks, the rows and the climb (`tail`). The queries read one by one
(`rdU32s_snoc`, `rdU32s_len`), a 4-byte read as `Reader::le` gives it (`rdLe_four`), the climb level
by level (`climb_acc`), a leaf's digest as `hash_words` computes it (`leaf_hash`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeVm NativeVm.Wire NativeRustcVm.Wire LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The rest of the phase after the six reads. -/
def tail (B : List UInt8) (qs : List Nat) (height lw rw c : Nat) : Option (PhaseOut × Nat) :=
  if ¬(height ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ height) then none else
  match rdRows B rw (sortD qs).length c with
  | none => none
  | some (rows, c) =>
    if 0 < rw ∧ ∀ r ∈ rows, r.getD 0 0 = 0 then none else
    match climbM B height ((sortD qs).zip ((rows.map fun r ↦ paddedLeaf r lw).map
        fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))) c with
    | none => none
    | some (sibs, c) => some (⟨height, lw, qs.map
        (openingAt (sortD qs) (rows.map fun r ↦ paddedLeaf r lw) sibs height)⟩, c)

end

public section

/-- **The phase** read by read. -/
theorem phaseM_eq (B : List UInt8) (c : Nat) : phaseM B c =
    match rdU32 B c with
    | none => none
    | some (count, c1) => if wireMaxQueries < count then none else
      match rdU32s B count c1 with
      | none => none
      | some (qs, c2) => match rdU32 B c2 with
        | none => none
        | some (height, c3) => match rdU32 B c3 with
          | none => none
          | some (lw, c4) => match rdU32 B c4 with
            | none => none
            | some (rw, c5) => tail B qs height lw rw c5 := by
  unfold phaseM tail
  simp only [Option.bind_eq_bind]
  rcases h1 : rdU32 B c with _ | ⟨count, c1⟩
  · rfl
  simp only [Option.bind_some]
  by_cases hq : wireMaxQueries < count
  · simp [hq]
  simp only [hq, ↓reduceIte]
  rcases h2 : rdU32s B count c1 with _ | ⟨qs, c2⟩
  · rfl
  simp only [Option.bind_some]
  rcases h3 : rdU32 B c2 with _ | ⟨ht, c3⟩
  · rfl
  simp only [Option.bind_some]
  rcases h4 : rdU32 B c3 with _ | ⟨lw, c4⟩
  · rfl
  simp only [Option.bind_some]
  rcases h5 : rdU32 B c4 with _ | ⟨rw, c5⟩
  · rfl
  simp only [Option.bind_some]
  split
  · rfl
  rcases h6 : rdRows B rw (sortD qs).length c5 with _ | ⟨rows, c6⟩
  · rfl
  simp only [Option.bind_some]
  split
  · rfl
  rcases h7 : climbM B ht _ c6 with _ | ⟨sibs, c7⟩
  · rfl
  rfl

/-- After the queries. -/
theorem pm_eq_of {B : List UInt8} {c count c1 : Nat} {qs : List Nat} {c2 : Nat}
    (h1 : rdU32 B c = some (count, c1)) (hc : count ≤ 256)
    (hqs : rdU32s B count c1 = some (qs, c2)) :
    phaseM B c = match rdU32 B c2 with
      | none => none
      | some (height, c3) => match rdU32 B c3 with
        | none => none
        | some (lw, c4) => match rdU32 B c4 with
          | none => none
          | some (rw, c5) => tail B qs height lw rw c5 := by
  rw [phaseM_eq, h1]
  simp only [show ¬ wireMaxQueries < count by unfold wireMaxQueries; omega, ↓reduceIte, hqs]

theorem tail_nil (B : List UInt8) (h lw rw c : Nat) : tail B [] h lw rw c = none := by
  simp [tail, sortD]

/-- A 4-byte read of `Reader::le` is `rdU32`'s. -/
theorem rdLe_four (B : List UInt8) (c : Nat) :
    rdLe B c 4 = (rdU32 B c).map fun p ↦ (p.1.toUInt64, p.2) := by
  unfold rdLe rdU32
  split <;> rfl

theorem rdU32s_len (B : List UInt8) : ∀ (n c : Nat) {qs : List Nat} {c' : Nat},
    rdU32s B n c = some (qs, c') → qs.length = n ∧ c' = c + 4 * n
  | 0, c, qs, c', h => by cases h; simp
  | n + 1, c, qs, c', h => by
    simp only [rdU32s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨v, c1⟩, h1, ⟨vs, c2⟩, h2, he⟩ := h
    cases he
    obtain ⟨hl, hc⟩ := rdU32s_len B n c1 h2
    have : c1 = c + 4 := by
      unfold rdU32 at h1
      split at h1
      · cases h1; rfl
      · cases h1
    exact ⟨by simp [hl], by rw [hc, this]; ring⟩

/-- **One more query.** -/
theorem rdU32s_snoc (B : List UInt8) : ∀ (n c : Nat) {qs : List Nat} {c' v c'' : Nat},
    rdU32s B n c = some (qs, c') → rdU32 B c' = some (v, c'') →
    rdU32s B (n + 1) c = some (qs ++ [v], c'')
  | 0, c, qs, c', v, c'', h, h' => by
    cases h
    simp [rdU32s, h']
  | n + 1, c, qs, c', v, c'', h, h' => by
    simp only [rdU32s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨v0, c1⟩, h1, ⟨vs, c2⟩, h2, he⟩ := h
    cases he
    have := rdU32s_snoc B n c1 h2 h'
    rw [rdU32s]
    simp only [Option.bind_eq_bind, h1, Option.bind_some]
    rw [this]
    rfl

/-- **A query missing**: no more queries. -/
theorem rdU32s_none (B : List UInt8) : ∀ (n c : Nat) {qs : List Nat} {c' : Nat} (m : Nat),
    rdU32s B n c = some (qs, c') → rdU32 B c' = none → rdU32s B (n + 1 + m) c = none
  | 0, c, qs, c', m, h, h' => by
    cases h
    rw [Nat.zero_add, Nat.add_comm, rdU32s]
    simp [h']
  | n + 1, c, qs, c', m, h, h' => by
    simp only [rdU32s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨v0, c1⟩, h1, ⟨vs, c2⟩, h2, he⟩ := h
    cases he
    have := rdU32s_none B n c1 m h2 h'
    rw [show n + 1 + 1 + m = (n + 1 + m) + 1 by omega, rdU32s]
    simp [h1, this]

/-- The queries' values as `Reader::le` gives them. -/
theorem leNat_four_lt (B : List UInt8) (c : Nat) : leNat B c 4 < 2 ^ 32 := by
  have := leNat_lt B c 4
  simpa using this

/-! ## The climb -/

/-- **The climb, level by level**: after levels `acc`, the rest from the level's nodes. -/
theorem climb_acc {B : List UInt8} {k : Nat} {ns : List (Nat × Digest)} {c : Nat}
    {sl : List (Nat × Digest × Bool)} {c' : Nat} (hs : sibsM B ns ns c = some (sl, c'))
    (acc : List (List (Nat × Digest))) :
    (climbM B (k + 1) ns c).map (fun q ↦ (acc ++ q.1, q.2)) =
      (climbM B k (parentsOf ns sl) c').map
        (fun q ↦ ((acc ++ [sl.map fun s ↦ (s.1, s.2.1)]) ++ q.1, q.2)) := by
  rw [climbM_succ, hs, Option.bind_some, Option.map_map]
  congr 1
  funext q
  simp

theorem sibsM_len (B : List UInt8) (ns : List (Nat × Digest)) :
    ∀ (l : List (Nat × Digest)) (c : Nat) {sl : List (Nat × Digest × Bool)} {c' : Nat},
    sibsM B ns l c = some (sl, c') → sl.length = l.length
  | [], c, sl, c', h => by cases h; rfl
  | (v, d) :: l, c, sl, c', h => by
    simp only [sibsM] at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨r, c1⟩, h1, he⟩ := h
      cases he
      simp [sibsM_len B ns l c h1]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨d', c1⟩, -, ⟨r, c2⟩, h2, he⟩ := h
      cases he
      simp [sibsM_len B ns l c1 h2]

theorem climb_none {B : List UInt8} {k : Nat} {ns : List (Nat × Digest)} {c : Nat}
    (hs : sibsM B ns ns c = none) : climbM B (k + 1) ns c = none := by
  rw [climbM_succ, hs]
  rfl

/-! ## Leaves -/

/-- **A leaf's digest** is `hash_words` of its words. -/
theorem leaf_hash (leaf : List K) :
    keccak256 (leaf.flatMap K.toBytes) = NativeVm.Model.hashWords (leaf.map K.lane).toArray := by
  unfold NativeVm.Model.hashWords Native.Keccak.wordsBytes
  rw [List.toList_toArray, List.flatMap_map]
  rfl

theorem length_paddedLeaf {r : List K} {lw : Nat} (h : r.length ≤ lw) :
    (paddedLeaf r lw).length = lw := by
  unfold paddedLeaf
  simp only [List.length_append, List.length_replicate]
  omega

end

end NativeRustcVmArm.Wire.PhaseM
