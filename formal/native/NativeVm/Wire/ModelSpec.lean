module

public import NativeVm.Wire.Climb

/-!
# The model is `Proof.fromBytes`

`decodeM_spec`: the word model `decodeM` decodes exactly the proofs `Proof.fromBytes` decodes over
Keccak-f[1600], from the same bytes: the reads are the wire's (`NativeVm.Wire.Read`), the distinct
positions by insertion are `distinctPositions` (`sortD_eq`), and the climb, reading each level's
carried siblings as it goes, is `readCarriedSiblings` then `climbLevels` (`climbM_agree`).
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Wire

/-! ## The distinct positions -/

theorem mem_insD (x y : Nat) : ∀ l : List Nat, y ∈ insD l x ↔ y = x ∨ y ∈ l
  | [] => by simp [insD]
  | a :: l => by
    unfold insD
    split
    · simp
    · split
      · subst_vars; simp
      · simp only [List.mem_cons, mem_insD x y l]
        tauto

theorem pairwise_insD (x : Nat) : ∀ l : List Nat, l.Pairwise (· < ·) → (insD l x).Pairwise (· < ·)
  | [], _ => by simp [insD]
  | a :: l, h => by
    unfold insD
    split
    · rename_i hx
      refine List.Pairwise.cons (fun y hy ↦ ?_) h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hx.trans (List.rel_of_pairwise_cons h hy)
    · split
      · exact h
      · rename_i hx hx'
        refine List.Pairwise.cons (fun y hy ↦ ?_) (pairwise_insD x l h.of_cons)
        rcases (mem_insD x y l).1 hy with rfl | hy
        · omega
        · exact List.rel_of_pairwise_cons h hy

theorem sortD_aux (qs : List Nat) : ∀ l : List Nat, l.Pairwise (· < ·) →
    (qs.foldl insD l).Pairwise (· < ·) ∧ ∀ y, y ∈ qs.foldl insD l ↔ y ∈ qs ∨ y ∈ l := by
  induction qs with
  | nil => intro l h; simp [h]
  | cons q qs ih =>
    intro l h
    obtain ⟨h1, h2⟩ := ih (insD l q) (pairwise_insD q l h)
    refine ⟨h1, fun y ↦ ?_⟩
    simp only [List.foldl_cons, h2, mem_insD, List.mem_cons]
    tauto

/-- **The distinct positions by insertion** are `distinctPositions`. -/
theorem sortD_eq (qs : List Nat) : sortD qs = distinctPositions qs := by
  obtain ⟨h1, h2⟩ := sortD_aux qs [] List.Pairwise.nil
  exact eq_of_pairwise_lt_of_mem_iff h1 (pairwise_lt_distinctPositions qs) fun y ↦ by
    rw [sortD, h2, mem_distinctPositions]
    simp

/-! ## A phase -/

theorem shiftRight_eq_zero_iff (a h : Nat) : a >>> h = 0 ↔ a < 2 ^ h := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos h)]

theorem last_iff (ps : List Nat) (h : Nat) :
    (∃ last ∈ ps.getLast?, last >>> h = 0) ↔ ps ≠ [] ∧ ps.getLastD 0 < 2 ^ h := by
  cases hp : ps.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hp
    simp [hp]
  | some v =>
    have hne : ps ≠ [] := by rintro rfl; simp at hp
    rw [List.getLastD_eq_getLast?, hp]
    simp [hne, shiftRight_eq_zero_iff]

theorem getD_paddedLeaf (r : List K) (lw : Nat) :
    (paddedLeaf r lw).getD (lw - r.length) 0 = r.getD 0 0 := by
  unfold paddedLeaf
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_replicate,
    Nat.sub_self, List.getD_eq_getElem?_getD]

/-- **A phase**: the model reads at `c` what `readPhase` reads from `B.drop c`, and gives the
openings `unprunePhase` gives. -/
theorem phase_agree {B : List UInt8} {c : Nat} (hc : c ≤ B.length) :
    (readPhase (B.drop c) = none → phaseM B c = none) ∧
    ∀ ph rest, readPhase (B.drop c) = some (ph, rest) → ∃ c', c' ≤ B.length ∧ rest = B.drop c' ∧
      phaseM B c = some (⟨ph.height, ph.leafWords,
        Id.run (unprunePhase (m := Id) LeanVM.Semantics.keccakF1600 ph)⟩, c') := by
  unfold readPhase phaseM
  rw [readU32_drop hc]
  cases h1 : rdU32 B c with
  | none => simp
  | some p =>
    obtain ⟨count, c1⟩ := p
    have hc1 := rdU32_le h1
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, sortD_eq]
    by_cases hq : count ≤ wireMaxQueries
    swap
    · simp [hq, show wireMaxQueries < count by omega]
    simp only [hq, show ¬ wireMaxQueries < count by omega, guard, ite_true, ite_false,
      Option.pure_def, Option.bind_some]
    rw [readU32s_drop count hc1]
    cases h2 : rdU32s B count c1 with
    | none => simp
    | some p =>
    obtain ⟨queries, c2⟩ := p
    have hc2 := rdU32s_le count hc1 h2
    simp only [Option.map_some, Option.bind_some]
    rw [readU32_drop hc2]
    cases h3 : rdU32 B c2 with
    | none => simp
    | some p =>
    obtain ⟨height, c3⟩ := p
    have hc3 := rdU32_le h3
    simp only [Option.map_some, Option.bind_some]
    rw [readU32_drop hc3]
    cases h4 : rdU32 B c3 with
    | none => simp
    | some p =>
    obtain ⟨leafWords, c4⟩ := p
    have hc4 := rdU32_le h4
    simp only [Option.map_some, Option.bind_some]
    rw [readU32_drop hc4]
    cases h5 : rdU32 B c4 with
    | none => simp
    | some p =>
    obtain ⟨rowWords, c5⟩ := p
    have hc5 := rdU32_le h5
    simp only [Option.map_some, Option.bind_some, last_iff]
    generalize hP : distinctPositions queries = positions
    by_cases hg : height ≤ wireMaxHeight ∧ leafWords ≤ wireMaxLeafWords ∧ rowWords ≤ leafWords ∧
      positions ≠ [] ∧ positions.getLastD 0 < 2 ^ height
    swap
    · rw [ite_no hg, ite_yes hg]
      simp [failure]
    rw [ite_yes hg, ite_no (not_not.2 hg)]
    simp only [Option.bind_some]
    rw [readRows_drop rowWords _ hc5]
    cases h6 : rdRows B rowWords positions.length c5 with
    | none => simp
    | some p =>
    obtain ⟨rows, c6⟩ := p
    have hc6 := rdRows_le _ _ hc5 h6
    obtain ⟨hrl, hrw⟩ := rdRows_length _ _ h6
    simp only [Option.map_some, Option.bind_some]
    have hzero : (∀ leaf ∈ rows.map (fun row ↦ paddedLeaf row leafWords),
        leaf.getD (leafWords - rowWords) 0 = 0) ↔ ∀ r ∈ rows, r.getD 0 0 = 0 := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      refine forall₂_congr fun r hr ↦ ?_
      rw [← hrw r hr, getD_paddedLeaf]
    simp only [hzero]
    by_cases hz : 0 < rowWords ∧ ∀ r ∈ rows, r.getD 0 0 = 0
    · rw [ite_no (not_not.2 hz), ite_yes hz]
      simp [failure]
    rw [ite_yes hz, ite_no hz]
    simp only [Option.bind_some]
    have hpos : positions.Pairwise (· < ·) := hP ▸ pairwise_lt_distinctPositions queries
    have hkeys : keys (positions.zip ((rows.map fun row ↦ paddedLeaf row leafWords).map
        fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))) = levelNodes positions 0 := by
      rw [levelNodes_zero hpos, keys, List.map_fst_zip]
      simp [hrl]
    obtain ⟨hn, hs⟩ := climbM_agree hpos height 0 _ c6 hc6 hkeys
    cases hr : readCarriedSiblings positions 0 height (B.drop c6) with
    | none => rw [hn hr]; simp
    | some p =>
    obtain ⟨carried, rest⟩ := p
    obtain ⟨c', hc', hrest, hm⟩ := hs carried rest hr
    refine ⟨fun h ↦ by simp at h, fun ph rest' h ↦ ?_⟩
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨c', hc', hrest, ?_⟩
    rw [hm]
    simp only [Option.bind_some, unprunePhase, Id.run_bind, List.idRun_mapM, keccak_id]
    rfl

/-- What a phase decodes to, from its pruned form. -/
def outOf (ph : PrunedPhase) : PhaseOut :=
  ⟨ph.height, ph.leafWords, Id.run (unprunePhase (m := Id) LeanVM.Semantics.keccakF1600 ph)⟩

theorem phases_agree {B : List UInt8} (n : Nat) : ∀ {c : Nat}, c ≤ B.length →
    (readPhases n (B.drop c) = none → phasesM B n c = none) ∧
    ∀ phs rest, readPhases n (B.drop c) = some (phs, rest) → ∃ c', c' ≤ B.length ∧
      rest = B.drop c' ∧ phasesM B n c = some (phs.map outOf, c') := by
  induction n with
  | zero =>
    intro c hc
    refine ⟨fun h ↦ (by cases h), fun phs rest h ↦ ?_⟩
    simp only [readPhases, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, hc, rfl, rfl⟩
  | succ n ih =>
    intro c hc
    obtain ⟨hn, hs⟩ := phase_agree hc
    simp only [readPhases, phasesM, Option.bind_eq_bind]
    cases hr : readPhase (B.drop c) with
    | none => rw [hn hr]; simp
    | some p =>
    obtain ⟨ph, rest1⟩ := p
    obtain ⟨c1, hc1, rfl, hm⟩ := hs ph rest1 hr
    rw [hm]
    simp only [Option.bind_some]
    obtain ⟨hn', hs'⟩ := ih hc1
    cases hr' : readPhases n (B.drop c1) with
    | none => rw [hn' hr']; simp
    | some p =>
    obtain ⟨phs, rest2⟩ := p
    obtain ⟨c2, hc2, rfl, hm'⟩ := hs' phs rest2 hr'
    rw [hm']
    refine ⟨fun h ↦ by simp at h, fun phs' rest h ↦ ?_⟩
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c2, hc2, rfl, by simp [outOf]⟩

/-- **The model is `Proof.fromBytes`** over Keccak-f[1600]. -/
theorem decodeM_spec (B : List UInt8) :
    Id.run (Proof.fromBytes (m := Id) LeanVM.Semantics.keccakF1600 B) = (decodeM B).map toProof := by
  have h0 : (0 : Nat) ≤ B.length := Nat.zero_le _
  have hB : readProof B = readProof (B.drop 0) := by rw [List.drop_zero]
  unfold Proof.fromBytes
  rw [hB]
  unfold readProof decodeM streamM
  rw [readU32_drop h0]
  cases h1 : rdU32 B 0 with
  | none => rfl
  | some p =>
  obtain ⟨len, c1⟩ := p
  have hc1 := rdU32_le h1
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  rw [readWords_drop hc1]
  cases h2 : rdWords B (2 * len) c1 with
  | none => rfl
  | some p =>
  obtain ⟨ws, c2⟩ := p
  have hc2 := rdWords_le h2
  simp only [Option.map_some, Option.bind_some]
  rw [readU32_drop hc2]
  cases h3 : rdU32 B c2 with
  | none => rfl
  | some p =>
  obtain ⟨pc, c3⟩ := p
  have hc3 := rdU32_le h3
  simp only [Option.map_some, Option.bind_some]
  by_cases hp : pc ≤ wireMaxPhases
  swap
  · simp [hp, show wireMaxPhases < pc by omega, failure]
  simp only [hp, show ¬ wireMaxPhases < pc by omega, guard, ite_true, ite_false, Option.pure_def,
    Option.bind_some]
  obtain ⟨hn, hs⟩ := phases_agree pc hc3
  cases hr : readPhases pc (B.drop c3) with
  | none => rw [hn hr]; rfl
  | some p =>
  obtain ⟨phs, rest⟩ := p
  obtain ⟨c4, hc4, rfl, hm⟩ := hs phs rest hr
  rw [hm]
  simp only [Option.bind_some]
  by_cases he : c4 = B.length
  · simp only [he, ne_eq, not_true_eq_false, ite_false]
    simp [toProof, outOf, List.idRun_mapM]
  · have : (B.drop c4).isEmpty = false := by simp; omega
    simp only [this, he, Bool.false_eq_true, ite_false, ne_eq, not_false_eq_true, ite_true]
    simp [failure]

end NativeVm.Wire
